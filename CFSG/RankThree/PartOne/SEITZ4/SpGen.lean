module

public import CFSG.RankThree.PartOne.SEITZ4.SpPlane
public import CFSG.RankThree.PartOne.SEITZ4.SpRational

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.CTP

variable {r : ℕ} {K : Type} [Field K]

@[expose] def rootSet (H : Subgroup (StatedSp r K)) : Set (Fin r ⊕ Fin r → K) :=
  {a | ∀ c : K, (⟨spTrans a c, spTrans_mem_statedSp a c⟩ : StatedSp r K) ∈ H}

theorem zero_mem_rootSet (H : Subgroup (StatedSp r K)) : (0 : Fin r ⊕ Fin r → K) ∈ rootSet H :=
  fun c => by
    have : (⟨spTrans 0 c, spTrans_mem_statedSp 0 c⟩ : StatedSp r K) = 1 :=
      Subtype.ext (spTrans_zero_vec c)
    rw [this]
    exact H.one_mem

theorem smul_mem_rootSet {H : Subgroup (StatedSp r K)} {a : Fin r ⊕ Fin r → K}
    (ha : a ∈ rootSet H) (l : K) : l • a ∈ rootSet H := fun c => by
  have : (⟨spTrans (l • a) c, spTrans_mem_statedSp (l • a) c⟩ : StatedSp r K) =
      ⟨spTrans a (l ^ 2 * c), spTrans_mem_statedSp a (l ^ 2 * c)⟩ :=
    Subtype.ext (spTrans_smul a l c)
  rw [this]
  exact ha _

theorem mulVec_mem_rootSet {H : Subgroup (StatedSp r K)} {a : Fin r ⊕ Fin r → K}
    (ha : a ∈ rootSet H) {g : StatedSp r K} (hg : g ∈ H) :
    spMat g *ᵥ a ∈ rootSet H := fun c => by
  have : (⟨spTrans (spMat g *ᵥ a) c, spTrans_mem_statedSp _ c⟩ : StatedSp r K) =
      g * ⟨spTrans a c, spTrans_mem_statedSp a c⟩ * g⁻¹ :=
    Subtype.ext (conj_spTrans g.2 a c).symm
  rw [this]
  exact H.mul_mem (H.mul_mem hg (ha c)) (H.inv_mem hg)

theorem add_smul_mem_rootSet {H : Subgroup (StatedSp r K)} {a b : Fin r ⊕ Fin r → K}
    (ha : a ∈ rootSet H) (hb : b ∈ rootSet H) (hab : spForm r K a b ≠ 0) (μ : K) :
    a + μ • b ∈ rootSet H := by
  have h := mulVec_mem_rootSet ha (hb (μ / spForm r K a b))
  have e : spMat (⟨spTrans b (μ / spForm r K a b), spTrans_mem_statedSp b _⟩ : StatedSp r K) *ᵥ
      a = a + μ • b := by
    change spTransMat b (μ / spForm r K a b) *ᵥ a = _
    rw [spTransMat_mulVec, div_mul_cancel₀ _ hab]
  rwa [e] at h

@[expose] def IsRat (k : Subfield K) (x : Fin r ⊕ Fin r → K) : Prop := ∀ i, x i ∈ k

theorem isRat_add {k : Subfield K} {x y : Fin r ⊕ Fin r → K} (hx : IsRat k x) (hy : IsRat k y) :
    IsRat k (x + y) := fun i => k.add_mem (hx i) (hy i)

theorem isRat_single (k : Subfield K) (i : Fin r ⊕ Fin r) :
    IsRat k (Pi.single i (1 : K) : Fin r ⊕ Fin r → K) := fun j => by
  by_cases h : j = i
  · subst h
    simp [k.one_mem]
  · simp [h, k.zero_mem]

theorem spForm_mem_of_isRat {k : Subfield K} {x y : Fin r ⊕ Fin r → K} (hx : IsRat k x)
    (hy : IsRat k y) : spForm r K x y ∈ k := by
  rw [spForm_apply]
  exact k.sum_mem fun i _ =>
    k.sub_mem (k.mul_mem (hx _) (hy _)) (k.mul_mem (hx _) (hy _))

theorem single_ne_zero (a : Fin r ⊕ Fin r) : (Pi.single a (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 :=
  fun h => by simpa using congrFun h a

noncomputable def vsupp (y : Fin r ⊕ Fin r → K) : Finset (Fin r ⊕ Fin r) := by
  classical exact Finset.univ.filter fun i => y i ≠ 0

theorem mem_vsupp {y : Fin r ⊕ Fin r → K} {i : Fin r ⊕ Fin r} : i ∈ vsupp y ↔ y i ≠ 0 := by
  classical simp [vsupp]

section Char2

variable [CharP K 2]

theorem add_self_vec (x : Fin r ⊕ Fin r → K) : x + x = 0 := by
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem spForm_single_right (x : Fin r ⊕ Fin r → K) (i : Fin r ⊕ Fin r) :
    spForm r K x (Pi.single i 1) = x i.swap := by
  rw [spForm_apply]
  rcases i with i | i
  · simp [Pi.single_apply, CharTwo.neg_eq]
  · simp [Pi.single_apply]

theorem rat_step {H : Subgroup (StatedSp r K)} {k : Subfield K} (hH : spSub r k ≤ H)
    {x y : Fin r ⊕ Fin r → K} (hx : x ∈ rootSet H) (hxr : IsRat k x) (hyr : IsRat k y)
    (hxy : spForm r K x y ≠ 0) : y ∈ rootSet H := by
  have hc : (spForm r K x y)⁻¹ ∈ k := k.inv_mem (spForm_mem_of_isRat hxr hyr)
  have hg := hH (spTrans_mem_spSub k (isRat_add hxr hyr) hc)
  have h := mulVec_mem_rootSet hx hg
  have e : spMat (⟨spTrans (x + y) (spForm r K x y)⁻¹, spTrans_mem_statedSp _ _⟩ :
      StatedSp r K) *ᵥ x = y := by
    change spTransMat (x + y) (spForm r K x y)⁻¹ *ᵥ x = y
    rw [spTransMat_mulVec, map_add, spForm_self, zero_add, inv_mul_cancel₀ hxy, one_smul,
      ← add_assoc, add_self_vec, zero_add]
  rwa [e] at h

theorem swap_ne_self (a : Fin r ⊕ Fin r) : a.swap ≠ a := by
  rcases a with a | a <;> simp

theorem rat_mem_rootSet {H : Subgroup (StatedSp r K)} {k : Subfield K} (hH : spSub r k ≤ H)
    {x y : Fin r ⊕ Fin r → K} (hx : x ∈ rootSet H) (hxr : IsRat k x) (hx0 : x ≠ 0)
    (hyr : IsRat k y) (hy0 : y ≠ 0) : y ∈ rootSet H := by
  by_cases hxy : spForm r K x y = 0
  · obtain ⟨i, hi⟩ : ∃ i, spForm r K x (Pi.single i 1) ≠ 0 := by
      obtain ⟨i', hi'⟩ := Function.ne_iff.mp hx0
      exact ⟨i'.swap, by rw [spForm_single_right, Sum.swap_swap]; simpa using hi'⟩
    obtain ⟨j, hj⟩ : ∃ j, spForm r K y (Pi.single j 1) ≠ 0 := by
      obtain ⟨j', hj'⟩ := Function.ne_iff.mp hy0
      exact ⟨j'.swap, by rw [spForm_single_right, Sum.swap_swap]; simpa using hj'⟩
    obtain ⟨z, hzr, hxz, hyz⟩ : ∃ z : Fin r ⊕ Fin r → K,
        IsRat k z ∧ spForm r K x z ≠ 0 ∧ spForm r K y z ≠ 0 := by
      by_cases h1 : spForm r K y (Pi.single i 1) ≠ 0
      · exact ⟨_, isRat_single k i, hi, h1⟩
      · by_cases h2 : spForm r K x (Pi.single j 1) ≠ 0
        · exact ⟨_, isRat_single k j, h2, hj⟩
        · push Not at h1 h2
          refine ⟨Pi.single i 1 + Pi.single j 1,
            isRat_add (isRat_single k i) (isRat_single k j), ?_, ?_⟩
          · rw [map_add, h2, add_zero]
            exact hi
          · rw [map_add, h1, zero_add]
            exact hj
    have hz := rat_step hH hx hxr hzr hxz
    exact rat_step hH hz hzr hyr (by rw [spForm_comm']; exact hyz)
  · exact rat_step hH hx hxr hyr hxy

theorem mem_rootSet_of_pair {H : Subgroup (StatedSp r K)} {k : Subfield K} (hH : spSub r k ≤ H)
    {x : Fin r ⊕ Fin r → K} (hx : x ∈ rootSet H) (hxr : IsRat k x) (hx0 : x ≠ 0) (n : ℕ)
    (IH : ∀ y : Fin r ⊕ Fin r → K, (vsupp y).card < n → y ∈ rootSet H)
    {y : Fin r ⊕ Fin r → K} (hy : (vsupp y).card ≤ n) {a : Fin r ⊕ Fin r} (ha : y a ≠ 0)
    (ha' : y a.swap ≠ 0) : y ∈ rootSet H := by
  set y' : Fin r ⊕ Fin r → K := Function.update y a 0 with hy'
  have hsupp : vsupp y' = (vsupp y).erase a := by
    ext i
    simp only [mem_vsupp, Finset.mem_erase, hy', Function.update_apply]
    by_cases h : i = a <;> simp [h]
  have hcard : (vsupp y').card < n := by
    rw [hsupp, Finset.card_erase_of_mem (mem_vsupp.2 ha)]
    have : 0 < (vsupp y).card := Finset.card_pos.2 ⟨a, mem_vsupp.2 ha⟩
    omega
  have hy'mem := IH y' hcard
  have hea : (Pi.single a (1 : K) : Fin r ⊕ Fin r → K) ∈ rootSet H :=
    rat_mem_rootSet hH hx hxr hx0 (isRat_single k a) (single_ne_zero a)
  have hB : spForm r K y' (Pi.single a 1) ≠ 0 := by
    rw [spForm_single_right, hy', Function.update_of_ne (swap_ne_self a)]
    exact ha'
  have h := add_smul_mem_rootSet hy'mem hea hB (y a)
  have e : y' + y a • (Pi.single a (1 : K) : Fin r ⊕ Fin r → K) = y := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp [hy']
    · simp [hy', hi]
  rwa [e] at h

theorem rootSet_eq_univ {H : Subgroup (StatedSp r K)} {k : Subfield K} (hH : spSub r k ≤ H)
    {x : Fin r ⊕ Fin r → K} (hx : x ∈ rootSet H) (hxr : IsRat k x) (hx0 : x ≠ 0) :
    rootSet H = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have key : ∀ n : ℕ, ∀ y : Fin r ⊕ Fin r → K, (vsupp y).card = n → y ∈ rootSet H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro y hn
      have IH' : ∀ y : Fin r ⊕ Fin r → K, (vsupp y).card < n → y ∈ rootSet H :=
        fun y hy => IH _ hy y rfl
      by_cases h1 : ∃ a, y a ≠ 0 ∧ y a.swap ≠ 0
      · obtain ⟨a, ha, ha'⟩ := h1
        exact mem_rootSet_of_pair hH hx hxr hx0 n IH' hn.le ha ha'
      · push Not at h1
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · interval_cases n
          · have : vsupp y = ∅ := Finset.card_eq_zero.1 hn
            have hy0 : y = 0 := by
              funext i
              by_contra hi
              exact (Finset.notMem_empty i) (this ▸ mem_vsupp.2 hi)
            rw [hy0]
            exact zero_mem_rootSet H
          · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hn
            have hy1 : y = y a • (Pi.single a (1 : K) : Fin r ⊕ Fin r → K) := by
              funext i
              by_cases hi : i = a
              · subst hi
                simp
              · have : y i = 0 := by
                  by_contra hne
                  have := mem_vsupp.2 hne
                  rw [ha, Finset.mem_singleton] at this
                  exact hi this
                simp [this, hi]
            rw [hy1]
            exact smul_mem_rootSet (rat_mem_rootSet hH hx hxr hx0 (isRat_single k a)
              (single_ne_zero a)) _
        · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (vsupp y).card)
          have ha0 : y a ≠ 0 := mem_vsupp.1 ha
          have hb0 : y b ≠ 0 := mem_vsupp.1 hb
          have hsa : y a.swap = 0 := h1 a ha0
          have hsb : y b.swap = 0 := h1 b hb0
          have hba : b ≠ a.swap := fun h => hb0 (h ▸ hsa)
          have hsab : a.swap ≠ b := fun h => hba h.symm
          set z : Fin r ⊕ Fin r → K := Pi.single a.swap 1 + Pi.single b 1 with hz
          have hzr : IsRat k z := isRat_add (isRat_single k _) (isRat_single k _)
          have hzb : z b = 1 := by simp [hz, hba]
          have hza : z a = 0 := by
            simp [hz, (swap_ne_self a).symm, hab]
          have hzs : z a.swap = 1 := by simp [hz, hsab]
          have hz0 : z ≠ 0 := fun h => by simp [h] at hzb
          have hzmem : z ∈ rootSet H := rat_mem_rootSet hH hx hxr hx0 hzr hz0
          have hBz : spForm r K y z = y a := by
            rw [hz, map_add, spForm_single_right, spForm_single_right, Sum.swap_swap, hsb,
              add_zero]
          set c : K := y b / y a with hc
          have hg := hzmem c
          set g : StatedSp r K := ⟨spTrans z c, spTrans_mem_statedSp z c⟩ with hgdef
          set y₁ : Fin r ⊕ Fin r → K := spMat g *ᵥ y with hy₁
          have hy₁eq : y₁ = y + y b • z := by
            change spTransMat z c *ᵥ y = _
            rw [spTransMat_mulVec, hBz, hc, div_mul_cancel₀ _ ha0]
          have hy₁a : y₁ a = y a := by simp [hy₁eq, hza]
          have hy₁s : y₁ a.swap = y b := by simp [hy₁eq, hzs, hsa]
          have hy₁b : y₁ b = 0 := by
            simp only [hy₁eq, Pi.add_apply, Pi.smul_apply, hzb, smul_eq_mul, mul_one]
            exact CharTwo.add_self_eq_zero _
          have hsub : vsupp y₁ ⊆ insert a.swap ((vsupp y).erase b) := by
            intro i hi
            rw [Finset.mem_insert, Finset.mem_erase]
            by_cases his : i = a.swap
            · exact Or.inl his
            · right
              refine ⟨fun h => (mem_vsupp.1 hi) (by rw [h]; exact hy₁b), ?_⟩
              have hi0 := mem_vsupp.1 hi
              rw [hy₁eq] at hi0
              have hzi : z i = 0 := by
                by_cases hib : i = b
                · rw [hib] at hi
                  exact absurd hy₁b (mem_vsupp.1 hi)
                · simp [hz, his, hib]
              rw [mem_vsupp]
              simpa [hzi] using hi0
          have hcard₁ : (vsupp y₁).card ≤ n := by
            calc (vsupp y₁).card ≤ (insert a.swap ((vsupp y).erase b)).card :=
                  Finset.card_le_card hsub
              _ ≤ ((vsupp y).erase b).card + 1 := Finset.card_insert_le _ _
              _ = n := by
                rw [Finset.card_erase_of_mem hb, hn]
                omega
          have hy₁mem : y₁ ∈ rootSet H :=
            mem_rootSet_of_pair hH hx hxr hx0 n IH' hcard₁ (a := a) (by rwa [hy₁a])
              (by rw [hy₁s]; exact hb0)
          have h := mulVec_mem_rootSet hy₁mem (H.inv_mem hg)
          rwa [hy₁, spMat_inv_mulVec_mulVec] at h
  exact key _ y rfl

end Char2

theorem eq_top_of_rootSet_eq_univ {H : Subgroup (StatedSp r K)} (h : rootSet H = Set.univ) :
    H = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  have hg : (g : GL (Fin r ⊕ Fin r) K) ∈
      Subgroup.closure {g | ∃ (a : Fin r ⊕ Fin r → K) (c : K), g = spTrans a c} := by
    rw [← statedSp_eq_closure_spTrans]
    exact g.2
  have hle : Subgroup.closure {g | ∃ (a : Fin r ⊕ Fin r → K) (c : K), g = spTrans a c} ≤
      H.map (StatedSp r K).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    refine ⟨⟨spTrans a c, spTrans_mem_statedSp a c⟩, ?_, rfl⟩
    have ha : a ∈ rootSet H := h ▸ Set.mem_univ a
    exact ha c
  obtain ⟨g', hg', hgg'⟩ := hle hg
  have : g' = g := Subtype.ext hgg'
  rwa [this] at hg'

end CFSG.RankThree.PartOne.SEITZ4

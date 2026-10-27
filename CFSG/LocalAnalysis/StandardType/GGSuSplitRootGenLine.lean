module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus
public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlocks
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {n r ε p : ℕ} {K : Type} [Field K]

private theorem mem_lineCoords_inl {m i : Fin r} :
    (.inl i : HypIndex r ε) ∈ lineCoords m ↔ i = m := by
  simp [lineCoords]

private theorem mem_lineCoords_z (m : Fin r) (k : Fin ε) :
    (.inr (.inl k) : HypIndex r ε) ∈ lineCoords m := by
  simp [lineCoords]

private theorem mem_lineCoords_inr {m i : Fin r} :
    (.inr (.inr i) : HypIndex r ε) ∈ lineCoords m ↔ i = m := by
  simp [lineCoords]

private theorem exists_ne_of_not_mem_lineCoords {m : Fin r} {a : HypIndex r ε}
    (ha : a ∉ lineCoords m) : ∃ k : Fin r, k ≠ m ∧ (a = .inl k ∨ a = .inr (.inr k)) := by
  rcases a with i | k | i
  · exact ⟨i, fun h => ha ((mem_lineCoords_inl).mpr h), Or.inl rfl⟩
  · exact absurd (mem_lineCoords_z m k) ha
  · exact ⟨i, fun h => ha ((mem_lineCoords_inr).mpr h), Or.inr rfl⟩

private theorem splitEntries_eq_one_of_mem_lineCoords {ζ : K} {t : Fin r → ZMod p} {m : Fin r}
    (htm : t m = 0) {a : HypIndex r ε} (ha : a ∈ lineCoords m) :
    splitEntries (ε := ε) ζ t a = 1 := by
  rcases a with i | k | i
  · rw [mem_lineCoords_inl] at ha
    rw [ha]
    simp [splitEntries, htm]
  · simp [splitEntries]
  · rw [mem_lineCoords_inr] at ha
    rw [ha]
    simp [splitEntries, htm]

private theorem splitEntries_single_eq_one_of_not_mem {ζ : K} {m : Fin r}
    {a : HypIndex r ε} (ha : a ∉ lineCoords m) :
    splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p)) a = 1 := by
  rcases a with i | k | i
  · rw [mem_lineCoords_inl] at ha
    simp [splitEntries, Pi.single_eq_of_ne ha]
  · exact absurd (mem_lineCoords_z m k) ha
  · rw [mem_lineCoords_inr] at ha
    simp [splitEntries, Pi.single_eq_of_ne ha]

private theorem splitEntries_single_inl [Fact (1 < p)] {ζ : K} {k : Fin r} :
    splitEntries (ε := ε) ζ (Pi.single k (1 : ZMod p)) (.inl k) = ζ := by
  simp [splitEntries, ZMod.val_one]

private theorem splitEntries_single_inr [Fact (1 < p)] {ζ : K} {k : Fin r} :
    splitEntries (ε := ε) ζ (Pi.single k (1 : ZMod p)) (.inr (.inr k)) = ζ⁻¹ := by
  simp [splitEntries, ZMod.val_one]

private theorem splitEntries_single_ne_one [Fact (1 < p)] {ζ : K} {k : Fin r} (hζne : ζ ≠ 1)
    {o : HypIndex r ε} (ho : o = .inl k ∨ o = .inr (.inr k)) :
    splitEntries (ε := ε) ζ (Pi.single k (1 : ZMod p)) o ≠ 1 := by
  rcases ho with rfl | rfl
  · rw [splitEntries_single_inl]
    exact hζne
  · rw [splitEntries_single_inr]
    exact inv_ne_one.mpr hζne

private theorem sum_eq_sum_range {ι κ M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid M] (θ : ι → κ) (hθ : Function.Injective θ) (F : κ → M)
    (hF : ∀ x, x ∉ Set.range θ → F x = 0) : ∑ x, F x = ∑ i, F (θ i) := by
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image θ)) ?_).symm.trans ?_
  · intro x _ hx
    exact hF x (by simpa using hx)
  · rw [Finset.sum_image]
    intro x _ y _ h
    exact hθ h

theorem isHypBlockOn_conj {T : Set (HypIndex r ε)}
    {M N G : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hG : IsHypBlockOn T G)
    (hM : ∀ a b, (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T) → M a b = 0)
    (hN : ∀ a b, (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T) → N a b = 0)
    (hMN : M * N = 1) : IsHypBlockOn T (M * G * N) := by
  classical
  have hMG : ∀ a, a ∉ T → ∀ x, (M * G) a x = if x ∈ T then 0 else M a x := by
    intro a ha x
    rw [Matrix.mul_apply]
    by_cases hx : x ∈ T
    · rw [if_pos hx]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y ∈ T
      · rw [hM a y (Or.inr ⟨ha, hy⟩), zero_mul]
      · rw [hG y x (Or.inl hy), Matrix.one_apply_ne (fun h : y = x => hy (h ▸ hx)),
          mul_zero]
    · rw [if_neg hx, Finset.sum_eq_single x]
      · rw [hG x x (Or.inr hx), Matrix.one_apply_eq, mul_one]
      · intro y _ hyx
        by_cases hy : y ∈ T
        · rw [hM a y (Or.inr ⟨ha, hy⟩), zero_mul]
        · rw [hG y x (Or.inr hx), Matrix.one_apply_ne hyx, mul_zero]
      · intro hx'
        exact absurd (Finset.mem_univ x) hx'
  have hGN : ∀ b, b ∉ T → ∀ y, (G * N) y b = N y b := by
    intro b hb y
    rw [Matrix.mul_apply]
    by_cases hy : y ∈ T
    · refine Eq.trans (Finset.sum_eq_zero fun z _ => ?_) ?_
      · by_cases hz : z ∈ T
        · rw [hN z b (Or.inl ⟨hz, hb⟩), mul_zero]
        · rw [hG y z (Or.inr hz), Matrix.one_apply_ne (fun h : y = z => hz (h ▸ hy)),
            zero_mul]
      · rw [hN y b (Or.inl ⟨hy, hb⟩)]
    · rw [Finset.sum_eq_single y]
      · rw [hG y y (Or.inr hy), Matrix.one_apply_eq, one_mul]
      · intro z _ hzy
        by_cases hz : z ∈ T
        · rw [hG y z (Or.inl hy),
            Matrix.one_apply_ne (fun h : y = z => (h ▸ hy) hz), zero_mul]
        · rw [hG y z (Or.inr hz), Matrix.one_apply_ne (Ne.symm hzy), zero_mul]
      · intro hy'
        exact absurd (Finset.mem_univ y) hy'
  rintro a b (ha | hb)
  · rw [Matrix.mul_apply]
    have hterm : ∀ x, (M * G) a x * N x b = M a x * N x b := by
      intro x
      rw [hMG a ha x]
      by_cases hx : x ∈ T
      · rw [if_pos hx, zero_mul, hM a x (Or.inr ⟨ha, hx⟩), zero_mul]
      · rw [if_neg hx]
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Matrix.mul_apply, hMN]
  · rw [Matrix.mul_assoc, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun y _ => by rw [hGN b hb y]]
    rw [← Matrix.mul_apply, hMN]

private theorem lineBlock_le_centralizer (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : K}
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (m : Fin r) :
    lineBlock h m ≤ Subgroup.centralizer (torusFix τ (SlNsRootGen.negMap m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  rintro x ⟨v, hv, rfl⟩
  let t : Fin r → ZMod p := Multiplicative.toAdd v
  have htv : Multiplicative.ofAdd t = v := rfl
  have htm : t m = 0 := (SlNsRootGen.negMap_eq_self_iff hp2).mp hv
  have hgb : IsHypBlockOn (lineCoords m)
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := hg
  have hcomm : (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) * diagonal (splitEntries ζ t) =
      diagonal (splitEntries ζ t) *
        (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hD : splitEntries ζ t a = splitEntries ζ t b
    · rw [hD, mul_comm]
    · have hne : a ≠ b := fun hab => hD (by rw [hab])
      have hMab : (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 := by
        by_cases ha : a ∈ lineCoords m
        · by_cases hb : b ∈ lineCoords m
          · exact absurd (by rw [splitEntries_eq_one_of_mem_lineCoords htm ha,
              splitEntries_eq_one_of_mem_lineCoords htm hb]) hD
          · rw [hgb a b (Or.inr hb), Matrix.one_apply_ne hne]
        · rw [hgb a b (Or.inl ha), Matrix.one_apply_ne hne]
      rw [hMab, zero_mul, mul_zero]
  rw [← htv]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hτ t]
  exact hcomm.symm

private theorem centralizer_apply_eq_zero_of_separated (h : UnitaryFieldData 2 n K)
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (m : Fin r)
    {c : hypSU h r ε}
    (hc : c ∈ Subgroup.centralizer (torusFix τ (SlNsRootGen.negMap m))) {a b : HypIndex r ε}
    (hab : (a ∈ lineCoords m ∧ b ∉ lineCoords m) ∨
      (a ∉ lineCoords m ∧ b ∈ lineCoords m)) :
    (((c : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hζne : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨k, hkm, hk⟩ : ∃ k : Fin r, k ≠ m ∧
      ((a ∉ lineCoords m ∧ (a = .inl k ∨ a = .inr (.inr k))) ∨
        (b ∉ lineCoords m ∧ (b = .inl k ∨ b = .inr (.inr k)))) := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨k, hkm, hk⟩ := exists_ne_of_not_mem_lineCoords (m := m) hb
      exact ⟨k, hkm, Or.inr ⟨hb, hk⟩⟩
    · obtain ⟨k, hkm, hk⟩ := exists_ne_of_not_mem_lineCoords (m := m) ha
      exact ⟨k, hkm, Or.inl ⟨ha, hk⟩⟩
  let t : Fin r → ZMod p := Pi.single k 1
  have htm : t m = 0 := by
    simp only [t, Pi.single_eq_of_ne (Ne.symm hkm)]
  have htfix : SlNsRootGen.negMap m t = t :=
    (SlNsRootGen.negMap_eq_self_iff hp2).mpr htm
  have hxmem : τ (Multiplicative.ofAdd t) ∈ torusFix τ (SlNsRootGen.negMap m) :=
    ⟨Multiplicative.ofAdd t, htfix, rfl⟩
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc) _ hxmem
  have hcD : (((c : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) * diagonal (splitEntries ζ t) =
      diagonal (splitEntries ζ t) *
        (((c : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    have hmat := congrArg (fun y : hypSU h r ε =>
      (((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))) hcomm
    simpa only [Subgroup.coe_mul, Units.val_mul, hτ t] using hmat.symm
  have hDne : splitEntries ζ t a ≠ splitEntries ζ t b := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hda : splitEntries ζ t a = 1 := splitEntries_eq_one_of_mem_lineCoords htm ha
      have hdb : splitEntries ζ t b ≠ 1 := by
        rcases hk with ⟨ha', _⟩ | ⟨_, hk⟩
        · exact absurd ha ha'
        · exact splitEntries_single_ne_one hζne hk
      rw [hda]
      exact fun h => hdb h.symm
    · have hdb : splitEntries ζ t b = 1 := splitEntries_eq_one_of_mem_lineCoords htm hb
      have hda : splitEntries ζ t a ≠ 1 := by
        rcases hk with ⟨_, hk⟩ | ⟨hb', _⟩
        · exact splitEntries_single_ne_one hζne hk
        · exact absurd hb hb'
      rw [hdb]
      exact hda
  exact TauCeti.apply_eq_zero_of_commute_diagonal hcD.symm hDne

private theorem lineBlock_normal (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (m : Fin r) :
    ((lineBlock h m).subgroupOf
      (Subgroup.centralizer (torusFix τ (SlNsRootGen.negMap m)))).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hle := lineBlock_le_centralizer h hp hp2 hτ m
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have hconj : ∀ (d : hypSU h r ε),
      d ∈ Subgroup.centralizer (torusFix τ (SlNsRootGen.negMap m)) →
      ∀ g ∈ lineBlock h m, d * g * d⁻¹ ∈ lineBlock h m := by
    intro d hd g hg
    have hdM : ∀ a b, (a ∈ lineCoords m ∧ b ∉ lineCoords m) ∨
        (a ∉ lineCoords m ∧ b ∈ lineCoords m) →
        (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 :=
      fun a b hab => centralizer_apply_eq_zero_of_separated h hp hp2 hζ hτ m hd hab
    have hdN : ∀ a b, (a ∈ lineCoords m ∧ b ∉ lineCoords m) ∨
        (a ∉ lineCoords m ∧ b ∈ lineCoords m) →
        (((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 :=
      fun a b hab => centralizer_apply_eq_zero_of_separated h hp hp2 hζ hτ m
        (Subgroup.inv_mem _ hd) hab
    have hgblock : IsHypBlockOn (lineCoords m)
        (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := hg
    have hMN : (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      have hmul : d * d⁻¹ = 1 := mul_inv_cancel d
      have hmat := congrArg (fun y : hypSU h r ε =>
        (((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))) hmul
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one] using hmat
    have hres := isHypBlockOn_conj hgblock hdM hdN hMN
    rw [lineBlock, mem_hypBlock]
    have hmat : ((((d * g * d⁻¹) : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) =
        (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hmat]
    exact hres
  intro x
  constructor
  · exact hconj c hc x
  · intro hx
    have h := hconj c⁻¹ (Subgroup.inv_mem _ hc) (c * x * c⁻¹) hx
    convert h using 1
    group

private theorem finOne_const_injective (m : Fin r) :
    Function.Injective (fun _ : Fin 1 => m) :=
  fun i j _ => Subsingleton.elim i j

private theorem extHyp_line_range (h : UnitaryFieldData 2 n K) (m : Fin r) :
    (extHyp h (hypMap (fun _ : Fin 1 => m) (id : Fin ε → Fin ε))
        (hypMap_injective (finOne_const_injective m) (fun _ _ h => h))
        (fun a => hypMap_partner _ _ a)).range = lineBlock (ε := ε) h m := by
  let θ : HypIndex 1 ε → HypIndex r ε := hypMap (fun _ : Fin 1 => m) (id : Fin ε → Fin ε)
  have hθ : Function.Injective θ :=
    hypMap_injective (finOne_const_injective m) (fun _ _ h => h)
  have hpθ : ∀ a, θ (hypPartner a) = hypPartner (θ a) := fun a => hypMap_partner _ _ a
  have hrange : ∀ a, a ∈ lineCoords m ↔ a ∈ Set.range θ := by
    intro a
    constructor
    · rintro (rfl | ⟨k, rfl⟩ | rfl)
      · exact ⟨.inl 0, by simp [θ, hypMap]⟩
      · exact ⟨.inr (.inl k), by simp [θ, hypMap]⟩
      · exact ⟨.inr (.inr 0), by simp [θ, hypMap]⟩
    · rintro ⟨i, rfl⟩
      rcases i with i | k | i
      · have hi : i = 0 := Subsingleton.elim i 0
        rw [hi]
        simp [θ, hypMap, lineCoords]
      · simp [θ, hypMap, lineCoords]
      · have hi : i = 0 := Subsingleton.elim i 0
        rw [hi]
        simp [θ, hypMap, lineCoords]
  have hθJ : ∀ i j, hypGram r ε K (θ i) (θ j) = hypGram 1 ε K i j := by
    intro i j
    rw [hypGram_apply, hypGram_apply]
    by_cases h : j = hypPartner i
    · have h' : θ j = hypPartner (θ i) := by rw [h, hpθ]
      rw [if_pos h, if_pos h']
    · have h' : θ j ≠ hypPartner (θ i) := by
        intro hh
        rw [← hpθ] at hh
        exact h (hθ hh)
      rw [if_neg h, if_neg h']
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [lineBlock, mem_hypBlock]
    intro a b hab
    rw [coe_extHyp]
    rcases hab with ha | hb
    · rw [extId_apply_of_not_left _ _ _ (fun h => ha ((hrange a).mpr h))]
    · rw [extId_apply_of_not_right _ _ _ _ (fun h => hb ((hrange b).mpr h))]
  · intro g hg
    let G : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)
    let G' : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K := fun i j => G (θ i) (θ j)
    have hGblock : IsHypBlockOn (lineCoords m) G := hg
    have hGunit : ((G.map h.bar)ᵀ * hypGram r ε K * G) = hypGram r ε K :=
      (mem_hypSU.mp g.2).1
    have hGdet : G.det = 1 := (mem_hypSU.mp g.2).2
    have hGext : G = extId θ hθ G' := by
      ext a b
      by_cases ha : a ∈ Set.range θ
      · obtain ⟨i, rfl⟩ := ha
        by_cases hb : b ∈ Set.range θ
        · obtain ⟨j, rfl⟩ := hb
          rw [extId_apply_map]
        · rw [extId_apply_of_not_right _ _ _ _ hb]
          exact hGblock (θ i) b (Or.inr (fun h => hb ((hrange b).mp h)))
      · rw [extId_apply_of_not_left _ _ _ ha]
        exact hGblock a b (Or.inl (fun h => ha ((hrange a).mp h)))
    have hsum_eq : ∀ i j, ((G.map h.bar)ᵀ * hypGram r ε K * G) (θ i) (θ j) =
        ((G'.map h.bar)ᵀ * hypGram 1 ε K * G') i j := by
      intro i j
      have houter : ∀ a : HypIndex r ε, a ∉ Set.range θ →
          (∑ y, h.bar (G y (θ i)) * hypGram r ε K y a) * G a (θ j) = 0 := by
        intro a ha
        rw [hGblock a (θ j) (Or.inl (fun h => ha ((hrange a).mp h)))]
        rw [Matrix.one_apply_ne (fun h : a = θ j => ha (h ▸ ⟨j, rfl⟩)), mul_zero]
      have hinner : ∀ a, ∀ b : HypIndex r ε, b ∉ Set.range θ →
          h.bar (G b (θ i)) * hypGram r ε K b a = 0 := by
        intro a b hb
        rw [hGblock b (θ i) (Or.inl (fun h => hb ((hrange b).mp h)))]
        rw [Matrix.one_apply_ne (fun h : b = θ i => hb (h ▸ ⟨i, rfl⟩)), map_zero, zero_mul]
      calc ((G.map h.bar)ᵀ * hypGram r ε K * G) (θ i) (θ j)
          = ∑ a, (∑ y, h.bar (G y (θ i)) * hypGram r ε K y a) * G a (θ j) := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
        _ = ∑ a, (∑ b, h.bar (G (θ b) (θ i)) *
              hypGram r ε K (θ b) (θ a)) * G (θ a) (θ j) := by
            rw [sum_eq_sum_range θ hθ
              (fun a => (∑ y, h.bar (G y (θ i)) * hypGram r ε K y a) * G a (θ j)) houter]
            refine Finset.sum_congr rfl fun a _ => ?_
            exact congrArg (fun z => z * G (θ a) (θ j))
              (sum_eq_sum_range θ hθ
                (fun b => h.bar (G b (θ i)) * hypGram r ε K b (θ a)) (hinner (θ a)))
        _ = ∑ a, (∑ b, h.bar (G' b i) * hypGram 1 ε K b a) * G' a j := by
            change (∑ a, (∑ b, h.bar (G (θ b) (θ i)) *
              hypGram r ε K (θ b) (θ a)) * G (θ a) (θ j)) = _
            refine Finset.sum_congr rfl fun a _ => ?_
            have h1 : (∑ b, h.bar (G (θ b) (θ i)) * hypGram r ε K (θ b) (θ a)) =
                ∑ b, h.bar (G' b i) * hypGram 1 ε K b a := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [hθJ b a]
            rw [h1]
        _ = ((G'.map h.bar)ᵀ * hypGram 1 ε K * G') i j := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    have hunit : ((G'.map h.bar)ᵀ * hypGram 1 ε K * G') = hypGram 1 ε K := by
      ext i j
      rw [← hsum_eq i j, hGunit, hθJ i j]
    have hdet : G'.det = 1 := by
      rw [← det_extId θ hθ G', ← hGext]
      exact hGdet
    have hdetne : G'.det ≠ 0 := by
      rw [hdet]
      exact one_ne_zero
    let g' : GL (HypIndex 1 ε) K := Matrix.GeneralLinearGroup.mkOfDetNeZero G' hdetne
    have hG'mem : g' ∈ hypSU h 1 ε := mem_hypSU.mpr ⟨hunit, hdet⟩
    refine ⟨⟨g', hG'mem⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_extHyp]
    exact hGext.symm

private theorem nonempty_lineBlock_mulEquiv (h : UnitaryFieldData 2 n K) (m : Fin r) :
    Nonempty (lineBlock (ε := ε) h m ≃* hypSU h (1 : ℕ) ε) := by
  let θ : HypIndex 1 ε → HypIndex r ε := hypMap (fun _ : Fin 1 => m) (id : Fin ε → Fin ε)
  have hθ : Function.Injective θ :=
    hypMap_injective (finOne_const_injective m) (fun _ _ h => h)
  have hpθ : ∀ a, θ (hypPartner a) = hypPartner (θ a) := fun a => hypMap_partner _ _ a
  have hrange := extHyp_line_range (ε := ε) h m
  exact ⟨((MonoidHom.ofInjective (extHyp_injective h θ hθ hpθ)).trans
    (MulEquiv.subgroupCongr hrange)).symm⟩

private theorem isQuasisimple_lineBlock (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (hε : ε ≤ 1) (m : Fin r) :
    CFSG.Assembly.IsQuasisimple (lineBlock (ε := ε) h m) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn2 : 2 ≤ n := by
    have hn1 : 1 ≤ n := h.one_le
    by_contra hn
    have hn1' : n = 1 := by omega
    subst hn1'
    have hp1 : p ∣ 1 := by simpa using hpq
    have hp_le : p ≤ 1 := Nat.le_of_dvd one_pos hp1
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have hmq : (2 * 1 + 1, 2 ^ n) ≠ (3, 2) := by
    rintro hEq
    have h2 : 2 ^ n = 2 := congrArg Prod.snd hEq
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hqSU : CFSG.Open.IsQuasisimple (hypSU h 1 ε) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · exact (CFSG.AGLEmbedding.LeviBlock.hypSU_facts_two h hn2).1
    · exact (CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le (s := 1) (ε := 1) h
        (by norm_num) hmq).1
  obtain ⟨e⟩ := nonempty_lineBlock_mulEquiv (ε := ε) (h := h) (m := m)
  exact hqSU.of_mulEquiv e

theorem isComponentOf_lineBlock (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (hε : ε ≤ 1)
    (m : Fin r) :
    IsComponentOf (lineBlock h m) (Subgroup.centralizer (torusFix τ (SlNsRootGen.negMap m))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem := lineBlock_le_centralizer h hp hp2 hτ m
  have hnorm := lineBlock_normal h hp hp2 hζ hτ m
  have hq := isQuasisimple_lineBlock h hp hpq hε m
  exact ⟨hmem, IsSubnormal.step hmem hnorm (IsSubnormal.refl _), hq⟩

theorem dvd_card_lineBlock (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε}
    (hτ : IsSplitTorus h ζ τ) (m : Fin r) :
    p ∣ Nat.card (lineBlock (ε := ε) h m) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hζne : ζ ≠ 1 := hζ.ne_one hp.one_lt
  let v : Fin r → ZMod p := Pi.single m 1
  let x : hypSU h r ε := τ (Multiplicative.ofAdd v)
  have hxmem : x ∈ lineBlock h m := by
    rw [lineBlock, mem_hypBlock]
    intro a b hab
    rw [hτ v]
    by_cases h : a = b
    · rw [h, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rcases hab with hab | hab
      · exact splitEntries_single_eq_one_of_not_mem (ζ := ζ) (m := m) (by rwa [h] at hab)
      · exact splitEntries_single_eq_one_of_not_mem (ζ := ζ) (m := m) hab
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hxpow : x ^ p = 1 := by
    have hv : (p : ℕ) • v = 0 := by
      ext k
      simp only [v, Pi.smul_apply, Pi.single_apply]
      by_cases hk : k = m
      · subst hk
        simp
      · simp [hk]
    have h1 : (Multiplicative.ofAdd v : Multiplicative (Fin r → ZMod p)) ^ p = 1 := by
      rw [← ofAdd_nsmul, hv]
      rfl
    calc x ^ p = τ ((Multiplicative.ofAdd v) ^ p) := (map_pow τ _ p).symm
      _ = τ 1 := by rw [h1]
      _ = 1 := map_one τ
  have hxne : x ≠ 1 := by
    intro hx
    have hmat := congrArg (fun y : hypSU h r ε =>
      (((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))) hx
    have hentry := congrFun (congrFun hmat (.inl m)) (.inl m)
    rw [hτ v, Matrix.diagonal_apply_eq] at hentry
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at hentry
    apply hζne
    simpa [v, splitEntries, ZMod.val_one] using hentry
  have hxord : orderOf x = p := orderOf_eq_prime hxpow hxne
  have hdvd := Subgroup.orderOf_dvd_natCard (lineBlock h m) hxmem
  rwa [hxord] at hdvd

end CFSG.StandardType.SuSplitRootGen

end

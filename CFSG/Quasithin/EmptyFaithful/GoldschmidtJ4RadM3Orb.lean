module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocConj
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadGL
public import Certificates.Certificate4178

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

@[expose] noncomputable def wordEl (w : List ℤ) : J := (w.map XJ).prod

theorem wordEl_mem {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) : wordEl w ∈ Hj := by
  unfold wordEl
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
  exact XJ_mem (hw ℓ hℓ)

theorem wordEl_conj (hM : MatFacts) {w : List ℤ}
    (hw : ∀ ℓ ∈ w, ℓ ∈ letters) (c : ℕ) :
    wordEl w * eta uJ 11 c * (wordEl w)⁻¹ = eta uJ 11 (w.foldr act c) :=
  word_conj XJ act w (fun ℓ hℓ c => hX_all hM (hw ℓ hℓ) c) c

theorem mem_wordImgF (w : List ℤ) : ∀ {W : Finset ℕ} {c : ℕ},
    c ∈ wordImgF w W ↔ ∃ d ∈ W, w.reverse.foldr act d = c := by
  induction w with
  | nil =>
    intro W c
    refine ⟨fun h => ⟨c, h, rfl⟩, ?_⟩
    rintro ⟨d, hd, rfl⟩
    exact hd
  | cons ℓ w ih =>
    intro W c
    simp only [wordImgF]
    rw [ih]
    simp only [Finset.mem_image, List.reverse_cons, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, e⟩
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, e⟩

@[expose] noncomputable def NV : Subgroup J := Hj ⊓ Subgroup.normalizer (V0 : Set J)

@[expose] noncomputable def CV : Subgroup J := Hj ⊓ Subgroup.centralizer (V0 : Set J)

theorem CV_le_NV : CV ≤ NV :=
  inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (V0 : Set J))

theorem CV_le_Hj : CV ≤ Hj := inf_le_left

theorem NV_le_Hj : NV ≤ Hj := inf_le_left

theorem eta_mem_V0 {c : ℕ} (hM : MatFacts) (hc : c ∈ V0L) :
    eta uJ 11 c ∈ V0 := (mem_V0_iff hM).2 ⟨c, hc, rfl⟩

section Trio

theorem trio_xor :
    ∀ W ∈ trioL, 0 ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W :=
  fun _ hW => (trioL_props hW).2.2.2

theorem conjSub_maskSub (hM : MatFacts) {h : J} {W W' : List ℕ}
    (hW : Img h W W') (h0 : 0 ∈ W)
    (hx : ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W) (h0' : 0 ∈ W')
    (hx' : ∀ x ∈ W', ∀ y ∈ W', x ^^^ y ∈ W') :
    conjSub h (maskSub W) = maskSub W' := by
  ext x
  rw [mem_conjSub, mem_maskSub_iff hM h0 hx, mem_maskSub_iff hM h0' hx']
  constructor
  · rintro ⟨c, hc, e⟩
    obtain ⟨c', hc', e'⟩ := hW.1 c hc
    refine ⟨c', hc', ?_⟩
    rw [← e', ← e]
    group
  · rintro ⟨c', hc', e⟩
    obtain ⟨c, hc, e'⟩ := hW.2 c' hc'
    refine ⟨c, hc, ?_⟩
    rw [e, ← e']
    group

theorem V0L_lt : ∀ c ∈ V0L, c < 2048 := by
  intro c hc
  simp only [V0L, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem V0_maskList (hM : MatFacts) : MaskList V0 V0L := by
  intro c
  constructor
  · intro hc
    exact ⟨V0L_lt c hc, eta_mem_V0 hM hc⟩
  · rintro ⟨hc, h⟩
    obtain ⟨c', hc', e⟩ := (mem_V0_iff hM).1 h
    have := eta_inj' hM hc (V0L_lt c' hc') e
    rw [this]
    exact hc'

theorem V0_le_Eg' (hM : MatFacts) {x : J} (hx : x ∈ V0) :
    x ∈ Eg uJ 11 := by
  obtain ⟨c, -, rfl⟩ := (mem_V0_iff hM).1 hx
  exact eta_mem_Eg 11 le_rfl c

theorem card_V0 (hM : MatFacts) : Nat.card ↥V0 = 8 := by
  have := MaskList.card hM (fun x hx => V0_le_Eg' hM hx) (V0_maskList hM) (by decide)
  simpa [V0L] using this

theorem V0_comm (hM : MatFacts) :
    ∀ a ∈ V0, ∀ b ∈ V0, a * b = b * a := fun _ ha _ hb =>
  Eg_comm (elem_uJ hM) (V0_le_Eg' hM ha) (V0_le_Eg' hM hb)

theorem V0_sq (hM : MatFacts) : ∀ a ∈ V0, a * a = 1 :=
  fun _ ha => Eg_sq (elem_uJ hM) (V0_le_Eg' hM ha)

theorem card_mulAut_V0 (hM : MatFacts) :
    Nat.card (MulAut ↥V0) = 168 :=
  card_mulAut_subgroup_eight V0 (V0_comm hM) (V0_sq hM) (card_V0 hM)

theorem mem_V0F_iff {d : ℕ} : d ∈ V0F ↔ d ∈ V0L := by
  rw [← V0L_toFinset, List.mem_toFinset]

end Trio

section Idx

theorem centralizer_inf_NV : NV ⊓ Subgroup.centralizer (V0 : Set J) = CV := by
  ext x
  simp only [NV, CV, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, Subgroup.centralizer_le_normalizer (V0 : Set J) h3⟩, h3⟩

theorem CV_le_normalizer : NV ≤ Subgroup.normalizer (V0 : Set J) := inf_le_right

@[expose] def TrioSet : Set (Subgroup J) := {A | ∃ W ∈ trioL, A = maskSub W}

theorem conj_V0_mem_TrioSet
    (hM : MatFacts) :
    ∀ h ∈ Hj, conjSub h V0 ∈ TrioSet := by
  intro h hh
  obtain ⟨W', hW', himg⟩ := (trio_conj hM hh).1 V0L trio_prop.1
  refine ⟨W', hW', ?_⟩
  rw [V0_eq_maskSub hM]
  exact conjSub_maskSub hM himg V0L_closed.1 V0L_closed.2 (trio_xor W' hW').1
    (trio_xor W' hW').2

theorem TrioSet_eq : TrioSet = maskSub '' trioL := by
  ext A
  simp only [TrioSet, Set.mem_setOf_eq, Set.mem_image]
  exact ⟨fun ⟨W, hW, e⟩ => ⟨W, hW, e.symm⟩, fun ⟨W, hW, e⟩ => ⟨W, hW, e.symm⟩⟩

theorem TrioSet_finite : TrioSet.Finite := by
  rw [TrioSet_eq]
  exact trioL_finite_ncard.1.image _

theorem ncard_TrioSet_le : TrioSet.ncard ≤ 3795 := by
  rw [TrioSet_eq]
  exact (Set.ncard_image_le trioL_finite_ncard.1).trans trioL_finite_ncard.2

theorem idx_NV_le
    (hM : MatFacts) :
    (NV.subgroupOf Hj).index ≤ 3795 :=
  (index_normalizer_le Hj V0 TrioSet (conj_V0_mem_TrioSet hM)).trans ncard_TrioSet_le

theorem wordImgF_sub
    (hM : MatFacts) {u v : List ℤ} (hu : ∀ ℓ ∈ u, ℓ ∈ letters) (hv : ∀ ℓ ∈ v, ℓ ∈ letters)
    (hn : (wordEl u.reverse)⁻¹ * wordEl v.reverse ∈ Subgroup.normalizer (V0 : Set J)) :
    wordImgF v V0F ⊆ wordImgF u V0F := by
  have hrev : ∀ {w : List ℤ}, (∀ ℓ ∈ w, ℓ ∈ letters) → ∀ ℓ ∈ w.reverse, ℓ ∈ letters :=
    fun hw ℓ hℓ => hw ℓ (List.mem_reverse.1 hℓ)
  intro c hc
  have hcl : c < 2048 :=
    (Certificates.certificate4174.2.2.2.2.2.1 _ ⟨v, hv, rfl⟩).2.2.1 c hc
  obtain ⟨d, hd, rfl⟩ := (mem_wordImgF v).1 hc
  have hdV : eta uJ 11 d ∈ V0 := eta_mem_V0 hM (mem_V0F_iff.1 hd)
  obtain ⟨d', hd', e⟩ := (mem_V0_iff hM).1 ((Subgroup.mem_normalizer_iff.mp hn (eta uJ 11 d)).mp hdV)
  have key : eta uJ 11 (v.reverse.foldr act d) = eta uJ 11 (u.reverse.foldr act d') := by
    rw [← wordEl_conj hM (hrev hv), ← wordEl_conj hM (hrev hu), ← e]
    group
  have hc' : u.reverse.foldr act d' ∈ wordImgF u V0F :=
    (mem_wordImgF u).2 ⟨d', mem_V0F_iff.2 hd', rfl⟩
  have hlt' := (Certificates.certificate4174.2.2.2.2.2.1 _ ⟨u, hu, rfl⟩).2.2.1 _ hc'
  rw [eta_inj' hM hcl hlt' key]
  exact hc'

theorem idx_NV_ge (hM : MatFacts) :
    3795 ≤ (NV.subgroupOf Hj).index := by
  have hT := Certificates.certificate4174.2.2.2.2.1
  have hfin : TrioOct.Finite := Set.finite_of_ncard_ne_zero (by rw [hT]; decide)
  have : Finite ↥TrioOct := hfin.to_subtype
  let e : Fin 3795 ≃ ↥TrioOct :=
    (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hT])).symm
  have hw : ∀ i, ∃ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) ∧ (e i : Finset ℕ) = wordImgF w V0F :=
    fun i => (e i).2
  choose w hwl hwe using hw
  refine index_ge_of_injection Hj NV 3795 (fun i => wordEl (w i).reverse)
    (fun i => wordEl_mem fun ℓ hℓ => hwl i ℓ (List.mem_reverse.1 hℓ)) ?_
  intro i j hij
  have hij' : (wordEl (w i).reverse)⁻¹ * wordEl (w j).reverse ∈
      Hj ⊓ Subgroup.normalizer (V0 : Set J) := hij
  have hn := (Subgroup.mem_inf.mp hij').2
  have hn' : (wordEl (w j).reverse)⁻¹ * wordEl (w i).reverse ∈
      Subgroup.normalizer (V0 : Set J) := by
    have := (Subgroup.normalizer (V0 : Set J)).inv_mem hn
    rwa [mul_inv_rev, inv_inv] at this
  have hs := (wordImgF_sub hM (hwl i) (hwl j) hn).antisymm (wordImgF_sub hM (hwl j) (hwl i) hn')
  apply e.injective
  apply Subtype.ext
  rw [hwe i, hwe j]
  exact hs.symm

theorem mem_normalizer_V0 (hM : MatFacts) {g : J}
    (h1 : g * eta uJ 11 422 * g⁻¹ ∈ V0) (h2 : g * eta uJ 11 553 * g⁻¹ ∈ V0)
    (h3 : g * eta uJ 11 1131 * g⁻¹ ∈ V0) : g ∈ Subgroup.normalizer (V0 : Set J) := by
  have hconj : ∀ y ∈ Subgroup.closure ({eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131} : Set J),
      g * y * g⁻¹ ∈ V0 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact V0.one_mem
    | mul y z _ _ hy hz =>
      have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [e]
      exact V0.mul_mem hy hz
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact V0.inv_mem hy
  have hsub : ((conjSub g V0 : Subgroup J) : Set J) ⊆ (V0 : Set J) := by
    intro x hx
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact hconj _ (mem_conjSub.mp hx)
  have heq := Set.eq_of_subset_of_ncard_le hsub (ncard_conjSub g V0).ge
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hconj h
  · intro hh
    have hh' : g * h * g⁻¹ ∈ ((conjSub g V0 : Subgroup J) : Set J) := by
      rw [heq]
      exact hh
    have := mem_conjSub.mp hh'
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rwa [e] at this

theorem conjAut_NV_surjective
    (hM : MatFacts) :
    Function.Surjective (conjAut V0 NV CV_le_normalizer) := by
  intro σ
  let el : ∀ p, p ∈ V0L → ↥V0 := fun p hp => ⟨eta uJ 11 p, eta_mem_V0 hM hp⟩
  have hmask : ∀ x : ↥V0, ∃ c ∈ V0L, (x : J) = eta uJ 11 c := fun x => (mem_V0_iff hM).1 x.2
  have hne : ∀ p (hp : p ∈ V0L) q (hq : q ∈ V0L), p ≠ q → ∀ a b : ℕ,
      (σ (el p hp) : J) = eta uJ 11 a → (σ (el q hq) : J) = eta uJ 11 b → a ≠ b := by
    intro p hp q hq hpq a b ea eb hab
    apply hpq
    have hσ : σ (el p hp) = σ (el q hq) := Subtype.ext (by rw [ea, eb, hab])
    have := congrArg Subtype.val (σ.injective hσ)
    exact eta_inj' hM (V0L_lt p hp) (V0L_lt q hq) this
  have m0 : (0 : ℕ) ∈ V0L := by decide
  have m1 : (422 : ℕ) ∈ V0L := by decide
  have m2 : (553 : ℕ) ∈ V0L := by decide
  have m3 : (1131 : ℕ) ∈ V0L := by decide
  have m4 : (911 : ℕ) ∈ V0L := by decide
  have e0 : (σ (el 0 m0) : J) = eta uJ 11 0 := by
    have : el 0 m0 = 1 := Subtype.ext (eta_zero _ _)
    rw [this, map_one, eta_zero]
    rfl
  obtain ⟨a, ha, ea⟩ := hmask (σ (el 422 m1))
  obtain ⟨b, hb, eb⟩ := hmask (σ (el 553 m2))
  obtain ⟨c, hc, ec⟩ := hmask (σ (el 1131 m3))
  have e4 : (σ (el 911 m4) : J) = eta uJ 11 (a ^^^ b) := by
    have : el 911 m4 = el 422 m1 * el 553 m2 :=
      Subtype.ext (by
        have h911 : (422 : ℕ) ^^^ 553 = 911 := by decide
        change eta uJ 11 911 = eta uJ 11 422 * eta uJ 11 553
        rw [eta_mul_eta hM, h911])
    rw [this, map_mul, Subgroup.coe_mul, ea, eb, eta_mul_eta hM]
  obtain ⟨w, hw, w1, w2, w3⟩ := Certificates.certificate4178 a (mem_V0F_iff.2 ha)
    b (mem_V0F_iff.2 hb) c (mem_V0F_iff.2 hc)
    (hne 422 m1 0 m0 (by decide) a 0 ea e0) (hne 553 m2 0 m0 (by decide) b 0 eb e0)
    (hne 553 m2 422 m1 (by decide) b a eb ea) (hne 1131 m3 0 m0 (by decide) c 0 ec e0)
    (hne 1131 m3 422 m1 (by decide) c a ec ea) (hne 1131 m3 553 m2 (by decide) c b ec eb)
    (hne 1131 m3 911 m4 (by decide) c (a ^^^ b) ec e4)
  have g1 : wordEl w * eta uJ 11 422 * (wordEl w)⁻¹ = σ (el 422 m1) := by
    rw [wordEl_conj hM hw, w1, ea]
  have g2 : wordEl w * eta uJ 11 553 * (wordEl w)⁻¹ = σ (el 553 m2) := by
    rw [wordEl_conj hM hw, w2, eb]
  have g3 : wordEl w * eta uJ 11 1131 * (wordEl w)⁻¹ = σ (el 1131 m3) := by
    rw [wordEl_conj hM hw, w3, ec]
  have hN : wordEl w ∈ NV :=
    Subgroup.mem_inf.mpr ⟨wordEl_mem hw, mem_normalizer_V0 hM (g1 ▸ (σ (el 422 m1)).2)
      (g2 ▸ (σ (el 553 m2)).2) (g3 ▸ (σ (el 1131 m3)).2)⟩
  refine ⟨⟨wordEl w, hN⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  have key : ∀ y (hy : y ∈ Subgroup.closure
      ({eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131} : Set J)),
      wordEl w * y * (wordEl w)⁻¹ = (σ ⟨y, hy⟩ : J) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact g1
      · exact g2
      · exact g3
    | one =>
      have : (⟨1, Subgroup.one_mem _⟩ : ↥V0) = 1 := rfl
      rw [mul_one, mul_inv_cancel, this, map_one]
      rfl
    | mul y z hy hz ihy ihz =>
      have : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : ↥V0) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      have e : wordEl w * (y * z) * (wordEl w)⁻¹ =
          (wordEl w * y * (wordEl w)⁻¹) * (wordEl w * z * (wordEl w)⁻¹) := by group
      rw [this, map_mul, Subgroup.coe_mul, e, ihy, ihz]
    | inv y hy ih =>
      have : (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : ↥V0) = (⟨y, hy⟩ : ↥V0)⁻¹ := rfl
      have e : wordEl w * y⁻¹ * (wordEl w)⁻¹ = (wordEl w * y * (wordEl w)⁻¹)⁻¹ := by group
      rw [this, map_inv, Subgroup.coe_inv, e, ih]
  obtain ⟨x, hx⟩ := x
  exact key x hx

theorem idx_CV_NV
    (hM : MatFacts) :
    (CV.subgroupOf NV).index = 168 := by
  have h := index_centralizer_eq V0 NV CV_le_normalizer
  rw [centralizer_inf_NV] at h
  rw [h, MonoidHom.range_eq_top.mpr (conjAut_NV_surjective hM), Subgroup.card_top,
    card_mulAut_V0 hM]

theorem idx_eq
    (hM : MatFacts) :
    (NV.subgroupOf Hj).index = 3795 ∧ (CV.subgroupOf NV).index = 168 ∧
      (CV.subgroupOf Hj).index = 637560 := by
  have hm : (CV.subgroupOf NV).index * (NV.subgroupOf Hj).index = (CV.subgroupOf Hj).index :=
    Subgroup.relIndex_mul_relIndex CV NV Hj CV_le_NV NV_le_Hj
  have hq := idx_CV_NV hM
  have hi : (NV.subgroupOf Hj).index = 3795 := le_antisymm (idx_NV_le hM) (idx_NV_ge hM)
  refine ⟨hi, hq, ?_⟩
  rw [← hm, hq, hi]

theorem card_CV
    (hF : J4Facts) :
    Nat.card ↥CV = 786432 := by
  have hM := hF.mat
  have h := card_mul_relIndex Hj CV CV_le_Hj
  rw [(idx_eq hM).2.2, card_Hj hF] at h
  generalize Nat.card ↥CV = c at h ⊢
  omega

theorem trio_orbit
    (hM : MatFacts) :
    ∀ W ∈ trioL, ∃ h ∈ Hj, maskSub W = conjSub h V0 := by
  have hidx : 3795 ≤ {A : Subgroup J | ∃ h ∈ Hj, A = conjSub h V0}.ncard := by
    have := index_normalizer_le Hj V0 {A : Subgroup J | ∃ h ∈ Hj, A = conjSub h V0}
      (fun h hh => ⟨h, hh, rfl⟩)
    rw [← (idx_eq hM).1]
    exact this
  have hsub : {A : Subgroup J | ∃ h ∈ Hj, A = conjSub h V0} ⊆ TrioSet := by
    rintro A ⟨h, hh, rfl⟩
    exact conj_V0_mem_TrioSet hM h hh
  have heq := Set.eq_of_subset_of_ncard_le hsub (ncard_TrioSet_le.trans hidx) TrioSet_finite
  intro W hW
  have : maskSub W ∈ TrioSet := ⟨W, hW, rfl⟩
  rw [← heq] at this
  obtain ⟨h, hh, e⟩ := this
  exact ⟨h, hh, e⟩

end Idx

end CFSG.Quasithin.J4Rad

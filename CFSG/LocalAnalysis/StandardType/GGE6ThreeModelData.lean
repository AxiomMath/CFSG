module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

structure GGE6ThreeData {L' : Type} [Group L'] (Z : Subgroup L') (A : Subgroup (MulAut L'))
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L') : Prop where
  injective : Function.Injective Φ
  range : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6
  comm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s
  le : ∀ z ∈ Z, Odd (orderOf z) → z ∈ T
  fixed : ∀ a ∈ A, ∀ t ∈ T, a t = t
  stable : ∀ i, ∀ t ∈ T, w i * t * (w i)⁻¹ ∈ T
  coboundary : ∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ T ∧ (w i * (a (w i))⁻¹) ^ 3 = 1
  act : ∀ i (a : A), ∃ b : A, MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b ∧
    Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a))
  torus : ∀ x ∈ NoOffRest.hypE6, ∃ t ∈ T, t ^ 3 = 1 ∧ ∃ b : A, MulAut.conj t = (b : MulAut L') ∧
    Multiplicative.toAdd (Φ b) = x
  inner : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
    ∃ u : WeylGroup .E6, ∀ a b : A,
      (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
        Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a))
  full : ∀ α : MulAut L', α ∈ Subgroup.normalizer (A : Set (MulAut L')) →
    ∃ (c : ZMod 3) (u : WeylGroup .E6), c ≠ 0 ∧ ∀ a b : A, (b : MulAut L') = α * a * α⁻¹ →
      Multiplicative.toAdd (Φ b) = c • adAct .E6 3 u (Multiplicative.toAdd (Φ a))
  odd : Odd (Nat.card Z) → (∀ i, w i * w i = 1) ∧
    ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ v ∈ Subgroup.closure (Set.range w), n * v⁻¹ ∈ T

structure GGE6ThreeActData {L' : Type} [Group L'] (A : Subgroup (MulAut L'))
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (w : Fin 6 → L') : Prop where
  injective : Function.Injective Φ
  range : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6
  act : ∀ i (a : A), ∃ b : A, MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b ∧
    Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a))

theorem GGE6ThreeData.toActData {L' : Type} [Group L'] {Z : Subgroup L'}
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'}
    {w : Fin 6 → L'} (h : GGE6ThreeData Z A Φ T w) : GGE6ThreeActData A Φ w :=
  ⟨h.injective, h.range, h.act⟩

theorem GGE6ThreeWeylModel.exists_data {L' : Type} [Group L'] {Z : Subgroup L'}
    {A : Subgroup (MulAut L')} (h : GGE6ThreeWeylModel Z A) :
    ∃ (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L'),
      GGE6ThreeData Z A Φ T w := by
  obtain ⟨Φ, T, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨Φ, T, w, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

@[expose] def heartOf {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) : Subgroup (MulAut L') :=
  ((AddSubgroup.toSubgroup NoOffRest.hypE6).comap Φ).map A.subtype

@[expose] def imageAdd {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (A' : Subgroup (MulAut L')) :
    AddSubgroup (Fin 6 → ZMod 3) where
  carrier := {v | ∃ a : A, (a : MulAut L') ∈ A' ∧ Φ a = Multiplicative.ofAdd v}
  zero_mem' := ⟨1, A'.one_mem, by simp⟩
  add_mem' := by
    rintro v w ⟨a, ha, hav⟩ ⟨b, hb, hbw⟩
    exact ⟨a * b, A'.mul_mem ha hb, by rw [map_mul, hav, hbw, ofAdd_add]⟩
  neg_mem' := by
    rintro v ⟨a, ha, hav⟩
    exact ⟨a⁻¹, A'.inv_mem ha, by rw [map_inv, hav]; rfl⟩

section API

variable {L' : Type} [Group L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem mem_heartOf_iff {x : MulAut L'} :
    x ∈ heartOf Φ ↔ ∃ h : x ∈ A, Multiplicative.toAdd (Φ ⟨x, h⟩) ∈ NoOffRest.hypE6 := by
  rw [heartOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    have ha' : Φ a ∈ AddSubgroup.toSubgroup NoOffRest.hypE6 := Subgroup.mem_comap.mp ha
    subst hax
    exact ⟨a.2, (Multiplicative.mem_toSubgroup (S := NoOffRest.hypE6) (a := Φ a)).mp ha'⟩
  · rintro ⟨h, hh⟩
    refine ⟨⟨x, h⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr
      ((Multiplicative.mem_toSubgroup (S := NoOffRest.hypE6) (a := Φ ⟨x, h⟩)).mpr hh)

theorem heartOf_le : heartOf Φ ≤ A := by
  rw [heartOf]
  exact Subgroup.map_subtype_le _

theorem GGE6ThreeData.exists_eq_of_mem_hypE6 (h : GGE6ThreeData Z A Φ T w)
    {v : Fin 6 → ZMod 3} (hv : v ∈ NoOffRest.hypE6) : ∃ a : A, Φ a = Multiplicative.ofAdd v := by
  rcases h.range with hr | hr
  · have hv' : Multiplicative.ofAdd v ∈ Φ.range := by rw [hr]; exact Subgroup.mem_top _
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv'
    exact ⟨a, ha⟩
  · have hv' : Multiplicative.ofAdd v ∈ Φ.range := (hr v).mpr hv
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv'
    exact ⟨a, ha⟩

theorem GGE6ThreeActData.card_cases (h : GGE6ThreeActData A Φ w) :
    (Nat.card A = 3 ^ 6 ∧ ∀ v : Fin 6 → ZMod 3, ∃ a : A, Φ a = Multiplicative.ofAdd v) ∨
      (Nat.card A = 3 ^ 5 ∧ ∀ a : A, Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6) := by
  have hcard : Nat.card A = Nat.card Φ.range :=
    Nat.card_congr (MonoidHom.ofInjective h.injective).toEquiv
  rcases h.range with hr | hr
  · left
    refine ⟨?_, ?_⟩
    · rw [hcard, hr, Subgroup.card_top]
      change Nat.card (Fin 6 → ZMod 3) = 3 ^ 6
      rw [Nat.card_pi]
      simp [Nat.card_zmod, Finset.prod_const, Fintype.card_fin]
    · intro v
      have hv' : Multiplicative.ofAdd v ∈ Φ.range := by rw [hr]; exact Subgroup.mem_top _
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv'
      exact ⟨a, ha⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [hcard]
      have heq : Nat.card Φ.range = Nat.card NoOffRest.hypE6 := by
        refine Nat.card_congr ?_
        refine
          { toFun := fun x =>
              ⟨Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)),
                (hr (Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)))).mp
                  (by simpa using x.2)⟩
            invFun := fun y =>
              ⟨Multiplicative.ofAdd (y : Fin Tag.E6.rank → ZMod 3),
                (hr (y : Fin Tag.E6.rank → ZMod 3)).mpr y.2⟩
            left_inv := fun x => Subtype.ext rfl
            right_inv := fun y => Subtype.ext rfl }
      rw [heq, NoOffRest.card_hypE6]
    · intro a
      exact (hr (Multiplicative.toAdd (Φ a))).mp ⟨a, rfl⟩

theorem GGE6ThreeData.card_cases (h : GGE6ThreeData Z A Φ T w) :
    (Nat.card A = 3 ^ 6 ∧ ∀ v : Fin 6 → ZMod 3, ∃ a : A, Φ a = Multiplicative.ofAdd v) ∨
      (Nat.card A = 3 ^ 5 ∧ ∀ a : A, Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6) :=
  h.toActData.card_cases

theorem GGE6ThreeActData.finite (h : GGE6ThreeActData A Φ w) : Finite A := by
  rcases h.card_cases with ⟨hc, _⟩ | ⟨hc, _⟩
  · exact Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  · exact Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)

theorem mem_normalizer_of_conj_mem {f : MulAut L'} [Finite L']
    (hf : ∀ a ∈ A, f * a * f⁻¹ ∈ A) : f ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · exact hf h
  · intro hh
    haveI : Finite A := inferInstance
    let c : A → A := fun a => ⟨f * (a : MulAut L') * f⁻¹, hf a a.2⟩
    have hc : Function.Injective c := by
      intro a b hab
      have h' : f * (a : MulAut L') * f⁻¹ = f * (b : MulAut L') * f⁻¹ :=
        congrArg (fun x : A => (x : MulAut L')) hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
    have hsurj : Function.Surjective c := Finite.injective_iff_surjective.mp hc
    obtain ⟨a, ha⟩ := hsurj ⟨f * h * f⁻¹, hh⟩
    have hval : (a : MulAut L') = h := by
      have h2 : f * (a : MulAut L') * f⁻¹ = f * h * f⁻¹ :=
        congrArg (fun x : A => (x : MulAut L')) ha
      exact mul_left_cancel (mul_right_cancel h2)
    exact hval ▸ a.2

theorem mem_imageAdd_iff (hΦ : Function.Injective Φ) {A' : Subgroup (MulAut L')} (a : A) :
    Multiplicative.toAdd (Φ a) ∈ imageAdd Φ A' ↔ (a : MulAut L') ∈ A' := by
  change (∃ b : A, (b : MulAut L') ∈ A' ∧
      Φ b = Multiplicative.ofAdd (Multiplicative.toAdd (Φ a))) ↔ (a : MulAut L') ∈ A'
  constructor
  · rintro ⟨b, hb, hbΦ⟩
    have hba : b = a := hΦ (by simpa using hbΦ)
    have hb' : (b : MulAut L') = (a : MulAut L') := by rw [hba]
    rwa [hb'] at hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem imageAdd_ne_bot (hΦ : Function.Injective Φ) {A' : Subgroup (MulAut L')} (hA' : A' ≤ A)
    (hne : A' ≠ ⊥) : imageAdd Φ A' ≠ ⊥ := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let a : A := ⟨(x : MulAut L'), hA' x.2⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hx1
    have h2 : (x : MulAut L') = 1 := congrArg (fun y : A => (y : MulAut L')) h
    exact Subtype.ext h2
  have hΦa : Φ a ≠ 1 := by
    intro h
    exact ha1 (hΦ (h.trans (map_one Φ).symm))
  have hne0 : Multiplicative.toAdd (Φ a) ≠ 0 := by
    intro h
    exact hΦa (by rw [← ofAdd_toAdd (Φ a), h, ofAdd_zero])
  have hmem : Multiplicative.toAdd (Φ a) ∈ imageAdd Φ A' :=
    (mem_imageAdd_iff hΦ a).mpr x.2
  exact fun hbot => hne0 (by simpa [hbot] using hmem)

theorem GGE6ThreeData.imageAdd_adRefl (h : GGE6ThreeData Z A Φ T w) {A' : Subgroup (MulAut L')}
    (hinv : ∀ i, ∀ a ∈ A', MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ ∈ A')
    (i : Fin Tag.E6.rank) {v : Fin 6 → ZMod 3} (hv : v ∈ imageAdd Φ A') :
    adRefl Tag.E6 3 i v ∈ imageAdd Φ A' := by
  obtain ⟨a, ha, hav⟩ := hv
  obtain ⟨b, hbconj, hbΦ⟩ := h.act i a
  have hbmem : (b : MulAut L') ∈ A' := by
    rw [← hbconj]
    exact hinv i (a : MulAut L') ha
  have hav' : Multiplicative.toAdd (Φ a) = v := by
    rw [hav]
    exact toAdd_ofAdd v
  have hval : adRefl Tag.E6 3 i v = Multiplicative.toAdd (Φ b) := by
    rw [hbΦ]
    exact congrArg (fun x => adRefl Tag.E6 3 i x) hav'.symm
  rw [hval]
  exact (mem_imageAdd_iff h.injective b).mpr hbmem

end API

end CFSG.StandardType

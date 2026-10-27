module

public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.Quasithin.EmptyFaithful.S1417Natural

public section

namespace CFSG.Quasithin

namespace S1417

abbrev F2sq : Type := Multiplicative (Fin 2 → ZMod 2)

def qK (a : F2sq) : ZMod 2 := if a = 1 then 0 else 1

def qF (x : F2sq × F2sq) : ZMod 2 := qK x.1 + qK x.2

theorem qK_polar_add₁ : ∀ a b c : F2sq,
    quadPolar qK (a * b) c = quadPolar qK a c + quadPolar qK b c := by decide

theorem qK_polar_add₂ : ∀ a b c : F2sq,
    quadPolar qK a (b * c) = quadPolar qK a b + quadPolar qK a c := by decide

theorem qK_nondeg : ∀ a : F2sq, (∀ b : F2sq, quadPolar qK a b = 0) → a = 1 := by decide

theorem quadPolar_qF (x y : F2sq × F2sq) :
    quadPolar qF x y = quadPolar qK x.1 y.1 + quadPolar qK x.2 y.2 := by
  simp only [quadPolar, qF, Prod.fst_mul, Prod.snd_mul]
  ring

theorem qF_isQuadratic : IsQuadraticFormOn qF := by
  refine ⟨by decide, fun x y z => ?_, fun x y z => ?_⟩
  · rw [quadPolar_qF, quadPolar_qF, quadPolar_qF, Prod.fst_mul, Prod.snd_mul, qK_polar_add₁,
      qK_polar_add₁]
    ring
  · rw [quadPolar_qF, quadPolar_qF, quadPolar_qF, Prod.fst_mul, Prod.snd_mul, qK_polar_add₂,
      qK_polar_add₂]
    ring

theorem qF_nondeg : IsNondegQuadratic qF := by
  intro x hx
  revert x
  decide

theorem qF_plus : IsPlusType qF := by
  refine ⟨(MonoidHom.prod (MonoidHom.id F2sq) (MonoidHom.id F2sq)).range, ?_, ?_⟩
  · have hinj : Function.Injective (MonoidHom.prod (MonoidHom.id F2sq) (MonoidHom.id F2sq)) := by
      intro a b h
      exact congrArg Prod.fst h
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  · rintro _ ⟨a, rfl⟩
    revert a
    decide

theorem card_F2sq_prod : Nat.card (F2sq × F2sq) = 16 := by
  rw [Nat.card_prod, card_F2sq]

section Transport

variable {V V' : Type*} [Group V] [Group V']

theorem isQuadratic_comp (e : V ≃* V') {q : V' → ZMod 2} (hq : IsQuadraticFormOn q) :
    IsQuadraticFormOn (fun v => q (e v)) := by
  obtain ⟨h0, h1, h2⟩ := hq
  have hp : ∀ x y : V, quadPolar (fun v => q (e v)) x y = quadPolar q (e x) (e y) := fun x y => by
    simp [quadPolar, map_mul]
  refine ⟨by simpa using h0, fun x y z => ?_, fun x y z => ?_⟩
  · rw [hp, hp, hp, map_mul]
    exact h1 _ _ _
  · rw [hp, hp, hp, map_mul]
    exact h2 _ _ _

theorem isNondeg_comp (e : V ≃* V') {q : V' → ZMod 2} (hq : IsNondegQuadratic q) :
    IsNondegQuadratic (fun v => q (e v)) := by
  intro x hx
  have : e x = 1 := by
    apply hq
    intro y
    have := hx (e.symm y)
    simpa [quadPolar, map_mul] using this
  simpa using this

theorem isPlus_comp (e : V ≃* V') {q : V' → ZMod 2} (hq : IsPlusType q) :
    IsPlusType (fun v => q (e v)) := by
  obtain ⟨S, hS, hq0⟩ := hq
  refine ⟨S.map e.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hS
  · rintro w ⟨s, hs, rfl⟩
    simpa using hq0 s hs

end Transport

section Abstract

variable {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W}

noncomputable def coordHom (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq) : F2sq × F2sq →* W :=
  (U₁.subtype.comp φ₁.symm.toMonoidHom).coprod (U₂.subtype.comp φ₂.symm.toMonoidHom)

theorem coordHom_apply (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq) (a b : F2sq) :
    coordHom φ₁ φ₂ (a, b) = (φ₁.symm a : W) * (φ₂.symm b : W) := by
  simp [coordHom]

theorem coordHom_bijective (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : Function.Bijective (coordHom φ₁ φ₂) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [coordHom_apply] at h
    have h1 : (φ₁.symm a : W) ∈ U₁ ⊓ U₂ := by
      refine ⟨(φ₁.symm a).2, ?_⟩
      have : (φ₁.symm a : W) = ((φ₂.symm b : W))⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact U₂.inv_mem (φ₂.symm b).2
    rw [hinf, Subgroup.mem_bot] at h1
    have h2 : (φ₂.symm b : W) = 1 := by
      rw [h1, one_mul] at h
      exact h
    have ha : a = 1 := by
      have := congrArg φ₁ (Subtype.ext h1 : φ₁.symm a = 1)
      simpa using this
    have hb : b = 1 := by
      have := congrArg φ₂ (Subtype.ext h2 : φ₂.symm b = 1)
      simpa using this
    rw [ha, hb]
    rfl
  · intro w
    have hw : w ∈ U₁ ⊔ U₂ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    refine ⟨(φ₁ ⟨y, hy⟩, φ₂ ⟨z, hz⟩), ?_⟩
    rw [coordHom_apply]
    simp

noncomputable def coordEquiv (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : W ≃* F2sq × F2sq :=
  (MulEquiv.ofBijective (coordHom φ₁ φ₂) (coordHom_bijective hinf hsup φ₁ φ₂)).symm

theorem coordEquiv_mul (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) {y z : W} (hy : y ∈ U₁) (hz : z ∈ U₂) :
    coordEquiv hinf hsup φ₁ φ₂ (y * z) = (φ₁ ⟨y, hy⟩, φ₂ ⟨z, hz⟩) := by
  rw [coordEquiv, MulEquiv.symm_apply_eq]
  rw [MulEquiv.ofBijective_apply, coordHom_apply]
  simp

noncomputable def quadOf (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) (w : W) : ZMod 2 :=
  qF (coordEquiv hinf hsup φ₁ φ₂ w)

theorem quadOf_isQuadratic (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : IsQuadraticFormOn (quadOf hinf hsup φ₁ φ₂) :=
  isQuadratic_comp (coordEquiv hinf hsup φ₁ φ₂) qF_isQuadratic

theorem quadOf_nondeg (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : IsNondegQuadratic (quadOf hinf hsup φ₁ φ₂) :=
  isNondeg_comp (coordEquiv hinf hsup φ₁ φ₂) qF_nondeg

theorem quadOf_plus (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : IsPlusType (quadOf hinf hsup φ₁ φ₂) :=
  isPlus_comp (coordEquiv hinf hsup φ₁ φ₂) qF_plus

theorem card_eq_sixteen (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) : Nat.card W = 16 := by
  rw [Nat.card_congr (coordEquiv hinf hsup φ₁ φ₂).toEquiv, card_F2sq_prod]

open scoped Classical in
theorem quadOf_mul (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) {y z : W} (hy : y ∈ U₁) (hz : z ∈ U₂) :
    quadOf hinf hsup φ₁ φ₂ (y * z) = (if y = 1 then 0 else 1) + (if z = 1 then 0 else 1) := by
  unfold quadOf
  rw [coordEquiv_mul hinf hsup φ₁ φ₂ hy hz]
  have h1 : φ₁ ⟨y, hy⟩ = 1 ↔ y = 1 := by
    rw [← map_one φ₁, φ₁.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : φ₂ ⟨z, hz⟩ = 1 ↔ z = 1 := by
    rw [← map_one φ₂, φ₂.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simp only [qF, qK, h1, h2]

theorem exists_mul_eq (hsup : U₁ ⊔ U₂ = ⊤) (w : W) : ∃ y ∈ U₁, ∃ z ∈ U₂, y * z = w := by
  have hw : w ∈ U₁ ⊔ U₂ := by rw [hsup]; exact Subgroup.mem_top w
  exact Subgroup.mem_sup.mp hw

theorem mem_inf_eq_one (hinf : U₁ ⊓ U₂ = ⊥) {x : W} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂) : x = 1 := by
  have : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact this

theorem quadOf_eq_one_iff (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) {w : W} :
    quadOf hinf hsup φ₁ φ₂ w = 1 ↔ (w ∈ U₁ ∨ w ∈ U₂) ∧ w ≠ 1 := by
  classical
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
  rw [quadOf_mul hinf hsup φ₁ φ₂ hy hz]
  by_cases hy1 : y = 1 <;> by_cases hz1 : z = 1
  · subst hy1; subst hz1; simp
  · subst hy1
    simp [hz1, hz]
  · subst hz1
    simp [hy1, hy]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [hy1, hz1, ↓reduceIte, this, zero_ne_one, false_iff, not_and]
    intro h
    exfalso
    rcases h with h | h
    · apply hz1
      have : z ∈ U₁ := by
        have := U₁.mul_mem (U₁.inv_mem hy) h
        simpa using this
      exact mem_inf_eq_one hinf this hz
    · apply hy1
      have : y ∈ U₂ := by
        have := U₂.mul_mem h (U₂.inv_mem hz)
        simpa using this
      exact mem_inf_eq_one hinf hy this

end Abstract

end S1417

end CFSG.Quasithin

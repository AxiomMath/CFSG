module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationSetup
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc
open scoped RegularWreathProduct

def permToS4Fun (σ : Equiv.Perm (Fin 4)) : S4 :=
  S4.ofImages [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val]

theorem permToS4_one : permToS4Fun 1 = 1 := by decide +kernel

theorem permToS4_mul : ∀ σ τ : Equiv.Perm (Fin 4),
    permToS4Fun (σ * τ) = permToS4Fun σ * permToS4Fun τ := by decide +kernel

theorem permToS4_inj : Function.Injective permToS4Fun := by
  intro σ τ h
  revert σ τ
  decide +kernel

theorem permToS4_surj : Function.Surjective permToS4Fun := by
  intro x
  revert x
  decide +kernel

@[expose] def permToS4 : Equiv.Perm (Fin 4) →* S4 where
  toFun := permToS4Fun
  map_one' := permToS4_one
  map_mul' := permToS4_mul

@[expose] noncomputable def permS4Equiv : Equiv.Perm (Fin 4) ≃* S4 :=
  MulEquiv.ofBijective permToS4 ⟨permToS4_inj, permToS4_surj⟩

noncomputable def wcToWreathFun (w : Wc) : Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2) :=
  ⟨fun q => if q = 1 then permS4Equiv.symm w.a else permS4Equiv.symm w.b,
    Multiplicative.ofAdd (if w.e then 1 else 0)⟩

theorem mult_zmod_two_cases : ∀ q : Multiplicative (ZMod 2), q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  decide

theorem wcToWreath_one : wcToWreathFun 1 = 1 := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext q
    simp [wcToWreathFun, one_def, RegularWreathProduct.one_left]
  · simp [wcToWreathFun, one_def]

theorem zmod2_one_ne : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 := by decide
theorem zmod2_mul_self : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) *
    Multiplicative.ofAdd 1 = 1 := by decide
theorem wcToWreath_mul (w w' : Wc) :
    wcToWreathFun (w * w') = wcToWreathFun w * wcToWreathFun w' := by
  rcases w with ⟨a, b, e⟩
  rcases w' with ⟨a', b', e'⟩
  rw [RegularWreathProduct.mul_def]
  refine RegularWreathProduct.ext ?_ ?_
  · funext q
    rcases mult_zmod_two_cases q with rfl | rfl <;> cases e <;> cases e' <;>
      simp [wcToWreathFun, Wc.mul_false, Wc.mul_true, map_mul]
    all_goals (intro h; exact absurd h (by decide))
  · cases e <;> cases e' <;> simp [wcToWreathFun, Wc.mul_false, Wc.mul_true]
    exact zmod2_mul_self.symm

@[expose] noncomputable def wcToWreath : Wc →* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2) where
  toFun := wcToWreathFun
  map_one' := wcToWreath_one
  map_mul' := wcToWreath_mul

theorem wcToWreath_injective : Function.Injective wcToWreath := by
  intro w w' h
  have hl := congrArg RegularWreathProduct.left h
  have hr := congrArg RegularWreathProduct.right h
  have h1 := congrFun hl 1
  have h2 := congrFun hl (Multiplicative.ofAdd 1)
  simp only [wcToWreath, MonoidHom.coe_mk, OneHom.coe_mk, wcToWreathFun] at h1 h2 hr
  simp only [ite_true, zmod2_one_ne, ite_false] at h1 h2
  refine Wc.ext (permS4Equiv.symm.injective h1) (permS4Equiv.symm.injective h2) ?_
  have hr' := Multiplicative.ofAdd.injective hr
  revert hr'
  cases w.e <;> cases w'.e <;> decide

theorem wcToWreath_surjective : Function.Surjective wcToWreath := by
  rintro ⟨f, q⟩
  refine ⟨⟨permS4Equiv (f 1), permS4Equiv (f (Multiplicative.ofAdd 1)), decide (q ≠ 1)⟩, ?_⟩
  refine RegularWreathProduct.ext ?_ ?_
  · funext x
    rcases mult_zmod_two_cases x with rfl | rfl
    · simp [wcToWreath, wcToWreathFun]
    · simp [wcToWreath, wcToWreathFun]
  · rcases mult_zmod_two_cases q with rfl | rfl
    · simp [wcToWreath, wcToWreathFun]
    · simp [wcToWreath, wcToWreathFun]

@[expose] noncomputable def wcEquivWreath :
    Wc ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective wcToWreath ⟨wcToWreath_injective, wcToWreath_surjective⟩

variable {G : Type*} [Group G]

theorem nonempty_emb_of_wreath [Finite G] {T M : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTM : T ≤ M)
    (φ : Nonempty (↥M ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2))) :
    Nonempty (Emb G T M) := by
  obtain ⟨φ⟩ := φ
  exact exists_emb hT hTM (φ.trans wcEquivWreath.symm)

end CFSG.Quasithin.A10

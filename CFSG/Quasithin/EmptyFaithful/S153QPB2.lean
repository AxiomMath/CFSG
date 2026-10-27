module

public import CFSG.Quasithin.EmptyFaithful.S153QPB1
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.Quasithin.EmptyFaithful.S153QPR

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_of_aut_trivial_mod_two_group (φ : MulAut (SpecialLinearGroup (Fin 3) F))
    (hφ5 : φ ^ 5 = 1) {P X : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) P) (hX : IsPGroup 2 X)
    (hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) (hφ : ∀ p ∈ P, φ p * p⁻¹ ∈ X) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ x, φ x = g * x * g⁻¹ := by
  obtain ⟨g, d, hd1, hd3, hPd⟩ := exists_conj_stabilizer_of_isMaxParabolic2 (by norm_num : 1 ≤ 3) hP
  have hd : d = 1 ∨ d = 2 := by omega
  set a : MulAut (SpecialLinearGroup (Fin 3) F) := MulAut.conj g⁻¹ with ha
  have hinv : a⁻¹ = MulAut.conj g := by rw [ha, ← map_inv, inv_inv]
  have ha_apply : ∀ y, a y = g⁻¹ * y * g := fun y => by simp [ha]
  have hainv_apply : ∀ y, a⁻¹ y = g * y * g⁻¹ := fun y => by rw [hinv, MulAut.conj_apply]
  set X' : Subgroup (SpecialLinearGroup (Fin 3) F) :=
    X.map (a : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) with hX'
  have hX'2 : IsPGroup 2 X' :=
    hX.of_equiv (X.equivMapOfInjective (a : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
      a.injective)
  have hQP : ∀ p' ∈ stabilizer (flagSpace 3 F d), a⁻¹ p' ∈ P := fun p' hp' => by
    rw [hPd]
    exact ⟨p', hp', by rw [hainv_apply]; rfl⟩
  have hN : ∀ q ∈ stabilizer (flagSpace 3 F d), ∀ x ∈ X', q * x * q⁻¹ ∈ X' := by
    rintro q hq _ ⟨x, hx, rfl⟩
    refine ⟨a⁻¹ q * x * (a⁻¹ q)⁻¹, hPX _ (hQP q hq) x hx, ?_⟩
    show a (a⁻¹ q * x * (a⁻¹ q)⁻¹) = q * a x * q⁻¹
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hrad : X' ≤ radU F (flagSpace 3 F d) := le_radU_of_isPGroup hd1 hd3 hX'2 hN
  set φ' : MulAut (SpecialLinearGroup (Fin 3) F) := a * φ * a⁻¹ with hφ'
  have hφ'Q : ∀ p' ∈ stabilizer (flagSpace 3 F d), φ' p' * p'⁻¹ ∈ radU F (flagSpace 3 F d) := by
    intro p' hp'
    apply hrad
    refine ⟨φ (a⁻¹ p') * (a⁻¹ p')⁻¹, hφ _ (hQP p' hp'), ?_⟩
    show a (φ (a⁻¹ p') * (a⁻¹ p')⁻¹) = (a * φ * a⁻¹) p' * p'⁻¹
    rw [map_mul, map_inv, MulAut.apply_inv_self]
    rfl
  have hφ'5 : φ' ^ 5 = 1 := by rw [hφ', conj_pow, hφ5]; group
  obtain ⟨h, hh⟩ := exists_conj_of_trivial_mod_radU hd φ' hφ'5 hφ'Q
  refine ⟨g * h * g⁻¹, fun x => ?_⟩
  have hx : φ x = a⁻¹ (φ' (a x)) := by
    rw [hφ']
    show φ x = a⁻¹ (a (φ (a⁻¹ (a x))))
    rw [MulAut.inv_apply_self, MulAut.inv_apply_self]
  rw [hx, hh, ha_apply, hainv_apply]
  group

end CFSG.Quasithin.QP

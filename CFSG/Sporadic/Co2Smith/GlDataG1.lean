module

public import CFSG.Sporadic.Co2Smith.GlDataC0Coset
public import CFSG.Sporadic.Co2Rank3.Extension

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glC_spec :
    lettersOK 11 Native.glCWord = true ∧ isInvA 2300 Native.glCArr Native.glCInv = true ∧
    Native.glCArr[80]! = 0 ∧ Native.glCArr[1172]! = 3 ∧ Native.glCArr[582]! = 1 := by
  have h := glElem_parts.2.2.2.1
  simp only [Native.glCOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_glCArr :
    Rep 2300 Native.glCArr cPerm :=
  rep_wordA (fun _ hh => rep_co2Strong hh) (fun _ hh => rep_co2StrongInv hh) _ glC_spec.1

theorem rep_glCInv :
    Rep 2300 Native.glCInv cPerm⁻¹ :=
  rep_inv_of_isInvA rep_glCArr glC_spec.2.1

theorem cPerm_mem :
    cPerm ∈ co2P := by
  refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact co2Strong_mem h.2

theorem cPerm_p0 :
    cPerm glP0 = 0 :=
  Fin.ext ((rep_glCArr glP0).symm.trans glC_spec.2.2.1)

theorem cPerm_1172 :
    cPerm 1172 = 3 :=
  Fin.ext ((rep_glCArr 1172).symm.trans glC_spec.2.2.2.1)

theorem cPerm_582 :
    cPerm 582 = 1 :=
  Fin.ext ((rep_glCArr 582).symm.trans glC_spec.2.2.2.2)

@[expose] noncomputable def psiK :
    K →* Equiv.Perm (Fin 2300) :=
  (MulAut.conj cPerm).toMonoidHom.comp co2PermHom

section Psi


theorem psiK_apply (g : K) : psiK g = cPerm * co2PermHom g * cPerm⁻¹ := by
  rw [psiK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem psiK_injective : Function.Injective (psiK : K →* Equiv.Perm (Fin 2300)) :=
  (MulAut.conj cPerm).injective.comp co2PermHom_injective

theorem co2PermHom_mem (g : K) : co2PermHom g ∈ co2P := by
  rw [← co2PermHom_range]
  exact ⟨g, rfl⟩

theorem psiK_mem_co2P (g : K) : psiK g ∈ co2P :=
  co2P.mul_mem (co2P.mul_mem cPerm_mem (co2PermHom_mem g)) (co2P.inv_mem cPerm_mem)

theorem psiK_apply_cPerm (g : K) (x : Fin 2300) : psiK g (cPerm x) = cPerm (co2PermHom g x) := by
  rw [psiK_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self]

theorem psiK_fix_iff {g : K} {x : Fin 2300} :
    psiK g (cPerm x) = cPerm x ↔ co2PermHom g x = x := by
  rw [psiK_apply_cPerm]
  exact cPerm.injective.eq_iff

end Psi

theorem map_psiK_G1c :
    G1c.map psiK = co2P0 := by
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨psiK_mem_co2P g, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def, ← cPerm_p0, psiK_fix_iff]
    exact hg
  · rintro ⟨hσP, hσ0⟩
    have hσ0' := MulAction.mem_stabilizer_iff.1 hσ0
    rw [Equiv.Perm.smul_def] at hσ0'
    obtain ⟨g, hg⟩ : cPerm⁻¹ * σ * cPerm ∈ co2PermHom.range := by
      rw [co2PermHom_range]
      exact co2P.mul_mem (co2P.mul_mem (co2P.inv_mem cPerm_mem) hσP) cPerm_mem
    refine ⟨g, ?_, ?_⟩
    · show co2PermHom g glP0 = glP0
      rw [hg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, cPerm_p0, hσ0', ← cPerm_p0,
        perm_inv_apply_self]
    · rw [psiK_apply, hg]
      group

@[expose] noncomputable def G1cEquiv :
    G1c ≃* co2P0 :=
  (G1c.equivMapOfInjective psiK psiK_injective).trans (MulEquiv.subgroupCongr map_psiK_G1c)

theorem G1cEquiv_apply
    (g : G1c) :
    (G1cEquiv g : Equiv.Perm (Fin 2300)) = psiK g := by
  rw [G1cEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]

theorem card_G1c :
    Nat.card G1c = 18393661440 := by
  rw [Nat.card_congr G1cEquiv.toEquiv, card_co2P0]

theorem uK_conj_mem_G1c
    {h : K}
    (h3 : psiK h 3 = 3) : uK * h * uK⁻¹ ∈ G1c := by
  have hfix : co2PermHom h 1172 = 1172 := by
    rw [← psiK_fix_iff, cPerm_1172]
    exact h3
  have hu : co2PermHom uK⁻¹ glP0 = 1172 := by
    rw [inv_eq_of_mul_eq_one_right uK_mul_self, co2PermHom_uK]
  show co2PermHom (uK * h * uK⁻¹) glP0 = glP0
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hu, hfix, ← hu,
    ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

theorem v1K_conj_mem_G1c
    {h : K}
    (h1 : psiK h 1 = 1) : v1K * h * v1K⁻¹ ∈ G1c := by
  have hfix : co2PermHom h 582 = 582 := by
    rw [← psiK_fix_iff, cPerm_582]
    exact h1
  have hv : co2PermHom v1K⁻¹ glP0 = 582 := by
    rw [inv_eq_of_mul_eq_one_right v1K_mul_self, co2PermHom_v1K]
  show co2PermHom (v1K * h * v1K⁻¹) glP0 = glP0
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv, hfix, ← hv,
    ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

end CFSG.Sporadic.Co2Smith

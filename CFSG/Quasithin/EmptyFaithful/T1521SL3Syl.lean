module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3Core
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Iface
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.L3Aut

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_one_of_fixes_odd_normalizer {K : Type*} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (Q : Sylow 2 (projectiveSL 3 K)) (β : MulAut (projectiveSL 3 K))
    (hβ : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)),
      Odd (orderOf z) → β z = z) : β = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) SU Q
  have hQ : (Q : Subgroup (projectiveSL 3 K)) =
      (projUnitriangular 3 K).map (MulAut.conj g : projectiveSL 3 K →* projectiveSL 3 K) := by
    rw [← hg, coe_sylow_smul, hSU]
  have hN : Subgroup.normalizer ((Q : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) =
      (projUpperTriangular 3 K).map (MulAut.conj g : projectiveSL 3 K →* projectiveSL 3 K) := by
    rw [hQ, normalizer_map_conj, normalizer_projUnitriangular 2]
  set β' : MulAut (projectiveSL 3 K) := (MulAut.conj g)⁻¹ * β * MulAut.conj g with hβ'def
  have hβ' : ∀ z ∈ projUpperTriangular 3 K, Odd (orderOf z) → β' z = z := by
    intro z hz hzo
    have hzN : g * z * g⁻¹ ∈
        Subgroup.normalizer ((Q : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
      rw [hN]
      exact ⟨z, hz, rfl⟩
    have hord : Odd (orderOf (g * z * g⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hzo
    have h1 := hβ _ hzN hord
    have e1 : β' z = (MulAut.conj g)⁻¹ (β (MulAut.conj g z)) := rfl
    rw [e1, MulAut.conj_apply, h1]
    simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]
  obtain ⟨a, ha, h12, h23, hT⟩ := Bor.exists_fixed_of_fixes_odd h4 β' hβ'
  have hone : β' = 1 := Core.eq_one_of_fixes_root_torus ha β' h12 h23 hT
  calc β = MulAut.conj g * β' * (MulAut.conj g)⁻¹ := by rw [hβ'def]; group
    _ = 1 := by rw [hone]; group

theorem l3ModelAut_holds : L3ModelAut := by
  intro K _ _ n hn hK H _ φ Q α hα
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite H := Finite.of_equiv (projectiveSL 3 K) φ.symm.toEquiv
  let Q' : Sylow 2 (projectiveSL 3 K) := Q.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ' : (Q' : Subgroup (projectiveSL 3 K)) = (Q : Subgroup H).map φ.toMonoidHom := rfl
  let β : MulAut (projectiveSL 3 K) := MulAut.congr φ α
  have hβ : ∀ z ∈ Subgroup.normalizer ((Q' : Subgroup (projectiveSL 3 K)) :
      Set (projectiveSL 3 K)), Odd (orderOf z) → β z = z := by
    intro z hz hzo
    rw [hQ', ← Subgroup.map_equiv_normalizer_eq] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hzo' : Odd (orderOf z') := by
      rw [← MulEquiv.orderOf_eq φ]
      exact hzo
    have h1 := hα z' hz' hzo'
    change φ (α (φ.symm (φ z'))) = φ z'
    rw [MulEquiv.symm_apply_apply, h1]
  have hβ1 : β = 1 :=
    eq_one_of_fixes_odd_normalizer h4 Q' β hβ
  ext x
  have := congrArg (fun γ : MulAut (projectiveSL 3 K) => φ.symm (γ (φ x))) hβ1
  simpa [β, MulAut.congr] using this

end CFSG.Quasithin.L3Aut

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylowParameter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralIndexTwoCentralInvolution
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning the low-two-part torus with a fixed Sylow subgroup

The low-two-part cyclic torus in odd `PGL₂(K)` supplies two commuting
involutions on opposite sides of the derived subgroup.  After conjugating
them into a prescribed Sylow `2`-subgroup, the inside involution is the
central rotation of any chosen dihedral model of that Sylow subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups Pointwise

universe u

/-- The low-two-part torus and its reflector can be conjugated into any fixed
Sylow `2`-subgroup so that the reflector becomes the central rotation of a
chosen dihedral model. -/
public theorem pgl2_low_two_part_torus_reflection_data_fixed_sylow
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m)) :
    ∃ U : Subgroup (PGL2 K), ∃ s t g : PGL2 K,
      IsCyclic U ∧ Odd (Nat.card U / 2) ∧
      (Nat.card U = Nat.card K - 1 ∨ Nat.card U = Nat.card K + 1) ∧
      s ∈ U ∧ s ∉ commutator (PGL2 K) ∧ s ≠ 1 ∧ s * s = 1 ∧
      t ∈ commutator (PGL2 K) ∧ t ∉ U ∧ t * t = 1 ∧
      (∀ x : PGL2 K, x ∈ U → t * x * t⁻¹ = x⁻¹) ∧
      g * s * g⁻¹ ∈ (P : Subgroup (PGL2 K)) ∧
      g * t * g⁻¹ =
        (eP.symm (DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m))) : PGL2 K) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, s, t, w, hUcyc, hUodd, hUcard, hsU, hsJ, hsne, hssq,
      htJ, htU, htsq, htinv, htrel, hwU, hwsq, hwinv, hcent⟩ :=
    pgl2_low_two_part_torus_reflection_data K hK hcard
  have htne : t ≠ 1 := by
    intro ht
    apply htU
    rw [ht]
    exact U.one_mem
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hssq
  have hcomm : Commute t s := by
    show t * s = s * t
    calc
      t * s = (t * s * t⁻¹) * t := by group
      _ = s⁻¹ * t := by rw [htinv s hsU]
      _ = s * t := by rw [hsinv]
  let A : Subgroup (PGL2 K) := Subgroup.zpowers s
  let B : Subgroup (PGL2 K) := Subgroup.zpowers t
  have hsord : orderOf s = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hssq) hsne
  have htord : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using htsq) htne
  have hAp : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 1)
    simp [A, Nat.card_zpowers, hsord]
  have hBp : IsPGroup 2 B := by
    apply IsPGroup.of_card (n := 1)
    simp [B, Nat.card_zpowers, htord]
  have htNormA : t ∈ Subgroup.normalizer (A : Set (PGL2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * s * t⁻¹) = Subgroup.zpowers s
    rw [htinv s hsU, hsinv]
  have hBnormA : B ≤ Subgroup.normalizer (A : Set (PGL2 K)) :=
    Subgroup.zpowers_le.mpr htNormA
  let V : Subgroup (PGL2 K) := A ⊔ B
  have hVp : IsPGroup 2 V := by
    exact IsPGroup.to_sup_of_normal_left' hAp hBp hBnormA
  obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow hVp
  have hsV : s ∈ V := by
    exact (le_sup_left : A ≤ V) (Subgroup.mem_zpowers s)
  have htV : t ∈ V := by
    exact (le_sup_right : B ≤ V) (Subgroup.mem_zpowers t)
  have hsQ : s ∈ (Q : Subgroup (PGL2 K)) := hVQ hsV
  have htQ : t ∈ (Q : Subgroup (PGL2 K)) := hVQ htV
  obtain ⟨g, hg⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq (PGL2 K) (Sylow 2 (PGL2 K))
      inferInstance inferInstance Q P
  have hsP : g * s * g⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
    have hmem : g * s * g⁻¹ ∈
        ((g • Q : Sylow 2 (PGL2 K)) : Subgroup (PGL2 K)) := by
      change (MulAut.conj g) s ∈
        (Q : Subgroup (PGL2 K)).map (MulAut.conj g).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨s, hsQ, rfl⟩
    rw [hg] at hmem
    exact hmem
  have htP : g * t * g⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
    have hmem : g * t * g⁻¹ ∈
        ((g • Q : Sylow 2 (PGL2 K)) : Subgroup (PGL2 K)) := by
      change (MulAut.conj g) t ∈
        (Q : Subgroup (PGL2 K)).map (MulAut.conj g).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨t, htQ, rfl⟩
    rw [hg] at hmem
    exact hmem
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let HP : Subgroup P := J.subgroupOf (P : Subgroup (PGL2 K))
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hHPindex : HP.index = 2 := by
    have : J.Normal := by
      dsimp [J]
      infer_instance
    have hdvd : HP.index ∣ 2 := by
      change J.relIndex (P : Subgroup (PGL2 K)) ∣ 2
      simpa [hJindex] using
        (Subgroup.relIndex_dvd_index_of_normal
          (H := J) (K := (P : Subgroup (PGL2 K))))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : HP = ⊤ := Subgroup.index_eq_one.mp hone
      have hsPH : (⟨g * s * g⁻¹, hsP⟩ : P) ∈ HP := by
        rw [htop]
        trivial
      apply hsJ
      have hsconjJ : g * s * g⁻¹ ∈ J := hsPH
      have hback : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ ∈ J :=
        (inferInstance : J.Normal).conj_mem
          (g * s * g⁻¹) hsconjJ g⁻¹
      have heq : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s := by
        group
      rw [heq] at hback
      exact hback
    · exact htwo
  let sP : P := ⟨g * s * g⁻¹, hsP⟩
  let tP : P := ⟨g * t * g⁻¹, htP⟩
  have htPH : tP ∈ HP := by
    change g * t * g⁻¹ ∈ J
    exact (inferInstance : J.Normal).conj_mem t htJ g
  have hsPH : sP ∉ HP := by
    intro hs
    apply hsJ
    have hsconjJ : g * s * g⁻¹ ∈ J := hs
    have hback : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ ∈ J :=
      (inferInstance : J.Normal).conj_mem
        (g * s * g⁻¹) hsconjJ g⁻¹
    have heq : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s := by
      group
    rw [heq] at hback
    exact hback
  have htPne : tP ≠ 1 := by
    intro h
    apply htne
    have hval : g * t * g⁻¹ = 1 := congrArg Subtype.val h
    calc
      t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hval]; simp
  have hsPne : sP ≠ 1 := by
    intro h
    apply hsne
    have hval : g * s * g⁻¹ = 1 := congrArg Subtype.val h
    calc
      s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [hval]; simp
  have htPsq : tP * tP = 1 := by
    apply Subtype.ext
    change (g * t * g⁻¹) * (g * t * g⁻¹) = 1
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by
        group
      _ = 1 := by rw [htsq]; simp
  have hsPsq : sP * sP = 1 := by
    apply Subtype.ext
    change (g * s * g⁻¹) * (g * s * g⁻¹) = 1
    calc
      (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by
        group
      _ = 1 := by rw [hssq]; simp
  have hcommP : Commute tP sP := by
    show tP * sP = sP * tP
    apply Subtype.ext
    simpa [tP, sP] using congrArg (MulAut.conj g) hcomm.eq
  have hm : 2 ≤ m := pgl2_dihedral_sylow_parameter_ge_two K hK P eP
  have htPcentral : tP = eP.symm (DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m))) :=
    eq_central_involution_of_mem_indexTwo_of_commuting_involution_not_mem
      hm eP HP hHPindex tP sP htPH hsPH htPne hsPne htPsq hsPsq hcommP
  refine ⟨U, s, t, g, hUcyc, hUodd, hUcard, hsU, hsJ, hsne, hssq,
    htJ, htU, htsq, htinv, hsP, ?_⟩
  exact congrArg Subtype.val htPcentral

end CFSG.GorensteinWalter

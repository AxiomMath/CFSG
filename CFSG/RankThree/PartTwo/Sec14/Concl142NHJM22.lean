module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.KFacts.KP4Basic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.KFacts.KP4 (G22 P0 card_P0 V lineE exists_centralizer_eq
  le_V_of_not_dvd conj_mem_V card_V)

theorem exists_conj_mem_P0 {b : G22} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ g : G22, g * b * g⁻¹ ∈ P0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP0 : IsPGroup 3 P0 := IsPGroup.of_card (n := 2) (by rw [card_P0]; norm_num)
  have hidx : ¬ 3 ∣ P0.index := by
    have h := P0.index_mul_card
    rw [card_P0, KFacts.KS14.card_nativeM22] at h
    omega
  have hb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one])
  obtain ⟨S, hbS⟩ := hb.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G22 S (hP0.toSylow hidx)
  refine ⟨g, ?_⟩
  have hmem : g * b * g⁻¹ ∈ ((g • S : Sylow 3 G22) : Subgroup G22) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj g)⁻¹ • (g * b * g⁻¹) = b := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      group
    rw [this]
    exact hbS (Subgroup.mem_zpowers b)
  rw [hg, IsPGroup.toSylow_coe] at hmem
  exact hmem

theorem ks142SignalM22 :
    KS142SignalM22 := by
  intro E hE _ b hbE hb1
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  obtain ⟨g, hg⟩ := exists_conj_mem_P0 hb3 hb1
  have hg1 : g * b * g⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨i, hi⟩ := exists_centralizer_eq hg hg1
  set φ : G22 ≃* G22 := MulAut.conj g with hφ
  have hφb : φ b = g * b * g⁻¹ := rfl
  have hcen : (Subgroup.centralizer ({b} : Set G22)).map φ.toMonoidHom =
      Subgroup.centralizer ({lineE i} : Set G22) := by
    rw [CFSG.RankThree.PartTwo.map_centralizer_singleton φ b, hφb, hi]
  have hφφ : ∀ x : G22, φ.symm (φ x) = x := fun x => φ.symm_apply_apply x
  refine ⟨(V i).map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.symm.injective, card_V]
    norm_num
  ·
    intro x hx
    have hφx : φ x ∈ Subgroup.centralizer ({lineE i} : Set G22) :=
      hcen ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hN : φ x ∈ Subgroup.normalizer ((V i : Subgroup G22) : Set G22) :=
      Subgroup.mem_normalizer_fintype fun v hv => conj_mem_V hφx hv
    have hN' : φ.symm (φ x) ∈ (Subgroup.normalizer ((V i : Subgroup G22) : Set G22)).map
        φ.symm.toMonoidHom := Subgroup.mem_map_of_mem φ.symm.toMonoidHom hN
    rw [Subgroup.map_equiv_normalizer_eq, hφφ] at hN'
    exact hN'
  ·
    intro U hU hU3 _
    have hUC : U.map φ.toMonoidHom ≤ Subgroup.centralizer ({lineE i} : Set G22) :=
      hcen ▸ Subgroup.map_mono hU
    have hU3' : ¬ 3 ∣ Nat.card (U.map φ.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective φ.injective]
    have hUV := le_V_of_not_dvd hUC hU3'
    intro u hu
    refine ⟨φ u, hUV (Subgroup.mem_map_of_mem φ.toMonoidHom hu), ?_⟩
    exact hφφ u

theorem step142M22_of'
    (h131 : Item131) (hspor : SporadicModels131) :
    Step142M22 :=
  step142M22_of h131 hspor ks142SignalM22

end CFSG.RankThree.PartTwo.Sec14

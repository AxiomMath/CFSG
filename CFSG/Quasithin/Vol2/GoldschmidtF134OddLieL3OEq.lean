module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OModel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OArith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelCard
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLift

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isSolvable_of_card_eq {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : Nat.card G = 2 ^ k * p ^ 3) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two hp (Ne.symm hp2) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem exists_conj_projUnitriangular {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hK : Nat.card K = p) {P₁ : Subgroup (projectiveSL 3 K)} (hP₁p : IsPGroup p P₁)
    (hP₁ : Nat.card P₁ = p ^ 3) :
    ∃ g : projectiveSL 3 K, ∀ z, z ∈ P₁ ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
  have hchar : CharP K p := charP_of_natCard_eq hp.out hK
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  obtain ⟨V, hV⟩ := hP₁p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) U₀ V
  have hmem : ∀ z, z ∈ (V : Subgroup (projectiveSL 3 K)) ↔
      g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hU₀]
  have hVcard : Nat.card (V : Subgroup (projectiveSL 3 K)) = p ^ 3 := by
    rw [Sylow.card_eq_multiplicity V, ← Sylow.card_eq_multiplicity U₀, hU₀,
      card_projUnitriangular, hK]
  have hPV : P₁ = V := Subgroup.eq_of_le_of_card_ge hV (by rw [hVcard, hP₁])
  exact ⟨g, fun z => by rw [hPV]; exact hmem z⟩

theorem card_eq_sq_of_eq {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    {L P T : Subgroup A} (hp5 : 5 ≤ p) (hL : StatedClassicalModel ↥L .PSL 3 p 1)
    (hcfg : OddCfg p L P T) : Nat.card P = p ^ 2 := by
  by_contra hne
  have hP3 : Nat.card P = p ^ 3 := (hcfg.card).resolve_left hne
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := exists_equiv_projectiveSL hL
  have hp2 : p ≠ 2 := by omega
  set P₁ : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e₁.toMonoidHom with hP₁def
  have hP₁card : Nat.card P₁ = p ^ 3 := by
    rw [hP₁def, Subgroup.card_map_of_injective e₁.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hP3]
  have hP₁p : IsPGroup p P₁ := hcfg.isPGroup.of_equiv
    ((Subgroup.subgroupOfEquivOfLe hcfg.le).symm.trans
      ((P.subgroupOf L).equivMapOfInjective e₁.toMonoidHom e₁.injective))
  obtain ⟨g, hg⟩ := exists_conj_projUnitriangular hK hP₁p hP₁card
  set e : ↥L ≃* projectiveSL 3 K := e₁.trans (MulAut.conj g⁻¹) with hedef
  have he : ∀ y : L, e y = g⁻¹ * e₁ y * g := fun y => by
    rw [hedef, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hPe : (P.subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e y ∈ _
      rw [he]
      exact (hg _).1 ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hye⟩ := (hg (g * x * g⁻¹)).2
        (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group])
      refine ⟨y, hy, ?_⟩
      change e y = x
      rw [he]
      change e₁ y = g * x * g⁻¹ at hye
      rw [hye]
      group
  have hSL := hcfg.isSylowTwoOf_inf
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hSL.2.1
  set HG : Subgroup (projectiveSL 3 K) :=
    ((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom with hHG
  set SG : Subgroup (projectiveSL 3 K) := ((T ⊓ L).subgroupOf L).map e.toMonoidHom with hSG
  have hHcard : Nat.card HG = 2 ^ j * p ^ 3 := by
    rw [hHG, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.sup_inf_le).toEquiv,
      hcfg.card_sup_inf hp5, hP3, hj, mul_comm]
  have hsolv : Group.IsSolvable HG := isSolvable_of_card_eq hp.out hp2 hHcard
  have hUH : projUnitriangular 3 K ≤ HG := by
    rw [← hPe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left)
  have hSH : SG ≤ HG := Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  have hK4 : 4 ≤ Nat.card K := by omega
  have hdvd := card_dvd_of_le_upperTriangular (B := SG) fun g' hg' =>
    le_upperTriangular_of_isSolvable hK4 hUH hsolv (hSH hg')
  have hSGcard : Nat.card SG = 2 ^ j := by
    rw [hSG, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL.1).toEquiv, hj]
  rw [hSGcard, hK] at hdvd
  have hidx := ((T ⊓ L).subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL.1).toEquiv, hj,
    Nat.card_congr e.toEquiv] at hidx
  have hN := card_projectiveSL_mul (K := K)
  rw [hK] at hN
  exact false_of_two_pow_dvd (hp.out.odd_of_ne_two hp2) not_two_dvd_card_scalars hSL.2.2 hN
    hidx hdvd

end CFSG.Quasithin.H13.NQCore.L3Odd

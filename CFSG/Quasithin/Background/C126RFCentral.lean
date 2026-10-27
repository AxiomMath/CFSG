module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_pow_mem_pCoreOf {H T M : Subgroup G} (h : MinParabolic H T M) {j : G}
    (hj : j ∈ kerIn M H) : ∃ m : ℕ, Odd m ∧ j ^ m ∈ pCoreOf 2 H := by
  have hS := h.isSylowTwoOf_pCoreOf_kerIn
  have hQJ : pCoreOf 2 H ≤ kerIn M H := hS.1
  have hn : ((pCoreOf 2 H).subgroupOf (kerIn M H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2
      (h.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  refine ⟨((pCoreOf 2 H).subgroupOf (kerIn M H)).index, ?_, ?_⟩
  · have h2 : ¬ 2 ∣ (pCoreOf 2 H).relIndex (kerIn M H) := hS.2.2
    have e : ((pCoreOf 2 H).subgroupOf (kerIn M H)).index =
        (pCoreOf 2 H).relIndex (kerIn M H) := rfl
    rw [e]
    exact Nat.odd_iff.2 (by omega)
  · have := Subgroup.pow_index_mem ((pCoreOf 2 H).subgroupOf (kerIn M H)) (⟨j, hj⟩ : kerIn M H)
    exact Subgroup.mem_subgroupOf.1 this

theorem inf_centralizer_le_pCoreOf_of_case_two {H T M V K₁ : Subgroup G}
    (hmin : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) (hK₁H : K₁ ≤ H) (hHK : H = K₁ ⊔ T)
    (hTN : T ≤ Subgroup.normalizer (K₁ : Set G))
    (hJ : ∀ x : G, x ∈ kerIn M H ↔ x ∈ K₁ ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K₁ ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hZ : IsPGroup 2 ↥(Subgroup.center (↥K₁ ⧸ CFSG.Open.pCore 2 ↥K₁))) :
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H := by
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
  have hT := hmin.isSylow
  have hHN : H ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTN
  have hK₁x : x ∈ K₁ :=
    twoResidual_le_of_isTwoQuotient hK₁H hHN
      (B6.isTwoQuotient_of_sup_eq hT.2.1 hHN ((sup_comm T K₁).trans hHK.symm)) hxK
  have hxH : x ∈ H := twoResidual_le H hxK
  have hxJ : x ∈ kerIn M H := hmin.inf_centralizer_le_kerIn hred hHV ⟨hxH, hxC⟩
  have hcomm := ((hJ x).1 hxJ).2
  have hQH := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hNK : K₁ ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ K₁ : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hQH (hK₁H hg), Subgroup.le_normalizer hg⟩
  have hQK : pCoreOf 2 H ⊓ K₁ ≤ pCoreOf 2 K₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hNK
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hmemN : ∀ y : ↥K₁, (y : G) ∈ pCoreOf 2 K₁ → y ∈ CFSG.Open.pCore 2 ↥K₁ := fun y hy =>
    (Subgroup.mem_map_iff_mem K₁.subtype_injective).1 hy
  set N₀ := CFSG.Open.pCore 2 ↥K₁ with hN₀
  let x' : ↥K₁ := ⟨x, hK₁x⟩
  have hc : (QuotientGroup.mk x' : ↥K₁ ⧸ N₀) ∈ Subgroup.center (↥K₁ ⧸ N₀) := by
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | _ y =>
      have h1 : ⁅x', y⁆ ∈ N₀ := by
        apply hmemN
        have h2 : ((⁅x', y⁆ : ↥K₁) : G) = ⁅x, (y : G)⁆ := rfl
        rw [h2]
        refine hQK ⟨hcomm _ (Subgroup.mem_sup_left y.2), ?_⟩
        exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hK₁x y.2) (K₁.inv_mem hK₁x)) (K₁.inv_mem y.2)
      have h3 : ⁅QuotientGroup.mk' N₀ x', QuotientGroup.mk' N₀ y⁆ = 1 := by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).2 h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  obtain ⟨m, hm, hxm⟩ := exists_odd_pow_mem_pCoreOf hmin hxJ
  have hxm' : x' ^ m ∈ N₀ := by
    apply hmemN
    exact hQK ⟨hxm, K₁.pow_mem hK₁x m⟩
  obtain ⟨k, hk⟩ := hZ ⟨QuotientGroup.mk x', hc⟩
  have hk' : (QuotientGroup.mk x' : ↥K₁ ⧸ N₀) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hm' : (QuotientGroup.mk x' : ↥K₁ ⧸ N₀) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hxm'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have h5 : orderOf (QuotientGroup.mk x' : ↥K₁ ⧸ N₀) ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
  rw [Nat.Coprime.gcd_eq_one hcop] at h5
  have h1 : (QuotientGroup.mk x' : ↥K₁ ⧸ N₀) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)
  have hx' : x' ∈ N₀ := (QuotientGroup.eq_one_iff x').1 h1
  have hxK₁ : x ∈ pCoreOf 2 K₁ := ⟨x', hx', rfl⟩
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁H)
    (hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)) hxK₁

end CFSG.Quasithin.C126

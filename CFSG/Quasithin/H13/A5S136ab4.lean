module

public import CFSG.Quasithin.H13.A5S136ab3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq
  map_oPrimeResidualOf_top)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem inner_or_case2 (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hr : 1 < CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) {y : G} (hy : y ∈ S.Lv)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    (∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ = MulAut.conj k) ∨
      A318Case2 (starImage 3 (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hGvS : SQTKGroup ↥Gv :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian S.pCoreOf_Gv_ne_bot'
  have hSQ := SQTKHyp.of_sqtkGroup ↥Gv hGvS
  have hLc := subgroupOf_mem_cComp hKc
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := K) hKG
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hr1 : 1 < CFSG.Open.pRank 3 (K.subgroupOf Gv) := by
    rw [pRank_subgroupOf_eq hKG Nat.prime_three (by norm_num)]
    exact hr
  have hconc := a318 hF318 hGvS (h36 _ hSQ) ((a38ForSQTK_of_cat h38) _ hSQ) hLc hQ'
    Nat.prime_three (by norm_num) hr1
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3', -⟩
  ·
    left
    have hKe : K = oPrimeResidualOf 3 Gv := by
      rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hKG]
    have hyK : y ∈ K := S.Lv_le_of_eq_oPrime_or_theta (Or.inl hKe) hy
    exact ⟨_, ConfAB.indHom_of_mem (MulEquiv.refl _) hyK⟩
  · exact Or.inr h2
  ·
    exfalso
    have hZ' : Subgroup.center (↥(K.subgroupOf Gv) ⧸ CFSG.pCore 2 ↥(K.subgroupOf Gv)) = ⊥ := by
      have h1 := Subgroup.map_center_eq e₀
      rw [hZ] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).mp h1
    have h3'' : 3 ∣ Nat.card (↥(K.subgroupOf Gv) ⧸ CFSG.pCore 2 ↥(K.subgroupOf Gv)) := by
      rw [Nat.card_congr e₀.toEquiv]
      exact h3
    obtain ⟨ψ, hψ, hψk⟩ := exists_starHom1515e hQ' hZ' h3''
    obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3'
    have hzc : ψ z ∈ Subgroup.center _ := Subgroup.map_center_le_center hψ ⟨_, hzcen, rfl⟩
    rw [hZ', Subgroup.mem_bot] at hzc
    obtain ⟨k, hk⟩ := hψk _ hzc
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [hz] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

end Setting

end CFSG.Quasithin.H13.A5

module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_6 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hnil : IsTwoNilpotentOn M (V154 T Mc M)) :
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G) := by
  obtain ⟨N, hNle, hNnorm, hNodd, hN2⟩ := hnil
  have hMT : InM T M := hM.1.1
  have hTM : T ≤ M := hMT.2
  have hVn : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMT).2
  have hVelem : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hMT)
  have hTC : T ≤ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_inf hTM fun t ht => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 t ht).symm
  have hPn : M ≤ Subgroup.normalizer (preOn M (V154 T Mc M) N : Set G) :=
    le_normalizer_preOn hVn hNnorm
  have hDC : M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer ((M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        preOn M (V154 T Mc M) N : Subgroup G) : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer (inf_le_left.trans hPn)
  have key : M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
      preOn M (V154 T Mc M) N ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    by_contra hnot
    have hDV : M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        preOn M (V154 T Mc M) N ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      (inf_le_left.trans inf_le_left).trans hVn
    have hDbar : autOn (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        preOn M (V154 T Mc M) N) (V154 T Mc M) ≤ N := by
      intro a ha
      obtain ⟨x, hxN, hxD, rfl⟩ := mem_autOn_iff_exists.mp ha
      obtain ⟨-, hxN', hxL⟩ := mem_preOn.mp (Subgroup.mem_inf.mp hxD).2
      exact hxL
    have hodd : Odd (Nat.card (autOn (M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G) ⊓ preOn M (V154 T Mc M) N) (V154 T Mc M))) :=
      hNodd.of_dvd_nat (Subgroup.card_dvd_of_le hDbar)
    have hcop := commutator_inf_centralizer_eq_bot hVelem hDV hodd
    have hW1 : ⁅V154 T Mc M, M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        preOn M (V154 T Mc M) N⁆ ≠ ⊥ := fun hW =>
      hnot (le_centralizer_of_commutator_eq_bot hW)
    have hWV : ⁅V154 T Mc M, M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        preOn M (V154 T Mc M) N⁆ ≤ V154 T Mc M :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hDV
    have hTW : T ≤ Subgroup.normalizer ((⁅V154 T Mc M, M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G) ⊓ preOn M (V154 T Mc M) N⁆ : Subgroup G) : Set G) :=
      fun t ht => A4.mem_normalizer_commutator (hVn (hTM ht)) (hDC (hTC ht))
    obtain ⟨z, hzW, hz1, hzZ⟩ := exists_ne_one_mem_omegaOneCenter_of_normalized h.sylow.1
      (hWV.trans hVT) hW1 hTW
    have hzC : z ∈ Subgroup.centralizer ((M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G) ⊓ preOn M (V154 T Mc M) N : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hd).1).2 z hzZ).symm
    have hmem : z ∈ ⁅V154 T Mc M, M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G) ⊓ preOn M (V154 T Mc M) N⁆ ⊓
        (V154 T Mc M ⊓ Subgroup.centralizer ((M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G) ⊓ preOn M (V154 T Mc M) N : Subgroup G) : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hzW, Subgroup.mem_inf.mpr ⟨hWV hzW, hzC⟩⟩
    rw [hcop, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hVn hx.1
  have hxbar : conjAct (V154 T Mc M) ⟨x, hxN⟩ ∈ autOn M (V154 T Mc M) :=
    mem_autOn_iff_exists.mpr ⟨x, hxN, hx.1, rfl⟩
  obtain ⟨k, hk⟩ := hN2 _ hxbar
  refine ⟨k, ?_⟩
  have hyC : x ^ 2 ^ k ∈ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.pow_mem _ hx _
  have hyN : x ^ 2 ^ k ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
    Subgroup.pow_mem _ hxN _
  have hyP : x ^ 2 ^ k ∈ preOn M (V154 T Mc M) N := by
    refine mem_preOn.mpr ⟨hyC.1, hyN, ?_⟩
    have : conjAct (V154 T Mc M) ⟨x ^ 2 ^ k, hyN⟩ = (conjAct (V154 T Mc M) ⟨x, hxN⟩) ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [this]
    exact hk
  exact key ⟨hyC, hyP⟩

theorem stageLemma1516_of (hnil : Nilpotency1512) : StageLemma1516 := by
  intro G _ _ T Mc M h hM
  exact lemma_15_1_6 h hM (hnil G T Mc M h hM)

end CFSG.Quasithin

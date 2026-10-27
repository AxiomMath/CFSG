module

public import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactor
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASAlm
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLie
public import CFSG.Quasithin.Vol2.Ch11SecU1L3ID
public import CFSG.Adapters.StatedPSLTwo
public import TauCeti.GroupTheory.Elementary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin

variable {G : Type} [Group G]

theorem quotientActionHom_mem_innAutOf {J N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (J : Set G)) (hJN : J ≤ N) (j : J) :
    quotientActionHom J hN ⟨j, hJN j.2⟩ ∈ innAutOf (↥J ⧸ Subgroup.center ↥J) := by
  rw [quotientActionHom_mem_eq_conj hN hJN]
  exact ⟨QuotientGroup.mk' (Subgroup.center J) j, rfl⟩

theorem map_subgroupOf_quotientActionHom_le_innAutOf {J N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (J : Set G)) (hJN : J ≤ N) :
    (J.subgroupOf N).map (quotientActionHom J hN) ≤ innAutOf (↥J ⧸ Subgroup.center ↥J) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  let j : J := ⟨x, hx⟩
  have hxN : x = (⟨j, hJN j.2⟩ : N) := Subtype.ext rfl
  rw [hxN]
  exact quotientActionHom_mem_innAutOf hN hJN j

theorem map_centralizer_subgroupOf_quotientActionHom_eq_bot {J N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (J : Set G)) :
    ((Subgroup.centralizer (J : Set G)).subgroupOf N).map (quotientActionHom J hN) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  exact MonoidHom.mem_ker.mpr
    (quotientActionHom_eq_one_of_mem_centralizer hN (Subgroup.mem_subgroupOf.mp hx))

theorem nParam_le_one_of_action_image_bound [Finite G] (J B : Subgroup G)
    (hJ : Group.IsPerfect J)
    (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hCs : Group.IsSolvable ↥((Subgroup.centralizer (J : Set G)).subgroupOf B))
    (hQH : E1.nParam (⊤ : Subgroup (quotientActionHom J hBN).range) ≤ 1) :
    E1.nParam B ≤ 1 := by
  haveI : Group.IsPerfect J := hJ
  let φ : B →* MulAut (↥J ⧸ Subgroup.center ↥J) := quotientActionHom J hBN
  have hker : Group.IsSolvable ↥φ.ker := by
    rw [ker_quotientActionHom hBN]
    exact hCs
  have hQ : E1.nParam (⊤ : Subgroup (B ⧸ φ.ker)) ≤ 1 := by
    rw [E1.Eleven.nParam_top_mulEquiv (QuotientGroup.quotientKerEquivRange φ)]
    exact hQH
  rw [E1.nParam_subgroupOf B]
  exact CFSG.Quasithin.Vol2.Ch11.SecU1.nParam_le_one_of_quotient (N := φ.ker) hker hQ

theorem action_image_psl2_structure [Finite G] {p f : ℕ}
    (J B : Subgroup G) (hJ : Group.IsPerfect J)
    (hJB : J ≤ B) (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J))
    (hpow : ∀ b : B, ∃ k : ℕ,
      b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) :
    IsSimpleGroup ↥(CFSG.generalizedFitting ↥((quotientActionHom J hBN).range)) ∧
    IsPSL 2 p f ↥(CFSG.generalizedFitting ↥((quotientActionHom J hBN).range)) ∧
    ∀ S : Sylow 2 ↥((quotientActionHom J hBN).range),
      CFSG.generalizedFitting ↥((quotientActionHom J hBN).range) ⊔
        (S : Subgroup ↥((quotientActionHom J hBN).range)) = ⊤ := by
  classical
  haveI : Group.IsPerfect J := hJ
  let X := ↥J ⧸ Subgroup.center ↥J
  let φ : B →* MulAut X := quotientActionHom J hBN
  let H : Subgroup (MulAut X) := φ.range
  let I : Subgroup (MulAut X) := innAutOf X
  let IH : Subgroup H := I.subgroupOf H
  haveI : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center J))
      (QuotientGroup.mk'_surjective _)
  have hs : IsSimpleGroup X :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hPSL
  haveI : IsSimpleGroup X := hs
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    have h := Group.IsPerfect.not_isMulCommutative X
    simpa only [isMulCommutative_iff, not_forall] using h
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.Quasithin.Vol2.Ch11.SecB.center_eq_bot_of_nonabelian' hnab
  have hIH : I ≤ H := inner_le_range_quotientActionHom hBN hJB
  haveI : IH.Normal := normal_innAutOf_subgroupOf hIH
  have hFstar : CFSG.generalizedFitting H = IH :=
    generalizedFitting_eq_innAutOf_subgroupOf hs hnab hIH
  have hmapJ : (J.subgroupOf B).map φ ≤ I :=
    map_subgroupOf_quotientActionHom_le_innAutOf hBN hJB
  have hmapC : ((Subgroup.centralizer (J : Set G)).subgroupOf B).map φ ≤ I := by
    rw [map_centralizer_subgroupOf_quotientActionHom_eq_bot hBN]
    exact bot_le
  have hmap : ((J.subgroupOf B ⊔
      (Subgroup.centralizer (J : Set G)).subgroupOf B).map φ) ≤ I := by
    rw [Subgroup.map_sup]
    exact sup_le hmapJ hmapC
  have hpowH : ∀ a : H, ∃ k : ℕ, a ^ 2 ^ k ∈ IH := by
    intro a
    obtain ⟨b, hb⟩ := a.2
    obtain ⟨k, hk⟩ := hpow b
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    have hval : ((a ^ 2 ^ k : H) : MulAut X) = φ (b ^ 2 ^ k) := by
      rw [Subgroup.coe_pow, ← hb, ← map_pow]
    rw [hval]
    exact hmap ⟨b ^ 2 ^ k, hk, rfl⟩
  have hquot : IsPGroup 2 (H ⧸ IH) :=
    TauCeti.isPGroup_quotient_of_forall_exists_pow_mem hpowH
  obtain ⟨e⟩ := nonempty_mulEquiv_innAutOf_subgroupOf hZ hIH
  have hsF : IsSimpleGroup ↥(CFSG.generalizedFitting H) := by
    rw [hFstar]
    exact e.isSimpleGroup
  have hF : IsPSL 2 p f ↥(CFSG.generalizedFitting H) := by
    rw [hFstar]
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hPSL
  refine ⟨hsF, hF, ?_⟩
  intro S
  have hFT : CFSG.generalizedFitting H ⊔ (S : Subgroup H) = ⊤ := by
    rw [hFstar, sup_comm]
    exact CFSG.GorensteinWalter.preambleSylow_sup_of_quotient_pgroup IH S hquot
  exact hFT

theorem nParam_le_one_of_action_image_psl2_pow [Finite G]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (J B : Subgroup G) (hJ : Group.IsPerfect J)
    (hJB : J ≤ B) (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J))
    (hpow : ∀ b : B, ∃ k : ℕ,
      b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) :
    E1.nParam (⊤ : Subgroup (quotientActionHom J hBN).range) ≤ 1 := by
  obtain ⟨hsF, hF, hsup⟩ := action_image_psl2_structure J B hJ hJB hBN hPSL hpow
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := (quotientActionHom J hBN).range)
  exact CFSG.Quasithin.RonanE114.L2.nParam_le_one_of_psl2_pow hp hp2 hf hsF hF
    S.isPGroup' (hsup S)

theorem nParam_le_one_of_action_image_psl2_noSQ [Finite G]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (J B : Subgroup G) (hJ : Group.IsPerfect J)
    (hJB : J ≤ B) (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J))
    (hpow : ∀ b : B, ∃ k : ℕ,
      b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) :
    E1.nParam (⊤ : Subgroup (quotientActionHom J hBN).range) ≤ 1 := by
  obtain ⟨hsF, hF, hsup⟩ := action_image_psl2_structure J B hJ hJB hBN hPSL hpow
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := (quotientActionHom J hBN).range)
  exact nParam_le_one_of_isPSL2_noSQ hsF ⟨S.isPGroup', S.not_dvd_index⟩ (hsup S)
    hp hp2 h5 hF

theorem nParam_le_one_of_normalized_perfect_psl2_two_action [Finite G]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (J B : Subgroup G) (hJ : Group.IsPerfect J)
    (hJB : J ≤ B) (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J))
    (hCs : Group.IsSolvable ↥((Subgroup.centralizer (J : Set G)).subgroupOf B))
    (hpow : ∀ b : B, ∃ k : ℕ,
      b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) :
    E1.nParam B ≤ 1 :=
  nParam_le_one_of_action_image_bound J B hJ hBN hCs
    (nParam_le_one_of_action_image_psl2_pow hp hp2 hf J B hJ hJB hBN hPSL hpow)

theorem nParam_le_one_of_normalized_perfect_psl2_two_action_of_five_lt [Finite G]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (J B : Subgroup G) (hJ : Group.IsPerfect J)
    (hJB : J ≤ B) (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J))
    (hCs : Group.IsSolvable ↥((Subgroup.centralizer (J : Set G)).subgroupOf B))
    (hpow : ∀ b : B, ∃ k : ℕ,
      b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) :
    E1.nParam B ≤ 1 :=
  nParam_le_one_of_action_image_bound J B hJ hBN hCs
    (nParam_le_one_of_action_image_psl2_noSQ hp hp2 h5 J B hJ hJB hBN hPSL hpow)

end CFSG.LocalAnalysis.WeakClosure81

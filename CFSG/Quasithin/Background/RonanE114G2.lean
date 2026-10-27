module

public import CFSG.Quasithin.Background.RonanE114QPair
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

section Ordinary


variable {τ : Tag} {K : Type} [Field K]

theorem rankOneSubgroup_le_parabolic (i : Fin τ.rank) :
    rankOneSubgroup (τ := τ) (K := K) i ≤
      (parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K) := by
  have hx : ∀ c : K, xUnit τ K i c ∈ parabolicSubgroup τ K {i} := fun c =>
    parabolicLevi_le_parabolicSubgroup {i} (xUnit_mem_parabolicLevi (Set.mem_singleton i) c)
  have hy : ∀ c : K, yUnit τ K i c ∈ parabolicSubgroup τ K {i} := fun c =>
    parabolicLevi_le_parabolicSubgroup {i} (yUnit_mem_parabolicLevi (Set.mem_singleton i) c)
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hg
    exact Subgroup.mem_subgroupOf.2 (by rw [hc]; exact hx c)
  · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hg
    exact Subgroup.mem_subgroupOf.2 (by rw [hc]; exact hy c)

theorem iSup_perfectCore_parabolic_eq_top [Finite K] (hK4 : 4 ≤ Nat.card K) :
    ⨆ i : Fin τ.rank,
      perfectCore ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)) = ⊤ := by
  have hK4' : (4 : ℕ∞) ≤ ENat.card K := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hK4
  rw [eq_top_iff, ← iSup_simplePosSubgroup_sup_simpleNegSubgroup]
  refine iSup_mono fun i => ?_
  have hperf : ⁅rankOneSubgroup (τ := τ) (K := K) i, rankOneSubgroup (τ := τ) (K := K) i⁆ =
      rankOneSubgroup (τ := τ) (K := K) i :=
    Subgroup.isPerfect_iff.mp ⟨(rank_one_scalar_perfect τ K i).2 hK4'⟩
  exact le_perfectCore_of_perfect (rankOneSubgroup_le_parabolic i) hperf

theorem hasQuotPair_of_invariant [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n)
    (hinv : ∀ α : MulAut ↥(adjointGroup τ K),
      ((posUnipotent τ K).subgroupOf (adjointGroup τ K)).map α.toMonoidHom =
        (posUnipotent τ K).subgroupOf (adjointGroup τ K) →
      ∀ i : Fin τ.rank, ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)).map
        α.toMonoidHom = (parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)) :
    HasQuotPair ↥(adjointGroup τ K)
      ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) n := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨Fin τ.rank, fun i => (parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K), hinv,
    ?_, fun i => ?_⟩
  · rw [iSup_perfectCore_parabolic_eq_top hK4, top_sup_eq]
  · obtain ⟨g, hg, hk⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom_adjoint
      (τ := τ) (K := K) hK hn i
    exact ⟨_, inferInstance, g, Rk1.sl2 hK hK4, hg, hk⟩

end Ordinary

section G2


variable {G : Type} [Group G] [Finite G]

theorem inEFor_of_isG2 {L T : Subgroup G} (hLn : L.Normal) (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) {n : ℕ} (hG2 : CFSG.Quasithin.IsG2 2 n ↥L) : E1.InEFor n ⊤ T := by
  obtain ⟨hn2, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hG2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  exact inEFor_of_hasQuotPair hLn hT hLT e hU₀
    (hasQuotPair_of_invariant hK hn2 fun α hα i => G2_invariant_parabolic hK4 hα i)

theorem nParam_le_of_isG2 {T : Subgroup G} {n : ℕ} (hLn : (CFSG.generalizedFitting G).Normal)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hG2 : CFSG.Quasithin.IsG2 2 n ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  obtain ⟨hn2, -⟩ := exists_mulEquiv_G2_model hG2
  exact (E1.nParam_le_iff (by omega)).mpr
    ((E1.inE_iff_inEFor hT).mpr (inEFor_of_isG2 hLn hT hFT hG2))

end G2

end CFSG.Quasithin.RonanE114

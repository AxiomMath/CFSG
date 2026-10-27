module

public import CFSG.Assembly.OrderReductions.StrongEmbeddingDoubleTransitivity
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore
import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem fusionStronglyEmbedded_to_orderReduction (H : Subgroup G)
    (hH : fusionStronglyEmbedded H) :
    CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded H :=
  (stronglyEmbedded_right_conjugate_iff H).mpr hH

theorem rank_two_exists_commuting_involutions (hrank : TwoRankAtLeastTwo G) :
    ∃ a b : CFSG.OrderReductions.InvolutionGraph.Involution G,
      a ≠ b ∧ Commute a.val b.val := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hcard, hsq⟩ := hrank
  obtain ⟨a, b, ha, hb, hab⟩ :=
    CFSG.BenderSuzuki.PFchapter1section2.proposition_1_b_exists_two_distinct_nontrivial_of_card_four
      hcard
  have hcommE : Commute a b :=
    (isMulCommutative_of_forall_sq_one hsq).is_comm.comm a b
  have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hbG : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have haOrder : orderOf (a : G) = 2 :=
    orderOf_eq_prime (congrArg Subtype.val (hsq a)) haG
  have hbOrder : orderOf (b : G) = 2 :=
    orderOf_eq_prime (congrArg Subtype.val (hsq b)) hbG
  refine ⟨⟨a, haOrder⟩, ⟨b, hbOrder⟩, ?_, ?_⟩
  · intro h
    exact hab (Subtype.ext (congrArg
      (fun z : CFSG.OrderReductions.InvolutionGraph.Involution G => z.val) h))
  · exact hcommE.map E.subtype

theorem native_twoPrimeCore_eq_bot_of_orderReduction_oddCore_eq_bot
    (hcore : CFSG.OrderReductions.OddCore.oddCore G = ⊥) :
    pPrimeCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 G)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := G) (p := 2))
  have hle := CFSG.OrderReductions.OddCore.normal_le_oddCore
    (pPrimeCore 2 G) hodd
  rw [hcore] at hle
  exact bot_unique hle

theorem orderReduction_rank_one_coreFree_centrality
    (hno : CFSG.OrderReductions.RankOneInduction.NoFourInvolutions G)
    (hcore : CFSG.OrderReductions.OddCore.oddCore G = ⊥)
    (z : CFSG.OrderReductions.InvolutionGraph.Involution G) :
    z.val ∈ Subgroup.center G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : ¬ TwoRankAtLeastTwo G := by
    intro h
    obtain ⟨a, b, hab, hcomm⟩ := rank_two_exists_commuting_involutions h
    exact hab (hno a b hcomm)
  have hz : IsInvolution z.val := by
    exact ⟨(orderOf_eq_prime_iff.mp z.property).2,
      (orderOf_eq_prime_iff.mp z.property).1⟩
  have hfactor :=
    CFSG.BenderSuzuki.PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      hrank hz
  rw [native_twoPrimeCore_eq_bot_of_orderReduction_oddCore_eq_bot hcore,
    bot_sup_eq] at hfactor
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hg : g ∈ Subgroup.centralizer ({z.val} : Set G) := by
    rw [hfactor]
    trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

theorem rank_two_strongEmbedding_conjugates_double_transitive
    (hrank : TwoRankAtLeastTwo G) (H : Subgroup G)
    (hH : fusionStronglyEmbedded H) :
    MulAction.IsMultiplyPretransitive G (Conjugates H) 2 := by
  obtain ⟨a, b, hab, hcomm⟩ := rank_two_exists_commuting_involutions hrank
  exact CFSG.OrderReductions.StrongEmbeddingDoubleTransitivity.double_transitive_of_odd_order_and_rank_one_inputs
      CFSG.FeitThompson.isSolvable_of_odd_natCard
      (fun _ _ _ hno hcore z =>
        orderReduction_rank_one_coreFree_centrality hno hcore z)
      G a b hab hcomm H (fusionStronglyEmbedded_to_orderReduction H hH)

theorem rank_two_strongEmbedding_isCoatom (hrank : TwoRankAtLeastTwo G)
    (H : Subgroup G) (hH : fusionStronglyEmbedded H) : IsCoatom H := by
  have horder := fusionStronglyEmbedded_to_orderReduction H hH
  let : MulAction.IsPreprimitive G (Conjugates H) :=
    MulAction.isPreprimitive_of_is_two_pretransitive
      (rank_two_strongEmbedding_conjugates_double_transitive hrank H hH)
  let : Nontrivial (Conjugates H) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      have hcard := conjugates_card_ge_three H horder
      omega)
  let base : Conjugates H := ⟨H, ⟨1, one_smul G H⟩⟩
  have hmax := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G base
  rwa [conjugate_stabilizer_eq H horder base] at hmax

omit [Finite G] in
theorem fusionStronglyEmbedded_inf_of_even (H K : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hK : fusionStronglyEmbedded K)
    (heven : Even (Nat.card ↥(H ⊓ K))) : fusionStronglyEmbedded (H ⊓ K) := by
  refine ⟨?_, heven, ?_⟩
  · intro htop
    exact hH.1 (top_unique (htop ▸ (inf_le_left : H ⊓ K ≤ H)))
  · intro g hg
    by_cases hgH : g ∈ H
    · have hgK : g ∉ K := fun h => hg ⟨hgH, h⟩
      have hle :
          (H ⊓ K) ⊓ (H ⊓ K).map (MulAut.conj g⁻¹).toMonoidHom ≤
            K ⊓ K.map (MulAut.conj g⁻¹).toMonoidHom :=
        inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)
      exact (hK.2.2 g hgK).of_dvd_nat (Subgroup.card_dvd_of_le hle)
    · have hle :
          (H ⊓ K) ⊓ (H ⊓ K).map (MulAut.conj g⁻¹).toMonoidHom ≤
            H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom :=
        inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)
      exact (hH.2.2 g hgH).of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem rank_two_strongEmbedding_eq_of_even_inf (hrank : TwoRankAtLeastTwo G)
    (H K : Subgroup G) (hH : fusionStronglyEmbedded H)
    (hK : fusionStronglyEmbedded K) (heven : Even (Nat.card ↥(H ⊓ K))) : H = K := by
  have hmax := rank_two_strongEmbedding_isCoatom hrank (H ⊓ K)
    (fusionStronglyEmbedded_inf_of_even H K hH hK heven)
  have hHinf : H = H ⊓ K :=
    (hmax.le_iff_eq hH.1).mp inf_le_left
  have hKinf : K = H ⊓ K :=
    (hmax.le_iff_eq hK.1).mp inf_le_right
  exact hHinf.trans hKinf.symm

theorem rank_two_strongEmbedding_conjugate (hrank : TwoRankAtLeastTwo G)
    (H K : Subgroup G) (hH : fusionStronglyEmbedded H)
    (hK : fusionStronglyEmbedded K) :
    ∃ g : G, H.map (MulAut.conj g⁻¹).toMonoidHom = K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSH⟩ := contains_sylow H (fusionStronglyEmbedded_to_orderReduction H hH)
  obtain ⟨T, hTK⟩ := contains_sylow K (fusionStronglyEmbedded_to_orderReduction K hK)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hSmap : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = T := by
    change (g • S : Sylow 2 G).toSubgroup = T.toSubgroup
    rw [hg]
  have hTH : (T : Subgroup G) ≤ H.map (MulAut.conj g).toMonoidHom := by
    rw [← hSmap]
    exact Subgroup.map_mono hSH
  have hevenG : Even (Nat.card G) :=
    even_iff_two_dvd.mpr (hH.2.1.two_dvd.trans (Subgroup.card_subgroup_dvd_card H))
  have hevenT : Even (Nat.card T) :=
    even_iff_two_dvd.mpr (T.dvd_card_of_dvd_card hevenG.two_dvd)
  have hevenInf : Even (Nat.card ↥(H.map (MulAut.conj g).toMonoidHom ⊓ K)) :=
    even_iff_two_dvd.mpr
      (hevenT.two_dvd.trans (Subgroup.card_dvd_of_le (le_inf hTH hTK)))
  have heq := rank_two_strongEmbedding_eq_of_even_inf hrank
    (H.map (MulAut.conj g).toMonoidHom) K
    (hH.map_mulEquiv (MulAut.conj g)) hK hevenInf
  exact ⟨g⁻¹, by simpa only [inv_inv] using heq⟩

theorem rank_two_strongEmbedding_maximality_and_conjugacy
    (hrank : TwoRankAtLeastTwo G) :
    (∀ H : Subgroup G, fusionStronglyEmbedded H → IsCoatom H) ∧
      (∀ H K : Subgroup G, fusionStronglyEmbedded H → fusionStronglyEmbedded K →
        Even (Nat.card ↥(H ⊓ K)) → H = K) ∧
      (∀ H K : Subgroup G, fusionStronglyEmbedded H → fusionStronglyEmbedded K →
        ∃ g : G, H.map (MulAut.conj g⁻¹).toMonoidHom = K) :=
  ⟨rank_two_strongEmbedding_isCoatom hrank,
    rank_two_strongEmbedding_eq_of_even_inf hrank,
    rank_two_strongEmbedding_conjugate hrank⟩

end CFSG.ShultStronglyClosedTI

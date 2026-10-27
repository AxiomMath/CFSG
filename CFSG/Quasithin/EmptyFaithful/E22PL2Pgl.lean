module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Quasithin.EmptyFaithful.E22PD1
import CFSG.Quasithin.EmptyFaithful.E22PS4
import CFSG.Quasithin.EmptyFaithful.E22PDick
import CFSG.Quasithin.EmptyFaithful.E22PGen
import CFSG.Quasithin.EmptyFaithful.E22PTypeII
import CFSG.Quasithin.EmptyFaithful.E22PL2PglB
import CFSG.Quasithin.EmptyFaithful.E22PL2PglC
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two)

theorem inEFor_pgl2_of_coatom_q
    {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) (hq7 : 7 ≤ Nat.card K)
    {T : Subgroup (PGL2 K)} (hT : IsSylowIn 2 T ⊤)
    (hcoat : ∀ {z : PGL2 K}, orderOf z = 2 → z ∈ commutator (PGL2 K) →
      IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K)))) :
    InEFor 1 ⊤ T := by
  have := e22pl2pgl_finite K
  have hcard3 : 3 < Nat.card K := by omega
  have hcomm : commutator (PGL2 K) = pslRange K :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd hcard3
  have : (pslRange K).Normal := pslRange_normal hodd hcard3
  have : IsSimpleGroup ↥(pslRange K) := e22pl2pgl_simple_J hcard3
  have hnc := e22pl2pgl_nonabelian_J hcard3
  have hCJ := e22pl2pgl_centralizer_J hodd hcard3
  have hJT := e22pl2pgl_sup_eq_top hodd hT
  obtain ⟨m, hm3, ⟨e⟩⟩ := e22pl2pgl_sylow_dihedral_q hodd hq8 hT
  have hm2 : 2 ≤ m := by omega
  obtain ⟨z, hzT, hz2, hzc, hzV, hAV⟩ := dihedral_sylow_data hm2 e
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  obtain ⟨t, -, htz⟩ := dihedral_central_involution_sq hm2 e hzT hz2 hzc
  have hzJ : z ∈ pslRange K := by
    rw [← htz]
    have := Subgroup.pow_index_mem (pslRange K) t
    rwa [pslRange_index_eq_two hodd] at this
  have hzJ' : z ∈ commutator (PGL2 K) := hcomm ▸ hzJ
  have hTD : T ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzc x hx).symm
  have hDs := pgl2_centralizer_inner_involution_isSolvable hodd hcard3 hz2 hzJ'
  have hDmax := hcoat hz2 hzJ'
  have hO2 : pCoreOf 2 (⊤ : Subgroup (PGL2 K)) = ⊥ :=
    pCoreOf_top_eq_bot_of_normal_simple (pslRange K) hnc hCJ
  have hII : ∀ A : Subgroup (PGL2 K), A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤ :=
    fun A hAT hA => isE_one_top_of_almostSimple (pslRange K) T A hnc hCJ hT hJT hAT hA
  refine inEFor_top_of_coatom hT hTD hDs hDmax hII ?_
  intro A hAT hAab hA4
  obtain ⟨hAcard, hAK⟩ := hAV A hAT hAab hA4
  by_cases hAJ : A ≤ pslRange K
  ·
    obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC, hcomm'⟩ :=
      dihedral_kleinFour_partner hm2 e hAT hAK
    have hV'J : V' ≤ pslRange K := by
      have hT₀ := dihedral_normalizer_le_of_index_two (T₀ := T ⊓ pslRange K) hm3 e inf_le_left
        (e22pl2pgl_relIndex_inf hodd hcard3 hT) (le_inf hAT hAJ) hAK hV'T hV' hVN hV'N hne hN8
      exact ((le_inf hV'T Subgroup.le_normalizer).trans hT₀).trans inf_le_right
    have hcent : Subgroup.centralizer (V' : Set (PGL2 K)) = V' :=
      pgl2_kleinFour_centralizer_eq_self K hodd V' hV'
    have hsurj := e22pl2pgl_normalizer_surjective_q hodd hq8 hq7 hV'J hV'
    exact ⟨Subgroup.normalizer (V' : Set (PGL2 K)),
      isE_one_normalizer_kleinFour hT hO2 hAK hV' hAT hV'T hne hcent hsurj hN8 hVN hC hcomm',
      not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') hz1⟩
  ·
    exact e22pl2pgl_outer_member hodd hcard3 hT hAT hAab hAcard hO2 (hzV A hAT hAK) hz2 hzJ hAJ

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem inEFor_pgl2_of_coatom
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    {T : Subgroup (PGL2 K)} (hT : IsSylowIn 2 T ⊤)
    (hcoat : ∀ {z : PGL2 K}, orderOf z = 2 → z ∈ commutator (PGL2 K) →
      IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K)))) :
    InEFor 1 ⊤ T :=
  inEFor_pgl2_of_coatom_q (e22pl2pgl_isOddPrimePower hp7 hK) (by rwa [hK]) (by omega) hT hcoat

theorem inEFor_pgl2_prime
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p)
    (hK : Nat.card K = p) {T : Subgroup (PGL2 K)} (hT : IsSylowIn 2 T ⊤) :
    InEFor 1 ⊤ T :=
  inEFor_pgl2_of_coatom hp8 (by omega) hK hT fun hz hzJ =>
    pgl2_centralizer_inner_involution_isCoatom hK hp8 hp17 hz hzJ

end CFSG.Quasithin.E22L2

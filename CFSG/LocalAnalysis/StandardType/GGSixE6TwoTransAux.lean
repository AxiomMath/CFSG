module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LargeExtraspecial.A2ModOrdCard
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.Adapters.TauCetiExceptional.BridgeTransport
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section Generic

private noncomputable def quotCenterEquiv {X S : Type} [Group X] [Group S] (e : X ≃* S) :
    X ⧸ Subgroup.center X ≃* S ⧸ Subgroup.center S :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center S) e (Subgroup.map_center_eq e)

private theorem center_eq_bot_of_mulEquiv {X S : Type} [Group X] [Group S] (e : X ≃* S)
    (h : Subgroup.center S = ⊥) : Subgroup.center X = ⊥ := by
  have hmap := Subgroup.map_center_eq e
  rw [h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) e.injective).mp hmap

theorem isQuasisimple_map_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    {J' : Subgroup E} (h : CFSG.Assembly.IsQuasisimple ↥J') :
    CFSG.Assembly.IsQuasisimple ↥(J'.map θ.toMonoidHom) := by
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective J' θ.toMonoidHom θ.injective).symm h

theorem lieModel_map_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E') {J' : Subgroup E}
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (↥J' ⧸ Subgroup.center ↥J') t n p f) :
    LieModel (↥(J'.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J'.map θ.toMonoidHom)) t n p f := by
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (quotCenterEquiv (Subgroup.equivMapOfInjective J' θ.toMonoidHom θ.injective)) h

theorem thirtyOne_dvd_card_centralizer {E : Type} [Group E] [Finite E] {x₀ : E} {L' : Subgroup E}
    (hcomp : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({x₀} : Set E)))
    (hL : LieModel (↥L' ⧸ Subgroup.center ↥L') .PSL 6 2 1) :
    31 ∣ Nat.card (Subgroup.centralizer ({x₀} : Set E)) := by
  have hcard : Nat.card (↥L' ⧸ Subgroup.center ↥L') = ordA 5 2 := by
    simpa using (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSL hL).2
  have h31 : 31 ∣ Nat.card (↥L' ⧸ Subgroup.center ↥L') := by
    rw [hcard]
    exact thirtyOne_dvd_ordA
  have h31L : 31 ∣ Nat.card ↥L' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L')]
    exact dvd_mul_of_dvd_left h31 _
  have hdvd : Nat.card ↥L' ∣ Nat.card (Subgroup.centralizer ({x₀} : Set E)) :=
    Subgroup.card_dvd_of_le hcomp.1
  exact h31L.trans hdvd

end Generic

section TransAux

theorem nonempty_mulEquiv_EC {E : Type} [Group E] [Finite E] (hperf : commutator E = ⊤)
    (hL : LieModel (E ⧸ Subgroup.center E) .E6 0 2 1) : Nonempty (E ≃* EC) := by
  have hcenter : Subgroup.center E = ⊥ := ggSixE6A24_center_eq_bot E hperf hL
  rcases hL with ⟨ht, -⟩ | ⟨-, -, hch⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hch
    have hK2 : Nat.card K = 2 := by simpa using hK
    haveI := Fintype.ofFinite K
    haveI : Fintype F2 := Fintype.ofFinite F2
    have hcardK : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK2
    have hcardF2 : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
      norm_num
    have hcard : Fintype.card K = Fintype.card F2 := by rw [hcardK, hcardF2]
    let σ : K ≃+* F2 := FiniteField.ringEquivOfCardEq hcard
    have hcenK : Subgroup.center (adjointGroup .E6 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have p : E ≃* (E ⧸ Subgroup.center E) :=
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    have q : AdjointQuotient .E6 K ≃* ↥(adjointGroup .E6 F2) :=
      ((QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot).trans
        (CFSG.TauCetiBridge.adjointGroupCongr σ)
    exact ⟨(p.trans e).trans q⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem ne_one_of_isComponentOf {E : Type} [Group E] [Finite E] (θ : E ≃* EC) {x₀ : E}
    {L' : Subgroup E}
    (hcomp : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({x₀} : Set E)))
    (hL : LieModel (↥L' ⧸ Subgroup.center ↥L') .PSL 6 2 1) : x₀ ≠ 1 := by
  intro hx
  have hC : Subgroup.centralizer ({x₀} : Set E) = ⊤ := by
    rw [hx, Subgroup.centralizer_eq_top_iff_subset]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.one_mem _
  have hsub : CFSG.Assembly.IsSubnormal L' ⊤ := by
    rw [hC] at hcomp
    exact hcomp.2.1
  haveI hEC : IsSimpleGroup EC := isSimpleGroup_EC
  haveI hE : IsSimpleGroup E := θ.isSimpleGroup
  have hQcard : Nat.card (↥L' ⧸ Subgroup.center ↥L') = ordA 5 2 := by
    simpa using (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSL hL).2
  rcases CFSG.Assembly.IsSubnormal.eq_bot_or_top hsub with hbot | htop
  · have hsimple := hcomp.2.2.2
    rw [hbot] at hsimple
    haveI : IsSimpleGroup (↥(⊥ : Subgroup E) ⧸ Subgroup.center ↥(⊥ : Subgroup E)) := hsimple
    haveI : Subsingleton ↥(⊥ : Subgroup E) :=
      ⟨fun a b => Subtype.ext (by
        rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
    haveI : Subsingleton (↥(⊥ : Subgroup E) ⧸ Subgroup.center ↥(⊥ : Subgroup E)) :=
      inferInstance
    obtain ⟨a, b, hab⟩ :=
      exists_pair_ne (↥(⊥ : Subgroup E) ⧸ Subgroup.center ↥(⊥ : Subgroup E))
    exact hab (Subsingleton.elim a b)
  · have hcenter : Subgroup.center E = ⊥ :=
      center_eq_bot_of_mulEquiv θ center_EC
    have hEcard : Nat.card E = ordE6 2 :=
      (Nat.card_congr θ.toEquiv).trans card_EC
    have hQtop : Nat.card (↥L' ⧸ Subgroup.center ↥L') = Nat.card E := by
      rw [htop]
      calc Nat.card (↥(⊤ : Subgroup E) ⧸ Subgroup.center ↥(⊤ : Subgroup E))
          = Nat.card (E ⧸ Subgroup.center E) :=
            Nat.card_congr (quotCenterEquiv (Subgroup.topEquiv (G := E))).toEquiv
        _ = Nat.card (E ⧸ (⊥ : Subgroup E)) := by rw [hcenter]
        _ = Nat.card E := Nat.card_congr (QuotientGroup.quotientBot).toEquiv
    have hcontra : ordA 5 2 = ordE6 2 := hQcard.symm.trans (hQtop.trans hEcard)
    exact ordE6_ne_ordA hcontra.symm

end TransAux

end CFSG.StandardType.GGSixE6Two

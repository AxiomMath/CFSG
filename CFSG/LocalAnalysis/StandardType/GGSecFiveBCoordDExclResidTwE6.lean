module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4ZKE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclCensus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certificates


theorem ggSecFiveBCoordDExclRestOn_twE6Two_neighbour
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp3 : p = 3)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧ lab.tag = .twE6) p Bs K) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  subst hp3
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have hH : GGResHyp 3 B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have hS : lab.n = 1 ∧ lab.tag = .twE6 := hP.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hP.2.1
  have hInn : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    largeEvenMarking_mono
      (fun _ _ _ _ _ _ hP =>
        ⟨⟨hP.1.2, rfl, by rw [hP.1.1]; norm_num⟩,
          Or.inr (Or.inr (Or.inr ⟨hP.1.1, rfl⟩)), hP.2.1, hP.2.2⟩) hM
  have hsc : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcard : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    hRk G 3 B Bs x L D J hcfg rfl y K hnb hInn hN (ggTorusSelfCent_ggGamma hN hsc)
  have hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer K Bs) :=
    GGResHyp.weylOfType_E6_of_card_gamma_five hRig hH hlab hhas
      (Or.inr ⟨hS.2, by rw [hS.1]; norm_num⟩) hN hcard
  exact map_le_coordProdStab_of_weylOfType_noFour hp hp2 coxeterMatrixE₆_noFour hW eta
    (map_ggAutomizer_le_bSignedFull_of_join hK𝒦 eta hK)

theorem ggSecFiveBCoordDExclRestOn_twE6Two (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput) :
    GGSecFiveBCoordDExclRestOn (fun _ lab => lab.n = 1 ∧ lab.tag = .twE6) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  subst hp3
  have hIncl :=
    ggSecFiveBCoordDExclRestOn_twE6Two_neighbour hRig hRk hR rfl eta hK hK𝒦 hnb hM
  rcases hsgn with ⟨i, hri⟩
  exact false_of_sgnAut_mem_map_coordProdStab Nat.prime_three (by norm_num) eta hr hri hIncl

end Certificates

end CFSG.StandardType

end

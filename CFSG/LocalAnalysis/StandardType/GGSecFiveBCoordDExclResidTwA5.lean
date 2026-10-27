module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclCensus
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveBCoordDExclRestOn_twA5Two_neighbour
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp3 : p = 3)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧ lab.tag = .twA ∧ lab.rank = 5) p Bs K) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  subst hp3
  have hH : GGResHyp 3 B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hcfg.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have htag : lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    ⟨hP.1.2.1, hP.1.2.2, by rw [hP.1.1]; norm_num⟩
  obtain ⟨f, hN, hf, hpq, hTor⟩ :=
    ggTwA5Three_torDataAt hRig hLB hPJ hH (X := K) (z := y)
      (Or.inr ⟨rfl, rfl⟩) rfl hlab hhas htag
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  obtain ⟨φ, e, hφ, he, hcl⟩ :=
    ggNbr_weylDatum_of_row hp hp2 (ggIntCartan_A 5) hodd hpq hBs hS hN hTor
  have hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n 3 :=
    map_ggAutomizer_le_bSignedFull_of_join hK𝒦 eta hK
  exact map_le_coordProdStab_of_coxeter_noFour hp hp2 (coxeterMatrixA_noFour (by norm_num))
    φ hφ e he hcl eta hAK

theorem ggSecFiveBCoordDExclRestOn_twA5Two
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) :
    GGSecFiveBCoordDExclRestOn (fun _ lab => lab.n = 1 ∧ lab.tag = .twA ∧ lab.rank = 5) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  subst hp3
  have hIncl :=
    ggSecFiveBCoordDExclRestOn_twA5Two_neighbour hRig hLB hPJ hR rfl eta hK hK𝒦 hnb hM
  rcases hsgn with ⟨i, hri⟩
  exact false_of_sgnAut_mem_map_coordProdStab (by norm_num) (by norm_num) eta hr hri hIncl

end CFSG.StandardType

end

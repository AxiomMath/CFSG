module

public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput
public import CFSG.LocalAnalysis.StandardType.GGTBTorTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
import CFSG.LocalAnalysis.StandardType.GGE6D4TwRank
import CFSG.LocalAnalysis.StandardType.GGE6D4LocalDatum
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGTBTorCentral
import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace E6D4Tw

theorem ggE6D4TwoNodeTwXDatum_of_tbTor (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hQ1 : GGBstarInnerDiagJInput)
    (hTw : GGTBTorTwE6Three) : GGE6D4TwoNodeTwXDatum := by
  intro G _ _ B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow htag
  obtain ⟨-, -, -, -, -, hDt, -⟩ := hT
  obtain ⟨n, rfl, hcase⟩ := E6D4J.row_cases hrow (Or.inr htag)
  obtain ⟨h3n, rfl⟩ : 3 ∣ 2 ^ n + 1 ∧ labX = ⟨.twE6, 0, n⟩ := by
    rcases hcase with ⟨-, rfl⟩ | h
    · simp at htag
    · exact h
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := Or.inr h3n
  have hInnJ : GGInnerDiagOn Bs J := hQ1 G 3 B Bs x L D J hH.1 hH.2.2.1.1
  obtain ⟨hNJ, hTorJ⟩ := E6D4J.torData_J hRig hDt hLift hH hInnJ hJΛ hJl h3
  obtain ⟨hm, h3m⟩ := E6D4J.odd_and_dvd_ggTorMpm (n := n) hJΛ.1 h3
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDc : Nat.card (B ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2 := by
    rw [← hDeq]
    exact hH.1.2.2.1.2.2.1
  obtain ⟨-, hS4, -, -⟩ := E6D4J.clauses_of_torData hm h3m hBs hSC hH.1.2.1.1
    hH.1.2.1.2.2.1 hDc hNJ hTorJ
  have hZ := E6D4J.inf_centralizer_eq_one_of_torData hm h3m hBs hNJ hTorJ
  have h3J : 3 ∣ Nat.card J := by
    have hd := Subgroup.card_dvd_of_le (inf_le_right : Bs ⊓ J ≤ J)
    rw [hS4] at hd
    exact (dvd_pow_self 3 (by norm_num)).trans hd
  have hdata : z ∈ Subgroup.centralizer (X : Set G) ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
      GGInnerDiagOn Bs X ∧ commutator ↥X = ⊤ ∧ J ≤ X := by
    rcases hXz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := GGConfig.data_L hH.1
      exact ⟨hc, h1, hpz, hH.2.2.1.1, hperf,
        (hH.1.2.2.1.2.2.2.2.2.1).1.trans inf_le_left⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := hH.data_K
      exact ⟨hc, h1, hpz, hH.2.2.1.2 _ _ hH.2.2.2.2.1, hperf,
        le_of_ggNbr hLB hH.1.1 hH.1.2.2 h3J hH.2.2.2.2.1⟩
  obtain ⟨hzc, hz1, hzp, hInn, hXperf, hJX⟩ := hdata
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := ggInnerDiagOn_le_normalizer hInn
  obtain ⟨d, hdBs, hdJ, hdX⟩ := exists_mem_centralizer_not_mem_centralizer hH hXz
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range :=
    pow_five_le_card_range_ggGamma hBs hJX hN hS4 hZ hdBs hdJ hdX
  have h3c : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range := le_trans (by norm_num) h5
  have hM3 : 3 ∣ ggTorM ⟨.twE6, 0, n⟩ := by simpa [ggTorM] using h3n
  have hmark := ggInnerDiagOn_relabel hRig hInn hXΛ hXl
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = ⟨.twE6, 0, n⟩)
    (P' := fun R _ I _ => GGTorusTorW 3 5 (ggTorM ⟨.twE6, 0, n⟩) 6 CartanMatrix.E₆
      CoxeterMatrix.E₆ R I)
    (fun lab' _ h' => by rw [h']; exact hTw _ hXΛ rfl hM3)
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨-, lab', -, hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hind⟩, hWtor⟩⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  obtain ⟨w, hw⟩ := hWtor ↥X (ggQuotHom θ) (ggGamma X hN).range
    (ggTorusTBGroup_of_marking hp hBs hSC hXperf θ hN hBsI h5 h3c)
  have hodd : Odd (ggTorM ⟨.twE6, 0, n⟩) := by
    have hn1 : 1 ≤ n := hXΛ.1
    have hev : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    simpa [ggTorM] using hev.add_one
  refine E6D4Loc.ggResXDatumE6x_of_wit_of_mem hp2 hodd hM3 ggIsWeylMatrix_E6 ggIntCartan_E₆
    hBs hSC hN w hw z fun hzX => ?_
  have hzcen : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    simpa using Subgroup.mem_centralizer_iff.mp hzc g g.2
  have hzo : orderOf (⟨z, hzX⟩ : ↥X) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hzp)
    · exact fun h => hz1 (congrArg Subtype.val h)
  have hxs := ggTor_central_mem_closure_E6 hodd hM3 w hw hw.2.2.2.2.2.1 _ hzcen hzo
  exact w.coroot_indep_of_center hp hodd hM3 hw ggCartanE₆_ker_le_one _ hzcen hzo hxs

end E6D4Tw

end CFSG.StandardType

end

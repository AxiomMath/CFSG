module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofAut
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofLift
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofExcl
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofSe
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open scoped commutatorElement


open Step1012ClaimProof in
theorem step1012SClaim_of (h48 : Sec4.Item4_8) (hGL : KS1012GL34) (hAut : KS1012AutHyp)
    (hK : Step1012ClaimK) (hON : Step1012ClaimON) : Step1012SClaim := by
  intro h45 h97 h107 h426 h1011 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd w hwA hwS
    hwa hwd hwc hSab e he hec hea heθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have heA : e ∈ A := Sec10XProof.closure_a_c_le h he
  set U := sec10U L a with hUdef
  obtain ⟨⟨-, hU2, hUA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hUmax
  have hU2' : IsPGroup 2 U := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hU2
  obtain ⟨-, hSA⟩ := ((mem_maxInvariantPiSubgroups_iff.mp hS).1.2)
  set X := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
    Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
    Subgroup.centralizer ({d} : Set G) with hX
  have hXO : X ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hXe : X ≤ Subgroup.centralizer ({e} : Set G) := inf_le_left.trans inf_le_right
  have hXd : X ≤ Subgroup.centralizer ({d} : Set G) := inf_le_right
  have hX2 : IsPGroup 2 X := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hXO
  have hXθU : X ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (U : Set G)) :=
    hXO.trans (Subgroup.map_mono ((solvable_prime_complement_core_characterization
      (H := Subgroup.centralizer (U : Set G)) Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two
      (by norm_num)))
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (hXO.trans (SteinbergBY.inSubgroup_pCore_le 2 _)).trans (Subgroup.centralizer_le_normalizer _)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf (SteinbergBY.mem_normalizer_inf
      (SteinbergBY.mem_normalizer_inf
        (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
          (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hUA hx)))
        (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hSA hx)))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx heA))))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx hdA)))
  have hXB : X ≤ Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G) :=
    fun x hx => mem_centralizer_closure_pair_iff.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mp (hXe hx),
        Subgroup.mem_centralizer_singleton_iff.mp (hXd hx)⟩
  set B := Subgroup.closure ({e, d} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact heA
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  refine ⟨B, hBA, Subgroup.subset_closure (by simp),
    Sec10XSteps.card_closure_e_d h97 h hdL he hec, ?_⟩
  have hUθe := le_theta_e h1011 h hdL he hec hXO hXe hea
  have h' := Sec10XProof.sec10Std_of_mem_closure h he hec
  have hUe : sec10U L e = U := Sec10XProof.sec10U_eq_of_mem_closure h he hec
  have hA3 : IsPGroup 3 A := Sec4.isPGroup_of_isElemAbelian h.mem_partTwoF.1
  have hAab : IsMulCommutative A := h.mem_partTwoF.1.1
  obtain ⟨Se, hSesyl, hSeA, hUSe, hXSe⟩ := exists_isSylowOf_theta_normalized hA3 hAab
    (Sec10XProof.le_centralizer_of_mem h heA) hU2' hUθe hUA hX2 hXe hAX hXU
  obtain ⟨we, hweA, hweS, hwee, hwed, hwec⟩ := exists_w_of_isSylowOf h107 h97 h' hdL hSesyl hSeA
  have hSe2 : IsPGroup 2 Se := hSesyl.isPGroup
  have hUmax' : sec10U L e ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) :=
    hUe ▸ hUmax
  have hUSe' : sec10U L e ≤ Se := hUe ▸ hUSe
  have hSec : Se ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L e :=
    Sec10XProof.inf_centralizer_c_eq h' hSe2 hSeA hUSe' hUmax'
  have hSemax := mem_maxInvariantPiSubgroups_of_isSylowOf hSesyl hSeA
  by_cases hSed : Se ⊓ Subgroup.centralizer ({d} : Set G) = ⊥
  ·
    exfalso
    have hSeab := Sec10XSteps.isMulCommutative_of_inf_centralizer_eq_bot h97 h' hdL hSe2 hSeA
      hUSe' hSec hSed hweS hwed hwec
    have hSepow := pow_two_eq_one h97 h' hdL hSe2 hSeab hSeA hSec hSed hweS hwed hwec
    have hXSe' := not_le_centralizer hSesyl hUSe hXθU hXe hXd heθ
    have hauto := automizer_type hGL h' hdL hSeab hSepow hSeA hSec hSed hweS hwee hwed hwec hX2
      hAX hXSe hXB hXSe'
    obtain ⟨K, hKmem, hKtype, hKne, hKZ⟩ := hK h45 h97 G A c L e R h' d hdL (hUe ▸ hUθe) hUmax'
      Se hSemax hUSe' hSec hSed hSeab we hweA hweS hwee hwed hwec X hX2 hAX hXSe hXB
      (hUe ▸ hXθU) hXSe' heθ hauto
    obtain ⟨X', hX', hKX', hX'type⟩ :=
      exists_mem_thetaComponentsAt_of_K h48 h426 h97 h' hdL hKmem hKtype hKne hKZ
    rcases hX'type with hX'4 | hX'6 | hX'64 | ⟨hX'ON, hKA6⟩
    · exact false_of_autHyp h45 h97 h' hdL hX'
        (hAut _ (Sec6.isQuasisimple_of_mem_thetaComponentsAt hX') (Or.inl hX'4))
    · exact false_of_autHyp h45 h97 h' hdL hX'
        (hAut _ (Sec6.isQuasisimple_of_mem_thetaComponentsAt hX') (Or.inr (Or.inl hX'6)))
    · exact false_of_autHyp h45 h97 h' hdL hX'
        (hAut _ (Sec6.isQuasisimple_of_mem_thetaComponentsAt hX') (Or.inr (Or.inr hX'64)))
    · exact hON h45 h97 G A c L e R h' d hdL K hKmem hKA6 hKne hKZ X' hX' hKX' hX'ON
  ·
    have hU1 : sec10U L e ∈ fourGroupsMinus A := (step1010U_holds h45 G A c L e R h').1
    obtain ⟨U', hU', hU'θ⟩ := Sec10XProof.exists_fourGroupsMinus_of_inf_centralizer_ne_bot h97 h'
      hdL hU1 hUmax' hSemax.prop hUSe' hSed
    obtain ⟨⟨-, -, hU'4⟩, hU'eq⟩ := hU'
    have hdvd : Nat.card U' ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer (B : Set G)), A⁆ : Subgroup G) :=
      Subgroup.card_dvd_of_le (hU'eq.le.trans (Subgroup.commutator_mono hU'θ le_rfl))
    rw [hU'4] at hdvd
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans hdvd)

end CFSG.RankThree.PartTwo.Sec10

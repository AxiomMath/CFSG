module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem residualTwoSubgroupTransfer_of (hPSR : ProperSubgroupResidual) :
    ResidualTwoSubgroupTransfer := by
  intro G _ _ hZ hKP he p hp hp3 A hA hAcard c hcA hc1 R hRθ hR2 hAR hRA hBcard hcR
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set B : Subgroup G := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBR : B ≤ Subgroup.centralizer (R : Set G) := inf_le_right
  have hcB : c ∈ B := ⟨hcA, hcR⟩
  have hBel : IsElementaryAbelian p B := SteinbergBM.isElementaryAbelian_of_le hA hBA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
  have hRC : R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) :=
    hRθ.trans (Sec9A.inSubgroup_theta_normalizer_le hp hcp)
  have hRle : ∀ d ∈ B, R ≤ Subgroup.centralizer ({d} : Set G) := fun d hd r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hBR hd) r hr)
  have hpart1 : ∀ b ∈ B, b ≠ 1 →
      R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) := by
    intro b hb hb1
    have hKtop : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
      intro h
      refine hb1 ((Subgroup.eq_bot_iff_forall _).mp hZ b (Subgroup.mem_center_iff.mpr fun g => ?_))
      have hg : g ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [h]
        exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    obtain ⟨a₀, ha₀A, ha₀B⟩ : ∃ a ∈ A, a ∉ B := by
      refine IsConcreteLE.not_le_iff_exists.mp fun hAB => ?_
      have := Subgroup.card_le_of_le hAB
      rw [hAcard, hBcard] at this
      have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
      omega
    have hxc : a₀ ∉ Subgroup.zpowers c := fun h => ha₀B ((Subgroup.zpowers_le.mpr hcB) h)
    set E := Subgroup.zpowers c ⊔ Subgroup.zpowers a₀ with hE
    have hEA : E ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr ha₀A)
    have hEcard : Nat.card E = p ^ 2 :=
      SteinbergBY.card_zpowers_sup_zpowers hp hAcard hcA hc1 ha₀A hxc
    have hEel : IsElementaryAbelian p E := SteinbergBM.isElementaryAbelian_of_le hA hEA
    have hEK : E ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (hEA hx) b (hBA hb))
    have hcE : c ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    have hAE : B ⊔ E = A := Sec9A.sup_eq_of_card hp hBA hEA hAcard hBcard fun h =>
      ha₀B (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers a₀)))
    have hRE : ⁅R, E⁆ = R := by
      rw [← Sec9A.commutator_sup_eq_of_le_centralizer (B := B) (hAE ▸ hAR) hBR, hAE, hRA]
    have hRθK : R ≤ inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) :=
      (le_inf (le_inf (hRle b hb) (hRC.trans (Subgroup.map_subtype_le _))) hRC).trans
        (Sec9A.inf_inSubgroup_theta_le hp inf_le_right)
    have hRW : R ≤ residualGroup p (Subgroup.centralizer ({b} : Set G)) E c := by
      calc R = ⁅R, E⁆ := hRE.symm
        _ ≤ ⁅inSubgroup (aschbacherSolvableCore p)
            (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)), E⁆ :=
          Subgroup.commutator_mono hRθK le_rfl
        _ ≤ residualGroup p (Subgroup.centralizer ({b} : Set G)) E c := le_sup_left
    exact (Sec9A.le_twoPrimeResidual hR2 hRW).trans
      (hPSR G hKP he p hp hp3 E hEel hEcard _ hEK hKtop c hcE hc1)
  refine ⟨hpart1, fun M hBM hMtop => ?_⟩
  have hI : R ⊓ M ≤ ⨅ d ∈ B, ⨅ (_ : d ≠ 1),
      inSubgroup (aschbacherSolvableCore p) (M ⊓ Subgroup.centralizer ({d} : Set G)) := by
    simp only [le_iInf_iff]
    intro d hd hd1
    exact (le_inf (le_inf inf_le_right (inf_le_left.trans (hRle d hd)))
      (inf_le_left.trans (hpart1 d hd hd1))).trans (Sec9A.inf_inSubgroup_theta_le hp inf_le_right)
  have hW : R ⊓ M ≤ residualGroup p M B c := hI.trans le_sup_right
  exact (Sec9A.le_twoPrimeResidual (hR2.to_le inf_le_left) hW).trans
    (hPSR G hKP he p hp hp3 B hBel hBcard M hBM hMtop c hcB hc1)

end CFSG.RankThree.PartOne

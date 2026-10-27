module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBNatOm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bc_case168_5 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (h5 : Case168_5 D ⊥ V hV L) : Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hLM : L ≤ D.M := hc.setting.hyp151.le
  obtain ⟨⟨e⟩, hΩ, hnat, hσ⟩ := h5
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 3
  have hQ : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥ := s16c1610_center_of_isOmegaPlus_four_two hΩ
  have hP : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤ :=
    s16c1610_commutator_of_isOmegaPlus_four_two hΩ
  obtain ⟨Z, -, hZM, hZcard, hZnorm, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 3) hQ e
  obtain ⟨n, hn1, hnfix⟩ := s16c13bc_exists_fixed D h
  obtain ⟨ψ, hψL, hψo, hψn⟩ := s16n9b_natOmegaPlus_fix hnat hn1
  have hψ1 : ψ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψZ : ψ ∉ Z := s16c13bc_not_mem_of_perfect Nat.prime_three hP hQ hZcard
    (fun m hm x hx => hZnorm m (barSub_mono ⊥ V hV hLM hm) x hx) hψL hψ1
  exact s16c13bc_insp_of_normal_prime D h hcomm hp3 hZM hZcard hZnorm hn1 hnfix
    (barSub_mono ⊥ V hV hLM hψL) hψo hψZ hψn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

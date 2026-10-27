module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23_commute_of_commutator_mem_bot {a b : G}
    (h : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G)) : a * b = b * a := by
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [h]

theorem c23_commutator_mem_of_mem_preBarSub_barSub {M V₀ V L' : Subgroup G}
    (hV : IsElemAbelian 2 V) {g u : G}
    (hg : g ∈ preBarSub M V₀ V hV (barSub V₀ V hV L')) (hu : u ∈ V)
    (hu' : u ∈ centralizer (L' : Set G)) : g * u * g⁻¹ * u⁻¹ ∈ V₀ := by
  obtain ⟨-, hgs, hxbar⟩ := (mem_preBarSub M V₀ V hV (barSub V₀ V hV L')).1 hg
  obtain ⟨l, hl, hl_eq⟩ := (mem_barSub V₀ V hV L' _).1 hxbar
  have key := congrArg
    (fun φ : MulAut (Vtil V₀ V hV) =>
      φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, hu⟩))) hl_eq
  rw [actTil_mk, actTil_mk, mkTil_eq_iff, actStab_apply_val, actStab_apply_val] at key
  change (l : G) * u * (l : G)⁻¹ * ((g : G) * u * (g : G)⁻¹)⁻¹ ∈ V₀ at key
  have hlu : (l : G) * u = u * (l : G) :=
    (Subgroup.mem_centralizer_iff.1 hu') (l : G) hl
  have hconj : (l : G) * u * (l : G)⁻¹ = u := by rw [hlu]; group
  rw [hconj] at key
  simpa [mul_inv_rev, inv_inv] using V₀.inv_mem key

theorem c23_preBarSub_conj_le_cElt (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {x : G} (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) {w : G}
    (hw : w ∈ wSub V₀ V hV L) :
    preBarSub D.M V₀ V hV (barSub V₀ V hV (conjSubgroup L x)) ≤ F11.CElt D.M V₀ w := by
  intro g hg
  obtain ⟨hgM, hgs, hxbar⟩ :=
    (mem_preBarSub D.M V₀ V hV (barSub V₀ V hV (conjSubgroup L x))).1 hg
  unfold wSub at hw
  obtain ⟨y, hyval, hyW⟩ := (mem_preTil V₀ V hV (wTil V₀ V hV L)).1 hw
  have hcomm := (h.commute x hx hxn).2
  have hfixV : wTil V₀ V hV L ≤ fixV (barSub V₀ V hV (conjSubgroup L x)) :=
    commSub_eq_bot_iff.mp hcomm
  have hfix := (mem_fixV.mp (hfixV hyW)) (actTil V₀ V hV ⟨g, hgs⟩) hxbar
  refine ⟨hgM, stabTil_le_normalizer₀ V₀ V hgs, ?_⟩
  have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨g, hgs⟩ y) = mkTil V₀ V hV y := by
    rw [← actTil_mk]
    exact hfix
  rw [mkTil_eq_iff, actStab_apply_val, hyval] at h1
  exact h1

theorem c23_preBarSub_conj_le_centralizer (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L)
    (hcases : ∀ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
      barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV (conjSubgroup L x))
    {w : G} (hw : w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :
    preBarSub D.M V₀ V hV (barSub V₀ V hV (conjSubgroup L x)) ≤ centralizer ({w} : Set G) := by
  have hclaim : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
      centralizer (preBarSub D.M V₀ V hV
        (barSub V₀ V hV (conjSubgroup L x)) : Set G) := by
    refine sup_le ?_ ?_
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨-, -, hc⟩ := c23_preBarSub_conj_le_cElt D h hV hx hxn hu hg
      exact c23_commute_of_commutator_mem_bot (h0 ▸ hc)
    · rw [s15_Infra_v1Sub_eq_iSup h.hyp125 hV h0]
      refine iSup_le fun m => ?_
      intro u hu
      rw [Subgroup.mem_inf] at hu
      obtain ⟨huW, huC⟩ := hu
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rcases hcases (m : G) m.2 with hcase | hcase
      · have hwsub : wSub V₀ V hV (conjSubgroup L (m : G)) = wSub V₀ V hV L := by
          unfold wSub wTil
          rw [hcase]
        rw [hwsub] at huW
        obtain ⟨-, -, hc⟩ := c23_preBarSub_conj_le_cElt D h hV hx hxn huW hg
        exact c23_commute_of_commutator_mem_bot (h0 ▸ hc)
      · rw [← hcase] at hg
        have huV : u ∈ V :=
          preTil_le V₀ V hV (wTil V₀ V hV (conjSubgroup L (m : G))) huW
        have hc := c23_commutator_mem_of_mem_preBarSub_barSub
          (M := D.M) (V₀ := V₀) (V := V) (L' := conjSubgroup L (m : G)) hV hg huV huC
        exact c23_commute_of_commutator_mem_bot (h0 ▸ hc)
  intro g hg
  have hwC : w ∈ centralizer (preBarSub D.M V₀ V hV
      (barSub V₀ V hV (conjSubgroup L x)) : Set G) := hclaim hw
  rw [Subgroup.mem_centralizer_iff] at hwC ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact (hwC g hg).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

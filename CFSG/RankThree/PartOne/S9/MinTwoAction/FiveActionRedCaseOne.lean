module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedAbstract
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedRealize
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingStructure

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36
  CFSG.RankThree.PartOne.Lifting36
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]

theorem false_of_trivial_atom (hFV : FiveAction.FixedVector) (hq2 : q ≠ 2)
    {A D R : Subgroup G} [hDq : Fact (IsPGroup q ↥D)] (hset : MinTwoActionSetting 5 q A D R)
    (hrk : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)
    (U : Subrepresentation (FRep q hset.D_inv))
    (hdim : 4 ≤ Module.finrank (ZMod q) U.toSubmodule)
    (hRU : ∀ r : ↥(R ⊔ A), (r : G) ∈ R → ∀ u ∈ U, FRep q hset.D_inv r u = u) : False := by
  classical
  have hLD := hset.D_inv
  obtain ⟨X, hXD, hXfr, hd⟩ := exists_sfdata hset hrk
  have hXq : IsPGroup q ↥X := isPGroup_of_le hXD hDq.out
  have : Fact (IsPGroup q ↥X) := ⟨hXq⟩
  have hLX := hd.irr.1
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_left hLX
  obtain ⟨r, hrC, x, hx1, hxfix⟩ :=
    exists_fixed_vector hFV hq2 hset.R_two hset.A_card hset.R_inv hd
  have hr1 : (r : G) ≠ 1 := by
    intro h
    apply hrC
    rw [h]
    exact Subgroup.one_mem _
  let rL : ↥(R ⊔ A) := Subgroup.inclusion (le_sup_left : R ≤ R ⊔ A) r
  let xD : ↥D := ⟨x, hXD x.2⟩
  let w : Additive (↥D ⧸ frattini ↥D) := Additive.ofMul (xD : ↥D ⧸ frattini ↥D)
  have hw0 : w ≠ 0 := by
    intro h
    apply hx1
    exact (mk_eq_one_iff hXD hXfr x).mpr (Additive.ofMul.injective h)
  have hrw : FRep q hLD rL w = w := by
    have h1 := FRep_apply_mk q hLD rL xD
    have h2 := (mk_eq_iff hXD hXfr (conjHom hRX r x) x).mp hxfix
    change FRep q hLD rL (Additive.ofMul (xD : ↥D ⧸ frattini ↥D)) = _
    rw [h1]
    exact congrArg Additive.ofMul h2
  have hwU : w ∉ U := by
    intro hwU
    let T : Subgroup (↥D ⧸ frattini ↥D) := toSubgroup q U.toSubmodule
    have hT : ∀ h : ↥(R ⊔ A), ∀ y : ↥D, (y : ↥D ⧸ frattini ↥D) ∈ T →
        ((conjHom hLD h y : ↥D) : ↥D ⧸ frattini ↥D) ∈ T := by
      intro h y hy
      have h1 := U.apply_mem_toSubmodule h (show Additive.ofMul (y : ↥D ⧸ frattini ↥D) ∈ U from hy)
      rw [FRep_apply_mk] at h1
      exact h1
    let Y : Subgroup G := X ⊓ liftSub D T
    have hΦY : inSubgroup frattini X ≤ Y := by
      refine le_inf (Subgroup.map_subtype_le _) ?_
      rw [← hXfr]
      exact inf_le_right.trans (frattini_le_liftSub T)
    have hLY : R ⊔ A ≤ Subgroup.normalizer (Y : Set G) := by
      have hLT := le_normalizer_liftSub hLD T hT
      refine le_normalizer_of_conj_mem fun c hc g hg => ?_
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hLX hc) g).mp hg.1,
        (Subgroup.mem_normalizer_iff.mp (hLT hc) g).mp hg.2⟩
    rcases hd.irr.2.2 Y hΦY inf_le_left hLY with hY | hY
    · apply hx1
      have hxY : (x : G) ∈ Y := ⟨x.2, mem_liftSub.mpr ⟨hXD x.2, hwU⟩⟩
      rw [hY] at hxY
      exact (QuotientGroup.eq_one_iff x).mpr ((mem_inSubgroup_frattini_iff x).mp hxY)
    · apply hrC
      have hall : ∀ y : ↥X, Additive.ofMul ((⟨y, hXD y.2⟩ : ↥D) : ↥D ⧸ frattini ↥D) ∈ U := by
        intro y
        have : (y : G) ∈ Y := by rw [hY]; exact y.2
        exact (mem_liftSub.mp this.2).2
      have htriv : ∀ y : ↥X, ((conjHom hRX r y : ↥X) : ↥X ⧸ frattini ↥X) =
          (y : ↥X ⧸ frattini ↥X) := by
        intro y
        refine (mk_eq_iff hXD hXfr (conjHom hRX r y) y).mpr ?_
        have h1 := hRU rL r.2 _ (hall y)
        rw [FRep_apply_mk] at h1
        exact Additive.ofMul.injective h1
      let _ := conjAction hRX
      have hfix := smul_eq_of_smul_mk_eq hXq r
        (not_dvd_orderOf_of_two_group (Fact.out) hq2 hset.R_two r) htriv
      exact (mem_ker_conjHom hRX r).mp (MulEquiv.ext hfix)
  have hUE : U.toSubmodule ≤ Module.End.eigenspace (FRep q hLD rL) 1 := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hRU rL r.2 u hu
  have hwE : Submodule.span (ZMod q) {w} ≤ Module.End.eigenspace (FRep q hLD rL) 1 := by
    rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff, one_smul]
    exact hrw
  have hdisj : U.toSubmodule ⊓ Submodule.span (ZMod q) {w} = ⊥ := by
    have := (Submodule.disjoint_span_singleton' hw0).mpr hwU
    exact this.eq_bot
  have h5 := finrank_add_le hUE hwE hdisj
  rw [finrank_span_singleton hw0] at h5
  have h4 := finrank_eigenspace_le_four hq2 hLD hset.D_exp hset.D_class rL
    (isPGroup_zpowers_two hset.R_two le_sup_left r) (hrk r r.2 hr1)
  omega

end CFSG.RankThree.PartOne.FiveAction.Red

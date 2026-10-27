module

public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourSwaps
import CFSG.OddTranspositions.PartThree.EightEight.Kernel
import CFSG.OddTranspositions.PartThree.HalphaConj
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.OddTranspositions.PartFour.Line

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem mem_Dalpha_of_mk_eq_w4p (hC : HypothesisC D) {γ β β' : Set G}
    (hγ : IsBlock D γ) (hBγ : BlocksInCosets D γ) (hAγ : FibresAnticlique D γ)
    (hβ : β ∈ Dalpha D γ) (hβ' : β' ∈ Dalpha D γ) {b b' : Halpha D γ}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b')
    (hαγ : hC.alpha ∈ Dalpha D γ) (hαβ : hC.alpha ∈ Dalpha D β) :
    hC.alpha ∈ Dalpha D β' := by
  let a : Halpha D γ := ⟨hC.d, Subgroup.subset_closure (subset_DalphaStar hαγ hC.d_mem_alpha)⟩
  have ha : (a : G) ∈ hC.alpha := hC.d_mem_alpha
  have h := (hBγ.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hγ hAγ hβ hαγ hb ha).mp hαβ
  exact (hBγ.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hγ hAγ hβ' hαγ hb' ha).mpr
    (hbb' ▸ h)

private theorem commute_and_ne_of_common_w4p (hC : HypothesisC D) {γ β β' : Set G}
    (hγ : IsBlock D γ) (hBγ : BlocksInCosets D γ) (hAγ : FibresAnticlique D γ)
    (hβ : β ∈ Dalpha D γ) (hβ' : β' ∈ Dalpha D γ) {b b' : Halpha D γ}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b')
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha)
    (hγDα : γ ∈ Dalpha D hC.alpha) (hβDα : β ∈ Dalpha D hC.alpha)
    (hβ'Dα : β' ∈ Dalpha D hC.alpha) {x : Halpha D hC.alpha} (hx : (x : G) ∈ β)
    {g : Halpha D hC.alpha} (hg : (g : G) ∈ γ)
    {q : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hq : q ∈ imageClass hC)
    (hqg : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g) q)
    (hqx : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) q)
    (hqneg : q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g)
    (hqnex : q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)
    {x' : Halpha D hC.alpha} (hx' : (x' : G) ∈ β') :
    Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x') q ∧
      q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x' := by
  obtain ⟨ρ, hρDα, p, hpρ, rfl⟩ := exists_mem_Dalpha_mk_eq hC hq
  have hρDγ : ρ ∈ Dalpha D γ :=
    (hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA hγDα hρDα
      hg hpρ).mpr ⟨hqneg.symm, hqg⟩
  have hρDβ : ρ ∈ Dalpha D β :=
    (hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA hβDα hρDα
      hx hpρ).mpr ⟨hqnex.symm, hqx⟩
  let pγ : Halpha D γ := ⟨(p : G), Subgroup.subset_closure (subset_DalphaStar hρDγ hpρ)⟩
  have hpγ : (pγ : G) ∈ ρ := hpρ
  have h1 := hBγ.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hγ hAγ hβ hρDγ hb hpγ
  have h2 := hBγ.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hγ hAγ hβ' hρDγ hb' hpγ
  have hρDβ' : ρ ∈ Dalpha D β' := h2.mpr (hbb' ▸ h1.mp hρDβ)
  have h3 := hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA
    hβ'Dα hρDα hx' hpρ
  obtain ⟨hne, hcomm⟩ := h3.mp hρDβ'
  exact ⟨hcomm, hne.symm⟩

private theorem setOf_commute_eq_w4p (hC : HypothesisC D) {γ β β' : Set G}
    (hγ : IsBlock D γ) (hBγ : BlocksInCosets D γ) (hAγ : FibresAnticlique D γ)
    (hβ : β ∈ Dalpha D γ) (hβ' : β' ∈ Dalpha D γ) {b b' : Halpha D γ}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b')
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha)
    (hγDα : γ ∈ Dalpha D hC.alpha) (hβDα : β ∈ Dalpha D hC.alpha)
    (hβ'Dα : β' ∈ Dalpha D hC.alpha) {x x' : Halpha D hC.alpha}
    (hx : (x : G) ∈ β) (hx' : (x' : G) ∈ β') {g : Halpha D hC.alpha} (hg : (g : G) ∈ γ) :
    {q | q ∈ imageClass hC ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g) q ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) q ∧
        q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g ∧
        q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x} =
      {q | q ∈ imageClass hC ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g) q ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x') q ∧
        q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) g ∧
        q ≠ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x'} := by
  ext q
  constructor
  · rintro ⟨hq, hqg, hqx, hqneg, hqnex⟩
    obtain ⟨hxq, hqnex'⟩ := commute_and_ne_of_common_w4p hC hγ hBγ hAγ hβ hβ' hb hb' hbb'
      hB hA hγDα hβDα hβ'Dα hx hg hq hqg hqx hqneg hqnex hx'
    exact ⟨hq, hqg, hxq, hqneg, hqnex'⟩
  · rintro ⟨hq, hqg, hqx', hqneg, hqnex'⟩
    obtain ⟨hxq, hqxne⟩ := commute_and_ne_of_common_w4p hC hγ hBγ hAγ hβ' hβ hb' hb hbb'.symm
      hB hA hγDα hβ'Dα hβDα hx' hg hq hqg hqx' hqneg hqnex' hx
    exact ⟨hq, hqg, hxq, hqneg, hqxne⟩

private theorem mk_eq_of_mk_eq_w4p (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f)
    (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {γ β β' : Set G}
    (hγ : IsBlock D γ) (hBγ : BlocksInCosets D γ) (hAγ : FibresAnticlique D γ)
    (hβ : β ∈ Dalpha D γ) (hβ' : β' ∈ Dalpha D γ) {b b' : Halpha D γ}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b')
    (hαγ : hC.alpha ∈ Dalpha D γ) (hαβ : hC.alpha ∈ Dalpha D β)
    (hαβ' : hC.alpha ∈ Dalpha D β') :
    ∀ c c' : Halpha D hC.alpha, (c : G) ∈ β → (c' : G) ∈ β' →
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c' := by
  intro c c' hc hc'
  have hβDα : β ∈ Dalpha D hC.alpha := mem_Dalpha_symm hαβ hβ.2.1
  have hβ'Dα : β' ∈ Dalpha D hC.alpha := mem_Dalpha_symm hαβ' hβ'.2.1
  have hγDα : γ ∈ Dalpha D hC.alpha := mem_Dalpha_symm hαγ hγ.subset
  obtain ⟨x, hx⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβDα.1
  obtain ⟨x', hx'⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ'Dα.1
  obtain ⟨g₀, hg₀⟩ := hγ.nonempty
  let gbar : Halpha D hC.alpha := ⟨g₀, Subgroup.subset_closure (subset_DalphaStar hγDα hg₀)⟩
  let xbar : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure (subset_DalphaStar hβDα hx)⟩
  let xbar' : Halpha D hC.alpha := ⟨x', Subgroup.subset_closure (subset_DalphaStar hβ'Dα hx')⟩
  have hcx : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) gbar)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar) :=
    ((hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA hγDα hβDα
      (a := gbar) (b := xbar) hg₀ hx).mp hβ).2
  have hcx' : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) gbar)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar') :=
    ((hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA hγDα hβ'Dα
      (a := gbar) (b := xbar') hg₀ hx').mp hβ').2
  have hset := setOf_commute_eq_w4p hC hγ hBγ hAγ hβ hβ' hb hb' hbb' hB hA hγDα hβDα hβ'Dα
    (x := xbar) (x' := xbar') hx hx' (g := gbar) hg₀
  have hxx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar' :=
    eq_of_setOf_commute_eq_of_mulEquiv (setup_quotient hC hns) hf hk φ
      ⟨gbar, (mem_DstarH_iff hC).mpr (subset_DalphaStar hγDα hg₀), rfl⟩
      ⟨xbar, (mem_DstarH_iff hC).mpr (subset_DalphaStar hβDα hx), rfl⟩
      ⟨xbar', (mem_DstarH_iff hC).mpr (subset_DalphaStar hβ'Dα hx'), rfl⟩
      hcx hcx' hset
  calc QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar :=
          (hB β hβDα xbar c hx hc).symm
    _ = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xbar' := by rw [hxx]
    _ = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c' :=
          hB β' hβ'Dα xbar' c' hx' hc'

theorem mem_Dalpha_and_mk_eq_of_mk_eq (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {γ : Set G}
    (hγ : IsBlock D γ) (hBγ : BlocksInCosets D γ) (hAγ : FibresAnticlique D γ)
    {β β' : Set G} (hβ : β ∈ Dalpha D γ) (hβ' : β' ∈ Dalpha D γ) {b b' : Halpha D γ}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) b')
    (hαγ : hC.alpha ∈ Dalpha D γ) (hαβ : hC.alpha ∈ Dalpha D β) :
    hC.alpha ∈ Dalpha D β' ∧ ∀ c c' : Halpha D hC.alpha, (c : G) ∈ β → (c' : G) ∈ β' →
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c' :=
  ⟨mem_Dalpha_of_mk_eq_w4p hC hγ hBγ hAγ hβ hβ' hb hb' hbb' hαγ hαβ,
    mk_eq_of_mk_eq_w4p hC hns hf hk φ hB hA hγ hBγ hAγ hβ hβ' hb hb' hbb' hαγ hαβ
      (mem_Dalpha_of_mk_eq_w4p hC hγ hBγ hAγ hβ hβ' hb hb' hbb' hαγ hαβ)⟩

private theorem propagation_aux_w4p (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {β β' : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hβ' : β' ∈ Dalpha D hC.alpha) {b b' : Halpha D hC.alpha}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b')
    {γ : Set G} (hγ : Relation.ReflTransGen (DalphaAdj D β) hC.alpha γ) :
    γ ∈ Dalpha D β' ∧ β ∈ Dalpha D γ ∧
      ∀ c c' : Halpha D γ, (c : G) ∈ β → (c' : G) ∈ β' →
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) c =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) c' := by
  induction hγ with
  | refl =>
    refine ⟨mem_Dalpha_symm hβ' hC.isBlock_alpha.subset, hβ, ?_⟩
    intro c c' hc hc'
    calc QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b :=
            (hB β hβ b c hb hc).symm
      _ = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b' := hbb'
      _ = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c' :=
            hB β' hβ' b' c' hb' hc'
  | @tail γ γ' _ hstep ih =>
    obtain ⟨hγ'Dβ, hγ'Dγ⟩ := hstep
    have hγ'cls : γ' ∈ blockClass hC.alpha := mem_blockClass_trans hβ.1 hγ'Dβ.1
    have hγcls : γ ∈ blockClass hC.alpha := by
      rw [← blockClass_eq_of_mem_blockClass hβ.1]
      exact mem_blockClass_comm.mpr ih.2.1.1
    have hγblock : IsBlock D γ := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγcls
    have hBγ : BlocksInCosets D γ := hB.of_mem_blockClass hC.setup.normal hγcls
    have hAγ : FibresAnticlique D γ := hA.of_mem_blockClass hC.setup.normal hγcls
    obtain ⟨r, hr⟩ := (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ'cls).nonempty
    obtain ⟨g, hgα, -⟩ := exists_conj_alpha_eq_and_d_eq hC hγ'cls hr
    let bγ : Halpha D γ := ⟨(b : G), Subgroup.subset_closure (subset_DalphaStar ih.2.1 hb)⟩
    have hβ'Dγ : β' ∈ Dalpha D γ := mem_Dalpha_symm ih.1 hβ'.2.1
    let bγ' : Halpha D γ := ⟨(b' : G), Subgroup.subset_closure (subset_DalphaStar hβ'Dγ hb')⟩
    have hbb'γ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) bγ =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) bγ' :=
      ih.2.2 bγ bγ' hb hb'
    subst γ'
    have h104 := mem_Dalpha_and_mk_eq_of_mk_eq (hC := hC.conj g)
      (not_isSolvable_Halpha_conj hC g hns) hf hk
      ((QuotientGroup.congr _ _ (conjEquiv hC g) (conjRadical_map hC g)).symm.trans φ)
      (BlocksInCosets.of_mem_blockClass hC.setup.normal hB hγ'cls)
      (FibresAnticlique.of_mem_blockClass hC.setup.normal hA hγ'cls)
      hγblock hBγ hAγ ih.2.1 hβ'Dγ (b := bγ) (b' := bγ') hb hb' hbb'γ
      hγ'Dγ hγ'Dβ
    exact ⟨h104.1, mem_Dalpha_symm hγ'Dβ hβ.2.1, h104.2⟩

theorem mem_Dalpha_and_mk_eq_of_reflTransGen (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {β β' : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hβ' : β' ∈ Dalpha D hC.alpha) {b b' : Halpha D hC.alpha}
    (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b')
    {γ : Set G} (hγ : Relation.ReflTransGen (DalphaAdj D β) hC.alpha γ) :
    γ ∈ Dalpha D β' ∧ ∀ c c' : Halpha D γ, (c : G) ∈ β → (c' : G) ∈ β' →
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) c =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D γ)) c' := by
  have h := propagation_aux_w4p hC hns hf hk φ hB hA hβ hβ' hb hb' hbb' hγ
  exact ⟨h.1, h.2.2⟩

end CFSG.OddTranspositions.PartThree.EightEight

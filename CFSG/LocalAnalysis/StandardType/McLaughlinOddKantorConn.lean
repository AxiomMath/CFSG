module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorSplit
public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorSection

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p : ℕ} [Fact p.Prime]

theorem det_neg_equiv {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] :
    LinearMap.det ((LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
      (-1) ^ Module.finrank (ZMod p) V := by
  have : ((LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
      (-1 : ZMod p) • LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem two_le_finrank_of_isTransvectionWith {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {t : V ≃ₗ[ZMod p] V} {v : V} {f : Module.Dual (ZMod p) V}
    (h : IsTransvectionWith t v f) : 2 ≤ Module.finrank (ZMod p) V := by
  by_contra hlt
  push Not at hlt
  have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v}) = 1 := finrank_span_singleton h.1
  have h2 : Submodule.span (ZMod p) {v} = ⊤ := Submodule.eq_top_of_finrank_eq (by
    have := Submodule.finrank_le (Submodule.span (ZMod p) {v})
    omega)
  apply h.2.1
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span (ZMod p) {v} := h2 ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, h.2.2.1, smul_zero, LinearMap.zero_apply]

theorem fixSub_eq_bot_of_isConnTr (hp : p ≠ 2) {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (D : Set (V ≃ₗ[ZMod p] V))
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) (hconn : IsConnTr D)
    (hT : NoNormalExpP (Subgroup.closure D)) (hU : cenSpan D = ⊤) :
    fixSub (Subgroup.closure D) = ⊥ := by
  induction hn : Module.finrank (ZMod p) V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_contra hne
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hX : Submodule.span (ZMod p) {r} ≤ fixSub (Subgroup.closure D) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hr)
  have hXinv : ∀ g ∈ Subgroup.closure D, ∀ x ∈ Submodule.span (ZMod p) {r}, g x ∈
      Submodule.span (ZMod p) {r} := fun g hg x hx => by rw [hX hx g hg]; exact hx
  have hS : SplitHyp (Subgroup.closure D) D r :=
    ⟨Subgroup.subset_closure, hD, hU, hr0, fun g hg => hr g hg,
      fun g hg hmov => eq_one_of_unip hT hXinv hg hmov fun x hx => hX hx g hg⟩
  have hφ := quoHom_injective hT hX
  have hD' : ∀ t' ∈ imgSet (Subgroup.closure D) (quoHom (Subgroup.closure D) _ hX) D,
      ∃ c ψ, IsTransvectionWith t' c ψ := by
    rintro _ ⟨⟨t, htT⟩, ht, rfl⟩
    obtain ⟨v, f, h⟩ := hD t ht
    obtain ⟨hvX, hfr⟩ := hS.center_notMem ht h
    exact ⟨_, _, isTransvectionWith_quoHom hX (g := ⟨t, htT⟩) h hvX
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hfr))⟩
  have hrange := range_eq_closure_imgSet D (quoHom (Subgroup.closure D) _ hX)
  have hT' := hrange ▸ noNormalExpP_range hT _ hφ
  have hconn' := isConnTr_imgSet hconn _ hφ
  have hU' : cenSpan (imgSet (Subgroup.closure D) (quoHom (Subgroup.closure D) _ hX) D) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      have hx : x ∈ cenSpan D := hU ▸ Submodule.mem_top
      have hmx : Submodule.Quotient.mk x ∈ (cenSpan D).map (Submodule.span (ZMod p) {r}).mkQ :=
        Submodule.mem_map_of_mem hx
      rw [cenSpan, Submodule.map_span] at hmx
      refine Submodule.span_mono ?_ hmx
      rintro _ ⟨v, ⟨t, ht, f, h⟩, rfl⟩
      obtain ⟨hvX, hfr⟩ := hS.center_notMem ht h
      exact ⟨_, mem_imgSet _ (t := ⟨t, Subgroup.subset_closure ht⟩) ht, _,
        isTransvectionWith_quoHom hX h hvX
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hfr))⟩
  have hdim : Module.finrank (ZMod p) (V ⧸ Submodule.span (ZMod p) {r}) < n := by
    have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span (ZMod p) {r})
    have h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {r}) = 1 :=
      finrank_span_singleton hr0
    omega
  have hC' := ih _ hdim _ hD' hconn' hT' hU' rfl
  have hirr := irreducible_of_isConnTr hD' hconn' hT' hU' hC'
  have hneg : LinearEquiv.neg (ZMod p) ∈ Subgroup.closure
      (imgSet (Subgroup.closure D) (quoHom (Subgroup.closure D) _ hX) D) → False := by
    intro hm
    rw [← hrange] at hm
    obtain ⟨z, hz⟩ := hm
    refine hS.false_of_neg hp z.2 fun x => ?_
    have h1 := LinearEquiv.congr_fun hz (Submodule.Quotient.mk x)
    change Submodule.Quotient.mk ((z : V ≃ₗ[ZMod p] V) x) = -Submodule.Quotient.mk x at h1
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_add, h1, neg_add_cancel]
  rcases mcLaughlin_odd hp _ hirr ⟨_, hD', rfl⟩ with hSL | ⟨B, -, -, hSp⟩
  · by_cases heven : Even (Module.finrank (ZMod p) (V ⧸ Submodule.span (ZMod p) {r}))
    · exact hneg ((hSL _).mpr (by rw [det_neg_equiv, heven.neg_one_pow]))
    · obtain ⟨t₀, ht₀, v₀, f₀, h₀⟩ := hS.exists_mem
      obtain ⟨c, ψ, hcψ⟩ := hD' _ (mem_imgSet (quoHom (Subgroup.closure D) _ hX)
        (t := ⟨t₀, Subgroup.subset_closure ht₀⟩) ht₀)
      have h2 := two_le_finrank_of_isTransvectionWith hcψ
      have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span (ZMod p) {r})
      have h3 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {r}) = 1 :=
        finrank_span_singleton hr0
      have hodd := Nat.not_even_iff_odd.mp heven
      have h4 : 4 ≤ Module.finrank (ZMod p) V := by
        obtain ⟨k, hk⟩ := hodd
        omega
      refine hS.false_of_lift h4 fun u g hgr hgu => ?_
      have hfX : Submodule.span (ZMod p) {r} ≤ LinearMap.ker g :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hgr)
      have hgu' : (Submodule.span (ZMod p) {r}).liftQ g hfX (Submodule.Quotient.mk u) = 0 := by
        rw [Submodule.liftQ_apply, hgu]
      have hmem := (hSL (LinearEquiv.transvection hgu')).mpr (by
        rw [← LinearEquiv.coe_det, LinearEquiv.transvection.det_eq_one]
        rfl)
      rw [← hrange] at hmem
      obtain ⟨τ, hτ⟩ := hmem
      refine ⟨τ, τ.2, fun x => ?_⟩
      have h5 := LinearEquiv.congr_fun hτ (Submodule.Quotient.mk x)
      rw [LinearEquiv.transvection.apply, Submodule.liftQ_apply] at h5
      change Submodule.Quotient.mk ((τ : V ≃ₗ[ZMod p] V) x) = _ at h5
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_smul, h5, add_sub_cancel_left, sub_self]
  · exact hneg ((hSp _).mpr fun x y => by simp)

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]

theorem cenSpan_inf_fixSub_eq_bot (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (D : Set (V ≃ₗ[ZMod p] V)) (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hconn : IsConnTr D) (hT : NoNormalExpP (Subgroup.closure D)) :
    cenSpan D ⊓ fixSub (Subgroup.closure D) = ⊥ := by
  have hφ := resCen_injective hD hT
  have hrange := range_eq_closure_imgSet D (resCen D hD)
  have hC := fixSub_eq_bot_of_isConnTr hp _ (isTransvection_imgSet_resCen hD hT)
    (isConnTr_imgSet hconn _ hφ) (hrange ▸ noNormalExpP_range hT _ hφ) (cenSpan_imgSet_resCen hD hT)
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hmem : (⟨x, hx1⟩ : cenSpan D) ∈ fixSub (resCen D hD).range :=
    (mem_fixSub_range_resHom (T := Subgroup.closure D) (W := cenSpan D) _).mpr hx2
  rw [hrange, hC, Submodule.mem_bot] at hmem
  exact (Submodule.mem_bot _).mpr (congrArg Subtype.val hmem)

@[expose] def axSet (D : Set (V ≃ₗ[ZMod p] V)) : Set (Module.Dual (ZMod p) V) :=
  {f | ∃ t ∈ D, ∃ v, IsTransvectionWith t v f}

theorem fixSub_eq_dualCoannihilator {D : Set (V ≃ₗ[ZMod p] V)}
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) :
    fixSub (Subgroup.closure D) = (Submodule.span (ZMod p) (axSet D)).dualCoannihilator := by
  ext x
  rw [mem_fixSub_closure hD, Submodule.mem_dualCoannihilator]
  constructor
  · intro hx φ hφ
    refine Submodule.span_induction (p := fun φ _ => φ x = 0) ?_ (by simp)
      (fun a b _ _ ha hb => by rw [LinearMap.add_apply, ha, hb, add_zero])
      (fun c a _ ha => by rw [LinearMap.smul_apply, ha, smul_zero]) hφ
    rintro φ ⟨t, ht, v, h⟩
    exact hx t ht v φ h
  · intro hx t ht v f h
    exact hx f (Submodule.subset_span ⟨t, ht, v, h⟩)

theorem cenSpan_sup_fixSub_eq_top (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (D : Set (V ≃ₗ[ZMod p] V)) (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hconn : IsConnTr D) (hT : NoNormalExpP (Subgroup.closure D)) :
    cenSpan D ⊔ fixSub (Subgroup.closure D) = ⊤ := by
  have hφ : Function.Injective
      ((dualHom (p := p) (V := V)).comp (Subgroup.closure D).subtype) :=
    dualHom_injective.comp Subtype.val_injective
  have hrange := range_eq_closure_imgSet D ((dualHom (p := p) (V := V)).comp
    (Subgroup.closure D).subtype)
  have hDs : ∀ t' ∈ imgSet (Subgroup.closure D) ((dualHom (p := p) (V := V)).comp
      (Subgroup.closure D).subtype) D, ∃ c ψ, IsTransvectionWith t' c ψ := by
    rintro _ ⟨⟨t, htT⟩, ht, rfl⟩
    obtain ⟨v, f, h⟩ := hD t ht
    exact ⟨_, _, isTransvectionWith_dualHom h⟩
  have hbot := cenSpan_inf_fixSub_eq_bot hp _ hDs (isConnTr_imgSet hconn _ hφ)
    (hrange ▸ noNormalExpP_range hT _ hφ)
  have h1 : Submodule.span (ZMod p) (axSet D) ≤ cenSpan (imgSet (Subgroup.closure D)
      ((dualHom (p := p) (V := V)).comp (Subgroup.closure D).subtype) D) := by
    refine Submodule.span_mono ?_
    rintro f ⟨t, ht, v, h⟩
    exact ⟨_, mem_imgSet _ (t := ⟨t, Subgroup.subset_closure ht⟩) ht, _,
      isTransvectionWith_dualHom h⟩
  have h2 : (cenSpan D).dualAnnihilator ≤ fixSub (Subgroup.closure (imgSet (Subgroup.closure D)
      ((dualHom (p := p) (V := V)).comp (Subgroup.closure D).subtype) D)) := by
    intro ψ hψ
    refine mem_fixSub_closure_of_forall ?_
    rintro _ ⟨⟨t, htT⟩, ht, rfl⟩
    obtain ⟨v, f, h⟩ := hD t ht
    have hψv : ψ v = 0 := (Submodule.mem_dualAnnihilator ψ).mp hψ v (center_mem_cenSpan ht h)
    refine LinearMap.ext fun x => ?_
    change ψ (t.symm x) = ψ x
    rw [show t.symm x = t⁻¹ x from rfl, h.inv_apply, map_sub, map_smul, hψv, smul_zero, sub_zero]
  have h3 : (cenSpan D ⊔ fixSub (Subgroup.closure D)).dualAnnihilator = ⊥ := by
    rw [Submodule.dualAnnihilator_sup_eq, fixSub_eq_dualCoannihilator hD,
      Subspace.dualCoannihilator_dualAnnihilator_eq, eq_bot_iff, ← hbot]
    exact fun ψ hψ => ⟨h1 hψ.2, h2 hψ.1⟩
  exact Submodule.dualAnnihilator_eq_bot_iff.mp h3

theorem mem_closure_imgSet_resCen_iff {D : Set (V ≃ₗ[ZMod p] V)}
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) (g : cenSpan D ≃ₗ[ZMod p] cenSpan D) :
    g ∈ Subgroup.closure (imgSet (Subgroup.closure D) (resCen D hD) D) ↔
      ∃ h ∈ Subgroup.closure D, ∀ x : cenSpan D, h x = g x := by
  rw [← range_eq_closure_imgSet]
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨h, hh, fun x => rfl⟩
  · rintro ⟨h, hh, hx⟩
    exact ⟨⟨h, hh⟩, LinearEquiv.ext fun x => Subtype.ext (hx x)⟩

theorem kantor_connected (hp : p ≠ 2) [Module.Finite (ZMod p) V] (D : Set (V ≃ₗ[ZMod p] V))
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) (hconn : IsConnTr D)
    (hT : NoNormalExpP (Subgroup.closure D)) :
    IsCompl (cenSpan D) (fixSub (Subgroup.closure D)) ∧
      ((∀ g : cenSpan D ≃ₗ[ZMod p] cenSpan D,
          (∃ h ∈ Subgroup.closure D, ∀ x : cenSpan D, h x = g x) ↔
            LinearMap.det (g : cenSpan D →ₗ[ZMod p] cenSpan D) = 1) ∨
        ∃ B : LinearMap.BilinForm (ZMod p) (cenSpan D), B.IsAlt ∧ B.Nondegenerate ∧
          ∀ g : cenSpan D ≃ₗ[ZMod p] cenSpan D,
            (∃ h ∈ Subgroup.closure D, ∀ x : cenSpan D, h x = g x) ↔
              ∀ x y, B (g x) (g y) = B x y) := by
  have hinf := cenSpan_inf_fixSub_eq_bot hp D hD hconn hT
  refine ⟨⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr (cenSpan_sup_fixSub_eq_top hp D hD hconn hT)⟩,
    ?_⟩
  have hφ := resCen_injective hD hT
  have hrange := range_eq_closure_imgSet D (resCen D hD)
  have hD' := isTransvection_imgSet_resCen hD hT
  have hconn' := isConnTr_imgSet hconn _ hφ
  have hT' := hrange ▸ noNormalExpP_range hT _ hφ
  have hU' := cenSpan_imgSet_resCen hD hT
  have hC' : fixSub (Subgroup.closure (imgSet (Subgroup.closure D) (resCen D hD) D)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [← hrange] at hy
    have h1 := (mem_fixSub_range_resHom (T := Subgroup.closure D) (W := cenSpan D) _).mp hy
    have h2 : (y : V) ∈ cenSpan D ⊓ fixSub (Subgroup.closure D) := ⟨y.2, h1⟩
    rw [hinf, Submodule.mem_bot] at h2
    exact (Submodule.mem_bot _).mpr (Subtype.ext h2)
  have hirr := irreducible_of_isConnTr hD' hconn' hT' hU' hC'
  rcases mcLaughlin_odd hp _ hirr ⟨_, hD', rfl⟩ with hSL | ⟨B, hBa, hBn, hSp⟩
  · exact Or.inl fun g => (mem_closure_imgSet_resCen_iff hD g).symm.trans (hSL g)
  · exact Or.inr ⟨B, hBa, hBn, fun g => (mem_closure_imgSet_resCen_iff hD g).symm.trans (hSp g)⟩

end CFSG.StandardType.McLaughlinOdd

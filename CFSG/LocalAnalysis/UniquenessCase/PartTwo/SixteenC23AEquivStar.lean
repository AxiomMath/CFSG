module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_equiv_star (D : Data G) (h1217 : R1217 D) {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hK : K₀ ≤ D.M) (hV0 : V₀ = ⊥) :
    ∃ (f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV)
      (ρ : ↥(barSub V₀ V hV K₀) ≃* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)),
      (∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
        mkTil (v1Sub D.M V₀ V hV L) V hV x) ∧
      ∀ (a : ↥(barSub V₀ V hV K₀)) (y : Vtil V₀ V hV),
        f ((a : MulAut (Vtil V₀ V hV)) y) =
          ((ρ a : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
            MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f y) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub (L := L) h.hyp125 hV)
  have hle : V₀ ≤ v1Sub D.M V₀ V hV L := by rw [hV0]; exact bot_le
  let f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV :=
    QuotientGroup.map (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV)
      (MonoidHom.id (IntMod V hV)) (by
        rw [Subgroup.comap_id]
        intro x hx
        rw [mem_modNull] at hx ⊢
        exact hle hx)
  have hf : ∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
      mkTil (v1Sub D.M V₀ V hV L) V hV x := by
    intro x
    exact QuotientGroup.map_mk (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV)
      (MonoidHom.id (IntMod V hV)) _ x
  let σ₀ : ↥K₀ →* ↥(barSub V₀ V hV K₀) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion (hK.trans hMs))).codRestrict _
      (fun k => by
        change actTil V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ ∈ barSub V₀ V hV K₀
        exact actTil_mem_barSub V₀ V hV k.2 (hMs (hK k.2)))
  let σ₁ : ↥K₀ →* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    ((actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion (hK.trans hMs1))).codRestrict _
      (fun k => by
        change actTil (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ ∈
          barSub (v1Sub D.M V₀ V hV L) V hV K₀
        exact actTil_mem_barSub _ V hV k.2 (hMs1 (hK k.2)))
  have hσ₀val : ∀ k : ↥K₀, (σ₀ k : MulAut (Vtil V₀ V hV)) =
      actTil V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ := fun k =>
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)
  have hσ₁val : ∀ k : ↥K₀,
      (σ₁ k : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) =
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ := fun k =>
    congrArg (actTil _ V hV) (Subtype.ext rfl)
  have hσ₀ : Function.Surjective σ₀ := by
    intro a
    obtain ⟨g, hgK, hga⟩ := (mem_barSub V₀ V hV K₀ a).1 a.2
    refine ⟨⟨(g : G), hgK⟩, ?_⟩
    apply Subtype.ext
    rw [hσ₀val ⟨(g : G), hgK⟩]
    rw [show actTil V₀ V hV ⟨(g : G), hMs (hK hgK)⟩ = actTil V₀ V hV g from
      congrArg _ (Subtype.ext rfl)]
    exact hga
  have hσ₁ : Function.Surjective σ₁ := by
    intro a
    obtain ⟨g, hgK, hga⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV K₀ a).1 a.2
    refine ⟨⟨(g : G), hgK⟩, ?_⟩
    apply Subtype.ext
    rw [hσ₁val ⟨(g : G), hgK⟩]
    rw [show actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), hMs1 (hK hgK)⟩ =
        actTil (v1Sub D.M V₀ V hV L) V hV g from congrArg _ (Subtype.ext rfl)]
    exact hga
  have hker₀ : σ₀.ker = (F11.CTilde D.M V₀ V).subgroupOf K₀ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hk
      have h3 := congrArg (fun z : ↥(barSub V₀ V hV K₀) =>
        (z : MulAut (Vtil V₀ V hV))) hk
      rw [hσ₀val k] at h3
      exact ⟨hK k.2, hMs (hK k.2), by simpa using h3⟩
    · rintro ⟨-, hst, hact⟩
      apply Subtype.ext
      rw [hσ₀val k]
      rw [show (⟨(k : G), hMs (hK k.2)⟩ : stabTil V₀ V) = ⟨(k : G), hst⟩ from
        Subtype.ext rfl]
      exact hact
  have hker₁ : σ₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hk
      have h3 := congrArg (fun z : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) =>
        (z : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))) hk
      rw [hσ₁val k] at h3
      exact ⟨hK k.2, hMs1 (hK k.2), by simpa using h3⟩
    · rintro ⟨-, hst, hact⟩
      apply Subtype.ext
      rw [hσ₁val k]
      rw [show (⟨(k : G), hMs1 (hK k.2)⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
          ⟨(k : G), hst⟩ from Subtype.ext rfl]
      exact hact
  have hkereq : (F11.CTilde D.M V₀ V).subgroupOf K₀ =
      (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ := by
    rw [fifteen_two_cent D h1217 h hV]
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf K₀).Normal := hker₀ ▸ MonoidHom.normal_ker σ₀
  haveI : ((F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀).Normal :=
    hker₁ ▸ MonoidHom.normal_ker σ₁
  let e0 : ↥K₀ ⧸ (F11.CTilde D.M V₀ V).subgroupOf K₀ ≃* ↥(barSub V₀ V hV K₀) :=
    QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf K₀) hσ₀ hker₀.symm
  let e1 : ↥K₀ ⧸ (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ ≃*
      ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    QuotientGroup.liftEquiv ((F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀)
      hσ₁ hker₁.symm
  let ρ : ↥(barSub V₀ V hV K₀) ≃* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    e0.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkereq).trans e1)
  have hρk : ∀ k : ↥K₀, ρ (σ₀ k) = σ₁ k := by
    intro k
    have h0 : e0.symm (σ₀ k) = QuotientGroup.mk k := by
      rw [show σ₀ k = e0 (QuotientGroup.mk k) from
        (QuotientGroup.liftEquiv_mk _ hσ₀ hker₀.symm k).symm]
      exact MulEquiv.symm_apply_apply e0 _
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkereq) (QuotientGroup.mk k) =
        QuotientGroup.mk k := QuotientGroup.quotientMulEquivOfEq_mk hkereq k
    have h2 : e1 (QuotientGroup.mk k) = σ₁ k :=
      QuotientGroup.liftEquiv_mk _ hσ₁ hker₁.symm k
    change e1 ((QuotientGroup.quotientMulEquivOfEq hkereq) (e0.symm (σ₀ k))) = σ₁ k
    rw [h0, h1, h2]
  have hstab : ∀ (k : ↥K₀) (x : IntMod V hV),
      actStab V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ x =
        actStab (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ x := by
    intro k x
    apply IntMod.val_injective
    rw [actStab_apply_val, actStab_apply_val]
  have hσinter : ∀ (k : ↥K₀) (y : Vtil V₀ V hV),
      f ((σ₀ k : MulAut (Vtil V₀ V hV)) y) =
        ((σ₁ k : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
          MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f y) := by
    intro k y
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV y
    have hL : f ((σ₀ k : MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x)) =
        mkTil (v1Sub D.M V₀ V hV L) V hV
          (actStab V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ x) := by
      rw [hσ₀val k, actTil_mk, hf]
    have hR : ((σ₁ k : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
          MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f (mkTil V₀ V hV x)) =
        mkTil (v1Sub D.M V₀ V hV L) V hV
          (actStab (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ x) := by
      rw [hσ₁val k, hf, actTil_mk]
    rw [hL, hR, hstab k x]
  refine ⟨f, ρ, hf, ?_⟩
  intro a y
  obtain ⟨k, rfl⟩ := hσ₀ a
  rw [hρk k]
  exact hσinter k y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

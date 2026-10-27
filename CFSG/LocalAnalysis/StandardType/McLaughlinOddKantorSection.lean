module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorBasic

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {V' : Type*} [AddCommGroup V'] [Module (ZMod p) V']

@[expose] def imgSet (T : Subgroup (V ≃ₗ[ZMod p] V)) (φ : T →* (V' ≃ₗ[ZMod p] V'))
    (D : Set (V ≃ₗ[ZMod p] V)) : Set (V' ≃ₗ[ZMod p] V') :=
  {t' | ∃ t : T, (t : V ≃ₗ[ZMod p] V) ∈ D ∧ φ t = t'}

theorem mem_imgSet {T : Subgroup (V ≃ₗ[ZMod p] V)} (φ : T →* (V' ≃ₗ[ZMod p] V'))
    {D : Set (V ≃ₗ[ZMod p] V)} {t : T} (ht : (t : V ≃ₗ[ZMod p] V) ∈ D) : φ t ∈ imgSet T φ D :=
  ⟨t, ht, rfl⟩

theorem range_eq_closure_imgSet (D : Set (V ≃ₗ[ZMod p] V))
    (φ : Subgroup.closure D →* (V' ≃ₗ[ZMod p] V')) :
    φ.range = Subgroup.closure (imgSet (Subgroup.closure D) φ D) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := D),
    MonoidHom.map_closure]
  rfl

theorem noNormalExpP_range {T : Subgroup (V ≃ₗ[ZMod p] V)} (hT : NoNormalExpP T)
    (φ : T →* (V' ≃ₗ[ZMod p] V')) (hφ : Function.Injective φ) : NoNormalExpP φ.range := by
  intro N' hN' hnorm hexp
  have hNbot : (N'.comap φ).map T.subtype = ⊥ := by
    refine hT _ (fun x hx => ?_) (fun g hg n hn => ?_) (fun n hn => ?_)
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · obtain ⟨m, hm, rfl⟩ := hn
      refine ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      change φ (⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹) ∈ N'
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ ⟨⟨g, hg⟩, rfl⟩ _ hm
    · obtain ⟨m, hm, rfl⟩ := hn
      have h1 : m ^ p = 1 := hφ (by rw [map_pow, map_one]; exact hexp _ hm)
      change (m : V ≃ₗ[ZMod p] V) ^ p = 1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  rw [eq_bot_iff]
  intro n' hn'
  obtain ⟨m, rfl⟩ := hN' hn'
  have : (m : V ≃ₗ[ZMod p] V) ∈ (N'.comap φ).map T.subtype := ⟨m, hn', rfl⟩
  rw [hNbot, Subgroup.mem_bot] at this
  have hm : m = 1 := Subtype.ext this
  rw [hm, map_one]
  exact Subgroup.one_mem _

theorem isConnTr_imgSet {D : Set (V ≃ₗ[ZMod p] V)} (hconn : IsConnTr D)
    (φ : Subgroup.closure D →* (V' ≃ₗ[ZMod p] V')) (hφ : Function.Injective φ) :
    IsConnTr (imgSet (Subgroup.closure D) φ D) := by
  intro P' hP' hcomm
  set P : Set (V ≃ₗ[ZMod p] V) :=
    {t | ∃ ht : t ∈ Subgroup.closure D, t ∈ D ∧ φ ⟨t, ht⟩ ∈ P'} with hPdef
  have hPD : P ⊆ D := fun t ⟨_, ht, _⟩ => ht
  have hc : ∀ t ∈ P, ∀ s ∈ D, s ∉ P → Commute t s := by
    rintro t ⟨ht, -, htP⟩ s hs hsP
    have hs' : φ ⟨s, Subgroup.subset_closure hs⟩ ∉ P' := fun h => hsP ⟨_, hs, h⟩
    have h1 := hcomm _ htP _ (mem_imgSet φ (t := ⟨s, Subgroup.subset_closure hs⟩) hs) hs'
    have h2 : φ (⟨t, ht⟩ * ⟨s, Subgroup.subset_closure hs⟩) =
        φ (⟨s, Subgroup.subset_closure hs⟩ * ⟨t, ht⟩) := by
      rw [map_mul, map_mul]
      exact h1.eq
    exact congrArg Subtype.val (hφ h2)
  rcases hconn P hPD hc with h | h
  · left
    refine Set.eq_empty_of_forall_notMem fun t' ht' => ?_
    obtain ⟨⟨t, htT⟩, htD, rfl⟩ := hP' ht'
    have : t ∈ P := ⟨htT, htD, ht'⟩
    rw [h] at this
    exact this
  · right
    refine Set.Subset.antisymm hP' fun t' ht' => ?_
    obtain ⟨⟨t, htT⟩, htD, rfl⟩ := ht'
    have : t ∈ P := h ▸ htD
    obtain ⟨ht2, -, htP⟩ := this
    exact htP

theorem mem_fixSub_closure_of_forall {S : Set (V ≃ₗ[ZMod p] V)} {x : V}
    (hx : ∀ s ∈ S, s x = x) : x ∈ fixSub (Subgroup.closure S) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => g x = x) (fun s hs => hx s hs) rfl
    (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) hg
  · rw [LinearEquiv.mul_apply, hb, ha]
  · change a.symm x = x
    rw [LinearEquiv.symm_apply_eq, ha]

theorem map_eq_of_invariant {T : Subgroup (V ≃ₗ[ZMod p] V)} {W : Submodule (ZMod p) V}
    (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ T) :
    W.map (g : V →ₗ[ZMod p] V) = W := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hW g hg y hy
  · refine ⟨g.symm x, hW g⁻¹ (T.inv_mem hg) x hx, ?_⟩
    exact g.apply_symm_apply x

@[expose] noncomputable def resHom (T : Subgroup (V ≃ₗ[ZMod p] V)) (W : Submodule (ZMod p) V)
    (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W) : T →* (W ≃ₗ[ZMod p] W) where
  toFun g := (g : V ≃ₗ[ZMod p] V).ofSubmodules W W (map_eq_of_invariant hW g.2)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

variable {T : Subgroup (V ≃ₗ[ZMod p] V)}

theorem resHom_apply {W : Submodule (ZMod p) V} (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W) (g : T)
    (x : W) : ((resHom T W hW g x : W) : V) = (g : V ≃ₗ[ZMod p] V) x := rfl

theorem resHom_injective (hT : NoNormalExpP T) {W : Submodule (ZMod p) V}
    (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W) (hmov : ∀ g ∈ T, ∀ x, g x - x ∈ W) :
    Function.Injective (resHom T W hW) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Subtype.ext (eq_one_of_unip hT hW g.2 (hmov g g.2) fun x hx => ?_)
  have := congrArg (fun e : W ≃ₗ[ZMod p] W => ((e ⟨x, hx⟩ : W) : V)) hg
  simpa [resHom_apply] using this

theorem isTransvectionWith_resHom {W : Submodule (ZMod p) V} (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W)
    {g : T} {v : V} {f : Module.Dual (ZMod p) V} (h : IsTransvectionWith (g : V ≃ₗ[ZMod p] V) v f)
    (hv : v ∈ W) (hf : f ∘ₗ W.subtype ≠ 0) :
    IsTransvectionWith (resHom T W hW g) ⟨v, hv⟩ (f ∘ₗ W.subtype) :=
  ⟨fun h0 => h.1 (congrArg Subtype.val h0), hf, h.2.2.1, fun x => Subtype.ext (h.2.2.2 x)⟩

theorem mem_fixSub_range_resHom {W : Submodule (ZMod p) V} (hW : ∀ g ∈ T, ∀ x ∈ W, g x ∈ W)
    {x : W} : x ∈ fixSub (resHom T W hW).range ↔ (x : V) ∈ fixSub T := by
  constructor
  · intro hx g hg
    have := hx _ ⟨⟨g, hg⟩, rfl⟩
    exact congrArg Subtype.val this
  · rintro hx _ ⟨g, rfl⟩
    exact Subtype.ext (hx g g.2)

variable {D : Set (V ≃ₗ[ZMod p] V)}

@[expose] noncomputable def resCen (D : Set (V ≃ₗ[ZMod p] V))
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) :
    Subgroup.closure D →* (cenSpan D ≃ₗ[ZMod p] cenSpan D) :=
  resHom (Subgroup.closure D) (cenSpan D) fun _ hg _ hx => cenSpan_invariant hD hg hx

theorem resCen_injective (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hT : NoNormalExpP (Subgroup.closure D)) : Function.Injective (resCen D hD) :=
  resHom_injective hT _ fun _ hg x => sub_mem_cenSpan hD hg x

theorem isTransvectionWith_resCen (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hT : NoNormalExpP (Subgroup.closure D)) {t : V ≃ₗ[ZMod p] V} (ht : t ∈ D) {v : V}
    {f : Module.Dual (ZMod p) V} (h : IsTransvectionWith t v f) :
    IsTransvectionWith (resCen D hD ⟨t, Subgroup.subset_closure ht⟩)
      ⟨v, center_mem_cenSpan ht h⟩ (f ∘ₗ (cenSpan D).subtype) := by
  refine isTransvectionWith_resHom _ (g := ⟨t, Subgroup.subset_closure ht⟩) h _ fun h0 => ?_
  refine transvection_ne_one h (eq_one_of_unip hT (fun _ hg _ hx => cenSpan_invariant hD hg hx)
    (Subgroup.subset_closure ht) (sub_mem_cenSpan hD (Subgroup.subset_closure ht)) fun x hx => ?_)
  have := LinearMap.congr_fun h0 ⟨x, hx⟩
  change f x = 0 at this
  rw [h.2.2.2, this, zero_smul, add_zero]

theorem isTransvection_imgSet_resCen (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hT : NoNormalExpP (Subgroup.closure D)) :
    ∀ t' ∈ imgSet (Subgroup.closure D) (resCen D hD) D, ∃ c φ, IsTransvectionWith t' c φ := by
  rintro _ ⟨⟨t, htT⟩, ht, rfl⟩
  obtain ⟨v, f, h⟩ := hD t ht
  exact ⟨_, _, isTransvectionWith_resCen hD hT ht h⟩

theorem cenSpan_imgSet_resCen (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hT : NoNormalExpP (Subgroup.closure D)) :
    cenSpan (imgSet (Subgroup.closure D) (resCen D hD) D) = ⊤ := by
  have htop : Submodule.span (ZMod p) (Subtype.val ⁻¹' cenSet D : Set (cenSpan D)) = ⊤ :=
    Submodule.span_span_coe_preimage
  rw [eq_top_iff, ← htop]
  refine Submodule.span_le.mpr fun x hx => Submodule.subset_span ?_
  obtain ⟨t, ht, f, h⟩ := hx
  exact ⟨_, mem_imgSet (resCen D hD) (t := ⟨t, Subgroup.subset_closure ht⟩) ht, _,
    isTransvectionWith_resCen hD hT ht h⟩

@[expose] noncomputable def quoHom (T : Subgroup (V ≃ₗ[ZMod p] V)) (X : Submodule (ZMod p) V)
    (hX : X ≤ fixSub T) : T →* ((V ⧸ X) ≃ₗ[ZMod p] (V ⧸ X)) where
  toFun g := Submodule.Quotient.equiv X X (g : V ≃ₗ[ZMod p] V)
    (map_eq_of_invariant (fun h hh x hx => by rw [hX hx h hh]; exact hx) g.2)
  map_one' := LinearEquiv.ext fun x => Submodule.Quotient.induction_on X x fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun x => Submodule.Quotient.induction_on X x fun _ => rfl

theorem quoHom_mk {X : Submodule (ZMod p) V} (hX : X ≤ fixSub T) (g : T) (x : V) :
    quoHom T X hX g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((g : V ≃ₗ[ZMod p] V) x) := rfl

theorem quoHom_injective (hT : NoNormalExpP T) {X : Submodule (ZMod p) V} (hX : X ≤ fixSub T) :
    Function.Injective (quoHom T X hX) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Subtype.ext (eq_one_of_unip hT (fun h hh x hx => by rw [hX hx h hh]; exact hx) g.2
    (fun x => ?_) fun x hx => hX hx g g.2)
  have := congrArg (fun e : (V ⧸ X) ≃ₗ[ZMod p] (V ⧸ X) => e (Submodule.Quotient.mk x)) hg
  change Submodule.Quotient.mk ((g : V ≃ₗ[ZMod p] V) x) = Submodule.Quotient.mk x at this
  rwa [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at this

theorem isTransvectionWith_quoHom {X : Submodule (ZMod p) V} (hX : X ≤ fixSub T) {g : T}
    {v : V} {f : Module.Dual (ZMod p) V} (h : IsTransvectionWith (g : V ≃ₗ[ZMod p] V) v f)
    (hv : v ∉ X) (hfX : X ≤ LinearMap.ker f) :
    IsTransvectionWith (quoHom T X hX g) (Submodule.Quotient.mk v) (X.liftQ f hfX) := by
  refine ⟨fun h0 => hv ((Submodule.Quotient.mk_eq_zero X).mp h0), fun h0 => h.2.1 ?_,
    by rw [Submodule.liftQ_apply, h.2.2.1], fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk x)
    rwa [Submodule.liftQ_apply] at this
  · induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [quoHom_mk, h.2.2.2, Submodule.liftQ_apply, Submodule.Quotient.mk_add,
        Submodule.Quotient.mk_smul]

@[expose] noncomputable def dualHom :
    (V ≃ₗ[ZMod p] V) →* (Module.Dual (ZMod p) V ≃ₗ[ZMod p] Module.Dual (ZMod p) V) where
  toFun g := g.symm.dualMap
  map_one' := LinearEquiv.ext fun _ => LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => LinearMap.ext fun _ => rfl

theorem dualHom_apply (g : V ≃ₗ[ZMod p] V) (φ : Module.Dual (ZMod p) V) (x : V) :
    dualHom g φ x = φ (g.symm x) := rfl

theorem dualHom_injective : Function.Injective (dualHom (p := p) (V := V)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h2 : ∀ x, g.symm x = x := by
    intro x
    refine sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).mp fun φ => ?_)
    have := LinearMap.congr_fun (LinearEquiv.congr_fun hg φ) x
    change φ (g.symm x) = φ x at this
    rw [map_sub, this, sub_self]
  refine LinearEquiv.ext fun x => ?_
  calc g x = g (g.symm x) := by rw [h2]
    _ = x := g.apply_symm_apply x

theorem isTransvectionWith_dualHom {t : V ≃ₗ[ZMod p] V} {v : V} {f : Module.Dual (ZMod p) V}
    (h : IsTransvectionWith t v f) :
    IsTransvectionWith (dualHom t) f (-(Module.Dual.eval (ZMod p) V v)) := by
  refine ⟨h.2.1, fun h0 => h.1 ?_, by simp [h.2.2.1], fun φ => LinearMap.ext fun x => ?_⟩
  · refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) v).mp fun φ => ?_
    have := LinearMap.congr_fun h0 φ
    simpa using this
  · rw [dualHom_apply, show t.symm x = t⁻¹ x from rfl, h.inv_apply]
    simp only [map_sub, map_smul, smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Module.Dual.eval_apply]
    ring

end CFSG.StandardType.McLaughlinOdd

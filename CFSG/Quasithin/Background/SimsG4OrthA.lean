module

public import CFSG.Quasithin.Background.SimsG4OrthAForm
public import CFSG.Quasithin.Background.SimsG4OrthAModel

public section

namespace CFSG.Quasithin.SimsG4

@[expose] def OrthIdent : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (W : Type) [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W), Module.finrank K W = 4 →
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) →
    ∀ R : Set W, (∀ r ∈ R, Q r = 1) →
    (∀ K₁ : Subfield K, (∀ r ∈ R, ∀ s ∈ R, QuadraticMap.polar Q r s ∈ K₁) → K₁ = ⊤) →
    IsIrredOnV (Subgroup.closure
      {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r}) →
    ¬ IsImprimitiveOnV (Subgroup.closure
      {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r}) →
    ∀ g : W ≃ₗ[K] W, (∀ x, Q (g x) = Q x) →
      g ∈ Subgroup.closure {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r}

namespace OrthA

open LinearMap (BilinForm)

@[expose] def orthTransvSet {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (R : Set W) : Set (W ≃ₗ[K] W) :=
  {g | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r}

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

section Transfer

variable {F₀ : Subfield F} {I : Submodule F₀ V} {G₀ : Subgroup (V ≃ₗ[F] V)}
  (hGI : ∀ g ∈ G₀, ∀ x ∈ I, g x ∈ I) {T : Set (I ≃ₗ[F₀] I)}

include hGI in
theorem resHom_mem_closure (hDT : ∀ d (hd : d ∈ transvSet G₀), resHom hGI ⟨d, hd.1⟩ ∈ T)
    {g : V ≃ₗ[F] V} (hg : g ∈ Subgroup.closure (transvSet G₀)) :
    resHom hGI ⟨g, transvGen_le G₀ hg⟩ ∈ Subgroup.closure T := by
  induction hg using Subgroup.closure_induction with
  | mem d hd => exact Subgroup.subset_closure (hDT d hd)
  | one =>
    have e : (⟨1, transvGen_le G₀ (one_mem _)⟩ : G₀) = 1 := rfl
    rw [e, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, transvGen_le G₀ (mul_mem hx hy)⟩ : G₀) =
        ⟨x, transvGen_le G₀ hx⟩ * ⟨y, transvGen_le G₀ hy⟩ := rfl
    rw [e, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have e : (⟨x⁻¹, transvGen_le G₀ (inv_mem hx)⟩ : G₀) = (⟨x, transvGen_le G₀ hx⟩)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem ihx

omit hGI in
theorem exists_of_mem_closure (hTD : ∀ h ∈ T, ∃ d ∈ transvSet G₀, ∀ x : I, (h x : V) = d x)
    {h : I ≃ₗ[F₀] I} (hh : h ∈ Subgroup.closure T) :
    ∃ g ∈ transvGen G₀, ∀ x : I, (h x : V) = g x := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨d, hd, hdh⟩ := hTD h hh
    exact ⟨d, Subgroup.subset_closure hd, hdh⟩
  | one => exact ⟨1, one_mem _, fun _ => rfl⟩
  | mul h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, e₁⟩ := ih₁
    obtain ⟨g₂, hg₂, e₂⟩ := ih₂
    refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun x => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₁, e₂]
  | inv h _ ih =>
    obtain ⟨g, hg, e⟩ := ih
    refine ⟨g⁻¹, inv_mem hg, fun x => ?_⟩
    have e' := e (h⁻¹ x)
    rw [mul_inv_apply] at e'
    rw [e', inv_mul_apply]

variable {B : BilinForm F V}

include hGI in
theorem isIrredOnV_closure [Finite V] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (hspan : Submodule.span F (I : Set V) = ⊤)
    (hDT : ∀ d (hd : d ∈ transvSet G₀), resHom hGI ⟨d, hd.1⟩ ∈ T)
    (hirr : IsIrredOnV (transvGen G₀)) : IsIrredOnV (Subgroup.closure T) := by
  intro U hU
  have hU'I : U.map I.subtype ≤ I := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hinv : ∀ g ∈ transvGen G₀, ∀ w ∈ Submodule.span F (U.map I.subtype : Set V),
      g w ∈ Submodule.span F (U.map I.subtype : Set V) := by
    intro g hg w hw
    have hU'g : ∀ w ∈ U.map I.subtype, g w ∈ U.map I.subtype := by
      rintro _ ⟨u, hu, rfl⟩
      exact Submodule.mem_map.mpr ⟨_, hU _ (resHom_mem_closure hGI hDT hg) u hu, rfl⟩
    have hle : Submodule.span F (U.map I.subtype : Set V) ≤
        (Submodule.span F (U.map I.subtype : Set V)).comap (g : V →ₗ[F] V) :=
      Submodule.span_le.mpr fun w hw => Submodule.subset_span (hU'g w hw)
    exact hle hw
  rcases hirr _ hinv with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have hu' : (u : V) ∈ Submodule.span F (U.map I.subtype : Set V) :=
      Submodule.subset_span (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
    rw [h, Submodule.mem_bot] at hu'
    exact (Submodule.mem_bot _).mpr (Subtype.ext hu')
  · right
    have hfr := finrank_span_of_le halt hnd hval hspan hU'I
    rw [h, finrank_top, ← finrank_form halt hnd hval hspan] at hfr
    have hU'eq : U.map I.subtype = I := Submodule.eq_of_le_of_finrank_eq hU'I hfr.symm
    rw [eq_top_iff]
    intro x _
    have hx : (x : V) ∈ U.map I.subtype := by
      rw [hU'eq]
      exact x.2
    obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp hx
    have hux' : u = x := Subtype.ext hux
    rw [← hux']
    exact hu

include hGI in
theorem not_isImprimitiveOnV_closure [Finite V] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (hspan : Submodule.span F (I : Set V) = ⊤)
    (hDT : ∀ d (hd : d ∈ transvSet G₀), resHom hGI ⟨d, hd.1⟩ ∈ T)
    (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) : ¬ IsImprimitiveOnV (Subgroup.closure T) := by
  rintro ⟨r, W, hr, hW0, hWind, hWsup, hWperm⟩
  apply hprim
  have hUI : ∀ i, (W i).map I.subtype ≤ I := fun i => by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  refine ⟨r, fun i => Submodule.span F ((W i).map I.subtype : Set V), hr, fun i => ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (hW0 i)
    rw [Submodule.ne_bot_iff]
    exact ⟨w, Submodule.subset_span (Submodule.mem_map.mpr ⟨w, hw, rfl⟩),
      fun h => hw0 (Subtype.ext h)⟩
  · rw [iSupIndep_def]
    intro i
    have hdisj : Disjoint ((W i).map I.subtype)
        (⨆ j, ⨆ (_ : j ≠ i), (W j).map I.subtype) := by
      have h2 := Submodule.disjoint_map I.injective_subtype (iSupIndep_def.mp hWind i)
      simp only [Submodule.map_iSup] at h2
      exact h2
    have e : (⨆ j, ⨆ (_ : j ≠ i), Submodule.span F ((W j).map I.subtype : Set V)) =
        Submodule.span F ((⨆ j, ⨆ (_ : j ≠ i), (W j).map I.subtype : Submodule F₀ V) : Set V) := by
      simp only [span_iSup]
    show Disjoint (Submodule.span F ((W i).map I.subtype : Set V))
      (⨆ j, ⨆ (_ : j ≠ i), Submodule.span F ((W j).map I.subtype : Set V))
    rw [e]
    exact disjoint_span_of_le halt hnd hval hspan (hUI i)
      (iSup_le fun j => iSup_le fun _ => hUI j) hdisj
  · show (⨆ i, Submodule.span F ((W i).map I.subtype : Set V)) = ⊤
    rw [← span_iSup, ← Submodule.map_iSup, hWsup, Submodule.map_subtype_top, hspan]
  · intro g hg i
    obtain ⟨j, hj⟩ := hWperm _ (resHom_mem_closure hGI hDT hg) i
    refine ⟨j, ?_⟩
    have hcomp : ((g : V →ₗ[F] V).restrictScalars F₀) ∘ₗ I.subtype =
        I.subtype ∘ₗ ((resHom hGI ⟨g, transvGen_le G₀ hg⟩ : I ≃ₗ[F₀] I) : I →ₗ[F₀] I) :=
      LinearMap.ext fun _ => rfl
    have hmap : ((W i).map I.subtype).map ((g : V →ₗ[F] V).restrictScalars F₀) =
        (W j).map I.subtype := by
      rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hj]
    show (Submodule.span F ((W i).map I.subtype : Set V)).map (g : V →ₗ[F] V) =
      Submodule.span F ((W j).map I.subtype : Set V)
    rw [Submodule.map_span, ← hmap, Submodule.map_coe]
    rfl

end Transfer

section Space

variable (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))

@[expose] def formQ : QuadraticForm (centreField Q G₀) (centreForm Q G₀) :=
  subForm Q (centreForm Q G₀) (fun _ hx => apply_mem_centreField hx)
    (fun _ hx _ hy => polar_mem_centreField hx hy)

@[expose] def formR : Set (centreForm Q G₀) :=
  {w | (w : V) ∈ centreSet Q G₀}

variable {Q G₀}

theorem coe_formQ (x : centreForm Q G₀) : ((formQ Q G₀ x : centreField Q G₀) : F) = Q x :=
  rfl

theorem coe_polar_formQ (x y : centreForm Q G₀) :
    ((QuadraticMap.polar (formQ Q G₀) x y : centreField Q G₀) : F) =
      QuadraticMap.polar Q x y :=
  coe_polar_subForm _ _ _ x y

theorem formQ_eq_one : ∀ r ∈ formR Q G₀, formQ Q G₀ r = 1 :=
  fun _ hr => Subtype.ext hr.1

theorem eq_top_of_polar_mem (K₁ : Subfield (centreField Q G₀))
    (hK₁ : ∀ r ∈ formR Q G₀, ∀ s ∈ formR Q G₀, QuadraticMap.polar (formQ Q G₀) r s ∈ K₁) :
    K₁ = ⊤ := by
  have hle : centreField Q G₀ ≤ K₁.map (centreField Q G₀).subtype := by
    refine Subfield.closure_le.mpr ?_
    rintro a ⟨r, hr, s, hs, rfl⟩
    exact Subfield.mem_map.mpr ⟨_, hK₁ ⟨r, Submodule.subset_span hr⟩ hr
      ⟨s, Submodule.subset_span hs⟩ hs, coe_polar_formQ _ _⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (hle x.2)
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end Space

structure OrthHyp (B : BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) (Q : QuadraticForm F V) :
    Prop where
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0
  finrank_eq : Module.finrank F V = 4
  le_sp : G₀ ≤ spGroup B
  transv_nonempty : (transvSet G₀).Nonempty
  irred : IsIrredOnV (transvGen G₀)
  polar_eq : ∀ x y, QuadraticMap.polar Q x y = B x y
  isometry : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x

namespace OrthHyp

variable [Finite F] [CharP F 2] {B : BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
  {Q : QuadraticForm F V} (h : OrthHyp B G₀ Q)

include h

theorem finite : Finite V :=
  (finite_even_card h.finrank_eq).1

theorem exists_centre {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) :
    ∃ r ∈ centreSet Q G₀, ∀ x, d x = x + QuadraticMap.polar Q x r • r :=
  OrthA.exists_centre B h.alt h.nondeg h.le_sp h.polar_eq h.isometry hd

theorem centreSet_nonempty : (centreSet Q G₀).Nonempty := by
  obtain ⟨d, hd⟩ := h.transv_nonempty
  obtain ⟨r, hr, -⟩ := h.exists_centre hd
  exact ⟨r, hr⟩

theorem span_form : Submodule.span F (centreForm Q G₀ : Set V) = ⊤ :=
  span_centreForm (span_centreSet h.isometry (isIrredOnV_of_le (transvGen_le G₀) h.irred)
    h.centreSet_nonempty)

theorem val : ∀ x ∈ centreForm Q G₀, ∀ y ∈ centreForm Q G₀, B x y ∈ centreField Q G₀ :=
  fun x hx y hy => h.polar_eq x y ▸ polar_mem_centreField hx hy

theorem mapsTo : ∀ g ∈ G₀, ∀ x ∈ centreForm Q G₀, g x ∈ centreForm Q G₀ :=
  fun _ hg _ hx => apply_mem_centreForm h.isometry hg hx

theorem finrank_form' : Module.finrank (centreField Q G₀) (centreForm Q G₀) = 4 := by
  haveI := h.finite
  rw [finrank_form h.alt h.nondeg h.val h.span_form, h.finrank_eq]

theorem nondeg_formQ :
    ∀ x : centreForm Q G₀, (∀ y, QuadraticMap.polar (formQ Q G₀) x y = 0) → x = 0 := by
  intro x hx
  by_contra hx0
  have hx0' : (x : V) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  obtain ⟨y, hy, hxy⟩ := exists_ne_zero_of_form h.nondeg h.span_form hx0'
  apply hxy
  have e := congrArg Subtype.val (hx ⟨y, hy⟩)
  rw [coe_polar_formQ, h.polar_eq] at e
  exact e

theorem resHom_mem_orthTransvSet (d : V ≃ₗ[F] V) (hd : d ∈ transvSet G₀) :
    resHom h.mapsTo ⟨d, hd.1⟩ ∈ orthTransvSet (formQ Q G₀) (formR Q G₀) := by
  obtain ⟨r, hr, hdr⟩ := h.exists_centre hd
  refine ⟨⟨r, Submodule.subset_span hr⟩, hr, fun x => Subtype.ext ?_⟩
  rw [coe_resHom_apply, hdr]
  simp only [Submodule.coe_add, Submodule.coe_smul, Subfield.smul_def, coe_polar_formQ]

omit h in
theorem exists_of_mem_orthTransvSet :
    ∀ φ ∈ orthTransvSet (formQ Q G₀) (formR Q G₀),
      ∃ d ∈ transvSet G₀, ∀ x : centreForm Q G₀, (φ x : V) = d x := by
  rintro φ ⟨r, ⟨-, d, hd, hdr⟩, hφ⟩
  refine ⟨d, hd, fun x => ?_⟩
  rw [hφ x, hdr]
  simp only [Submodule.coe_add, Submodule.coe_smul, Subfield.smul_def, coe_polar_formQ]

theorem isIrredOnV_formQ :
    IsIrredOnV (Subgroup.closure (orthTransvSet (formQ Q G₀) (formR Q G₀))) := by
  haveI := h.finite
  exact isIrredOnV_closure h.mapsTo h.alt h.nondeg h.val h.span_form
    h.resHom_mem_orthTransvSet h.irred

theorem not_isImprimitiveOnV_formQ (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) :
    ¬ IsImprimitiveOnV (Subgroup.closure (orthTransvSet (formQ Q G₀) (formR Q G₀))) := by
  haveI := h.finite
  exact not_isImprimitiveOnV_closure h.mapsTo h.alt h.nondeg h.val h.span_form
    h.resHom_mem_orthTransvSet hprim

theorem mem_closure_of_isometry (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀))
    (φ : centreForm Q G₀ ≃ₗ[centreField Q G₀] centreForm Q G₀)
    (hφ : ∀ x, formQ Q G₀ (φ x) = formQ Q G₀ x) :
    φ ∈ Subgroup.closure (orthTransvSet (formQ Q G₀) (formR Q G₀)) :=
  hORTH _ _ (formQ Q G₀) h.finrank_form' h.nondeg_formQ (formR Q G₀) formQ_eq_one
    eq_top_of_polar_mem h.isIrredOnV_formQ (h.not_isImprimitiveOnV_formQ hprim) φ hφ

theorem mem_transvGen_of_isometry (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀))
    {g : V ≃ₗ[F] V} (hgI : ∀ x ∈ centreForm Q G₀, g x ∈ centreForm Q G₀)
    (hgQ : ∀ x, Q (g x) = Q x) : g ∈ transvGen G₀ := by
  haveI := h.finite
  have hsurj : Function.Surjective
      (fun x : centreForm Q G₀ => (⟨g x, hgI x x.2⟩ : centreForm Q G₀)) :=
    Finite.surjective_of_injective fun x y hxy =>
      Subtype.ext (g.injective (congrArg Subtype.val hxy))
  have hgI' : ∀ x ∈ centreForm Q G₀, g⁻¹ x ∈ centreForm Q G₀ := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hy' : g y = x := congrArg Subtype.val hy
    rw [← hy', inv_mul_apply]
    exact y.2
  obtain ⟨g', hg', e⟩ := exists_of_mem_closure exists_of_mem_orthTransvSet
    (h.mem_closure_of_isometry hORTH hprim (restr g hgI hgI') fun x => Subtype.ext (hgQ x))
  have hgg' : g = g' := eq_of_eqOn_span h.span_form fun x hx => e ⟨x, hx⟩
  rw [hgg']
  exact hg'

theorem transvGen_eq (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) :
    transvGen G₀ = G₀ :=
  le_antisymm (transvGen_le G₀) fun g hg =>
    h.mem_transvGen_of_isometry hORTH hprim (h.mapsTo g hg) (h.isometry g hg)

theorem mem_iff (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀))
    (g : V ≃ₗ[F] V) :
    g ∈ G₀ ↔ g ∈ spGroup B ∧ (∀ x ∈ centreForm Q G₀, g x ∈ centreForm Q G₀) ∧
      ∀ x, Q (g x) = Q x :=
  ⟨fun hg => ⟨h.le_sp hg, h.mapsTo g hg, h.isometry g hg⟩,
    fun ⟨_, hgI, hgQ⟩ => transvGen_le G₀ (h.mem_transvGen_of_isometry hORTH hprim hgI hgQ)⟩

theorem range_resHom (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) :
    (resHom (F₀ := centreField Q G₀) h.mapsTo).range = orthGroup (formQ Q G₀) := by
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact mem_orthGroup.mpr fun x => Subtype.ext (h.isometry g g.2 x)
  · intro hφ
    obtain ⟨g', hg', e⟩ := exists_of_mem_closure exists_of_mem_orthTransvSet
      (h.mem_closure_of_isometry hORTH hprim φ (mem_orthGroup.mp hφ))
    exact ⟨⟨g', transvGen_le G₀ hg'⟩, LinearEquiv.ext fun x => Subtype.ext (e x).symm⟩

theorem nonempty_mulEquiv_orthGroup (hORTH : OrthIdent)
    (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) : Nonempty (G₀ ≃* orthGroup (formQ Q G₀)) :=
  ⟨(MonoidHom.ofInjective (resHom_injective h.span_form h.mapsTo)).trans
    (MulEquiv.subgroupCongr (h.range_resHom hORTH hprim))⟩

theorem isO4Type (hORTH : OrthIdent) (hprim : ¬ IsImprimitiveOnV (transvGen G₀)) {k : ℕ}
    (hk : 0 < k) (hK : Nat.card (centreField Q G₀) = 2 ^ k) : IsO4Type k G₀ := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_orthGroup hORTH hprim
  exact isO4Type_of_orthGroup (formQ Q G₀) h.finrank_form' h.nondeg_formQ hk hK e

end OrthHyp

end OrthA

open OrthA

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]

theorem case2_at_of_orth (hORTH : OrthIdent) {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hD : (transvSet G₀).Nonempty)
    (hirrG : IsIrredOnV (transvGen G₀)) (hprimG : ¬ IsImprimitiveOnV (transvGen G₀))
    (Q : QuadraticForm F V) (hQB : ∀ x y, QuadraticMap.polar Q x y = B x y)
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) {k : ℕ} (hK : Nat.card (centreField Q G₀) = 2 ^ k) :
    G41Case2AtExponent n k B G₀ := by
  have h : OrthHyp B G₀ Q := ⟨halt, hnd, hdim, hSp, hD, hirrG, hQB, hQ⟩
  obtain ⟨k', hk', hk'n, hK'⟩ := exists_card_subfield hn (centreField Q G₀)
  obtain rfl : k = k' := Nat.pow_right_injective le_rfl (hK.symm.trans hK')
  obtain ⟨b, hb, hbI⟩ := exists_sympBasis_form halt hnd h.val h.span_form hdim
  refine ⟨h.transvGen_eq hORTH hprimG, Q, b, centreField Q G₀, hQB, hb, hk', hk'n, hK,
    fun g => ?_, h.isO4Type hORTH hprimG hk' hK⟩
  rw [h.mem_iff hORTH hprimG, mem_subfieldSpOf_iff h.val b hb hbI]

theorem case2_of_orth (hORTH : OrthIdent) {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hD : (transvSet G₀).Nonempty)
    (hirrG : IsIrredOnV (transvGen G₀)) (hprimG : ¬ IsImprimitiveOnV (transvGen G₀))
    (Q : QuadraticForm F V) (hQB : ∀ x y, QuadraticMap.polar Q x y = B x y)
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) :
    ∃ k : ℕ, G41Case2AtExponent n k B G₀ := by
  obtain ⟨k, -, -, hK⟩ := exists_card_subfield hn (centreField Q G₀)
  exact ⟨k, case2_at_of_orth hORTH n hn B halt hnd hdim G₀ hSp hD hirrG hprimG Q hQB hQ hK⟩

end CFSG.Quasithin.SimsG4

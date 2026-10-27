module

import CFSG.GroupTheory.EquivariantPatch
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocalIso
import CFSG.OddTranspositions.PartThree.CommSetConj

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Fischer CFSG.GroupTheory

variable {G G' : Type} [Group G] [Group G']

abbrev Hloc (D : Set G) (u : G) : Subgroup G := Subgroup.closure (commSet D u)

@[expose, instance_reducible] def conjAction {D : Set G} (hS : Setup G D) : MulAction G D where
  smul g x := ⟨g * x * g⁻¹, hS.conj_mem g x.2⟩
  one_smul x := Subtype.ext (by
    change (1 : G) * (x : G) * (1 : G)⁻¹ = x
    simp)
  mul_smul g h x := Subtype.ext (by
    change (g * h) * (x : G) * (g * h)⁻¹ = g * (h * (x : G) * h⁻¹) * g⁻¹
    simp [mul_assoc])

@[expose] def baseSet (D : Set G) (u : G) : Set D := {x | (x : G) = u ∨ (x : G) ∈ commSet D u}

@[expose] def sliceSet (D : Set G) (u v : G) : Set D := {x | (x : G) ∈ patchSlice D u v}

open scoped Classical in
@[expose] noncomputable def LocalIso.restr {D : Set G} {u : G} {D' : Set G'} {u' : G'}
    (θ : LocalIso D u D' u') (c : D') (x : D) : D' :=
  if h : (x : G) ∈ commSet D u then ⟨θ.app x, (θ.app_mem_commSet h).1⟩ else c

theorem LocalIso.coe_restr_of_mem {D : Set G} {u : G} {D' : Set G'} {u' : G'}
    (θ : LocalIso D u D' u') (c : D') {x : D} (hx : (x : G) ∈ commSet D u) :
    ((θ.restr c x : D') : G') = θ.app x := by
  unfold LocalIso.restr
  rw [dif_pos hx]

theorem LocalIso.restr_of_not_mem {D : Set G} {u : G} {D' : Set G'} {u' : G'}
    (θ : LocalIso D u D' u') (c : D') {x : D} (hx : (x : G) ∉ commSet D u) :
    θ.restr c x = c := by
  unfold LocalIso.restr
  rw [dif_neg hx]

theorem LocalIso.app_conj {D : Set G} {u : G} {D' : Set G'} {u' : G'} (θ : LocalIso D u D' u')
    {g x : G} (hg : g ∈ Subgroup.closure (commSet D u)) (hx : x ∈ Subgroup.closure (commSet D u)) :
    θ.app (g * x * g⁻¹) = θ.app g * θ.app x * (θ.app g)⁻¹ := by
  rw [θ.app_mul (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg), θ.app_mul hg hx,
    θ.app_inv hg]

theorem conj_eq_iff_of_commute {h u s : G} (hc : Commute h u) : h * s * h⁻¹ = u ↔ s = u := by
  constructor
  · intro e
    have h1 : s = h⁻¹ * (h * s * h⁻¹) * h := by group
    rw [h1, e, hc.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  · rintro rfl
    simp [hc.eq]

theorem conj_mem_patchSlice {D : Set G} (hS : Setup G D) {u v r s : G} (hru : Commute r u)
    (hrv : Commute r v) (hs : s ∈ patchSlice D u v) : r * s * r⁻¹ ∈ patchSlice D u v := by
  refine ⟨conj_mem_commSet_of_commute hS.normal hrv hs.1, fun hc => hs.2 ?_⟩
  have hu : r * u * r⁻¹ = u := by rw [hru.eq, mul_inv_cancel_right]
  exact (Commute.conj_iff r).1 (by rw [hu]; exact hc)

theorem exists_translate_mem_patchSlice {D : Set G} (hS : Setup G D) {H : Subgroup G}
    {u v : G} (hv : v ∈ commSet D u) (hHu : ∀ h ∈ H, Commute h u)
    (hdiam : ∀ w ∈ D, ¬ Commute w u → (commSet D u ∩ commSet D w).Nonempty)
    (htrans : ∀ x ∈ commSet D u, ∀ y ∈ commSet D u, ∃ h ∈ H, h * x * h⁻¹ = y)
    {x : G} (hxD : x ∈ D) (hxu : x ≠ u) (hxn : x ∉ commSet D u) :
    ∃ h ∈ H, h * x * h⁻¹ ∈ patchSlice D u v := by
  have hnc : ¬ Commute x u := fun hc => hxn ⟨hxD, hc, hxu⟩
  obtain ⟨t, htu, htx⟩ := hdiam x hxD hnc
  obtain ⟨h, hh, hht⟩ := htrans t htu v hv
  have hhc : Commute h u := hHu h hh
  refine ⟨h, hh, ⟨hS.conj_mem h hxD, ?_, ?_⟩, ?_⟩
  · have hcm : Commute (h * x * h⁻¹) (h * t * h⁻¹) :=
      (conj_commute_iff h x t).2 htx.2.1.symm.eq
    rwa [hht] at hcm
  · intro e
    rw [← hht] at e
    have : x = t := conj_injective h e
    exact htx.2.2 this.symm
  · intro hc
    have hu : h * u * h⁻¹ = u := by rw [hhc.eq, mul_inv_cancel_right]
    exact hnc ((Commute.conj_iff h).1 (by rw [hu]; exact hc))

theorem exists_translate_mem_commSet {D : Set G} (hS : Setup G D) {H : Subgroup G}
    {u v : G} (hv : v ∈ commSet D u)
    (htrans : ∀ x ∈ commSet D u, ∀ y ∈ commSet D u, ∃ h ∈ H, h * x * h⁻¹ = y)
    (hcov : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Commute a b →
      (commSet D u ∩ commSet D a ∩ commSet D b).Nonempty)
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : Commute a b) :
    ∃ h ∈ H, h * a * h⁻¹ ∈ commSet D v ∧ h * b * h⁻¹ ∈ commSet D v := by
  obtain ⟨w, ⟨hwu, hwa⟩, hwb⟩ := hcov a ha b hb hab hc
  obtain ⟨h, hh, hhw⟩ := htrans w hwu v hv
  refine ⟨h, hh, ⟨hS.conj_mem h ha, ?_, ?_⟩, ⟨hS.conj_mem h hb, ?_, ?_⟩⟩
  · have hcm : Commute (h * a * h⁻¹) (h * w * h⁻¹) :=
      (conj_commute_iff h a w).2 hwa.2.1.symm.eq
    rwa [hhw] at hcm
  · intro e
    rw [← hhw] at e
    exact hwa.2.2 (conj_injective h e).symm
  · have hcm : Commute (h * b * h⁻¹) (h * w * h⁻¹) :=
      (conj_commute_iff h b w).2 hwb.2.1.symm.eq
    rwa [hhw] at hcm
  · intro e
    rw [← hhw] at e
    exact hwb.2.2 (conj_injective h e).symm


theorem LocalIso.coe_equiv_eq_app {D : Set G} {u : G} {D' : Set G'} {u' : G'}
    (θ : LocalIso D u D' u') (h : Hloc D u) :
    ((θ.toMulEquiv h : Hloc D' u') : G') = θ.app (h : G) :=
  (θ.app_of_mem h.2).symm

theorem LocalIso.exists_preimage_closure_inter {D : Set G} {D' : Set G'} {u v : G} {u' v' : G'}
    (θ : LocalIso D u D' u') (hv : v ∈ commSet D u) (hθv : θ.app v = v') {r : G'}
    (hr : r ∈ Subgroup.closure (commSet D' u' ∩ commSet D' v')) :
    ∃ r₀ ∈ Subgroup.closure (commSet D u ∩ commSet D v), θ.app r₀ = r := by
  have hvc : v ∈ Subgroup.closure (commSet D u) := Subgroup.subset_closure hv
  have hle : ∀ {r₀ : G}, r₀ ∈ Subgroup.closure (commSet D u ∩ commSet D v) →
      r₀ ∈ Subgroup.closure (commSet D u) := fun h => Subgroup.closure_mono Set.inter_subset_left h
  induction hr using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨y, hy, hyz⟩ := θ.exists_app_eq hz.1
    have hyv : y ∈ commSet D v := by
      refine ⟨hy.1, ?_, ?_⟩
      · have h1 : Commute (θ.app y) (θ.app v) := by
          rw [hyz, hθv]
          exact hz.2.2.1
        exact (θ.commute_iff (Subgroup.subset_closure hy) hvc).1 h1
      · intro e
        apply hz.2.2.2
        rw [← hyz, e, hθv]
    exact ⟨y, Subgroup.subset_closure ⟨hy, hyv⟩, hyz⟩
  | one => exact ⟨1, Subgroup.one_mem _, θ.app_one⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨a₀, ha₀, rfl⟩ := iha
    obtain ⟨b₀, hb₀, rfl⟩ := ihb
    exact ⟨a₀ * b₀, Subgroup.mul_mem _ ha₀ hb₀, θ.app_mul (hle ha₀) (hle hb₀)⟩
  | inv a _ iha =>
    obtain ⟨a₀, ha₀, rfl⟩ := iha
    exact ⟨a₀⁻¹, Subgroup.inv_mem _ ha₀, θ.app_inv (hle ha₀)⟩

theorem disjoint_sliceSet_baseSet (D : Set G) (u v : G) :
    Disjoint (sliceSet D u v) (baseSet D u) := by
  rw [Set.disjoint_left]
  intro x hxS hxB
  have hxS' : (x : G) ∈ patchSlice D u v := hxS
  rcases hxB with hxB | hxB
  · exact hxS'.2 (by simp [hxB])
  · exact hxS'.2 hxB.2.1

theorem exists_conj_eq_of_not_mem_baseSet {D : Set G} (hS : Setup G D) {H : Subgroup G}
    {u v : G} (hv : v ∈ commSet D u) (hHu : ∀ h ∈ H, Commute h u)
    (hdiam : ∀ w ∈ D, ¬ Commute w u → (commSet D u ∩ commSet D w).Nonempty)
    (htrans : ∀ x ∈ commSet D u, ∀ y ∈ commSet D u, ∃ h ∈ H, h * x * h⁻¹ = y)
    {x : D} (hx : x ∉ baseSet D u) :
    ∃ h : H, ∃ s ∈ sliceSet D u v, (h : G) * s * (h : G)⁻¹ = x := by
  have hxu : (x : G) ≠ u := fun e => hx (Or.inl e)
  have hxn : (x : G) ∉ commSet D u := fun e => hx (Or.inr e)
  obtain ⟨h, hh, hs⟩ := exists_translate_mem_patchSlice hS hv hHu hdiam htrans x.2 hxu hxn
  refine ⟨⟨h⁻¹, Subgroup.inv_mem _ hh⟩, ⟨h * x * h⁻¹, hS.conj_mem h x.2⟩, hs, ?_⟩
  show h⁻¹ * (h * (x : G) * h⁻¹) * h⁻¹⁻¹ = x
  group

theorem restr_bijOn_base {D : Set G} {D' : Set G'} {u : G} {u' : G'} (hu : u ∈ D) (hu' : u' ∈ D')
    (θ : LocalIso D u D' u') : Set.BijOn (θ.restr ⟨u', hu'⟩) (baseSet D u) (baseSet D' u') := by
  have hnu : ∀ x : D, (x : G) = u → (x : G) ∉ commSet D u := fun x hx h => h.2.2 hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [θ.restr_of_not_mem _ (hnu x hx)]
      exact Or.inl rfl
    · refine Or.inr ?_
      rw [θ.coe_restr_of_mem _ hx]
      exact θ.app_mem_commSet hx
  · intro x hx y hy hxy
    by_cases hxu : (x : G) ∈ commSet D u
    · by_cases hyu : (y : G) ∈ commSet D u
      · have h1 : ((θ.restr ⟨u', hu'⟩ x : D') : G') = ((θ.restr ⟨u', hu'⟩ y : D') : G') :=
          congrArg Subtype.val hxy
        rw [θ.coe_restr_of_mem _ hxu, θ.coe_restr_of_mem _ hyu] at h1
        exact Subtype.ext
          (θ.app_injOn (Subgroup.subset_closure hxu) (Subgroup.subset_closure hyu) h1)
      · exfalso
        rw [θ.restr_of_not_mem _ hyu] at hxy
        have h1 : ((θ.restr ⟨u', hu'⟩ x : D') : G') = u' := by rw [hxy]
        rw [θ.coe_restr_of_mem _ hxu] at h1
        exact (θ.app_mem_commSet hxu).2.2 h1
    · by_cases hyu : (y : G) ∈ commSet D u
      · exfalso
        rw [θ.restr_of_not_mem _ hxu] at hxy
        have h1 : ((θ.restr ⟨u', hu'⟩ y : D') : G') = u' := by rw [← hxy]
        rw [θ.coe_restr_of_mem _ hyu] at h1
        exact (θ.app_mem_commSet hyu).2.2 h1
      · exact Subtype.ext ((hx.resolve_right hxu).trans (hy.resolve_right hyu).symm)
  · intro z hz
    rcases hz with hz | hz
    · refine ⟨⟨u, hu⟩, Or.inl rfl, ?_⟩
      rw [θ.restr_of_not_mem _ (hnu ⟨u, hu⟩ rfl)]
      exact Subtype.ext hz.symm
    · obtain ⟨y, hy, hyz⟩ := θ.exists_app_eq hz
      refine ⟨⟨y, hy.1⟩, Or.inr hy, Subtype.ext ?_⟩
      rw [θ.coe_restr_of_mem _ hy]
      exact hyz

theorem restr_bijOn_slice {D : Set G} {D' : Set G'} {u v : G} {u' v' : G'} (hu : u ∈ commSet D v)
    (ψ : LocalIso D v D' v') (hψu : ψ.app u = u') (c : D') :
    Set.BijOn (ψ.restr c) (sliceSet D u v) (sliceSet D' u' v') := by
  have huc : u ∈ Subgroup.closure (commSet D v) := Subgroup.subset_closure hu
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxs : (x : G) ∈ patchSlice D u v := hx
    show ((ψ.restr c x : D') : G') ∈ patchSlice D' u' v'
    rw [ψ.coe_restr_of_mem c hxs.1]
    refine ⟨ψ.app_mem_commSet hxs.1, fun hc => hxs.2 ?_⟩
    rw [← hψu] at hc
    exact (ψ.commute_iff (Subgroup.subset_closure hxs.1) huc).1 hc
  · intro x hx y hy hxy
    have hxs : (x : G) ∈ patchSlice D u v := hx
    have hys : (y : G) ∈ patchSlice D u v := hy
    have h1 : ((ψ.restr c x : D') : G') = ((ψ.restr c y : D') : G') := congrArg Subtype.val hxy
    rw [ψ.coe_restr_of_mem c hxs.1, ψ.coe_restr_of_mem c hys.1] at h1
    exact Subtype.ext
      (ψ.app_injOn (Subgroup.subset_closure hxs.1) (Subgroup.subset_closure hys.1) h1)
  · intro z hz
    have hzs : (z : G') ∈ patchSlice D' u' v' := hz
    obtain ⟨y, hy, hyz⟩ := ψ.exists_app_eq hzs.1
    refine ⟨⟨y, hy.1⟩, ⟨hy, fun hc => hzs.2 ?_⟩, Subtype.ext ?_⟩
    · rw [← hyz, ← hψu]
      exact (ψ.commute_iff (Subgroup.subset_closure hy) huc).2 hc
    · rw [ψ.coe_restr_of_mem c hy]
      exact hyz


theorem exists_conj_equivariant_equiv_of_patch {D : Set G} {D' : Set G'}
    (hS : Setup G D) (hS' : Setup G' D') {H : Subgroup G} {H' : Subgroup G'} (θ : H ≃* H')
    {u v : G} {u' : G'} (hHu : ∀ h ∈ H, Commute h u)
    (R : Subgroup H) (hRv : ∀ r ∈ R, Commute (r : G) v) (f₀ ψ : D → D') {S' : Set D'}
    (hf₀ : Set.BijOn f₀ (baseSet D u) (baseSet D' u'))
    (hf₀θ : ∀ (h : H) (x : D), x ∈ baseSet D u →
      (f₀ ⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : G') =
        (θ h : G') * (f₀ x : G') * (θ h : G')⁻¹)
    (hψ : Set.BijOn ψ (sliceSet D u v) S') (hSB' : Disjoint S' (baseSet D' u'))
    (hψθ : ∀ r ∈ R, ∀ x ∈ sliceSet D u v,
      (ψ ⟨(r : G) * x * (r : G)⁻¹, hS.conj_mem r x.2⟩ : G') =
        (θ r : G') * (ψ x : G') * (θ r : G')⁻¹)
    (hcov : ∀ x : D, x ∉ baseSet D u →
      ∃ h : H, ∃ s ∈ sliceSet D u v, (h : G) * s * (h : G)⁻¹ = x)
    (hcov' : ∀ x : D', x ∉ baseSet D' u' →
      ∃ h : H', ∃ s ∈ S', (h : G') * s * (h : G')⁻¹ = x)
    (hstab : ∀ s ∈ sliceSet D u v, ∀ h : H,
      (h : G) * s * (h : G)⁻¹ = s ↔ (θ h : G') * (ψ s : G') * (θ h : G')⁻¹ = ψ s)
    (hfus : ∀ s ∈ sliceSet D u v, ∀ h : H,
      (⟨(h : G) * s * (h : G)⁻¹, hS.conj_mem h s.2⟩ : D) ∈ sliceSet D u v →
        ∃ r ∈ R, (r : G) * s * (r : G)⁻¹ = (h : G) * s * (h : G)⁻¹)
    (hfus' : ∀ s ∈ S', ∀ h : H',
      (⟨(h : G') * s * (h : G')⁻¹, hS'.conj_mem h s.2⟩ : D') ∈ S' →
        ∃ r ∈ R, (θ r : G') * s * (θ r : G')⁻¹ = (h : G') * s * (h : G')⁻¹) :
    ∃ F : D ≃ D', (∀ (h : H) (x : D),
        (F ⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : G') =
          (θ h : G') * (F x : G') * (θ h : G')⁻¹) ∧
      (∀ x ∈ baseSet D u, F x = f₀ x) ∧ ∀ s ∈ sliceSet D u v, F s = ψ s := by
  classical
  let : MulAction G D := conjAction hS
  let : MulAction G' D' := conjAction hS'
  have hc : ∀ (g : G) (x : D), ((g • x : D) : G) = g * x * g⁻¹ := fun g x => rfl
  have hc' : ∀ (g : G') (x : D'), ((g • x : D') : G') = g * x * g⁻¹ := fun g x => rfl
  have hsub : ∀ {K : Subgroup G} (h : K) (x : D),
      ((h • x : D) : G) = (h : G) * x * (h : G)⁻¹ := fun h x => hc (h : G) x
  have hsub' : ∀ {K : Subgroup G'} (h : K) (x : D'),
      ((h • x : D') : G') = (h : G') * x * (h : G')⁻¹ := fun h x => hc' (h : G') x
  have hB : ∀ h : H, ∀ x ∈ baseSet D u, h • x ∈ baseSet D u := by
    intro h x hx
    have hhc : Commute (h : G) u := hHu h h.2
    show ((h • x : D) : G) = u ∨ ((h • x : D) : G) ∈ commSet D u
    rw [hsub]
    rcases hx with hx | hx
    · left
      rw [hx]
      exact (conj_eq_iff_of_commute hhc).2 rfl
    · right
      exact conj_mem_commSet_of_commute hS.normal hhc hx
  have hf₀θ' : ∀ (h : H) (x : D), x ∈ baseSet D u → f₀ (h • x) = θ h • f₀ x :=
    fun h x hx => Subtype.ext (hf₀θ h x hx)
  have hSB := disjoint_sliceSet_baseSet D u v
  have hRS : ∀ r ∈ R, ∀ s ∈ sliceSet D u v, r • s ∈ sliceSet D u v := by
    intro r hr s hs
    show ((r • s : D) : G) ∈ patchSlice D u v
    rw [hsub]
    exact conj_mem_patchSlice hS (hHu (r : G) r.2) (hRv r hr) hs
  have hψθ' : ∀ r ∈ R, ∀ s ∈ sliceSet D u v, ψ (r • s) = θ r • ψ s :=
    fun r hr s hs => Subtype.ext (hψθ r hr s hs)
  have hcov_g : ∀ x : D, x ∉ baseSet D u →
      ∃ h : H, ∃ s ∈ sliceSet D u v, h • s = x := by
    intro x hx
    obtain ⟨h, s, hs, hhx⟩ := hcov x hx
    exact ⟨h, s, hs, Subtype.ext hhx⟩
  have hcov_g' : ∀ x : D', x ∉ baseSet D' u' → ∃ h : H', ∃ s ∈ S', h • s = x := by
    intro x hx
    obtain ⟨h, s, hs, hhx⟩ := hcov' x hx
    exact ⟨h, s, hs, Subtype.ext hhx⟩
  have hstab' : ∀ s ∈ sliceSet D u v,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s) := by
    intro s hs
    have hsl : (s : G) ∈ patchSlice D u v := hs
    have e : ∀ h : H, h • s = s ↔ θ h • ψ s = ψ s := by
      intro h
      have key : ((h • s : D) : G) = s ↔ ((θ h • ψ s : D') : G') = ((ψ s : D') : G') := by
        rw [hsub, hsub']
        exact hstab s hsl h
      exact ⟨fun h1 => Subtype.ext (key.1 (congrArg Subtype.val h1)),
        fun h1 => Subtype.ext (key.2 (congrArg Subtype.val h1))⟩
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact MulAction.mem_stabilizer_iff.2 ((e h).1 (MulAction.mem_stabilizer_iff.1 hh))
    · intro hy
      obtain ⟨h, rfl⟩ := θ.surjective y
      exact ⟨h, MulAction.mem_stabilizer_iff.2 ((e h).2 (MulAction.mem_stabilizer_iff.1 hy)), rfl⟩
  have hfus_g : ∀ s ∈ sliceSet D u v, ∀ h : H, h • s ∈ sliceSet D u v →
      ∃ r ∈ R, r • s = h • s := by
    intro s hs h hhs
    have hsl : (s : G) ∈ patchSlice D u v := hs
    have hhs' : (⟨(h : G) * s * (h : G)⁻¹, hS.conj_mem h s.2⟩ : D) ∈ sliceSet D u v := hhs
    obtain ⟨r, hr, hrs⟩ := hfus s hsl h hhs'
    exact ⟨r, hr, Subtype.ext hrs⟩
  have hfus_g' : ∀ s ∈ S', ∀ h : H', h • s ∈ S' →
      ∃ r ∈ R.map θ.toMonoidHom, r • s = h • s := by
    intro s hs h hhs
    have hhs' : (⟨(h : G') * s * (h : G')⁻¹, hS'.conj_mem h s.2⟩ : D') ∈ S' := hhs
    obtain ⟨r, hr, hrs⟩ := hfus' s hs h hhs'
    exact ⟨θ r, Subgroup.mem_map_of_mem θ.toMonoidHom hr, Subtype.ext hrs⟩
  obtain ⟨F, hFeq, hFB, hFS⟩ := exists_equivariant_equiv_of_patch θ R f₀ ψ
    (B := baseSet D u) (S := sliceSet D u v) (B' := baseSet D' u') (S' := S')
    hB hf₀ hf₀θ' hSB hSB' hψ hRS hψθ' hcov_g hcov_g' hstab' hfus_g hfus_g'
  exact ⟨F, fun h x => congrArg Subtype.val (hFeq h x), hFB, hFS⟩

theorem nonempty_commGraphIso_of_conj_equivariant {D : Set G} {D' : Set G'}
    (hS : Setup G D) (hS' : Setup G' D') {H : Subgroup G} {H' : Subgroup G'} (θ : H ≃* H')
    (F : D ≃ D')
    (hF : ∀ (h : H) (x : D),
      (F ⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : G') =
        (θ h : G') * (F x : G') * (θ h : G')⁻¹)
    (P : Set D) (hP : ∀ x ∈ P, ∀ y ∈ P, (commGraph D).Adj x y ↔ (commGraph D').Adj (F x) (F y))
    (hcov : ∀ x y : D, (commGraph D).Adj x y → ∃ h : H,
      (⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : D) ∈ P ∧
        (⟨(h : G) * y * (h : G)⁻¹, hS.conj_mem h y.2⟩ : D) ∈ P)
    (hcov' : ∀ x y : D', (commGraph D').Adj x y → ∃ h : H',
      (⟨(h : G') * x * (h : G')⁻¹, hS'.conj_mem h x.2⟩ : D') ∈ F '' P ∧
        (⟨(h : G') * y * (h : G')⁻¹, hS'.conj_mem h y.2⟩ : D') ∈ F '' P) :
    Nonempty (commGraph D' ≃g commGraph D) := by
  classical
  let : MulAction G D := conjAction hS
  let : MulAction G' D' := conjAction hS'
  have hc : ∀ (g : G) (x : D), ((g • x : D) : G) = g * x * g⁻¹ := fun g x => rfl
  have hc' : ∀ (g : G') (x : D'), ((g • x : D') : G') = g * x * g⁻¹ := fun g x => rfl
  have hsub : ∀ {K : Subgroup G} (h : K) (x : D),
      ((h • x : D) : G) = (h : G) * x * (h : G)⁻¹ := fun h x => hc (h : G) x
  have hsub' : ∀ {K : Subgroup G'} (h : K) (x : D'),
      ((h • x : D') : G') = (h : G') * x * (h : G')⁻¹ := fun h x => hc' (h : G') x
  have hF' : ∀ (h : H) (x : D), F (h • x) = θ h • F x := fun h x => Subtype.ext (hF h x)
  have hΓ : ∀ (h : H) (x y : D), (commGraph D).Adj x y →
      (commGraph D).Adj (h • x) (h • y) := by
    intro h x y hxy
    rw [commGraph_adj_iff] at hxy ⊢
    rw [hsub, hsub]
    exact ⟨fun e => hxy.1 (conj_injective (h : G) e), (conj_commute_iff (h : G) x y).2 hxy.2⟩
  have hΓ' : ∀ (h : H') (x y : D'), (commGraph D').Adj x y →
      (commGraph D').Adj (h • x) (h • y) := by
    intro h x y hxy
    rw [commGraph_adj_iff] at hxy ⊢
    rw [hsub', hsub']
    exact ⟨fun e => hxy.1 (conj_injective (h : G') e), (conj_commute_iff (h : G') x y).2 hxy.2⟩
  have hcov_g : ∀ x y : D, (commGraph D).Adj x y → ∃ h : H, h • x ∈ P ∧ h • y ∈ P := by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hcov x y hxy
    exact ⟨h, hx, hy⟩
  have hcov_g' : ∀ x y : D', (commGraph D').Adj x y →
      ∃ h : H', h • x ∈ F '' P ∧ h • y ∈ F '' P := by
    intro x y hxy
    obtain ⟨h, hx, hy⟩ := hcov' x y hxy
    exact ⟨h, hx, hy⟩
  have hadj := adj_iff_of_equivariant_of_patch θ F hF' (commGraph D) (commGraph D') hΓ hΓ' P hP
    hcov_g hcov_g'
  exact ⟨{ toEquiv := F.symm
           map_rel_iff' := fun {a b} => by
             have h0 := hadj (F.symm a) (F.symm b)
             simpa using h0 }⟩

theorem nonempty_commGraphIso_of_patch {D : Set G} {D' : Set G'}
    (hS : Setup G D) (hS' : Setup G' D') {u : G} {u' : G'} (hu : u ∈ D) (hu' : u' ∈ D')
    (θ : LocalIso D u D' u') {v : G} {v' : G'} (hv : v ∈ commSet D u) (hv' : v' ∈ commSet D' u')
    (hθv : θ.app v = v') (ψ : LocalIso D v D' v') (hψu : ψ.app u = u')
    (hψθ : ∀ y ∈ Subgroup.closure (commSet D u ∩ commSet D v), ψ.app y = θ.app y)
    (hdiam : ∀ w ∈ D, ¬ Commute w u → (commSet D u ∩ commSet D w).Nonempty)
    (hdiam' : ∀ w ∈ D', ¬ Commute w u' → (commSet D' u' ∩ commSet D' w).Nonempty)
    (htrans : ∀ x ∈ commSet D u, ∀ y ∈ commSet D u,
      ∃ h ∈ Subgroup.closure (commSet D u), h * x * h⁻¹ = y)
    (htrans' : ∀ x ∈ commSet D' u', ∀ y ∈ commSet D' u',
      ∃ h ∈ Subgroup.closure (commSet D' u'), h * x * h⁻¹ = y)
    (hfus : ∀ s ∈ patchSlice D u v, ∀ h ∈ Subgroup.closure (commSet D u),
      h * s * h⁻¹ ∈ patchSlice D u v →
        ∃ r ∈ Subgroup.closure (commSet D u ∩ commSet D v), r * s * r⁻¹ = h * s * h⁻¹)
    (hfus' : ∀ s ∈ patchSlice D' u' v', ∀ h ∈ Subgroup.closure (commSet D' u'),
      h * s * h⁻¹ ∈ patchSlice D' u' v' →
        ∃ r ∈ Subgroup.closure (commSet D' u' ∩ commSet D' v'), r * s * r⁻¹ = h * s * h⁻¹)
    (hstab : ∀ s ∈ patchSlice D u v, ∀ h ∈ Subgroup.closure (commSet D u),
      (h * s * h⁻¹ = s ↔ θ.app h * ψ.app s * (θ.app h)⁻¹ = ψ.app s))
    (hcov : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Commute a b →
      (commSet D u ∩ commSet D a ∩ commSet D b).Nonempty)
    (hcov' : ∀ a ∈ D', ∀ b ∈ D', a ≠ b → Commute a b →
      (commSet D' u' ∩ commSet D' a ∩ commSet D' b).Nonempty) :
    Nonempty (commGraph D' ≃g commGraph D) := by
  classical
  let : MulAction G D := conjAction hS
  let : MulAction G' D' := conjAction hS'
  have hc : ∀ (g : G) (x : D), ((g • x : D) : G) = g * x * g⁻¹ := fun g x => rfl
  have hc' : ∀ (g : G') (x : D'), ((g • x : D') : G') = g * x * g⁻¹ := fun g x => rfl
  have hsub : ∀ {K : Subgroup G} (h : K) (x : D),
      ((h • x : D) : G) = (h : G) * x * (h : G)⁻¹ := fun h x => hc (h : G) x
  have hsub' : ∀ {K : Subgroup G'} (h : K) (x : D'),
      ((h • x : D') : G') = (h : G') * x * (h : G')⁻¹ := fun h x => hc' (h : G') x
  have hu_v : u ∈ commSet D v := mem_commSet_symm hu hv
  have hR_le : ∀ {r : G}, r ∈ Subgroup.closure (commSet D u ∩ commSet D v) →
      r ∈ Subgroup.closure (commSet D u) := fun hr => Subgroup.closure_mono Set.inter_subset_left hr
  have hR_le' : ∀ {r : G}, r ∈ Subgroup.closure (commSet D u ∩ commSet D v) →
      r ∈ Subgroup.closure (commSet D v) :=
        fun hr => Subgroup.closure_mono Set.inter_subset_right hr
  let c : D' := ⟨u', hu'⟩
  let R : Subgroup (Hloc D u) :=
    (Subgroup.closure (commSet D u ∩ commSet D v)).subgroupOf (Hloc D u)
  let θH : Hloc D u ≃* Hloc D' u' := θ.toMulEquiv
  have hHu : ∀ h ∈ Hloc D u, Commute h u := fun h hh => OddLocal.commute_of_mem_closure_commSet hh
  have hHu' : ∀ h ∈ Hloc D' u', Commute h u' :=
    fun h hh => OddLocal.commute_of_mem_closure_commSet hh
  have hRv : ∀ r ∈ R, Commute (r : G) v := fun r hr =>
    OddLocal.commute_of_mem_closure_commSet
      (Subgroup.closure_mono Set.inter_subset_right (Subgroup.mem_subgroupOf.1 hr))
  have hf₀ : Set.BijOn (θ.restr c) (baseSet D u) (baseSet D' u') := restr_bijOn_base hu hu' θ
  have hf₀θ : ∀ (h : Hloc D u) (x : D), x ∈ baseSet D u →
      (θ.restr c ⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : G') =
        (θH h : G') * (θ.restr c x : G') * (θH h : G')⁻¹ := by
    intro h x hx
    have hhc : Commute (h : G) u := hHu h h.2
    have hhc' : Commute ((θH h : Hloc D' u') : G') u' := hHu' (θH h) (θH h).2
    have h0 : θ.restr c (h • x) = θH h • θ.restr c x := by
      apply Subtype.ext
      rcases hx with hx | hx
      · have hxn : (x : G) ∉ commSet D u := fun e => e.2.2 hx
        have hhx : ((h • x : D) : G) = u := by
          rw [hsub, hx]
          exact (conj_eq_iff_of_commute hhc).2 rfl
        have hhxn : ((h • x : D) : G) ∉ commSet D u := fun e => e.2.2 hhx
        rw [θ.restr_of_not_mem c hhxn, hsub', θ.restr_of_not_mem c hxn]
        exact ((conj_eq_iff_of_commute hhc').2 rfl).symm
      · have hhx : ((h • x : D) : G) ∈ commSet D u := by
          rw [hsub]
          exact conj_mem_commSet_of_commute hS.normal hhc hx
        rw [θ.coe_restr_of_mem c hhx, hsub, hsub', θ.coe_restr_of_mem c hx, θ.coe_equiv_eq_app]
        exact θ.app_conj h.2 (Subgroup.subset_closure hx)
    exact congrArg Subtype.val h0
  have hψ : Set.BijOn (ψ.restr c) (sliceSet D u v) (sliceSet D' u' v') :=
    restr_bijOn_slice hu_v ψ hψu c
  have hψθ_ : ∀ r ∈ R, ∀ s ∈ sliceSet D u v,
      (ψ.restr c ⟨(r : G) * s * (r : G)⁻¹, hS.conj_mem r s.2⟩ : G') =
        (θH r : G') * (ψ.restr c s : G') * (θH r : G')⁻¹ := by
    intro r hr s hs
    have hr' : (r : G) ∈ Subgroup.closure (commSet D u ∩ commSet D v) :=
      Subgroup.mem_subgroupOf.1 hr
    have hsl : (s : G) ∈ patchSlice D u v := hs
    have hrs : ((r • s : D) : G) ∈ patchSlice D u v := by
      rw [hsub]
      exact conj_mem_patchSlice hS (hHu (r : G) r.2) (hRv r hr) hsl
    have h0 : ψ.restr c (r • s) = θH r • ψ.restr c s := by
      apply Subtype.ext
      rw [ψ.coe_restr_of_mem c hrs.1, hsub, hsub', ψ.coe_restr_of_mem c hsl.1, θ.coe_equiv_eq_app,
        ψ.app_conj (hR_le' hr') (Subgroup.subset_closure hsl.1), hψθ _ hr']
    exact congrArg Subtype.val h0
  have hcov_ := fun x (hx : x ∉ baseSet D u) =>
    exists_conj_eq_of_not_mem_baseSet hS hv hHu hdiam htrans hx
  have hcov'_ := fun x (hx : x ∉ baseSet D' u') =>
    exists_conj_eq_of_not_mem_baseSet hS' hv' hHu' hdiam' htrans' hx
  have hstab_ : ∀ s ∈ sliceSet D u v, ∀ h : Hloc D u,
      (h : G) * s * (h : G)⁻¹ = s ↔
        (θH h : G') * (ψ.restr c s : G') * (θH h : G')⁻¹ = ψ.restr c s := by
    intro s hs h
    have hsl : (s : G) ∈ patchSlice D u v := hs
    rw [θ.coe_equiv_eq_app, ψ.coe_restr_of_mem c hsl.1]
    exact hstab s hsl h h.2
  have hfus_ : ∀ s ∈ sliceSet D u v, ∀ h : Hloc D u,
      (⟨(h : G) * s * (h : G)⁻¹, hS.conj_mem h s.2⟩ : D) ∈ sliceSet D u v →
        ∃ r ∈ R, (r : G) * s * (r : G)⁻¹ = (h : G) * s * (h : G)⁻¹ := by
    intro s hs h hhs
    have hsl : (s : G) ∈ patchSlice D u v := hs
    have hhs' : (h : G) * s * (h : G)⁻¹ ∈ patchSlice D u v := hhs
    obtain ⟨r, hr, hrs⟩ := hfus s hsl h h.2 hhs'
    exact ⟨⟨r, hR_le hr⟩, Subgroup.mem_subgroupOf.2 hr, hrs⟩
  have hfus'_ : ∀ s ∈ sliceSet D' u' v', ∀ h : Hloc D' u',
      (⟨(h : G') * s * (h : G')⁻¹, hS'.conj_mem h s.2⟩ : D') ∈ sliceSet D' u' v' →
        ∃ r ∈ R, (θH r : G') * s * (θH r : G')⁻¹ = (h : G') * s * (h : G')⁻¹ := by
    intro s hs h hhs
    have hsl : (s : G') ∈ patchSlice D' u' v' := hs
    have hhs' : (h : G') * s * (h : G')⁻¹ ∈ patchSlice D' u' v' := hhs
    obtain ⟨r, hr, hrs⟩ := hfus' s hsl h h.2 hhs'
    obtain ⟨r₀, hr₀, hθr₀⟩ := θ.exists_preimage_closure_inter hv hθv hr
    have hr₀H : r₀ ∈ Subgroup.closure (commSet D u) := hR_le hr₀
    have hmem : (⟨r₀, hr₀H⟩ : Hloc D u) ∈ R := Subgroup.mem_subgroupOf.2 hr₀
    have hθ : ((θH ⟨r₀, hr₀H⟩ : Hloc D' u') : G') = r := by
      rw [θ.coe_equiv_eq_app]
      exact hθr₀
    exact ⟨⟨r₀, hr₀H⟩, hmem, by rw [hθ]; exact hrs⟩
  obtain ⟨F, hFeq, hFB, hFS⟩ := exists_conj_equivariant_equiv_of_patch hS hS' θH hHu R hRv
    (θ.restr c) (ψ.restr c) (S' := sliceSet D' u' v') hf₀ hf₀θ hψ
    (disjoint_sliceSet_baseSet D' u' v') hψθ_ hcov_ hcov'_ hstab_ hfus_ hfus'_
  have hFP : ∀ x : D, (x : G) ∈ commSet D v → F x = ψ.restr c x := by
    intro x hx
    by_cases hxu : Commute (x : G) u
    · have hxB : x ∈ baseSet D u := by
        by_cases hxe : (x : G) = u
        · exact Or.inl hxe
        · exact Or.inr ⟨x.2, hxu, hxe⟩
      rw [hFB x hxB]
      by_cases hxe : (x : G) = u
      · have h1 : (x : G) ∉ commSet D u := fun h => h.2.2 hxe
        rw [θ.restr_of_not_mem c h1]
        apply Subtype.ext
        rw [ψ.coe_restr_of_mem c hx, hxe, hψu]
      · have hxD : (x : G) ∈ commSet D u := ⟨x.2, hxu, hxe⟩
        apply Subtype.ext
        rw [θ.coe_restr_of_mem c hxD, ψ.coe_restr_of_mem c hx]
        exact (hψθ _ (Subgroup.subset_closure ⟨hxD, hx⟩)).symm
    · exact hFS x ⟨hx, hxu⟩
  let P : Set D := {x | (x : G) ∈ commSet D v}
  have hP : ∀ x ∈ P, ∀ y ∈ P, (commGraph D).Adj x y ↔ (commGraph D').Adj (F x) (F y) := by
    intro x hx y hy
    have hx' : (x : G) ∈ commSet D v := hx
    have hy' : (y : G) ∈ commSet D v := hy
    rw [hFP x hx', hFP y hy']
    have hxc : (x : G) ∈ Subgroup.closure (commSet D v) := Subgroup.subset_closure hx'
    have hyc : (y : G) ∈ Subgroup.closure (commSet D v) := Subgroup.subset_closure hy'
    rw [commGraph_adj_iff, commGraph_adj_iff]
    rw [ψ.coe_restr_of_mem c hx', ψ.coe_restr_of_mem c hy']
    constructor
    · rintro ⟨hne, hcm⟩
      exact ⟨fun h => hne (ψ.app_injOn hxc hyc h), (ψ.commute_iff hxc hyc).2 hcm⟩
    · rintro ⟨hne, hcm⟩
      exact ⟨fun h => hne (by rw [h]), (ψ.commute_iff hxc hyc).1 hcm⟩
  have hcovP : ∀ x y : D, (commGraph D).Adj x y → ∃ h : Hloc D u,
      (⟨(h : G) * x * (h : G)⁻¹, hS.conj_mem h x.2⟩ : D) ∈ P ∧
        (⟨(h : G) * y * (h : G)⁻¹, hS.conj_mem h y.2⟩ : D) ∈ P := by
    intro x y hxy
    rw [commGraph_adj_iff] at hxy
    obtain ⟨h, hh, h1, h2⟩ :=
      exists_translate_mem_commSet hS hv htrans hcov x.2 y.2 hxy.1 hxy.2
    exact ⟨⟨h, hh⟩, h1, h2⟩
  have hcovP' : ∀ x y : D', (commGraph D').Adj x y → ∃ h : Hloc D' u',
      (⟨(h : G') * x * (h : G')⁻¹, hS'.conj_mem h x.2⟩ : D') ∈ F '' P ∧
        (⟨(h : G') * y * (h : G')⁻¹, hS'.conj_mem h y.2⟩ : D') ∈ F '' P := by
    intro x y hxy
    rw [commGraph_adj_iff] at hxy
    obtain ⟨h, hh, h1, h2⟩ :=
      exists_translate_mem_commSet hS' hv' htrans' hcov' x.2 y.2 hxy.1 hxy.2
    have hmem : ∀ z : D', (z : G') ∈ commSet D' v' → z ∈ F '' P := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := ψ.exists_app_eq hz
      refine ⟨⟨w, hw.1⟩, hw, ?_⟩
      rw [hFP ⟨w, hw.1⟩ hw]
      apply Subtype.ext
      rw [ψ.coe_restr_of_mem c hw]
      exact hwz
    exact ⟨⟨h, hh⟩, hmem _ h1, hmem _ h2⟩
  exact nonempty_commGraphIso_of_conj_equivariant hS hS' θH F hFeq P hP hcovP hcovP'

end CFSG.OddTranspositions.PartThree

end

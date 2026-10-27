module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedLieTag StatedClassicalModel)

private theorem map_le_normalizer_iff {G H : Type} [Group G] [Group H]
    (e : G →* H) (he : Function.Injective e) (E C : Subgroup G) :
    E.map e ≤ Subgroup.normalizer (C.map e : Set H) ↔
      E ≤ Subgroup.normalizer (C : Set G) := by
  constructor
  · intro h
    have h' : E ≤ (Subgroup.normalizer (C.map e : Set H)).comap e :=
      Subgroup.map_le_iff_le_comap.mp h
    rwa [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range e C),
      Subgroup.comap_map_eq_self_of_injective he] at h'
  · intro h
    exact (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map e)

private theorem largeEvenInduces_map_iff {G H : Type} [Group G] [Group H]
    (e : G →* H) (he : Function.Injective e) (E C : Subgroup G)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θX : ↥C ⧸ Subgroup.center ↥C ≃* R)
    (θH : ↥(C.map e) ⧸ Subgroup.center ↥(C.map e) ≃* R)
    (hθ : ∀ l : ↥C, θX (QuotientGroup.mk l) =
      θH (QuotientGroup.mk (C.equivMapOfInjective e he l))) :
    (∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θX
      (fun l l' : ↥C => (l' : G) = ε⁻¹ * l * ε) φ) ↔
    (∀ ε' ∈ E.map e, ∃ φ ∈ I, LargeEvenInduces θH
      (fun l l' : ↥(C.map e) => (l' : H) = ε'⁻¹ * l * ε') φ) := by
  let φc := C.equivMapOfInjective e he
  constructor
  · intro h ε' hε'
    obtain ⟨ε, hε, rfl⟩ := hε'
    obtain ⟨φ, hφ, hind⟩ := h ε hε
    refine ⟨φ, hφ, fun u u' hrel => ?_⟩
    have hrel' : ((φc.symm u' : ↥C) : G) = ε⁻¹ * (φc.symm u : ↥C) * ε := by
      apply he
      have h1 : e ((φc.symm u' : ↥C) : G) = (u' : H) := by
        have h := Subgroup.coe_equivMapOfInjective_apply C e he (φc.symm u')
        rw [MulEquiv.apply_symm_apply] at h
        exact h.symm
      have h2 : e ((φc.symm u : ↥C) : G) = (u : H) := by
        have h := Subgroup.coe_equivMapOfInjective_apply C e he (φc.symm u)
        rw [MulEquiv.apply_symm_apply] at h
        exact h.symm
      simp only [map_mul, map_inv]
      rw [h1, h2]
      exact hrel
    have h := hind (φc.symm u) (φc.symm u') hrel'
    simpa only [hθ, φc, MulEquiv.apply_symm_apply] using h
  · intro h ε hε
    obtain ⟨φ, hφ, hind⟩ := h (e ε) (Subgroup.mem_map_of_mem e hε)
    refine ⟨φ, hφ, fun l l' hrel => ?_⟩
    have hrel' : ((φc l' : ↥(C.map e)) : H) = (e ε)⁻¹ * (φc l) * (e ε) := by
      rw [Subgroup.coe_equivMapOfInjective_apply C e he l',
        Subgroup.coe_equivMapOfInjective_apply C e he l]
      simpa using congrArg e hrel
    have h := hind (φc l) (φc l') hrel'
    simpa only [← hθ, φc] using h

theorem ggE0Concl_map_iff {G H : Type} [Group G] [Group H] (e : G →* H)
    (he : Function.Injective e) (E₀ C₀ : Subgroup G) :
    GGE0Concl (E₀.map e) (C₀.map e) ↔ GGE0Concl E₀ C₀ := by
  let φc := C₀.equivMapOfInjective e he
  have hnorm := map_le_normalizer_iff e he E₀ C₀
  constructor
  · intro h
    refine ⟨hnorm.mp h.1, fun hm => ?_⟩
    have hm' : LargeEvenMarking ↥(C₀.map e) (fun _ _ _ _ _ _ => True) :=
      largeEvenMarking_congr φc.symm (fun _ _ _ _ _ _ _ => trivial) hm
    have hH := h.2 hm'
    refine largeEvenMarking_congr φc ?_ hH
    intro lab R _ I _ θ hθ
    exact ⟨hθ.1, (largeEvenInduces_map_iff e he E₀ C₀ ((centerQuotCongr φc).trans θ) θ
      (fun l => by rw [MulEquiv.trans_apply, centerQuotCongr_mk])).2 hθ.2⟩
  · intro h
    refine ⟨hnorm.mpr h.1, fun hm => ?_⟩
    have hm' : LargeEvenMarking ↥C₀ (fun _ _ _ _ _ _ => True) :=
      largeEvenMarking_congr φc (fun _ _ _ _ _ _ _ => trivial) hm
    have hG := h.2 hm'
    refine largeEvenMarking_congr φc.symm ?_ hG
    intro lab R _ I _ θ hθ
    refine ⟨hθ.1, (largeEvenInduces_map_iff e he E₀ C₀ θ
      ((centerQuotCongr φc.symm).trans θ) ?_).1 hθ.2⟩
    intro l
    rw [MulEquiv.trans_apply, centerQuotCongr_mk]
    simp only [φc, MulEquiv.symm_apply_apply]

theorem ggE0Concl_of_mulEquiv {U V : Type} [Group U] [Group V] {H : Subgroup U} {M : Subgroup V}
    (e : ↥H ≃* ↥M) (hM : ∀ C : Subgroup V, IsComponentOf C M → GGE0Concl M C)
    {C₀ : Subgroup U} (hC₀ : IsComponentOf C₀ H) : GGE0Concl H C₀ := by
  obtain ⟨f, hf, hfM⟩ : ∃ f : ↥H →* V, Function.Injective f ∧ (⊤ : Subgroup ↥H).map f = M :=
    ⟨M.subtype.comp e.toMonoidHom, M.subtype_injective.comp e.injective, by
      rw [Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]⟩
  have hC₀H : (C₀.subgroupOf H).map H.subtype = C₀ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC₀.1]
  have hH : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hc : IsComponentOf (C₀.subgroupOf H) ⊤ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff H.subtype_injective, hC₀H, hH]
    exact hC₀
  have hcM : IsComponentOf ((C₀.subgroupOf H).map f) M := by
    rw [← hfM]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hf).2 hc
  have h₁ : GGE0Concl ((⊤ : Subgroup ↥H).map f) ((C₀.subgroupOf H).map f) := by
    rw [hfM]
    exact hM _ hcM
  have h₂ := (ggE0Concl_map_iff H.subtype H.subtype_injective ⊤ (C₀.subgroupOf H)).2
    ((ggE0Concl_map_iff f hf ⊤ (C₀.subgroupOf H)).1 h₁)
  rwa [hH, hC₀H] at h₂

theorem largeEvenMarking_of_isComponentOf_mulEquiv
    {U V : Type} [Group U] [Group V] {H : Subgroup U} {M : Subgroup V}
    (e : ↥H ≃* ↥M)
    (hM : ∀ C : Subgroup V, IsComponentOf C M →
      LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True))
    {C : Subgroup U} (hC : IsComponentOf C H) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  let f : ↥H →* V := M.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := M.subtype_injective.comp e.injective
  have hfM : (⊤ : Subgroup ↥H).map f = M := by
    rw [Subgroup.map_top, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCH : (C.subgroupOf H).map H.subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC.1]
  have hH : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hc : IsComponentOf (C.subgroupOf H) ⊤ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff H.subtype_injective,
      hCH, hH]
    exact hC
  have hcM : IsComponentOf ((C.subgroupOf H).map f) M := by
    rw [← hfM]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hf).2 hc
  let eC : ↥C ≃* ↥((C.subgroupOf H).map f) :=
    ((C.subgroupOf H).equivMapOfInjective H.subtype H.subtype_injective |>.trans
      (MulEquiv.subgroupCongr hCH)).symm.trans
        ((C.subgroupOf H).equivMapOfInjective f hf)
  exact largeEvenMarking_congr eC (fun _ _ _ _ _ _ _ => trivial) (hM _ hcM)

theorem ggE0Concl_inf_centralizer_of_injective {G U : Type} [Group G] [Group U] (ψ : U →* G)
    (hψ : Function.Injective ψ) {G₀ : Subgroup G} (hG₀ : ψ.range = G₀) (u : U)
    (hU : ∀ C : Subgroup U, IsComponentOf C (Subgroup.centralizer {u}) →
      GGE0Concl (Subgroup.centralizer {u}) C)
    {C₀ : Subgroup G} (hC₀ : IsComponentOf C₀ (G₀ ⊓ Subgroup.centralizer {ψ u})) :
    GGE0Concl (G₀ ⊓ Subgroup.centralizer {ψ u}) C₀ := by
  have hmap : (Subgroup.centralizer ({u} : Set U)).map ψ =
      G₀ ⊓ Subgroup.centralizer {ψ u} := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective ψ hψ ⊤ u
    rwa [top_inf_eq, ← MonoidHom.range_eq_map, hG₀] at h
  have hle : C₀ ≤ ψ.range :=
    hC₀.1.trans (hmap ▸ Subgroup.map_le_range ψ _)
  have hCeq : (C₀.comap ψ).map ψ = C₀ := Subgroup.map_comap_eq_self hle
  have hc : IsComponentOf (C₀.comap ψ) (Subgroup.centralizer {u}) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hψ, hCeq, hmap]
    exact hC₀
  have h := (ggE0Concl_map_iff ψ hψ _ _).2 (hU _ hc)
  rwa [hCeq, hmap] at h

theorem ggE0Concl_centralizer_of_mulEquiv {U V : Type} [Group U] [Group V] (e : U ≃* V) (u : U)
    (hV : ∀ C : Subgroup V, IsComponentOf C (Subgroup.centralizer {e u}) →
      GGE0Concl (Subgroup.centralizer {e u}) C)
    (C : Subgroup U) (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    GGE0Concl (Subgroup.centralizer {u}) C := by
  have hmap : (Subgroup.centralizer ({u} : Set U)).map e.toMonoidHom =
      Subgroup.centralizer {e u} := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ u
    rwa [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at h
  exact ggE0Concl_of_mulEquiv ((Subgroup.equivMapOfInjective _ _ e.injective).trans
    (MulEquiv.subgroupCongr hmap)) hV hC

theorem ggE0Concl_inf_centralizer_of_presents {G U : Type} [Group G] [Group U] (ψ : U →* G)
    (hker : ψ.ker ≤ Subgroup.center U) (hZ : Subgroup.center U = ⊥) {G₀ : Subgroup G}
    (hG₀ : ψ.range = G₀) {b : G} (hb : b ∈ G₀) (hodd : Odd (orderOf b))
    (hU : ∀ u : U, Odd (orderOf u) → ∀ C : Subgroup U,
      IsComponentOf C (Subgroup.centralizer {u}) → GGE0Concl (Subgroup.centralizer {u}) C)
    {C₀ : Subgroup G} (hC₀ : IsComponentOf C₀ (G₀ ⊓ Subgroup.centralizer {b})) :
    GGE0Concl (G₀ ⊓ Subgroup.centralizer {b}) C₀ := by
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  rw [← hG₀] at hb
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hb
  rw [orderOf_injective ψ hψ u] at hodd
  exact ggE0Concl_inf_centralizer_of_injective ψ hψ hG₀ u (hU u hodd) hC₀

private theorem conj_inv_centerQuot_mk {G : Type} [Group G] {C₀ : Subgroup G}
    {R : Type} [Group R] (θ : ↥C₀ ⧸ Subgroup.center ↥C₀ ≃* R) {c : G} (hc : c ∈ C₀)
    {l l' : ↥C₀} (h : (l' : G) = c⁻¹ * (l : G) * c) :
    (MulAut.conj (θ (⟨c, hc⟩ : ↥C₀)))⁻¹ (θ (QuotientGroup.mk l)) =
      θ (QuotientGroup.mk l') := by
  have hl' : (l' : ↥C₀) = ⟨c, hc⟩⁻¹ * l * ⟨c, hc⟩ := by
    apply Subtype.ext
    simpa using h
  rw [hl']
  have hmk : (QuotientGroup.mk (⟨c, hc⟩⁻¹ * l * ⟨c, hc⟩) :
        ↥C₀ ⧸ Subgroup.center ↥C₀) =
      (QuotientGroup.mk ⟨c, hc⟩)⁻¹ * QuotientGroup.mk l * QuotientGroup.mk ⟨c, hc⟩ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hmk, MulAut.conj_inv_apply, map_mul, map_mul, map_inv]

theorem ggE0Concl_of_inner {G : Type} [Group G] {E₀ C₀ : Subgroup G}
    (hinn : ∀ ε ∈ E₀, ∃ c ∈ C₀, ∀ l ∈ C₀, ε⁻¹ * l * ε = c⁻¹ * l * c)
    (hmark : LargeEvenMarking ↥C₀ fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) :
    GGE0Concl E₀ C₀ := by
  constructor
  · intro ε hε
    obtain ⟨c, hc, hcl⟩ := hinn ε⁻¹ (E₀.inv_mem hε)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hfun : ∀ l ∈ C₀, MulAut.conj ε l = MulAut.conj c⁻¹ l := by
      intro l hl
      rw [MulAut.conj_apply, MulAut.conj_apply]
      simpa using hcl (l : G) hl
    have hmap : C₀.map (MulAut.conj ε : G →* G) = C₀.map (MulAut.conj c⁻¹ : G →* G) := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, (hfun l hl).symm⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, hfun l hl⟩
    have hc₀ : C₀.map (MulAut.conj c⁻¹ : G →* G) = C₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (C₀.inv_mem hc))
    rw [hmap, hc₀]
  · intro hm
    refine largeEvenMarking_mono ?_ hmark
    intro lab R _ I _ θ hθ
    refine ⟨hθ.1, fun ε hε => ?_⟩
    obtain ⟨c, hc, hcl⟩ := hinn ε hε
    refine ⟨(MulAut.conj (θ (⟨c, hc⟩ : ↥C₀)))⁻¹,
      hθ.2 ⟨(θ (⟨c, hc⟩ : ↥C₀))⁻¹, map_inv MulAut.conj (θ (⟨c, hc⟩ : ↥C₀))⟩,
      fun l l' hrel => ?_⟩
    exact conj_inv_centerQuot_mk θ hc (hrel.trans (hcl (l : G) l.2))

theorem ggE0Concl_of_isQuasisimple {G : Type} [Group G] {M : Subgroup G}
    (hM : CFSG.Assembly.IsQuasisimple ↥M) {t : StatedLieTag} {n f : ℕ}
    (hmodel : StatedClassicalModel (↥M ⧸ Subgroup.center ↥M) t n 2 f) :
    ∀ C : Subgroup G, IsComponentOf C M → GGE0Concl M C := by
  intro C hC
  obtain rfl := GGHalf.eq_of_isComponentOf_isQuasisimple hM hC
  exact ggE0Concl_of_inner (fun ε hε => ⟨ε, hε, fun _ _ => rfl⟩)
    (largeEvenMarking_inn_of_statedClassicalModel hM hmodel)

theorem ggAutFixedSubgroup_mulAut_conj {H : Type*} [Group H] (s : H) :
    ggAutFixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set H) := by
  ext x
  rw [mem_ggAutFixedSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have hx := congrArg (fun z : H => z * s) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hx.symm
  · intro h
    calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [← h]
      _ = x := by group

theorem ggAutFixedSubgroup_inner_actor {H : Type*} [Group H]
    (hconj : Function.Injective (MulAut.conj : H →* MulAut H))
    {A : Subgroup (MulAut H)} (hA : (A : Set (MulAut H)) ⊆ LargeEvenInnSet H)
    {u : MulAut H} {s : H} (hs : MulAut.conj s = u)
    (hcomm : ∀ a ∈ A, Commute a u)
    (hdonor : ∀ C : Subgroup H, IsComponentOf C (ggAutFixedSubgroup u) →
      Subgroup.centralizer {s} ≤ Subgroup.normalizer (C : Set H) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ =>
        ∀ ε ∈ Subgroup.centralizer {s}, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C => (l' : H) = ε⁻¹ * l * ε) φ))
    {C : Subgroup H} (hC : IsComponentOf C (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ c ∈ C, a c ∈ C) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ => GGAutsInduceOn A C θ I) := by
  classical
  have hfix : ggAutFixedSubgroup u = Subgroup.centralizer ({s} : Set H) := by
    rw [← hs]
    exact ggAutFixedSubgroup_mulAut_conj s
  obtain ⟨hnorm, hmark⟩ := hdonor C hC
  have hnorm' : Subgroup.centralizer ({s} : Set H) ≤ Subgroup.normalizer (C : Set H) := hnorm
  have hconj_cent : ∀ t : H, MulAut.conj t ∈ A →
      t ∈ Subgroup.centralizer ({s} : Set H) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm' : (MulAut.conj t) * (MulAut.conj s) = (MulAut.conj s) * (MulAut.conj t) := by
      have h := hcomm (MulAut.conj t) ht
      simpa only [← hs] using h.eq
    have hmul : MulAut.conj (t * s) = MulAut.conj (s * t) := by
      calc MulAut.conj (t * s) = MulAut.conj t * MulAut.conj s := map_mul _ t s
        _ = MulAut.conj s * MulAut.conj t := hcomm'
        _ = MulAut.conj (s * t) := (map_mul _ s t).symm
    exact hconj hmul
  refine ⟨?_, ?_⟩
  · intro a ha c hc
    obtain ⟨t, rfl⟩ := hA ha
    have ht : t ∈ Subgroup.centralizer ({s} : Set H) := hconj_cent t ha
    have hmap : C.map (MulAut.conj t).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm' ht)
    have hmem : (MulAut.conj t) c ∈ C.map (MulAut.conj t).toMonoidHom := by
      simpa using Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hc
    rwa [hmap] at hmem
  · refine largeEvenMarking_mono (P' := fun _ _ _ I _ θ => GGAutsInduceOn A C θ I) ?_ hmark
    intro lab R _ I F θ hθ a ha
    obtain ⟨t, rfl⟩ := hA ha
    have ht : t ∈ Subgroup.centralizer ({s} : Set H) := hconj_cent t ha
    obtain ⟨φ, hφI, hind⟩ := hθ t⁻¹ ((Subgroup.centralizer {s}).inv_mem ht)
    refine ⟨φ, hφI, fun j j' hjj => hind j j' ?_⟩
    simpa [MulAut.conj_apply] using hjj.symm

end CFSG.StandardType

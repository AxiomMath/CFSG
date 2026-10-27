module

public import CFSG.RankThree.PartOne.LIT.McBasic
public import CFSG.RankThree.Classical.TransvectionGeneration

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical
  (IsTransvectionWith exists_mem_of_det_eq_one isCompl_span_pair_ker_inf_ker
    invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

private theorem exists_dual_one_of_notMem {W : Submodule (ZMod p) V} {x : V} (hx : x ∉ W) :
    ∃ f : Module.Dual (ZMod p) V, f x = 1 ∧ ∀ y ∈ W, f y = 0 := by
  obtain ⟨ψ, hψx, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(ψ x)⁻¹ • ψ, ?_, fun y hy => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψx]
  · have h : ψ y ∈ W.map ψ := Submodule.mem_map_of_mem hy
    rw [hψ, Submodule.mem_bot] at h
    rw [LinearMap.smul_apply, h, smul_zero]

private theorem finrank_span_pair_eq_two {v w : V} {f : Module.Dual (ZMod p) V} (hv : v ≠ 0)
    (hfv : f v = 0) (hfw : f w ≠ 0) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) {v, w}) = 2 := by
  have hli : LinearIndependent (ZMod p) ![v, w] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have hf := congrArg f hst
    rw [map_add, map_smul, map_smul, hfv, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
      map_zero] at hf
    have ht : t = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, ht⟩
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.pair_comm] at this
  exact this

theorem exists_partner
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {a : V} {f : Module.Dual (ZMod p) V} (ha : a ≠ 0) (hf : f ≠ 0) (h : TrIn H a f) :
    ∃ (b : V) (g φ : Module.Dual (ZMod p) V),
      TrIn H a φ ∧ TrIn H b g ∧ φ b ≠ 0 ∧ g a ≠ 0 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ : ∃ N : Submodule (ZMod p) V,
      ∀ x, x ∈ N ↔ ∀ φ, TrIn H a φ → φ x = 0 :=
    ⟨{ carrier := {x | ∀ φ, TrIn H a φ → φ x = 0}
       add_mem' := fun {x y} hx hy φ hφ => by rw [map_add, hx φ hφ, hy φ hφ, add_zero]
       zero_mem' := fun φ _ => map_zero φ
       smul_mem' := fun s x hx φ hφ => by rw [map_smul, hx φ hφ, smul_zero] },
     fun x => Iff.rfl⟩
  have haN : a ∈ N := (hN a).mpr fun φ hφ => hφ.1
  have hinv : ∀ t ∈ S, ∀ x ∈ N, t x ∈ N ∧ t⁻¹ x ∈ N := by
    intro t ht x hx
    obtain ⟨b, g, hbg⟩ := hS t ht
    have hTr : TrIn H b g := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure ht) hbg
    have hgx : g x • b ∈ N := by
      by_cases hb : b ∈ N
      · exact N.smul_mem _ hb
      · obtain ⟨φ, hφ, hφb⟩ : ∃ φ, TrIn H a φ ∧ φ b ≠ 0 := by
          by_contra hno
          push Not at hno
          exact hb ((hN b).mpr hno)
        have hga : g a = 0 := hcon b g φ hφ hTr hφb
        have h1 : TrIn H a (φ b • g) := TrIn.rule_R hφ hTr hga
        have h2 : TrIn H a g := by
          have := h1.smul (φ b)⁻¹
          rwa [smul_smul, inv_mul_cancel₀ hφb, one_smul] at this
        rw [(hN x).mp hx g h2, zero_smul]
        exact N.zero_mem
    refine ⟨?_, ?_⟩
    · rw [hbg.2.2.2 x]
      exact N.add_mem hx hgx
    · rw [hbg.inv_apply x]
      exact N.sub_mem hx hgx
  have hH : ∀ h ∈ H, ∀ x ∈ N, h x ∈ N := invariant_of_generators hHS hinv
  rcases hirr N hH with hbot | htop
  · rw [hbot, Submodule.mem_bot] at haN
    exact ha haN
  · apply hf
    ext x
    have hx : x ∈ N := by rw [htop]; trivial
    exact (hN x).mp hx f h

theorem isFrame_of_reciprocal [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = 4)
    {a b : V} {φ g : Module.Dual (ZMod p) V} (hφ : TrIn H a φ) (hg : TrIn H b g)
    (hφb : φ b ≠ 0) (hga : g a ≠ 0) :
    IsFrame H (Submodule.span (ZMod p) {a, b}) (LinearMap.ker φ ⊓ LinearMap.ker g) := by
  have ha : a ≠ 0 := fun h0 => hga (by rw [h0, map_zero])
  have hb : b ≠ 0 := fun h0 => hφb (by rw [h0, map_zero])
  have hφ0 : φ ≠ 0 := fun h0 => hφb (by rw [h0, LinearMap.zero_apply])
  have hg0 : g ≠ 0 := fun h0 => hga (by rw [h0, LinearMap.zero_apply])
  obtain ⟨t₁, ht₁, htx₁⟩ := hφ.2
  obtain ⟨t₂, ht₂, htx₂⟩ := hg.2
  have h₁ : IsTransvectionWith t₁ a φ := ⟨ha, hφ0, hφ.1, htx₁⟩
  have h₂ : IsTransvectionWith t₂ b g := ⟨hb, hg0, hg.1, htx₂⟩
  have hcompl : IsCompl (Submodule.span (ZMod p) {a, b}) (LinearMap.ker φ ⊓ LinearMap.ker g) :=
    isCompl_span_pair_ker_inf_ker hφ.1 hg.1 hφb hga
  have hU2 := finrank_span_pair_eq_two ha hφ.1 hφb
  have hL2 : Module.finrank (ZMod p) ↥(LinearMap.ker φ ⊓ LinearMap.ker g) = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  refine ⟨hcompl, hU2, hL2, fun c hcU f hfL hfc => ⟨hfc, ?_⟩⟩
  let ψ : Submodule.span (ZMod p) {a, b} →ₗ[ZMod p] Submodule.span (ZMod p) {a, b} :=
    LinearMap.transvection (f ∘ₗ (Submodule.span (ZMod p) {a, b}).subtype) ⟨c, hcU⟩
  have hψ : LinearMap.det ψ = 1 := by
    simp only [ψ, LinearMap.transvection.det, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hfc]; simp
  obtain ⟨h, hh, hhU, hhL⟩ := exists_mem_of_det_eq_one h₁ h₂ ht₁ ht₂ hφb hga ψ hψ
  refine ⟨h, hh, fun x => ?_⟩
  have hx : x ∈ Submodule.span (ZMod p) {a, b} ⊔ (LinearMap.ker φ ⊓ LinearMap.ker g) := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : h y₁ = y₁ + f y₁ • c := by
    have := hhU ⟨y₁, hy₁⟩
    rw [this]
    simp [ψ, LinearMap.transvection.apply]
  rw [map_add, h1, hhL y₂ hy₂, map_add, hfL y₂ hy₂]
  simp only [add_zero]
  abel

theorem exists_frame [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S) :
    ∃ U L : Submodule (ZMod p) V, IsFrame H U L := by
  obtain ⟨S, hS, hHS⟩ := hgen
  have hSne : S.Nonempty := by
    by_contra hS0
    rw [Set.not_nonempty_iff_eq_empty] at hS0
    have hH : H = ⊥ := by rw [hHS, hS0, Subgroup.closure_empty]
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hdim]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    rcases hirr (Submodule.span (ZMod p) {x}) (fun h hh y hy => by
        rw [hH, Subgroup.mem_bot] at hh
        rw [hh]
        exact hy) with h | h
    · exact hx (Submodule.span_singleton_eq_bot.mp h)
    · have := finrank_span_singleton (K := ZMod p) hx
      rw [h, finrank_top, hdim] at this
      omega
  obtain ⟨t, htS⟩ := hSne
  obtain ⟨v, f, hvf⟩ := hS t htS
  have hTr : TrIn H v f :=
    TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hvf
  obtain ⟨b, g, φ, hφ, hg, hφb, hgv⟩ := exists_partner H hirr ⟨S, hS, hHS⟩ hvf.1 hvf.2.1 hTr
  exact ⟨_, _, isFrame_of_reciprocal H hdim hφ hg hφb hgv⟩

namespace IsFrame

variable {H} {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)

@[expose] noncomputable def projU : V →ₗ[ZMod p] V :=
  U.projection L hF.1

@[expose] noncomputable def projL : V →ₗ[ZMod p] V :=
  L.projection U hF.1.symm

theorem projU_mem (x : V) : hF.projU x ∈ U :=
  Submodule.projection_apply_mem hF.1 x

theorem projL_mem (x : V) : hF.projL x ∈ L :=
  Submodule.projection_apply_mem hF.1.symm x

theorem projU_add_projL (x : V) : hF.projU x + hF.projL x = x :=
  Submodule.projection_add_projection_eq_self hF.1 x

theorem projU_of_mem {y : V} (hy : y ∈ U) : hF.projU y = y :=
  Submodule.projection_apply_of_mem_left hF.1 hy

theorem projU_of_mem_L {l : V} (hl : l ∈ L) : hF.projU l = 0 :=
  Submodule.projection_apply_of_mem_right hF.1 hl

theorem projL_of_mem {l : V} (hl : l ∈ L) : hF.projL l = l :=
  Submodule.projection_apply_of_mem_left hF.1.symm hl

theorem projL_of_mem_U {y : V} (hy : y ∈ U) : hF.projL y = 0 :=
  Submodule.projection_apply_of_mem_right hF.1.symm hy

include hF in
theorem trIn_center_of_vanish {u u' : V} (hu : u ∈ U) (hu' : u' ∈ U) (hu0 : u ≠ 0)
    {lam : Module.Dual (ZMod p) V} (hlam : ∀ y ∈ U, lam y = 0) (h : TrIn H u lam) :
    TrIn H u' lam := by
  by_cases hspan : u' ∈ Submodule.span (ZMod p) {u}
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hspan
    exact TrIn.smul_center_iff.mpr (h.smul s)
  have hc : u' - u ∈ U := U.sub_mem hu' hu
  have hnot : u ∉ L ⊔ Submodule.span (ZMod p) {u' - u} := by
    intro hmem
    obtain ⟨y, hyL, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hyU : y ∈ U := by
      have : y = u - s • (u' - u) := eq_sub_of_add_eq hyz
      rw [this]
      exact U.sub_mem hu (U.smul_mem s hc)
    have hy0 : y = 0 := Submodule.disjoint_def.mp hF.1.disjoint y hyU hyL
    rw [hy0, zero_add] at hyz
    by_cases hs : s = 0
    · rw [hs, zero_smul] at hyz
      exact hu0 hyz.symm
    · apply hspan
      refine Submodule.mem_span_singleton.mpr ⟨s⁻¹ * (1 + s), ?_⟩
      have h1 : s • u' = (1 + s) • u := by
        have h2 : s • (u' - u) = u := hyz
        rw [smul_sub] at h2
        rw [add_smul, one_smul]
        exact sub_eq_iff_eq_add.mp h2
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]
  obtain ⟨f, hfu, hfW⟩ := exists_dual_one_of_notMem hnot
  have hfL : ∀ l ∈ L, f l = 0 := fun l hl => hfW l (Submodule.mem_sup_left hl)
  have hfc : f (u' - u) = 0 :=
    hfW _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  obtain ⟨-, t, ht, htx⟩ := hF.2.2.2 (u' - u) hc f hfL hfc
  have htu : t u = u' := by
    rw [htx u, hfu, one_smul]
    abel
  have hinv : ∀ y, t.symm y = y - f y • (u' - u) := fun y => TrIn.inv_apply hfc htx y
  have hform : lam ∘ₗ t.symm.toLinearMap = lam := by
    ext y
    show lam (t.symm y) = lam y
    rw [hinv, map_sub, map_smul, hlam (u' - u) hc, smul_zero, sub_zero]
  have := h.conj ht
  rwa [htu, hform] at this

include hF in
theorem trIn_axis_of_vanish {l : V} (hl : l ∈ L) {φ φ' : Module.Dual (ZMod p) V}
    (hφ : ∀ y ∈ L, φ y = 0) (hφ' : ∀ y ∈ L, φ' y = 0) (hφ0 : φ ≠ 0) (h : TrIn H l φ) :
    TrIn H l φ' := by
  obtain ⟨c, hcU, hφc⟩ : ∃ c ∈ U, φ c ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hφ0
    ext x
    have hx : x ∈ U ⊔ L := by rw [hF.1.sup_eq_top]; trivial
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [LinearMap.zero_apply, map_add, hno y₁ hy₁, hφ y₂ hy₂, add_zero]
  obtain ⟨f, hfdef⟩ : ∃ f : Module.Dual (ZMod p) V, f = φ' - (φ' c / φ c) • φ := ⟨_, rfl⟩
  have hfL : ∀ y ∈ L, f y = 0 := fun y hy => by
    rw [hfdef, LinearMap.sub_apply, LinearMap.smul_apply, hφ y hy, hφ' y hy]
    simp
  have hfc : f c = 0 := by
    rw [hfdef, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hφc,
      sub_self]
  obtain ⟨-, t, ht, htx⟩ := hF.2.2.2 c hcU f hfL hfc
  have htl : t l = l := by rw [htx, hfL l hl, zero_smul, add_zero]
  have hinv : ∀ y, t.symm y = y - f y • c := fun y => TrIn.inv_apply hfc htx y
  have hform : φ ∘ₗ t.symm.toLinearMap = (1 + φ' c) • φ - φ c • φ' := by
    ext y
    show φ (t.symm y) = ((1 + φ' c) • φ - φ c • φ') y
    rw [hinv, map_sub, map_smul, hfdef]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    ring
  have h1 := h.conj ht
  rw [htl, hform] at h1
  have h2 : TrIn H l (φ c • φ') := by
    have := (h.smul (1 + φ' c)).sub h1
    rwa [sub_sub_cancel] at this
  have h3 := h2.smul (φ c)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hφc, one_smul] at h3

end IsFrame

theorem exists_ne_zero_ker_of_finrank_two {U : Submodule (ZMod p) V}
    (hU : Module.finrank (ZMod p) U = 2) (f : Module.Dual (ZMod p) V) :
    ∃ u ∈ U, u ≠ 0 ∧ f u = 0 := by
  have : Module.Finite (ZMod p) U := Module.finite_of_finrank_pos (by omega)
  have hker : LinearMap.ker (f ∘ₗ U.subtype) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [hU, Module.finrank_self]; omega)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨u, u.2, fun h0 => hu0 (Subtype.ext h0), ?_⟩
  simpa using hu

theorem eq_smul_of_vanish_on_plane {U : Submodule (ZMod p) V}
    (hU : Module.finrank (ZMod p) U = 2) {u : V} (hu : u ∈ U) (hu0 : u ≠ 0)
    {f f' : Module.Dual (ZMod p) V} (hf : f u = 0) (hf' : f' u = 0)
    (hf'0 : ∃ y ∈ U, f' y ≠ 0) : ∃ t : ZMod p, ∀ y ∈ U, f y = t * f' y := by
  obtain ⟨y₀, hy₀, hy₀ne⟩ := hf'0
  have : Module.Finite (ZMod p) U := Module.finite_of_finrank_pos (by omega)
  have hspan : Submodule.span (ZMod p) {u, y₀} = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair_eq_two hu0 hf' hy₀ne, hU])
    rw [Submodule.span_le]
    rintro x (rfl | hx)
    · exact hu
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hy₀
  refine ⟨f y₀ / f' y₀, fun y hy => ?_⟩
  rw [← hspan] at hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [map_add, map_smul, hf, hf', smul_eq_mul, mul_zero, zero_add]
  field_simp

end CFSG.RankThree.PartOne.LIT

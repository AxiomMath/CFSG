module

public import CFSG.RankThree.PartOne.LIT.McFrame

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

section Aux

variable {H : Subgroup (V ≃ₗ[ZMod p] V)} {U L : Submodule (ZMod p) V}
  {ψ : Module.Dual (ZMod p) V} {l₀ m : V}

private theorem exists_dual_one_of_notMem {W : Submodule (ZMod p) V} {x : V} (hx : x ∉ W) :
    ∃ f : Module.Dual (ZMod p) V, f x = 1 ∧ ∀ y ∈ W, f y = 0 := by
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(φ x)⁻¹ • φ, ?_, fun y hy => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφx]
  · have h : φ y ∈ W.map φ := Submodule.mem_map_of_mem hy
    rw [hφ, Submodule.mem_bot] at h
    rw [LinearMap.smul_apply, h, smul_zero]

private structure Pack (H : Subgroup (V ≃ₗ[ZMod p] V)) (U L : Submodule (ZMod p) V)
    (ψ : Module.Dual (ZMod p) V) (l₀ m : V) : Prop where
  frame : IsFrame H U L
  psiU : ∀ y ∈ U, ψ y = 0
  psi : ∀ u ∈ U, TrIn H u ψ
  mem_l₀ : l₀ ∈ L
  trIn_l₀ : ∀ φ : Module.Dual (ZMod p) V, (∀ y ∈ L, φ y = 0) → TrIn H l₀ φ
  ne_zero : ψ l₀ ≠ 0
  mem_m : m ∈ L
  m_ne_zero : m ≠ 0
  psi_m : ψ m = 0

private theorem Pack.eq_of_mem (P : Pack H U L ψ l₀ m) {f : Module.Dual (ZMod p) V}
    (hfm : f m = 0) {y : V} (hy : y ∈ L) : f y = f l₀ / ψ l₀ * ψ y := by
  obtain ⟨t, ht⟩ := eq_smul_of_vanish_on_plane P.frame.2.2.1 P.mem_m P.m_ne_zero hfm P.psi_m
    ⟨l₀, P.mem_l₀, P.ne_zero⟩
  rw [ht y hy, ht l₀ P.mem_l₀, mul_div_cancel_right₀ _ P.ne_zero]

private theorem Pack.decomp (P : Pack H U L ψ l₀ m) {f : Module.Dual (ZMod p) V} (hfm : f m = 0) :
    f = f ∘ₗ P.frame.projU + (f l₀ / ψ l₀) • ψ := by
  ext x
  have hx := P.frame.projU_add_projL x
  have h1 := P.eq_of_mem hfm (P.frame.projL_mem x)
  have hfx : f (P.frame.projU x) + f (P.frame.projL x) = f x := by rw [← map_add, hx]
  have hψx : ψ (P.frame.projU x) + ψ (P.frame.projL x) = ψ x := by rw [← map_add, hx]
  rw [P.psiU _ (P.frame.projU_mem x), zero_add] at hψx
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← hfx, ← hψx, h1]

private theorem Pack.m_notMem (P : Pack H U L ψ l₀ m) :
    m ∉ U ⊔ Submodule.span (ZMod p) {l₀} := by
  intro hm
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have huL : u ∈ L := by
    have : u = m - a • l₀ := eq_sub_of_add_eq huz
    rw [this]
    exact L.sub_mem P.mem_m (L.smul_mem a P.mem_l₀)
  have hu0 : u = 0 := Submodule.disjoint_def.mp P.frame.1.disjoint u hu huL
  rw [hu0, zero_add] at huz
  have h := congrArg ψ huz
  rw [map_smul, P.psi_m, smul_eq_mul] at h
  have ha : a = 0 := (mul_eq_zero.mp h).resolve_right P.ne_zero
  rw [ha, zero_smul] at huz
  exact P.m_ne_zero huz.symm

private theorem Pack.exists_eq_add (P : Pack H U L ψ l₀ m) {y : V} (hy : y ∈ L) :
    ∃ b : ZMod p, y = (ψ y / ψ l₀) • l₀ + b • m := by
  have hqL : y - (ψ y / ψ l₀) • l₀ ∈ L := L.sub_mem hy (L.smul_mem _ P.mem_l₀)
  have hψq : ψ (y - (ψ y / ψ l₀) • l₀) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ P.ne_zero, sub_self]
  have hqm : y - (ψ y / ψ l₀) • l₀ ∈ Submodule.span (ZMod p) {m} := by
    by_contra hqm
    obtain ⟨g, hgq, hg⟩ := exists_dual_one_of_notMem hqm
    have hgm : g m = 0 := hg m (Submodule.mem_span_singleton_self m)
    have := P.eq_of_mem hgm hqL
    rw [hψq, mul_zero, hgq] at this
    exact one_ne_zero this
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hqm
  exact ⟨b, by rw [hb]; abel⟩

private theorem Pack.exists_sub_mem (P : Pack H U L ψ l₀ m) (x : V) :
    ∃ a : ZMod p, x - a • m ∈ U ⊔ Submodule.span (ZMod p) {l₀} := by
  obtain ⟨b, hb⟩ := P.exists_eq_add (P.frame.projL_mem x)
  refine ⟨b, ?_⟩
  have hx := P.frame.projU_add_projL x
  have : x - b • m = P.frame.projU x + (ψ (P.frame.projL x) / ψ l₀) • l₀ := by
    conv_lhs => rw [← hx, hb]
    abel
  rw [this]
  exact Submodule.add_mem_sup (P.frame.projU_mem x)
    (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l₀))

private def Good (H : Subgroup (V ≃ₗ[ZMod p] V)) (m x : V) : Prop :=
  ∀ f : Module.Dual (ZMod p) V, f m = 0 → f x = 0 → TrIn H x f

private theorem Good.smul {x : V} (hx : Good H m x) (s : ZMod p) : Good H m (s • x) := by
  intro f hfm hfx
  rw [TrIn.smul_center_iff]
  refine hx (s • f) (by rw [LinearMap.smul_apply, hfm, smul_zero]) ?_
  rw [LinearMap.smul_apply, ← map_smul]
  exact hfx

private theorem Pack.good_add (P : Pack H U L ψ l₀ m) {x y : V}
    (hx : x ∈ U ⊔ Submodule.span (ZMod p) {l₀}) (hy : y ∈ U ⊔ Submodule.span (ZMod p) {l₀})
    (hgx : Good H m x) (hgy : Good H m y) : Good H m (x + y) := by
  by_cases hyx : y ∈ Submodule.span (ZMod p) {x}
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hyx
    have : x + a • x = (1 + a) • x := by rw [add_smul, one_smul]
    rw [this]
    exact hgx.smul _
  have hy' : y ∉ Submodule.span (ZMod p) {x, m} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hb : b = 0 := by
      by_contra hb
      apply P.m_notMem
      have h1 : b • m ∈ U ⊔ Submodule.span (ZMod p) {l₀} := by
        have : b • m = y - a • x := by rw [← hab]; abel
        rw [this]
        exact Submodule.sub_mem _ hy (Submodule.smul_mem _ a hx)
      have h2 := Submodule.smul_mem _ b⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h2
    rw [hb, zero_smul, add_zero] at hab
    exact hyx (Submodule.mem_span_singleton.mpr ⟨a, hab⟩)
  obtain ⟨f₁, hf₁y, hf₁⟩ := exists_dual_one_of_notMem hy'
  have hf₁x : f₁ x = 0 := hf₁ x (Submodule.subset_span (by simp))
  have hf₁m : f₁ m = 0 := hf₁ m (Submodule.subset_span (by simp))
  obtain ⟨-, t, ht, htx⟩ := hgx f₁ hf₁m hf₁x
  have htm : t m = m := by rw [htx m, hf₁m, zero_smul, add_zero]
  have hty : t y = x + y := by rw [htx y, hf₁y, one_smul, add_comm]
  intro f hfm hfxy
  have hf' : TrIn H y (f ∘ₗ t.toLinearMap) :=
    hgy _ (by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, htm, hfm])
      (by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hty, hfxy])
  have hconj := hf'.conj ht
  have hcomp : (f ∘ₗ t.toLinearMap) ∘ₗ t.symm.toLinearMap = f := by
    ext z
    simp
  rwa [hty, hcomp] at hconj

private theorem Pack.good_of_mem_U (P : Pack H U L ψ l₀ m) {u : V} (hu : u ∈ U) :
    Good H m u := by
  intro f hfm hfu
  have h1 : TrIn H u (f ∘ₗ P.frame.projU) := by
    refine P.frame.2.2.2 u hu _ (fun l hl => ?_) ?_
    · rw [LinearMap.comp_apply, P.frame.projU_of_mem_L hl, map_zero]
    · rw [LinearMap.comp_apply, P.frame.projU_of_mem hu]
      exact hfu
  have h2 : TrIn H u ((f l₀ / ψ l₀) • ψ) := (P.psi u hu).smul _
  have := h1.add h2
  rwa [← P.decomp hfm] at this

private theorem Pack.good_l₀ (P : Pack H U L ψ l₀ m) : Good H m l₀ := by
  intro f hfm hfl
  refine P.trIn_l₀ f (fun y hy => ?_)
  rw [P.eq_of_mem hfm hy, hfl, zero_div, zero_mul]

private theorem Pack.step_one (P : Pack H U L ψ l₀ m) :
    ∀ c ∈ U ⊔ Submodule.span (ZMod p) {l₀}, Good H m c := by
  let S : Submodule (ZMod p) V :=
    { carrier := {v | v ∈ U ⊔ Submodule.span (ZMod p) {l₀} ∧ Good H m v}
      add_mem' := fun hx hy => ⟨Submodule.add_mem _ hx.1 hy.1, P.good_add hx.1 hy.1 hx.2 hy.2⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun f _ _ => TrIn.zero_center f⟩
      smul_mem' := fun s _ hx => ⟨Submodule.smul_mem _ s hx.1, hx.2.smul s⟩ }
  have hmem : ∀ v, v ∈ S ↔ v ∈ U ⊔ Submodule.span (ZMod p) {l₀} ∧ Good H m v :=
    fun v => Iff.rfl
  have hU : U ≤ S := fun u hu => (hmem u).mpr ⟨Submodule.mem_sup_left hu, P.good_of_mem_U hu⟩
  have hl : Submodule.span (ZMod p) {l₀} ≤ S := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (hmem l₀).mpr
      ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self l₀), P.good_l₀⟩
  intro c hc
  exact ((hmem c).mp (sup_le hU hl hc)).2

private theorem exists_moving_transvection
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {W : Submodule (ZMod p) V} (hbot : W ≠ ⊥) (htop : W ≠ ⊤) :
    ∃ (x : V) (h : Module.Dual (ZMod p) V) (y : V), TrIn H x h ∧ x ∉ W ∧ y ∈ W ∧ h y ≠ 0 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  by_contra hcon
  push Not at hcon
  have hinv : ∀ t ∈ S, ∀ z ∈ W, t z ∈ W ∧ t⁻¹ z ∈ W := by
    intro t ht z hz
    obtain ⟨v, g, hvg⟩ := hS t ht
    have hTr : TrIn H v g := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure ht) hvg
    have hgz : g z • v ∈ W := by
      by_cases hv : v ∈ W
      · exact W.smul_mem _ hv
      · rw [hcon v g z hTr hv hz, zero_smul]
        exact W.zero_mem
    refine ⟨?_, ?_⟩
    · rw [hvg.2.2.2 z]
      exact W.add_mem hz hgz
    · rw [hvg.inv_apply z]
      exact W.sub_mem hz hgz
  rcases hirr W (invariant_of_generators hHS hinv) with h | h
  · exact hbot h
  · exact htop h

private theorem Pack.fullCenter_of_moving_ne (P : Pack H U L ψ l₀ m) {x : V}
    {h : Module.Dual (ZMod p) V} {a : ZMod p} (hxh : TrIn H x h) (ha : a ≠ 0)
    (hx₃ : x - a • m ∈ U ⊔ Submodule.span (ZMod p) {l₀}) (hhm : h m ≠ 0) :
    ∃ c, FullCenter H c := by
  obtain ⟨c, hcU, hc0, hhc⟩ := exists_ne_zero_ker_of_finrank_two P.frame.2.1 h
  have hcW : c ∈ U ⊔ Submodule.span (ZMod p) {l₀} := Submodule.mem_sup_left hcU
  have hhx₃ : h (x - a • m) ≠ 0 := by
    rw [map_sub, map_smul, hxh.1, zero_sub, smul_eq_mul]
    exact neg_ne_zero.mpr (mul_ne_zero ha hhm)
  have hnot : x - a • m ∉ Submodule.span (ZMod p) {c, m} := by
    intro hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hβ : β = 0 := by
      by_contra hβ
      apply P.m_notMem
      have h1 : β • m ∈ U ⊔ Submodule.span (ZMod p) {l₀} := by
        have : β • m = (x - a • m) - α • c := by rw [← hαβ]; abel
        rw [this]
        exact Submodule.sub_mem _ hx₃ (Submodule.smul_mem _ α hcW)
      have h2 := Submodule.smul_mem _ β⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hβ, one_smul] at h2
    rw [hβ, zero_smul, add_zero] at hαβ
    apply hhx₃
    rw [← hαβ, map_smul, hhc, smul_zero]
  obtain ⟨f, hfx₃, hf⟩ := exists_dual_one_of_notMem hnot
  have hfc : f c = 0 := hf c (Submodule.subset_span (by simp))
  have hfm : f m = 0 := hf m (Submodule.subset_span (by simp))
  have hTc : TrIn H c f := P.step_one c hcW f hfm hfc
  have hfx : f x ≠ 0 := by
    have : f x = f (x - a • m) := by rw [map_sub, map_smul, hfm, smul_zero, sub_zero]
    rw [this, hfx₃]
    exact one_ne_zero
  have hTch : TrIn H c h := by
    have := (TrIn.rule_R hTc hxh hhc).smul (f x)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hfx, one_smul] at this
  refine ⟨c, hc0, fun g hgc => ?_⟩
  have h1 : TrIn H c (g - (g m / h m) • h) :=
    P.step_one c hcW _
      (by rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hhm,
        sub_self])
      (by rw [LinearMap.sub_apply, LinearMap.smul_apply, hgc, hhc, smul_zero, sub_zero])
  have := h1.add (hTch.smul (g m / h m))
  rwa [sub_add_cancel] at this

private theorem Pack.fullCenter_of_moving_eq (P : Pack H U L ψ l₀ m) {x y : V}
    {h : Module.Dual (ZMod p) V} {a : ZMod p} (hxh : TrIn H x h) (ha : a ≠ 0)
    (hx₃ : x - a • m ∈ U ⊔ Submodule.span (ZMod p) {l₀})
    (hy : y ∈ U ⊔ Submodule.span (ZMod p) {l₀}) (hhy : h y ≠ 0) (hhm : h m = 0) :
    ∃ c, FullCenter H c := by
  have hhx₃ : h (x - a • m) = 0 := by rw [map_sub, map_smul, hxh.1, hhm, smul_zero, sub_zero]
  have hT₃ : TrIn H (x - a • m) h := P.step_one _ hx₃ h hhm hhx₃
  have hTam : TrIn H (a • m) h := by
    have h1 : TrIn H ((-1 : ZMod p) • (x - a • m)) h :=
      TrIn.smul_center_iff.mpr (hT₃.smul (-1))
    have h2 := hxh.add_center h1
    have h3 : x + (-1 : ZMod p) • (x - a • m) = a • m := by module
    rwa [h3] at h2
  have hTm : TrIn H m (a • h) := TrIn.smul_center_iff.mp hTam
  have hay : (a • h) y ≠ 0 := by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero ha hhy
  have key : ∀ f : Module.Dual (ZMod p) V, f m = 0 → f y = 0 → TrIn H m f := by
    intro f hfm hfy
    obtain ⟨-, t, ht, htx⟩ := P.step_one y hy f hfm hfy
    have htm : t m = m := by rw [htx m, hfm, zero_smul, add_zero]
    have hinv : ∀ z, t.symm z = z - f z • y := fun z => TrIn.inv_apply hfy htx z
    have hconj := hTm.conj ht
    have hform : (a • h) ∘ₗ t.symm.toLinearMap = a • h - (a • h) y • f := by
      ext z
      show (a • h) (t.symm z) = (a • h) z - (a • h) y * f z
      rw [hinv, map_sub, map_smul, smul_eq_mul]
      ring
    rw [htm, hform] at hconj
    have h2 : TrIn H m ((a • h) y • f) := by
      have := hTm.sub hconj
      rwa [sub_sub_cancel] at this
    have h3 := h2.smul ((a • h) y)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hay, one_smul] at h3
  refine ⟨m, P.m_ne_zero, fun g hgm => ?_⟩
  have h1 : TrIn H m (g - (g y / (a • h) y) • (a • h)) :=
    key _ (by rw [LinearMap.sub_apply, LinearMap.smul_apply, hgm, hTm.1, smul_zero, sub_zero])
      (by rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hay,
        sub_self])
  have := h1.add (hTm.smul (g y / (a • h) y))
  rwa [sub_add_cancel] at this

end Aux

variable (H : Subgroup (V ≃ₗ[ZMod p] V))

theorem exists_fullCenter_of_aplus_aminus [Module.Finite (ZMod p) V]
    (_hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {ψ : Module.Dual (ZMod p) V} (hψU : ∀ y ∈ U, ψ y = 0) (hψ : ∀ u ∈ U, TrIn H u ψ)
    {l₀ : V} (hl₀L : l₀ ∈ L)
    (hl₀ : ∀ φ : Module.Dual (ZMod p) V, (∀ y ∈ L, φ y = 0) → TrIn H l₀ φ) (hs : ψ l₀ ≠ 0) :
    ∃ c, FullCenter H c := by
  obtain ⟨m, hmL, hm0, hψm⟩ := exists_ne_zero_ker_of_finrank_two hF.2.2.1 ψ
  have P : Pack H U L ψ l₀ m := ⟨hF, hψU, hψ, hl₀L, hl₀, hs, hmL, hm0, hψm⟩
  have hbot : U ⊔ Submodule.span (ZMod p) {l₀} ≠ ⊥ := by
    intro h
    have hl₀0 : l₀ ≠ 0 := fun h0 => hs (by rw [h0, map_zero])
    have hmem : l₀ ∈ U ⊔ Submodule.span (ZMod p) {l₀} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self l₀)
    rw [h, Submodule.mem_bot] at hmem
    exact hl₀0 hmem
  have htop : U ⊔ Submodule.span (ZMod p) {l₀} ≠ ⊤ := fun h =>
    P.m_notMem (by rw [h]; exact Submodule.mem_top)
  obtain ⟨x, h, y, hxh, hxW, hyW, hhy⟩ := exists_moving_transvection hirr hgen hbot htop
  obtain ⟨a, ha₃⟩ := P.exists_sub_mem x
  have ha : a ≠ 0 := by
    rintro rfl
    apply hxW
    simpa using ha₃
  by_cases hhm : h m = 0
  · exact P.fullCenter_of_moving_eq hxh ha ha₃ hyW hhy hhm
  · exact P.fullCenter_of_moving_ne hxh ha ha₃ hhm

end CFSG.RankThree.PartOne.LIT

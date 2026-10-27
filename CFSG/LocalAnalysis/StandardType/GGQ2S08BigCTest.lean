module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDichot
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigPairIndep
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigWCard
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRestrict
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCIrr
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCKernel
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCHyper
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumCoxeter
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumConn
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreAbs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08ct_zmod3_eq_one_or_neg_one :
    ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by
  decide

private theorem ggQ2s08ct_isRefl_ggLinRefl {n : ℕ} {g : Vn n ≃ₗ[ZMod 3] Vn n}
    (hg : IsRefl g) : GGLinRefl g := by
  obtain ⟨c, a, hac, hv⟩ := hg
  refine (ggDepA_linRefl_iff (p := 3) (by norm_num) g).mpr ⟨c, ggQ2CellDot a, ?_, ?_⟩
  · rw [ggQ2CellDot_apply]; exact hac
  · intro v; rw [hv v, ggQ2CellDot_apply]

private theorem ggQ2s08ct_isLinRefl_of_isReflLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {T : V ≃ₗ[ZMod 3] V} (h : IsReflLin T) : IsLinRefl T := by
  obtain ⟨c, f, hfc, rfl⟩ := h
  exact ⟨c, f, hfc, fun v => by rw [Module.reflection_apply]⟩

private theorem ggQ2s08ct_isReflLin_of_isLinRefl {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {T : V ≃ₗ[ZMod 3] V} (h : IsLinRefl T) : IsReflLin T := by
  obtain ⟨c, f, hfc, hT⟩ := h
  exact ⟨c, f, hfc, LinearEquiv.ext (fun v => by rw [hT v, Module.reflection_apply])⟩

private theorem ggQ2s08ct_linRefl_conj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V')
    {T : V ≃ₗ[ZMod 3] V} (h : GGLinRefl T) : GGLinRefl (ggLinConj κ T) := by
  have h1 : IsLinRefl T := (ggDepA_linRefl_iff (p := 3) (by norm_num) T).mp h
  have h2 : IsReflLin T := ggQ2s08ct_isReflLin_of_isLinRefl h1
  have h3 : IsReflLin (ggLinConj κ T) := (ggLinConj_isReflLin κ T).mpr h2
  exact (ggDepA_linRefl_iff (p := 3) (by norm_num) (ggLinConj κ T)).mpr
    (ggQ2s08ct_isLinRefl_of_isReflLin h3)

private lemma ggQ2s08ct_mem_span_map {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V') (y : V) (v : V') :
    v ∈ Submodule.span (ZMod 3) {κ y} ↔ κ.symm v ∈ Submodule.span (ZMod 3) {y} := by
  have hmap : (Submodule.span (ZMod 3) {y}).map κ.toLinearMap =
      Submodule.span (ZMod 3) {κ y} := by
    rw [Submodule.map_span]
    simp
  rw [← hmap, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzv⟩
    have hzv' : κ.symm v = z := by
      rw [← hzv]
      exact LinearEquiv.symm_apply_apply κ z
    simpa [hzv'] using hz
  · intro hv
    exact ⟨κ.symm v, hv, by simp⟩

private theorem ggQ2s08ct_isTransv_of_rank_one {n : ℕ} {a : Vn n ≃ₗ[ZMod 3] Vn n}
    (hrank : Module.finrank (ZMod 3) (ggLinMove a) = 1)
    (hsq : ∀ w, a (a w - w) = a w - w) : IsTransv a := by
  classical
  let N : Vn n →ₗ[ZMod 3] Vn n := a.toLinearMap - LinearMap.id
  have hNapply : ∀ v, N v = a v - v := fun v => rfl
  have hNrange : N.range = ggLinMove a := rfl
  have hsq' : ∀ w, N (N w) = 0 := by
    intro w
    have h := hsq w
    rw [← hNapply w] at h
    rw [hNapply (N w), h, sub_self]
  have hrankN : Module.finrank (ZMod 3) N.range = 1 := by
    rw [hNrange]; exact hrank
  have hne : N.range ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod 3) N.range = 0 := by rw [hbot, finrank_bot]
    exact (by decide : (0 : ℕ) ≠ 1) (h0.symm.trans hrankN)
  obtain ⟨c, hcrange, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu⟩ := hcrange
  have hcN : N c = 0 := by
    rw [← hu]
    exact hsq' u
  have hspan : N.range = Submodule.span (ZMod 3) {c} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrankN ⟨u, hu⟩ hc0
  obtain ⟨j, hcj⟩ : ∃ j : Fin n, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext fun k => h k)
  let ψ : Vn n →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun v => (N v) j * (c j)⁻¹
      map_add' := by
        intro x y
        show (N (x + y)) j * (c j)⁻¹ =
          (N x) j * (c j)⁻¹ + (N y) j * (c j)⁻¹
        rw [map_add, Pi.add_apply, add_mul]
      map_smul' := by
        intro r x
        show (N (r • x)) j * (c j)⁻¹ = r • ((N x) j * (c j)⁻¹)
        rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  let a' : Vn n := fun k => ψ (Pi.single k 1)
  have hdot : ∀ v : Vn n, a' ⬝ᵥ v = ψ v := fun v => ggQ2Cell_dotProduct_eval ψ v
  have hNv : ∀ v, N v = ψ v • c := by
    intro v
    have hmem : N v ∈ Submodule.span (ZMod 3) {c} := by
      rw [← hspan]
      exact ⟨v, rfl⟩
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have hcoord : (N v) j = k * c j := by
      rw [← hk, Pi.smul_apply, smul_eq_mul]
    have hψ : ψ v = k := by
      show (N v) j * (c j)⁻¹ = k
      rw [hcoord, mul_assoc, mul_inv_cancel₀ hcj, mul_one]
    rw [hψ]
    exact hk.symm
  have hψc : ψ c = 0 := by
    show (N c) j * (c j)⁻¹ = 0
    rw [hcN, Pi.zero_apply, zero_mul]
  have hNne : N ≠ 0 := by
    intro hN0
    have hbot : N.range = ⊥ := by rw [hN0]; simp
    have h0 : Module.finrank (ZMod 3) N.range = 0 := by rw [hbot, finrank_bot]
    exact (by decide : (0 : ℕ) ≠ 1) (h0.symm.trans hrankN)
  have ha'0 : a' ≠ 0 := by
    intro ha'
    apply hNne
    apply LinearMap.ext
    intro v
    have hψ0 : ψ v = 0 := by
      rw [← hdot v, ha', zero_dotProduct]
    rw [hNv v, hψ0]
    simp
  unfold IsTransv
  refine ⟨c, a', hc0, ha'0, ?_, ?_⟩
  · rw [hdot c, hψc]
  · intro v
    have hav : a v = v + N v := by
      show a v = v + (a v - v)
      abel
    rw [hav, hNv v, hdot v]

private theorem ggQ2s08ct_commutator_eq {n : ℕ}
    {s k : Vn n ≃ₗ[ZMod 3] Vn n} (α : Vn n →ₗ[ZMod 3] ZMod 3) (h : Vn n)
    (hαh : α h = 2) (hs : ∀ v, s v = v - α v • h) (hsinv : s⁻¹ = s)
    {φ : Vn n →ₗ[ZMod 3] Vn n} (hk : ∀ v, k v = v + φ v)
    (hφ2 : ∀ v, φ (φ v) = 0) (hφh : φ h = 0) :
    ∀ v, (s * k * s⁻¹ * k⁻¹) v = v - (α (φ v)) • h := by
  intro v
  have hkinv : k⁻¹ v = v - φ v := by
    apply k.injective
    change k (k.symm v) = k (v - φ v)
    rw [LinearEquiv.apply_symm_apply k v, hk (v - φ v)]
    simp only [map_sub, hφ2 v, sub_zero]
    abel
  have h1 : s (v - φ v) = (v - φ v) - α (v - φ v) • h := hs (v - φ v)
  have h2 : k ((v - φ v) - α (v - φ v) • h) = v - α (v - φ v) • h := by
    rw [hk]
    simp only [map_sub, map_smul, hφh, hφ2 v, smul_zero, sub_zero]
    abel
  have h3 : s (v - α (v - φ v) • h) = v - α (φ v) • h := by
    rw [hs]
    simp only [map_sub, map_smul, hαh]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  calc (s * k * s⁻¹ * k⁻¹) v
      = s (k (s⁻¹ (k⁻¹ v))) := by simp only [LinearEquiv.mul_apply]
    _ = s (k (s (k⁻¹ v))) := by rw [hsinv]
    _ = s (k (s (v - φ v))) := by rw [hkinv]
    _ = s (k ((v - φ v) - α (v - φ v) • h)) := by rw [h1]
    _ = s (v - α (v - φ v) • h) := by rw [h2]
    _ = v - α (φ v) • h := h3

theorem ggQ2s08_bigC_test (hKG : GGReflClassLargeThree) [Finite G] (M : GGQ2LDatum 3 Bs L x)
    (hC : M.ShapeC) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1) (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1))
    {A Mg : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))}
    (hT : TestHyp ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) (κ M.xV) A Mg)
    (hb : ∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)), R ≤ A →
      8 * Nat.card R < 3 ^ ((lab.rank - 1) * (lab.rank - 2) / 2))
    {r t : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)} (hr : r ∈ Mg) (hrr : IsRefl r)
    (hrx : ¬ FixesLine (κ M.xV) r) (ht : t ∈ A) (htr : IsRefl t) (htx : ¬ FixesLine (κ M.xV) t) :
    t ∈ Mg := by
  classical
  obtain ⟨hxL, hfinHmodel, hxHmodel, hfinV, hrootSurj⟩ := hC
  have h9 : 9 ≤ lab.rank := hlab.2.2
  have h4 : 4 ≤ lab.rank := by omega
  obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa [GGQ2LabelWeyl, htag] using hMW
  have hcardΛ : Fintype.card M.Λ = lab.rank := by
    simpa using (Fintype.card_congr e).symm
  have hdimV : Module.finrank (ZMod 3) (Vn (lab.rank + 1)) = lab.rank + 1 := by
    rw [Module.finrank_fin_fun]
  have hfinHmodel' : Module.finrank (ZMod 3) M.coSpan = lab.rank - 1 := by
    rw [hcardΛ] at hfinHmodel
    omega
  let W : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    (ggAutomizer L Bs).map (ggQ2CellLin M κ)
  let x₀ : Vn (lab.rank + 1) := κ M.xV
  let H : Submodule (ZMod 3) (Vn (lab.rank + 1)) := M.coSpan.map κ.toLinearMap
  let s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    fun i => ggQ2CellLin M κ (M.simple (e i))
  let R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    Subgroup.closure ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t})
  have hWdef : W = (ggAutomizer L Bs).map (ggQ2CellLin M κ) := rfl
  have hx0def : x₀ = κ M.xV := rfl
  have hHdef : H = M.coSpan.map κ.toLinearMap := rfl
  have hsdef : s = fun i => ggQ2CellLin M κ (M.simple (e i)) := rfl
  have hRdef : R = Subgroup.closure
      ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t}) := rfl
  have hWclosure : W = Subgroup.closure (Set.range s) := by
    rw [hWdef]
    exact ggQ2Cell_map_automizer_L M κ e s (fun i v => rfl)
  have hWR : W ≤ R := by
    intro w hw
    rw [hRdef]
    exact Subgroup.subset_closure (Or.inl hw)
  have hrR : r ∈ R := by
    rw [hRdef]
    exact Subgroup.subset_closure (Or.inr (by simp))
  have htR : t ∈ R := by
    rw [hRdef]
    exact Subgroup.subset_closure (Or.inr (by simp))
  have hWA : W ≤ A := by
    rw [hWdef]
    exact le_trans hT.W_le hT.le
  have hrA : r ∈ A := hT.le hr
  have hRA : R ≤ A := by
    rw [hRdef, Subgroup.closure_le]
    intro a ha
    rcases ha with ha | ha
    · exact hWA ha
    · rcases ha with rfl | rfl
      · exact hrA
      · exact ht
  have hsW : ∀ i, s i ∈ W := by
    intro i
    rw [hWclosure]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hsR : ∀ i, s i ∈ R := fun i => hWR (hsW i)
  let hroot : Fin lab.rank → Vn (lab.rank + 1) := fun i => κ (M.coroot (e i))
  let αroot : Fin lab.rank → Vn (lab.rank + 1) →ₗ[ZMod 3] ZMod 3 :=
    fun i => (M.root (e i)).comp κ.symm.toLinearMap
  have hs_form : ∀ i v, s i v = v - (αroot i v) • hroot i := by
    intro i v
    change κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v))
      = v - (M.root (e i) (κ.symm v)) • κ (M.coroot (e i))
    rw [M.simple_apply (e i) (κ.symm v), map_sub, map_smul, LinearEquiv.apply_symm_apply]
  have hαh : ∀ i, αroot i (hroot i) = 2 := by
    intro i
    change M.root (e i) (κ.symm (κ (M.coroot (e i)))) = 2
    rw [LinearEquiv.symm_apply_apply, M.pairing (e i) (e i), M.isCartan.1 (e i)]
    norm_num
  have hroot0 : ∀ i, M.coroot (e i) ≠ 0 := fun i => (ggQ2s08d_simple_refl M (e i)).1
  have hrootmem : ∀ i, hroot i ∈ H := by
    intro i
    exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self (e i)))
  have hsH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span (ZMod 3) {h} := by
    intro i
    refine ⟨hroot i, hrootmem i, ?_, ?_⟩
    · change κ (M.coroot (e i)) ≠ 0
      intro h0
      exact hroot0 i (κ.injective (by simpa using h0))
    · intro v
      have h1 : (αroot i v) • hroot i ∈ Submodule.span (ZMod 3) {hroot i} :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have h : -(αroot i v) • hroot i ∈ Submodule.span (ZMod 3) {hroot i} := by
        simpa only [neg_smul] using Submodule.neg_mem _ h1
      have heq : s i v - v = -(αroot i v) • hroot i := by
        rw [hs_form i, neg_smul]; abel
      rwa [heq]
  have hsH' : ∀ i, ∀ v, s i v - v ∈ H := by
    intro i v
    have h1 : (αroot i v) • hroot i ∈ H := H.smul_mem (αroot i v) (hrootmem i)
    have h : -(αroot i v) • hroot i ∈ H := by
      simpa only [neg_smul] using H.neg_mem h1
    have heq : s i v - v = -(αroot i v) • hroot i := by
      rw [hs_form i, neg_smul]; abel
    rwa [heq]
  have hWH : ∀ w ∈ W, ∀ v, w v - v ∈ H := by
    intro w hw v
    have hw' : w ∈ Subgroup.closure (Set.range s) := by rwa [← hWclosure]
    let K : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
      { carrier := {g | ∀ v, g v - v ∈ H}
        one_mem' := by intro v; simp
        mul_mem' := by
          intro g h hg hh v
          have h1 : g (h v) - h v ∈ H := hg (h v)
          have h2 : h v - v ∈ H := hh v
          have heq : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
            rw [LinearEquiv.mul_apply]; abel
          rw [heq]; exact H.add_mem h1 h2
        inv_mem' := by
          intro g hg v
          have h1 : g (g⁻¹ v) - g⁻¹ v ∈ H := hg (g⁻¹ v)
          have h2 : g (g⁻¹ v) = v := by simp
          rw [h2] at h1
          have heq : g⁻¹ v - v = -(v - g⁻¹ v) := by abel
          rw [heq]; exact H.neg_mem h1 }
    exact ((Subgroup.closure_le K).mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hsH' i)) hw' v
  have hxH : x₀ ∉ H := by
    intro hmem
    rw [hx0def, hHdef] at hmem
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hmem
    exact hxHmodel (κ.injective hyx ▸ hy)
  have hx0ne : x₀ ≠ 0 := by
    intro h0
    have hMx : M.xV = 0 := κ.injective (by simpa [hx0def] using h0)
    exact hxHmodel (by rw [hMx]; exact M.coSpan.zero_mem)
  have hdisj : H ⊓ Submodule.span (ZMod 3) {x₀} = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huH, huS⟩ := Submodule.mem_inf.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp huS
    rcases eq_or_ne c 0 with h0 | h0
    · rw [h0, zero_smul, Submodule.mem_bot]
    · exfalso
      apply hxH
      have hx : x₀ = c⁻¹ • (c • x₀) := by rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
      rw [hx]
      exact H.smul_mem c⁻¹ huH
  have hsrefl : ∀ i, GGLinRefl (s i) := by
    intro i
    have hT' : GGLinRefl (ggLin (p := 3) M.model (M.simple (e i))) :=
      (ggQ2s08d_simple_refl M (e i)).2.1
    have hconv : s i = ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i))) := rfl
    rw [hconv]
    exact ggQ2s08ct_linRefl_conj κ hT'
  have hrrGGLin : GGLinRefl r := ggQ2s08ct_isRefl_ggLinRefl hrr
  have htrGGLin : GGLinRefl t := ggQ2s08ct_isRefl_ggLinRefl htr
  have hgen : R = Subgroup.closure {a | a ∈ R ∧ GGLinRefl a} := by
    apply le_antisymm
    · rw [hRdef, Subgroup.closure_le]
      rintro a (hw | hr_or_t)
      · have ha : a ∈ Subgroup.closure (Set.range s) := by rwa [← hWclosure]
        exact Subgroup.closure_mono (fun x hx => by
          obtain ⟨i, rfl⟩ := hx
          exact ⟨hsR i, hsrefl i⟩) ha
      · rcases hr_or_t with rfl | rfl
        · exact Subgroup.subset_closure ⟨hrR, hrrGGLin⟩
        · exact Subgroup.subset_closure ⟨htR, htrGGLin⟩
    · rw [Subgroup.closure_le]
      intro a ha; exact ha.1
  have hWcard : Nat.card W = (lab.rank + 1).factorial := by
    rw [hWdef, Subgroup.card_map_of_injective (f := ggQ2CellLin M κ)
      (ggQ2CellLin_injective M κ)]
    exact ggQ2s08_big_W_card M hMW htag h4
  obtain ⟨eAM⟩ := ggQ2s08_big_W_equiv M hMW htag h4
  let eW : ↥W ≃* Equiv.Perm (Fin (lab.rank + 1)) :=
    ((ggAutomizer L Bs).equivMapOfInjective (ggQ2CellLin M κ)
      (ggQ2CellLin_injective M κ)).symm.trans eAM
  have hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {x₀} := by
    intro v
    constructor
    · intro hv
      apply (ggQ2s08ct_mem_span_map κ M.xV v).mpr
      have hfix : κ.symm v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
        rw [mem_ggFixedSubmodule_iff]
        intro φ hφ
        have hw : ggQ2CellLin M κ φ ∈ W := by
          rw [hWdef]; exact Subgroup.mem_map_of_mem _ hφ
        have h1 : κ (ggLin (p := 3) M.model φ (κ.symm v)) = v := by
          change ggQ2CellLin M κ φ v = v
          exact hv _ hw
        exact κ.injective (by rw [h1, LinearEquiv.apply_symm_apply κ v])
      rwa [M.fixed_x] at hfix
    · intro hv w hw
      rw [hWdef] at hw
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      have hmem : κ.symm v ∈ Submodule.span (ZMod 3) {M.xV} :=
        (ggQ2s08ct_mem_span_map κ M.xV v).mp hv
      have hfix : ggLin (p := 3) M.model φ (κ.symm v) = κ.symm v := by
        have hmem' : κ.symm v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
          rwa [M.fixed_x]
        exact (mem_ggFixedSubmodule_iff (p := 3) (ι := M.model)
          (N := ggAutomizer L Bs) (v := κ.symm v)).mp hmem' φ hφ
      change ggQ2CellLin M κ φ v = v
      rw [ggQ2CellLin_apply, hfix, LinearEquiv.apply_symm_apply]
  have hWfaith : ∀ w ∈ W, (∀ u ∈ H, w u = u) → w = 1 := by
    intro w hwW hwfixH
    let φ : Vn (lab.rank + 1) →ₗ[ZMod 3] Vn (lab.rank + 1) := w.toLinearMap - LinearMap.id
    have hφapply : ∀ v, φ v = w v - v := fun v => rfl
    have hφH : ∀ u ∈ H, φ u = 0 := by
      intro u hu
      rw [hφapply, hwfixH u hu, sub_self]
    have hφimH : ∀ v, φ v ∈ H := by
      intro v
      rw [hφapply]
      exact hWH w hwW v
    have hφ2 : ∀ v, φ (φ v) = 0 := fun v => hφH (φ v) (hφimH v)
    have hβzero : ∀ i, (αroot i).comp φ = 0 := by
      intro i
      by_contra hβne
      have hss : s i * s i = 1 := (hsrefl i).1
      have hsinv : (s i)⁻¹ = s i := inv_eq_of_mul_eq_one_right hss
      have hcomm : ∀ v, (s i * w * (s i)⁻¹ * w⁻¹) v
          = v - ((αroot i).comp φ) v • hroot i :=
        ggQ2s08ct_commutator_eq (α := αroot i) (h := hroot i) (hαh i) (hs_form i) hsinv
          (k := w) (fun v => by rw [hφapply]; abel) hφ2 (hφH (hroot i) (hrootmem i))
      have hγA : s i * w * (s i)⁻¹ * w⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem (hWA (hsW i)) (hWA hwW))
          (A.inv_mem (hWA (hsW i)))) (A.inv_mem (hWA hwW))
      have htransv : IsTransv (s i * w * (s i)⁻¹ * w⁻¹) := by
        let β : Vn (lab.rank + 1) →ₗ[ZMod 3] ZMod 3 := (αroot i).comp φ
        let avec : Vn (lab.rank + 1) := fun j => (-β) (Pi.single j 1)
        have hdot : ∀ v, avec ⬝ᵥ v = (-β) v := fun v => ggQ2Cell_dotProduct_eval (-β) v
        have ha0 : avec ≠ 0 := by
          intro h0
          apply hβne
          apply LinearMap.ext
          intro v
          have h1 := hdot v
          rw [h0, zero_dotProduct] at h1
          change β v = 0
          simpa only [LinearMap.neg_apply, neg_eq_zero] using h1.symm
        have hac : avec ⬝ᵥ hroot i = 0 := by
          rw [hdot, LinearMap.neg_apply, LinearMap.comp_apply, hφH (hroot i) (hrootmem i),
            map_zero, neg_zero]
        refine ⟨hroot i, avec, ?_, ha0, hac, ?_⟩
        · change κ (M.coroot (e i)) ≠ 0
          intro h0
          exact hroot0 i (κ.injective (by simpa using h0))
        · intro v
          rw [hcomm v, hdot v, LinearMap.neg_apply, neg_smul]
          abel
      exact hT.noTransv _ hγA htransv
    have hφzero : ∀ v, φ v = 0 := by
      intro v
      have hmemH : φ v ∈ H := hφimH v
      have hfix : ∀ w' ∈ W, w' (φ v) = φ v := by
        intro w' hw'
        have hw'' : w' ∈ Subgroup.closure (Set.range s) := by rwa [← hWclosure]
        refine Subgroup.closure_induction (p := fun g _ => g (φ v) = φ v) ?_ ?_ ?_ ?_ hw''
        · rintro x ⟨i, rfl⟩
          have hβi : αroot i (φ v) = 0 := by
            have := congrArg (fun f : Vn (lab.rank + 1) →ₗ[ZMod 3] ZMod 3 => f v) (hβzero i)
            simpa [LinearMap.comp_apply] using this
          rw [hs_form i, hβi, zero_smul, sub_zero]
        · rfl
        · intro a b _ _ iha ihb
          rw [LinearEquiv.mul_apply, ihb, iha]
        · intro a _ iha
          calc a⁻¹ (φ v) = a⁻¹ (a (φ v)) := by rw [iha]
            _ = φ v := LinearEquiv.symm_apply_apply a (φ v)
      have hspan : φ v ∈ Submodule.span (ZMod 3) {x₀} := (hWfix (φ v)).mp hfix
      have hmem : φ v ∈ H ⊓ Submodule.span (ZMod 3) {x₀} := ⟨hmemH, hspan⟩
      rw [hdisj] at hmem
      simpa using hmem
    apply LinearEquiv.ext
    intro v
    have h := hφapply v
    rw [hφzero v] at h
    exact sub_eq_zero.mp h.symm
  have hdich : ∀ S : Submodule (ZMod 3) (Vn (lab.rank + 1)),
      (∀ w ∈ W, ∀ u ∈ S, w u ∈ S) → S ≤ Submodule.span (ZMod 3) {x₀} ∨ H ≤ S := by
    intro S hS
    let U : Submodule (ZMod 3) M.V := S.comap κ.toLinearMap
    have hU : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), ∀ u ∈ U, w u ∈ U := by
      intro w hw u hu
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      have hwW : ggQ2CellLin M κ φ ∈ W := by
        rw [hWdef]; exact Subgroup.mem_map_of_mem _ hφ
      have hSu : κ u ∈ S := Submodule.mem_comap.mp hu
      have hmem : ggQ2CellLin M κ φ (κ u) ∈ S := hS _ hwW _ hSu
      have hkey : κ.toLinearMap (ggLin (p := 3) M.model φ u) = ggQ2CellLin M κ φ (κ u) := by
        change κ (ggLin (p := 3) M.model φ u) = ggQ2CellLin M κ φ (κ u)
        rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply]
      rw [Submodule.mem_comap, hkey]
      exact hmem
    rcases ggQ2s08_big_dichotomy M hlab hMW U hU with hle | hle
    · left
      intro s hs
      apply (ggQ2s08ct_mem_span_map κ M.xV s).mpr
      exact hle (Submodule.mem_comap.mpr (by simpa using hs))
    · right
      have hmap : (M.coSpan).map κ.toLinearMap ≤ S := by
        rw [Submodule.map_le_iff_le_comap]
        exact hle
      rwa [← hHdef] at hmap
  have hWf_exists : ∃ f : Vn (lab.rank + 1) →ₗ[ZMod 3] ZMod 3,
      f x₀ ≠ 0 ∧ ∀ w ∈ W, ∀ v, f (w v) = f v := by
    obtain ⟨f0, hf0x, hf0H⟩ := Submodule.exists_le_ker_of_notMem hxH
    let f : Vn (lab.rank + 1) →ₗ[ZMod 3] ZMod 3 := (f0 x₀)⁻¹ • f0
    have hfx : f x₀ ≠ 0 := by
      have h1 : f x₀ = 1 := by
        change ((f0 x₀)⁻¹ • f0) x₀ = 1
        rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf0x]
      rw [h1]; exact one_ne_zero
    refine ⟨f, hfx, ?_⟩
    intro w hw v
    have hker : f0 (w v - v) = 0 := by
      have hmem := hf0H (hWH w hw v)
      simpa [LinearMap.mem_ker] using hmem
    have h1 : f0 (w v) = f0 v := by
      rw [map_sub] at hker
      exact sub_eq_zero.mp hker
    change ((f0 x₀)⁻¹ • f0) (w v) = ((f0 x₀)⁻¹ • f0) v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, h1]
  have h6 : ∀ i j : M.Λ, i ≠ j → M.coxeter i j ≠ 6 :=
    (ggQ2s08d_label_connected hlab M.coxeter hMW).2
  have hexp : ∀ i j, (CoxeterMatrix.A lab.rank) i j = M.coxeter (e i) (e j) := by
    intro i j
    rw [he, CoxeterMatrix.reindex_apply]
    simp
  have hTij : ∀ i j, s i * s j =
      ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i)) *
        ggLin (p := 3) M.model (M.simple (e j))) := by
    intro i j
    show ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i))) *
        ggLinConj κ (ggLin (p := 3) M.model (M.simple (e j))) =
      ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i)) *
        ggLin (p := 3) M.model (M.simple (e j)))
    rw [map_mul]
  have hrel : ∀ i j, i ≠ j → (s i * s j) ^ (CoxeterMatrix.A lab.rank) i j = 1 := by
    intro i j hij
    have hij' : e i ≠ e j := fun h => hij (e.injective h)
    have hpair := ggQ2s08_big_pairIndep M hMW htag h4 (e i) (e j) hij'
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij' hpair).1
    rw [hTij i j, hexp i j, ← map_pow, hf, map_one]
  have hdist : ∀ i j, i ≠ j → s i ≠ s j := by
    intro i j hij h
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have hpair := ggQ2s08_big_pairIndep M hMW htag h4 (e i) (e j) hij'
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij' hpair).2.1
    have h' : ggLin (p := 3) M.model (M.simple (e i)) =
        ggLin (p := 3) M.model (M.simple (e j)) := by
      apply (ggLinConj κ).injective
      change s i = s j
      exact h
    exact hf h'
  have hncomm : ∀ i j, i ≠ j → (CoxeterMatrix.A lab.rank) i j ≠ 2 →
      s i * s j ≠ s j * s i := by
    intro i j hij h2 h
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have hpair := ggQ2s08_big_pairIndep M hMW htag h4 (e i) (e j) hij'
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij' hpair).2.2.2
    have hT : ggLin (p := 3) M.model (M.simple (e i)) * ggLin (p := 3) M.model (M.simple (e j)) =
        ggLin (p := 3) M.model (M.simple (e j)) * ggLin (p := 3) M.model (M.simple (e i)) := by
      apply (ggLinConj κ).injective
      rw [map_mul, map_mul]
      change s i * s j = s j * s i
      exact h
    exact hf (by rwa [← hexp i j]) hT
  have not_smul_of_fixesLine : ∀ {g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)},
      ¬ FixesLine x₀ g → ¬ ∃ c : ZMod 3, g x₀ = c • x₀ := by
    intro g hg hc
    apply hg
    rcases hc with ⟨c, hc⟩
    rcases eq_or_ne c 0 with h0 | h0
    · exfalso
      have : g x₀ = 0 := by rw [hc, h0, zero_smul]
      exact hx0ne (g.injective (by rw [this, map_zero]))
    · rcases ggQ2s08ct_zmod3_eq_one_or_neg_one c h0 with h1 | h1
      · left; exact hc.trans (by rw [h1]; simp)
      · right; exact hc.trans (by rw [h1]; exact neg_one_smul (ZMod 3) x₀)
  have hsmall_irr : 8 * Nat.card R < 3 ^ ((lab.rank + 1) * lab.rank / 2) := by
    have hb0 := hb R hRA
    have hle1 : lab.rank - 1 ≤ lab.rank + 1 := by omega
    have hle2 : lab.rank - 2 ≤ lab.rank := by omega
    have hle : (lab.rank - 1) * (lab.rank - 2) ≤ (lab.rank + 1) * lab.rank :=
      Nat.mul_le_mul hle1 hle2
    have hdiv : (lab.rank - 1) * (lab.rank - 2) / 2 ≤ (lab.rank + 1) * lab.rank / 2 :=
      Nat.div_le_div_right hle
    exact lt_of_lt_of_le hb0 (Nat.pow_le_pow_right (by norm_num) hdiv)
  have hb_hyper : 8 * Nat.card R <
      3 ^ (((lab.rank + 1) - 2) * ((lab.rank + 1) - 3) / 2) := by
    rw [show (lab.rank + 1) - 2 = lab.rank - 1 by omega,
      show (lab.rank + 1) - 3 = lab.rank - 2 by omega]
    exact hb R hRA
  have hb_restrict : 8 * Nat.card R < 3 ^ ((lab.rank - 1) * ((lab.rank - 1) - 1) / 2) := by
    rw [show (lab.rank - 1) - 1 = lab.rank - 2 by omega]
    exact hb R hRA
  have hnt : ∀ a ∈ A, ¬ (Module.finrank (ZMod 3)
      (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w) := by
    intro a ha hcond
    exact hT.noTransv a ha (ggQ2s08ct_isTransv_of_rank_one hcond.1 hcond.2)
  have hfinH : Module.finrank (ZMod 3) H = lab.rank - 1 := by
    rw [hHdef, LinearEquiv.finrank_map_eq]
    omega
  have hfinH_hyper : Module.finrank (ZMod 3) H = (lab.rank + 1) - 2 := by
    rw [show (lab.rank + 1) - 2 = lab.rank - 1 by omega]; exact hfinH
  have h3_restrict : 3 ∣ (lab.rank - 1) + 2 := by
    rw [show (lab.rank - 1) + 2 = lab.rank + 1 by omega]; exact h3
  have h10_restrict : 10 ≤ lab.rank - 1 := by omega
  have hWcard_restrict : Nat.card W = ((lab.rank - 1) + 2).factorial := by
    rw [show (lab.rank - 1) + 2 = lab.rank + 1 by omega]; exact hWcard
  have hxmove : ¬ ∀ a ∈ R, ∀ u ∈ Submodule.span (ZMod 3) {x₀},
      a u ∈ Submodule.span (ZMod 3) {x₀} := by
    intro hall
    have hrxmem : r x₀ ∈ Submodule.span (ZMod 3) {x₀} :=
      hall r hrR x₀ (Submodule.mem_span_singleton_self x₀)
    obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hrxmem
    exact (not_smul_of_fixesLine (by simpa only [hx0def] using hrx)) ⟨cc, hcc.symm⟩
  by_cases hirr : ∀ S : Submodule (ZMod 3) (Vn (lab.rank + 1)),
      (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤
  ·
    have habs : ZS.AbsIrred 3 R :=
      ggQ2s08core_absIrred_of_irred R hgen ⟨r, hrR, hrrGGLin⟩ hirr
    obtain ⟨f, hf, hWf⟩ := hWf_exists
    have hrx'' : ¬ ∃ c : ZMod 3, r x₀ = c • x₀ :=
      not_smul_of_fixesLine (by simpa only [hx0def] using hrx)
    have hM0eq : GGQ2S08M0 R W r x₀ = R :=
      ggQ2s08_bigC_irr hKG h9 h3 hdimV R W habs hgen hsmall_irr hWR s hsR hsrefl
        hrel hdist hncomm hWclosure eW x₀ hx0ne hWfix f hf hWf r hrR hrrGGLin hrx''
    have hle : GGQ2S08M0 R W r x₀ ≤ Mg := by
      show Subgroup.closure ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪
        {r} ∪ GGQ2S08LineStab R x₀) ≤ Mg
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with ha | ha
      · rcases ha with haW | har
        · exact hT.W_le haW
        · rw [Set.mem_singleton_iff] at har
          rw [har]
          exact hr
      · obtain ⟨haR, cc, hcc0, hccx⟩ := ha
        refine hT.stab_mem a (hRA haR) ?_
        change a x₀ = x₀ ∨ a x₀ = -x₀
        rcases ggQ2s08ct_zmod3_eq_one_or_neg_one cc hcc0 with h1 | h1
        · left; rw [hccx, h1, one_smul]
        · right; rw [hccx, h1, neg_one_smul]
    exact hle (by rw [hM0eq]; exact htR)
  ·
    have hred : ¬ ∀ S : Submodule (ZMod 3) (Vn (lab.rank + 1)),
        (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤ := hirr
    push Not at hirr
    obtain ⟨S, hSR, hS0, hS1⟩ := hirr
    have hpresH : ∀ g ∈ R, ∀ u ∈ H, g u ∈ H :=
      ggQ2s08_bigC_hyper hKG hdimV h3 h12 hfinH_hyper hxH hWH hWcard hWR hWfaith
        hdich hgen hb_hyper hxmove hred
    have hWirr : ∀ U : Submodule (ZMod 3) (Vn (lab.rank + 1)), U ≤ H →
        (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = ⊥ ∨ U = H := by
      intro U hUH hUinv
      rcases hdich U hUinv with hle | hle
      · left
        rw [eq_bot_iff]
        intro u hu
        have hmem : u ∈ H ⊓ Submodule.span (ZMod 3) {x₀} := ⟨hUH hu, hle hu⟩
        rwa [hdisj] at hmem
      · right
        exact le_antisymm hUH hle
    have hres : ∀ g ∈ R, ∃ w ∈ W, ∀ u ∈ H, g u = w u :=
      ggQ2s08_big_restrict hKG h3_restrict h10_restrict hfinH hWcard_restrict hWR hgen
        hpresH hWirr hWfaith hb_restrict
    have hkernel : ∀ g ∈ R, ∃ c : ZMod 3, g x₀ = c • x₀ :=
      ggQ2s08_bigC_kernel hWclosure hsH hWfix hxH hWR hRA hnt hpresH hres
    obtain ⟨c, hc⟩ := hkernel t htR
    have hfl : FixesLine x₀ t := by
      rcases eq_or_ne c 0 with h0 | h0
      · exfalso
        have h1 : t x₀ = 0 := by rw [hc, h0, zero_smul]
        exact hx0ne (t.injective (by rw [h1, map_zero]))
      · rcases ggQ2s08ct_zmod3_eq_one_or_neg_one c h0 with h1 | h1
        · left; exact hc.trans (by rw [h1]; simp)
        · right; exact hc.trans (by rw [h1]; exact neg_one_smul (ZMod 3) x₀)
    exact (htx (by simpa only [hx0def] using hfl)).elim

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDichot
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigPairIndep
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigWCard
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigARed
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigAIrr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08at_zmod3_eq_one_or_neg_one :
    ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by
  decide

private theorem ggQ2s08at_isRefl_linRefl {n : ℕ} {g : Vn n ≃ₗ[ZMod 3] Vn n}
    (hg : IsRefl g) : GGLinRefl g := by
  obtain ⟨c, a, hac, hgv⟩ := hg
  let f : Module.Dual (ZMod 3) (Vn n) :=
    { toFun := fun v => a ⬝ᵥ v
      map_add' := fun v w => dotProduct_add a v w
      map_smul' := fun s v => by
        rw [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul] }
  refine (ggDepA_linRefl_iff (p := 3) (by norm_num) g).mpr ⟨c, f, ?_, ?_⟩
  · change a ⬝ᵥ c = 2
    exact hac
  · intro v
    change g v = v - (a ⬝ᵥ v) • c
    exact hgv v

private theorem ggQ2s08at_linRefl_conj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V')
    {T : V ≃ₗ[ZMod 3] V} (h : GGLinRefl T) : GGLinRefl (ggLinConj κ T) := by
  rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)] at h ⊢
  obtain ⟨c, f, hcf, hT⟩ := h
  refine ⟨κ c, f.comp κ.symm.toLinearMap, ?_, fun v => ?_⟩
  · change f (κ.symm (κ c)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hcf
  · rw [ggLinConj_apply, hT (κ.symm v)]
    change κ (κ.symm v - f (κ.symm v) • c) = v - f (κ.symm v) • κ c
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2s08at_mem_span_map {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
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

private theorem ggQ2s08at_xV_ne_zero {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hA : M.ShapeA) : M.xV ≠ 0 := by
  obtain ⟨-, hli, -, hdim, hsurj⟩ := hA
  have hker : LinearMap.ker M.rootMap ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective M.rootMap := by
      intro a b hab
      have h : M.rootMap (a - b) = 0 := by
        rw [map_sub, hab]
        abel
      have h2 : a - b = 0 := by
        have hmem : a - b ∈ LinearMap.ker M.rootMap := by
          rw [LinearMap.mem_ker]
          exact h
        rw [hbot] at hmem
        simpa using hmem
      exact sub_eq_zero.mp h2
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hle' : Fintype.card M.Λ + 1 ≤ Fintype.card M.Λ := by
      simpa [hdim, Module.finrank_fintype_fun_eq_card] using hle
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfix : ∀ i, ggLin (p := 3) M.model (M.simple i) u = u := by
    intro i
    have hui : M.root i u = 0 := by
      have h := congrFun hu i
      simpa [GGQ2LDatum.rootMap, LinearMap.pi_apply] using h
    rw [M.simple_apply i u, hui, zero_smul, sub_zero]
  have hmem : u ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    induction hφ using Subgroup.closure_induction with
    | mem ψ hψ =>
        obtain ⟨i, rfl⟩ := hψ
        exact hfix i
    | one =>
        change ggLin (p := 3) M.model 1 u = u
        rw [map_one]
        rfl
    | mul a b _ _ iha ihb =>
        rw [map_mul, LinearEquiv.mul_apply, ihb, iha]
    | inv a _ iha =>
        rw [map_inv]
        have h1 : (ggLin (p := 3) M.model a)⁻¹ u
            = (ggLin (p := 3) M.model a)⁻¹ (ggLin (p := 3) M.model a u) := by rw [iha]
        rw [h1]
        exact LinearEquiv.symm_apply_apply _ u
  rw [M.fixed_x] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  intro hzero
  have hzero' : M.model (Additive.ofMul ⟨x, M.hx⟩) = 0 := by
    simpa [GGQ2LDatum.xV] using hzero
  rw [hzero', smul_zero] at hc
  exact hu0 hc.symm

private theorem ggQ2s08at_A_adj (m : ℕ) {i j : Fin m} (hij : i ≠ j)
    (h : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) :
    CoxeterMatrix.A m i j = 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  rw [if_neg hij, if_pos h]

private theorem ggQ2s08at_cartan_of_coxeter_three {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {i j : M.Λ} (hij : i ≠ j) (h : M.coxeter i j = 3) :
    M.cartan i j = -1 := by
  rcases M.isCartan.2 i j hij with ⟨h2, -, -⟩ | ⟨-, h1, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · rw [h] at h2; norm_num at h2
  · exact h1
  · rw [h] at h4; norm_num at h4
  · rw [h] at h6; norm_num at h6

theorem ggQ2s08_bigA_test (hKG : GGReflClassLargeThree) [Finite G] (M : GGQ2LDatum 3 Bs L x)
    (hA : M.ShapeA) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1) (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1))
    {A Mg : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))}
    (hT : TestHyp ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) (κ M.xV) A Mg)
    (hb : ∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)), R ≤ A →
      8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2))
    {r t : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)} (hr : r ∈ Mg) (hrr : IsRefl r)
    (hrx : ¬ FixesLine (κ M.xV) r) (ht : t ∈ A) (htr : IsRefl t) (htx : ¬ FixesLine (κ M.xV) t) :
    t ∈ Mg ∨ GGQ2S08CoreRO (N := lab.rank + 1)
      (Subgroup.closure
        (((ggAutomizer L Bs).map (ggQ2CellLin M κ) :
            Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪
          {r, t}))
      ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) r (κ M.xV) := by
  classical
  have h9 : 9 ≤ lab.rank := hlab.2.2
  have h4 : 4 ≤ lab.rank := by omega
  obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa [GGQ2LabelWeyl, htag] using hMW
  have hcardΛ : Fintype.card M.Λ = lab.rank := by
    simpa using (Fintype.card_congr e).symm
  have hdimV : Module.finrank (ZMod 3) (Vn (lab.rank + 1)) = lab.rank + 1 := by
    rw [Module.finrank_fin_fun]
  have hA0 : M.ShapeA := hA
  obtain ⟨-, hli, hxUmodel, -, -⟩ := hA
  let W : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    (ggAutomizer L Bs).map (ggQ2CellLin M κ)
  let x₀ : Vn (lab.rank + 1) := κ M.xV
  let U : Submodule (ZMod 3) (Vn (lab.rank + 1)) := M.coSpan.map κ.toLinearMap
  let s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    fun i => ggQ2CellLin M κ (M.simple (e i))
  let R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    Subgroup.closure ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t})
  have hWdef : W = (ggAutomizer L Bs).map (ggQ2CellLin M κ) := rfl
  have hx0def : x₀ = κ M.xV := rfl
  have hUdef : U = M.coSpan.map κ.toLinearMap := rfl
  have hRdef : R = Subgroup.closure
      ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t}) := rfl
  have hx0ne : x₀ ≠ 0 := by
    have hxV0 : M.xV ≠ 0 := ggQ2s08at_xV_ne_zero M hA0
    intro h0
    apply hxV0
    apply κ.injective
    rw [hx0def] at h0
    rw [h0, map_zero]
  have hfinCoSpan : Module.finrank (ZMod 3) M.coSpan = lab.rank := by
    rw [GGQ2LDatum.coSpan, ← hcardΛ]
    exact finrank_span_eq_card hli
  have hfinU : Module.finrank (ZMod 3) U = lab.rank := by
    rw [hUdef, LinearEquiv.finrank_map_eq, hfinCoSpan]
  have hfinU_red : Module.finrank (ZMod 3) U = (lab.rank + 1) - 1 := by
    rw [show (lab.rank + 1) - 1 = lab.rank by omega]
    exact hfinU
  have hxU : x₀ ∈ U := by
    rw [hx0def, hUdef]
    exact Submodule.mem_map_of_mem hxUmodel
  let hroot : Fin lab.rank → Vn (lab.rank + 1) := fun i => κ (M.coroot (e i))
  have hrootmem : ∀ i, hroot i ∈ U := by
    intro i
    rw [hUdef]
    exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self (e i)))
  have hs_form : ∀ i v, s i v = v - (M.root (e i) (κ.symm v)) • hroot i := by
    intro i v
    change κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v))
      = v - (M.root (e i) (κ.symm v)) • κ (M.coroot (e i))
    rw [M.simple_apply (e i) (κ.symm v), map_sub, map_smul, LinearEquiv.apply_symm_apply]
  have hsrefl : ∀ i, GGLinRefl (s i) := by
    intro i
    have hT' : GGLinRefl (ggLin (p := 3) M.model (M.simple (e i))) :=
      (ggQ2s08d_simple_refl M (e i)).2.1
    have hconv : s i = ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i))) := rfl
    rw [hconv]
    exact ggQ2s08at_linRefl_conj κ hT'
  have hWclosure : W = Subgroup.closure (Set.range s) := by
    rw [hWdef]
    exact ggQ2Cell_map_automizer_L M κ e s (fun i v => rfl)
  have hsW : ∀ i, s i ∈ W := by
    intro i
    rw [hWclosure]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hWR : W ≤ R := fun w hw => Subgroup.subset_closure (Or.inl hw)
  have hrR : r ∈ R := Subgroup.subset_closure (Or.inr (by simp))
  have htR : t ∈ R := Subgroup.subset_closure (Or.inr (by simp))
  have hWA : W ≤ A := le_trans hT.W_le hT.le
  have hrA : r ∈ A := hT.le hr
  have hRA : R ≤ A := by
    rw [hRdef, Subgroup.closure_le]
    intro a ha
    rcases ha with ha | ha
    · exact hWA ha
    · rcases ha with rfl | rfl
      · exact hrA
      · exact ht
  have hsR : ∀ i, s i ∈ R := fun i => hWR (hsW i)
  have hsH' : ∀ i v, s i v - v ∈ U := by
    intro i v
    rw [hs_form i v]
    have heq : (v - (M.root (e i) (κ.symm v)) • hroot i) - v
        = -((M.root (e i) (κ.symm v)) • hroot i) := by abel
    rw [heq]
    exact U.neg_mem (U.smul_mem _ (hrootmem i))
  have hWU : ∀ w ∈ W, ∀ v, w v - v ∈ U := by
    intro w hw v
    have hw' : w ∈ Subgroup.closure (Set.range s) := by rwa [← hWclosure]
    let KU : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
      { carrier := {g | ∀ v, g v - v ∈ U}
        one_mem' := by intro v; simp
        mul_mem' := by
          intro g h hg hh u
          have h1 : g (h u) - h u ∈ U := hg (h u)
          have h2 : h u - u ∈ U := hh u
          have heq : (g * h) u - u = (g (h u) - h u) + (h u - u) := by
            rw [LinearEquiv.mul_apply]; abel
          rw [heq]; exact U.add_mem h1 h2
        inv_mem' := by
          intro g hg u
          have h1 : g (g⁻¹ u) - g⁻¹ u ∈ U := hg (g⁻¹ u)
          have h2 : g (g⁻¹ u) = u := by simp
          rw [h2] at h1
          have heq : g⁻¹ u - u = -(u - g⁻¹ u) := by abel
          rw [heq]; exact U.neg_mem h1 }
    exact (Subgroup.closure_le KU).mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hsH' i) hw' v
  have hsU : ∀ i, (∀ u ∈ U, s i u ∈ U) ∧ (∀ u ∈ U, (s i)⁻¹ u ∈ U) := by
    intro i
    have hfwd : ∀ u ∈ U, s i u ∈ U := by
      intro u hu
      rw [show s i u = ggQ2CellLin M κ (M.simple (e i)) u from rfl, ggQ2CellLin_apply]
      apply Submodule.mem_map_of_mem
      have hu' : κ.symm u ∈ M.coSpan := by
        obtain ⟨y, hy, hyu⟩ := Submodule.mem_map.mp hu
        have hy' : κ.symm u = y := by
          rw [← hyu]
          exact LinearEquiv.symm_apply_apply κ y
        rwa [hy']
      rw [M.simple_apply (e i) (κ.symm u)]
      exact M.coSpan.sub_mem hu'
        (M.coSpan.smul_mem _ (Submodule.subset_span (Set.mem_range_self (e i))))
    have hinv : (s i)⁻¹ = s i := inv_eq_of_mul_eq_one_right (hsrefl i).1
    exact ⟨hfwd, fun u hu => by rw [hinv]; exact hfwd u hu⟩
  have hUinv : ∀ w ∈ W, (∀ u ∈ U, w u ∈ U) ∧ (∀ u ∈ U, w⁻¹ u ∈ U) := by
    intro w hw
    rw [hWclosure] at hw
    have hprop : ∀ g ∈ Subgroup.closure (Set.range s),
        (∀ u ∈ U, g u ∈ U) ∧ (∀ u ∈ U, g⁻¹ u ∈ U) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact hsU i
      | one => exact ⟨fun _ hu => hu, fun _ hu => hu⟩
      | mul a b _ _ iha ihb =>
          refine ⟨fun u hu => ?_, fun u hu => ?_⟩
          · rw [LinearEquiv.mul_apply]
            exact iha.1 (b u) (ihb.1 u hu)
          · rw [_root_.mul_inv_rev, LinearEquiv.mul_apply]
            exact ihb.2 (a⁻¹ u) (iha.2 u hu)
      | inv a _ iha => exact ⟨iha.2, iha.1⟩
    exact hprop w hw
  have hrrGGLin : GGLinRefl r := ggQ2s08at_isRefl_linRefl hrr
  have htrGGLin : GGLinRefl t := ggQ2s08at_isRefl_linRefl htr
  have hgen : R = Subgroup.closure {a | a ∈ R ∧ GGLinRefl a} := by
    apply le_antisymm
    · rw [hRdef, Subgroup.closure_le]
      rintro a (hw | hr_or_t)
      · have ha : a ∈ Subgroup.closure (Set.range s) := by rwa [← hWclosure]
        exact Subgroup.closure_mono (fun y hy => by
          obtain ⟨i, rfl⟩ := hy
          exact ⟨hsR i, hsrefl i⟩) ha
      · rcases hr_or_t with rfl | rfl
        · exact Subgroup.subset_closure ⟨hrR, hrrGGLin⟩
        · exact Subgroup.subset_closure ⟨htR, htrGGLin⟩
    · rw [Subgroup.closure_le]
      intro a ha; exact ha.1
  have hcardW : Nat.card W = (lab.rank + 1).factorial := by
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
      apply (ggQ2s08at_mem_span_map κ M.xV v).mpr
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
        (ggQ2s08at_mem_span_map κ M.xV v).mp hv
      have hfix : ggLin (p := 3) M.model φ (κ.symm v) = κ.symm v := by
        have hmem' : κ.symm v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
          rwa [M.fixed_x]
        exact (mem_ggFixedSubmodule_iff (p := 3) (ι := M.model)
          (N := ggAutomizer L Bs) (v := κ.symm v)).mp hmem' φ hφ
      change ggQ2CellLin M κ φ v = v
      rw [ggQ2CellLin_apply, hfix, LinearEquiv.apply_symm_apply]
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
    have hf' : (ggLinConj κ (ggLin (p := 3) M.model (M.simple (e i)) *
        ggLin (p := 3) M.model (M.simple (e j)))) ^ M.coxeter (e i) (e j) = 1 := by
      have h := congrArg (ggLinConj κ) hf
      simpa [map_pow] using h
    rwa [hTij i j, hexp i j]
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
    have hT : ggLin (p := 3) M.model (M.simple (e i)) *
        ggLin (p := 3) M.model (M.simple (e j)) =
        ggLin (p := 3) M.model (M.simple (e j)) *
        ggLin (p := 3) M.model (M.simple (e i)) := by
      apply (ggLinConj κ).injective
      rw [map_mul, map_mul]
      change s i * s j = s j * s i
      exact h
    exact hf (by rwa [← hexp i j]) hT
  have hWfaith : ∀ w ∈ W, (∀ u ∈ U, w u = u) → w = 1 := by
    intro w hw hwfix
    by_contra hwne
    let K : Subgroup ↥W :=
      { carrier := {g | ∀ u ∈ U, (g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) u = u}
        one_mem' := by intro u _; rfl
        mul_mem' := by
          intro g h hg hh u hu
          rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hh u hu, hg u hu]
        inv_mem' := by
          intro g hg u hu
          rw [Subgroup.coe_inv]
          calc (g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))⁻¹ u
              = (g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))⁻¹
                  ((g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) u) := by
                rw [hg u hu]
            _ = u := LinearEquiv.symm_apply_apply _ u }
    have hwK : (⟨w, hw⟩ : ↥W) ∈ K := fun u hu => hwfix u hu
    have hKne : K ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨w, hw⟩, hwK⟩, ?_⟩
      intro h1
      apply hwne
      have h2 : ((⟨⟨w, hw⟩, hwK⟩ : ↥K) : ↥W) = 1 :=
        congrArg (fun y : ↥K => (y : ↥W)) h1
      exact congrArg Subtype.val h2
    have hKnormal : K.Normal := Subgroup.Normal.mk fun n hn g => by
      intro u hu
      have hgu : ((g⁻¹ : ↥W) : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) u ∈ U := by
        rw [Subgroup.coe_inv]
        exact (hUinv g g.2).2 u hu
      show ((g * n * g⁻¹ : ↥W) :
        Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) u = u
      rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hn _ hgu, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one]
      rfl
    let K' : Subgroup (Equiv.Perm (Fin (lab.rank + 1))) := K.map eW.toMonoidHom
    have hK'ne : K' ≠ ⊥ := by
      intro hbot
      apply hKne
      rw [Subgroup.eq_bot_iff_forall]
      intro k hk
      have hmem : eW k ∈ K' := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      rw [hbot] at hmem
      have h1 : eW k = 1 := Subgroup.mem_bot.mp hmem
      exact eW.injective (by rw [h1, map_one])
    haveI : Nontrivial K' := (Subgroup.nontrivial_iff_ne_bot K').mpr hK'ne
    haveI : K'.Normal := Subgroup.Normal.map hKnormal eW.toMonoidHom eW.surjective
    have halt : alternatingGroup (Fin (lab.rank + 1)) ≤ K' :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin (lab.rank + 1))
        (by rw [Nat.card_fin]; omega) (ntN := inferInstance)
    let k0 : Fin lab.rank := ⟨0, by omega⟩
    let k1 : Fin lab.rank := ⟨1, by omega⟩
    have hk01 : k0 ≠ k1 := by
      intro hh
      have hv : (k0 : ℕ) = (k1 : ℕ) := congrArg Fin.val hh
      simp [k0, k1] at hv
    have hs01W : s k0 * s k1 ∈ W := W.mul_mem (hsW k0) (hsW k1)
    let w01 : ↥W := ⟨s k0 * s k1, hs01W⟩
    have hA01 : CoxeterMatrix.A lab.rank k0 k1 = 3 :=
      ggQ2s08at_A_adj _ hk01 (Or.inr (by simp [k0, k1]))
    have hA10 : CoxeterMatrix.A lab.rank k1 k0 = 3 :=
      ggQ2s08at_A_adj _ (Ne.symm hk01) (Or.inl (by simp [k0, k1]))
    have hcox01 : M.coxeter (e k0) (e k1) = 3 := by
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hA01]
    have hcox10 : M.coxeter (e k1) (e k0) = 3 := by
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hA10]
    have hcaret01 : M.cartan (e k0) (e k1) = -1 :=
      ggQ2s08at_cartan_of_coxeter_three M (fun hh => hk01 (e.injective hh)) hcox01
    have hcaret10 : M.cartan (e k1) (e k0) = -1 :=
      ggQ2s08at_cartan_of_coxeter_three M (fun hh => hk01 (e.injective hh).symm) hcox10
    have hα01 : M.root (e k0) (M.coroot (e k1)) = 2 := by
      rw [M.pairing (e k0) (e k1), hcaret01]; decide
    have hα10 : M.root (e k1) (M.coroot (e k0)) = 2 := by
      rw [M.pairing (e k1) (e k0), hcaret10]; decide
    have h01pow : (s k0 * s k1) ^ 3 = 1 := by
      have h := hrel k0 k1 hk01
      rwa [hA01] at h
    have hw01pow : w01 ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (s k0 * s k1) ^ 3 = 1
      exact h01pow
    have hσ3 : (eW w01) ^ 3 = 1 := by rw [← map_pow, hw01pow, map_one]
    have hsign : Equiv.Perm.sign (eW w01) = 1 := by
      have h3 : (Equiv.Perm.sign (eW w01)) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
      have h2 : Equiv.Perm.sign (eW w01) * Equiv.Perm.sign (eW w01) = 1 :=
        Int.units_mul_self _
      calc Equiv.Perm.sign (eW w01)
          = Equiv.Perm.sign (eW w01) * 1 := (mul_one _).symm
        _ = Equiv.Perm.sign (eW w01) *
              (Equiv.Perm.sign (eW w01) * Equiv.Perm.sign (eW w01)) := by rw [h2]
        _ = (Equiv.Perm.sign (eW w01)) ^ 3 := by
            rw [pow_succ, pow_two]
            ac_rfl
        _ = 1 := h3
    have hσA : eW w01 ∈ alternatingGroup (Fin (lab.rank + 1)) :=
      Equiv.Perm.mem_alternatingGroup.2 hsign
    have hw01K : w01 ∈ K := by
      have hmem : eW w01 ∈ K' := halt hσA
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.mp hmem
      have hk : k = w01 := eW.injective hkeq
      rwa [hk] at hkK
    have hfix01 : ∀ u ∈ U, (s k0 * s k1) u = u := fun u hu => hw01K u hu
    have hs1h0 : s k1 (hroot k0) = hroot k0 + hroot k1 := by
      rw [hs_form k1 (hroot k0),
        show κ.symm (hroot k0) = M.coroot (e k0) by simp [hroot], hα10]
      rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul, sub_neg_eq_add]
    have hs0h0 : s k0 (hroot k0) = - hroot k0 := by
      have hα : M.root (e k0) (M.coroot (e k0)) = 2 := by
        rw [M.pairing (e k0) (e k0), M.isCartan.1 (e k0)]; norm_num
      rw [hs_form k0 (hroot k0),
        show κ.symm (hroot k0) = M.coroot (e k0) by simp [hroot], hα]
      rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul, sub_neg_eq_add]
      rw [← two_smul (ZMod 3) (hroot k0), show (2 : ZMod 3) = -1 by decide, neg_one_smul]
    have hs0h1 : s k0 (hroot k1) = hroot k1 + hroot k0 := by
      rw [hs_form k0 (hroot k1),
        show κ.symm (hroot k1) = M.coroot (e k1) by simp [hroot], hα01]
      rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul, sub_neg_eq_add]
    have hcomp : (s k0 * s k1) (hroot k0) = hroot k1 := by
      rw [LinearEquiv.mul_apply, hs1h0, map_add, hs0h0, hs0h1]
      abel
    have hroot_ne : hroot k0 ≠ hroot k1 := by
      intro hh
      have hh' : M.coroot (e k0) = M.coroot (e k1) := κ.injective hh
      have hpair := ggQ2s08_big_pairIndep M hMW htag h4 (e k0) (e k1)
        (fun hh => hk01 (e.injective hh))
      have hzero : (1 : ZMod 3) • M.coroot (e k0) + (-1 : ZMod 3) • M.coroot (e k1) = 0 := by
        rw [hh']; simp
      exact one_ne_zero ((LinearIndependent.pair_iff.mp hpair) 1 (-1) hzero).1
    exact hroot_ne ((hfix01 (hroot k0) (hrootmem k0)).symm.trans hcomp)
  have not_smul_of_fixesLine : ∀ {g : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)},
      ¬ FixesLine x₀ g → ¬ ∃ c : ZMod 3, g x₀ = c • x₀ := by
    intro g hg hc
    apply hg
    rcases hc with ⟨c, hc⟩
    rcases eq_or_ne c 0 with h0 | h0
    · exfalso
      have hzero : g x₀ = 0 := by rw [hc, h0, zero_smul]
      exact hx0ne (g.injective (by rw [hzero, map_zero]))
    · rcases ggQ2s08at_zmod3_eq_one_or_neg_one c h0 with h1 | h1
      · left; exact hc.trans (by rw [h1]; simp)
      · right; exact hc.trans (by rw [h1]; exact neg_one_smul (ZMod 3) x₀)
  have hxmove : ¬ ∀ a ∈ R, ∀ u ∈ Submodule.span (ZMod 3) {x₀},
      a u ∈ Submodule.span (ZMod 3) {x₀} := by
    intro hall
    have hrxmem : r x₀ ∈ Submodule.span (ZMod 3) {x₀} :=
      hall r hrR x₀ (Submodule.mem_span_singleton_self x₀)
    obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hrxmem
    exact (not_smul_of_fixesLine (g := r) hrx) ⟨cc, hcc.symm⟩
  have hsmall : 8 * Nat.card R < 3 ^ ((lab.rank + 1) * lab.rank / 2) := by
    have hle : lab.rank * (lab.rank - 1) ≤ (lab.rank + 1) * lab.rank :=
      Nat.mul_le_mul (by omega) (by omega)
    have hdiv : lab.rank * (lab.rank - 1) / 2 ≤ (lab.rank + 1) * lab.rank / 2 :=
      Nat.div_le_div_right hle
    exact lt_of_lt_of_le (hb R hRA) (Nat.pow_le_pow_right (by norm_num) hdiv)
  have hb_red : 8 * Nat.card R <
      3 ^ (((lab.rank + 1) - 1) * ((lab.rank + 1) - 2) / 2) := by
    rw [show (lab.rank + 1) - 1 = lab.rank by omega,
      show (lab.rank + 1) - 2 = lab.rank - 1 by omega]
    exact hb R hRA
  have hdich : ∀ S : Submodule (ZMod 3) (Vn (lab.rank + 1)),
      (∀ w ∈ W, ∀ u ∈ S, w u ∈ S) → S ≤ Submodule.span (ZMod 3) {x₀} ∨ U ≤ S := by
    intro S hS
    let Uin : Submodule (ZMod 3) M.V := S.comap κ.toLinearMap
    have hUin : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model),
        ∀ u ∈ Uin, w u ∈ Uin := by
      intro w hw u hu
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      have hwW : ggQ2CellLin M κ φ ∈ W := by
        rw [hWdef]; exact Subgroup.mem_map_of_mem _ hφ
      have hSu : κ u ∈ S := Submodule.mem_comap.mp hu
      have hmem : ggQ2CellLin M κ φ (κ u) ∈ S := hS _ hwW _ hSu
      have hkey : κ.toLinearMap (ggLin (p := 3) M.model φ u) =
          ggQ2CellLin M κ φ (κ u) := by
        change κ (ggLin (p := 3) M.model φ u) = ggQ2CellLin M κ φ (κ u)
        rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply]
      rw [Submodule.mem_comap, hkey]
      exact hmem
    rcases ggQ2s08_big_dichotomy M hlab hMW Uin hUin with hle | hle
    · left
      intro s hs
      apply (ggQ2s08at_mem_span_map κ M.xV s).mpr
      exact hle (Submodule.mem_comap.mpr (by simpa using hs))
    · right
      have hmap : (M.coSpan).map κ.toLinearMap ≤ S := by
        rw [Submodule.map_le_iff_le_comap]
        exact hle
      rwa [← hUdef] at hmap
  by_cases hirr : ∀ S : Submodule (ZMod 3) (Vn (lab.rank + 1)),
      (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤
  · have habs : ZS.AbsIrred 3 R :=
      ggQ2s08core_absIrred_of_irred R hgen ⟨r, hrR, hrrGGLin⟩ hirr
    have hrx'' : ¬ ∃ c : ZMod 3, r x₀ = c • x₀ :=
      not_smul_of_fixesLine (g := r) hrx
    rcases ggQ2s08_bigA_irr hKG h9 hdimV R W habs hgen hsmall hWR s hsR hsrefl
        hrel hdist hncomm hWclosure eW x₀ hx0ne hWfix r hrR hrrGGLin hrx'' with hM0 | hRO
    · left
      have hle : GGQ2S08M0 R W r x₀ ≤ Mg := by
        show Subgroup.closure
          ((W : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r} ∪
            GGQ2S08LineStab R x₀) ≤ Mg
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
          rcases ggQ2s08at_zmod3_eq_one_or_neg_one cc hcc0 with h1 | h1
          · left; rw [hccx, h1, one_smul]
          · right; rw [hccx, h1, neg_one_smul]
      exact hle (by rw [hM0]; exact htR)
    · right
      exact hRO
  · exfalso
    exact ggQ2s08_bigA_red hKG hdimV h3 h12 hfinU_red hxU hWU hcardW hWR hWfaith
      hdich hgen hb_red hxmove hirr

end CFSG.StandardType

end

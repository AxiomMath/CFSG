module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDichot
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrthFour
public import CFSG.LocalAnalysis.StandardType.GGQ2ShapeDNoForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08td1_IsRefl_to_GGLinRefl {n : ℕ} {g : Vn n ≃ₗ[ZMod 3] Vn n}
    (hg : IsRefl g) : GGLinRefl g := by
  rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)]
  obtain ⟨c, a, h, hv⟩ := hg
  refine ⟨c, ggQ2CellDot a, ?_, ?_⟩
  · simpa [ggQ2CellDot_apply] using h
  · intro v
    rw [hv v, ggQ2CellDot_apply]

theorem ggQ2s08_bigD_test (hKG : GGReflClassLargeThree) [Finite G] (M : GGQ2LDatum 3 Bs L x)
    (hD : M.ShapeD) (hx0 : M.xV ≠ 0) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1) (κ : M.V ≃ₗ[ZMod 3] Vn lab.rank)
    {A Mg : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank)}
    (hT : TestHyp ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) (κ M.xV) A Mg)
    (hb : ∀ R : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank), R ≤ A →
      8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2))
    {r t : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank} (hr : r ∈ Mg) (hrr : IsRefl r)
    (hrx : ¬ FixesLine (κ M.xV) r) (ht : t ∈ A) (htr : IsRefl t) (htx : ¬ FixesLine (κ M.xV) t) :
    False := by
  classical
  let n := lab.rank
  let W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) := (ggAutomizer L Bs).map (ggQ2CellLin M κ)
  let R : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) :=
    Subgroup.closure ((W : Set (Vn n ≃ₗ[ZMod 3] Vn n)) ∪ (Set.singleton r ∪ Set.singleton t))
  have hWR : W ≤ R := by
    intro w hw
    exact Subgroup.subset_closure (Or.inl hw)
  have hrR : r ∈ R := Subgroup.subset_closure (Or.inr (Or.inl (Set.mem_singleton r)))
  have htR : t ∈ R := Subgroup.subset_closure (Or.inr (Or.inr (Set.mem_singleton t)))
  have hWA : W ≤ A := le_trans hT.W_le hT.le
  have hRA : R ≤ A := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases ha with ha | ha
    · exact hWA ha
    · rcases ha with ha | ha
      · have ha' : a = r := Set.mem_singleton_iff.mp ha
        subst a
        exact hT.le hr
      · have ha' : a = t := Set.mem_singleton_iff.mp ha
        subst a
        exact ht
  have hcard : 8 * Nat.card R < 3 ^ (n * (n - 1) / 2) := hb R hRA
  have hrrefl : GGLinRefl r := ggQ2s08td1_IsRefl_to_GGLinRefl hrr
  have htrefl : GGLinRefl t := ggQ2s08td1_IsRefl_to_GGLinRefl htr
  have hx0ne : κ M.xV ≠ 0 := by
    intro h0
    exact hx0 (κ.injective (by rw [h0, map_zero]))
  have hpm1 : ∀ c : ZMod 3, c ≠ 0 ↔ (c = 1 ∨ c = -1) := by decide
  have hirr : ∀ S : Submodule (ZMod 3) (Vn n),
      (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hSinv : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model),
        ∀ u ∈ S.comap κ.toLinearMap, w u ∈ S.comap κ.toLinearMap := by
      intro w hw u hu
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      rw [Submodule.mem_comap] at hu ⊢
      have hmem : ggQ2CellLin M κ φ ∈ R := by
        change ggQ2CellLin M κ φ ∈
          Subgroup.closure ((W : Set (Vn n ≃ₗ[ZMod 3] Vn n)) ∪
            (Set.singleton r ∪ Set.singleton t))
        exact Subgroup.subset_closure (Or.inl (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩))
      have hres := hS _ hmem (κ u) hu
      rwa [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply] at hres
    have hdich := ggQ2s08_big_dichotomy M hlab hMW (S.comap κ.toLinearMap) hSinv
    rcases hdich with hsub | htop
    · left
      by_contra hSne
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
      have hSle : S ≤ Submodule.span (ZMod 3) {κ M.xV} := by
        intro u hu
        have hu' : κ.symm u ∈ S.comap κ.toLinearMap := by
          rw [Submodule.mem_comap]
          simpa using hu
        have hspan := hsub hu'
        rw [Submodule.mem_span_singleton] at hspan ⊢
        obtain ⟨c, hc⟩ := hspan
        exact ⟨c, by rw [← LinearEquiv.apply_symm_apply κ u, ← hc, map_smul]⟩
      have hsspan : s ∈ Submodule.span (ZMod 3) {κ M.xV} := hSle hs
      rw [Submodule.mem_span_singleton] at hsspan
      obtain ⟨c, hc⟩ := hsspan
      have hc0 : c ≠ 0 := by
        intro hc0
        rw [hc0, zero_smul] at hc
        exact hs0 hc.symm
      have hx0mem : κ M.xV ∈ S := by
        have hxeq : κ M.xV = c⁻¹ • s := by
          rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hxeq]
        exact S.smul_mem _ hs
      have hS_eq : S = Submodule.span (ZMod 3) {κ M.xV} := by
        apply le_antisymm hSle
        rw [Submodule.span_singleton_le_iff_mem]
        exact hx0mem
      have hmemr : r (κ M.xV) ∈ S := hS r hrR _ hx0mem
      rw [hS_eq, Submodule.mem_span_singleton] at hmemr
      obtain ⟨d, hd⟩ := hmemr
      have hd0 : d ≠ 0 := by
        intro hd0
        rw [hd0, zero_smul] at hd
        have hzero : κ M.xV = 0 := by
          have := congrArg r.symm hd
          simpa using this.symm
        exact hx0ne hzero
      have hr2 : r * r = 1 := by
        obtain ⟨c', a', h', hv'⟩ := hrr
        have hreq : r = refl c' a' h' := LinearEquiv.ext hv'
        rw [hreq]
        exact refl_mul_self c' a' h'
      have hd2 : d * d = 1 := by
        have h1 : r (r (κ M.xV)) = κ M.xV := by
          have := congrArg (fun e => e (κ M.xV)) hr2
          simpa [LinearEquiv.mul_apply] using this
        rw [← hd, map_smul, ← hd, smul_smul] at h1
        have h3 : (d * d) • κ M.xV = (1 : ZMod 3) • κ M.xV := by simpa using h1
        exact smul_left_injective (ZMod 3) hx0ne h3
      have hdpm : d = 1 ∨ d = -1 := by
        have h : (d - 1) * (d + 1) = 0 := by
          calc (d - 1) * (d + 1) = d * d - 1 := by ring
            _ = 0 := by rw [hd2]; ring
        rcases mul_eq_zero.mp h with h | h
        · left; linear_combination h
        · right; linear_combination h
      rcases hdpm with hd1 | hdneg
      · exact hrx (Or.inl (by rw [← hd, hd1, one_smul]))
      · exact hrx (Or.inr (by rw [← hd, hdneg, neg_one_smul]))
    · right
      have hS'top : S.comap κ.toLinearMap = ⊤ := top_unique (hD.2.2 ▸ htop)
      have hStop : S = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro s
        have hs' : κ.symm s ∈ S.comap κ.toLinearMap := by
          rw [hS'top]
          exact Submodule.mem_top
        rw [Submodule.mem_comap] at hs'
        simpa using hs'
      exact hStop
  let S : M.Λ → (Vn n ≃ₗ[ZMod 3] Vn n) := fun i => ggQ2CellLin M κ (M.simple i)
  have hS_refl : ∀ i : M.Λ, GGLinRefl (S i) := by
    intro i
    rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)]
    refine ⟨κ (M.coroot i), (M.root i).comp κ.symm.toLinearMap, ?_, ?_⟩
    · change M.root i (κ.symm (κ (M.coroot i))) = 2
      rw [LinearEquiv.symm_apply_apply, M.pairing i i, M.isCartan.1 i]
      norm_num
    · intro v
      rw [ggQ2CellLin_apply, M.simple_apply i]
      simp only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply, map_sub, map_smul]
      rfl
  have hW_eq : W = Subgroup.closure (Set.range S) := by
    change (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range S)
    rw [M.automizer_L, MonoidHom.map_closure]
    congr 1
    ext T
    constructor
    · rintro ⟨φ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hRgen : R = Subgroup.closure (Set.range S ∪ (Set.singleton r ∪ Set.singleton t)) := by
    change Subgroup.closure ((W : Set (Vn n ≃ₗ[ZMod 3] Vn n)) ∪
        (Set.singleton r ∪ Set.singleton t)) =
      Subgroup.closure (Set.range S ∪ (Set.singleton r ∪ Set.singleton t))
    rw [hW_eq]
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      rcases ha with ha | ha
      · have hle : Subgroup.closure (Set.range S) ≤
            Subgroup.closure (Set.range S ∪ (Set.singleton r ∪ Set.singleton t)) :=
          Subgroup.closure_mono (Set.subset_union_left)
        exact hle ha
      · exact Subgroup.subset_closure (Or.inr ha)
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      rcases ha with ha | ha
      · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ha))
      · exact Subgroup.subset_closure (Or.inr ha)
  have hgen_set : (Set.range S ∪ (Set.singleton r ∪ Set.singleton t)) ⊆
      {a | a ∈ R ∧ GGLinRefl a} := by
    intro a ha
    rcases ha with ha | ha
    · obtain ⟨i, rfl⟩ := ha
      refine ⟨?_, hS_refl i⟩
      change S i ∈
        Subgroup.closure ((W : Set (Vn n ≃ₗ[ZMod 3] Vn n)) ∪
          (Set.singleton r ∪ Set.singleton t))
      exact Subgroup.subset_closure (Or.inl (Subgroup.mem_map.mpr ⟨M.simple i, by
        rw [M.automizer_L]
        exact Subgroup.subset_closure (Set.mem_range_self i), rfl⟩))
    · rcases ha with ha | ha
      · have ha' : a = r := Set.mem_singleton_iff.mp ha
        subst a
        exact ⟨Subgroup.subset_closure (Or.inr (Or.inl (Set.mem_singleton r))), hrrefl⟩
      · have ha' : a = t := Set.mem_singleton_iff.mp ha
        subst a
        exact ⟨Subgroup.subset_closure (Or.inr (Or.inr (Set.mem_singleton t))), htrefl⟩
  have hgen : R = Subgroup.closure {a | a ∈ R ∧ GGLinRefl a} := by
    apply le_antisymm
    · calc R = Subgroup.closure (Set.range S ∪ (Set.singleton r ∪ Set.singleton t)) := hRgen
        _ ≤ Subgroup.closure {a | a ∈ R ∧ GGLinRefl a} := by
            apply (Subgroup.closure_le _).mpr
            intro a ha
            exact Subgroup.subset_closure (hgen_set ha)
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      exact ha.1
  have habs : ZS.AbsIrred 3 R :=
    ggQ2s08core_absIrred_of_irred R hgen ⟨r, hrR, hrrefl⟩ hirr
  have hn : Module.finrank (ZMod 3) (Vn n) = n := Module.finrank_fin_fun (ZMod 3)
  have h9 : 9 ≤ n := by omega
  rcases hKG (Vn n) n hn h9 R habs hgen with himp | hcard' | hsym1 | hsym2
  ·
    obtain ⟨b, hbmon⟩ := ggRC_monomial_of_imprimitive hn R habs hgen himp
    let B : LinearMap.BilinForm (ZMod 3) (Vn n) := OrthExcEven.stdBilin b
    let Q : QuadraticForm (ZMod 3) (Vn n) := B.toQuadraticMap
    have hQinv : ∀ a ∈ R, ∀ v, Q (a v) = Q v := by
      intro a ha v
      obtain ⟨σ, c, hcne, hbc⟩ := hbmon a ha
      have hε : ∀ i, c i = 1 ∨ c i = -1 := fun i => (hpm1 (c i)).1 (hcne i)
      have hu : ∀ i, a.toLinearMap (b i) = c i • b (σ i) := by
        intro i
        rw [LinearEquiv.coe_toLinearMap]
        exact hbc i
      have hiso := OrthExcEven.stdBilin_signedPerm b hε hu v v
      simpa [Q, B, LinearMap.BilinMap.toQuadraticMap_apply] using hiso
    have hBnd : B.Nondegenerate := OrthExcEven.stdBilin_nondegenerate b
    have hpolar : ∀ x y : Vn n, QuadraticMap.polarBilin Q x y = 2 * B x y := by
      intro x y
      rw [show Q = B.toQuadraticMap from rfl, QuadraticMap.polarBilin_apply_apply,
        LinearMap.BilinMap.polar_toQuadraticMap]
      have hsym : B x y = B y x := by
        rw [show B = OrthExcEven.stdBilin b from rfl, OrthExcEven.stdBilin_apply,
          OrthExcEven.stdBilin_apply]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsym]
      ring
    have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
      constructor
      · intro x hx
        apply hBnd.1 x
        intro y
        have := hx y
        rw [hpolar] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
      · intro y hy
        apply hBnd.2 y
        intro x
        have := hy x
        rw [hpolar] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
    let Q' : QuadraticForm (ZMod 3) M.V := Q.comp κ.toLinearMap
    have hpolar' : ∀ x y : M.V,
        QuadraticMap.polarBilin Q' x y = QuadraticMap.polarBilin Q (κ x) (κ y) := by
      intro x y
      rw [show Q' = Q.comp κ.toLinearMap from rfl, QuadraticMap.polarBilin_comp]
      rfl
    have hQ'nd : (QuadraticMap.polarBilin Q').Nondegenerate := by
      constructor
      · intro x hx
        apply κ.injective
        rw [map_zero]
        apply hQnd.1 (κ x)
        intro y
        obtain ⟨z, rfl⟩ := κ.surjective y
        have hz := hx z
        rw [hpolar'] at hz
        exact hz
      · intro y hy
        apply κ.injective
        rw [map_zero]
        apply hQnd.2 (κ y)
        intro x
        obtain ⟨z, rfl⟩ := κ.surjective x
        have hz := hy z
        rw [hpolar'] at hz
        exact hz
    have hQ'iso : ∀ φ ∈ ggAutomizer L Bs, ZS.IsIsom 3 Q' (ggLin (p := 3) M.model φ) := by
      intro φ hφ v
      change Q (κ (ggLin (p := 3) M.model φ v)) = Q (κ v)
      have h1 : κ (ggLin (p := 3) M.model φ v) = ggQ2CellLin M κ φ (κ v) := by
        rw [ggQ2CellLin_apply]
        simp
      rw [h1]
      have hmem : ggQ2CellLin M κ φ ∈ R := by
        change ggQ2CellLin M κ φ ∈
          Subgroup.closure ((W : Set (Vn n ≃ₗ[ZMod 3] Vn n)) ∪
            (Set.singleton r ∪ Set.singleton t))
        exact Subgroup.subset_closure (Or.inl (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩))
      exact hQinv _ hmem (κ v)
    exact ggQ2_shapeD_noForm M hD hx0 ⟨Q', hQ'nd, hQ'iso⟩
  · exact absurd hcard' (not_le.mpr hcard)
  · rcases hsym1 with ⟨hnot, _⟩
    exact hnot h3
  · rcases hsym2 with ⟨hdvd, _⟩
    have h3' : 3 ∣ n + 1 := h3
    have hsub : 3 ∣ (n + 2) - (n + 1) := Nat.dvd_sub hdvd h3'
    have h1 : (n + 2) - (n + 1) = 1 := by omega
    rw [h1] at hsub
    exact absurd hsub (by norm_num)

end CFSG.StandardType

end

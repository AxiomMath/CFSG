module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Group
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace QTwoD6

open CFSG.StandardType.QTwoLin

theorem ggQ2d6_scaledDiagram (π : Fin 6 ≃ Fin 6) (μ : Fin 6 → ZMod 3) (hμ : ∀ i, μ i ≠ 0)
    (h : ∀ i j, μ i * (cartanD6 i j : ZMod 3) = μ j * (cartanD6 (π i) (π j) : ZMod 3)) :
    (π = Equiv.refl _ ∨ π = swapD6) ∧ ∃ m : ZMod 3, m ≠ 0 ∧ ∀ i, μ i = m := by
  rw [cartanD6_eq] at h
  obtain ⟨hμc, hπ⟩ := ggQ2g_scaledD 6 (le_refl 6) π μ hμ h
  refine ⟨?_, μ ⟨0, by omega⟩, hμ _, hμc⟩
  rcases hπ with h1 | h1
  · exact Or.inl (by rw [h1]; rfl)
  · exact Or.inr (by rw [h1]; rfl)

private lemma ggQ2d6l_yV_not_coroot {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∉
      Submodule.span (ZMod 3) (Set.range N.coroot) := by
  intro hmem
  let ψ : N.V →ₗ[ZMod 3] ZMod 3 :=
    (LinearMap.proj 0 : V7 →ₗ[ZMod 3] ZMod 3).comp (Fr.F : N.V →ₗ[ZMod 3] V7)
  have hzero : ∀ i : N.Λ, ψ (N.coroot i) = 0 := by
    intro i
    have hi : Fr.F (N.coroot i) = hvec (Fr.e.symm i) := by
      rw [← Fr.F_coroot (Fr.e.symm i), Fr.e.apply_symm_apply]
    change (LinearMap.proj 0 : V7 →ₗ[ZMod 3] ZMod 3) (Fr.F (N.coroot i)) = 0
    rw [hi]
    simp [hvec]
  have hone : ψ (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 1 := by
    change (LinearMap.proj 0 : V7 →ₗ[ZMod 3] ZMod 3)
      (Fr.F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))) = 1
    rw [Fr.F_y]
    simp [e0]
  have hle : Submodule.span (ZMod 3) (Set.range N.coroot) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hzero i
  have h0 : ψ (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
    simpa using hle hmem
  rw [hone] at h0
  exact one_ne_zero h0

private lemma ggQ2d6l_coord_mem_W6 {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K Bs) : ggCoord N Fr.F φ ∈ W6 := by
  have himg : (ggCoord N Fr.F) '' Set.range N.simple = Set.range simpleD6 := by
    ext t
    constructor
    · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
      refine ⟨Fr.e.symm i, ?_⟩
      have h := ggQ2_d6_coord_simple Fr (Fr.e.symm i)
      rw [Fr.e.apply_symm_apply i] at h
      exact h.symm
    · rintro ⟨j, rfl⟩
      exact ⟨N.simple (Fr.e j), ⟨Fr.e j, rfl⟩, ggQ2_d6_coord_simple Fr j⟩
  have hmap : (ggAutomizer K Bs).map (ggCoord N Fr.F) = W6 := by
    rw [N.automizer_K, MonoidHom.map_closure, himg]
    rfl
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩

private lemma ggQ2d6l_lin_coroot {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy)
    (φ : MulAut ↥Bs) (i : Fin 6) :
    ggLin (p := 3) N.model φ (N.coroot (Fr.e i)) = Fr.F.symm (ggCoord N Fr.F φ (hvec i)) := by
  rw [ggQ2_d6_coord_apply, Fr.F.symm_apply_apply]
  congr 1
  apply Fr.F.injective
  rw [Fr.F_coroot, LinearEquiv.apply_symm_apply]

private lemma ggQ2d6l_lin_u {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy)
    (φ : MulAut ↥Bs) :
    ggLin (p := 3) N.model φ (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
      Fr.F.symm (ggCoord N Fr.F φ e0) := by
  rw [ggQ2_d6_coord_apply, Fr.F.symm_apply_apply]
  rw [← Fr.F_y, Fr.F.symm_apply_apply]

theorem ggQ2d6_normForm {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hb : N.IsD6Fork b}
    {hy : y ∈ Bs} (hK1 : GGQTwoK1 3 B Bs x D J) (Fr : GGQ2D6Frame N b hy)
    (hnorm : N.NormAt y) :
    ∀ φ ∈ linA N Fr.F, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
      ∃ w ∈ W6, ∃ c : ZMod 3, c ≠ 0 ∧ ∃ π : Fin 6 ≃ Fin 6,
        (π = Equiv.refl _ ∨ π = swapD6) ∧ ∀ i, φ (hvec i) = c • w (hvec (π i)) := by
  have _ := hS
  have _ := hb
  intro φ hφ hφe0
  obtain ⟨φg, hφg_top, hφgeq⟩ := Subgroup.mem_map.mp hφ
  have hfixK : ∀ v : N.V,
      (∀ g ∈ (ggAutomizer K Bs).map (ggLin (p := 3) N.model), g v = v) ↔
        v ∈ Submodule.span (ZMod 3) {N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} := by
    rw [← GGQ2NbrDatum.weyl_eq_map N]
    exact ggQ2d6_fix_weyl hnb N hK1 hy
  have hyV : N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∉
      Submodule.span (ZMod 3) (Set.range N.coroot) := ggQ2d6l_yV_not_coroot Fr
  have hstepC : ggLin (p := 3) N.model φg (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) ∈
      Submodule.span (ZMod 3) {N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} := by
    obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφe0
    refine Submodule.mem_span_singleton.mpr ⟨c₀, ?_⟩
    have h1 : ggLin (p := 3) N.model φg (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        Fr.F.symm (φ e0) := by
      rw [ggQ2d6l_lin_u Fr φg, hφgeq]
    rw [h1, ← hc₀, map_smul,
      show Fr.F.symm e0 = N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from by
        rw [← Fr.F_y, Fr.F.symm_apply_apply]]
  obtain ⟨π₀, μ, c, hc, hμ, hcartan, w, hw, hwapply⟩ :=
    hnorm ⟨y, hy⟩ rfl hfixK hyV φg hφg_top hstepC
  let π' : Fin 6 ≃ Fin 6 := Fr.e.trans (π₀.trans Fr.e.symm)
  let μ' : Fin 6 → ZMod 3 := fun i => μ (Fr.e i)
  have hπ'e : ∀ i, Fr.e (π' i) = π₀ (Fr.e i) := by
    intro i
    simp only [π', Equiv.trans_apply, Equiv.apply_symm_apply]
  have hμ' : ∀ i, μ' i ≠ 0 := fun i => hμ (Fr.e i)
  have hcartFr := ggQ2d6_cartan_reindex N Fr.e Fr.coxeter_eq
  have hcartan' : ∀ i j, μ' i * (cartanD6 i j : ZMod 3) =
      μ' j * (cartanD6 (π' i) (π' j) : ZMod 3) := by
    intro i j
    change μ (Fr.e i) * (cartanD6 i j : ZMod 3) =
      μ (Fr.e j) * (cartanD6 (π' i) (π' j) : ZMod 3)
    have h := hcartan (Fr.e i) (Fr.e j)
    rw [show N.cartan (Fr.e i) (Fr.e j) = cartanD6 i j from hcartFr i j,
      show N.cartan (π₀ (Fr.e i)) (π₀ (Fr.e j)) = cartanD6 (π' i) (π' j) from by
        rw [← hπ'e i, ← hπ'e j]
        exact hcartFr (π' i) (π' j)] at h
    exact h
  obtain ⟨hπ, m, hm, hμm⟩ := ggQ2d6_scaledDiagram π' μ' hμ' hcartan'
  obtain ⟨wg, hwg, hwgeq⟩ := Subgroup.mem_map.mp hw
  let w6 : V7 ≃ₗ[ZMod 3] V7 := ggCoord N Fr.F wg
  have hw6 : w6 ∈ W6 := ggQ2d6l_coord_mem_W6 Fr hwg
  refine ⟨w6, hw6, c * m, mul_ne_zero hc hm, π', hπ, fun i => ?_⟩
  have happ := hwapply (Fr.e i)
  rw [ggQ2d6l_lin_coroot Fr φg i, hφgeq, ← hwgeq, ← hπ'e i] at happ
  have hF : Fr.F (ggLin (p := 3) N.model wg (N.coroot (Fr.e (π' i)))) = w6 (hvec (π' i)) := by
    have hc' : N.coroot (Fr.e (π' i)) = Fr.F.symm (hvec (π' i)) := by
      apply Fr.F.injective
      rw [Fr.F_coroot, LinearEquiv.apply_symm_apply]
    rw [hc']
    exact (ggQ2_d6_coord_apply N Fr.F wg (hvec (π' i))).symm
  have hmi : μ (Fr.e i) = m := hμm i
  have h2 := congrArg Fr.F happ
  rw [Fr.F.apply_symm_apply, map_smul, map_smul, hF, hmi] at h2
  exact h2.trans (smul_smul c m (w6 (hvec (π' i))))

end QTwoD6

end CFSG.StandardType

end


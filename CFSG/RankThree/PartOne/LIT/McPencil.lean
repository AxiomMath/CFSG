module

public import CFSG.RankThree.PartOne.LIT.McBasic
import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

namespace FullCenter

variable {H : Subgroup (V ≃ₗ[ZMod p] V)} {v x y : V}

theorem smul_of_ne_zero (hv : FullCenter H v) {s : ZMod p} (hs : s ≠ 0) : FullCenter H (s • v) := by
  refine ⟨smul_ne_zero hs hv.1, fun f hf => ?_⟩
  rw [TrIn.smul_center_iff]
  refine hv.2 _ ?_
  rw [LinearMap.smul_apply, ← map_smul]
  exact hf

theorem map_of_mem (hv : FullCenter H v) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) :
    FullCenter H (g v) := by
  refine ⟨fun h => hv.1 (g.map_eq_zero_iff.mp h), fun f hf => ?_⟩
  have h := (hv.2 (f ∘ₗ g.toLinearMap) hf).conj hg
  have hfg : (f ∘ₗ g.toLinearMap) ∘ₗ g.symm.toLinearMap = f := by
    ext z
    simp
  rwa [hfg] at h

theorem add_of_notMem_span (hx : FullCenter H x) (hy : FullCenter H y)
    (hxy : y ∉ Submodule.span (ZMod p) {x}) : FullCenter H (x + y) := by
  obtain ⟨f, hfy, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxy inferInstance
  have hfx : f x = 0 := by
    have hmem : f x ∈ (Submodule.span (ZMod p) {x}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self x)
    rw [hf] at hmem
    exact (Submodule.mem_bot _).mp hmem
  obtain ⟨-, t, ht, htx⟩ := hx.2 ((f y)⁻¹ • f) (by simp [hfx])
  have hty := hy.map_of_mem ht
  rwa [htx y, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfy, one_smul,
    add_comm y x] at hty

end FullCenter

private theorem zero_or_fullCenter_add {H : Subgroup (V ≃ₗ[ZMod p] V)} {x y : V}
    (hx : x = 0 ∨ FullCenter H x) (hy : y = 0 ∨ FullCenter H y) :
    x + y = 0 ∨ FullCenter H (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa using Or.inr hx
  by_cases hxy : y ∈ Submodule.span (ZMod p) {x}
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hxy
    have hsum : x + s • x = (1 + s) • x := by rw [add_smul, one_smul]
    by_cases hs : 1 + s = 0
    · exact Or.inl (by rw [hsum, hs, zero_smul])
    · exact Or.inr (by rw [hsum]; exact hx.smul_of_ne_zero hs)
  · exact Or.inr (hx.add_of_notMem_span hy hxy)

private theorem zero_or_fullCenter_smul {H : Subgroup (V ≃ₗ[ZMod p] V)} {x : V}
    (hx : x = 0 ∨ FullCenter H x) (s : ZMod p) : s • x = 0 ∨ FullCenter H (s • x) := by
  by_cases hs : s = 0
  · exact Or.inl (by rw [hs, zero_smul])
  rcases hx with rfl | hx
  · exact Or.inl (smul_zero s)
  · exact Or.inr (hx.smul_of_ne_zero hs)

theorem forall_trIn_of_fullCenter (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : V} (hc : FullCenter H c) :
    ∀ (c' : V) (f : Module.Dual (ZMod p) V), f c' = 0 → TrIn H c' f := by
  let S : Submodule (ZMod p) V :=
    { carrier := {v | v = 0 ∨ FullCenter H v}
      add_mem' := fun hx hy => zero_or_fullCenter_add hx hy
      zero_mem' := Or.inl rfl
      smul_mem' := fun s _ hx => zero_or_fullCenter_smul hx s }
  have hmem : ∀ v, v ∈ S ↔ v = 0 ∨ FullCenter H v := fun v => Iff.rfl
  have hinv : ∀ h ∈ H, ∀ x ∈ S, h x ∈ S := by
    intro h hh x hx
    rcases (hmem x).mp hx with rfl | hx
    · exact (hmem _).mpr (Or.inl (map_zero h))
    · exact (hmem _).mpr (Or.inr (hx.map_of_mem hh))
  have hne : S ≠ ⊥ := fun hbot =>
    hc.1 ((Submodule.mem_bot (ZMod p)).mp (hbot ▸ (hmem c).mpr (Or.inr hc)))
  have htop : S = ⊤ := (hirr S hinv).resolve_left hne
  intro c' f hf
  by_cases hc' : c' = 0
  · rw [hc']
    exact TrIn.zero_center f
  · rcases (hmem c').mp (htop ▸ Submodule.mem_top) with h | h
    · exact absurd h hc'
    · exact h.2 f hf

private noncomputable def slActN {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod p) →* (V ≃ₗ[ZMod p] V) where
  toFun A := Matrix.toLinearEquiv b A (by rw [A.2]; exact isUnit_one)
  map_one' := LinearEquiv.ext fun x => by
    rw [Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one]
    rfl
  map_mul' A B := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin_mul b b b]
    rfl

private theorem slActN_apply_basis {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Matrix.SpecialLinearGroup (Fin n) (ZMod p)) (k : Fin n) :
    slActN b A (b k) = ∑ l, (A : Matrix (Fin n) (Fin n) (ZMod p)) l k • b l := by
  rw [show slActN b A (b k) = Matrix.toLin b b (A : Matrix (Fin n) (Fin n) (ZMod p)) (b k) from
    rfl, Matrix.toLin_self]

private theorem slActN_transvection_apply {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j : Fin n} (hij : i ≠ j) (c : ZMod p) (x : V) :
    slActN b (Matrix.SpecialLinearGroup.transvection hij c) x = x + (c • b.coord j) x • b i := by
  have hlin : (slActN b (Matrix.SpecialLinearGroup.transvection hij c) : V →ₗ[ZMod p] V) =
      LinearMap.transvection (c • b.coord j) (b i) := by
    refine b.ext fun k => ?_
    rw [LinearEquiv.coe_coe, slActN_apply_basis, LinearMap.transvection.apply,
      CFSG.LinearGroups.coe_transvection, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_eq_mul]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
      Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Ne.symm hk]
  exact congrArg (fun φ : V →ₗ[ZMod p] V => φ x) hlin

private theorem det_one_mem_of_basis {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ (c : V) (f : Module.Dual (ZMod p) V), f c = 0 → TrIn H c f) :
    ∀ g : V ≃ₗ[ZMod p] V, LinearMap.det (g : V →ₗ[ZMod p] V) = 1 → g ∈ H := by
  have hEmem : ∀ (i j : Fin n) (hij : i ≠ j) (c : ZMod p),
      slActN b (Matrix.SpecialLinearGroup.transvection hij c) ∈ H := by
    intro i j hij c
    obtain ⟨-, t, ht, htx⟩ := hall (b i) (c • b.coord j) (by
      rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne (Ne.symm hij), smul_zero])
    have heq : slActN b (Matrix.SpecialLinearGroup.transvection hij c) = t :=
      LinearEquiv.ext fun x => by rw [slActN_transvection_apply, htx]
    rw [heq]
    exact ht
  have hallSL : ∀ A, slActN b A ∈ H := by
    intro A
    have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet n (ZMod p)) ≤
        H.comap (slActN b) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      exact hEmem i j hij c
    rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
    exact hle (Subgroup.mem_top A)
  intro g hdet
  have hA : (LinearMap.toMatrix b b (g : V →ₗ[ZMod p] V)).det = 1 := by
    rw [LinearMap.det_toMatrix, hdet]
  have hg := hallSL ⟨_, hA⟩
  convert hg using 1
  ext x
  change g x = Matrix.toLin b b (LinearMap.toMatrix b b (g : V →ₗ[ZMod p] V)) x
  rw [Matrix.toLin_toMatrix]
  rfl

theorem det_one_mem_of_forall_trIn [Module.Finite (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ (c : V) (f : Module.Dual (ZMod p) V), f c = 0 → TrIn H c f) :
    ∀ g : V ≃ₗ[ZMod p] V, LinearMap.det (g : V →ₗ[ZMod p] V) = 1 → g ∈ H :=
  det_one_mem_of_basis (Module.finBasis (ZMod p) V) H hall

theorem det_one_mem_of_fullCenter [Module.Finite (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : V} (hc : FullCenter H c) :
    ∀ g : V ≃ₗ[ZMod p] V, LinearMap.det (g : V →ₗ[ZMod p] V) = 1 → g ∈ H :=
  det_one_mem_of_forall_trIn H (forall_trIn_of_fullCenter H hirr hc)

end CFSG.RankThree.PartOne.LIT

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpSiegel
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.LieType.BorelTits CFSG.StandardType.RCKK1IIISp
  CFSG.StandardType.LieKnownR2.Short
open scoped Matrix

abbrev SpMod (m : ℕ) := Fin m ⊕ Fin m → GaloisField 2 1

abbrev SpG (m : ℕ) := ↥(StatedSp m (GaloisField 2 1))

variable {m : ℕ}

noncomputable abbrev spBilin (m : ℕ) : LinearMap.BilinForm (GaloisField 2 1) (SpMod m) :=
  CFSG.ClassicalGroups.Symplectic.spForm m (GaloisField 2 1)

theorem spB_eq_spBilin (x y : SpMod m) : spB m x y = spBilin m x y := by
  rw [CFSG.ClassicalGroups.Symplectic.spForm_apply]
  rfl

theorem spBilin_nondegenerate : (spBilin m).Nondegenerate :=
  CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate

theorem spBilin_self (x : SpMod m) : spBilin m x x = 0 :=
  CFSG.ClassicalGroups.Symplectic.spForm_self x

theorem spForm_perp_eq_orthogonal (W : Submodule (GaloisField 2 1) (SpMod m)) :
    (spForm m (GaloisField 2 1)).perp W = (spBilin m).orthogonal W := by
  ext v
  rw [ReflForm.mem_perp, LinearMap.BilinForm.mem_orthogonal_iff]
  exact forall₂_congr fun w _ => by rw [← spB_eq_spForm, spB_eq_spBilin]

theorem spB_symm (x y : SpMod m) : spB m x y = spB m y x := by
  rw [spB_eq_spBilin, spB_eq_spBilin]
  rw [← CharTwo.neg_eq (spBilin m x y)]
  exact (CFSG.ClassicalGroups.Symplectic.spForm_isAlt).neg_eq x y

theorem spB_smul_left (c : GaloisField 2 1) (x y : SpMod m) :
    spB m (c • x) y = c * spB m x y := by
  simp only [spB_eq_spBilin]
  exact (spBilin m).smul_left c x y

theorem spSiegel_apply {x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s) (v : SpMod m) :
    spAct s v = v + spB m v y • x + spB m v x • y := by
  rw [hs v, spB_symm (m := m) y v, spB_symm (m := m) x v]

noncomputable def spAltMap (x y : SpMod m) : SpMod m →ₗ[GaloisField 2 1] SpMod m :=
  ((spBilin m).flip y).smulRight x + ((spBilin m).flip x).smulRight y

theorem spAltMap_apply (x y v : SpMod m) :
    spAltMap x y v = spB m v y • x + spB m v x • y := by
  have h : spAltMap x y v = spBilin m v y • x + spBilin m v x • y := by
    simp only [spAltMap, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.BilinForm.flip_apply]
  rw [h, ← spB_eq_spBilin, ← spB_eq_spBilin]

theorem spAdd_self_eq_zero (v : SpMod m) : v + v = 0 := by
  rw [← two_smul (GaloisField 2 1) v,
    show (2 : GaloisField 2 1) = 0 from CharP.cast_eq_zero _ 2, zero_smul]

theorem spAltMap_self (x : SpMod m) : spAltMap x x = 0 := by
  apply LinearMap.ext
  intro v
  rw [spAltMap_apply]
  simpa only [LinearMap.zero_apply] using spAdd_self_eq_zero (spB m v x • x)

theorem spAltMap_add_left (x x' y : SpMod m) :
    spAltMap (x + x') y = spAltMap x y + spAltMap x' y := by
  apply LinearMap.ext
  intro v
  simp only [spAltMap, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.BilinForm.flip_apply, (spBilin m).add_right, add_smul, smul_add]
  abel

theorem spAltMap_smul_left (c : GaloisField 2 1) (x y : SpMod m) :
    spAltMap (c • x) y = c • spAltMap x y := by
  apply LinearMap.ext
  intro v
  rw [spAltMap_apply, LinearMap.smul_apply, spAltMap_apply, spB_smul_right, smul_add,
    smul_smul, smul_smul, smul_smul, mul_comm (spB m v y) c]

theorem spAltMap_add_right (x y y' : SpMod m) :
    spAltMap x (y + y') = spAltMap x y + spAltMap x y' := by
  apply LinearMap.ext
  intro v
  simp only [spAltMap, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.BilinForm.flip_apply, (spBilin m).add_right, add_smul, smul_add]
  abel

theorem spAltMap_smul_right (c : GaloisField 2 1) (x y : SpMod m) :
    spAltMap x (c • y) = c • spAltMap x y := by
  apply LinearMap.ext
  intro v
  rw [spAltMap_apply, LinearMap.smul_apply, spAltMap_apply, spB_smul_right, smul_add,
    smul_smul, smul_smul, smul_smul, mul_comm (spB m v x) c]

theorem spAltMap_comm (x y : SpMod m) : spAltMap x y = spAltMap y x := by
  apply LinearMap.ext
  intro v
  rw [spAltMap_apply, spAltMap_apply, add_comm]

theorem spAltMap_natRep {x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s) :
    natRep (StatedSp m (GaloisField 2 1)) s = 1 + spAltMap x y := by
  apply LinearMap.ext
  intro v
  rw [← spAct_eq_natRep, spSiegel_apply hs v]
  simp only [spAltMap_apply, LinearMap.add_apply, Module.End.one_apply]
  abel

theorem spAltMap_eq_smul_of_mem_span {a b x y : SpMod m}
    (hx : x ∈ Submodule.span (GaloisField 2 1) {a, b})
    (hy : y ∈ Submodule.span (GaloisField 2 1) {a, b}) :
    ∃ c : GaloisField 2 1, spAltMap x y = c • spAltMap a b := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  refine ⟨α * δ + β * γ, ?_⟩
  simp only [spAltMap_add_left, spAltMap_smul_left, spAltMap_add_right, spAltMap_smul_right,
    smul_smul, spAltMap_self, spAltMap_comm (x := b) (y := a), smul_zero, add_zero, zero_add,
    ← add_smul]
  rw [show γ * β + δ * α = α * δ + β * γ by ring]

theorem spAltMap_eq_of_span_eq {a b x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s)
    (hs1 : s ≠ 1) (hspan : Submodule.span (GaloisField 2 1) {x, y} =
      Submodule.span (GaloisField 2 1) {a, b}) :
    spAltMap x y = spAltMap a b := by
  have hx : x ∈ Submodule.span (GaloisField 2 1) {a, b} :=
    hspan ▸ Submodule.subset_span (by simp)
  have hy : y ∈ Submodule.span (GaloisField 2 1) {a, b} :=
    hspan ▸ Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := spAltMap_eq_smul_of_mem_span hx hy
  have hcne : c ≠ 0 := by
    intro hc0
    have h0 : spAltMap x y = 0 := by rw [hc, hc0, zero_smul]
    have hnat : natRep (StatedSp m (GaloisField 2 1)) s = 1 := by
      rw [spAltMap_natRep hs, h0, add_zero]
    exact hs1 (natRep_injective (StatedSp m (GaloisField 2 1)) (by simpa using hnat))
  have hc1 : c = 1 := by
    rcases rck1416_gf2_eq_zero_or_one c with h | h
    · exact absurd h hcne
    · exact h
  rw [hc, hc1, one_smul]

theorem spSiegel_eq_of_span_eq {a b x y : SpMod m} {r s : SpG m}
    (hr : SpSiegel a b r) (hr1 : r ≠ 1) (hs : SpSiegel x y s) (hs1 : s ≠ 1)
    (hspan : Submodule.span (GaloisField 2 1) {x, y} =
      Submodule.span (GaloisField 2 1) {a, b}) : r = s := by
  have hM : spAltMap x y = spAltMap a b := spAltMap_eq_of_span_eq hs hs1 hspan
  have h : natRep (StatedSp m (GaloisField 2 1)) r =
      natRep (StatedSp m (GaloisField 2 1)) s := by
    rw [spAltMap_natRep hr, spAltMap_natRep hs, hM]
  exact natRep_injective (StatedSp m (GaloisField 2 1)) h

theorem spSiegel_li_pair (x y : SpMod m) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent (GaloisField 2 1) ![x, y] := by
  rw [LinearIndependent.pair_iff' hx]
  intro a ha
  rcases rck1416_gf2_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul] at ha
    exact hy ha.symm
  · rw [one_smul] at ha
    exact hxy ha

theorem spSiegel_li {x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s) (hs1 : s ≠ 1) :
    LinearIndependent (GaloisField 2 1) ![x, y] := by
  have h : ¬(x = 0 ∨ y = 0 ∨ x = y) := by
    intro h
    exact hs1 ((spSiegel_eq_one_iff hs).mpr h)
  push Not at h
  exact spSiegel_li_pair x y h.1 h.2.1 h.2.2

theorem spSiegel_beta_moved {x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s) (v : SpMod m) :
    spB m v (spAct s v - v) = 0 := by
  rw [spSiegel_apply hs v]
  have hsub : v + spB m v y • x + spB m v x • y - v =
      spB m v y • x + spB m v x • y := by abel
  rw [hsub, spB_add_right, spB_smul_right, spB_smul_right,
    mul_comm (spB m v y) (spB m v x)]
  exact CharTwo.add_self_eq_zero _

theorem exists_spDualPair (x y : SpMod m)
    (hli : LinearIndependent (GaloisField 2 1) ![x, y]) (hB : spB m x y = 0) :
    ∃ c d : SpMod m, spB m x c = 1 ∧ spB m y c = 0 ∧ spB m x d = 0 ∧ spB m y d = 1 ∧
      spB m c d = 0 := by
  classical
  have hnd : (spBilin m).Nondegenerate := spBilin_nondegenerate
  let B := Module.Basis.sumExtend hli
  let f₁ : SpMod m →ₗ[GaloisField 2 1] GaloisField 2 1 :=
    B.constr (GaloisField 2 1) fun i => match i with
      | Sum.inl j => if j = 0 then 1 else 0
      | Sum.inr _ => 0
  let f₂ : SpMod m →ₗ[GaloisField 2 1] GaloisField 2 1 :=
    B.constr (GaloisField 2 1) fun i => match i with
      | Sum.inl j => if j = 1 then 1 else 0
      | Sum.inr _ => 0
  let c₀ : SpMod m := (LinearMap.BilinForm.toDual (spBilin m) hnd).symm f₁
  let d₀ : SpMod m := (LinearMap.BilinForm.toDual (spBilin m) hnd).symm f₂
  have hBx : B (Sum.inl 0) = x := by
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
      Module.Basis.extend_apply_self]
    rfl
  have hBy : B (Sum.inl 1) = y := by
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
      Module.Basis.extend_apply_self]
    rfl
  have hf₁x : f₁ x = 1 := by
    rw [← hBx]
    change (B.constr (GaloisField 2 1) _) (B (Sum.inl 0)) = 1
    rw [Module.Basis.constr_basis]
    simp
  have hf₁y : f₁ y = 0 := by
    rw [← hBy]
    change (B.constr (GaloisField 2 1) _) (B (Sum.inl 1)) = 0
    rw [Module.Basis.constr_basis]
    simp
  have hf₂x : f₂ x = 0 := by
    rw [← hBx]
    change (B.constr (GaloisField 2 1) _) (B (Sum.inl 0)) = 0
    rw [Module.Basis.constr_basis]
    simp
  have hf₂y : f₂ y = 1 := by
    rw [← hBy]
    change (B.constr (GaloisField 2 1) _) (B (Sum.inl 1)) = 1
    rw [Module.Basis.constr_basis]
    simp
  have hc₀x : spB m c₀ x = 1 := by
    rw [spB_eq_spBilin]
    have h : LinearMap.BilinForm.toDual (spBilin m) hnd c₀ = f₁ :=
      LinearEquiv.apply_symm_apply _ _
    calc spBilin m c₀ x = LinearMap.BilinForm.toDual (spBilin m) hnd c₀ x :=
          (LinearMap.BilinForm.toDual_def hnd).symm
      _ = f₁ x := by rw [h]
      _ = 1 := hf₁x
  have hc₀y : spB m c₀ y = 0 := by
    rw [spB_eq_spBilin]
    have h : LinearMap.BilinForm.toDual (spBilin m) hnd c₀ = f₁ :=
      LinearEquiv.apply_symm_apply _ _
    calc spBilin m c₀ y = LinearMap.BilinForm.toDual (spBilin m) hnd c₀ y :=
          (LinearMap.BilinForm.toDual_def hnd).symm
      _ = f₁ y := by rw [h]
      _ = 0 := hf₁y
  have hd₀x : spB m d₀ x = 0 := by
    rw [spB_eq_spBilin]
    have h : LinearMap.BilinForm.toDual (spBilin m) hnd d₀ = f₂ :=
      LinearEquiv.apply_symm_apply _ _
    calc spBilin m d₀ x = LinearMap.BilinForm.toDual (spBilin m) hnd d₀ x :=
          (LinearMap.BilinForm.toDual_def hnd).symm
      _ = f₂ x := by rw [h]
      _ = 0 := hf₂x
  have hd₀y : spB m d₀ y = 1 := by
    rw [spB_eq_spBilin]
    have h : LinearMap.BilinForm.toDual (spBilin m) hnd d₀ = f₂ :=
      LinearEquiv.apply_symm_apply _ _
    calc spBilin m d₀ y = LinearMap.BilinForm.toDual (spBilin m) hnd d₀ y :=
          (LinearMap.BilinForm.toDual_def hnd).symm
      _ = f₂ y := by rw [h]
      _ = 1 := hf₂y
  refine ⟨c₀ + spB m c₀ d₀ • y, d₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spB_symm (m := m) x (c₀ + spB m c₀ d₀ • y), spB_add_left, spB_smul_left,
      spB_symm (m := m) y x, hB, mul_zero, add_zero]
    exact hc₀x
  · rw [spB_symm (m := m) y (c₀ + spB m c₀ d₀ • y), spB_add_left, spB_smul_left, spB_self,
      mul_zero, add_zero]
    exact hc₀y
  · rw [spB_symm (m := m) x d₀]
    exact hd₀x
  · rw [spB_symm (m := m) y d₀]
    exact hd₀y
  · rw [spB_add_left, spB_smul_left, spB_symm (m := m) y d₀, hd₀y, mul_one]
    exact CharTwo.add_self_eq_zero _

theorem spAltMap_range (x y : SpMod m)
    (hli : LinearIndependent (GaloisField 2 1) ![x, y]) (hB : spB m x y = 0) :
    LinearMap.range (spAltMap x y) = Submodule.span (GaloisField 2 1) {x, y} := by
  obtain ⟨c, d, hxc, hyc, hxd, hyd, -⟩ := exists_spDualPair x y hli hB
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [spAltMap_apply]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact ⟨d, by
        rw [spAltMap_apply, spB_symm (m := m) d y, spB_symm (m := m) d x, hyd, hxd,
          one_smul, zero_smul, add_zero]⟩
    · rw [hz]
      exact ⟨c, by
        rw [spAltMap_apply, spB_symm (m := m) c y, spB_symm (m := m) c x, hyc, hxc,
          zero_smul, one_smul, zero_add]⟩

theorem spSiegel_range {x y : SpMod m} {s : SpG m} (hs : SpSiegel x y s) (hs1 : s ≠ 1)
    (hB : spB m x y = 0) :
    LinearMap.range (natRep (StatedSp m (GaloisField 2 1)) s - 1) =
      Submodule.span (GaloisField 2 1) {x, y} := by
  have hli : LinearIndependent (GaloisField 2 1) ![x, y] := spSiegel_li hs hs1
  have hsub : natRep (StatedSp m (GaloisField 2 1)) s - 1 = spAltMap x y := by
    rw [spAltMap_natRep hs, add_sub_cancel_left]
  rw [hsub, spAltMap_range x y hli hB]

theorem spAltMap_ker (x y : SpMod m)
    (hli : LinearIndependent (GaloisField 2 1) ![x, y]) :
    LinearMap.ker (spAltMap x y) =
      (spBilin m).orthogonal (Submodule.span (GaloisField 2 1) {x, y}) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hv
    have hcoef : spB m v y = 0 ∧ spB m v x = 0 := by
      have h0 : spB m v y • x + spB m v x • y = 0 := by
        rw [← spAltMap_apply]
        exact hv
      exact (LinearIndependent.pair_iff.mp hli) (spB m v y) (spB m v x) h0
    intro w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [(spBilin m).add_left, (spBilin m).smul_left, (spBilin m).smul_left,
      show spBilin m x v = 0 by rw [← spB_eq_spBilin, spB_symm]; exact hcoef.2,
      show spBilin m y v = 0 by rw [← spB_eq_spBilin, spB_symm]; exact hcoef.1]
    simp
  · intro hv
    rw [spAltMap_apply]
    have hx0 : spB m x v = 0 := by
      rw [spB_eq_spBilin]
      exact hv x (Submodule.subset_span (by simp))
    have hy0 : spB m y v = 0 := by
      rw [spB_eq_spBilin]
      exact hv y (Submodule.subset_span (by simp))
    rw [spB_symm (m := m) v y, spB_symm (m := m) v x, hy0, hx0, zero_smul, zero_smul,
      add_zero]

theorem spForm_totallyIsotropic_span (x y : SpMod m) (hB : spB m x y = 0) :
    (spForm m (GaloisField 2 1)).IsTotallyIsotropic
      (Submodule.span (GaloisField 2 1) {x, y}) := by
  have hxx : spBilin m x x = 0 := spBilin_self x
  have hyy : spBilin m y y = 0 := spBilin_self y
  have hxy : spBilin m x y = 0 := by rw [← spB_eq_spBilin]; exact hB
  have hyx : spBilin m y x = 0 := by rw [← spB_eq_spBilin, spB_symm]; exact hB
  rw [ReflForm.IsTotallyIsotropic, spForm_perp_eq_orthogonal, Submodule.span_le]
  intro z hz
  change z ∈ (spBilin m).orthogonal (Submodule.span (GaloisField 2 1) {x, y})
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rcases hz with hz | hz
  · rw [hz]
    refine Submodule.span_induction (p := fun w _ => spBilin m w x = 0)
      (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hw
    · intro w hw
      rcases hw with hw | hw
      · rw [hw]; exact hxx
      · rw [hw]; exact hyx
    · simp
    · intro a b _ _ ha hb
      rw [LinearMap.BilinForm.add_left, ha, hb, add_zero]
    · intro r a _ ha
      rw [LinearMap.BilinForm.smul_left, ha, mul_zero]
  · rw [hz]
    refine Submodule.span_induction (p := fun w _ => spBilin m w y = 0)
      (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hw
    · intro w hw
      rcases hw with hw | hw
      · rw [hw]; exact hxy
      · rw [hw]; exact hyy
    · simp
    · intro a b _ _ ha hb
      rw [LinearMap.BilinForm.add_left, ha, hb, add_zero]
    · intro r a _ ha
      rw [LinearMap.BilinForm.smul_left, ha, mul_zero]

theorem spPlanePair_of_isoPair (x y : SpMod m)
    (hli : LinearIndependent (GaloisField 2 1) ![x, y]) (hB : spB m x y = 0) :
    ∃ c d : SpMod m, SpPlanePair m (GaloisField 2 1) x y c d := by
  obtain ⟨c, d, hxc, hyc, hxd, hyd, hcd⟩ := exists_spDualPair x y hli hB
  refine ⟨c, d, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [spB, spJ] using hxc
  · simpa only [spB, spJ] using hyd
  · simpa only [spB, spJ] using hB
  · simpa only [spB, spJ] using hcd
  · simpa only [spB, spJ] using hxd
  · simpa only [spB, spJ] using hyc

end CFSG.StandardType.RCKC1

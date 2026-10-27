module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.TablePair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

open HardMathSupport.Kantor79

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem apply_basis_eq_of_toMatrix_diagSignMat {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {g : U ≃ₗ[ZMod p] U} {i : Fin n}
    (hg : LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) (j : Fin n) :
    g (f j) = (if j = i then (-1 : ZMod p) else 1) • f j := by
  apply f.repr.injective
  ext k
  change (f.repr ((g : U →ₗ[ZMod p] U) (f j))) k =
    (f.repr ((if j = i then (-1 : ZMod p) else 1) • f j)) k
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    ← LinearMap.toMatrix_apply f f (g : U →ₗ[ZMod p] U) k j, hg]
  rw [diagSignMat, Matrix.diagonal_apply]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · simp [hk]

private theorem movedSpace_eq_span_of_toMatrix_diagSignMat {n : ℕ} (hp2 : p ≠ 2)
    (f : Module.Basis (Fin n) (ZMod p) U) {g : U ≃ₗ[ZMod p] U} {i : Fin n}
    (hg : LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) :
    HardMathSupport.Kantor79.movedSpace g = Submodule.span (ZMod p) {f i} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hgfj := apply_basis_eq_of_toMatrix_diagSignMat (p := p) f hg
  change LinearMap.range ((g : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f i}
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    have hv : g v - v = ∑ j, (f.repr v j) • (g (f j) - f j) := by
      conv_lhs => rw [← f.sum_repr v]
      rw [map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_sub]
    change g v - v ∈ Submodule.span (ZMod p) {f i}
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · rw [hgfj j, if_pos hj]
      rw [show (-1 : ZMod p) • f j - f j = (-2 : ZMod p) • f j by module]
      rw [hj]
      exact Submodule.smul_mem (Submodule.span (ZMod p) {f i}) ((f.repr v) i)
        (Submodule.smul_mem (Submodule.span (ZMod p) {f i}) (-2 : ZMod p)
          (Submodule.subset_span (Set.mem_singleton (f i))))
    · rw [hgfj j, if_neg hj, one_smul, sub_self, smul_zero]
      exact Submodule.zero_mem _
  · rw [Submodule.span_singleton_le_iff_mem]
    have hmem : g (f i) - f i ∈ HardMathSupport.Kantor79.movedSpace g := ⟨f i, rfl⟩
    rw [hgfj i, if_pos rfl] at hmem
    have h2fi : (-2 : ZMod p) • f i ∈ HardMathSupport.Kantor79.movedSpace g := by
      convert hmem using 1
      module
    have hne : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
    rw [show f i = (-2 : ZMod p)⁻¹ • ((-2 : ZMod p) • f i) by rw [inv_smul_smul₀ hne]]
    exact Submodule.smul_mem _ _ h2fi

private theorem repr_blockSucc_sub_f1_ne_zero (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (f : Module.Basis (Fin 4) (ZMod p) U) {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    f.repr (a (f 1) - f 1) 2 ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h1a : (1 + α : ZMod p) ≠ 0 := by
    intro h
    have hα1 : α = -1 := by linear_combination h
    rw [hα1] at hα
    simp at hα
  rw [map_sub, Finsupp.sub_apply]
  change (f.repr ((a : U →ₗ[ZMod p] U) (f 1))) 2 - (f.repr (f 1)) 2 ≠ 0
  rw [← LinearMap.toMatrix_apply f f (a : U →ₗ[ZMod p] U) 2 1, ha, Module.Basis.repr_self_apply]
  simp only [show (1 : Fin 4) ≠ 2 by decide, if_false, sub_zero]
  have h21 : (Matrix.blockSucc (h3BlockMat α)) 2 1 = (h3BlockMat α) 2 1 := by
    rw [show (2 : Fin 4) = Fin.castSucc (2 : Fin 3) from rfl,
      show (1 : Fin 4) = Fin.castSucc (1 : Fin 3) from rfl,
      Matrix.blockSucc_castSucc_castSucc]
  rw [h21]
  have hmat : (h3BlockMat α) 2 1 = (2 : ZMod p)⁻¹ * (-(1 + α)) := rfl
  rw [hmat]
  exact mul_ne_zero (inv_ne_zero h2) (neg_ne_zero.mpr h1a)

private theorem apply_f1_ne_of_toMatrix_blockSucc (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (f : Module.Basis (Fin 4) (ZMod p) U) {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    a (f 1) ≠ f 1 := by
  intro h
  exact repr_blockSucc_sub_f1_ne_zero hp2 hα f ha
    (by rw [h, sub_self, map_zero, Finsupp.zero_apply])

private theorem not_movedSpace_le_span_of_toMatrix_blockSucc (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (f : Module.Basis (Fin 4) (ZMod p) U) {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    ¬ HardMathSupport.Kantor79.movedSpace a ≤ Submodule.span (ZMod p) {f 0} := by
  intro hle
  have hmem : a (f 1) - f 1 ∈ Submodule.span (ZMod p) {f 0} := hle ⟨f 1, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine repr_blockSucc_sub_f1_ne_zero hp2 hα f ha ?_
  rw [← hc, map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
  simp


private theorem reflGen_closure_insert {K : Subgroup (U ≃ₗ[ZMod p] U)} (hK : ReflGen p K)
    {x : U ≃ₗ[ZMod p] U} (hxr : IsRefl p x) :
    ReflGen p (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) := by
  rw [ReflGen] at hK ⊢
  let R : Set (U ≃ₗ[ZMod p] U) :=
    {t | t ∈ Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))) ∧ IsRefl p t}
  change Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))) = Subgroup.closure R
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hxr⟩
    · have hle : K ≤ Subgroup.closure R := by
        rw [hK]
        rw [Subgroup.closure_le]
        intro s hs
        exact Subgroup.subset_closure
          ⟨Subgroup.subset_closure (Set.mem_insert_of_mem x hs.1), hs.2⟩
      exact hle ht
  · rw [Subgroup.closure_le]
    intro t ht
    exact ht.1


private theorem reflGen_closure_pair {a b : U ≃ₗ[ZMod p] U} (har : IsRefl p a) (hbr : IsRefl p b) :
    ReflGen p (Subgroup.closure ({a, b} : Set (U ≃ₗ[ZMod p] U))) := by
  rw [ReflGen]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), har⟩
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hbr⟩
  · rw [Subgroup.closure_le]
    intro t ht
    exact ht.1


namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem reflGen_sup {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKr : ReflGen p K) (hHr : ReflGen p H) : ReflGen p (K ⊔ H) := by
  rw [ReflGen] at hKr hHr ⊢
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · conv_lhs => rw [hKr]
      apply Subgroup.closure_mono
      intro t ht
      exact ⟨Subgroup.mem_sup_left ht.1, ht.2⟩
    · conv_lhs => rw [hHr]
      apply Subgroup.closure_mono
      intro t ht
      exact ⟨Subgroup.mem_sup_right ht.1, ht.2⟩
  · rw [Subgroup.closure_le]
    intro t ht
    exact ht.1

private theorem commutatorSpace_eq_sup_inf_of_isCompl {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hcompl : IsCompl (commutatorSpace K) (centralizerSpace K))
    (hVKleVH : commutatorSpace K ≤ commutatorSpace H) :
    commutatorSpace H = commutatorSpace K ⊔ (commutatorSpace H ⊓ centralizerSpace K) := by
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ commutatorSpace K ⊔ centralizerSpace K := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw'
    have hvH : v ∈ commutatorSpace H := by
      have : v = w - u := by rw [← huv]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (hVKleVH hu)
    exact Submodule.mem_sup.mpr ⟨u, hu, v, ⟨hvH, hv⟩, huv⟩
  · exact sup_le hVKleVH inf_le_left

private theorem map_mem_commutatorSpace_of_mem {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hdecomp : commutatorSpace H =
      commutatorSpace K ⊔ (commutatorSpace H ⊓ centralizerSpace K))
    {k : U ≃ₗ[ZMod p] U} (hk : k ∈ K) {w : U} (hw : w ∈ commutatorSpace H) :
    k w ∈ commutatorSpace H := by
  rw [hdecomp] at hw ⊢
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw
  rw [← huv, map_add]
  refine Submodule.mem_sup.mpr ⟨k u, ?_, k v, ?_, rfl⟩
  · rw [← map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hk)]
    exact Submodule.mem_map_of_mem hu
  · rw [(mem_centralizerSpace.mp hv.2) k hk]
    exact hv

private theorem fix_of_mem_sup {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hVHc_le : centralizerSpace H ≤ centralizerSpace K) :
    ∀ y ∈ K ⊔ H, ∀ w ∈ centralizerSpace H, y w = w := by
  let C : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {y | ∀ w ∈ centralizerSpace H, y w = w},
      mul_mem' := by
        intro a b ha hb w hw
        rw [LinearEquiv.mul_apply, hb w hw, ha w hw],
      one_mem' := by intro w hw; rfl,
      inv_mem' := by
        intro a ha w hw
        have h1 : a⁻¹ (a w) = w := a.symm_apply_apply w
        rwa [ha w hw] at h1 }
  have hsub : K ⊔ H ≤ C := by
    refine sup_le ?_ ?_
    · intro k hk w hw
      exact (mem_centralizerSpace.mp (hVHc_le hw)) k hk
    · intro h hh w hw
      exact (mem_centralizerSpace.mp hw) h hh
  intro y hy
  exact hsub hy

private theorem inv_of_mem_sup [Module.Finite (ZMod p) U] {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKVH : ∀ k ∈ K, ∀ w ∈ commutatorSpace H, k w ∈ commutatorSpace H) :
    ∀ y ∈ K ⊔ H, ∀ w ∈ commutatorSpace H, y w ∈ commutatorSpace H := by
  let D : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {y | ∀ w ∈ commutatorSpace H, y w ∈ commutatorSpace H},
      mul_mem' := by
        intro a b ha hb w hw
        rw [LinearEquiv.mul_apply]
        exact ha _ (hb w hw),
      one_mem' := by intro w hw; simpa using hw,
      inv_mem' := by
        intro a ha w hw
        have hle : (commutatorSpace H).map (a : U →ₗ[ZMod p] U) ≤ commutatorSpace H := by
          rw [Submodule.map_le_iff_le_comap]
          intro v hv
          exact ha v hv
        have heq : (commutatorSpace H).map (a : U →ₗ[ZMod p] U) = commutatorSpace H :=
          Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq a])
        have hw' : w ∈ (commutatorSpace H).map (a : U →ₗ[ZMod p] U) := by rw [heq]; exact hw
        obtain ⟨u, hu, hua⟩ := Submodule.mem_map.mp hw'
        have : a⁻¹ w = u := by
          rw [← hua]
          exact a.symm_apply_apply u
        rw [this]; exact hu }
  have hsub : K ⊔ H ≤ D := by
    refine sup_le ?_ ?_
    · intro k hk w hw
      exact hKVH k hk w hw
    · intro h hh w hw
      exact (map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hh)) ▸
        Submodule.mem_map_of_mem hw
  intro y hy
  exact hsub hy

private theorem finrank_sup_movedSpace_eq_two (hp2 : p ≠ 2) [Module.Finite (ZMod p) U]
    {h₁ a : U ≃ₗ[ZMod p] U} {f : Module.Basis (Fin 4) (ZMod p) U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    {α : ZMod p} (hα : α ^ 2 = α + 1)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hVsup_le : movedSpace h₁ ⊔ movedSpace a ≤ commutatorSpace K) (hKs : SplitSupport K 2) :
    Module.finrank (ZMod p) (movedSpace h₁ ⊔ movedSpace a : Submodule (ZMod p) U) = 2 := by
  have hVh1 : movedSpace h₁ = Submodule.span (ZMod p) {f 0} :=
    movedSpace_eq_span_of_toMatrix_diagSignMat hp2 f hh₁
  have hVa : ¬ movedSpace a ≤ Submodule.span (ZMod p) {f 0} :=
    not_movedSpace_le_span_of_toMatrix_blockSucc hp2 hα f ha
  have hle2 : Module.finrank (ZMod p)
      ((movedSpace h₁ ⊔ movedSpace a : Submodule (ZMod p) U)) ≤ 2 := by
    rw [← hKs.2.1]
    exact Submodule.finrank_mono hVsup_le
  have hlt : movedSpace h₁ < (movedSpace h₁ ⊔ movedSpace a : Submodule (ZMod p) U) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact hVa (by rw [← hVh1, heq]; exact le_sup_right)
  have hge2 : 2 ≤ Module.finrank (ZMod p)
      ((movedSpace h₁ ⊔ movedSpace a : Submodule (ZMod p) U)) := by
    have h1 : Module.finrank (ZMod p) (movedSpace h₁) = 1 := by
      rw [hVh1, finrank_span_singleton (f.ne_zero 0)]
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  omega

private theorem finrank_centralizer_closure_pair_le_two (hp2 : p ≠ 2)
    [Module.Finite (ZMod p) U] {h₁ a : U ≃ₗ[ZMod p] U}
    {f : Module.Basis (Fin 4) (ZMod p) U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    {α : ZMod p} (hα : α ^ 2 = α + 1)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    Module.finrank (ZMod p) (centralizerSpace (Subgroup.closure {h₁, a})) ≤ 2 := by
  have hfinU : Module.finrank (ZMod p) U = 4 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hVh1 : movedSpace h₁ = Submodule.span (ZMod p) {f 0} :=
    movedSpace_eq_span_of_toMatrix_diagSignMat hp2 f hh₁
  have hker1 : Module.finrank (ZMod p) (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) = 3 := by
    have hsum : Module.finrank (ZMod p) (movedSpace h₁) +
        Module.finrank (ZMod p) (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) =
        Module.finrank (ZMod p) U := LinearMap.finrank_range_add_finrank_ker _
    rw [hVh1, finrank_span_singleton (f.ne_zero 0), hfinU] at hsum
    omega
  have hf1_mem : f 1 ∈ LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1) := by
    rw [LinearMap.mem_ker]
    change h₁ (f 1) - f 1 = 0
    rw [apply_basis_eq_of_toMatrix_diagSignMat f hh₁ 1]
    simp [show (1 : Fin 4) ≠ 0 by decide]
  have hf1_not : f 1 ∉ centralizerSpace (Subgroup.closure {h₁, a}) := by
    intro hv
    have hfix : a (f 1) = f 1 :=
      (mem_centralizerSpace.mp hv) a (Subgroup.subset_closure (by simp))
    exact apply_f1_ne_of_toMatrix_blockSucc hp2 hα f ha hfix
  have hVH₀_le_ker : centralizerSpace (Subgroup.closure {h₁, a}) ≤
      LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1) := by
    intro v hv
    rw [LinearMap.mem_ker]
    change h₁ v - v = 0
    rw [(mem_centralizerSpace.mp hv) h₁ (Subgroup.subset_closure (by simp)), sub_self]
  have hlt : centralizerSpace (Subgroup.closure {h₁, a}) <
      LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1) := by
    refine lt_of_le_of_ne hVH₀_le_ker ?_
    intro heq
    exact hf1_not (heq ▸ hf1_mem)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

private theorem centralizerSpace_eq_of_splitSupport_two (hp2 : p ≠ 2)
    [Module.Finite (ZMod p) U] {h₁ a : U ≃ₗ[ZMod p] U}
    {f : Module.Basis (Fin 4) (ZMod p) U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    {α : ZMod p} (hα : α ^ 2 = α + 1)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hH₀K : Subgroup.closure {h₁, a} ≤ K)
    (hKs : SplitSupport K 2) :
    centralizerSpace K = centralizerSpace (Subgroup.closure {h₁, a}) := by
  have hfinU : Module.finrank (ZMod p) U = 4 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hVKc_le : centralizerSpace K ≤ centralizerSpace (Subgroup.closure {h₁, a}) := by
    intro v hv
    exact (mem_centralizerSpace).mpr fun h hh => (mem_centralizerSpace.mp hv) h (hH₀K hh)
  have hfinVKc : Module.finrank (ZMod p) (centralizerSpace K) = 2 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (commutatorSpace K) (centralizerSpace K)
    rw [hKs.1.sup_eq_top, hKs.1.inf_eq_bot, finrank_top, finrank_bot, add_zero] at hsum
    rw [hKs.2.1, hfinU] at hsum
    omega
  have hVH₀c_le2 := finrank_centralizer_closure_pair_le_two hp2 hh₁ hα ha
  refine Submodule.eq_of_le_of_finrank_eq hVKc_le ?_
  have hmono := Submodule.finrank_mono hVKc_le
  omega

private theorem exists_moved_of_h3Pair (hp2 : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {h₁ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    {K H : Subgroup (U ≃ₗ[ZMod p] U)} (hh₁K : h₁ ∈ K)
    (hVKleVH : commutatorSpace K ≤ commutatorSpace H)
    (hVh1 : movedSpace h₁ = Submodule.span (ZMod p) {f 0}) :
    ∃ y ∈ K ⊔ H, ∃ w ∈ commutatorSpace H, y w ≠ w := by
  refine ⟨h₁, Subgroup.mem_sup_left hh₁K, f 0, ?_, ?_⟩
  · exact hVKleVH (movedSpace_le_commutatorSpace hh₁K
      (by rw [hVh1]; exact Submodule.subset_span (Set.mem_singleton (f 0))))
  · rw [apply_basis_eq_of_toMatrix_diagSignMat f hh₁ 0]
    simp only [if_true]
    intro hcontra
    have h2f : (2 : ZMod p) • f 0 = 0 := by
      have hneg : f 0 = -f 0 := by simpa [neg_one_smul] using hcontra.symm
      rw [two_smul]
      nth_rewrite 1 [hneg]
      rw [neg_add_cancel]
    rcases (smul_eq_zero.mp h2f) with h2 | hf
    · exact (ZMod.prime_ne_zero p 2 hp2) h2
    · exact (f.ne_zero 0) hf

private theorem splitSupport_sup_three (hp2 : p ≠ 2) [Module.Finite (ZMod p) U]
    {f : Module.Basis (Fin 4) (ZMod p) U} {h₁ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    {K H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hKs : SplitSupport K 2) (hfinU : Module.finrank (ZMod p) U = 4)
    (hh₁K : h₁ ∈ K) (hVh1 : movedSpace h₁ = Submodule.span (ZMod p) {f 0})
    (hVKleVH : commutatorSpace K ≤ commutatorSpace H)
    (hVHc_le : centralizerSpace H ≤ centralizerSpace K) :
    SplitSupport (K ⊔ H) 3 := by
  have hVHdecomp : commutatorSpace H =
      commutatorSpace K ⊔ (commutatorSpace H ⊓ centralizerSpace K) :=
    commutatorSpace_eq_sup_inf_of_isCompl hKs.1 hVKleVH
  have hKVH : ∀ k ∈ K, ∀ w ∈ commutatorSpace H, k w ∈ commutatorSpace H :=
    fun k hk w hw => map_mem_commutatorSpace_of_mem hVHdecomp hk hw
  have hfixY := fix_of_mem_sup hVHc_le
  have hinvY := inv_of_mem_sup hKVH
  have hirrY : IrredOnSection (K ⊔ H) ⊥ (commutatorSpace H) := by
    intro X hXbot hXle hXinv
    exact hHs.2.2 X hXbot hXle fun h hh x hx => hXinv h (Subgroup.mem_sup_right hh) x hx
  have hneY := exists_moved_of_h3Pair hp2 hh₁ hh₁K hVKleVH hVh1
  have h := splitSupport_of_isCompl (B := K ⊔ H)
    (W := commutatorSpace H) (W' := centralizerSpace H)
    hHs.1 hfixY hinvY hirrY hneY
  rwa [hHs.2.1, hfinU] at h

private theorem closure_pair_le_of_h3Mats {α : ZMod p} {f : Module.Basis (Fin 4) (ZMod p) U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hfH : H = basisClosure f (h3Mats α))
    {h₁ a : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    Subgroup.closure {h₁, a} ≤ H := by
  have hh₁H : h₁ ∈ H := by
    rw [hfH]
    refine Subgroup.subset_closure ?_
    change LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) ∈ h3Mats α
    rw [hh₁]
    exact ⟨(diagSignMat 0 : Matrix (Fin 3) (Fin 3) (ZMod p)), by simp [h3BlockMats],
      by simpa using blockSucc_diagSignMat (n := 3) (0 : Fin 3)⟩
  have haH : a ∈ H := by
    rw [hfH]
    refine Subgroup.subset_closure ?_
    change LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) ∈ h3Mats α
    rw [ha]
    exact ⟨h3BlockMat α, by simp [h3BlockMats], rfl⟩
  rw [Subgroup.closure_le]
  intro t ht
  rcases ht with rfl | rfl
  · exact hh₁H
  · exact haH

private theorem h3Pair_commutator_data (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 4) (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {h₁ a : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hH₀K : Subgroup.closure {h₁, a} ≤ K)
    (hH₀H : Subgroup.closure {h₁, a} ≤ H) (hKs : SplitSupport K 2) :
    p ≠ 2 ∧ Module.finrank (ZMod p) U = 4 ∧ h₁ ∈ K ∧
      movedSpace h₁ = Submodule.span (ZMod p) {f 0} ∧
      commutatorSpace K = movedSpace h₁ ⊔ movedSpace a ∧
      commutatorSpace K ≤ commutatorSpace H ∧ centralizerSpace H ≤ centralizerSpace K := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hfinU : Module.finrank (ZMod p) U = 4 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hh₁K : h₁ ∈ K := hH₀K (Subgroup.subset_closure (by simp))
  have haK : a ∈ K := hH₀K (Subgroup.subset_closure (by simp))
  have hVsup_le : movedSpace h₁ ⊔ movedSpace a ≤ commutatorSpace K :=
    sup_le (movedSpace_le_commutatorSpace hh₁K) (movedSpace_le_commutatorSpace haK)
  have hVh1 : movedSpace h₁ = Submodule.span (ZMod p) {f 0} :=
    movedSpace_eq_span_of_toMatrix_diagSignMat hp2 f hh₁
  have hVK : commutatorSpace K = movedSpace h₁ ⊔ movedSpace a :=
    (Submodule.eq_of_le_of_finrank_eq hVsup_le
      (by rw [finrank_sup_movedSpace_eq_two hp2 hh₁ hα ha hVsup_le hKs, hKs.2.1])).symm
  have hVKleVH : commutatorSpace K ≤ commutatorSpace H := by
    rw [hVK]
    exact sup_le (movedSpace_le_commutatorSpace (hH₀H (Subgroup.subset_closure (by simp))))
      (movedSpace_le_commutatorSpace (hH₀H (Subgroup.subset_closure (by simp))))
  have hVKc : centralizerSpace K = centralizerSpace (Subgroup.closure {h₁, a}) :=
    centralizerSpace_eq_of_splitSupport_two hp2 hh₁ hα ha hH₀K hKs
  have hVHc_le : centralizerSpace H ≤ centralizerSpace K := by
    rw [hVKc]
    intro v hv
    exact (mem_centralizerSpace).mpr fun h hh => (mem_centralizerSpace.mp hv) h (hH₀H hh)
  exact ⟨hp2, hfinU, hh₁K, hVh1, hVK, hVKleVH, hVHc_le⟩

private theorem le_closure_pair_of_tfH3Pair (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    [Module.Finite (ZMod p) U] {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 4) (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hfH : H = basisClosure f (h3Mats α)) {h₁ a : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hKr : ReflGen p K) (hKH : K ≤ H)
    (hVK : commutatorSpace K = movedSpace h₁ ⊔ movedSpace a) (hpair : TFH3Pair p) :
    K ≤ Subgroup.closure {h₁, a} := by
  rw [hKr, Subgroup.closure_le]
  intro t ht
  have htH : t ∈ basisClosure f (h3Mats α) := by rw [← hfH]; exact hKH ht.1
  have hmov : movedSpace t ≤ (movedSpace h₁ ⊔ movedSpace a : Submodule (ZMod p) U) := by
    rw [← hVK]
    exact movedSpace_le_commutatorSpace ht.1
  exact hpair U f α hp2 hp5 hα h₁ a hh₁ ha t htH ht.2 hmov

theorem eq_closure_h3Pair_of_le (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 5) (hpair : TFH3Pair p) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hfH : H = basisClosure f (h3Mats α))
    {h₁ a : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hKG : K ≤ G) (hH₀K : Subgroup.closure {h₁, a} ≤ K)
    (hKr : ReflGen p K) (hKs : SplitSupport K 2) : K = Subgroup.closure {h₁, a} := by
  have hH₀H : Subgroup.closure {h₁, a} ≤ H := closure_pair_le_of_h3Mats hfH hh₁ ha
  obtain ⟨hp2, hfinU, hh₁K, hVh1, hVK, hVKleVH, hVHc_le⟩ :=
    h3Pair_commutator_data hp5 hα hh₁ ha hH₀K hH₀H hKs
  have hYr : ReflGen p (K ⊔ H) := reflGen_sup hKr S.reflGen_H
  have hYs : SplitSupport (K ⊔ H) 3 :=
    splitSupport_sup_three hp2 hh₁ S.splitSupport hKs hfinU hh₁K hVh1 hVKleVH hVHc_le
  have hYH : K ⊔ H = H :=
    S.eq_of_le (sup_le hKG S.H_le) le_sup_right hYr (by rw [hfinU]; exact hYs)
  have hKH : K ≤ H := by rw [← hYH]; exact le_sup_left
  exact le_antisymm
    (le_closure_pair_of_tfH3Pair hp2 hp5 hα hfH hh₁ ha hKr hKH hVK hpair) hH₀K


private theorem splitSupport_closure_insert_of_reflGen [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hdeg : DegenerateInput p G 2) (hp2 : p ≠ 2)
    (hp5 : 5 < p) (hrefl : ReflGen p G) (htf : QTwoLin.TransvectionFree G)
    (hab : AbsIrred p G) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G)
    (hn4 : 2 + 2 ≤ Module.finrank (ZMod p) U)
    (hdmax : ∀ x ∈ G, ∀ y ∈ G, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 5)
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hKG : K ≤ G) (hKr : ReflGen p K) (hKs : SplitSupport K 2)
    (hmax : ∀ K' ≤ G, K ≤ K' → ReflGen p K' → SplitSupport K' 2 → K' = K)
    (hd : ∃ x ∈ K, ∃ y ∈ K, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : ¬ ∃ h ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set (U ≃ₗ[ZMod p] U)), x = h * c) :
    SplitSupport (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) 3 := by
  have hres := hdeg hp2 hrefl htf hab hprim hn4 K hKG hKr hKs hmax hd x hx hxr hxK
  rcases hres with hres | hres
  · exact hres
  · exfalso
    obtain ⟨⟨x', hx', y', hy', hx'r, hy'r, hxy'⟩, _⟩ := hres
    have hFG : Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
      rw [Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | ht
      · exact hx
      · exact hKG ht
    have hle := hdmax x' (hFG hx') y' (hFG hy') hx'r hy'r
    rw [hxy'] at hle
    omega


theorem splitSupport_closure_insert_pair [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    (hp5 : 5 < p) (hn : Module.finrank (ZMod p) U = 4) (hdeg : DegenerateInput p G 2)
    {a b x : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (hb : b ∈ G) (har : IsRefl p a) (hbr : IsRefl p b)
    (hab : orderOf (a * b) = 5)
    (hmax : ∀ K ≤ G, Subgroup.closure {a, b} ≤ K → ReflGen p K → SplitSupport K 2 →
      K = Subgroup.closure {a, b})
    (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : ¬ ∃ h ∈ Subgroup.closure {a, b}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)), x = h * c) :
    SplitSupport (Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U))))
      3 := by
  have hp2 : p ≠ 2 := by omega
  refine splitSupport_closure_insert_of_reflGen hdeg hp2 hp5 S.reflGen S.transvectionFree
    S.absIrred S.primitive (by omega) S.dmax.1 ?_ ?_ ?_ ?_ ?_ hx hxr hxK
  · rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact ha
    · exact hb
  · exact reflGen_closure_pair har hbr
  · refine splitSupport_closure_pair hp2 har hbr ?_ ?_
    · rw [hab, Nat.coprime_comm]
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        omega)
    · rw [hab]; norm_num
  · intro K' hK'G hle hK'r hK's
    exact hmax K' hK'G hle hK'r hK's
  · exact ⟨a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp),
      har, hbr, by rw [hab]; norm_num⟩


private theorem lemmaThreeTwo_F_refl [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    (hp5 : 5 < p) (hn : Module.finrank (ZMod p) U = 4) (hdeg : DegenerateInput p G 2)
    {a b x : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (hb : b ∈ G)
    (har : IsRefl p a) (hbr : IsRefl p b) (hab : orderOf (a * b) = 5)
    (hmax : ∀ K ≤ G, Subgroup.closure {a, b} ≤ K → ReflGen p K → SplitSupport K 2 →
      K = Subgroup.closure {a, b})
    (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : ¬ ∃ h ∈ Subgroup.closure {a, b}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)), x = h * c) :
    SplitSupport (Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)))) 3 ∧
      Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U))) ≤ G ∧
      ReflGen p (Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)))) ∧
      QTwoLin.TransvectionFree
        (Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)))) := by
  set K₀ : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure {a, b} with hK₀
  set F : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert x (K₀ : Set (U ≃ₗ[ZMod p] U))) with hF
  have hp2 : p ≠ 2 := by omega
  have hK₀G : K₀ ≤ G := by
    rw [hK₀, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact ha
    · exact hb
  have hF3 : SplitSupport F 3 := by
    rw [hF, hK₀]
    exact splitSupport_closure_insert_pair S hp5 hn hdeg ha hb har hbr hab hmax hx hxr hxK
  have hFG : F ≤ G := by
    rw [hF]
    rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact hx
    · exact hK₀G ht
  have hK₀r : ReflGen p K₀ := by
    rw [hK₀]
    exact reflGen_closure_pair har hbr
  have hFr : ReflGen p F := by
    rw [hF]
    exact reflGen_closure_insert hK₀r hxr
  have hFtf : QTwoLin.TransvectionFree F := fun g hg => S.transvectionFree g (hFG hg)
  exact ⟨hF3, hFG, hFr, hFtf⟩

private theorem lemmaThreeTwo_F_dmax [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    (hn : Module.finrank (ZMod p) U = 4) (hH : Nat.card H = 120)
    {a b x : U ≃ₗ[ZMod p] U} (har : IsRefl p a) (hbr : IsRefl p b) (hab : orderOf (a * b) = 5)
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF : F = Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U))))
    (hF3 : SplitSupport F 3) (hFG : F ≤ G) (hFr : ReflGen p F) :
    Nat.card F ≤ 120 ∧ DMax p F 5 := by
  have haF : a ∈ F := by
    rw [hF]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x (Subgroup.subset_closure (by simp)))
  have hbF : b ∈ F := by
    rw [hF]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x (Subgroup.subset_closure (by simp)))
  have hFcard : Nat.card F ≤ 120 := by
    have hs : SplitSupport F (Module.finrank (ZMod p) U - 1) := by rw [hn]; exact hF3
    have hd : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 5 :=
      ⟨a, haF, b, hbF, har, hbr, hab⟩
    have := S.card_le_of_orderOf hFG hFr hs hd
    omega
  exact ⟨hFcard, fun x hxF y hyF hxr hyr => S.dmax.1 x (hFG hxF) y (hFG hyF) hxr hyr,
    ⟨a, haF, b, hbF, har, hbr, hab⟩⟩

theorem lemmaThreeTwo [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5) (hp5 : 5 < p)
    (hn : Module.finrank (ZMod p) U = 4) (hH : Nat.card H = 120) (hdeg : DegenerateInput p G 2)
    (htab : TFDimThreeFive p) {a b x : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (hb : b ∈ G)
    (har : IsRefl p a) (hbr : IsRefl p b) (hab : orderOf (a * b) = 5)
    (hmax : ∀ K ≤ G, Subgroup.closure {a, b} ≤ K → ReflGen p K → SplitSupport K 2 →
      K = Subgroup.closure {a, b})
    (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : ¬ ∃ h ∈ Subgroup.closure {a, b}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)), x = h * c) :
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U), α ^ 2 = α + 1 ∧
      Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U))) =
        basisClosure f (h3Mats α) := by
  obtain ⟨hF3, hFG, hFr, hFtf⟩ :=
    lemmaThreeTwo_F_refl S hp5 hn hdeg ha hb har hbr hab hmax hx hxr hxK
  obtain ⟨hFcard, hFd⟩ := lemmaThreeTwo_F_dmax S hn hH har hbr hab rfl hF3 hFG hFr
  exact htab U (Subgroup.closure (insert x (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U))))
    hp5 hn hFr hFtf hF3 hFd hFcard
theorem exists_conj_commute_of_lemmaThreeTwo [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 5) (hp5 : 5 < p) (hn : Module.finrank (ZMod p) U = 4)
    (hH : Nat.card H = 120) (hdeg : DegenerateInput p G 2) (htab : TFDimThreeFive p)
    (hH3 : TFH3Model p) {a b x : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (hb : b ∈ G)
    (har : IsRefl p a) (hbr : IsRefl p b) (hab : orderOf (a * b) = 5)
    (hmax : ∀ K ≤ G, Subgroup.closure {a, b} ≤ K → ReflGen p K → SplitSupport K 2 →
      K = Subgroup.closure {a, b})
    (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : ¬ ∃ h ∈ Subgroup.closure {a, b}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)), x = h * c) :
    ∃ g ∈ Subgroup.closure {a, b}, g * x * g⁻¹ * a = a * (g * x * g⁻¹) := by
  have hp2 : p ≠ 2 := by omega
  have hp5' : p ≠ 5 := by omega
  obtain ⟨α, f, hα, hFb⟩ :=
    lemmaThreeTwo S hp5 hn hH hdeg htab ha hb har hbr hab hmax hx hxr hxK
  have hxnot : x ∉ Subgroup.closure {a, b} := by
    intro hx0
    exact hxK ⟨x, hx0, 1, Subgroup.one_mem _, by simp⟩
  have haF : a ∈ basisClosure f (h3Mats α) := by
    rw [← hFb]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x (Subgroup.subset_closure (by simp)))
  have hbF : b ∈ basisClosure f (h3Mats α) := by
    rw [← hFb]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x (Subgroup.subset_closure (by simp)))
  have hxF : x ∈ basisClosure f (h3Mats α) := by
    rw [← hFb]
    exact Subgroup.subset_closure (Set.mem_insert x _)
  exact (hH3 U f α hp2 hp5' hα).2.2 a haF b hbF x hxF har hbr hxr hab hxnot


end PrimExtSetting

end CFSG.StandardType.ZS

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

public section

namespace CFSG.StandardType

variable {p n : ℕ} [Fact p.Prime]

private lemma apply_pow_eq_prod_of_eigen (π : Equiv.Perm (Fin n)) (d : Fin n → ZMod p)
    {v : Fin n → ZMod p} (hv : ∀ j, v (π j) = d j * v j) (i : Fin n) :
    ∀ k : ℕ, v ((π ^ k) i) =
      (∏ t ∈ Finset.range k, d ((π ^ t) i)) * v i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hv, ih, Finset.prod_range_succ, ← mul_assoc,
      mul_comm (d ((π ^ k) i)) (∏ t ∈ Finset.range k, d ((π ^ t) i))]

private lemma eq_zero_of_forall_apply_rep_eq_zero {π : Equiv.Perm (Fin n)} {d : Fin n → ZMod p}
    (hd : ∀ j, π j = j → d j ≠ 1) {K : Submodule (ZMod p) (Fin n → ZMod p)}
    (hK : ∀ v ∈ K, ∀ j, v (π j) = d j * v j)
    (rep : π.cycleFactorsFinset → Fin n) (hrep : ∀ c, rep c ∈ c.val.support)
    {z : Fin n → ZMod p} (hz : z ∈ K) (hzrep : ∀ c, z (rep c) = 0) : z = 0 := by
  classical
  funext j
  by_cases hfix : π j = j
  · have hdj : d j ≠ 1 := hd j hfix
    have h1 : z j = d j * z j := by
      have h := hK z hz j
      rwa [hfix] at h
    have h3 : (d j - 1) * z j = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hdj)
  · have hsupp : j ∈ π.support := by
      simpa [Equiv.Perm.mem_support] using hfix
    let c : π.cycleFactorsFinset :=
      ⟨π.cycleOf j, (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff (f := π)).mpr hsupp⟩
    have hjc : j ∈ c.val.support := by
      show j ∈ (π.cycleOf j).support
      rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
      exact hfix
    obtain ⟨k, -, hk⟩ := (Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.2).exists_pow_eq
      (a := rep c) (b := j) (hrep c) hjc
    have hpow := apply_pow_eq_prod_of_eigen π d (hK z hz) (rep c) k
    rw [hk, hzrep c] at hpow
    simpa using hpow

private lemma finrank_le_card_cycleFactors (π : Equiv.Perm (Fin n)) (d : Fin n → ZMod p)
    (hd : ∀ j, π j = j → d j ≠ 1) (K : Submodule (ZMod p) (Fin n → ZMod p))
    (hK : ∀ v ∈ K, ∀ j, v (π j) = d j * v j) :
    Module.finrank (ZMod p) K ≤ π.cycleFactorsFinset.card := by
  classical
  let rep : π.cycleFactorsFinset → Fin n := fun c =>
    Classical.choose (Equiv.Perm.IsCycle.nonempty_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1)
  have hrep : ∀ c, rep c ∈ c.val.support := fun c =>
    Classical.choose_spec
      (Equiv.Perm.IsCycle.nonempty_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1)
  have hrep_inj : Function.Injective rep := by
    intro c c' hcc'
    by_contra hne
    have hdis : Equiv.Perm.Disjoint c.val c'.val :=
      Equiv.Perm.cycleFactorsFinset_pairwise_disjoint π c.2 c'.2
        (fun h => hne (Subtype.ext h))
    have hmem : rep c ∈ c'.val.support := by simpa [hcc'] using hrep c'
    exact (Finset.disjoint_left.mp hdis.disjoint_support) (hrep c) hmem
  let R : Finset (Fin n) := Finset.univ.image rep
  have hRcard : R.card = π.cycleFactorsFinset.card := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ hrep_inj, Finset.card_attach]
  let φ : K →ₗ[ZMod p] (R → ZMod p) :=
    { toFun := fun z r => z.1 r
      map_add' := fun z z' => by ext r; rfl
      map_smul' := fun a z => by ext r; rfl }
  have hφ : Function.Injective φ := by
    intro z z' hzz'
    have hsub : (z - z').1 ∈ K := by
      simpa using (Submodule.sub_mem (p := K) z.2 z'.2)
    have hfun : (z - z').1 = 0 := by
      apply eq_zero_of_forall_apply_rep_eq_zero hd hK rep hrep hsub
      intro c
      have hmem : rep c ∈ R := by
        dsimp [R]
        exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
      have hzz : z.1 (rep c) = z'.1 (rep c) := by
        simpa [φ] using congrFun hzz' ⟨rep c, hmem⟩
      simpa using sub_eq_zero.mpr hzz
    exact sub_eq_zero.mp (Subtype.ext (by simpa using hfun))
  calc Module.finrank (ZMod p) K
      ≤ Module.finrank (ZMod p) (R → ZMod p) :=
        LinearMap.finrank_le_finrank_of_injective hφ
    _ = R.card := by rw [Module.finrank_pi, Fintype.card_coe]
    _ = π.cycleFactorsFinset.card := hRcard

private lemma card_cycleFactorsFinset_le_support_div_two (π : Equiv.Perm (Fin n)) :
    π.cycleFactorsFinset.card ≤ π.support.card / 2 := by
  classical
  have hdis : (π.cycleFactorsFinset : Set (Equiv.Perm (Fin n))).PairwiseDisjoint
      (fun c => c.support) := by
    intro c hc c' hc' hne
    exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint π hc hc' hne).disjoint_support
  have hunion : π.cycleFactorsFinset.biUnion (fun c => c.support) = π.support := by
    ext x
    rw [Finset.mem_biUnion,
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset (g := π)]
  have hsum : π.support.card = ∑ c ∈ π.cycleFactorsFinset, c.support.card := by
    rw [← Finset.card_biUnion hdis, hunion]
  have htwo : π.cycleFactorsFinset.card * 2 ≤
      ∑ c ∈ π.cycleFactorsFinset, c.support.card := by
    calc π.cycleFactorsFinset.card * 2 = ∑ _c ∈ π.cycleFactorsFinset, 2 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ π.cycleFactorsFinset, c.support.card :=
          Finset.sum_le_sum fun c hc =>
            (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, hsum]
  exact htwo

private lemma n_sub_two_le_finrank_ker_one_sub_smul
    {r s : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)} (hr : GGLinRefl r)
    (c : ZMod p) (w : Fin n → ZMod p)
    (h : ∀ v, r v - c • s v ∈ Submodule.span (ZMod p) {w}) :
    n - 2 ≤ Module.finrank (ZMod p)
      (LinearMap.ker ((LinearMap.id - c • s.toLinearMap :
        (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)))) := by
  set T : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
    LinearMap.id - c • s.toLinearMap with hT
  let P : Submodule (ZMod p) (Fin n → ZMod p) :=
    LinearMap.range (LinearMap.id - r.toLinearMap) ⊔
      LinearMap.range (r.toLinearMap - c • s.toLinearMap)
  have hle : LinearMap.range T ≤ P := by
    rw [hT]
    rw [show (LinearMap.id - c • s.toLinearMap :
        (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) =
        (LinearMap.id - r.toLinearMap) + (r.toLinearMap - c • s.toLinearMap) by
      ext v
      simp [sub_eq_add_neg, add_assoc, add_left_comm]]
    exact LinearMap.range_add_le _ _
  have hr1 : Module.finrank (ZMod p) (LinearMap.range (LinearMap.id - r.toLinearMap)) ≤ 1 := by
    rw [show LinearMap.range (LinearMap.id - r.toLinearMap) = ggLinMove r by
      have hneg : (LinearMap.id - r.toLinearMap :
          (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) =
          -(r.toLinearMap - LinearMap.id) := by
        ext v
        simp
      rw [hneg, LinearMap.range_neg]
      rfl]
    exact hr.2.le
  have hr2 : Module.finrank (ZMod p)
      (LinearMap.range (r.toLinearMap - c • s.toLinearMap)) ≤ 1 := by
    calc Module.finrank (ZMod p) (LinearMap.range (r.toLinearMap - c • s.toLinearMap))
        ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) {w}) :=
          Submodule.finrank_mono (by rintro y ⟨v, rfl⟩; exact h v)
      _ ≤ 1 := by
          simpa using (finrank_span_le_card ({w} : Set (Fin n → ZMod p)))
  have hrank : Module.finrank (ZMod p) (LinearMap.range T) ≤ 2 := by
    calc Module.finrank (ZMod p) (LinearMap.range T)
        ≤ Module.finrank (ZMod p) P := Submodule.finrank_mono hle
      _ ≤ Module.finrank (ZMod p) (LinearMap.range (LinearMap.id - r.toLinearMap)) +
            Module.finrank (ZMod p) (LinearMap.range (r.toLinearMap - c • s.toLinearMap)) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ 1 + 1 := add_le_add hr1 hr2
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [Module.finrank_fin_fun] at hrn
  omega

theorem eq_one_of_linRefl_sub_smul_perm_mem_span (hn : 5 ≤ n)
    {r s : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)} (hr : GGLinRefl r)
    (π : Equiv.Perm (Fin n)) (hs : ∀ v j, s v (π j) = v j) (c : ZMod p) (w : Fin n → ZMod p)
    (h : ∀ v, r v - c • s v ∈ Submodule.span (ZMod p) {w}) : c = 1 := by
  by_contra hc
  set T : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
    LinearMap.id - c • s.toLinearMap with hT
  have hK : ∀ v ∈ LinearMap.ker T, ∀ j, v (π j) = c * v j := by
    intro v hv j
    have hv' : v = c • s v := by
      have h0 : v - c • s v = 0 := by simpa [T] using hv
      exact sub_eq_zero.mp h0
    calc v (π j) = c * (s v) (π j) := by simpa using congrFun hv' (π j)
      _ = c * v j := by rw [hs v j]
  have hlow : n - 2 ≤ Module.finrank (ZMod p) (LinearMap.ker T) :=
    n_sub_two_le_finrank_ker_one_sub_smul hr c w h
  have hup : Module.finrank (ZMod p) (LinearMap.ker T) ≤ π.cycleFactorsFinset.card :=
    finrank_le_card_cycleFactors π (fun _ => c) (fun _ _ => hc) (LinearMap.ker T) hK
  have hcyc : π.cycleFactorsFinset.card ≤ π.support.card / 2 :=
    card_cycleFactorsFinset_le_support_div_two π
  have hsupp : π.support.card ≤ n := by simpa using Finset.card_le_univ π.support
  have hhalf : π.support.card / 2 ≤ n / 2 := Nat.div_le_div_right hsupp
  have hfin : n - 2 ≤ n / 2 := hlow.trans (hup.trans (hcyc.trans hhalf))
  omega

theorem eq_one_or_eq_neg_one_of_linRefl_sub_smul_signedPerm (hn : 4 ≤ n) {i0 : Fin n}
    {r s : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)} (hr : GGLinRefl r)
    (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hπ : π i0 = i0) (hs : ∀ v j, s v (π j) = ε j * v j) (c : ZMod p) (w : Fin n → ZMod p)
    (h : ∀ v, r v - c • s v ∈ Submodule.span (ZMod p) {w}) : c = 1 ∨ c = -1 := by
  by_contra hc
  have hc1 : c ≠ 1 := fun h1 => hc (Or.inl h1)
  have hcn1 : c ≠ -1 := fun h1 => hc (Or.inr h1)
  set T : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
    LinearMap.id - c • s.toLinearMap with hT
  have hd : ∀ j, π j = j → (c * ε j) ≠ 1 := by
    intro j _
    rcases hε j with hεj | hεj
    · rw [hεj, mul_one]
      exact hc1
    · rw [hεj, mul_neg, mul_one]
      intro h1
      exact hcn1 (by simpa using congrArg Neg.neg h1)
  have hK : ∀ v ∈ LinearMap.ker T, ∀ j, v (π j) = (c * ε j) * v j := by
    intro v hv j
    have hv' : v = c • s v := by
      have h0 : v - c • s v = 0 := by simpa [T] using hv
      exact sub_eq_zero.mp h0
    calc v (π j) = c * (s v) (π j) := by simpa using congrFun hv' (π j)
      _ = c * (ε j * v j) := by rw [hs v j]
      _ = (c * ε j) * v j := by rw [mul_assoc]
  have hlow : n - 2 ≤ Module.finrank (ZMod p) (LinearMap.ker T) :=
    n_sub_two_le_finrank_ker_one_sub_smul hr c w h
  have hup : Module.finrank (ZMod p) (LinearMap.ker T) ≤ π.cycleFactorsFinset.card :=
    finrank_le_card_cycleFactors π (fun j => c * ε j) hd (LinearMap.ker T) hK
  have hcyc : π.cycleFactorsFinset.card ≤ π.support.card / 2 :=
    card_cycleFactorsFinset_le_support_div_two π
  have hsupp : π.support.card ≤ n - 1 := by
    have hsub : π.support ⊆ Finset.univ.erase i0 := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ x⟩
      intro hxi
      exact (Equiv.Perm.mem_support.mp hx) (by rw [hxi]; exact hπ)
    calc π.support.card ≤ (Finset.univ.erase i0).card := Finset.card_le_card hsub
      _ = n - 1 := by simp
  have hhalf : π.support.card / 2 ≤ (n - 1) / 2 := Nat.div_le_div_right hsupp
  have hfin : n - 2 ≤ (n - 1) / 2 := hlow.trans (hup.trans (hcyc.trans hhalf))
  omega

end CFSG.StandardType

end

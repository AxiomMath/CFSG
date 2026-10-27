module

public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private structure MonomialData {n : ℕ} (b : Fin n → U) (y : U ≃ₗ[ZMod p] U) where
  σ : Equiv.Perm (Fin n)
  d : Fin n → (ZMod p)ˣ
  hd : ∀ i, y (b i) = (d i : ZMod p) • b (σ i)

variable {n : ℕ} {b : Fin n → U}

private lemma zs4o_index_unique (hb : LinearIndependent (ZMod p) b) {j j' : Fin n}
    {c c' : ZMod p} (hc : c ≠ 0) (h : c • b j = c' • b j') : j = j' := by
  by_contra hjj
  have key := (linearIndependent_iff'ₛ.mp hb) ({j, j'} : Finset (Fin n))
    (fun i => if i = j then c else 0) (fun i => if i = j' then c' else 0)
  have hsum : ∑ i ∈ ({j, j'} : Finset (Fin n)), (if i = j then c else 0) • b i =
      ∑ i ∈ ({j, j'} : Finset (Fin n)), (if i = j' then c' else 0) • b i := by
    rw [Finset.sum_pair hjj, Finset.sum_pair hjj]
    simpa [hjj, Ne.symm hjj] using h
  have hij := key hsum j (by simp)
  rw [if_pos rfl, if_neg hjj] at hij
  exact hc hij

private lemma zs4o_not_smul_eq_of_ne (hb : LinearIndependent (ZMod p) b) {i i' : Fin n}
    (hne : i ≠ i') {c c' : ZMod p} (hc : c ≠ 0) (h : c • b i = c' • b i') : False := by
  have key := (linearIndependent_iff'ₛ.mp hb) ({i, i'} : Finset (Fin n))
    (fun k => if k = i then c else 0) (fun k => if k = i' then c' else 0)
  have hsum : ∑ k ∈ ({i, i'} : Finset (Fin n)), (if k = i then c else 0) • b k =
      ∑ k ∈ ({i, i'} : Finset (Fin n)), (if k = i' then c' else 0) • b k := by
    rw [Finset.sum_pair hne, Finset.sum_pair hne]
    simpa [hne, Ne.symm hne] using h
  have hii := key hsum i (by simp)
  rw [if_pos rfl, if_neg hne] at hii
  exact hc hii

private lemma zs4o_scalar_ne_zero (hb : LinearIndependent (ZMod p) b) {y : U ≃ₗ[ZMod p] U}
    {i j : Fin n} {c : ZMod p} (h : y (b i) = c • b j) : c ≠ 0 := by
  intro hc
  rw [hc, zero_smul] at h
  exact hb.ne_zero i (y.injective (by rw [h, map_zero]))

private theorem zs4o_monomialData_exists (hb : LinearIndependent (ZMod p) b) {Y : Subgroup
      (U ≃ₗ[ZMod p] U)} (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) : Nonempty (MonomialData b y) := by
  classical
  choose σ c hc using hmon y hy
  have hc0 : ∀ i, c i ≠ 0 := fun i => zs4o_scalar_ne_zero hb (hc i)
  have hσinj : Function.Injective σ := by
    intro i i' hii
    by_contra hne
    have hyi : y (b i) = c i • b (σ i) := hc i
    have hyi' : y (b i') = c i' • b (σ i) := by rw [hc i', hii]
    have h1 : b i = (c i) • y.symm (b (σ i)) := by
      rw [← (LinearEquiv.symm_apply_apply y (b i)), hyi, map_smul]
    have h2 : b i' = (c i') • y.symm (b (σ i)) := by
      rw [← (LinearEquiv.symm_apply_apply y (b i')), hyi', map_smul]
    have hrel : (c i') • b i = (c i) • b i' := by
      rw [h1, h2, smul_smul, smul_smul, mul_comm]
    exact zs4o_not_smul_eq_of_ne hb hne (hc0 i') hrel
  refine ⟨⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj), fun i =>
    Units.mk0 (c i) (hc0 i), fun i => ?_⟩⟩
  show y (b i) = ((Units.mk0 (c i) (hc0 i) : (ZMod p)ˣ) : ZMod p) • b (Equiv.ofBijective σ _ i)
  rw [Units.val_mk0]
  exact hc i

private theorem zs4o_monomialData_subsingleton (hb : LinearIndependent (ZMod p) b)
    (y : U ≃ₗ[ZMod p] U) : Subsingleton (MonomialData b y) := by
  constructor
  rintro ⟨σ, d, hd⟩ ⟨σ', d', hd'⟩
  have hσσ : σ = σ' := by
    refine Equiv.ext fun i => ?_
    have h1 := hd i
    have h2 := hd' i
    rw [h1] at h2
    exact zs4o_index_unique hb (Units.ne_zero (d i)) h2
  subst hσσ
  have hdd : d = d' := by
    funext i
    have h1 := hd i
    have h2 := hd' i
    have heq : (d i : ZMod p) • b (σ i) = (d' i : ZMod p) • b (σ i) := by rw [← h1, h2]
    exact Units.ext (smul_left_injective (ZMod p) (hb.ne_zero (σ i)) heq)
  subst hdd
  rfl

private noncomputable def zs4o_coord {n : ℕ} {b : Fin n → U} {y : U ≃ₗ[ZMod p] U}
    (D : MonomialData b y) (i : Fin n) : Fin n →₀ ZMod p :=
  Finsupp.single (D.σ i) (D.d i : ZMod p) - Finsupp.single i 1

private lemma zs4o_support_coord {n : ℕ} {i j : Fin n} {c : ZMod p} (hij : j ≠ i)
    (hc : c ≠ 0) :
    (Finsupp.single j c - Finsupp.single i 1 : Fin n →₀ ZMod p).support =
      ({i, j} : Finset (Fin n)) := by
  ext k
  rw [Finsupp.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hki : k = i
  · rw [hki, Finsupp.sub_apply, Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.single_eq_same,
      zero_sub, neg_ne_zero]
    simp
  · by_cases hkj : k = j
    · rw [hkj, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
        sub_zero]
      simp [hij, hc]
    · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hkj, Finsupp.single_eq_of_ne hki,
        sub_self]
      simp [hki, hkj]

private lemma zs4o_coord_eq_zero {n : ℕ} {b : Fin n → U} {y : U ≃ₗ[ZMod p] U}
    (D : MonomialData b y) {i : Fin n} (h : zs4o_coord D i = 0) : D.σ i = i := by
  have h' : Finsupp.single (D.σ i) (D.d i : ZMod p) - Finsupp.single i 1 = 0 := h
  have hsingle : Finsupp.single (D.σ i) (D.d i : ZMod p) = Finsupp.single i 1 :=
    sub_eq_zero.mp h'
  by_contra hne
  have hcongr := congrArg (fun f : Fin n →₀ ZMod p => f (D.σ i)) hsingle
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne] at hcongr
  exact Units.ne_zero (D.d i) hcongr

private lemma zs4o_reflection_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hle : HardMathSupport.Kantor79.commutatorSpace Y ≤ Submodule.span (ZMod p) (Set.range b))
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ Y) (htR : IsRefl p t) (D : MonomialData b t) :
    ∃ (φ : Module.Dual (ZMod p) U) (A : Fin n →₀ ZMod p),
      (∀ i, D.σ (D.σ i) = i) ∧
      (∀ i, D.σ i ≠ i → φ (b i) ≠ 0) ∧
      (∀ i, zs4o_coord D i = (-(φ (b i))) • A) := by
  classical
  obtain ⟨a, φ, hφ, ht_eq⟩ := (isRefl_iff hp t).mp htR
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hprime : Nat.Prime p := Fact.out
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact hprime.ne_one h1
    · exact hp h1
  have ha_comm : a ∈ HardMathSupport.Kantor79.commutatorSpace Y := by
    apply HardMathSupport.Kantor79.movedSpace_le_commutatorSpace ht
    have hneg : -a ∈ HardMathSupport.Kantor79.movedSpace t := by
      refine ⟨(2 : ZMod p)⁻¹ • a, ?_⟩
      change t ((2 : ZMod p)⁻¹ • a) - (2 : ZMod p)⁻¹ • a = -a
      rw [ht_eq, Module.reflection_apply, map_smul, hφ, smul_eq_mul, inv_mul_cancel₀ h2]
      simp
    simpa using Submodule.neg_mem _ hneg
  have haB : a ∈ Submodule.span (ZMod p) (Set.range b) := hle ha_comm
  obtain ⟨A, hA⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp haB
  have hA' : Finsupp.linearCombination (ZMod p) b A = a := by
    rw [Finsupp.linearCombination_apply]; exact hA
  have hcoord (i : Fin n) : zs4o_coord D i = (-(φ (b i))) • A := by
    apply LinearIndependent.finsuppLinearCombination_injective hb
    have h1 : Finsupp.linearCombination (ZMod p) b (zs4o_coord D i) = -(φ (b i)) • a := by
      simp only [zs4o_coord, map_sub, Finsupp.linearCombination_single, one_smul]
      rw [← D.hd i, ht_eq, Module.reflection_apply]
      simp
    rw [h1, map_smul, hA']
  have hσ2 : ∀ i, D.σ (D.σ i) = i := by
    intro i
    have h1 : t (t (b i)) = b i := by rw [← LinearEquiv.mul_apply, htR.1]; rfl
    rw [D.hd i, map_smul, D.hd (D.σ i), smul_smul] at h1
    have hc : ((D.d i : ZMod p) * (D.d (D.σ i) : ZMod p)) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    refine zs4o_index_unique (j := D.σ (D.σ i)) (j' := i) (c' := 1) hb hc ?_
    rw [one_smul]; exact h1
  have hφ_ne (i : Fin n) (hi : D.σ i ≠ i) : φ (b i) ≠ 0 := by
    intro h0
    exact hi (zs4o_coord_eq_zero D (by rw [hcoord i, h0, neg_zero, zero_smul]))
  exact ⟨φ, A, hσ2, hφ_ne, hcoord⟩

private lemma zs4o_reflection_case {n : ℕ} {b : Fin n → U}
    (_hb : LinearIndependent (ZMod p) b)
    {t : U ≃ₗ[ZMod p] U} (D : MonomialData b t) (φ : Module.Dual (ZMod p) U)
    (A : Fin n →₀ ZMod p)
    (hσ2 : ∀ i, D.σ (D.σ i) = i)
    (hφ_ne : ∀ i, D.σ i ≠ i → φ (b i) ≠ 0)
    (hcoord : ∀ i, zs4o_coord D i = (-(φ (b i))) • A) :
    D.σ = 1 ∨ D.σ.IsSwap := by
  by_cases hmoved : ∃ i, D.σ i ≠ i
  · right
    obtain ⟨i₁, hi₁⟩ := hmoved
    have hsupp1 : A.support = ({i₁, D.σ i₁} : Finset (Fin n)) := by
      have h1 : (zs4o_coord D i₁).support = A.support := by
        rw [hcoord i₁, Finsupp.support_smul_eq (neg_ne_zero.mpr (hφ_ne i₁ hi₁))]
      have h2 : (zs4o_coord D i₁).support = ({i₁, D.σ i₁} : Finset (Fin n)) :=
        zs4o_support_coord (i := i₁) (j := D.σ i₁) (c := (D.d i₁ : ZMod p)) hi₁
          (Units.ne_zero _)
      rw [← h1, h2]
    have hmoved_eq (i : Fin n) (hi : D.σ i ≠ i) :
        ({i, D.σ i} : Finset (Fin n)) = ({i₁, D.σ i₁} : Finset (Fin n)) := by
      have h1 : (zs4o_coord D i).support = A.support := by
        rw [hcoord i, Finsupp.support_smul_eq (neg_ne_zero.mpr (hφ_ne i hi))]
      have h3 : (zs4o_coord D i).support = ({i, D.σ i} : Finset (Fin n)) :=
        zs4o_support_coord (i := i) (j := D.σ i) (c := (D.d i : ZMod p)) hi
          (Units.ne_zero _)
      rw [← h3, h1, hsupp1]
    refine ⟨i₁, D.σ i₁, Ne.symm hi₁, ?_⟩
    refine Equiv.ext fun i => ?_
    by_cases hii : i = i₁
    · subst hii; rw [Equiv.swap_apply_left]
    · by_cases his : i = D.σ i₁
      · subst his; rw [hσ2 i₁, Equiv.swap_apply_right]
      · have hfix : D.σ i = i := by
          by_contra hm
          have hset := hmoved_eq i hm
          have hmem : i ∈ ({i₁, D.σ i₁} : Finset (Fin n)) := by
            rw [← hset]; simp
          simp [hii, his] at hmem
        rw [hfix, Equiv.swap_apply_of_ne_of_ne hii his]
  · left
    refine Equiv.ext fun i => ?_
    by_contra hne
    exact hmoved ⟨i, hne⟩

private theorem zs4o_perm_isSwap_or_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hle : HardMathSupport.Kantor79.commutatorSpace Y ≤ Submodule.span (ZMod p) (Set.range b))
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ Y) (htR : IsRefl p t) (D : MonomialData b t) :
    D.σ = 1 ∨ D.σ.IsSwap := by
  obtain ⟨φ, A, hσ2, hφ_ne, hcoord⟩ := zs4o_reflection_setup hp hb hle ht htR D
  exact zs4o_reflection_case hb D φ A hσ2 hφ_ne hcoord

private lemma zs4o_map_span_le {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) :
    (Submodule.span (ZMod p) (Set.range b)).map (y : U →ₗ[ZMod p] U) ≤
      Submodule.span (ZMod p) (Set.range b) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro z ⟨k, hk, rfl⟩
  obtain ⟨m, hm⟩ := hk
  rw [← hm]
  obtain ⟨j, c, hc⟩ := hmon y hy m
  change (y : U ≃ₗ[ZMod p] U) (b m) ∈ Submodule.span (ZMod p) (Set.range b)
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

private lemma zs4o_map_span_eq {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) :
    (Submodule.span (ZMod p) (Set.range b)).map (y : U →ₗ[ZMod p] U) =
      Submodule.span (ZMod p) (Set.range b) := by
  refine le_antisymm (zs4o_map_span_le hmon hy) ?_
  have h3 : (Submodule.span (ZMod p) (Set.range b)).map
      ((y⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤
      Submodule.span (ZMod p) (Set.range b) :=
    zs4o_map_span_le (Y := Y) hmon (Y.inv_mem hy)
  have h4 := Submodule.map_mono (f := (y : U →ₗ[ZMod p] U)) h3
  have hcomp : (y : U →ₗ[ZMod p] U) ∘ₗ ((y⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.id := by
    ext v; simp
  rwa [← Submodule.map_comp, hcomp, Submodule.map_id] at h4

private noncomputable def zs4o_basisB {n : ℕ} {b : Fin n → U}
    (hb : LinearIndependent (ZMod p) b) :
    Module.Basis (Fin n) (ZMod p) (Submodule.span (ZMod p) (Set.range b)) :=
  Module.Basis.mk
    (v := fun i => (⟨b i, Submodule.subset_span (Set.mem_range_self i)⟩ :
      Submodule.span (ZMod p) (Set.range b)))
    (LinearIndependent.of_comp (Submodule.span (ZMod p) (Set.range b)).subtype
      (by simpa [Function.comp_def] using hb))
    (by
      have hli : LinearIndependent (ZMod p)
          (fun i => (⟨b i, Submodule.subset_span (Set.mem_range_self i)⟩ :
            Submodule.span (ZMod p) (Set.range b))) :=
        LinearIndependent.of_comp (Submodule.span (ZMod p) (Set.range b)).subtype
          (by simpa [Function.comp_def] using hb)
      have h1 : Module.finrank (ZMod p)
          (Submodule.span (ZMod p) (Set.range (fun i =>
            (⟨b i, Submodule.subset_span (Set.mem_range_self i)⟩ :
              Submodule.span (ZMod p) (Set.range b))))) = n := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      have h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range b)) = n := by
        rw [finrank_span_eq_card hb, Fintype.card_fin]
      have : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) (Set.range b)) :=
        FiniteDimensional.span_of_finite (ZMod p) (Set.finite_range b)
      have htop : Submodule.span (ZMod p) (Set.range (fun i =>
          (⟨b i, Submodule.subset_span (Set.mem_range_self i)⟩ :
            Submodule.span (ZMod p) (Set.range b)))) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h1, h2])
      rw [htop])

private noncomputable def zs4o_restrictB {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) :
    (Submodule.span (ZMod p) (Set.range b)) ≃ₗ[ZMod p]
      (Submodule.span (ZMod p) (Set.range b)) :=
  (y : U ≃ₗ[ZMod p] U).ofSubmodules _ _ (zs4o_map_span_eq hmon hy)

private theorem zs4o_restrictB_apply_basis {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) (D : MonomialData b y) (i : Fin n) :
    zs4o_restrictB hmon hy (zs4o_basisB hb i) =
      (D.d i : ZMod p) • zs4o_basisB hb (D.σ i) := by
  apply Subtype.ext
  rw [zs4o_restrictB, LinearEquiv.ofSubmodules_apply]
  simp only [zs4o_basisB, Module.Basis.mk_apply]
  rw [D.hd i]
  rfl

private theorem zs4o_equivFun_restrictB {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) (D : MonomialData b y)
    (v : Submodule.span (ZMod p) (Set.range b)) (i : Fin n) :
    (zs4o_basisB hb).equivFun (zs4o_restrictB hmon hy v) (D.σ i) =
      (zs4o_basisB hb).equivFun v i * (D.d i : ZMod p) := by
  conv_lhs => rw [← (zs4o_basisB hb).sum_equivFun v]
  have hstep : zs4o_restrictB hmon hy
      (∑ k, (zs4o_basisB hb).equivFun v k • zs4o_basisB hb k) =
      ∑ k, ((zs4o_basisB hb).equivFun v k * (D.d k : ZMod p)) •
        zs4o_basisB hb (D.σ k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, zs4o_restrictB_apply_basis, smul_smul]
  rw [hstep, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [if_neg (fun h => hki (D.σ.injective h))]
    simp
  · intro hi; exact absurd (Finset.mem_univ i) hi

private def zs4o_monomialData_mul {n : ℕ} {b : Fin n → U} {y y' : U ≃ₗ[ZMod p] U}
    (D : MonomialData b y) (D' : MonomialData b y') : MonomialData b (y * y') where
  σ := D.σ * D'.σ
  d := fun i => D'.d i * D.d (D'.σ i)
  hd := by
    intro i
    rw [LinearEquiv.mul_apply, D'.hd i, map_smul, D.hd (D'.σ i), smul_smul, Units.val_mul,
      Equiv.Perm.mul_apply]

private def zs4o_monomialData_one {n : ℕ} {b : Fin n → U} :
    MonomialData b (1 : U ≃ₗ[ZMod p] U) where
  σ := 1
  d := 1
  hd := by intro i; simp

private noncomputable def zs4o_permHom {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j) :
    Y →* Equiv.Perm (Fin n) where
  toFun y := (Classical.choice (zs4o_monomialData_exists hb hmon y.2)).σ
  map_one' := by
    let D1 := Classical.choice (zs4o_monomialData_exists hb hmon Y.one_mem)
    have := zs4o_monomialData_subsingleton hb (1 : U ≃ₗ[ZMod p] U)
    have h : D1 = zs4o_monomialData_one (p := p) (b := b) := Subsingleton.elim _ _
    change D1.σ = 1
    rw [h]
    rfl
  map_mul' y y' := by
    let Dy := Classical.choice (zs4o_monomialData_exists hb hmon y.2)
    let Dy' := Classical.choice (zs4o_monomialData_exists hb hmon y'.2)
    let Dyy := Classical.choice (zs4o_monomialData_exists hb hmon (y * y').2)
    have := zs4o_monomialData_subsingleton hb
      ((y : U ≃ₗ[ZMod p] U) * (y' : U ≃ₗ[ZMod p] U))
    have h : Dyy = zs4o_monomialData_mul Dy Dy' := Subsingleton.elim _ _
    change Dyy.σ = Dy.σ * Dy'.σ
    rw [h]
    rfl

private noncomputable def zs4o_orbitF {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => ∃ y : Y, zs4o_permHom hb hmon y i = j

private lemma zs4o_mem_orbitF {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {i j : Fin n} :
    j ∈ zs4o_orbitF hb hmon i ↔ ∃ y : Y, zs4o_permHom hb hmon y i = j := by
  simp [zs4o_orbitF]

private lemma zs4o_permHom_orbitF_mem {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {i m : Fin n} (hm : m ∈ zs4o_orbitF hb hmon i) (y : Y) :
    zs4o_permHom hb hmon y m ∈ zs4o_orbitF hb hmon i := by
  rw [zs4o_mem_orbitF] at hm ⊢
  obtain ⟨z, hz⟩ := hm
  exact ⟨y * z, by rw [map_mul, Equiv.Perm.mul_apply, hz]⟩

private def zs4o_Wof {n : ℕ} {b : Fin n → U} (S : Finset (Fin n)) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) (b '' (S : Set (Fin n)))

private lemma zs4o_map_Wof_orbitF_le {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (i : Fin n) {y : U ≃ₗ[ZMod p] U} (hy : y ∈ Y) :
    (zs4o_Wof (b := b) (zs4o_orbitF hb hmon i)).map (y : U →ₗ[ZMod p] U) ≤
      zs4o_Wof (b := b) (zs4o_orbitF hb hmon i) := by
  rw [zs4o_Wof, Submodule.map_span, Submodule.span_le]
  rintro z ⟨k, hk, rfl⟩
  obtain ⟨m, hm⟩ := hk
  rw [← hm.2]
  let D := Classical.choice (zs4o_monomialData_exists hb hmon hy)
  have hD : zs4o_permHom hb hmon ⟨y, hy⟩ = D.σ := rfl
  have hmem : D.σ m ∈ zs4o_orbitF hb hmon i := by
    rw [← hD]
    exact zs4o_permHom_orbitF_mem hb hmon hm.1 ⟨y, hy⟩
  rw [show (y : U →ₗ[ZMod p] U) (b m) = (D.d m : ZMod p) • b (D.σ m) from D.hd m]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨D.σ m, hmem, rfl⟩)
private lemma zs4o_finrank_Wof {n : ℕ} {b : Fin n → U}
    (hb : LinearIndependent (ZMod p) b) (S : Finset (Fin n)) :
    Module.finrank (ZMod p) ↥(zs4o_Wof (p := p) (b := b) S) = S.card := by
  have hset : b '' (S : Set (Fin n)) = Set.range (fun i : S => b i) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
  have hli : LinearIndependent (ZMod p) (fun i : S => b i) :=
    hb.comp (Subtype.val : S → Fin n) Subtype.val_injective
  show Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (b '' (S : Set (Fin n)))) = S.card
  rw [hset, finrank_span_eq_card hli, Fintype.card_coe]

private lemma zs4o_step1 {n : ℕ} {V C B : Submodule (ZMod p) U} (hVB : V ≤ B)
    (hdisj : Disjoint V C) (hsup : V ⊔ C = ⊤) (hfinB : Module.finrank (ZMod p) B = n)
    (hfinV : Module.finrank (ZMod p) V = n - 1) (hn : 1 ≤ n)
    (hFinV : FiniteDimensional (ZMod p) V) (hFinCB : FiniteDimensional (ZMod p) ↥(C ⊓ B)) :
    B = V ⊔ (C ⊓ B) ∧ V ⊓ (C ⊓ B) = ⊥ ∧ Module.finrank (ZMod p) ↥(C ⊓ B) = 1 := by
  have := hFinV
  have := hFinCB
  have h1 : B = V ⊔ (C ⊓ B) := by
    calc B = ⊤ ⊓ B := by rw [top_inf_eq]
      _ = (V ⊔ C) ⊓ B := by rw [hsup]
      _ = V ⊔ (C ⊓ B) := sup_inf_assoc_of_le C hVB
  have h2 : V ⊓ (C ⊓ B) = ⊥ := by
    rw [← inf_assoc, hdisj.eq_bot, bot_inf_eq]
  have h3 : Module.finrank (ZMod p) ↥(C ⊓ B) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V (C ⊓ B)
    rw [← h1, h2, finrank_bot, add_zero, hfinB, hfinV] at h
    omega
  exact ⟨h1, h2, h3⟩

private lemma zs4o_invariant_sub_bot {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {B W : Submodule (ZMod p) U} (hWB : W ≤ B)
    (hinv : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W)
    (hbot : W ⊓ HardMathSupport.Kantor79.commutatorSpace Y = ⊥)
    (hfinl : Module.finrank (ZMod p) ↥(centralizerSpace Y ⊓ B) = 1)
    (hFinW : FiniteDimensional (ZMod p) W)
    (hFinCB : FiniteDimensional (ZMod p) ↥(centralizerSpace Y ⊓ B)) :
    W = ⊥ ∨ W = centralizerSpace Y ⊓ B := by
  have := hFinW
  have := hFinCB
  have hWC : W ≤ centralizerSpace Y := by
    intro w hw
    rw [mem_centralizerSpace]
    intro y hy
    have hmem : y w - w ∈ W ⊓ HardMathSupport.Kantor79.commutatorSpace Y :=
      ⟨W.sub_mem (hinv y hy w hw) hw,
        Submodule.subset_span ⟨y, hy, w, rfl⟩⟩
    rw [hbot] at hmem
    exact sub_eq_zero.mp hmem
  have hWle : W ≤ centralizerSpace Y ⊓ B := le_inf hWC hWB
  by_cases hzero : Module.finrank (ZMod p) W = 0
  · exact Or.inl (Submodule.finrank_eq_zero.mp hzero)
  · refine Or.inr (Submodule.eq_of_le_of_finrank_eq hWle ?_)
    have hfr : Module.finrank (ZMod p) W = 1 := by
      have := Submodule.finrank_mono hWle
      rw [hfinl] at this
      omega
    rw [hfr, hfinl]

private lemma zs4o_invariant_sub_top {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {B W : Submodule (ZMod p) U} (hWB : W ≤ B)
    (hBsup : B = HardMathSupport.Kantor79.commutatorSpace Y ⊔ (centralizerSpace Y ⊓ B))
    (htop : W ⊓ HardMathSupport.Kantor79.commutatorSpace Y =
      HardMathSupport.Kantor79.commutatorSpace Y)
    (hfinl : Module.finrank (ZMod p) ↥(centralizerSpace Y ⊓ B) = 1)
    (hFinCB : FiniteDimensional (ZMod p) ↥(centralizerSpace Y ⊓ B)) :
    W = HardMathSupport.Kantor79.commutatorSpace Y ∨ W = B := by
  have := hFinCB
  have hVW : HardMathSupport.Kantor79.commutatorSpace Y ≤ W := by
    rw [← htop]; exact inf_le_left
  have hmod : W = HardMathSupport.Kantor79.commutatorSpace Y ⊔
      (W ⊓ (centralizerSpace Y ⊓ B)) := by
    calc W = W ⊓ B := (inf_eq_left.mpr hWB).symm
      _ = W ⊓ (HardMathSupport.Kantor79.commutatorSpace Y ⊔ (centralizerSpace Y ⊓ B)) := by
            conv_lhs => rw [hBsup]
      _ = (HardMathSupport.Kantor79.commutatorSpace Y ⊔ (centralizerSpace Y ⊓ B)) ⊓ W :=
            inf_comm _ _
      _ = HardMathSupport.Kantor79.commutatorSpace Y ⊔ (centralizerSpace Y ⊓ B) ⊓ W :=
            sup_inf_assoc_of_le (centralizerSpace Y ⊓ B) hVW
      _ = HardMathSupport.Kantor79.commutatorSpace Y ⊔
            (W ⊓ (centralizerSpace Y ⊓ B)) := by conv_lhs => rw [inf_comm]
  have hle : W ⊓ (centralizerSpace Y ⊓ B) ≤ centralizerSpace Y ⊓ B := inf_le_right
  by_cases hzero : Module.finrank (ZMod p) ↥(W ⊓ (centralizerSpace Y ⊓ B)) = 0
  · exact Or.inl (by rw [hmod, Submodule.finrank_eq_zero.mp hzero, sup_bot_eq])
  · have hfr : Module.finrank (ZMod p) ↥(W ⊓ (centralizerSpace Y ⊓ B)) = 1 := by
      have hle' := Submodule.finrank_mono hle
      rw [hfinl] at hle'
      omega
    have heq : W ⊓ (centralizerSpace Y ⊓ B) = centralizerSpace Y ⊓ B :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hfinl])
    exact Or.inr (by rw [hmod, heq, ← hBsup])

private lemma zs4o_invariant_sub {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {B : Submodule (ZMod p) U}
    (hBsup : B = HardMathSupport.Kantor79.commutatorSpace Y ⊔ (centralizerSpace Y ⊓ B))
    (hfinl : Module.finrank (ZMod p) ↥(centralizerSpace Y ⊓ B) = 1)
    (hirrV : ∀ W : Submodule (ZMod p) U, W ≤ HardMathSupport.Kantor79.commutatorSpace Y →
      (∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) → W = ⊥ ∨ W = HardMathSupport.Kantor79.commutatorSpace Y)
    (hFinCB : FiniteDimensional (ZMod p) ↥(centralizerSpace Y ⊓ B))
    (hFinB : FiniteDimensional (ZMod p) B)
    {W : Submodule (ZMod p) U} (hWB : W ≤ B)
    (hinv : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) :
    W = ⊥ ∨ W = centralizerSpace Y ⊓ B ∨ W = HardMathSupport.Kantor79.commutatorSpace Y ∨
      W = B := by
  have hFinW : FiniteDimensional (ZMod p) W := Submodule.finiteDimensional_of_le hWB
  have hinvV : ∀ y ∈ Y, ∀ w ∈ W ⊓ HardMathSupport.Kantor79.commutatorSpace Y,
      y w ∈ W ⊓ HardMathSupport.Kantor79.commutatorSpace Y := by
    rintro y hy w ⟨hwW, hwV⟩
    exact ⟨hinv y hy w hwW, apply_mem_commutatorSpace hy hwV⟩
  rcases hirrV (W ⊓ HardMathSupport.Kantor79.commutatorSpace Y) inf_le_right hinvV with
    hbot | htop
  · rcases zs4o_invariant_sub_bot hWB hinv hbot hfinl hFinW hFinCB with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases zs4o_invariant_sub_top hWB hBsup htop hfinl hFinCB with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

private lemma zs4o_orbitF_trans {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hb : LinearIndependent (ZMod p) b)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {i m k : Fin n} (hm : m ∈ zs4o_orbitF hb hmon i) (hk : m ∈ zs4o_orbitF hb hmon k) :
    k ∈ zs4o_orbitF hb hmon i := by
  rw [zs4o_mem_orbitF] at hm hk ⊢
  obtain ⟨z, hz⟩ := hm
  obtain ⟨y, hy⟩ := hk
  exact ⟨y⁻¹ * z, by
    rw [map_mul, Equiv.Perm.mul_apply, hz, map_inv, ← hy, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]⟩

private structure ZS4oData (n : ℕ) (b : Fin n → U) (Y : Subgroup (U ≃ₗ[ZMod p] U)) : Type where
  hp : p ≠ 2
  hn : 3 ≤ n
  hb : LinearIndependent (ZMod p) b
  hY : ReflGen p Y
  hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j
  hle : HardMathSupport.Kantor79.commutatorSpace Y ≤ Submodule.span (ZMod p) (Set.range b)
  hYs : SplitSupport Y (n - 1)
  hirr : ∀ W : Submodule (ZMod p) U, W ≤ HardMathSupport.Kantor79.commutatorSpace Y →
    (∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) → W = ⊥ ∨ W = HardMathSupport.Kantor79.commutatorSpace Y
  hFinU : Module.Finite (ZMod p) U

private lemma zs4o_step1_data {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) :
    Submodule.span (ZMod p) (Set.range b) =
        HardMathSupport.Kantor79.commutatorSpace Y ⊔
          (centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b)) ∧
      Module.finrank (ZMod p)
        ↥(centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b)) = 1 ∧
      FiniteDimensional (ZMod p) (Submodule.span (ZMod p) (Set.range b)) ∧
      FiniteDimensional (ZMod p)
        ↥(centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b)) := by
  have := D.hFinU
  obtain ⟨hcompl, hfinV, -⟩ := D.hYs
  have hFinB : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) (Set.range b)) :=
    FiniteDimensional.span_of_finite (ZMod p) (Set.finite_range b)
  have hfinB : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range b)) = n := by
    rw [finrank_span_eq_card D.hb, Fintype.card_fin]
  have hFinV : FiniteDimensional (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) :=
    Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span (ZMod p) (Set.range b)) D.hle
  have hFinCB : FiniteDimensional (ZMod p)
      ↥(centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b)) :=
    Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span (ZMod p) (Set.range b)) inf_le_right
  obtain ⟨hBsup, -, hfinl⟩ :=
    zs4o_step1 (V := HardMathSupport.Kantor79.commutatorSpace Y) (C := centralizerSpace Y)
      (B := Submodule.span (ZMod p) (Set.range b)) D.hle hcompl.disjoint hcompl.sup_eq_top
      hfinB hfinV (by have := D.hn; omega) hFinV hFinCB
  exact ⟨hBsup, hfinl, hFinB, hFinCB⟩

private lemma zs4o_main_setup_index {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) :
    ∃ i₀, b i₀ ∉ centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) := by
  have := D.hFinU
  obtain ⟨-, hfinl, -, -⟩ := zs4o_step1_data D
  have hfinV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) = n - 1 :=
    D.hYs.2.1
  have hn := D.hn
  by_contra h
  simp only [not_exists, not_not] at h
  have hBle : Submodule.span (ZMod p) (Set.range b) ≤
      centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hfr := Submodule.finrank_mono (le_trans D.hle hBle)
  rw [hfinV, hfinl] at hfr
  omega

private lemma zs4o_main_setup {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) :
    ∃ i₀ : Fin n,
      (zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) =
        HardMathSupport.Kantor79.commutatorSpace Y ∨
       zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) =
        Submodule.span (ZMod p) (Set.range b)) ∧
      Module.finrank (ZMod p)
        ↥(zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀)) =
        (zs4o_orbitF D.hb D.hmon i₀).card := by
  have := D.hFinU
  obtain ⟨hBsup, hfinl, hFinB, hFinCB⟩ := zs4o_step1_data D
  obtain ⟨i₀, hi₀⟩ := zs4o_main_setup_index D
  have hWle : zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) ≤
      Submodule.span (ZMod p) (Set.range b) := by
    rw [zs4o_Wof, Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  have hWin : ∀ y ∈ Y, ∀ w ∈ zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀),
      y w ∈ zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) := by
    intro y hy w hw
    exact zs4o_map_Wof_orbitF_le D.hb D.hmon i₀ hy
      (Submodule.mem_map_of_mem (f := (y : U →ₗ[ZMod p] U)) hw)
  have hi₀mem : i₀ ∈ zs4o_orbitF D.hb D.hmon i₀ := by
    rw [zs4o_mem_orbitF]; exact ⟨1, by simp⟩
  have hb0mem : b i₀ ∈ zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) :=
    Submodule.subset_span ⟨i₀, hi₀mem, rfl⟩
  have hfinOrb : Module.finrank (ZMod p)
      ↥(zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀)) =
      (zs4o_orbitF D.hb D.hmon i₀).card := zs4o_finrank_Wof D.hb _
  rcases zs4o_invariant_sub (Y := Y) (B := Submodule.span (ZMod p) (Set.range b))
      hBsup hfinl D.hirr hFinCB hFinB hWle hWin with hbot | hmid | hV | htop
  · exfalso
    rw [hbot] at hb0mem
    exact absurd (by simpa using hb0mem) (D.hb.ne_zero i₀)
  · exfalso
    exact absurd (hmid ▸ hb0mem) hi₀
  · exact ⟨i₀, Or.inl hV, hfinOrb⟩
  · exact ⟨i₀, Or.inr htop, hfinOrb⟩

private lemma zs4o_two_orbit_find {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) {i₀ : Fin n}
    (hfinOrb : Module.finrank (ZMod p)
      ↥(zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀)) =
      (zs4o_orbitF D.hb D.hmon i₀).card)
    (hV : zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) =
      HardMathSupport.Kantor79.commutatorSpace Y) :
    ∃ k, zs4o_orbitF D.hb D.hmon i₀ = Finset.univ.erase k := by
  have := D.hFinU
  have hn := D.hn
  have hcard : (zs4o_orbitF D.hb D.hmon i₀).card = n - 1 := by
    rw [← hfinOrb, hV, D.hYs.2.1]
  have hkex : ∃ k, k ∉ zs4o_orbitF D.hb D.hmon i₀ := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.eq_univ_iff_forall.mpr h, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨k, hk⟩ := hkex
  refine ⟨k, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro j hj
    rw [Finset.mem_erase]
    exact ⟨fun hjk => hk (hjk ▸ hj), Finset.mem_univ j⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin, hcard]

private lemma zs4o_two_orbit_line_fix {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (D : ZS4oData n b Y) {k : Fin n}
    (hOrbk : zs4o_orbitF D.hb D.hmon k = {k}) :
    ∀ y ∈ Y, ∀ w ∈ Submodule.span (ZMod p) {b k},
      y w ∈ Submodule.span (ZMod p) {b k} := by
  intro y hy w hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  let D' := Classical.choice (zs4o_monomialData_exists D.hb D.hmon hy)
  have hDk : D'.σ k = k := by
    have hmem : D'.σ k ∈ zs4o_orbitF D.hb D.hmon k := by
      rw [← (show zs4o_permHom D.hb D.hmon ⟨y, hy⟩ = D'.σ from rfl)]
      exact zs4o_permHom_orbitF_mem D.hb D.hmon
        (by rw [hOrbk]; exact Finset.mem_singleton_self k) ⟨y, hy⟩
    rw [hOrbk] at hmem
    exact Finset.mem_singleton.mp hmem
  rw [← hc, map_smul,
    show (y : U ≃ₗ[ZMod p] U) (b k) = (D'.d k : ZMod p) • b (D'.σ k) from D'.hd k, hDk]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))

private lemma zs4o_two_orbit_line {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) {i₀ k : Fin n}
    (hOrb : zs4o_orbitF D.hb D.hmon i₀ = Finset.univ.erase k)
    (hk : k ∉ zs4o_orbitF D.hb D.hmon i₀) :
    centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k} := by
  have := D.hFinU
  obtain ⟨hBsup, hfinl, hFinB, hFinCB⟩ := zs4o_step1_data D
  have hOrbk : zs4o_orbitF D.hb D.hmon k = {k} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · rw [zs4o_mem_orbitF]; exact ⟨1, by simp⟩
    · intro m hm
      by_contra hmk
      have hm' : m ∈ zs4o_orbitF D.hb D.hmon i₀ := by
        rw [hOrb, Finset.mem_erase]
        exact ⟨hmk, Finset.mem_univ m⟩
      exact hk (zs4o_orbitF_trans D.hb D.hmon hm' hm)
  have hinvk := zs4o_two_orbit_line_fix D hOrbk
  have hle_k : Submodule.span (ZMod p) {b k} ≤ Submodule.span (ZMod p) (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ rfl
    exact Submodule.subset_span (Set.mem_range_self k)
  have hbk0 : b k ≠ 0 := D.hb.ne_zero k
  have hn := D.hn
  have hfr1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {b k}) = 1 :=
    finrank_span_singleton hbk0
  rcases zs4o_invariant_sub (Y := Y) (B := Submodule.span (ZMod p) (Set.range b))
      hBsup hfinl D.hirr hFinCB hFinB hle_k hinvk with h | h | h | h
  · exfalso
    have hmem : b k ∈ (⊥ : Submodule (ZMod p) U) :=
      h ▸ Submodule.subset_span (Set.mem_singleton (b k))
    exact hbk0 (by simpa using hmem)
  · exact h.symm
  · exfalso
    rw [h, D.hYs.2.1] at hfr1
    omega
  · exfalso
    have hfinB : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range b)) = n := by
      rw [finrank_span_eq_card D.hb, Fintype.card_fin]
    rw [h, hfinB] at hfr1
    omega

private lemma zs4o_two_orbit {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) {i₀ : Fin n}
    (hfinOrb : Module.finrank (ZMod p)
      ↥(zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀)) =
      (zs4o_orbitF D.hb D.hmon i₀).card)
    (hV : zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) =
      HardMathSupport.Kantor79.commutatorSpace Y) :
    ∃ k, HardMathSupport.Kantor79.commutatorSpace Y =
        Submodule.span (ZMod p) (b '' {i | i ≠ k}) ∧
      centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
        Submodule.span (ZMod p) {b k} := by
  have := D.hFinU
  obtain ⟨k, hOrb⟩ := zs4o_two_orbit_find D hfinOrb hV
  have hk : k ∉ zs4o_orbitF D.hb D.hmon i₀ := by rw [hOrb]; simp
  have hVeq : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k}) := by
    rw [← hV, zs4o_Wof, hOrb]
    congr 1
    ext z
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
      Set.mem_setOf_eq]
  exact ⟨k, hVeq, zs4o_two_orbit_line D hOrb hk⟩

private lemma zs4o_one_orbit_trans {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) {i₀ : Fin n}
    (hOrb : zs4o_orbitF D.hb D.hmon i₀ = Finset.univ) :
    ∀ i j : Fin n, ∃ y : Y, zs4o_permHom D.hb D.hmon y i = j := by
  intro i j
  have hi : i ∈ zs4o_orbitF D.hb D.hmon i₀ := by rw [hOrb]; exact Finset.mem_univ i
  have hj : j ∈ zs4o_orbitF D.hb D.hmon i₀ := by rw [hOrb]; exact Finset.mem_univ j
  obtain ⟨z, hz⟩ := (zs4o_mem_orbitF D.hb D.hmon).mp hi
  obtain ⟨w, hw⟩ := (zs4o_mem_orbitF D.hb D.hmon).mp hj
  refine ⟨w * z⁻¹, ?_⟩
  rw [map_mul, Equiv.Perm.mul_apply, map_inv, ← hz, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, hw]

private lemma zs4o_one_orbit_hAne {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y)
    (htrans : ∀ i j : Fin n, ∃ y : Y, zs4o_permHom D.hb D.hmon y i = j)
    {uB : Submodule.span (ZMod p) (Set.range b)}
    (hfixu : ∀ y₀ : Y, zs4o_restrictB D.hmon y₀.2 uB = uB)
    (hA0 : (zs4o_basisB D.hb).equivFun uB ≠ 0) :
    ∀ i, (zs4o_basisB D.hb).equivFun uB i ≠ 0 := by
  intro i
  have hex₁ : ∃ i₁, (zs4o_basisB D.hb).equivFun uB i₁ ≠ 0 := by
    by_contra h; simp only [not_exists, not_not] at h
    exact hA0 (funext h)
  obtain ⟨i₁, hi₁⟩ := hex₁
  obtain ⟨y₀, hy₀⟩ := htrans i₁ i
  let Dy := Classical.choice (zs4o_monomialData_exists D.hb D.hmon y₀.2)
  have hσ : Dy.σ i₁ = i := hy₀
  have hcoord := zs4o_equivFun_restrictB D.hb D.hmon y₀.2 Dy uB i₁
  rw [hfixu y₀, hσ] at hcoord
  rw [hcoord]
  exact mul_ne_zero hi₁ (Units.ne_zero _)

private lemma zs4o_one_orbit_ker_apply {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (D : ZS4oData n b Y) {y : Y}
    {Dz : MonomialData b (y : U ≃ₗ[ZMod p] U)} (hσz : ∀ i, Dz.σ i = i)
    (hdz : ∀ i, Dz.d i = 1) : (y : U ≃ₗ[ZMod p] U) = 1 := by
  have hzB : ∀ w ∈ Submodule.span (ZMod p) (Set.range b),
      (y : U ≃ₗ[ZMod p] U) w = w := by
    intro w hw
    refine Submodule.span_induction
      (p := fun w _ => (y : U ≃ₗ[ZMod p] U) w = w) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩
      rw [show (y : U ≃ₗ[ZMod p] U) (b i) = (Dz.d i : ZMod p) • b (Dz.σ i) from Dz.hd i,
        hσz i, hdz i]
      simp
    · simp
    · intro a bb _ _ ha hb; rw [map_add, ha, hb]
    · intro c a _ ha; rw [map_smul, ha]
  ext v
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace Y ⊔ centralizerSpace Y := by
    rw [D.hYs.1.sup_eq_top]; trivial
  obtain ⟨a, ha, bb, hbb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hzB a (D.hle ha), mem_centralizerSpace.mp hbb _ y.2]
  simp

private lemma zs4o_one_orbit_ker {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y)
    (htrans : ∀ i j : Fin n, ∃ y : Y, zs4o_permHom D.hb D.hmon y i = j)
    {y : Y} (hy1 : zs4o_permHom D.hb D.hmon y = 1) : y = 1 := by
  have := D.hFinU
  obtain ⟨-, hfinl, -, -⟩ := zs4o_step1_data D
  have hℓne : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hfinl
    exact Nat.zero_ne_one hfinl
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓne
  let uB : Submodule.span (ZMod p) (Set.range b) := ⟨u, hu.2⟩
  have hfixu : ∀ y₀ : Y, zs4o_restrictB D.hmon y₀.2 uB = uB := by
    intro y₀
    apply Subtype.ext
    rw [zs4o_restrictB, LinearEquiv.ofSubmodules_apply]
    exact mem_centralizerSpace.mp hu.1 _ y₀.2
  have hA0 : (zs4o_basisB D.hb).equivFun uB ≠ 0 := by
    intro hA
    apply hu0
    have hzero : uB = 0 := by
      have h := (zs4o_basisB D.hb).equivFun.symm_apply_apply uB
      rw [hA, map_zero] at h
      exact h.symm
    exact congrArg Subtype.val hzero
  have hAne := zs4o_one_orbit_hAne D htrans hfixu hA0
  let Dz := Classical.choice (zs4o_monomialData_exists D.hb D.hmon y.2)
  have hσz : ∀ i, Dz.σ i = i := by
    intro i
    have hDz : Dz.σ = zs4o_permHom D.hb D.hmon y := rfl
    have := congrArg (fun e : Equiv.Perm (Fin n) => e i) hy1
    rw [← hDz] at this
    simpa using this
  have hdz : ∀ i, Dz.d i = 1 := by
    intro i
    have hcoord := zs4o_equivFun_restrictB D.hb D.hmon y.2 Dz uB i
    rw [hfixu y, hσz i] at hcoord
    have hmul : (zs4o_basisB D.hb).equivFun uB i * (Dz.d i : ZMod p) =
        (zs4o_basisB D.hb).equivFun uB i * 1 := by
      rw [mul_one]; exact hcoord.symm
    exact Units.ext (mul_left_cancel₀ (hAne i) hmul)
  exact Subtype.ext (zs4o_one_orbit_ker_apply D hσz hdz)

private lemma zs4o_one_orbit_inj {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y)
    (htrans : ∀ i j : Fin n, ∃ y : Y, zs4o_permHom D.hb D.hmon y i = j) :
    Function.Injective (zs4o_permHom D.hb D.hmon) := by
  intro y y' hyy
  have h1 : zs4o_permHom D.hb D.hmon (y'⁻¹ * y : Y) = 1 := by
    rw [map_mul, map_inv, hyy, inv_mul_cancel]
  have hz1 : y'⁻¹ * y = 1 := zs4o_one_orbit_ker D htrans h1
  rw [inv_mul_eq_one] at hz1
  exact hz1.symm

private lemma zs4o_one_orbit_surj {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y)
    (htrans : ∀ i j : Fin n, ∃ y : Y, zs4o_permHom D.hb D.hmon y i = j) :
    Function.Surjective (zs4o_permHom D.hb D.hmon) := by
  have := D.hFinU
  have hSclosure : (⊤ : Subgroup Y) =
      Subgroup.closure {t : Y | IsRefl p (t : U ≃ₗ[ZMod p] U)} := by
    let S : Set Y := {t : Y | IsRefl p (t : U ≃ₗ[ZMod p] U)}
    have hSR : Y.subtype '' S = {s : U ≃ₗ[ZMod p] U | s ∈ Y ∧ IsRefl p s} := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t.2, ht⟩
      · rintro ⟨hsY, hsR⟩; exact ⟨⟨s, hsY⟩, hsR, rfl⟩
    refine le_antisymm ?_ le_top
    intro t _
    have ht : (t : U ≃ₗ[ZMod p] U) ∈ (Subgroup.closure S).map Y.subtype := by
      rw [MonoidHom.map_closure, hSR, ← D.hY]; exact t.2
    obtain ⟨s, hs, hst⟩ := ht
    have hst' : s = t := Y.subtype_injective hst
    rwa [hst'] at hs
  let T : Set (Equiv.Perm (Fin n)) := {σ | σ ∈ (zs4o_permHom D.hb D.hmon).range ∧ σ.IsSwap}
  have hrange' : (zs4o_permHom D.hb D.hmon).range = Subgroup.closure
      ((zs4o_permHom D.hb D.hmon) '' {t : Y | IsRefl p (t : U ≃ₗ[ZMod p] U)}) := by
    rw [MonoidHom.range_eq_map, hSclosure, MonoidHom.map_closure]
  have hsub : (zs4o_permHom D.hb D.hmon) '' {t : Y | IsRefl p (t : U ≃ₗ[ZMod p] U)} ⊆
      Subgroup.closure T := by
    rintro σ ⟨t, ht, rfl⟩
    let D' := Classical.choice (zs4o_monomialData_exists D.hb D.hmon t.2)
    have hD : D'.σ = zs4o_permHom D.hb D.hmon t := rfl
    rcases zs4o_perm_isSwap_or_one D.hp D.hb D.hle t.2 ht D' with h | h
    · rw [← hD, h]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨MonoidHom.mem_range.mpr ⟨t, rfl⟩, hD ▸ h⟩
  have hrange : (zs4o_permHom D.hb D.hmon).range = Subgroup.closure T := by
    apply le_antisymm
    · rw [hrange', Subgroup.closure_le]; exact hsub
    · rw [Subgroup.closure_le]; rintro σ ⟨hσ, -⟩; exact hσ
  have hTclosure : Subgroup.closure T = ⊤ := by
    have hpre : MulAction.IsPretransitive (Subgroup.closure T) (Fin n) := by
      refine ⟨fun i j => ?_⟩
      obtain ⟨y, hy⟩ := htrans i j
      refine ⟨⟨zs4o_permHom D.hb D.hmon y, ?_⟩, ?_⟩
      · rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
      · exact hy
    exact closure_of_isSwap_of_isPretransitive (fun σ hσ => hσ.2)
  intro σ
  have hmem : σ ∈ (zs4o_permHom D.hb D.hmon).range := by
    rw [hrange, hTclosure]; exact Subgroup.mem_top σ
  exact MonoidHom.mem_range.mp hmem

private lemma zs4o_one_orbit {n : ℕ} {b : Fin n → U} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (D : ZS4oData n b Y) {i₀ : Fin n}
    (hfinOrb : Module.finrank (ZMod p)
      ↥(zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀)) =
      (zs4o_orbitF D.hb D.hmon i₀).card)
    (htop : zs4o_Wof (p := p) (b := b) (zs4o_orbitF D.hb D.hmon i₀) =
      Submodule.span (ZMod p) (Set.range b)) :
    Nat.card Y = n.factorial := by
  have := D.hFinU
  have hfinB : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range b)) = n := by
    rw [finrank_span_eq_card D.hb, Fintype.card_fin]
  have hcard : (zs4o_orbitF D.hb D.hmon i₀).card = n := by
    rw [← hfinOrb, htop, hfinB]
  have hOrb : zs4o_orbitF D.hb D.hmon i₀ = Finset.univ := by
    rw [← Finset.card_eq_iff_eq_univ, hcard, Fintype.card_fin]
  have htrans := zs4o_one_orbit_trans D hOrb
  have hbij : Function.Bijective (zs4o_permHom D.hb D.hmon) :=
    ⟨zs4o_one_orbit_inj D htrans, zs4o_one_orbit_surj D htrans⟩
  have hcardY : Nat.card Y = Nat.card (Equiv.Perm (Fin n)) :=
    Nat.card_congr (Equiv.ofBijective (zs4o_permHom D.hb D.hmon) hbij)
  rw [hcardY, Nat.card_perm, Nat.card_fin]

theorem exists_span_eq_or_card_eq_factorial (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} (hn : 3 ≤ n) {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hY : ReflGen p Y)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hle : HardMathSupport.Kantor79.commutatorSpace Y ≤
      Submodule.span (ZMod p) (Set.range b))
    (hYs : SplitSupport Y (n - 1))
    (hirr : ∀ W : Submodule (ZMod p) U, W ≤ HardMathSupport.Kantor79.commutatorSpace Y →
      (∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) →
        W = ⊥ ∨ W = HardMathSupport.Kantor79.commutatorSpace Y) :
    (∃ k, HardMathSupport.Kantor79.commutatorSpace Y =
        Submodule.span (ZMod p) (b '' {i | i ≠ k}) ∧
      centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
        Submodule.span (ZMod p) {b k}) ∨
    Nat.card Y = n.factorial := by
  classical
  let D : ZS4oData n b Y :=
    ⟨hp, hn, hb, hY, hmon, hle, hYs, hirr, ‹Module.Finite (ZMod p) U›⟩
  obtain ⟨i₀, hV | htop, hfinOrb⟩ := zs4o_main_setup D
  · exact Or.inl (zs4o_two_orbit D hfinOrb hV)
  · exact Or.inr (zs4o_one_orbit D hfinOrb htop)

private lemma zs4o_pow_eq {m n' : ℕ} (hn : 2 ≤ n') (h : m ^ (n' - 1) = n' + 1) :
    (m = 3 ∧ n' = 2) ∨ (m = 2 ∧ n' = 3) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [zero_pow (by omega), eq_comm] at h
    omega
  · rcases Nat.eq_or_lt_of_le
      (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)) with hm1 | hm2
    · subst hm1
      rw [one_pow] at h
      omega
    · rcases lt_or_ge n' 3 with hn3 | hn3
      · have hn' : n' = 2 := by omega
        subst hn'
        rw [show 2 - 1 = 1 from rfl, pow_one] at h
        exact Or.inl ⟨h, rfl⟩
      · rcases lt_or_ge n' 4 with hn4 | hn4
        · have hn' : n' = 3 := by omega
          subst hn'
          refine Or.inr ⟨?_, rfl⟩
          have hmle : m ≤ 2 := by
            by_contra hmc
            have hm3 : 3 ≤ m := by omega
            have h9 : 9 ≤ m ^ 2 := by
              calc 9 = 3 ^ 2 := by norm_num
                _ ≤ m ^ 2 := Nat.pow_le_pow_left hm3 2
            rw [show 3 - 1 = 2 from rfl] at h
            omega
          omega
        · exfalso
          obtain ⟨k, hk⟩ : ∃ k, n' = k + 4 := ⟨n' - 4, by omega⟩
          subst hk
          rw [show k + 4 - 1 = k + 3 by omega] at h
          have hge := Nat.pow_le_pow_left hm2 (k + 3)
          have hval : 2 ^ (k + 3) = 8 * 2 ^ k := by
            rw [pow_add]
            ring
          have hge : 2 ^ (k + 3) ≤ m ^ (k + 3) :=
            Nat.pow_le_pow_left (show 2 ≤ m by omega) (k + 3)
          have hltk : k < 2 ^ k := Nat.lt_two_pow_self
          omega

private lemma zs4o_no_one_orbit_gmmn (_hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : 3 ≤ n) {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYs : SplitSupport Y (n - 1))
    (g : Module.Basis (Fin (n - 1)) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin (n - 1)} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = gmmn p g j₀ j₁ ζ)
    (hexc : ¬ (n = 3 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 3 ∨ orderOf ζ = 4)) ∧
      ¬ (n = 4 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 3)) ∧ ¬ (n = 5 ∧ orderOf ζ = 2))
    (hcard : Nat.card Y = n.factorial) : False := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hn' : 2 ≤ n' := by omega
  have hmoved : Nat.card (movedGroup Y) = Nat.card Y := card_movedGroup_of_splitSupport hYs
  have hcardm : Nat.card (gmmn p g j₀ j₁ ζ) = Nat.card Y := by
    rw [← hmoved, hYg]
  rw [← hcardm, card_gmmn hn' g hj ζ, Nat.factorial_succ] at hcard
  have hpos : 0 < n'.factorial := Nat.factorial_pos n'
  have heq : orderOf ζ ^ (n' - 1) = n' + 1 := by
    have h : n'.factorial * (n' + 1) = n'.factorial * orderOf ζ ^ (n' - 1) := by
      rw [mul_comm n'.factorial (n' + 1), mul_comm n'.factorial (orderOf ζ ^ (n' - 1)), hcard]
    exact (Nat.eq_of_mul_eq_mul_left hpos h).symm
  rcases zs4o_pow_eq hn' heq with ⟨h3, h2⟩ | ⟨h2, h3⟩
  · exact hexc.1 ⟨by omega, Or.inl (by omega)⟩
  · exact hexc.2.1 ⟨by omega, Or.inl (by omega)⟩

private lemma zs4o_not_smul_eq {n : ℕ} {b : Fin n → U}
    (hb : LinearIndependent (ZMod p) b) {i k : Fin n} (hik : i ≠ k) {a : ZMod p}
    (_ha : a ≠ 0) (h : b i = a • b k) : False := by
  have h' : (1 : ZMod p) • b i = a • b k := by rwa [one_smul]
  have key := (linearIndependent_iff'ₛ.mp hb) ({i, k} : Finset (Fin n))
    (fun j => if j = i then 1 else 0) (fun j => if j = k then a else 0)
  have hsum : ∑ j ∈ ({i, k} : Finset (Fin n)), (if j = i then (1 : ZMod p) else 0) • b j =
      ∑ j ∈ ({i, k} : Finset (Fin n)), (if j = k then a else 0) • b j := by
    rw [Finset.sum_pair hik, Finset.sum_pair hik]
    simpa [hik, Ne.symm hik] using h'
  have hii := key hsum i (by simp)
  rw [if_pos rfl, if_neg hik] at hii
  exact one_ne_zero hii

private lemma zs4o_bk_mem_centralizer {n : ℕ} {b : Fin n → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} {k : Fin n}
    (hC : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k}) :
    b k ∈ centralizerSpace Y := by
  have hle : Submodule.span (ZMod p) {b k} ≤ centralizerSpace Y := by
    rw [← hC]; exact inf_le_left
  exact hle (Submodule.subset_span (Set.mem_singleton (b k)))

private noncomputable def zs4o_coordV {n' : ℕ} {b : Fin (n' + 1) → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} {k : Fin (n' + 1)}
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k})) (i : Fin n') :
    HardMathSupport.Kantor79.commutatorSpace Y :=
  ⟨b (k.succAbove i), by
    rw [hV]
    exact Submodule.subset_span ⟨k.succAbove i, Fin.succAbove_ne k i, rfl⟩⟩

private lemma zs4o_coordV_li {n' : ℕ} {b : Fin (n' + 1) → U}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} {k : Fin (n' + 1)}
    (hb : LinearIndependent (ZMod p) b)
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k})) :
    LinearIndependent (ZMod p) (zs4o_coordV (Y := Y) hV) := by
  have hli : LinearIndependent (ZMod p)
      (fun i => ((zs4o_coordV (Y := Y) hV i :
        HardMathSupport.Kantor79.commutatorSpace Y) : U)) := by
    simpa [Function.comp_def, zs4o_coordV] using
      hb.comp k.succAbove (Fin.succAbove_right_injective (p := k))
  exact LinearIndependent.of_comp (Submodule.subtype _) (by simpa [Function.comp_def] using hli)

private lemma zs4o_coordV_index_ne {n' : ℕ}
    {b : Fin (n' + 1) → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {k : Fin (n' + 1)} (hbk : b k ∈ centralizerSpace Y)
    {i : Fin n'} {x : Y} {j : Fin (n' + 1)} {a : ZMod p}
    (ha : (x : U ≃ₗ[ZMod p] U) (b (k.succAbove i)) = a • b j) (ha0 : a ≠ 0) : j ≠ k := by
  intro hjk
  have hxi : (x : U ≃ₗ[ZMod p] U) (b (k.succAbove i)) = a • b k := by rw [ha, hjk]
  have hfix : (x : U ≃ₗ[ZMod p] U).symm (b k) = b k :=
    (mem_centralizerSpace.mp hbk) _ (Y.inv_mem x.2)
  have hcontra : b (k.succAbove i) = a • b k := by
    calc b (k.succAbove i) =
          (x : U ≃ₗ[ZMod p] U).symm ((x : U ≃ₗ[ZMod p] U) (b (k.succAbove i))) :=
          ((x : U ≃ₗ[ZMod p] U).symm_apply_apply _).symm
      _ = (x : U ≃ₗ[ZMod p] U).symm (a • b k) := by rw [hxi]
      _ = a • (x : U ≃ₗ[ZMod p] U).symm (b k) := by rw [map_smul]
      _ = a • b k := by rw [hfix]
  exact zs4o_not_smul_eq hb (Fin.succAbove_ne k i) ha0 hcontra

private lemma zs4o_map_coordV [Module.Finite (ZMod p) U] {n' : ℕ} (_hn' : 2 ≤ n')
    {b : Fin (n' + 1) → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    {k : Fin (n' + 1)}
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k}))
    (hC : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k}) (i : Fin n') :
    ∀ z ∈ movedGroup Y, ∃ j',
      (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i}).map
        (z : HardMathSupport.Kantor79.commutatorSpace Y →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace Y) =
        Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV j'} := by
  let c := zs4o_coordV (Y := Y) hV
  have hbk : b k ∈ centralizerSpace Y := zs4o_bk_mem_centralizer hC
  rintro z hz
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
  obtain ⟨j, a, ha⟩ := hmon x x.2 (k.succAbove i)
  have ha0 : a ≠ 0 := by
    intro h0
    have hxe : (x : U ≃ₗ[ZMod p] U) (b (k.succAbove i)) ≠ 0 := by
      intro hx0
      exact hb.ne_zero (k.succAbove i)
        ((x : U ≃ₗ[ZMod p] U).injective (by simpa using hx0))
    rw [ha, h0, zero_smul] at hxe
    exact hxe rfl
  have hjk : j ≠ k := zs4o_coordV_index_ne hb hbk ha ha0
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := k) hjk
  refine ⟨j', ?_⟩
  have hz_apply : (restrictHom Y (HardMathSupport.Kantor79.commutatorSpace Y)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x) (c i) = a • c j' := by
    apply Subtype.ext
    rw [restrictHom_apply, Submodule.coe_smul]
    show (x : U ≃ₗ[ZMod p] U) (b (k.succAbove i)) = a • b (k.succAbove j')
    rw [ha, hj']
  have himg : ((restrictHom Y (HardMathSupport.Kantor79.commutatorSpace Y)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x : _) '' ({c i} : Set _)) =
      {a • c j'} := by
    rw [Set.image_singleton]
    exact congrArg Set.singleton hz_apply
  rw [Submodule.map_span]
  change Submodule.span (ZMod p) (((restrictHom Y (HardMathSupport.Kantor79.commutatorSpace Y)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x : _) : _) '' ({c i} : Set _)) =
    Submodule.span (ZMod p) {c j'}
  rw [himg, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha0)]

private lemma zs4o_isImprimSystem_gmmn [Module.Finite (ZMod p) U] {n' : ℕ} (hn' : 2 ≤ n')
    {b : Fin (n' + 1) → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hYs : SplitSupport Y n')
    {k : Fin (n' + 1)}
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k}))
    (hC : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k}) :
    IsImprimSystem (movedGroup Y)
      (fun i => Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i}) := by
  let c := zs4o_coordV (Y := Y) hV
  have hli : LinearIndependent (ZMod p) c := zs4o_coordV_li hb hV
  have hfinV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) = n' :=
    hYs.2.1
  have hsup : ⨆ i, Submodule.span (ZMod p) {c i} = ⊤ := by
    rw [← Submodule.span_range_eq_iSup]
    have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c)) = n' := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfin, hfinV])
  refine ⟨by omega, fun i => ?_, hli.iSupIndep_span_singleton, hsup, ?_⟩
  · intro hbot
    have hzero : c i = 0 := Submodule.span_singleton_eq_bot.mp hbot
    exact hli.ne_zero i hzero
  · intro z hz i
    exact zs4o_map_coordV hn' hb hmon hV hC i z hz

private lemma zs4o_coordV_spans_gmmn [Module.Finite (ZMod p) U] {n' : ℕ} (hn' : 2 ≤ n')
    {b : Fin (n' + 1) → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hYs : SplitSupport Y n')
    (g : Module.Basis (Fin n') (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin n'} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = gmmn p g j₀ j₁ ζ) (hζ : orderOf ζ ≠ 1)
    (hexc' : ¬ (n' = 2 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 4)) ∧ ¬ (n' = 3 ∧ orderOf ζ = 3) ∧
      ¬ (n' = 4 ∧ orderOf ζ = 2))
    {k : Fin (n' + 1)}
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k}))
    (hC : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k}) :
    ∀ i, ∃ j, Submodule.span (ZMod p)
      {((g i : HardMathSupport.Kantor79.commutatorSpace Y) : U)} =
      Submodule.span (ZMod p) {b j} := by
  have hW := zs4o_isImprimSystem_gmmn hn' hb hmon hYs hV hC
  rw [hYg] at hW
  have hex : ∀ i, ∃ σ : Fin n', Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i} =
      Submodule.span (ZMod p) {g σ} := fun i =>
    eq_span_of_isImprimSystem_gmmn hn' g hj hζ hexc' hW i
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i i' hii
    by_contra hne
    have hd := hW.2.2.1.pairwiseDisjoint hne
    have hd' : Disjoint (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i})
        (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i'}) := hd
    rw [hσ i, hσ i', hii] at hd'
    have hbot : Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i} = ⊥ := by
      rw [hσ i, hii]
      have := disjoint_iff.mp hd'
      rwa [inf_idem] at this
    exact hW.2.1 i hbot
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective hσinj
  intro i
  obtain ⟨i', rfl⟩ := hσsurj i
  refine ⟨k.succAbove i', ?_⟩
  have hmap : (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i'}).map
      (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace Y)) =
      (Submodule.span (ZMod p) {g (σ i')}).map
        (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace Y)) := by
    rw [hσ i']
  rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton] at hmap
  simpa [zs4o_coordV] using hmap.symm

private lemma zs4o_coordV_spans_g2mmn [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n' : ℕ}
    (hn' : 2 ≤ n') {b : Fin (n' + 1) → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hYs : SplitSupport Y n')
    (g : Module.Basis (Fin n') (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin n'} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = g2mmn p g j₀ j₁ ζ)
    (hexc' : ¬ (n' = 2 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)))
    {k : Fin (n' + 1)}
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      Submodule.span (ZMod p) (b '' {i | i ≠ k}))
    (hC : centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b k}) :
    ∀ i, ∃ j, Submodule.span (ZMod p)
      {((g i : HardMathSupport.Kantor79.commutatorSpace Y) : U)} =
      Submodule.span (ZMod p) {b j} := by
  have hW := zs4o_isImprimSystem_gmmn hn' hb hmon hYs hV hC
  rw [hYg] at hW
  have hex : ∀ i, ∃ σ : Fin n', Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i} =
      Submodule.span (ZMod p) {g σ} := fun i =>
    eq_span_of_isImprimSystem_g2mmn hp hn' g hj hexc' hW i
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i i' hii
    by_contra hne
    have hd := hW.2.2.1.pairwiseDisjoint hne
    have hd' : Disjoint (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i})
        (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i'}) := hd
    rw [hσ i, hσ i', hii] at hd'
    have hbot : Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i} = ⊥ := by
      rw [hσ i, hii]
      have := disjoint_iff.mp hd'
      rwa [inf_idem] at this
    exact hW.2.1 i hbot
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective hσinj
  intro i
  obtain ⟨i', rfl⟩ := hσsurj i
  refine ⟨k.succAbove i', ?_⟩
  have hmap : (Submodule.span (ZMod p) {zs4o_coordV (Y := Y) hV i'}).map
      (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace Y)) =
      (Submodule.span (ZMod p) {g (σ i')}).map
        (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace Y)) := by
    rw [hσ i']
  rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton] at hmap
  simpa [zs4o_coordV] using hmap.symm

private lemma zs4o_gmmn_one_fixes_sum [Module.Finite (ZMod p) U] {n' : ℕ}
    {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    (g : Module.Basis (Fin n') (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin n'} {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = gmmn p g j₀ j₁ ζ) (hζ1 : orderOf ζ = 1) :
    ∀ z ∈ movedGroup Y, z (∑ i, g i) = ∑ i, g i := by
  have hζ : ζ = 1 := orderOf_eq_one_iff.mp hζ1
  intro z hz
  rw [hYg, hζ] at hz
  refine Subgroup.closure_induction
    (p := fun z _ => z (∑ i, g i) = ∑ i, g i) ?_ ?_ ?_ ?_ hz
  · rintro x (⟨σ, rfl⟩ | hx)
    · rw [map_sum]
      simp only [permMap_apply_basis]
      exact Fintype.sum_equiv σ (fun i => g (σ i)) (fun i => g i) (fun _ => rfl)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [pairUnit_one, diagMap_one]
      rfl
  · rfl
  · intro x y _ _ hx hy; rw [LinearEquiv.mul_apply, hy, hx]
  · intro x _ hx
    have h2 : x⁻¹ (∑ i, g i) = x⁻¹ (x (∑ i, g i)) := by rw [hx]
    rw [h2, ← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl

private lemma zs4o_proper_fixed_line [Module.Finite (ZMod p) U] {n' : ℕ} (hn' : 2 ≤ n')
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYs : SplitSupport Y n')
    {s : HardMathSupport.Kantor79.commutatorSpace Y} (hs : s ≠ 0)
    (hfix : ∀ z ∈ movedGroup Y, z s = s) : False := by
  let V := HardMathSupport.Kantor79.commutatorSpace Y
  have hXinv : ∀ x ∈ Y, ∀ w ∈ Submodule.span (ZMod p) {(s : U)},
      x w ∈ Submodule.span (ZMod p) {(s : U)} := by
    intro x hx w hw
    rw [Submodule.mem_span_singleton] at hw ⊢
    obtain ⟨c, rfl⟩ := hw
    refine ⟨c, ?_⟩
    rw [map_smul]
    congr 1
    have hfix := hfix (restrictHom Y V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩)
      (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
    have hcoe : ((restrictHom Y V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩) s :
        U) = (x : U ≃ₗ[ZMod p] U) (s : U) := rfl
    rw [← hcoe, hfix]
  have hXle : Submodule.span (ZMod p) {(s : U)} ≤ V := by
    rw [Submodule.span_le]
    rintro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact s.2
  have hsU : (s : U) ≠ 0 := fun h => hs (Subtype.ext h)
  have hXne : Submodule.span (ZMod p) {(s : U)} ≠ ⊥ :=
    fun h => hsU (Submodule.span_singleton_eq_bot.mp h)
  have hXfin : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {(s : U)}) = 1 :=
    finrank_span_singleton hsU
  have hVfin : Module.finrank (ZMod p) V = n' := hYs.2.1
  have hXneV : Submodule.span (ZMod p) {(s : U)} ≠ V := by
    intro hEq
    have h1 : (1 : ℕ) = n' := by
      have hc : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {(s : U)}) =
          Module.finrank (ZMod p) V := by rw [hEq]
      rw [hXfin, hVfin] at hc
      exact hc
    omega
  rcases hYs.2.2 (Submodule.span (ZMod p) {(s : U)}) bot_le hXle hXinv with h | h
  · exact hXne h
  · exact hXneV h

private lemma zs4o_no_one_orbit_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : 3 ≤ n) {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYs : SplitSupport Y (n - 1))
    (g : Module.Basis (Fin (n - 1)) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin (n - 1)} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = g2mmn p g j₀ j₁ ζ)
    (hexc : ¬ (n = 3 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)))
    (hcard : Nat.card Y = n.factorial) : False := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hn' : 2 ≤ n' := by omega
  have hmoved : Nat.card (movedGroup Y) = Nat.card Y := card_movedGroup_of_splitSupport hYs
  have hcardm : Nat.card (g2mmn p g j₀ j₁ ζ) = Nat.card Y := by rw [← hmoved, hYg]
  rw [← hcardm, card_g2mmn hp hn' g hj ζ, Nat.factorial_succ] at hcard
  have hpos : 0 < n'.factorial := Nat.factorial_pos n'
  have heq : 2 * Nat.lcm 2 (orderOf ζ) ^ (n' - 1) = n' + 1 := by
    have h : n'.factorial * (n' + 1) =
        n'.factorial * (2 * Nat.lcm 2 (orderOf ζ) ^ (n' - 1)) := by
      rw [mul_comm n'.factorial (n' + 1),
        mul_comm n'.factorial (2 * Nat.lcm 2 (orderOf ζ) ^ (n' - 1)), hcard]
    exact (Nat.eq_of_mul_eq_mul_left hpos h).symm
  have hL2 : 2 ≤ Nat.lcm 2 (orderOf ζ) :=
    Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ)) (Nat.dvd_lcm_left 2 _)
  have h2 : 2 ^ n' = 2 * 2 ^ (n' - 1) := by
    conv_lhs => rw [show n' = (n' - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hnle : n' ≤ 2 ^ (n' - 1) := by
    have := Nat.lt_two_pow_self (n := n' - 1)
    omega
  have hge : 2 ^ n' ≤ 2 * Nat.lcm 2 (orderOf ζ) ^ (n' - 1) := by
    rw [h2]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hL2 _)
  have hgt : n' + 1 < 2 ^ n' := by rw [h2]; omega
  omega

private lemma zs4o_zeta_one_false [Module.Finite (ZMod p) U] {n' : ℕ} (hn' : 2 ≤ n')
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYs : SplitSupport Y n')
    (g : Module.Basis (Fin n') (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin n'} (_hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ}
    (hYg : movedGroup Y = gmmn p g j₀ j₁ ζ) (hζ1 : orderOf ζ = 1) : False := by
  let V := HardMathSupport.Kantor79.commutatorSpace Y
  let s : V := ∑ i, g i
  have hs_ne : s ≠ 0 := by
    intro hs
    have h1 : (g.equivFun s) j₀ = 1 := by
      rw [show s = ∑ i, g i from rfl, map_sum]
      simp only [Finset.sum_apply, Module.Basis.equivFun_self]
      rw [Finset.sum_ite_eq' Finset.univ j₀ (fun _ => (1 : ZMod p))]
      simp
    rw [hs, map_zero] at h1
    exact zero_ne_one h1
  have hs_fix : ∀ z ∈ movedGroup Y, z s = s := by
    intro z hz
    exact zs4o_gmmn_one_fixes_sum g hYg hζ1 z hz
  exact zs4o_proper_fixed_line hn' hYs hs_ne hs_fix

theorem span_eq_of_splitSupport_gmmn (hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : 3 ≤ n) {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hY : ReflGen p Y)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hle : HardMathSupport.Kantor79.commutatorSpace Y ≤ Submodule.span (ZMod p) (Set.range b))
    (hYs : SplitSupport Y (n - 1))
    (g : Module.Basis (Fin (n - 1)) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin (n - 1)} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} (hYg : movedGroup Y = gmmn p g j₀ j₁ ζ)
    (hexc : ¬ (n = 3 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 3 ∨ orderOf ζ = 4)) ∧
      ¬ (n = 4 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 3)) ∧ ¬ (n = 5 ∧ orderOf ζ = 2)) :
    (∀ i, ∃ j, Submodule.span (ZMod p) {((g i : HardMathSupport.Kantor79.commutatorSpace Y) : U)} =
      Submodule.span (ZMod p) {b j}) ∧
    ∃ j, centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b j} := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hn' : 2 ≤ n' := by omega
  have hζ : orderOf ζ ≠ 1 := fun h => zs4o_zeta_one_false (by omega) hYs g hj hYg h
  have hexc' : ¬ (n' = 2 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 4)) ∧ ¬ (n' = 3 ∧ orderOf ζ = 3) ∧
      ¬ (n' = 4 ∧ orderOf ζ = 2) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h2, hζ2⟩; exact hexc.1 ⟨by omega, by tauto⟩
    · rintro ⟨h3, hζ3⟩; exact hexc.2.1 ⟨by omega, by omega⟩
    · rintro ⟨h4, hζ4⟩; exact hexc.2.2 ⟨by omega, by omega⟩
  have hirr : ∀ W : Submodule (ZMod p) U, W ≤ HardMathSupport.Kantor79.commutatorSpace Y →
      (∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) →
        W = ⊥ ∨ W = HardMathSupport.Kantor79.commutatorSpace Y :=
    fun W hW hinv => hYs.2.2 W bot_le hW hinv
  rcases exists_span_eq_or_card_eq_factorial hp (by omega) hb hY hmon hle hYs hirr with
    ⟨k, hV, hC⟩ | hcard
  · exact ⟨zs4o_coordV_spans_gmmn hn' hb hmon hYs g hj hYg hζ hexc' hV hC, k, hC⟩
  · exact absurd (zs4o_no_one_orbit_gmmn hp (by omega) hb hYs g hj hYg hexc hcard) not_false

theorem span_eq_of_splitSupport_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : 3 ≤ n) {b : Fin n → U} (hb : LinearIndependent (ZMod p) b)
    {Y : Subgroup (U ≃ₗ[ZMod p] U)} (hY : ReflGen p Y)
    (hmon : ∀ y ∈ Y, ∀ i, ∃ j, ∃ c : ZMod p, y (b i) = c • b j)
    (hle : HardMathSupport.Kantor79.commutatorSpace Y ≤ Submodule.span (ZMod p) (Set.range b))
    (hYs : SplitSupport Y (n - 1))
    (g : Module.Basis (Fin (n - 1)) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin (n - 1)} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} (hYg : movedGroup Y = g2mmn p g j₀ j₁ ζ)
    (hexc : ¬ (n = 3 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4))) :
    (∀ i, ∃ j, Submodule.span (ZMod p) {((g i : HardMathSupport.Kantor79.commutatorSpace Y) : U)} =
      Submodule.span (ZMod p) {b j}) ∧
    ∃ j, centralizerSpace Y ⊓ Submodule.span (ZMod p) (Set.range b) =
      Submodule.span (ZMod p) {b j} := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hn' : 2 ≤ n' := by omega
  have hexc' : ¬ (n' = 2 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)) := by
    rintro ⟨h2, hζ⟩; exact hexc ⟨by omega, hζ⟩
  have hirr : ∀ W : Submodule (ZMod p) U, W ≤ HardMathSupport.Kantor79.commutatorSpace Y →
      (∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) →
        W = ⊥ ∨ W = HardMathSupport.Kantor79.commutatorSpace Y :=
    fun W hW hinv => hYs.2.2 W bot_le hW hinv
  rcases exists_span_eq_or_card_eq_factorial hp (by omega) hb hY hmon hle hYs hirr with
    ⟨k, hV, hC⟩ | hcard
  · exact ⟨zs4o_coordV_spans_g2mmn hp hn' hb hmon hYs g hj hYg hexc' hV hC, k, hC⟩
  · exact absurd (zs4o_no_one_orbit_g2mmn hp (by omega) hb hYs g hj hYg hexc hcard) not_false

end CFSG.StandardType.ZS

end

module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.LieType.Steinberg.Adjoint

private def lk0xlqlongestCone {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {v | ∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x}

private def lk0xlqlongestP {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {v | IsRoot τ v ∧ v ∈ lk0xlqlongestCone α}

private def lk0xlqlongestN {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {v | IsRoot τ v ∧ -v ∈ lk0xlqlongestCone α}

private def lk0xlqlongestS {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {v | v ∈ lk0xlqlongestP α ∧ w • v ∈ lk0xlqlongestN α}

private theorem lk0xlqlongest_sum_eq_zero
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    (c : ι → ℤ) (h : ∑ x, c x • α x = 0) : ∀ x, c x = 0 := by
  have hli := hind
  rw [Fintype.linearIndependent_iff] at hli
  intro x
  have hc : ∑ y, ((c y : ℤ) : ℚ) • (fun i => ((α y i : ℤ) : ℚ)) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hi : (∑ y, c y * α y i : ℤ) = 0 := by
      have := congrFun h i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have hcast : (∑ y, ((c y : ℤ) : ℚ) * ((α y i : ℤ) : ℚ))
        = ((∑ y, c y * α y i : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun y _ => by push_cast; ring
    rw [hcast, hi, Int.cast_zero]
  have := hli (fun y => ((c y : ℤ) : ℚ)) hc x
  exact_mod_cast this

private theorem lk0xlqlongest_coeff_unique
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    {a b : ι → ℤ} (h : ∑ x, a x • α x = ∑ x, b x • α x) : a = b := by
  have hc : ∑ x, (a x - b x) • α x = 0 := by
    rw [Finset.sum_congr rfl (fun x _ => sub_smul (a x) (b x) (α x)),
      Finset.sum_sub_distrib, h, sub_self]
  funext x
  exact sub_eq_zero.mp (lk0xlqlongest_sum_eq_zero α hind (fun x => a x - b x) hc x)

private theorem lk0xlqlongest_alpha_injective
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι] (α : ι → Fin τ.rank → ℤ)
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ))) :
    Function.Injective α := by
  intro x y hxy
  by_contra hne
  have e1 : (∑ z, (Pi.single x (1 : ℤ) : ι → ℤ) z • α z) = α x := by
    rw [Finset.sum_eq_single x (fun z _ hz => by simp [Pi.single_eq_of_ne hz])
      (fun hz => absurd (Finset.mem_univ x) hz)]
    simp
  have e2 : (∑ z, (Pi.single y (1 : ℤ) : ι → ℤ) z • α z) = α y := by
    rw [Finset.sum_eq_single y (fun z _ hz => by simp [Pi.single_eq_of_ne hz])
      (fun hz => absurd (Finset.mem_univ y) hz)]
    simp
  have hsum : ∑ z,
      ((Pi.single x (1 : ℤ) : ι → ℤ) - (Pi.single y (1 : ℤ) : ι → ℤ)) z
        • α z = 0 := by
    rw [Finset.sum_congr rfl (fun z _ => by rw [Pi.sub_apply, sub_smul]),
      Finset.sum_sub_distrib, e1, e2, hxy, sub_self]
  have hx0 := lk0xlqlongest_sum_eq_zero α hind _ hsum x
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero] at hx0
  exact one_ne_zero hx0

private theorem lk0xlqlongest_cone_add
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    {a b : Fin τ.rank → ℤ} (ha : a ∈ lk0xlqlongestCone α)
    (hb : b ∈ lk0xlqlongestCone α) : a + b ∈ lk0xlqlongestCone α := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hb
  refine ⟨m + k, ?_⟩
  rw [show (∑ x, (((m + k) x : ℕ) : ℤ) • α x)
        = ∑ x, ((m x : ℤ) • α x + (k x : ℤ) • α x) from
      Finset.sum_congr rfl fun x _ => by rw [Pi.add_apply, Nat.cast_add, add_smul],
    Finset.sum_add_distrib]

private theorem lk0xlqlongest_cone_nsmul
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    (c : ℕ) {a : Fin τ.rank → ℤ} (ha : a ∈ lk0xlqlongestCone α) :
    c • a ∈ lk0xlqlongestCone α := by
  induction c with
  | zero => simpa using (show (0 : Fin τ.rank → ℤ) ∈ lk0xlqlongestCone α from
      ⟨fun _ => 0, by simp⟩)
  | succ c ih =>
      rw [succ_nsmul]
      exact lk0xlqlongest_cone_add α ih ha

private theorem lk0xlqlongest_cone_sum
    {τ : Tag} {ι : Type} [Fintype ι] {κ : Type*}
    (α : ι → Fin τ.rank → ℤ) (s : Finset κ) (c : κ → ℕ)
    (g : κ → Fin τ.rank → ℤ) (hg : ∀ x, g x ∈ lk0xlqlongestCone α) :
    (∑ x ∈ s, (c x : ℤ) • g x) ∈ lk0xlqlongestCone α := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact lk0xlqlongest_cone_add α (lk0xlqlongest_cone_nsmul α (c a) (hg a)) ih

private theorem lk0xlqlongest_neg_smul_mem_cone
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    {w : WeylGroup τ} (hwN : ∀ x, w • α x ∈ lk0xlqlongestN α)
    {v : Fin τ.rank → ℤ} (hv : v ∈ lk0xlqlongestCone α) :
    -(w • v) ∈ lk0xlqlongestCone α := by
  obtain ⟨n, rfl⟩ := hv
  have hwv : w • (∑ x, (n x : ℤ) • α x) = ∑ x, (n x : ℤ) • (w • α x) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm w (n x : ℤ) (α x)
  have hneg : -(w • (∑ x, (n x : ℤ) • α x)) = ∑ x, (n x : ℤ) • (-(w • α x)) := by
    rw [hwv, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => (smul_neg (n x : ℤ) (w • α x)).symm
  rw [hneg]
  exact lk0xlqlongest_cone_sum α Finset.univ n (fun x => -(w • α x)) fun x => (hwN x).2

private theorem lk0xlqlongest_union
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v → v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x) ∨
      (∃ n : ι → ℕ, v = -∑ x, (n x : ℤ) • α x))
    {v : Fin τ.rank → ℤ} (hr : IsRoot τ v)
    (hspan : v ∈ Submodule.span ℤ (Set.range α)) :
    v ∈ lk0xlqlongestP α ∨ v ∈ lk0xlqlongestN α := by
  rcases hcone v hr hspan with h | h
  · exact Or.inl ⟨hr, h⟩
  · obtain ⟨n, hn⟩ := h
    exact Or.inr ⟨hr, ⟨n, by rw [hn, neg_neg]⟩⟩

private theorem lk0xlqlongest_disjoint
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    {v : Fin τ.rank → ℤ} (hvP : v ∈ lk0xlqlongestP α)
    (hvN : v ∈ lk0xlqlongestN α) : False := by
  obtain ⟨hrP, n, hn⟩ := hvP
  obtain ⟨hrN, m, hm⟩ := hvN
  have hzero : ∑ x, ((n x : ℤ) + (m x : ℤ)) • α x = 0 := by
    rw [show (∑ x, ((n x : ℤ) + (m x : ℤ)) • α x)
          = ∑ x, ((n x : ℤ) • α x + (m x : ℤ) • α x) from
        Finset.sum_congr rfl fun x _ => add_smul _ _ _,
      Finset.sum_add_distrib, ← hn, ← hm, add_neg_cancel]
  have hn0 : n = 0 := by
    funext x
    have hx := lk0xlqlongest_sum_eq_zero α hind (fun x => (n x : ℤ) + (m x : ℤ)) hzero x
    have : (n x : ℤ) = 0 := by
      have := Int.natCast_nonneg (m x)
      omega
    exact_mod_cast this
  rw [hn, hn0] at hrP
  exact hrP.ne_zero (by simp)

private theorem lk0xlqlongestP_finite
    {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) : (lk0xlqlongestP α).Finite :=
  (finite_setOf_isRoot τ).subset fun _ hv => hv.1

private theorem lk0xlqlongestN_finite
    {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) : (lk0xlqlongestN α).Finite :=
  (finite_setOf_isRoot τ).subset fun _ hv => hv.1

private theorem lk0xlqlongestS_finite
    {τ : Tag} {ι : Type} [Fintype ι]
    (α : ι → Fin τ.rank → ℤ) (w : WeylGroup τ) : (lk0xlqlongestS α w).Finite :=
  (lk0xlqlongestP_finite α).subset fun _ hv => hv.1

private theorem lk0xlqlongest_smul_mem_span
    {τ : Tag} {ι : Type} [Fintype ι] (α : ι → Fin τ.rank → ℤ)
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ,
        IsRoot τ γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ})
    {v : Fin τ.rank → ℤ} (hv : v ∈ Submodule.span ℤ (Set.range α)) :
    w • v ∈ Submodule.span ℤ (Set.range α) := by
  classical
  have H : ∀ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ,
        IsRoot τ γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ},
      ∀ v : Fin τ.rank → ℤ, v ∈ Submodule.span ℤ (Set.range α) →
        u • v ∈ Submodule.span ℤ (Set.range α) := by
    intro u hu
    induction hu using Subgroup.closure_induction'' with
    | mem x hx =>
        obtain ⟨γ, hγr, hγs, rfl⟩ := hx
        intro v hv
        rw [rootReflection_smul hγr]
        exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ hγs)
    | inv_mem x hx =>
        obtain ⟨γ, hγr, hγs, rfl⟩ := hx
        intro v hv
        rw [rootReflection_inv hγr, rootReflection_smul hγr]
        exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ hγs)
    | one => intro v hv; simpa using hv
    | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy _ hv)
  exact H w hw v hv

private theorem lk0xlqlongest_sum_sub_smul
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Fin τ.rank → ℤ) (c : ι → ℤ) (x : ι) (d : ℤ) :
    (∑ z, c z • α z) - d • α x =
      ∑ z, (c z - d * (if z = x then 1 else 0)) • α z := by
  ext j
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ z, (c z - d * (if z = x then 1 else 0)) * α z j)
      = (∑ z, c z * α z j) - ∑ z, (d * (if z = x then 1 else 0)) * α z j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => sub_mul _ _ _
  rw [h1]
  congr 1
  rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz])
    (fun hz => absurd (Finset.mem_univ x) hz)]
  simp

private theorem lk0xlqlongest_alpha_mem_P
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Fin τ.rank → ℤ) (hroot : ∀ x, IsRoot τ (α x)) (x : ι) :
    α x ∈ lk0xlqlongestP α := by
  refine ⟨hroot x, ⟨fun y => if y = x then 1 else 0, ?_⟩⟩
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem lk0xlqlongest_reflect_mem_P
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Fin τ.rank → ℤ) (hroot : ∀ x, IsRoot τ (α x))
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v →
      v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x) ∨
      (∃ n : ι → ℕ, v = -∑ x, (n x : ℤ) • α x))
    {v : Fin τ.rank → ℤ} (hvP : v ∈ lk0xlqlongestP α)
    {x : ι} (hvne : v ≠ α x) :
    rootReflection (α x) • v ∈ lk0xlqlongestP α := by
  obtain ⟨hvroot, n, hn⟩ := hvP
  have hex : ∃ y, y ≠ x ∧ 0 < n y := by
    by_contra h
    push Not at h
    have hsingle : v = (n x : ℤ) • α x := by
      rw [hn]
      refine Finset.sum_eq_single x (fun y _ hy => ?_)
        (fun hx => absurd (Finset.mem_univ x) hx)
      have hny0 : n y = 0 := by
        have := h y hy
        omega
      simp [hny0]
    have hm := IsRoot.eq_one_or_neg_one_of_eq_smul hvroot hsingle
    rcases hm with h1 | h1
    · exact absurd (by rw [hsingle, h1, one_smul]) hvne
    · have : (0 : ℤ) ≤ (n x : ℤ) := Int.natCast_nonneg _
      omega
  obtain ⟨y, hyx, hny⟩ := hex
  have hrepr : rootReflection (α x) • v =
      ∑ z, ((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0)) • α z := by
    calc rootReflection (α x) • v = v - corootPair (α x) v • α x :=
          rootReflection_smul (hroot x) v
      _ = (∑ z, (n z : ℤ) • α z) - corootPair (α x) v • α x := by rw [hn]
      _ = ∑ z, ((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0)) • α z :=
          lk0xlqlongest_sum_sub_smul α (fun z => (n z : ℤ)) x (corootPair (α x) v)
  have hrroot : IsRoot τ (rootReflection (α x) • v) := IsRoot.smul hvroot _
  have hrspan : rootReflection (α x) • v ∈ Submodule.span ℤ (Set.range α) := by
    rw [hrepr]
    exact Submodule.sum_mem _ fun z _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self z))
  rcases lk0xlqlongest_union α hcone hrroot hrspan with hP | hN
  · exact hP
  · exfalso
    obtain ⟨m, hm⟩ := hN.2
    have hzero : ∑ z,
        (((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0)) + (m z : ℤ)) • α z = 0 := by
      rw [show (∑ z, (((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0))
              + (m z : ℤ)) • α z)
            = ∑ z, (((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0)) • α z
              + (m z : ℤ) • α z) from Finset.sum_congr rfl fun z _ => add_smul _ _ _,
        Finset.sum_add_distrib, ← hrepr, ← hm, add_neg_cancel]
    have hy0 := lk0xlqlongest_sum_eq_zero α hind
        (fun z => ((n z : ℤ) - corootPair (α x) v * (if z = x then 1 else 0)) + (m z : ℤ))
        hzero y
    have hmy : (0 : ℤ) ≤ (m y : ℤ) := Int.natCast_nonneg _
    simp [hyx] at hy0
    omega

private theorem lk0xlqlongest_ncard_step
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Fin τ.rank → ℤ) (hroot : ∀ x, IsRoot τ (α x))
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v →
      v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x) ∨
      (∃ n : ι → ℕ, v = -∑ x, (n x : ℤ) • α x))
    (w : WeylGroup τ) (x : ι) (hxP : w • α x ∈ lk0xlqlongestP α) :
    (lk0xlqlongestS α (w * rootReflection (α x))).ncard =
      (lk0xlqlongestS α w).ncard + 1 := by
  classical
  set r := rootReflection (α x) with hr
  have hrα : r • α x = -α x := rootReflection_smul_self (hroot x)
  have hrmul : r * r = 1 := rootReflection_mul_self (hroot x)
  have hrperm : ∀ {v : Fin τ.rank → ℤ}, v ∈ lk0xlqlongestP α → v ≠ α x →
      r • v ∈ lk0xlqlongestP α := fun hvP hvne =>
    lk0xlqlongest_reflect_mem_P α hroot hind hcone hvP hvne
  have hrinj : Function.Injective (fun v : Fin τ.rank → ℤ => r • v) := by
    intro a b hab
    have := congrArg (fun z => r • z) hab
    rwa [← mul_smul, hrmul, one_smul, ← mul_smul, hrmul, one_smul] at this
  have hαxP : α x ∈ lk0xlqlongestP α := lk0xlqlongest_alpha_mem_P α hroot x
  have hnegN : -α x ∈ lk0xlqlongestN α :=
    ⟨IsRoot.neg (hroot x), by simpa using hαxP.2⟩
  have hnotmem : α x ∉ (fun v : Fin τ.rank → ℤ => r • v) '' lk0xlqlongestS α w := by
    rintro ⟨v, hvS, hvx⟩
    have hval : v = -α x := by
      have h1 : r • (r • v) = r • α x := by
        have := congrArg (fun z => r • z) hvx
        simpa using this
      rwa [← mul_smul, hrmul, one_smul, hrα] at h1
    exact lk0xlqlongest_disjoint α hind hvS.1 (hval.symm ▸ hnegN)
  have hS : lk0xlqlongestS α (w * r) =
      insert (α x) ((fun v : Fin τ.rank → ℤ => r • v) '' lk0xlqlongestS α w) := by
    ext v
    constructor
    · rintro ⟨hvP, hvN⟩
      by_cases hvx : v = α x
      · exact Or.inl hvx
      · refine Or.inr ⟨r • v, ⟨hrperm hvP hvx, ?_⟩, ?_⟩
        · have : (w * r) • v = w • (r • v) := by rw [mul_smul]
          rwa [this] at hvN
        · show r • (r • v) = v
          rw [← mul_smul, hrmul, one_smul]
    · rintro (rfl | ⟨u, huS, rfl⟩)
      · refine ⟨hαxP, ?_⟩
        have : (w * r) • α x = -(w • α x) := by rw [mul_smul, hrα, smul_neg]
        rw [this]
        exact ⟨IsRoot.neg hxP.1, by
          obtain ⟨n, hn⟩ := hxP.2
          exact ⟨n, by rw [hn, neg_neg]⟩⟩
      · refine ⟨hrperm huS.1 (fun h => ?_), ?_⟩
        · exact lk0xlqlongest_disjoint α hind hxP (h ▸ huS.2)
        · have h1 : (w * r) • (r • u) = w • ((r * r) • u) := by
            rw [mul_smul]
            congr 1
            rw [← mul_smul]
          rw [h1, hrmul, one_smul]
          exact huS.2
  rw [hS, Set.ncard_insert_of_notMem hnotmem
      (hs := (lk0xlqlongestS_finite α w).image (fun v : Fin τ.rank → ℤ => r • v)),
    Set.ncard_image_of_injective _ hrinj]

private theorem lk0xlqlongest_decompose
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Fin τ.rank → ℤ) (hroot : ∀ x, IsRoot τ (α x))
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v →
      v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x) ∨
      (∃ n : ι → ℕ, v = -∑ x, (n x : ℤ) • α x))
    {v : Fin τ.rank → ℤ} (hvP : v ∈ lk0xlqlongestP α)
    (hvne : ∀ y, v ≠ α y) :
    ∃ γ ∈ lk0xlqlongestP α, ∃ δ ∈ lk0xlqlongestP α, v = γ + δ := by
  obtain ⟨hvroot, n, hn⟩ := hvP
  have hex1 : ∃ x, 0 < iform v (α x) := by
    by_contra h
    push Not at h
    have hvv : 0 < iform v v := iform_self_pos_of_isRoot hvroot
    have hsum : iform v v = ∑ x, (n x : ℤ) * iform v (α x) := by
      calc iform v v = iform v (∑ x, (n x : ℤ) • α x) := by rw [hn]
        _ = ∑ x, iform v ((n x : ℤ) • α x) := by
              rw [iform_finset_sum_right Finset.univ v (fun x => (n x : ℤ) • α x)]
        _ = ∑ x, (n x : ℤ) * iform v (α x) := by
              exact Finset.sum_congr rfl fun x _ => by rw [iform_smul_right]
    rw [hsum] at hvv
    have hle : ∑ x, (n x : ℤ) * iform v (α x) ≤ 0 :=
      Finset.sum_nonpos fun x _ =>
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (h x)
    omega
  obtain ⟨x, hxpos⟩ := hex1
  have hex2 : ∃ ε, ε ≠ x ∧ 0 < n ε := by
    by_contra h
    push Not at h
    have hsingle : v = (n x : ℤ) • α x := by
      rw [hn]
      refine Finset.sum_eq_single x (fun y _ hy => ?_)
        (fun hx => absurd (Finset.mem_univ x) hx)
      have hny0 : n y = 0 := by
        have := h y hy
        omega
      simp [hny0]
    have hm := IsRoot.eq_one_or_neg_one_of_eq_smul hvroot hsingle
    rcases hm with h1 | h1
    · exact hvne x (by rw [hsingle, h1, one_smul])
    · have : (0 : ℤ) ≤ (n x : ℤ) := Int.natCast_nonneg _
      omega
  obtain ⟨ε, hεx, hnε⟩ := hex2
  have hsubroot : IsRoot τ (v - α x) :=
    isRoot_sub_of_iform_pos hvroot (hroot x) (hvne x) hxpos
  have hreprsub : v - α x = ∑ z, ((n z : ℤ) - (if z = x then 1 else 0)) • α z := by
    rw [hn]
    simpa using lk0xlqlongest_sum_sub_smul α (fun z => (n z : ℤ)) x 1
  have hsubspan : v - α x ∈ Submodule.span ℤ (Set.range α) := by
    rw [hreprsub]
    exact Submodule.sum_mem _ fun z _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self z))
  rcases lk0xlqlongest_union α hcone hsubroot hsubspan with hP | hN
  · exact ⟨v - α x, hP, α x, lk0xlqlongest_alpha_mem_P α hroot x, by abel⟩
  · exfalso
    obtain ⟨k, hk⟩ := hN.2
    have hzero : ∑ z, (((n z : ℤ) - (if z = x then 1 else 0)) + (k z : ℤ)) • α z = 0 := by
      rw [show (∑ z, (((n z : ℤ) - (if z = x then 1 else 0)) + (k z : ℤ)) • α z)
            = ∑ z, (((n z : ℤ) - (if z = x then 1 else 0)) • α z + (k z : ℤ) • α z) from
          Finset.sum_congr rfl fun z _ => add_smul _ _ _,
        Finset.sum_add_distrib, ← hreprsub, ← hk, add_neg_cancel]
    have hε0 := lk0xlqlongest_sum_eq_zero α hind
      (fun z => ((n z : ℤ) - (if z = x then 1 else 0)) + (k z : ℤ)) hzero ε
    have hkε : (0 : ℤ) ≤ (k ε : ℤ) := Int.natCast_nonneg _
    simp [hεx] at hε0
    omega

theorem lq_longest
    {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι] (α : ι → Fin τ.rank → ℤ)
    (hroot : ∀ x, IsRoot τ (α x))
    (hind : LinearIndependent ℚ (fun x i => ((α x i : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v → v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : ι → ℕ, v = ∑ x, (n x : ℤ) • α x) ∨ (∃ n : ι → ℕ, v = -∑ x, (n x : ℤ) • α x)) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧
        γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ},
      ∃ opp : Equiv.Perm ι, ∀ x, w • α x = -α (opp x) := by
  classical
  let G : Subgroup (WeylGroup τ) :=
    Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧
      γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ}
  let P := lk0xlqlongestP α
  let N := lk0xlqlongestN α
  let S : WeylGroup τ → Set (Fin τ.rank → ℤ) := fun w => lk0xlqlongestS α w
  obtain ⟨w, hwG, hwmax⟩ :=
    Set.exists_max_image (G : Set (WeylGroup τ)) (fun u => (S u).ncard)
      (Set.toFinite _) ⟨1, one_mem G⟩
  have hspan : ∀ (u : WeylGroup τ), u ∈ G → ∀ v : Fin τ.rank → ℤ,
      v ∈ Submodule.span ℤ (Set.range α) → u • v ∈ Submodule.span ℤ (Set.range α) :=
    fun u hu v hv => lk0xlqlongest_smul_mem_span α hu hv
  have hwN : ∀ x, w • α x ∈ N := by
    intro x
    by_contra hxN
    have hxP : w • α x ∈ P := by
      have hr : IsRoot τ (w • α x) := IsRoot.smul (hroot x) w
      have hs : w • α x ∈ Submodule.span ℤ (Set.range α) :=
        hspan w hwG (α x) (Submodule.subset_span (Set.mem_range_self x))
      rcases lk0xlqlongest_union α hcone hr hs with h | h
      · exact h
      · exact absurd h hxN
    have hmem : w * rootReflection (α x) ∈ G :=
      mul_mem hwG (Subgroup.subset_closure
        ⟨α x, hroot x, Submodule.subset_span (Set.mem_range_self x), rfl⟩)
    have hle := hwmax (w * rootReflection (α x)) hmem
    have hstepx := lk0xlqlongest_ncard_step α hroot hind hcone w x hxP
    simp only [S] at hle hstepx
    omega
  have hwPN : ∀ v ∈ P, w • v ∈ N := by
    intro v hvP
    refine ⟨IsRoot.smul hvP.1 w, ?_⟩
    obtain ⟨m, hm⟩ := lk0xlqlongest_neg_smul_mem_cone α (fun x => hwN x) hvP.2
    exact ⟨m, hm⟩
  have hPfin : P.Finite := lk0xlqlongestP_finite α
  have hNfin : N.Finite := lk0xlqlongestN_finite α
  have hNncard : N.ncard = P.ncard := by
    have hN_eq : N = (fun v : Fin τ.rank → ℤ => -v) '' P := by
      ext v
      constructor
      · rintro ⟨hvroot, hvcone⟩
        exact ⟨-v, ⟨IsRoot.neg hvroot, by simpa using hvcone⟩, by simp⟩
      · rintro ⟨u, ⟨hur, huc⟩, rfl⟩
        exact ⟨IsRoot.neg hur, by simpa using huc⟩
    rw [hN_eq, Set.ncard_image_of_injective P neg_injective]
  have hwinj : Function.Injective (fun v : Fin τ.rank → ℤ => w • v) := by
    intro a b hab
    have := congrArg (fun z => w⁻¹ • z) hab
    simpa [← mul_smul] using this
  have hwPeqN : (fun v : Fin τ.rank → ℤ => w • v) '' P = N := by
    refine Set.eq_of_subset_of_ncard_le (fun u hu => ?_) ?_ hNfin
    · rcases hu with ⟨v, hvP, rfl⟩
      exact hwPN v hvP
    · rw [Set.ncard_image_of_injective P hwinj, hNncard]
  let T : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) := fun v => -(w • v)
  have hTsub : T '' P ⊆ P := by
    rintro u ⟨v, hvP, rfl⟩
    exact ⟨IsRoot.neg (hwPN v hvP).1, (hwPN v hvP).2⟩
  have hTinj : Function.Injective T := by
    intro a b hab
    have : w • a = w • b := by
      have := congrArg (fun z => -z) hab
      simpa [T] using this
    exact hwinj this
  have hTeq : T '' P = P := by
    refine Set.eq_of_subset_of_ncard_le hTsub ?_ hPfin
    rw [Set.ncard_image_of_injective P hTinj]
  have hbeta : ∀ x, ∃ y, w • α x = -α y := by
    intro x
    have hxP : -(w • α x) ∈ P := ⟨IsRoot.neg (hwN x).1, (hwN x).2⟩
    by_contra h
    push Not at h
    have h' : ∀ y, -(w • α x) ≠ α y := fun y hy => h y (by rw [← hy, neg_neg])
    obtain ⟨γ, hγP, δ, hδP, hsum⟩ := lk0xlqlongest_decompose α hroot hind hcone hxP h'
    obtain ⟨p, hpP, hpT⟩ : ∃ p ∈ P, T p = γ := by
      have : γ ∈ T '' P := by rw [hTeq]; exact hγP
      rcases this with ⟨p, hpP, hpT⟩
      exact ⟨p, hpP, hpT⟩
    obtain ⟨q, hqP, hqT⟩ : ∃ q ∈ P, T q = δ := by
      have : δ ∈ T '' P := by rw [hTeq]; exact hδP
      rcases this with ⟨q, hqP, hqT⟩
      exact ⟨q, hqP, hqT⟩
    have hpw : w • p = -γ := by
      have := congrArg (fun z => -z) hpT
      simpa [T] using this
    have hqw : w • q = -δ := by
      have := congrArg (fun z => -z) hqT
      simpa [T] using this
    have hα : α x = p + q := by
      have h2 : w • α x = -(γ + δ) := by
        have := congrArg (fun z => -z) hsum
        simpa using this
      have h3 : w • (p + q) = -(γ + δ) := by rw [smul_add, hpw, hqw]; abel
      have h4 : w • α x = w • (p + q) := by rw [h2, h3]
      have := congrArg (fun z => w⁻¹ • z) h4
      simpa [← mul_smul] using this
    obtain ⟨mp, hmp⟩ := hpP.2
    obtain ⟨mq, hmq⟩ := hqP.2
    have hpq : ∑ z, ((mp z + mq z : ℕ) : ℤ) • α z
        = ∑ z, ((if z = x then 1 else 0 : ℕ) : ℤ) • α z := by
      have h1 : p + q = ∑ z, ((mp z + mq z : ℕ) : ℤ) • α z := by
        rw [hmp, hmq,
          show (∑ z, ((mp z + mq z : ℕ) : ℤ) • α z)
              = ∑ z, ((mp z : ℤ) • α z + (mq z : ℤ) • α z) from
            Finset.sum_congr rfl fun z _ => by rw [Nat.cast_add, add_smul],
          Finset.sum_add_distrib]
      have h2 : α x = ∑ z, ((if z = x then 1 else 0 : ℕ) : ℤ) • α z := by
        rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz])
          (fun hz => absurd (Finset.mem_univ x) hz)]
        simp
      rw [← h1, ← h2, hα]
    have hcoeff := lk0xlqlongest_coeff_unique α hind hpq
    have hmp0 : ∀ z, z ≠ x → mp z = 0 := by
      intro z hz
      have := congrFun hcoeff z
      simp [hz] at this
      omega
    have hmq0 : ∀ z, z ≠ x → mq z = 0 := by
      intro z hz
      have := congrFun hcoeff z
      simp [hz] at this
      omega
    have hpx : mp x ≠ 0 := by
      intro h0
      apply hγP.1.ne_zero
      rw [← hpT]
      have hzero : p = 0 := by
        rw [hmp, Finset.sum_eq_single x (fun z _ hz => by simp [hmp0 z hz])
          (fun hz => absurd (Finset.mem_univ x) hz)]
        simp [h0]
      rw [hzero]
      simp [T]
    have hqx : mq x ≠ 0 := by
      intro h0
      apply hδP.1.ne_zero
      rw [← hqT]
      have hzero : q = 0 := by
        rw [hmq, Finset.sum_eq_single x (fun z _ hz => by simp [hmq0 z hz])
          (fun hz => absurd (Finset.mem_univ x) hz)]
        simp [h0]
      rw [hzero]
      simp [T]
    have hx1 : mp x + mq x = 1 := by
      have h := congrFun hcoeff x
      have h' : ((mp x + mq x : ℕ) : ℤ) = 1 := by simpa using h
      exact_mod_cast h'
    omega
  choose f hf using hbeta
  have hfinj : Function.Injective f := by
    intro x y hxy
    have : w • α x = w • α y := by rw [hf x, hf y, hxy]
    have h2 : α x = α y := hwinj this
    exact lk0xlqlongest_alpha_injective α hind h2
  refine ⟨w, hwG, Equiv.ofBijective f ⟨hfinj, ?_⟩, fun x => hf x⟩
  exact Finite.surjective_of_injective hfinj

end CFSG.StandardType.GGK0LQ

end

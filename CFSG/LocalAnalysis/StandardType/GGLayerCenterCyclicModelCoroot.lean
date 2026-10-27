module

public import CFSG.LieType.HighestRoot.CentChevalleyCenter
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public section

namespace CFSG.StandardType

namespace LayerCycCoroot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}

section Defs


variable (K χ i) in
@[expose] noncomputable def componentCorootTorus : Subgroup (Module.End K (RootModule τ K))ˣ :=
  Subgroup.closure {x | ∃ (w : WeylGroup τ) (k : Fin τ.rank) (t : Kˣ),
    w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i ∧
      canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = x}

variable (K χ i) in
@[expose] noncomputable def componentCorootBorel : Subgroup (Module.End K (RootModule τ K))ˣ :=
  componentCorootTorus K χ i ⊔ componentUnipotent K χ i

variable (K χ i) in
@[expose] def corootCells : Set (Module.End K (RootModule τ K))ˣ :=
  {x | ∃ b ∈ componentCorootBorel K χ i, ∃ w ∈ componentWeylGroup (componentRoots χ i),
    ∃ b' ∈ componentCorootBorel K χ i, b * canonicalRep (coxeterSystem τ) K w * b' = x}

end Defs

section Mono


theorem canonicalRep_mem_monomialSubgroup (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ monomialSubgroup τ K :=
  Subgroup.mem_sup_right (canonicalRep_mem_closure _ K w)

theorem componentCorootTorus_le_componentCorootBorel :
    componentCorootTorus K χ i ≤ componentCorootBorel K χ i :=
  le_sup_left

theorem componentUnipotent_le_componentCorootBorel :
    componentUnipotent K χ i ≤ componentCorootBorel K χ i :=
  le_sup_right

end Mono

section Basic


theorem componentCorootTorus_le_componentTorus :
    componentCorootTorus K χ i ≤ componentTorus K χ i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, k, t, hw, rfl⟩
  exact canonicalRep_conj_torusElt_mem hw t

theorem componentCorootTorus_le_torusGroup :
    componentCorootTorus K χ i ≤ torusGroup τ K :=
  componentCorootTorus_le_componentTorus.trans (componentTorus_le_torusGroup K χ i)

theorem coe_componentCorootBorel :
    (componentCorootBorel K χ i : Set (Module.End K (RootModule τ K))ˣ) =
      (componentCorootTorus K χ i : Set (Module.End K (RootModule τ K))ˣ) *
        (componentUnipotent K χ i : Set (Module.End K (RootModule τ K))ˣ) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (componentCorootTorus_le_componentTorus.trans componentTorus_le_normalizer)

theorem componentCorootBorel_le_componentBorel :
    componentCorootBorel K χ i ≤ componentBorel K χ i :=
  sup_le (componentCorootTorus_le_componentTorus.trans componentTorus_le_componentBorel)
    componentUnipotent_le_componentBorel

theorem componentCorootBorel_le_borelGroup :
    componentCorootBorel K χ i ≤ borelGroup τ K :=
  componentCorootBorel_le_componentBorel.trans componentBorel_le_borelGroup

theorem exists_mul_canonicalRep_eq {w : WeylGroup τ} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : w⁻¹ • γ ∈ posRoots (componentRoots χ i)) {x : (Module.End K (RootModule τ K))ˣ}
    (hx : x ∈ rootSpan τ K {γ}) :
    ∃ u ∈ componentUnipotent K χ i, x * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K w * u := by
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem (canonicalRep_mem_monomialSubgroup w))
    (mapsRootLines_canonicalRep w).inv (S := {γ}) (by rintro _ rfl; exact hγ) hx
  rw [Set.image_singleton, inv_inv] at h
  exact ⟨_, rootSpan_mono (Set.singleton_subset_iff.2 hpos) h, by group⟩


end Basic

section CharTwo


variable [CharP K 2]

theorem canonicalRep_inv_charTwo (w : WeylGroup τ) :
    (canonicalRep (coxeterSystem τ) K w)⁻¹ = canonicalRep (coxeterSystem τ) K w⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    mul_inv_cancel, canonicalRep_one]

theorem componentWeylElt_eq_canonicalRep {v : (Fin τ.rank → ℤ) → WeylGroup τ}
    {j : (Fin τ.rank → ℤ) → Fin τ.rank} {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) :
    componentWeylElt K v j β = canonicalRep (coxeterSystem τ) K (rootReflection β) := by
  rw [componentWeylElt, canonicalRep_inv_charTwo, ← canonicalRep_simple (coxeterSystem τ) K (j β),
    ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, rootReflection_eq_conj hβv]

theorem canonicalRep_conj_mem_componentCorootTorus {u : WeylGroup τ}
    (hu : ∀ α ∈ componentRoots χ i, u • α ∈ componentRoots χ i)
    {x : (Module.End K (RootModule τ K))ˣ} (hx : x ∈ componentCorootTorus K χ i) :
    canonicalRep (coxeterSystem τ) K u * x * (canonicalRep (coxeterSystem τ) K u)⁻¹ ∈
      componentCorootTorus K χ i := by
  have h : componentCorootTorus K χ i ≤ (componentCorootTorus K χ i).comap
      (MulAut.conj (canonicalRep (coxeterSystem τ) K u)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, k, t, hw, rfl⟩
    refine Subgroup.subset_closure ⟨u * w, k, t, by rw [mul_smul]; exact hu _ hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo]
    group
  exact h hx

theorem exists_componentWeylElt_mul_eq_coroot {v : (Fin τ.rank → ℤ) → WeylGroup τ}
    {j : (Fin τ.rank → ℤ) → Fin τ.rank}
    (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots (componentRoots χ i))
    {b : (Module.End K (RootModule τ K))ˣ} (hb : b ∈ componentCorootBorel K χ i) :
    ∃ b'' ∈ componentCorootBorel K χ i, ∃ c : K, componentWeylElt K v j β * b =
      b'' * (componentWeylElt K v j β * componentXElt K v j β c) := by
  have hΨ := isRootComponent_componentRoots i
  have hβv := hvj β hβ
  rw [← SetLike.mem_coe, coe_componentCorootBorel] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  set S₁ := posRoots (componentRoots χ i) \ {β}
  have hsplit : posRoots (componentRoots χ i) = S₁ ∪ {β} :=
    (Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ))).symm
  have hu' : u ∈ rootSpan τ K (S₁ ∪ {β}) := by
    rw [← hsplit]
    exact hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := S₁) (S₂ := {β})
    (fun α hα => isRoot_height_pos_of_mem_posRoots hα.1)
    (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact isRoot_height_pos_of_mem_posRoots (simpleRoot_mem_posRoots hβ))
    Set.disjoint_sdiff_left
    (fun α hα γ hγ a a' ha ha' hr => by
      rw [← hsplit] at hα hγ ⊢
      exact mem_posRoots_of_nsmul_add hα hγ a a' ha ha' hr) hu'
  obtain ⟨c, rfl⟩ := exists_componentXElt_eq hβv hu₂
  set n := componentWeylElt K v j β
  have hn : n = canonicalRep (coxeterSystem τ) K (rootReflection β) :=
    componentWeylElt_eq_canonicalRep hβv
  have hnt : n * t * n⁻¹ ∈ componentCorootTorus K χ i := by
    rw [hn]
    exact canonicalRep_conj_mem_componentCorootTorus
      (smul_mem_of_mem_componentWeylGroup hΨ (rootReflection_mem_componentWeylGroup hβ)) ht
  have hnu : n * u₁ * n⁻¹ ∈ componentUnipotent K χ i := by
    have h := conj_mem_rootSpan_of_mapsRootLines (componentWeylElt_mem_monomialSubgroup K v j β)
      (mapsRootLines_componentWeylElt hβv) (S := S₁)
      (fun α hα => (isRoot_height_pos_of_mem_posRoots hα.1).1) hu₁
    refine rootSpan_mono ?_ h
    rintro _ ⟨α, ⟨hα, hne⟩, rfl⟩
    exact (rootReflection_mem_posRoots hΨ hβ hα hne).1
  refine ⟨n * t * n⁻¹ * (n * u₁ * n⁻¹), mul_mem (componentCorootTorus_le_componentCorootBorel hnt)
    (componentUnipotent_le_componentCorootBorel hnu), c, ?_⟩
  group

theorem canonicalRep_rootReflection_mul_mem_corootCells {v : (Fin τ.rank → ℤ) → WeylGroup τ}
    {j : (Fin τ.rank → ℤ) → Fin τ.rank}
    (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots (componentRoots χ i))
    {x : (Module.End K (RootModule τ K))ˣ} (hx : x ∈ corootCells K χ i) :
    canonicalRep (coxeterSystem τ) K (rootReflection β) * x ∈ corootCells K χ i := by
  obtain ⟨b, hb, w, hw, b', hb', rfl⟩ := hx
  have hΨ := isRootComponent_componentRoots i
  have hβv := hvj β hβ
  have hn := componentWeylElt_eq_canonicalRep (K := K) hβv
  obtain ⟨b'', hb'', c, hc⟩ := exists_componentWeylElt_mul_eq_coroot hvj hβ hb
  rw [hn] at hc
  have hrw : rootReflection β * w ∈ componentWeylGroup (componentRoots χ i) :=
    mul_mem (rootReflection_mem_componentWeylGroup hβ) hw
  have hmul : canonicalRep (coxeterSystem τ) K (rootReflection β * w) =
      canonicalRep (coxeterSystem τ) K (rootReflection β) * canonicalRep (coxeterSystem τ) K w :=
    CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo _ _
  have hmem := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) β (simpleRoots_subset hβ)
  rcases mem_posRoots_or_mem_negRoots hΨ hmem with hpos | hneg
  · obtain ⟨u', hu', hxu⟩ := exists_mul_canonicalRep_eq (simpleRoots_isRoot hβ) hpos
      (componentXElt_mem hβv c)
    refine ⟨b'', hb'', _, hrw, u' * b', mul_mem (componentUnipotent_le_componentCorootBorel hu')
      hb', ?_⟩
    rw [hmul]
    set n := canonicalRep (coxeterSystem τ) K (rootReflection β)
    set m := canonicalRep (coxeterSystem τ) K w
    calc b'' * (n * m) * (u' * b') = b'' * n * (m * u') * b' := by group
      _ = b'' * n * (componentXElt K v j β c * m) * b' := by rw [← hxu]
      _ = b'' * (n * componentXElt K v j β c) * m * b' := by group
      _ = n * b * m * b' := by rw [← hc]
      _ = n * (b * m * b') := by group
  · by_cases hc0 : c = 0
    · refine ⟨b'', hb'', _, hrw, b', hb', ?_⟩
      rw [hc0, componentXElt_zero, mul_one] at hc
      rw [hmul]
      set n := canonicalRep (coxeterSystem τ) K (rootReflection β)
      set m := canonicalRep (coxeterSystem τ) K w
      calc b'' * (n * m) * b' = b'' * n * m * b' := by group
        _ = n * b * m * b' := by rw [← hc]
        _ = n * (b * m * b') := by group
    · have h₀ := componentWeylElt_mul_componentXElt (K := K) (v := v) (j := j) β (Units.mk0 c hc0)
      rw [hn, Units.val_mk0] at h₀
      have hneg' : w⁻¹ • (-β) ∈ posRoots (componentRoots χ i) := by
        rw [smul_neg]
        exact hneg
      obtain ⟨u'', hu'', hyu⟩ := exists_mul_canonicalRep_eq (IsRoot.neg (simpleRoots_isRoot hβ))
        hneg' (componentYElt_mem hβv (((Units.mk0 c hc0)⁻¹ : Kˣ) : K))
      set n := canonicalRep (coxeterSystem τ) K (rootReflection β)
      set m := canonicalRep (coxeterSystem τ) K w
      set x₀ := componentXElt K v j β (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) with hx₀_def
      set t₀ := canonicalRep (coxeterSystem τ) K (v β) * torusElt τ K (j β) (-(Units.mk0 c hc0)⁻¹) *
        (canonicalRep (coxeterSystem τ) K (v β))⁻¹ with ht₀_def
      set y₀ := componentYElt K v j β (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) with hy₀_def
      have hx₀ : x₀ ∈ componentCorootBorel K χ i :=
        componentUnipotent_le_componentCorootBorel (rootSpan_mono
          (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) (componentXElt_mem hβv _))
      have ht₀ : t₀ ∈ componentCorootBorel K χ i :=
        componentCorootTorus_le_componentCorootBorel (Subgroup.subset_closure
          ⟨v β, j β, _, by rw [hβv]; exact simpleRoots_subset hβ, rfl⟩)
      refine ⟨b'' * (x₀ * t₀), mul_mem hb'' (mul_mem hx₀ ht₀), w, hw, u'' * b',
        mul_mem (componentUnipotent_le_componentCorootBorel hu'') hb', ?_⟩
      calc b'' * (x₀ * t₀) * m * (u'' * b') = b'' * (x₀ * t₀) * (m * u'') * b' := by group
        _ = b'' * (x₀ * t₀) * (y₀ * m) * b' := by rw [← hyu]
        _ = b'' * (x₀ * t₀ * y₀) * m * b' := by group
        _ = b'' * (n * componentXElt K v j β c) * m * b' := by rw [h₀]
        _ = n * b * m * b' := by rw [← hc]
        _ = n * (b * m * b') := by group

theorem componentTorus_le_componentCorootTorus :
    componentTorus K χ i ≤ componentCorootTorus K χ i := by
  classical
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  have hΨ := isRootComponent_componentRoots i
  set Y := corootCells K χ i with hY
  have hBY : ∀ b ∈ componentCorootBorel K χ i, ∀ x ∈ Y, b * x ∈ Y := by
    rintro b hb _ ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩
    exact ⟨b * b₁, mul_mem hb hb₁, w, hw, b₂, hb₂, by group⟩
  let St : Subgroup (Module.End K (RootModule τ K))ˣ :=
    { carrier := {g | (∀ x ∈ Y, g * x ∈ Y) ∧ ∀ x ∈ Y, g⁻¹ * x ∈ Y}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBSt : componentCorootBorel K χ i ≤ St := fun b hb =>
    ⟨fun x hx => hBY b hb x hx, fun x hx => hBY b⁻¹ (inv_mem hb) x hx⟩
  have hnSt : ∀ β ∈ simpleRoots (componentRoots χ i),
      canonicalRep (coxeterSystem τ) K (rootReflection β) ∈ St := by
    intro β hβ
    have hinv : (canonicalRep (coxeterSystem τ) K (rootReflection β))⁻¹ =
        canonicalRep (coxeterSystem τ) K (rootReflection β) := by
      rw [canonicalRep_inv_charTwo, rootReflection_inv (simpleRoots_isRoot hβ)]
    refine ⟨fun x hx => canonicalRep_rootReflection_mul_mem_corootCells hvj hβ hx,
      fun x hx => ?_⟩
    rw [hinv]
    exact canonicalRep_rootReflection_mul_mem_corootCells hvj hβ hx
  let φ : WeylGroup τ →* (Module.End K (RootModule τ K))ˣ :=
    MonoidHom.mk' (canonicalRep (coxeterSystem τ) K)
      CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
  have hWSt : componentWeylGroup (componentRoots χ i) ≤ St.comap φ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    exact hnSt β hβ
  have hSSt : componentRootSpan K χ i ≤ St := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨u, hu, β, hβ, e⟩ := exists_smul_simpleRoot hΨ hα
    intro x hx
    have hx' : x ∈ rootSpan τ K {α} := by
      rw [rootSpan, iSup_singleton]
      exact hx
    have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem (canonicalRep_mem_monomialSubgroup u))
      (mapsRootLines_canonicalRep u).inv (S := {α}) (by rintro _ rfl; exact hΨ.isRoot _ hα) hx'
    rw [Set.image_singleton, inv_inv, e, inv_smul_smul] at h
    have hb : (canonicalRep (coxeterSystem τ) K u)⁻¹ * x * canonicalRep (coxeterSystem τ) K u ∈
        St := hBSt (componentUnipotent_le_componentCorootBorel
          (rootSpan_mono (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) h))
    have hu' : canonicalRep (coxeterSystem τ) K u ∈ St := hWSt hu
    have e' : x = canonicalRep (coxeterSystem τ) K u *
        ((canonicalRep (coxeterSystem τ) K u)⁻¹ * x * canonicalRep (coxeterSystem τ) K u) *
          (canonicalRep (coxeterSystem τ) K u)⁻¹ := by group
    rw [e']
    exact mul_mem (mul_mem hu' hb) (inv_mem hu')
  intro t ht
  have h1 : (1 : (Module.End K (RootModule τ K))ˣ) ∈ Y :=
    ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by rw [canonicalRep_one]; group⟩
  have htY : t ∈ Y := by simpa using (hSSt (Subgroup.mem_inf.1 ht).1).1 1 h1
  have htH : t ∈ torusGroup τ K := (Subgroup.mem_inf.1 ht).2
  obtain ⟨b, hb, w, hw, b', hb', hbt⟩ := htY
  have hw1 : w = 1 := by
    by_contra hne
    have h1cell : t ∈ bruhatCell τ K 1 := mem_bruhatCell.2
      ⟨t, torusGroup_le_borelGroup htH, 1, one_mem _, by rw [canonicalRep_one]; group⟩
    have hwcell : t ∈ bruhatCell τ K w := mem_bruhatCell.2
      ⟨b, componentCorootBorel_le_borelGroup hb, b', componentCorootBorel_le_borelGroup hb', hbt⟩
    exact Set.disjoint_left.1 (disjoint_bruhatCell hne) hwcell h1cell
  subst hw1
  rw [canonicalRep_one, mul_one] at hbt
  have hbb : b * b' ∈ (componentCorootBorel K χ i : Set (Module.End K (RootModule τ K))ˣ) :=
    mul_mem hb hb'
  rw [coe_componentCorootBorel] at hbb
  obtain ⟨t₁, ht₁, u₁, hu₁, he⟩ := hbb
  have hu1 : u₁ = 1 := by
    have hut : u₁ = t₁⁻¹ * t := by rw [← hbt, ← he]; group
    have hmem : u₁ ∈ torusGroup τ K ⊓ posUnipotent τ K := Subgroup.mem_inf.2
      ⟨by rw [hut]; exact mul_mem (inv_mem (componentCorootTorus_le_torusGroup ht₁)) htH,
        componentUnipotent_le_posUnipotent hu₁⟩
    rwa [(triangular_borel_structure.{0, 0} τ K).2.2.2.1, Subgroup.mem_bot] at hmem
  have he' : t₁ * u₁ = t := he.trans hbt
  rw [← he', hu1, mul_one]
  exact ht₁

theorem coe_mem_componentCorootTorus_of_mem_center {z : componentRootSpan K χ i}
    (hz : z ∈ Subgroup.center (componentRootSpan K χ i)) :
    (z : (Module.End K (RootModule τ K))ˣ) ∈ componentCorootTorus K χ i :=
  componentTorus_le_componentCorootTorus
    (CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center hz)

end CharTwo

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (s : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ x ∈ s, a ^ f x = a ^ ∑ x ∈ s, f x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro x s hx ih
  rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]

theorem eq_one_of_mul_self_eq_one [CharP K 2] {u : Kˣ} (hu : u * u = 1) : u = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (u : K) * u = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  have h3 : ((u : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (u : K)) * h2
  exact Units.ext (by simpa [sub_eq_zero] using h3)

section Norm


open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

noncomputable def torusTuple (x : torusGroup τ K) : Fin τ.rank → Kˣ :=
  (exists_rootDiagUnit_eq_of_mem_torusGroup x.2).choose

theorem rootDiagUnit_torusTuple (x : torusGroup τ K) :
    rootDiagUnit τ (torusTuple x) = (x : (Module.End K (RootModule τ K))ˣ) :=
  (exists_rootDiagUnit_eq_of_mem_torusGroup x.2).choose_spec.symm

noncomputable def torusTupleHom : torusGroup τ K →* (Fin τ.rank → Kˣ) where
  toFun := torusTuple
  map_one' := rootDiagUnit_injective (by rw [rootDiagUnit_torusTuple, rootDiagUnit_one]; rfl)
  map_mul' x y := rootDiagUnit_injective (by
    rw [rootDiagUnit_torusTuple, rootDiagUnit_mul, rootDiagUnit_torusTuple,
      rootDiagUnit_torusTuple]
    rfl)

theorem torusTuple_apply_eq {x : torusGroup τ K} {j : Fin τ.rank} {s : Kˣ}
    (h : (x : (Module.End K (RootModule τ K))ˣ) * pinnedX τ K (Pi.single j 1) 1 *
      (x : (Module.End K (RootModule τ K))ˣ)⁻¹ = pinnedX τ K (Pi.single j 1) (s : K)) :
    torusTuple x j = s := by
  rw [← rootDiagUnit_torusTuple x, rootDiagUnit_conj_pinnedX _ (isRoot_single τ j)] at h
  have h1 := pinnedX_injective τ K _ h
  have h2 : rootChar (torusTuple x) (Pi.single j 1) = torusTuple x j := by
    have := rootChar_nsmul_single (torusTuple x) j 1
    rwa [one_nsmul, pow_one] at this
  rw [h2, mul_one] at h1
  exact Units.ext h1

theorem torusTuple_corootElt (w : WeylGroup τ) (k : Fin τ.rank) (t : Kˣ)
    (hx : canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ torusGroup τ K) (j : Fin τ.rank) :
    torusTuple ⟨_, hx⟩ j =
      t ^ corootPair (w • (Pi.single k 1 : Fin τ.rank → ℤ)) (Pi.single j 1) := by
  apply torusTuple_apply_eq
  rw [corootPair_smul_single]
  exact (canonicalRep_conj_torusElt_conj_pinnedX w k t (isRoot_single τ j) 1).trans
    (by rw [mul_one])

theorem corootPair_neg_root {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (v : Fin τ.rank → ℤ) :
    corootPair (-δ) v = -corootPair δ v := by
  have h1 := corootPair_mul hδ v
  have h2 := corootPair_mul (IsRoot.neg hδ) v
  have hn : iform (-δ) v = -iform δ v := by
    simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hnn : iform (-δ) (-δ) = iform δ δ := by
    simp only [iform, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  apply mul_right_cancel₀ (iform_self_pos_of_isRoot hδ).ne'
  rw [neg_mul, h1, ← hnn, h2, hn]
  ring

theorem sum_corootPair_eq_zero [Fintype (componentWeylGroup (componentRoots χ i))]
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) (v : Fin τ.rank → ℤ) :
    ∑ u : componentWeylGroup (componentRoots χ i), corootPair ((u : WeylGroup τ) • γ) v = 0 := by
  have hΨ := isRootComponent_componentRoots i
  obtain ⟨u₀, hu₀, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
  have hγr : IsRoot τ (u₀ • β) := IsRoot.smul (simpleRoots_isRoot hβ) u₀
  have hr : rootReflection (u₀ • β) ∈ componentWeylGroup (componentRoots χ i) := by
    rw [rootReflection_smul_root u₀ (simpleRoots_isRoot hβ)]
    exact mul_mem (mul_mem hu₀ (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hu₀)
  set g : componentWeylGroup (componentRoots χ i) := ⟨rootReflection (u₀ • β), hr⟩
  have key : ∀ u : componentWeylGroup (componentRoots χ i),
      corootPair (((u * g : componentWeylGroup (componentRoots χ i)) : WeylGroup τ) • (u₀ • β)) v =
        -corootPair ((u : WeylGroup τ) • (u₀ • β)) v := by
    intro u
    rw [Subgroup.coe_mul, mul_smul, rootReflection_smul_self hγr, smul_neg,
      corootPair_neg_root (IsRoot.smul hγr _)]
  have h := Fintype.sum_equiv (Equiv.mulRight g)
    (fun u => corootPair (((u * g : componentWeylGroup (componentRoots χ i)) : WeylGroup τ) •
      (u₀ • β)) v)
    (fun u => corootPair ((u : WeylGroup τ) • (u₀ • β)) v) (fun u => rfl)
  simp only [key, Finset.sum_neg_distrib] at h
  linarith

theorem pow_card_eq_one_of_mem_center [CharP K 2] {z : componentRootSpan K χ i}
    (hz : z ∈ Subgroup.center (componentRootSpan K χ i)) :
    (z : (Module.End K (RootModule τ K))ˣ) ^
      Nat.card (componentWeylGroup (componentRoots χ i)) = 1 := by
  classical
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  have : Fintype (componentWeylGroup (componentRoots χ i)) := Fintype.ofFinite _
  let φ : WeylGroup τ →* (Module.End K (RootModule τ K))ˣ :=
    MonoidHom.mk' (canonicalRep (coxeterSystem τ) K)
      CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
  have hWS : componentWeylGroup (componentRoots χ i) ≤ (componentRootSpan K χ i).comap φ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    show canonicalRep (coxeterSystem τ) K (rootReflection β) ∈ componentRootSpan K χ i
    rw [← componentWeylElt_eq_canonicalRep (hvj β hβ)]
    exact componentWeylElt_mem_componentRootSpan (hvj β hβ) (simpleRoots_subset hβ)
  let c : WeylGroup τ → torusGroup τ K →* torusGroup τ K := fun u =>
    ((MulAut.conj (canonicalRep (coxeterSystem τ) K u)).toMonoidHom.comp
      (torusGroup τ K).subtype).codRestrict (torusGroup τ K) (fun x =>
        (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) u) _).1 x.2)
  let F : torusGroup τ K →* (Fin τ.rank → Kˣ) :=
    ∏ u : componentWeylGroup (componentRoots χ i), torusTupleHom.comp (c u)
  have hgen : componentCorootTorus K χ i ≤ F.ker.map (torusGroup τ K).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, k, t, hw, rfl⟩
    have hx : canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ torusGroup τ K :=
      componentTorus_le_torusGroup K χ i (canonicalRep_conj_torusElt_mem hw t)
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    have hfac : ∀ (u : componentWeylGroup (componentRoots χ i)) (l : Fin τ.rank),
        (torusTupleHom.comp (c u)) ⟨_, hx⟩ l =
          t ^ corootPair ((u : WeylGroup τ) • (w • (Pi.single k 1 : Fin τ.rank → ℤ)))
            (Pi.single l 1) := by
      intro u l
      have hmem : canonicalRep (coxeterSystem τ) K (u * w) * torusElt τ K k t *
          (canonicalRep (coxeterSystem τ) K (u * w))⁻¹ ∈ torusGroup τ K :=
        (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) _) _).1
          (torusElt_mem_torusGroup k t)
      have he : (c u) ⟨_, hx⟩ = ⟨_, hmem⟩ := by
        apply Subtype.ext
        change canonicalRep (coxeterSystem τ) K u * (canonicalRep (coxeterSystem τ) K w *
          torusElt τ K k t * (canonicalRep (coxeterSystem τ) K w)⁻¹) *
            (canonicalRep (coxeterSystem τ) K u)⁻¹ =
          canonicalRep (coxeterSystem τ) K (u * w) * torusElt τ K k t *
            (canonicalRep (coxeterSystem τ) K (u * w))⁻¹
        rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo]
        group
      rw [MonoidHom.comp_apply, he]
      exact (torusTuple_corootElt _ k t hmem l).trans (by rw [mul_smul])
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.finsetProd_apply]
    funext l
    rw [Finset.prod_apply, Pi.one_apply]
    simp only [hfac]
    rw [prod_zpow_eq_zpow_sum, sum_corootPair_eq_zero hw, zpow_zero]
  obtain ⟨z', hzF, hzz⟩ := hgen (coe_mem_componentCorootTorus_of_mem_center hz)
  have hzc : ((z' : torusGroup τ K) : (Module.End K (RootModule τ K))ˣ) = z := hzz
  have hfix : ∀ u : componentWeylGroup (componentRoots χ i), c u z' = z' := by
    intro u
    apply Subtype.ext
    change canonicalRep (coxeterSystem τ) K u * (z' : (Module.End K (RootModule τ K))ˣ) *
      (canonicalRep (coxeterSystem τ) K u)⁻¹ = z'
    have hnS : canonicalRep (coxeterSystem τ) K u ∈ componentRootSpan K χ i := hWS u.2
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hnS⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hzc, hc]
    group
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.finsetProd_apply] at hzF
  simp only [MonoidHom.comp_apply, hfix, Finset.prod_const, Finset.card_univ] at hzF
  rw [← map_pow] at hzF
  have hpow : z' ^ Fintype.card (componentWeylGroup (componentRoots χ i)) = 1 := by
    apply Subtype.ext
    rw [← rootDiagUnit_torusTuple (z' ^ _)]
    change rootDiagUnit τ (torusTupleHom _) = 1
    rw [hzF, rootDiagUnit_one]
  rw [← hzc, Nat.card_eq_fintype_card, ← Subgroup.coe_pow, hpow]
  rfl

theorem center_eq_bot_of_neg_mem [CharP K 2] {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i))
    (hneg : ∀ γ ∈ componentRoots χ i, w • γ = -γ) :
    Subgroup.center (componentRootSpan K χ i) = ⊥ := by
  classical
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  let φ : WeylGroup τ →* (Module.End K (RootModule τ K))ˣ :=
    MonoidHom.mk' (canonicalRep (coxeterSystem τ) K)
      CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
  have hWS : componentWeylGroup (componentRoots χ i) ≤ (componentRootSpan K χ i).comap φ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    show canonicalRep (coxeterSystem τ) K (rootReflection β) ∈ componentRootSpan K χ i
    rw [← componentWeylElt_eq_canonicalRep (hvj β hβ)]
    exact componentWeylElt_mem_componentRootSpan (hvj β hβ) (simpleRoots_subset hβ)
  let c : torusGroup τ K →* torusGroup τ K :=
    ((MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom.comp
      (torusGroup τ K).subtype).codRestrict (torusGroup τ K) (fun x =>
        (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) _).1 x.2)
  let F : torusGroup τ K →* (Fin τ.rank → Kˣ) := torusTupleHom * torusTupleHom.comp c
  have hgen : componentCorootTorus K χ i ≤ F.ker.map (torusGroup τ K).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, k, t, hu, rfl⟩
    have hx : canonicalRep (coxeterSystem τ) K u * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K u)⁻¹ ∈ torusGroup τ K :=
      componentTorus_le_torusGroup K χ i (canonicalRep_conj_torusElt_mem hu t)
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    have hmem : canonicalRep (coxeterSystem τ) K (w * u) * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K (w * u))⁻¹ ∈ torusGroup τ K :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) _) _).1
        (torusElt_mem_torusGroup k t)
    have he : c ⟨_, hx⟩ = ⟨_, hmem⟩ := by
      apply Subtype.ext
      change canonicalRep (coxeterSystem τ) K w * (canonicalRep (coxeterSystem τ) K u *
        torusElt τ K k t * (canonicalRep (coxeterSystem τ) K u)⁻¹) *
          (canonicalRep (coxeterSystem τ) K w)⁻¹ =
        canonicalRep (coxeterSystem τ) K (w * u) * torusElt τ K k t *
          (canonicalRep (coxeterSystem τ) K (w * u))⁻¹
      rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo]
      group
    have hγ : IsRoot τ (u • (Pi.single k 1 : Fin τ.rank → ℤ)) :=
      IsRoot.smul (isRoot_single τ k) u
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    funext l
    change torusTuple ⟨_, hx⟩ l * torusTupleHom (c ⟨_, hx⟩) l = 1
    rw [he]
    change torusTuple ⟨_, hx⟩ l * torusTuple ⟨_, hmem⟩ l = 1
    rw [torusTuple_corootElt u k t hx l, torusTuple_corootElt (w * u) k t hmem l, mul_smul,
      hneg _ hu, corootPair_neg_root hγ, zpow_neg, mul_inv_cancel]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨z', hzF, hzz⟩ := hgen (coe_mem_componentCorootTorus_of_mem_center hz)
  have hzc : ((z' : torusGroup τ K) : (Module.End K (RootModule τ K))ˣ) = z := hzz
  have hfix : c z' = z' := by
    apply Subtype.ext
    change canonicalRep (coxeterSystem τ) K w * (z' : (Module.End K (RootModule τ K))ˣ) *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ = z'
    have hnS : canonicalRep (coxeterSystem τ) K w ∈ componentRootSpan K χ i := hWS hw
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hnS⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hzc, hc]
    group
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hzF
  have ha : torusTuple z' = 1 := by
    funext l
    have hl := congrFun hzF l
    change torusTuple z' l * torusTupleHom (c z') l = 1 at hl
    rw [hfix] at hl
    exact eq_one_of_mul_self_eq_one hl
  apply Subtype.ext
  rw [← hzc, ← rootDiagUnit_torusTuple z', ha, rootDiagUnit_one]
  rfl

end Norm

end LayerCycCoroot

end CFSG.StandardType

end

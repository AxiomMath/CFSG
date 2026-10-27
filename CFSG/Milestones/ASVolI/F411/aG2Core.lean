module

public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity
public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section ChevCore


variable {K : Type} [Field K]

theorem burnsideF411a_chev_no_swap (τ : Tag) {i j : Fin τ.rank} (hij : i ≠ j)
    {c : ModGL τ K} (hc : c ∈ borelGroup τ K) {s : K}
    (h : c * xUnit τ K j s * c⁻¹ = xUnit τ K i 1) : False := by
  have hB : c ∈ (borelGroup τ K : Set (ModGL τ K)) := hc
  rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1] at hB
  obtain ⟨u, hu, t, ht, hut⟩ := hB
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set x := pinnedX τ K (Pi.single j 1) ((rootChar b (Pi.single j 1) : K) * s) with hx
  have hconj : u * x * u⁻¹ = pinnedX τ K (Pi.single i 1) 1 := by
    rw [hx, ← rootDiagUnit_conj_pinnedX b (IsRoot.basis j) s, pinnedX_single, pinnedX_single, ← h,
      ← hut]
    group
  set T : Set (Fin τ.rank → ℤ) :=
    {β | IsRoot τ β ∧ 0 < height β ∧ (β = Pi.single j 1 ∨ 2 ≤ height β)} with hT
  have hxT : x ∈ rootSpan τ K T :=
    pinnedX_mem_rootSpan (S := T) (α := Pi.single j 1) ⟨IsRoot.basis j, by simp, Or.inl rfl⟩ _
  have hx1 : x ∈ heightSeries τ K 1 :=
    pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α ∧ 1 ≤ height α})
      (α := Pi.single j 1) ⟨IsRoot.basis j, by simp, by simp⟩ _
  have hu1 : u ∈ heightSeries τ K 1 := by
    rw [heightSeries_one]
    exact hu
  have hcomm := commutator_heightSeries_le K 1 1 (Subgroup.commutator_mem_commutator hu1 hx1)
  have hle : heightSeries τ K (1 + 1) ≤ rootSpan τ K T :=
    biSup_mono fun β hβ => ⟨hβ.1, hβ.2.1, Or.inr (by have := hβ.2.2; omega)⟩
  have heq : pinnedX τ K (Pi.single i 1) 1 = ⁅u, x⁆ * x := by
    rw [← hconj, commutatorElement_def]
    group
  have hmem : pinnedX τ K (Pi.single i 1) 1 ∈ rootSpan τ K T := by
    rw [heq]
    exact mul_mem (hle hcomm) hxT
  have hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T := by
    intro β hβ γ hγ a b ha hb hr
    obtain ⟨hr', hp, hle'⟩ := nsmul_add_nsmul_mem_heightSet (h := 1) (k := 1)
      ⟨hβ.2.1, by have := hβ.2.1; omega⟩ ⟨hγ.2.1, by have := hγ.2.1; omega⟩ ha hb hr
    exact ⟨hr', hp, Or.inr (by omega)⟩
  have hiT := mem_of_pinnedX_mem_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) hTc
    ⟨IsRoot.basis i, by simp⟩ one_ne_zero hmem
  rcases hiT.2.2 with h1 | h2
  · apply hij
    have := congrFun h1 i
    simpa [Pi.single_apply, eq_comm] using this
  · simp at h2

theorem burnsideF411a_chev_mem_borel (τ : Tag) {c : adjointGroup τ K}
    {β : MulAut (adjointGroup τ K)}
    (hU : ((posUnipotent τ K).subgroupOf (adjointGroup τ K)).map β.toMonoidHom =
      (posUnipotent τ K).subgroupOf (adjointGroup τ K))
    (hα : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ posUnipotent τ K →
      (MulAut.conj c * β) x = x) :
    (c : ModGL τ K) ∈ borelGroup τ K := by
  set U := (posUnipotent τ K).subgroupOf (adjointGroup τ K) with hUdef
  have hαU : U.map (MulAut.conj c * β).toMonoidHom = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hα x (Subgroup.mem_subgroupOf.1 hx)]
      exact hx
    · intro hy
      exact ⟨y, hy, hα y (Subgroup.mem_subgroupOf.1 hy)⟩
  have hcU : U.map (MulAut.conj c).toMonoidHom = U := by
    calc U.map (MulAut.conj c).toMonoidHom =
        (U.map β.toMonoidHom).map (MulAut.conj c).toMonoidHom := by rw [hU]
      _ = U.map (MulAut.conj c * β).toMonoidHom := by rw [Subgroup.map_map]; rfl
      _ = U := hαU
  have hfwd : ∀ y : adjointGroup τ K, y ∈ U → c * y * c⁻¹ ∈ U := fun y hy => by
    have := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hy
    rwa [hcU] at this
  have hbwd : ∀ y : adjointGroup τ K, c * y * c⁻¹ ∈ U → y ∈ U := fun y hy => by
    rw [← hcU] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    have : y' = y := (MulAut.conj c).injective hyy'
    rwa [← this]
  rw [← (borel_self_normalizers τ K).1]
  refine Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have hyC : y ∈ adjointGroup τ K := posUnipotent_le_adjointGroup hy
    have := hfwd ⟨y, hyC⟩ (Subgroup.mem_subgroupOf.2 hy)
    exact Subgroup.mem_subgroupOf.1 this
  · have hyC' : (c : ModGL τ K) * y * (c : ModGL τ K)⁻¹ ∈ adjointGroup τ K :=
      posUnipotent_le_adjointGroup hy
    have hyC : y ∈ adjointGroup τ K := by
      have e : y = (c : ModGL τ K)⁻¹ * ((c : ModGL τ K) * y * (c : ModGL τ K)⁻¹) *
          (c : ModGL τ K) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem c.2) hyC') c.2
    have := hbwd ⟨y, hyC⟩ (Subgroup.mem_subgroupOf.2 hy)
    exact Subgroup.mem_subgroupOf.1 this

theorem burnsideF411a_chev_inner_of_fix [Finite K] (τ : Tag) (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : MulAut (adjointGroup τ K))
    (hα : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ posUnipotent τ K → α x = x) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀).2.2.2.2.2 α
  obtain ⟨π, hπ⟩ := exists_perm_map_simple (show β ∈ unipotentPairAut τ K from ⟨hU, hV⟩)
  by_cases hπ1 : π = 1
  · subst hπ1
    have hβ : β ∈ rootPairAut τ K := mem_rootPairAut.2 fun i => ⟨(hπ i).1, (hπ i).2⟩
    obtain ⟨q, hq, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter τ K).1 β hβ
    have hβN : β = exactNormalAut τ K q.1 q.2 0 :=
      mulAut_ext_adjX_adjY (fun i c => by rw [(hq i).1, exactNormalAut_zero_adjX])
        fun i c => by rw [(hq i).2.1, exactNormalAut_zero_adjY]
    subst hβN
    have hJ : (∅ : Set (Fin τ.rank)) ≠ Set.univ := by
      have : Nonempty (Fin τ.rank) := ⟨⟨0, by cases τ <;> decide⟩⟩
      exact Set.empty_ne_univ
    have hform : ∀ x : adjointGroup τ K,
        ((MulAut.conj c * exactNormalAut τ K q.1 q.2 0) x : ModGL τ K) =
          (c : ModGL τ K) * rootDiagUnit τ q.1 * Units.map (entrywiseHom q.2.toRingHom) x *
            (rootDiagUnit τ q.1)⁻¹ * (c : ModGL τ K)⁻¹ := by
      intro x
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_exactNormalAut_zero, Subgroup.coe_inv]
      simp only [mul_assoc]
    obtain ⟨-, z, -, hz, hαz⟩ :=
      (Chevalley_parabolic_radical_diagonal_field_pointwise_rigidity τ K hJ).1 (c : ModGL τ K) c.2
        q.1 q.2 _ hform fun x hx => hα x (parabolicRadical_le_posUnipotent ∅ hx)
    exact ⟨⟨z, hz⟩, hαz⟩
  · exfalso
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
      by_contra hcon
      exact hπ1 (Equiv.ext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
    have hcB := burnsideF411a_chev_mem_borel τ hU hα
    have hx1 : adjX τ K i 1 ∈ simplePosSubgroup τ K i := ⟨1, rfl⟩
    have hβx : β (adjX τ K i 1) ∈ simplePosSubgroup τ K (π i) := by
      rw [← (hπ i).1]
      exact Subgroup.mem_map_of_mem _ hx1
    obtain ⟨s, hs⟩ := hβx
    have hfix := hα (adjX τ K i 1) (by
      show xUnit τ K i 1 ∈ posUnipotent τ K
      rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) (α := Pi.single i 1)
        ⟨IsRoot.basis i, by simp⟩ 1)
    have h2 := congrArg Subtype.val hfix
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hs,
      Subgroup.coe_inv] at h2
    exact burnsideF411a_chev_no_swap τ (Ne.symm hi) hcB h2

theorem burnsideF411a_chev_inner_of_fix_sylow (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (α : MulAut (adjointGroup τ K)) (S : Sylow p (adjointGroup τ K))
    (hα : ∀ s ∈ (S : Subgroup (adjointGroup τ K)), α s = s) : ∃ g, α = MulAut.conj g := by
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (adjointGroup τ K) P₀ S
  have hβ : ∀ u : adjointGroup τ K, (u : ModGL τ K) ∈ posUnipotent τ K →
      ((MulAut.conj x)⁻¹ * α * MulAut.conj x) u = u := by
    intro u hu
    have hu' : u ∈ (P₀ : Subgroup (adjointGroup τ K)) := by
      rw [hP₀]
      exact Subgroup.mem_subgroupOf.2 hu
    have hxu : x * u * x⁻¹ ∈ (S : Subgroup (adjointGroup τ K)) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj x) (P₀ : Subgroup _) hu'
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxu, MulAut.conj_inv_apply]
    group
  obtain ⟨g, hg⟩ := burnsideF411a_chev_inner_of_fix τ p _ hβ
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

end ChevCore

end CFSG.ASVolI

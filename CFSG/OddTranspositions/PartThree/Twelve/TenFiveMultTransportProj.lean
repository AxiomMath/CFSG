module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultTransport

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

noncomputable def omegaIncl {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ↥(fiveOmega k ε) →* ↥(fiveReflectionGroup k ε π) :=
  Subgroup.inclusion (fiveOmega_le_fiveReflectionGroup hk ε π (fiveSameClass hk ε π))

@[simp] theorem coe_omegaIncl {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) (ω : ↥(fiveOmega k ε)) :
    ((omegaIncl hk ε π ω : ↥(fiveReflectionGroup k ε π)) : GL (Fin (k + 1)) (ZMod 5)) =
      (ω : GL (Fin (k + 1)) (ZMod 5)) :=
  Subgroup.coe_inclusion _ ω

theorem commutator_fiveProjective_eq_map {k : ℕ} (ε π : Bool) :
    commutator (fiveProjective k ε π) =
      (commutator ↥(fiveReflectionGroup k ε π)).map
        (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) := by
  rw [commutator_def]
  conv_rhs => rw [commutator_def]
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem omegaIncl_mem_commutator {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) (ω : ↥(fiveOmega k ε)) :
    omegaIncl hk ε π ω ∈ commutator ↥(fiveReflectionGroup k ε π) := by
  have hmap : (commutator ↥(fiveReflectionGroup k ε π)).map
      (Subgroup.subtype (fiveReflectionGroup k ε π)) = fiveOmega k ε := by
    rw [Subgroup.map_subtype_commutator, commutator_fiveReflectionGroup_eq_fiveOmega hk ε π]
  have hmem' : ((omegaIncl hk ε π ω : ↥(fiveReflectionGroup k ε π)) :
      GL (Fin (k + 1)) (ZMod 5)) ∈ (commutator ↥(fiveReflectionGroup k ε π)).map
        (Subgroup.subtype (fiveReflectionGroup k ε π)) := by
    rw [hmap, coe_omegaIncl]
    exact ω.property
  obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hmem'
  have : y = omegaIncl hk ε π ω := Subtype.ext hyval
  rwa [this] at hy

theorem exists_eq_mul_center_of_mem_commutator {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (g : fiveReflectionGroup k ε π)
    (hg : (QuotientGroup.mk g : fiveProjective k ε π) ∈ commutator (fiveProjective k ε π)) :
    ∃ (ω : ↥(fiveOmega k ε)) (z : fiveReflectionGroup k ε π),
      z ∈ Subgroup.center (fiveReflectionGroup k ε π) ∧ g = omegaIncl hk ε π ω * z := by
  rw [commutator_fiveProjective_eq_map ε π] at hg
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
  have hz : y⁻¹ * g ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) (y⁻¹ * g) = 1
    rw [map_mul, map_inv, show (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) y =
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) g from hyg]
    exact inv_mul_cancel _
  have hmap : (commutator ↥(fiveReflectionGroup k ε π)).map
      (Subgroup.subtype (fiveReflectionGroup k ε π)) = fiveOmega k ε := by
    rw [Subgroup.map_subtype_commutator, commutator_fiveReflectionGroup_eq_fiveOmega hk ε π]
  have hyΩ : (y : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveOmega k ε := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hy_eq : y = omegaIncl hk ε π ⟨y.val, hyΩ⟩ := Subtype.ext rfl
  refine ⟨⟨y.val, hyΩ⟩, y⁻¹ * g, hz, ?_⟩
  calc g = y * (y⁻¹ * g) := by group
    _ = omegaIncl hk ε π ⟨y.val, hyΩ⟩ * (y⁻¹ * g) :=
        congrArg (· * (y⁻¹ * g)) (Subtype.ext rfl)

theorem qProj_mem {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) (ω : ↥(fiveOmega k ε)) :
    (QuotientGroup.mk (omegaIncl hk ε π ω) : fiveProjective k ε π) ∈
      commutator (fiveProjective k ε π) := by
  rw [commutator_fiveProjective_eq_map ε π]
  exact Subgroup.mem_map.mpr ⟨omegaIncl hk ε π ω, omegaIncl_mem_commutator hk ε π ω, rfl⟩

noncomputable def qProj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ↥(fiveOmega k ε) →* ↥(commutator (fiveProjective k ε π)) :=
  ((QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))).comp
    (omegaIncl hk ε π)).codRestrict
    (commutator (fiveProjective k ε π)) (qProj_mem hk ε π)

@[simp] theorem coe_qProj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) (ω : ↥(fiveOmega k ε)) :
    ((qProj hk ε π ω : ↥(commutator (fiveProjective k ε π))) : fiveProjective k ε π) =
      QuotientGroup.mk (omegaIncl hk ε π ω) := by
  rw [qProj]
  rfl

theorem qProj_surjective {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) : Function.Surjective (qProj hk ε π) := by
  intro y
  have hy : (y : fiveProjective k ε π) ∈ (commutator ↥(fiveReflectionGroup k ε π)).map
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) := by
    rw [← commutator_fiveProjective_eq_map ε π]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  have hmap : (commutator ↥(fiveReflectionGroup k ε π)).map
      (Subgroup.subtype (fiveReflectionGroup k ε π)) = fiveOmega k ε := by
    rw [Subgroup.map_subtype_commutator, commutator_fiveReflectionGroup_eq_fiveOmega hk ε π]
  have hxΩ : (x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveOmega k ε := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  refine ⟨⟨x.val, hxΩ⟩, ?_⟩
  apply Subtype.ext
  rw [coe_qProj, show omegaIncl hk ε π ⟨x.val, hxΩ⟩ = x from Subtype.ext rfl]
  exact hxy

theorem qProj_ker {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    (qProj hk ε π).ker =
      (Subgroup.center (GL (Fin (k + 1)) (ZMod 5))).comap
        (Subgroup.subtype (fiveOmega k ε)) := by
  ext ω
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  constructor
  · intro h
    have h' : (QuotientGroup.mk (omegaIncl hk ε π ω) : fiveProjective k ε π) = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    have hZ : omegaIncl hk ε π ω ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      exact h'
    exact (mem_center_fiveOmega_iff hk ε π ω).mpr hZ
  · intro h
    have hZ : omegaIncl hk ε π ω ∈ Subgroup.center (fiveReflectionGroup k ε π) :=
      (mem_center_fiveOmega_iff hk ε π ω).mp h
    apply Subtype.ext
    rw [Subgroup.coe_one, coe_qProj]
    exact (QuotientGroup.eq_one_iff (omegaIncl hk ε π ω)).mpr hZ

theorem qProj_ker_map_theta {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5} (Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀))
    (hΘ_scalar : ∀ g : ↥(fiveOmega k ε),
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ Subgroup.center (GL (Fin (k + 1)) (ZMod 5)) ↔
        (Θ g : GL ι (ZMod 5)) ∈ StatedScalars ι (ZMod 5)) :
    ((Subgroup.center (GL (Fin (k + 1)) (ZMod 5))).comap
        (Subgroup.subtype (fiveOmega k ε))).map Θ =
      (StatedScalars ι (ZMod 5)).subgroupOf (StatedOmega Q₀) := by
  ext g
  constructor
  · intro hg
    obtain ⟨ω, hω, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_subgroupOf]
    exact (hΘ_scalar ω).mp hω
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    refine Subgroup.mem_map.mpr ⟨Θ.symm g, ?_, Θ.apply_symm_apply g⟩
    rw [Subgroup.mem_comap]
    exact (hΘ_scalar (Θ.symm g)).mpr (by simpa using hg)

noncomputable def psiProj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5} (Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀))
    (hΘ_scalar : ∀ g : ↥(fiveOmega k ε),
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ Subgroup.center (GL (Fin (k + 1)) (ZMod 5)) ↔
        (Θ g : GL ι (ZMod 5)) ∈ StatedScalars ι (ZMod 5)) :
    ↥(commutator (fiveProjective k ε π)) ≃* StatedProj (StatedOmega Q₀) :=
  (QuotientGroup.quotientKerEquivOfSurjective (qProj hk ε π) (qProj_surjective hk ε π)).symm.trans
    (QuotientGroup.congr (qProj hk ε π).ker
      ((StatedScalars ι (ZMod 5)).subgroupOf (StatedOmega Q₀)) Θ
      (by
        rw [qProj_ker hk ε π]
        exact qProj_ker_map_theta hk ε π Θ hΘ_scalar))

theorem psiProj_qProj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5} (Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀))
    (hΘ_scalar : ∀ g : ↥(fiveOmega k ε),
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ Subgroup.center (GL (Fin (k + 1)) (ZMod 5)) ↔
        (Θ g : GL ι (ZMod 5)) ∈ StatedScalars ι (ZMod 5)) (ω : ↥(fiveOmega k ε)) :
    psiProj hk ε π Θ hΘ_scalar (qProj hk ε π ω) =
      (QuotientGroup.mk (Θ ω) : StatedProj (StatedOmega Q₀)) := by
  rw [psiProj]
  simp only [MulEquiv.trans_apply]
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (qProj hk ε π)
      (qProj_surjective hk ε π)).symm (qProj hk ε π ω) =
      (QuotientGroup.mk ω : ↥(fiveOmega k ε) ⧸ (qProj hk ε π).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  exact QuotientGroup.congr_mk _ _ Θ _ ω

theorem mk_theta_eq_mk_of_intertwine {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q₀ : (ι → ZMod 5) → ZMod 5}
    (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5))
    (Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀))
    (hΘ_mul : ∀ (g : ↥(fiveOmega k ε)) (v : Fin (k + 1) → ZMod 5),
      ((Θ g : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5)) *ᵥ S v =
        S (((g : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v))
    {g : fiveReflectionGroup k ε π} {ω : ↥(fiveOmega k ε)} {z : fiveReflectionGroup k ε π}
    (hz : z ∈ Subgroup.center (fiveReflectionGroup k ε π)) (hg : g = omegaIncl hk ε π ω * z)
    {g₀ : ↥(StatedOmega Q₀)}
    (hg₀ : ∀ v : Fin (k + 1) → ZMod 5,
      ((g₀ : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5)) *ᵥ S v =
        S (((g : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)) :
    (QuotientGroup.mk (Θ ω) : StatedProj (StatedOmega Q₀)) =
      (QuotientGroup.mk g₀ : StatedProj (StatedOmega Q₀)) := by
  have hmat : ∀ (a b : GL ι (ZMod 5)),
      (∀ v, (a : Matrix ι ι (ZMod 5)) *ᵥ S v = (b : Matrix ι ι (ZMod 5)) *ᵥ S v) → a = b := by
    intro a b h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := S.surjective w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v
  have hz' := (mem_center_fiveReflectionGroup_iff hk ε π z).mp hz
  have hg_val : (g : GL (Fin (k + 1)) (ZMod 5)) =
      (ω : GL (Fin (k + 1)) (ZMod 5)) * (z : GL (Fin (k + 1)) (ZMod 5)) := by
    rw [hg]
    change ((omegaIncl hk ε π ω : ↥(fiveReflectionGroup k ε π)) : GL (Fin (k + 1)) (ZMod 5)) *
      (z : GL (Fin (k + 1)) (ZMod 5)) = _
    rw [coe_omegaIncl]
  have hdiv : (Θ ω : GL ι (ZMod 5)) * (g₀ : GL ι (ZMod 5))⁻¹ ∈ StatedScalars ι (ZMod 5) := by
    rcases hz' with hz1 | hz2
    · have hg0val : (g₀ : GL ι (ZMod 5)) = (Θ ω : GL ι (ZMod 5)) := by
        apply hmat
        intro v
        rw [hg₀ v, hg_val, hz1, mul_one, hΘ_mul ω v]
      rw [hg0val, mul_inv_cancel]
      rw [StatedScalars, MonoidHom.mem_range]
      exact ⟨1, by simp⟩
    · have hg0val : (g₀ : GL ι (ZMod 5)) = -((Θ ω : GL ι (ZMod 5))) := by
        apply hmat
        intro v
        rw [hg₀ v, hg_val, hz2, mul_neg, mul_one]
        simp only [Units.val_neg, Matrix.neg_mulVec, hΘ_mul ω v]
        exact map_neg S _
      rw [hg0val]
      have h1 : (Θ ω : GL ι (ZMod 5)) * (-((Θ ω : GL ι (ZMod 5))))⁻¹ = -1 := by
        rw [inv_neg, mul_neg, mul_inv_cancel]
      rw [h1, StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar,
        Subgroup.mem_center_iff]
      intro g
      simp [neg_mul, mul_neg]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  change (Θ ω : GL ι (ZMod 5)) * (g₀ : GL ι (ZMod 5))⁻¹ ∈ StatedScalars ι (ZMod 5)
  exact hdiv

end CFSG.OddTranspositions.PartThree

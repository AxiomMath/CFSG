module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

namespace KCLinearSubfield

variable {n : ℕ} {K : Type*} [Field K]

theorem map_subtype_mem_scalars {k : Subfield K} {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ scalars n k) : SpecialLinearGroup.map k.subtype g ∈ scalars n K := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  refine mem_scalars.mpr ⟨Units.map k.subtype.toMonoidHom c, ?_, ?_⟩
  · rw [← map_pow, hc, map_one]
  · ext i j
    by_cases hij : i = j
    · simp [SpecialLinearGroup.map_apply_coe, hgc, scalar_apply, hij]
    · simp [SpecialLinearGroup.map_apply_coe, hgc, scalar_apply, hij]

theorem mem_scalars_of_map_subtype_mem_scalars (hn : 0 < n) {k : Subfield K}
    {g : SpecialLinearGroup (Fin n) k}
    (hg : SpecialLinearGroup.map k.subtype g ∈ scalars n K) : g ∈ scalars n k := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  have hent : ∀ i j : Fin n, ((g : Matrix (Fin n) (Fin n) k) i j : K) =
      if i = j then (c : K) else 0 := by
    intro i j
    have := congrFun (congrFun hgc i) j
    simpa [SpecialLinearGroup.map_apply_coe, scalar_apply, diagonal_apply] using this
  have hcmem : (c : K) ∈ k := by
    have := hent i₀ i₀
    rw [ite_eq_left rfl] at this
    rw [← this]
    exact ((g : Matrix (Fin n) (Fin n) k) i₀ i₀).2
  have hc0 : (⟨(c : K), hcmem⟩ : k) ≠ 0 := fun h => c.ne_zero (congrArg Subtype.val h)
  refine mem_scalars.mpr ⟨Units.mk0 ⟨(c : K), hcmem⟩ hc0, ?_, ?_⟩
  · apply Units.ext
    apply Subtype.ext
    have h1 : ((c : Kˣ) : K) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    simpa using h1
  · ext i j
    rw [hent i j]
    by_cases hij : i = j
    · simp [scalar_apply, hij]
    · simp [scalar_apply, hij]

theorem ker_subfield_proj (hn : 0 < n) (k : Subfield K) :
    ((proj n K).comp (SpecialLinearGroup.map k.subtype)).ker = scalars n k := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff]
  exact ⟨mem_scalars_of_map_subtype_mem_scalars hn, map_subtype_mem_scalars⟩

theorem scalars_eq_comap_map_subtype (hn : 0 < n) (k : Subfield K) :
    scalars n k = (scalars n K).comap (SpecialLinearGroup.map k.subtype) := by
  ext g
  exact ⟨map_subtype_mem_scalars, mem_scalars_of_map_subtype_mem_scalars hn⟩

end KCLinearSubfield

open KCLinearSubfield

variable {n : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def linearSubfieldInclusion (n : ℕ) (k : Subfield K) :
    projectiveSL n k →* projectiveSL n K :=
  QuotientGroup.lift (scalars n k) ((proj n K).comp (SpecialLinearGroup.map k.subtype))
    (fun _ hg => proj_eq_one_iff.mpr (map_subtype_mem_scalars hg))

theorem linearSubfieldInclusion_proj (k : Subfield K) (g : SpecialLinearGroup (Fin n) k) :
    linearSubfieldInclusion n k (proj n k g) = proj n K (SpecialLinearGroup.map k.subtype g) :=
  rfl

theorem linearSubfieldInclusion_injective (hn : 0 < n) (k : Subfield K) :
    Function.Injective (linearSubfieldInclusion n k) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective n k x
  rw [linearSubfieldInclusion_proj, proj_eq_one_iff] at hx
  exact proj_eq_one_iff.mpr (mem_scalars_of_map_subtype_mem_scalars hn hx)

theorem mem_range_linearSubfieldInclusion {k : Subfield K} {x : projectiveSL n K} :
    x ∈ (linearSubfieldInclusion n k).range ↔
      ∃ g : SpecialLinearGroup (Fin n) K,
        (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ k) ∧ proj n K g = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨h, rfl⟩ := proj_surjective n k y
    exact ⟨SpecialLinearGroup.map k.subtype h,
      fun i j => ((h : Matrix (Fin n) (Fin n) k) i j).2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    let M : Matrix (Fin n) (Fin n) k := fun i j => ⟨(g : Matrix (Fin n) (Fin n) K) i j, hg i j⟩
    have hM : k.subtype.mapMatrix M = (g : Matrix (Fin n) (Fin n) K) := rfl
    have hdet : M.det = 1 := by
      apply k.subtype.injective
      rw [map_one, RingHom.map_det, hM]
      exact g.2
    obtain ⟨h, hh⟩ : ∃ h : SpecialLinearGroup (Fin n) k, (h : Matrix (Fin n) (Fin n) k) = M :=
      ⟨⟨M, hdet⟩, rfl⟩
    refine ⟨proj n k h, ?_⟩
    rw [linearSubfieldInclusion_proj]
    congr 1
    exact Subtype.ext (by rw [SpecialLinearGroup.map_apply_coe, hh, hM])

theorem fieldAut_linearSubfieldInclusion {k : Subfield K} {σ : K ≃+* K}
    (hσ : ∀ c ∈ k, σ c = c) (x : projectiveSL n k) :
    fieldAut n K σ (linearSubfieldInclusion n k x) = linearSubfieldInclusion n k x := by
  obtain ⟨h, rfl⟩ := proj_surjective n k x
  rw [linearSubfieldInclusion_proj, fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  simp [SpecialLinearGroup.map_apply_coe, hσ _ ((h : Matrix (Fin n) (Fin n) k) i j).2]

theorem card_semilinearFixedSubfield {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  obtain ⟨hdvd, S, hS, hScard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hScard
  have hk₀S : semilinearFixedSubfield σ = S := by
    apply SetLike.ext'
    rw [hS]
    ext x
    constructor
    · intro hx τ hτ
      have hx' : σ x = x := RingHom.mem_eqLocusField.mp hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
        (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx'
      exact hstab (Subgroup.zpow_mem_zpowers σ m)
    · intro hx
      exact RingHom.mem_eqLocusField.mpr (hx σ (Subgroup.mem_zpowers σ))
  exact ⟨hdvd, by rw [hk₀S, hScard]⟩

theorem card_rootsOfUnity_finite_field [Finite K] (hn : 0 < n) :
    Nat.card (rootsOfUnity n K) = Nat.gcd n (Nat.card K - 1) := by
  have hm : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hm0 : 0 < Nat.card K - 1 := hm ▸ Nat.card_pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (g : K) (Nat.card K - 1) :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr
      (by rw [← hm]; exact orderOf_eq_card_of_forall_mem_zpowers hg))
  have hall : rootsOfUnity (Nat.card K - 1) K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_rootsOfUnity, ← hm]
    exact pow_card_eq_one'
  have hinf : rootsOfUnity n K = rootsOfUnity (Nat.gcd n (Nat.card K - 1)) K := by
    rw [← rootsOfUnity_inf_rootsOfUnity, hall, inf_top_eq]
  have hd0 : Nat.gcd n (Nat.card K - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ hn).ne'
  have hdvd : Nat.gcd n (Nat.card K - 1) ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
  have : NeZero (Nat.gcd n (Nat.card K - 1)) := ⟨hd0⟩
  rw [hinf]
  refine card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mpr ⟨(g : K) ^ ((Nat.card K - 1) /
    Nat.gcd n (Nat.card K - 1)), ?_⟩
  have h1 := hprim.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hm0 hdvd) (Nat.pos_of_ne_zero hd0)).ne'
    (Nat.div_dvd_of_dvd hdvd)
  rwa [Nat.div_div_self hdvd hm0.ne'] at h1

theorem card_scalars [Finite K] (hn : 0 < n) :
    Nat.card (scalars n K) = Nat.gcd n (Nat.card K - 1) := by
  rw [scalars_eq_center, Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv,
    Fintype.card_fin]
  exact card_rootsOfUnity_finite_field hn

end CFSG.RankThree.PartOne

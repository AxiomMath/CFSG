module

public import CFSG.Quasithin.Vol2.F134LieL3Torus
public import CFSG.Quasithin.Vol2.F134LieL3Plane

public section

namespace CFSG.Quasithin.S146zY

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS CFSG.ComponentClassification CFSG.Quasithin.F134.LieL3
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem card_le_five [Finite K] {Q : Subgroup (projectiveSL 3 K)}
    (φ : upperTriangular 3 K →* Kˣ)
    (hφ : ∀ z (hz : z ∈ scalars 3 K), φ ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1)
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K)
    (hexp : ∀ x ∈ Q, x ^ 5 = 1)
    (hker : ∀ g (hg : g ∈ upperTriangular 3 K), proj 3 K g ∈ Q → φ ⟨g, hg⟩ = 1 →
      proj 3 K g = 1) :
    Nat.card Q ≤ 5 := by
  classical
  choose lift hlift using fun x : Q => proj_surjective 3 K (x : projectiveSL 3 K)
  have hB : ∀ x : Q, lift x ∈ upperTriangular 3 K := fun x => hQB _ (by rw [hlift]; exact x.2)
  have hroot : ∀ x : Q, φ ⟨lift x, hB x⟩ ^ 5 = 1 := by
    intro x
    have hz : lift x ^ 5 ∈ scalars 3 K := by
      rw [← proj_eq_one_iff, map_pow, hlift]
      exact hexp _ x.2
    rw [← map_pow]
    have he : (⟨lift x, hB x⟩ : upperTriangular 3 K) ^ 5 =
        ⟨lift x ^ 5, scalars_le_upperTriangular 3 K hz⟩ := Subtype.ext (by simp)
    rw [he, hφ _ hz]
  let f : Q → rootsOfUnity 5 K := fun x => ⟨φ ⟨lift x, hB x⟩, (mem_rootsOfUnity 5 _).mpr (hroot x)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : φ ⟨lift x, hB x⟩ = φ ⟨lift y, hB y⟩ := congrArg Subtype.val hxy
    have hmem : lift x * (lift y)⁻¹ ∈ upperTriangular 3 K := mul_mem (hB x) (inv_mem (hB y))
    have hproj : proj 3 K (lift x * (lift y)⁻¹) =
        (x : projectiveSL 3 K) * (y : projectiveSL 3 K)⁻¹ := by
      rw [map_mul, map_inv, hlift, hlift]
    have h1 : φ ⟨lift x * (lift y)⁻¹, hmem⟩ = 1 := by
      have he : (⟨lift x * (lift y)⁻¹, hmem⟩ : upperTriangular 3 K) =
          ⟨lift x, hB x⟩ * (⟨lift y, hB y⟩)⁻¹ := rfl
      rw [he, map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 := hker _ hmem (by rw [hproj]; exact mul_mem x.2 (inv_mem y.2)) h1
    rw [hproj, mul_inv_eq_one] at h2
    exact Subtype.ext h2
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity K 5)

theorem inf_projUnitriangular_eq_bot_twentyFive [Finite K] [CharP K 2]
    {Q : Subgroup (projectiveSL 3 K)} (hQ : Nat.card Q = 25) :
    Q ⊓ projUnitriangular 3 K = ⊥ := by
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hk
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hQ, card_projUnitriangular, hk, ← pow_mul]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem inf_ratioGroup_ne_bot_twentyFive [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : Nat.card Q = 25)
    (hexp : ∀ x ∈ Q, x ^ 5 = 1) : Q ⊓ ratioGroup K ≠ ⊥ := by
  intro hbot
  have := card_le_five ratioHom (fun z hz => ratioHom_scalar hz) hQB hexp
    (fun g hg hgQ h1 => by
      have hN : proj 3 K g ∈ Q ⊓ ratioGroup K :=
        ⟨hgQ, ⟨g, (ratioHom_eq_one_iff hg).mp h1, rfl⟩⟩
      rw [hbot] at hN
      exact hN)
  omega

theorem not_le_ratioGroup_twentyFive [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : Nat.card Q = 25)
    (hexp : ∀ x ∈ Q, x ^ 5 = 1) : ¬ Q ≤ ratioGroup K := by
  intro hle
  have hQU := inf_projUnitriangular_eq_bot_twentyFive hQ
  have := card_le_five firstRatio (fun z hz => firstRatio_scalar hz) hQB hexp
    (fun g hg hgQ h1 => by
      have hr := ratioHom_eq_one_of_proj_mem hg (hle hgQ)
      rw [ratioHom, MonoidHom.mul_apply, MonoidHom.inv_apply, h1, one_mul, inv_eq_one,
        secondRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, Units.ext_iff,
        coe_diagUnit, coe_diagUnit] at hr
      rw [firstRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, Units.ext_iff,
        coe_diagUnit, coe_diagUnit] at h1
      have hU : proj 3 K g ∈ Q ⊓ projUnitriangular 3 K :=
        ⟨hgQ, proj_mem_projUnitriangular hg h1 hr⟩
      rw [hQU] at hU
      exact hU)
  omega

end CFSG.Quasithin.S146zY

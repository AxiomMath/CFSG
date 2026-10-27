module

public import CFSG.Quasithin.Vol2.F134LieL3Torus
public import CFSG.Quasithin.Vol2.F134LieL3Plane

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Quasithin.F134.LieL3
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem inf_projUnitriangular_eq_bot_of_coprime [Finite K] [CharP K 2]
    {Q : Subgroup (projectiveSL 3 K)} (hQ : Nat.Coprime (Nat.card Q) 2) :
    Q ⊓ projUnitriangular 3 K = ⊥ := by
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hk
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [card_projUnitriangular, hk, ← pow_mul]
  exact Nat.Coprime.pow_right _ hQ

theorem card_le_of_exp [Finite K] {p : ℕ} [NeZero p] {Q : Subgroup (projectiveSL 3 K)}
    (φ : upperTriangular 3 K →* Kˣ)
    (hφ : ∀ z (hz : z ∈ scalars 3 K), φ ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1)
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K)
    (hexp : ∀ x ∈ Q, x ^ p = 1)
    (hker : ∀ g (hg : g ∈ upperTriangular 3 K), proj 3 K g ∈ Q → φ ⟨g, hg⟩ = 1 →
      proj 3 K g = 1) :
    Nat.card Q ≤ p := by
  classical
  choose lift hlift using fun x : Q => proj_surjective 3 K (x : projectiveSL 3 K)
  have hB : ∀ x : Q, lift x ∈ upperTriangular 3 K := fun x => hQB _ (by rw [hlift]; exact x.2)
  have hroot : ∀ x : Q, φ ⟨lift x, hB x⟩ ^ p = 1 := by
    intro x
    have hz : lift x ^ p ∈ scalars 3 K := by
      rw [← proj_eq_one_iff, map_pow, hlift]
      exact hexp _ x.2
    rw [← map_pow]
    have he : (⟨lift x, hB x⟩ : upperTriangular 3 K) ^ p =
        ⟨lift x ^ p, scalars_le_upperTriangular 3 K hz⟩ := Subtype.ext (by simp)
    rw [he, hφ _ hz]
  let f : Q → rootsOfUnity p K := fun x => ⟨φ ⟨lift x, hB x⟩, (mem_rootsOfUnity p _).mpr (hroot x)⟩
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
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity K p)

theorem inf_ratioGroup_ne_bot_of_exp [Finite K] [CharP K 2] {p : ℕ} [NeZero p]
    {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : p < Nat.card Q)
    (hexp : ∀ x ∈ Q, x ^ p = 1) : Q ⊓ ratioGroup K ≠ ⊥ := by
  intro hbot
  have := card_le_of_exp (p := p) ratioHom (fun z hz => ratioHom_scalar hz) hQB hexp
    (fun g hg hgQ h1 => by
      have hN : proj 3 K g ∈ Q ⊓ ratioGroup K :=
        ⟨hgQ, ⟨g, (ratioHom_eq_one_iff hg).mp h1, rfl⟩⟩
      rw [hbot] at hN
      exact hN)
  omega

theorem not_le_ratioGroup_of_exp [Finite K] [CharP K 2] {p : ℕ} [NeZero p]
    {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : p < Nat.card Q)
    (hodd : Nat.Coprime (Nat.card Q) 2) (hexp : ∀ x ∈ Q, x ^ p = 1) : ¬ Q ≤ ratioGroup K := by
  intro hle
  have hQU := inf_projUnitriangular_eq_bot_of_coprime hodd
  have := card_le_of_exp (p := p) firstRatio (fun z hz => firstRatio_scalar hz) hQB hexp
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

theorem proj_commutator_mem_projUnitriangular {g h : SL(3, K)} (hg : g ∈ upperTriangular 3 K)
    (hh : h ∈ upperTriangular 3 K) :
    proj 3 K (g * h * g⁻¹ * h⁻¹) ∈ projUnitriangular 3 K := by
  have hc : g * h * g⁻¹ * h⁻¹ ∈ upperTriangular 3 K :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hd : ∀ i, (((g * h * g⁻¹ * h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i i) = 1 := by
    intro i
    have h1 : diagUnit i (⟨g, hg⟩ * ⟨h, hh⟩ * ⟨g, hg⟩⁻¹ * ⟨h, hh⟩⁻¹ : upperTriangular 3 K) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (diagUnit i ⟨g, hg⟩),
        mul_inv_cancel_right, mul_inv_cancel]
    exact congrArg Units.val h1
  exact proj_mem_projUnitriangular hc ((hd 0).trans (hd 1).symm) ((hd 1).trans (hd 2).symm)

theorem mul_comm_of_borel [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K)
    (hodd : Nat.Coprime (Nat.card Q) 2) {x y : projectiveSL 3 K} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y = y * x := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  obtain ⟨h, rfl⟩ := proj_surjective 3 K y
  have hcom := proj_commutator_mem_projUnitriangular (hQB g hx) (hQB h hy)
  have hQ : proj 3 K (g * h * g⁻¹ * h⁻¹) ∈ Q ⊓ projUnitriangular 3 K :=
    ⟨mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy), hcom⟩
  rw [inf_projUnitriangular_eq_bot_of_coprime hodd, Subgroup.mem_bot] at hQ
  simp only [map_mul, map_inv] at hQ
  rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hQ

end CFSG.Quasithin.H13.NQCore.Psl3Even

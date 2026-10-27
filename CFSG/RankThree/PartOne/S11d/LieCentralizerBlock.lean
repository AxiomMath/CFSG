module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerPSL

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Matrix
open CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem isComponentOf_map_block {H : Type*} {T : Type} [Group H] [Group T] (π : H →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) (A : H) (B : Subgroup H)
    (hBq : CFSG.IsQuasisimple ↥B) (hBC : B ≤ Subgroup.centralizer ({A} : Set H))
    (hBnorm : ∀ g ∈ Subgroup.centralizer ({A} : Set H), ∀ f ∈ B, g * f * g⁻¹ ∈ B) :
    IsComponentOf (Subgroup.centralizer ({π A} : Set T)) (B.map π) := by
  have hBnc : ¬ B ≤ π.ker := fun hle => not_le_center_of_isQuasisimple hBq (hle.trans hker)
  set D₀ : Subgroup T := B.map π with hD₀
  have hD₀q : CFSG.IsQuasisimple ↥D₀ := CFSG.LocalCores.isQuasisimple_map hBq π hBnc
  set CA : Subgroup H := Subgroup.centralizer ({A} : Set H) with hCA
  set C0 : Subgroup T := CA.map π with hC0
  set Cx : Subgroup T := Subgroup.centralizer ({π A} : Set T) with hCx
  have hC0Cx : C0 ≤ Cx := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g * A = A * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hg']
  have hD₀C0 : D₀ ≤ C0 := Subgroup.map_mono hBC
  have hconj1 : ∀ g ∈ Cx, ∀ h ∈ C0, g * h * g⁻¹ ∈ C0 := by
    intro g hg h hh
    obtain ⟨G, rfl⟩ := hπ g
    obtain ⟨H', hH', rfl⟩ := hh
    refine ⟨G * H' * G⁻¹, ?_, by simp [map_mul, map_inv]⟩
    refine conj_mem_centralizer_of_commutator_central ?_ hH'
    refine hker (MonoidHom.mem_ker.mpr ?_)
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hconj0 : ∀ g ∈ C0, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀ := by
    intro g hg d hd
    obtain ⟨H', hH', rfl⟩ := hg
    obtain ⟨b₀, hb₀, rfl⟩ := hd
    exact ⟨H' * b₀ * H'⁻¹, hBnorm _ hH' _ hb₀, by simp [map_mul, map_inv]⟩
  have hCxN : Cx ≤ Subgroup.normalizer (C0 : Set T) := fun g hg =>
    mem_normalizer_of_forall_conj (hconj1 g hg) (fun x hx => by
      simpa using hconj1 g⁻¹ (Cx.inv_mem hg) x hx)
  refine ⟨hD₀C0.trans hC0Cx, hD₀q, ?_⟩
  have hD1C1 : D₀.subgroupOf Cx ≤ C0.subgroupOf Cx := fun g hg => hD₀C0 hg
  have hn1 : (C0.subgroupOf Cx).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC0Cx]
    exact hCxN
  have hn2 : ((D₀.subgroupOf Cx).subgroupOf (C0.subgroupOf Cx)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1C1]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgC0 : (g : T) ∈ C0 := hg
    constructor
    · intro hh
      exact hconj0 _ hgC0 _ hh
    · intro hh
      have := hconj0 _ (C0.inv_mem hgC0) _ hh
      exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
  exact Subgroup.IsSubnormal.trans hD1C1 hn2.isSubnormal hn1.isSubnormal

theorem exists_component_of_block {H : Type*} {T : Type} [Group H] [Group T] (π : H →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) (A : H) (B : Subgroup H)
    (hBq : CFSG.IsQuasisimple ↥B) (hBC : B ≤ Subgroup.centralizer ({A} : Set H))
    (hBnorm : ∀ g ∈ Subgroup.centralizer ({A} : Set H), ∀ f ∈ B, g * f * g⁻¹ ∈ B) :
    ∃ D : Subgroup T, CFSG.IsQuasisimple ↥D ∧ D ≤ Subgroup.centralizer ({π A} : Set T) ∧
      (D.subgroupOf (Subgroup.centralizer ({π A} : Set T))).IsSubnormal :=
  let h := isComponentOf_map_block π hπ hker A B hBq hBC hBnorm
  ⟨_, h.2.1, h.1, h.2.2⟩

theorem squarefree_minpoly_toLin'_of_pow_scalar {n p : ℕ} {K : Type} [Field K] (hpK : (p : K) ≠ 0)
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) := by
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p = algebraMap K (Matrix (Fin n) (Fin n) K) c := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  have haeval : Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
    have hX : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) =
        Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
  exact KCPrimary.squarefree_minpoly_of_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree haeval

theorem exists_normalized_involution {n : ℕ} [Nonempty (Fin n)] {K : Type} [Field K] [Finite K]
    [CharP K 2] {a s : GL (Fin n) K} {c₂ ν : Kˣ}
    (hs2 : s ^ 2 = GeneralLinearGroup.scalar (Fin n) c₂)
    (hcomm0 : a * s * a⁻¹ * s⁻¹ = GeneralLinearGroup.scalar (Fin n) ν) :
    ∃ μ : Kˣ, ((GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * s) ^ 2 = 1 ∧
      ((GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * s) * a =
        a * ((GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * s) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ^ 2 = c₂ := by
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c₂ : K)
    have hr0 : r ≠ 0 := fun h => c₂.ne_zero (by rw [hr, h, mul_zero])
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩
  refine ⟨μ, ?_⟩
  set w : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) μ with hw
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ν with hz
  have hwc : ∀ g : GL (Fin n) K, w * g = g * w := fun g => GeneralLinearGroup.scalar_commute μ g
  have hzc : ∀ g : GL (Fin n) K, z * g = g * z := fun g => GeneralLinearGroup.scalar_commute ν g
  have hwic : ∀ g : GL (Fin n) K, w⁻¹ * g = g * w⁻¹ := fun g => by
    have h1 : w * g = g * w := hwc g
    calc w⁻¹ * g = w⁻¹ * (g * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * g) * w⁻¹ := by rw [h1]
      _ = g * w⁻¹ := by group
  set s' : GL (Fin n) K := w⁻¹ * s with hs'
  have hss : s = w * s' := by rw [hs']; group
  have hww : w ^ 2 = GeneralLinearGroup.scalar (Fin n) c₂ := by
    rw [hw, ← map_pow, hμ]
  have hs'2 : s' ^ 2 = 1 := by
    have h1 : s' ^ 2 = w⁻¹ * w⁻¹ * s ^ 2 := by
      calc s' ^ 2 = w⁻¹ * s * (w⁻¹ * s) := by rw [hs', pow_two]
        _ = w⁻¹ * (s * w⁻¹) * s := by group
        _ = w⁻¹ * (w⁻¹ * s) * s := by rw [← hwic s]
        _ = w⁻¹ * w⁻¹ * (s * s) := by group
        _ = w⁻¹ * w⁻¹ * s ^ 2 := by rw [pow_two]
    rw [h1, hs2, ← hww]
    group
  have hcz : a * s' * a⁻¹ * s'⁻¹ = z := by
    have h1 : a * s * a⁻¹ * s⁻¹ = a * s' * a⁻¹ * s'⁻¹ := by
      calc a * s * a⁻¹ * s⁻¹ = a * (w * s') * a⁻¹ * (w * s')⁻¹ := by rw [← hss]
        _ = w * (a * s' * a⁻¹ * s'⁻¹) * w⁻¹ := by
          have := hwc a
          calc a * (w * s') * a⁻¹ * (w * s')⁻¹ = (a * w) * s' * a⁻¹ * s'⁻¹ * w⁻¹ := by group
            _ = (w * a) * s' * a⁻¹ * s'⁻¹ * w⁻¹ := by rw [← this]
            _ = w * (a * s' * a⁻¹ * s'⁻¹) * w⁻¹ := by group
        _ = a * s' * a⁻¹ * s'⁻¹ := by
          rw [hwc (a * s' * a⁻¹ * s'⁻¹)]
          group
    rw [← h1, hcomm0]
  have hz1 : z = 1 := by
    have h1 : (a * s' * a⁻¹) ^ 2 = 1 := by
      calc (a * s' * a⁻¹) ^ 2 = a * s' ^ 2 * a⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hs'2]; group
    have h2' : a * s' * a⁻¹ = z * s' := by
      rw [← hcz]; group
    rw [h2'] at h1
    have h3 : z ^ 2 = 1 := by
      calc z ^ 2 = z * z * (s' * s') * (s' * s')⁻¹ := by rw [pow_two]; group
        _ = z * s' * (z * s') * (s' * s')⁻¹ := by
          have : s' * z = z * s' := (hzc s').symm
          calc z * z * (s' * s') * (s' * s')⁻¹ = z * (z * s') * s' * (s' * s')⁻¹ := by group
            _ = z * (s' * z) * s' * (s' * s')⁻¹ := by rw [← this]
            _ = z * s' * (z * s') * (s' * s')⁻¹ := by group
        _ = (z * s') ^ 2 * (s' * s')⁻¹ := by rw [pow_two]
        _ = 1 := by
          rw [h1, one_mul, ← pow_two, hs'2]
          group
    have h4 : (ν : K) ^ 2 = 1 := by
      have h5 : GeneralLinearGroup.scalar (Fin n) (ν ^ 2) = 1 := by
        rw [map_pow]
        exact h3
      have h7 : ((GeneralLinearGroup.scalar (Fin n) (ν ^ 2) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h5]
      rw [GeneralLinearGroup.coe_scalar, Units.val_one,
        ← map_one (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K)] at h7
      have h8 := Matrix.scalar_inj.mp h7
      rw [Units.val_pow_eq_pow_val] at h8
      exact h8
    have h7 : (ν : K) = 1 := by
      have h8 : ((ν : K) - 1) ^ 2 = 0 := by
        have : ((ν : K) - 1) ^ 2 = (ν : K) ^ 2 - 1 - 2 * ((ν : K) - 1) := by ring
        rw [this, h4, h2]
        ring
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
    rw [hz, show ν = 1 from Units.ext h7, map_one]
  refine ⟨hs'2, ?_⟩
  have h1 : a * s' * a⁻¹ * s'⁻¹ = 1 := by rw [hcz, hz1]
  calc s' * a = (a * s' * a⁻¹ * s'⁻¹)⁻¹ * (a * s') := by group
    _ = a * s' := by rw [h1]; group

open CFSG.Blueprint CFSG.Assembly.LowTwoRank in
theorem statedClassicalModel_of_lieModel_classical {T : Type} [Group T] {t : StatedLieTag}
    (ht : t ∈ classicalTags) {n p f : ℕ} (h : LieModel T t n p f) :
    StatedClassicalModel T t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

end CFSG.RankThree.PartOne

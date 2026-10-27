module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.SubgroupLists.CommutatorScalarBound

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix Matrix.ProjGenLinGroup

variable {K : Type} [Field K]

theorem card_le_twentyseven_of_isElemAbelian_projImage [Finite K] (h3 : (3 : K) ≠ 0)
    {G₀ : Subgroup (GL (Fin 3) K)} (hdet : ∀ g ∈ G₀, (g : Matrix (Fin 3) (Fin 3) K).det = 1)
    (E : Subgroup ↥(projImage G₀)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  classical
  obtain ⟨hcomm, hexp⟩ := hE
  let π : G₀ →* ↥(projImage G₀) :=
    (ProjGenLinGroup.mk.comp G₀.subtype).codRestrict (projImage G₀) fun g => ⟨g.1, g.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨x, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hsurj := MonoidHom.subgroupComap_surjective π E hπ
  have hle : Nat.card E ≤ Nat.card (E.comap π) := Nat.card_le_card_of_surjective _ hsurj
  let R : Subgroup (GL (Fin 3) K) := (E.comap π).map G₀.subtype
  have hRcard : Nat.card R = Nat.card (E.comap π) :=
    Subgroup.card_map_of_injective G₀.subtype_injective
  have hπeq : ∀ r : G₀, ((π r : ↥(projImage G₀)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (r : GL (Fin 3) K) := fun r => rfl
  have hcenter : ∀ g : GL (Fin 3) K, ProjGenLinGroup.mk g = 1 →
      ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
    intro g hg
    rw [mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, rfl⟩ := hg
    exact ⟨(u : K), by simp⟩
  have hbound : Nat.card R ≤ 27 := by
    refine CFSG.RankThree.SubgroupLists.card_le_twentyseven_of_scalar_commutators h3 R ?_ ?_ ?_
    · rintro _ ⟨r, -, rfl⟩
      exact hdet r.1 r.2
    · rintro _ ⟨r₁, hr₁, rfl⟩ _ ⟨r₂, hr₂, rfl⟩
      apply hcenter
      have hc : (⟨π r₁, hr₁⟩ : E) * ⟨π r₂, hr₂⟩ = ⟨π r₂, hr₂⟩ * ⟨π r₁, hr₁⟩ :=
        hcomm.is_comm.comm _ _
      have hc' : π r₁ * π r₂ = π r₂ * π r₁ := congrArg Subtype.val hc
      have h1 : π (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc']
        group
      have h2 := congrArg Subtype.val h1
      rw [hπeq] at h2
      simpa using h2
    · rintro _ ⟨r, hr, rfl⟩
      apply hcenter
      have h1 : π (r ^ 3) = 1 := by
        have := hexp (π r) hr
        simpa using this
      have h2 := congrArg Subtype.val h1
      rw [hπeq] at h2
      simpa using h2
  omega

instance finite_projImage [Finite K] (G₀ : Subgroup (GL (Fin 3) K)) : Finite ↥(projImage G₀) := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  infer_instance

instance finite_projSL [Finite K] (n : ℕ) : Finite ↥(projSL n K) := by
  have : Finite (ProjGenLinGroup (Fin n) K) := by
    unfold ProjGenLinGroup
    infer_instance
  infer_instance

instance finite_projSU (n p f : ℕ) [Fact p.Prime] : Finite ↥(projSU n p f) := by
  have : Finite (ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) := by
    unfold ProjGenLinGroup
    infer_instance
  infer_instance

theorem pRank_three_le_three_projImage [Finite K] (h3 : (3 : K) ≠ 0)
    {G₀ : Subgroup (GL (Fin 3) K)} [Finite ↥(projImage G₀)]
    (hdet : ∀ g ∈ G₀, (g : Matrix (Fin 3) (Fin 3) K).det = 1)
    (H : Subgroup ↥(projImage G₀)) : CFSG.Assembly.pRank 3 H ≤ 3 := by
  unfold CFSG.Assembly.pRank
  apply csSup_le'
  rintro k ⟨E, -, hE, hcard⟩
  have hle := card_le_twentyseven_of_isElemAbelian_projImage h3 hdet E hE
  rw [hcard] at hle
  by_contra hk
  push Not at hk
  have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem localRank_three_le_three_projImage [Finite K] (h3 : (3 : K) ≠ 0)
    {G₀ : Subgroup (GL (Fin 3) K)} [Finite ↥(projImage G₀)]
    (hdet : ∀ g ∈ G₀, (g : Matrix (Fin 3) (Fin 3) K).det = 1) :
    localRank 3 ↥(projImage G₀) ≤ 3 := by
  unfold localRank CFSG.Open.twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨H, -, rfl⟩
  exact pRank_three_le_three_projImage h3 hdet H

theorem localRank_three_le_three_projSL [Finite K] (h3 : (3 : K) ≠ 0) :
    localRank 3 ↥(projSL 3 K) ≤ 3 := by
  unfold projSL
  refine localRank_three_le_three_projImage h3 fun g hg => ?_
  have := MonoidHom.mem_ker.1 hg
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val this

theorem localRank_three_le_three_projSU (p f : ℕ) [Fact p.Prime]
    (h3 : (3 : GaloisField p (2 * f)) ≠ 0) : localRank 3 ↥(projSU 3 p f) ≤ 3 := by
  unfold projSU
  refine localRank_three_le_three_projImage h3 fun g hg => ?_
  have hle := (Subgroup.closure_le _).2 (fun A (hA : A ∈ {A : GL (Fin 3) (GaloisField p (2 * f)) |
    Matrix.GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))).map (· ^ (p ^ f)))ᵀ *
      (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))) = 1}) => MonoidHom.mem_ker.2 hA.1)
  have := MonoidHom.mem_ker.1 (hle hg)
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val this

end CFSG.RankThree.PartOne.N143

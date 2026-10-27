module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

universe u

private theorem unit_pth_root_of_pow_eq_of_coprime {K : Type*} [Field K] {p d : ℕ}
    (hcop : Nat.Coprime p d) {u w : Kˣ} (h : w ^ p = u ^ d) :
    ∃ c : Kˣ, c ^ p = u := by
  have hq1 : (QuotientGroup.mk u : PowQuot K p) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  have hq2 : (QuotientGroup.mk u : PowQuot K p) ^ d = 1 := by
    rw [← QuotientGroup.mk_pow, ← h, powQuot_mk_eq_one_iff]
    exact ⟨w, rfl⟩
  have h3 : (QuotientGroup.mk u : PowQuot K p) ^ Nat.gcd p d = 1 :=
    pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
  rw [hcop.gcd_eq_one, pow_one] at h3
  exact powQuot_mk_eq_one_iff.mp h3

theorem toral_of_coprime {K : Type*} [Field K] {p : ℕ} [Finite K] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (hpι : ¬ p ∣ Fintype.card ι) {G : Subgroup (GL ι K)} (hG : IsProjElem p G) : IsToral G := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty ι := hι
    exact ⟨1, fun _ _ i => isEmptyElim i⟩
  have : Nonempty ι := hι
  have hcop : Nat.Coprime p (Fintype.card ι) := hp.coprime_iff_not_dvd.mpr hpι
  have hall : ∀ x ∈ G, ∃ c : Kˣ, x ^ p = GeneralLinearGroup.scalar ι (c ^ p) := by
    intro x hx
    obtain ⟨u, hu⟩ := hG.pow_scalar x hx
    have hdet : Matrix.GeneralLinearGroup.det x ^ p = u ^ Fintype.card ι := by
      have h := congrArg Matrix.GeneralLinearGroup.det hu
      rwa [map_pow, Matrix.GeneralLinearGroup.det_scalar] at h
    obtain ⟨c, hc⟩ := unit_pth_root_of_pow_eq_of_coprime (p := p) (d := Fintype.card ι) hcop hdet
    exact ⟨c, by rw [hu, hc]⟩
  have hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x := by
    intro h hhG hhp x hxG
    obtain ⟨u, hu⟩ := hG.comm_scalar x hxG h hhG
    have hud : u ^ Fintype.card ι = 1 := by
      have hdet := congrArg Matrix.GeneralLinearGroup.det hu
      simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar] at hdet
      rw [mul_comm (Matrix.GeneralLinearGroup.det h) (Matrix.GeneralLinearGroup.det x)] at hdet
      have h1 : (1 : Kˣ) * (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det h) =
          u ^ Fintype.card ι *
            (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det h) := by
        rw [one_mul]
        exact hdet
      exact (mul_right_cancel h1).symm
    have hup : u ^ p = 1 := by
      have h1 : (x * h * x⁻¹) ^ p = 1 := by
        rw [conj_pow, hhp, mul_one, mul_inv_cancel]
      have h2 : x * h * x⁻¹ = GeneralLinearGroup.scalar ι u * h := by
        rw [hu]; group
      rw [h2] at h1
      rw [(commute_scalar u h).mul_pow, hhp, mul_one] at h1
      rw [← map_pow] at h1
      exact scalar_injective (by rw [h1, map_one])
    have hu1 : u = 1 := by
      have hg : u ^ Nat.gcd p (Fintype.card ι) = 1 := pow_gcd_eq_one.mpr ⟨hup, hud⟩
      rwa [hcop.gcd_eq_one, pow_one] at hg
    rw [hu, hu1, map_one, one_mul]
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
  set H₁ : Set (GL ι K) := {y | y ∈ G ∧ y ^ p = 1} with hH₁
  have : Finite H₁ := Subtype.finite
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ H₁
    (fun x hx y hy => hcent y hy.1 hy.2 x hx.1) (fun x hx => hx.2)
  have hdecomp : ∀ x ∈ G, ∀ c : Kˣ, x ^ p = GeneralLinearGroup.scalar ι (c ^ p) →
      ∃ y ∈ H₁, x = GeneralLinearGroup.scalar ι c * y := fun x hx c hc =>
    ⟨GeneralLinearGroup.scalar ι c⁻¹ * x,
      ⟨G.mul_mem (hG.scalar_mem _) hx, pow_eq_one_of_pow_eq_scalar_pow hc⟩, by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]⟩
  refine ⟨A₀, fun x hx i j hij => ?_⟩
  obtain ⟨c, hc⟩ := hall x hx
  obtain ⟨y, hy, rfl⟩ := hdecomp x hx c hc
  change conjMatrix A₀ _ i j = 0
  rw [conjMatrix_scalar_mul, Matrix.smul_apply,
    show conjMatrix A₀ y i j = 0 from hA₀ y hy i j hij, smul_zero]

end CFSG.StandardType.TypeA.PGLTor

namespace CFSG.StandardType

namespace TableBUD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem ggPGUTorality_coprime {n d p : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXU : ∀ x ∈ X, ∃ M ∈ LargeEvenGUSet (Fin d) K (2 ^ n), conjAut d K M = x) :
    ∃ P ∈ primeFormUnitary h (idGram K d), ∀ M : GL (Fin d) K, conjAut d K M ∈ X →
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact absurd (dvd_zero p) hpd
  have hpK := dvd_card_sub_one' h hpq
  have htor := TypeA.PGLTor.toral_of_coprime (ι := Fin d) hp hpK (by simpa using hpd)
    (TypeA.isProjElem_comap hd hX)
  exact exists_unitary_diag_of_isToral h hp hpq hd hX hXU htor

end TableBUD

end CFSG.StandardType

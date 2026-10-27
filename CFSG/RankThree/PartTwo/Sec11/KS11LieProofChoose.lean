module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofND

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section Group

variable {M : Type*} [Group M]

theorem exists_pow_mul_pow_of_mem_closure {u v z : M} (huv : u * v = v * u)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hz : z ∈ Subgroup.closure ({u, v} : Set M)) :
    ∃ i k : ℕ, z = u ^ i * v ^ k := by
  have hinv : ∀ (w : M) (n : ℕ), w ^ 3 = 1 → (w ^ n)⁻¹ = w ^ (2 * n) := by
    intro w n hw
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, show 2 * n + n = 3 * n by ring, pow_mul, hw, one_pow]
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul y w _ _ hy hw =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hw
    refine ⟨a + a', b + b', ?_⟩
    have hcom : v ^ b * u ^ a' = u ^ a' * v ^ b :=
      ((Commute.pow_pow (huv : Commute u v) a' b).eq).symm
    calc u ^ a * v ^ b * (u ^ a' * v ^ b') = u ^ a * (v ^ b * u ^ a') * v ^ b' := by
          simp only [mul_assoc]
      _ = u ^ a * (u ^ a' * v ^ b) * v ^ b' := by rw [hcom]
      _ = u ^ (a + a') * v ^ (b + b') := by rw [pow_add, pow_add]; simp only [mul_assoc]
  | inv y _ hy =>
    obtain ⟨a, b, rfl⟩ := hy
    refine ⟨2 * a, 2 * b, ?_⟩
    have hcom : v ^ (2 * b) * u ^ (2 * a) = u ^ (2 * a) * v ^ (2 * b) :=
      ((Commute.pow_pow (huv : Commute u v) (2 * a) (2 * b)).eq).symm
    rw [_root_.mul_inv_rev, hinv v b hv3, hinv u a hu3, hcom]

end Group

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_closure_of_mem_centralizer {Y : Subgroup G} {c d z : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdY : d ∈ Y) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} {e : Kfˣ} (he3 : (e : Kf) ^ 3 = 1) (he1 : e ≠ 1)
    (hαc : ∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m :
        ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹)
    {B : GL (Fin 2) Kf} (hBdet : GeneralLinearGroup.det B = 1) (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    (hBe : (φ ((⟨d, hdY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹))
    (hz : z ∈ Subgroup.closure ({c, d} : Set G)) (hzC : z ∈ Sec4.thetaQuotCentralizer Y) :
    z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, k, rfl⟩ := exists_pow_mul_pow_of_mem_closure hcd hc3 hd3 hz
  have hdN : d ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hdY
  have hτz : (Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)
      ((⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ i * ⟨d, hdN⟩ ^ k) = 1 := by
    obtain ⟨y, hy, hyz⟩ := hzC
    have hy' : y = (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ i * ⟨d, hdN⟩ ^ k :=
      Subtype.ext (by simpa using hyz)
    rw [← hy']
    exact MonoidHom.mem_ker.mp hy
  rw [map_mul, map_pow, map_pow, MonoidHom.comp_apply, MonoidHom.comp_apply] at hτz
  have hα := congrArg (MulAut.congr φ) hτz
  rw [map_mul, map_pow, map_pow, map_one] at hα
  have hαd : ∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) m :
      ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹))⁻¹ := by
    intro m
    rw [thetaQuotMulAut_of_mem hdY hdN, mulAut_congr_conj, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hBe]
  set W := (h₀ * diagE e * h₀⁻¹) ^ i * (h₀ * blockHom B * h₀⁻¹) ^ k with hW
  have hU : ∀ m : projImage (slPi π 3 (p ^ f) Kf), (m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk W * m * (ProjGenLinGroup.mk W)⁻¹ := by
    intro m
    have h1 := mulAut_mul_coe (mulAut_pow_coe hαc i) (mulAut_pow_coe hαd k) m
    rw [hα, MulAut.one_apply] at h1
    rw [hW, map_mul, map_pow, map_pow]
    exact h1
  have hWs : W ∈ StatedScalars (Fin 3) Kf := by
    refine Sec13.mem_statedScalars_of_commute_mk hKf hq hq2 fun s hs => ?_
    have h1 := hU (projOf _ ⟨s, hs⟩)
    have h2 : ((projOf _ ⟨s, hs⟩ : projImage (slPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk s := rfl
    rw [h2] at h1
    calc ProjGenLinGroup.mk W * ProjGenLinGroup.mk s =
        (ProjGenLinGroup.mk W * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk W)⁻¹) *
          ProjGenLinGroup.mk W := by group
      _ = ProjGenLinGroup.mk s * ProjGenLinGroup.mk W := by rw [← h1]
  have hW' : W = h₀ * (diagE (e ^ i) * blockHom (B ^ k)) * h₀⁻¹ := by
    rw [hW, conj_pow_gl, conj_pow_gl, diagE_pow, map_pow]
    group
  rw [hW', conj_mem_statedScalars_iff] at hWs
  obtain ⟨ζ, hζ⟩ := hWs
  obtain ⟨he', hB'⟩ := eq_of_scalar_eq_diagE_mul_blockHom (det_pow_eq_one hBdet k) hζ
  have hz2 : (ζ : Kf) ^ 2 = 1 := by
    have h1 := congrArg Matrix.det hB'
    rw [matDet_eq_one (det_pow_eq_one hBdet k), Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at h1
    exact h1.symm
  have hz3 : (ζ : Kf) ^ 3 = 1 := by
    have h1 : (B ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hB3, one_pow]
    have h2 := congrArg (fun A : GL (Fin 2) Kf => (A : Matrix (Fin 2) (Fin 2) Kf) 0 0) h1
    simp only [Units.val_pow_eq_pow_val, hB', smul_pow, one_pow, Units.val_one] at h2
    simpa using h2
  have hz1 : (ζ : Kf) = 1 := by
    have h1 := hz3
    rw [pow_succ, hz2, one_mul] at h1
    exact h1
  have hBk : B ^ k = 1 := Units.ext (by rw [hB', hz1, one_smul, Units.val_one])
  have hei : e ^ i = 1 := Units.ext (by rw [he', hz1, Units.val_one])
  have he3' : e ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, he3, Units.val_one])
  have hBo : orderOf B = 3 := orderOf_eq_prime hB3 hB1
  have heo : orderOf e = 3 := orderOf_eq_prime he3' he1
  obtain ⟨k', rfl⟩ : 3 ∣ k := hBo ▸ orderOf_dvd_of_pow_eq_one hBk
  obtain ⟨i', rfl⟩ : 3 ∣ i := heo ▸ orderOf_dvd_of_pow_eq_one hei
  rw [pow_mul, pow_mul, hc3, hd3, one_pow, one_pow, one_mul]

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11

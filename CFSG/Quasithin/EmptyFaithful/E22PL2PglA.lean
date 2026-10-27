module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

omit [Fact p.Prime] [Field K] [Finite K] in
theorem e22pl2pgl_sixteen_dvd {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q * (q ^ 2 - 1) := by
  rcases hq with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 1 := ⟨q / 8, by omega⟩
    have h2 : (8 * k + 1) ^ 2 = 16 * (4 * k ^ 2 + k) + 1 := by ring
    have h3 : (8 * k + 1) ^ 2 - 1 = 16 * (4 * k ^ 2 + k) := by omega
    rw [h3]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 7 := ⟨q / 8, by omega⟩
    have h2 : (8 * k + 7) ^ 2 = 16 * (4 * k ^ 2 + 7 * k + 3) + 1 := by ring
    have h3 : (8 * k + 7) ^ 2 - 1 = 16 * (4 * k ^ 2 + 7 * k + 3) := by omega
    rw [h3]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

omit [Field K] [Finite K] in
theorem e22pl2pgl_isOddPrimePower (hp7 : 7 ≤ p) (hK : Nat.card K = p) :
    IsOddPrimePower (Nat.card K) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩

omit [Fact p.Prime] in
theorem e22pl2pgl_finite (K : Type) [Field K] [Finite K] : Finite (PGL2 K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem e22pl2pgl_sixteen_dvd_card_q (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) :
    16 ∣ Nat.card (PGL2 K) := by
  rw [pgl2_card_formula K]
  exact e22pl2pgl_sixteen_dvd hq8

omit [Finite K] in
theorem e22pl2pgl_simple_J (hcard : 3 < Nat.card K) : IsSimpleGroup ↥(pslRange K) := by
  have : IsSimpleGroup (PSL2 K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact (MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K))).symm.isSimpleGroup

theorem e22pl2pgl_perfect_J (hcard : 3 < Nat.card K) : Group.IsPerfect ↥(pslRange K) := by
  have : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard
  exact Group.IsPerfect.range (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))

theorem e22pl2pgl_nonabelian_J (hcard : 3 < Nat.card K) :
    ∃ a b : ↥(pslRange K), a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : Group.IsPerfect ↥(pslRange K) := e22pl2pgl_perfect_J hcard
  have : IsSimpleGroup ↥(pslRange K) := e22pl2pgl_simple_J hcard
  have hc : IsMulCommutative ↥(pslRange K) := ⟨⟨fun a b => hcomm a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (G := ↥(pslRange K)) hc

theorem e22pl2pgl_centralizer_J (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Subgroup.centralizer ((pslRange K : Subgroup (PGL2 K)) : Set (PGL2 K)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hinl : (SemidirectProduct.inl x : PGammaL2 K) ∈
      Subgroup.centralizer (pGammaL2PSLRange K : Set (PGammaL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := (mem_pGammaL2PSLRange_iff K y).1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_iff.mp hx
      (Matrix.ProjectiveSpecialLinearGroup.toPGL j) ⟨j, rfl⟩)
  rw [pGammaL2_pslRange_centralizer_eq_bot K hodd hcard, Subgroup.mem_bot] at hinl
  exact (Subgroup.mem_bot).2 (SemidirectProduct.inl_injective (hinl.trans (map_one _).symm))

theorem e22pl2pgl_card_J (hodd : IsOddPrimePower (Nat.card K)) :
    Nat.card (pslRange K) * 2 = Nat.card (PGL2 K) := by
  have := (pslRange K).card_mul_index
  rwa [pslRange_index_eq_two hodd] at this

theorem e22pl2pgl_not_le_J (hodd : IsOddPrimePower (Nat.card K)) {T : Subgroup (PGL2 K)}
    (hT : IsSylowIn 2 T ⊤) : ¬ T ≤ pslRange K := by
  have := e22pl2pgl_finite K
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.not_dvd_relIndex
  let S : Sylow 2 (PGL2 K) := hT.isPGroup.toSylow hindex
  have hcardT : Nat.card T = 2 ^ (Nat.card (PGL2 K)).factorization 2 :=
    Sylow.card_eq_multiplicity S
  have hdvd : 2 ^ (Nat.card (PGL2 K)).factorization 2 ∣ Nat.card (pslRange K) :=
    hcardT ▸ Subgroup.card_dvd_of_le hle
  have h3 : 2 ^ ((Nat.card (PGL2 K)).factorization 2 + 1) ∣ Nat.card (pslRange K) * 2 := by
    rw [pow_succ]
    exact Nat.mul_dvd_mul hdvd (dvd_refl 2)
  rw [e22pl2pgl_card_J hodd] at h3
  exact Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := PGL2 K)).ne' Nat.prime_two h3

theorem e22pl2pgl_sup_eq_top (hodd : IsOddPrimePower (Nat.card K)) {T : Subgroup (PGL2 K)}
    (hT : IsSylowIn 2 T ⊤) : pslRange K ⊔ T = ⊤ := by
  have hdvd : (pslRange K ⊔ T).index ∣ 2 := by
    have := Subgroup.index_dvd_of_le (le_sup_left : pslRange K ≤ pslRange K ⊔ T)
    rwa [pslRange_index_eq_two hodd] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hrel := Subgroup.relIndex_mul_index (le_sup_left : pslRange K ≤ pslRange K ⊔ T)
    rw [h2, pslRange_index_eq_two hodd] at hrel
    have h1 : (pslRange K).relIndex (pslRange K ⊔ T) = 1 := by omega
    have hle : pslRange K ⊔ T ≤ pslRange K := Subgroup.relIndex_eq_one.mp h1
    exact e22pl2pgl_not_le_J hodd hT (le_sup_right.trans hle)

theorem e22pl2pgl_relIndex_inf (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {T : Subgroup (PGL2 K)} (hT : IsSylowIn 2 T ⊤) : (T ⊓ pslRange K).relIndex T = 2 := by
  have : (pslRange K).Normal := pslRange_normal hodd hcard
  rw [Subgroup.inf_relIndex_left]
  have hdvd : (pslRange K).relIndex T ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal (pslRange K) T
    rwa [pslRange_index_eq_two hodd] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.mp h1) (e22pl2pgl_not_le_J hodd hT)
  · exact h2

theorem e22pl2pgl_param_ge {X : Type*} [Group X] [Finite X] {n m : ℕ}
    (hdvd : 2 ^ (n + 1) ∣ Nat.card X) (S : Sylow 2 X)
    (e : ↥(S : Subgroup X) ≃* DihedralGroup (2 ^ m)) : n ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardS : Nat.card S = 2 ^ (Nat.card X).factorization 2 := Sylow.card_eq_multiplicity S
  have hS : Nat.card (S : Subgroup X) = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hfac : n + 1 ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := X)).ne').mp hdvd
  have h1 : 2 ^ (n + 1) ≤ 2 ^ (Nat.card X).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hfac
  have h2 : 2 ^ (n + 1) ≤ 2 ^ (m + 1) := by
    rw [pow_succ 2 m, mul_comm]
    have : Nat.card (S : Subgroup X) = Nat.card S := rfl
    omega
  exact Nat.le_of_succ_le_succ ((Nat.pow_le_pow_iff_right (by norm_num)).mp h2)

theorem e22pl2pgl_sylow_dihedral_q (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) {T : Subgroup (PGL2 K)}
    (hT : IsSylowIn 2 T ⊤) :
    ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥T ≃* DihedralGroup (2 ^ m)) := by
  have := e22pl2pgl_finite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.not_dvd_relIndex
  let S : Sylow 2 (PGL2 K) := hT.isPGroup.toSylow hindex
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd S
  have hST : (S : Subgroup (PGL2 K)) = T := rfl
  refine ⟨m, ?_, ⟨(MulEquiv.subgroupCongr hST).symm.trans e⟩⟩
  exact e22pl2pgl_param_ge (n := 3) (by simpa using e22pl2pgl_sixteen_dvd_card_q hq8) S e

theorem e22pl2pgl_sylow_dihedral_J_q (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) (S : Sylow 2 ↥(pslRange K)) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup ↥(pslRange K)) ≃* DihedralGroup (2 ^ m)) := by
  have := e22pl2pgl_finite K
  have hD : HasDihedralSylowTwo ↥(pslRange K) :=
    hasDihedralSylowTwo_of_mulEquiv
      (MonoidHom.ofInjective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K))).symm
      (psl2_odd_hasDihedralSylowTwo_model K hodd)
  obtain ⟨m, -, ⟨e⟩⟩ := hD S
  refine ⟨m, e22pl2pgl_param_ge (n := 2) ?_ S e, ⟨e⟩⟩
  have h16 := e22pl2pgl_sixteen_dvd_card_q (K := K) hq8
  have hc := e22pl2pgl_card_J hodd
  show 2 ^ (2 + 1) ∣ Nat.card ↥(pslRange K)
  omega

end CFSG.Quasithin.E22L2

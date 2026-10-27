module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore
public import CFSG.Quasithin.H13.GoldschmidtCTKFamEA
public import CFSG.Quasithin.H13.GoldschmidtCTKFamOddLift
public import CFSG.GH74.SmallRanks.PSL

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Assembly.LowTwoRank

theorem det_eq_one_of_mem_statedSL (n : ℕ) (K : Type) [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem det_eq_one_of_mem_statedSU (n q : ℕ) (K : Type) [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSU n q K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem scalar_cube {K : Type} [Field K] (H : Subgroup (GL (Fin 3) K))
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) {g : GL (Fin 3) K} (hg : g ∈ H)
    (hs : g ∈ StatedScalars (Fin 3) K) : g ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hs
  have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 :=
    Units.ext (hdet _ hg)
  rw [Matrix.GeneralLinearGroup.det_scalar] at h1
  simp only [Fintype.card_fin] at h1
  rw [← map_pow, h1, map_one]

theorem odd_card_scalars {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 3) K))
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Odd (Nat.card ((StatedScalars (Fin 3) K).subgroupOf H)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf H) := by
    rcases Nat.even_or_odd (Nat.card ((StatedScalars (Fin 3) K).subgroupOf H)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((StatedScalars (Fin 3) K).subgroupOf H)) 2 h2
  have hx3 : x ^ 3 = 1 := by
    have := scalar_cube H hdet (x : ↥H).2 x.2
    exact Subtype.ext (Subtype.ext (by simpa using this))
  have := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at this
  omega

theorem false_of_model_gl3 {S : Type} [Group S] [Finite S] {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (H : Subgroup (GL (Fin 3) K))
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) (e : S ≃* StatedProj H)
    {V : Subgroup S} (hV : CFSG.Open.IsElemAbelian 2 V) (hV16 : Nat.card V = 16) : False := by
  let ψ : ↥H →* S := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hψ : Function.Surjective ψ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = (StatedScalars (Fin 3) K).subgroupOf H := by
    ext x
    simp [ψ]
  have hodd : Odd (Nat.card ψ.ker) := by
    rw [hker]
    exact odd_card_scalars H hdet
  obtain ⟨P, hsq, hcomm, hP⟩ := exists_elemAbelian_of_odd_ker ψ hψ hodd
    (V := V) hV.2 fun a ha b hb => mul_comm_of_isElemAbelian hV ha hb
  let P' : Subgroup (GL (Fin 3) K) := P.map H.subtype
  have hP'card : Nat.card P' = 16 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP, hV16]
  have hle := card_le_two_pow_gl h2 3 (E := P')
    (by
      rintro _ ⟨y, hy, rfl⟩
      have := hsq y hy
      rw [pow_two] at this
      simpa using congrArg Subtype.val this)
    (by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (hcomm y hy z hz))
  rw [hP'card] at hle
  norm_num at hle

theorem two_ne_zero_of_odd_card {K : Type} [Field K] [Finite K] (h : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  intro h2
  have h1 : addOrderOf (1 : K) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa using h2)
  have h3 : addOrderOf (1 : K) ∣ Nat.card K := addOrderOf_dvd_natCard 1
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h4 | h4
  · rw [AddMonoid.addOrderOf_eq_one_iff] at h4
    exact one_ne_zero h4
  · rw [h4] at h3
    exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 h3)

theorem four_le_twoRank {S : Type} [Group S] [Finite S] {V : Subgroup S}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hV16 : Nat.card V = 16) : 4 ≤ CFSG.Open.twoRank S := by
  refine le_csSup ⟨Nat.card S, ?_⟩ ⟨V, le_top, hV, by rw [hV16]; norm_num⟩
  rintro k ⟨B, -, -, hB⟩
  have h1 : 2 ^ k ≤ Nat.card S := hB ▸ Subgroup.card_le_card_group B
  exact (Nat.lt_two_pow_self.trans_le h1).le

theorem not_core_odd {S : Type} [Group S] [Finite S] (hS : SQTKOddFam S) :
    ¬ A5Core S := by
  rintro ⟨K, V, hVK, hKN, hK, hV16, hel, -⟩
  obtain ⟨p, hp, hp2, hcase⟩ := hS
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases hcase with ⟨f, -, hm⟩ | hm | hm
  · have h1 := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 hm
    have h2 := four_le_twoRank hel hV16
    omega
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact hpodd.pow
    exact false_of_model_gl3 (two_ne_zero_of_odd_card hodd) (StatedSL 3 F)
      (fun A hA => det_eq_one_of_mem_statedSL 3 F hA) e hel hV16
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (hpodd.pow).pow
    exact false_of_model_gl3 (two_ne_zero_of_odd_card hodd) (StatedSU 3 (p ^ 1) F)
      (fun A hA => det_eq_one_of_mem_statedSU 3 (p ^ 1) F hA) e hel hV16

theorem exclA5BlockFor_odd : ExclA5BlockFor fun S _ => SQTKOddFam S :=
  ExclA5BlockFor.of_not_core fun _ _ _ hS => not_core_odd hS

end CFSG.Quasithin.H13.CTK

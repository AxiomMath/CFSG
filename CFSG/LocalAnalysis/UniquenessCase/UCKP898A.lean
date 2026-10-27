module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP1
public import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem prime_ne_two_three_of_dvd_pow_sub_one {r s : ℕ} (hs : Odd s) (hrs : r ∣ 2 ^ s - 1) :
    r ≠ 2 ∧ r ≠ 3 := by
  obtain ⟨k, rfl⟩ := hs
  have h2 : 2 ≤ 2 ^ (2 * k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod2 : 2 ^ (2 * k + 1) % 2 = 0 := by
    rw [Nat.pow_mod]; simp
  have hmod3 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * k + 1) = t at *
  constructor
  · rintro rfl
    omega
  · rintro rfl
    omega

theorem u3_prime_descent {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSU3 X n) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) {α : MulAut X} (hα : α ^ r = 1)
    (hni : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 n K)
      (e : (X ⧸ center X) ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (M : uU h 3) (φ : K ≃+* K),
      orderOf φ = r ∧ r ∣ n ∧ Nat.card (semilinearFixedSubfield φ) = (2 ^ (n / r)) ^ 2 ∧
      (∀ x : K, φ x = x → h.bar x = x ^ 2 ^ (n / r)) ∧
      ∀ y : StatedProj (StatedSU 3 (2 ^ n) K), uFieldAut h (by norm_num) φ y = y →
        autQuot α (e.symm (uConjAut h (by norm_num) M y)) = e.symm (uConjAut h (by norm_num) M y) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hn2 : 2 ≤ n := u3Range X n hX
  have hP : commutator X = ⊤ := hX.1.1
  have hcl : StatedClassicalModel (X ⧸ center X) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX.2 (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq3 : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hn3 : 3 ≤ 3 := le_rfl
  have hn1 : 1 ≤ 3 := by norm_num
  obtain ⟨α', hα'⟩ : ∃ α' : MulAut (StatedProj (StatedSU 3 (2 ^ n) K)), α' = MulAut.congr e (autQuot α) :=
    ⟨_, rfl⟩
  have hα'r : α' ^ r = 1 := by
    rw [hα', ← map_pow, ← map_pow, hα, map_one, map_one]
  have hα1 : α ≠ 1 := fun h1 => hni ⟨1, by rw [h1, map_one]⟩
  have hα'1 : α' ≠ 1 := by
    intro h1
    apply hα1
    apply autQuot_injective hP
    rw [map_one]
    apply (MulAut.congr e).injective
    rw [← hα', h1, map_one]
  have hα'ord : orderOf α' = r := orderOf_eq_prime hα'r hα'1
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq3 α'
  have hφr : φ ^ r = 1 := fieldAut_pow_eq_one h hn3 hq3 (hαeq ▸ hα'r)
  by_cases hφ : φ = 1
  · exfalso
    rw [hφ, map_one, mul_one] at hαeq
    have hcop : ¬ r ∣ 3 := by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact hr.one_lt.ne' h1
      · exact hr3 h3
    have hinn := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.OrdPU.uConjAut_inner_of_coprime h hn3 hr hcop A
      (hαeq ▸ hα'r)
    rw [← hαeq] at hinn
    obtain ⟨p, hp⟩ := hinn
    apply hni
    have hqa : autQuot α ∈ (MulAut.conj : (X ⧸ center X) →* MulAut (X ⧸ center X)).range := by
      refine ⟨e.symm p, ?_⟩
      apply (MulAut.congr e).injective
      rw [← hα', ← hp]
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    obtain ⟨x, hx⟩ := exists_conj_autQuot hqa
    exact ⟨x, (autQuot_injective hP hx).symm.symm ▸ rfl⟩
  · have hφord : orderOf φ = r := orderOf_eq_prime hφr hφ
    obtain ⟨a', ha'⟩ : ∃ a' : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
        a' = MulAut.congr (uTransport h hn1) α' := ⟨_, rfl⟩
    have ha'ord : orderOf a' = r :=
      (ha' ▸ (MulEquiv.orderOf_eq (MulAut.congr (uTransport h hn1)) α').trans hα'ord)
    have hσa : primeFormFieldFactor h isPrimeFormGram_one hn3 hq3 a' = φ := by
      have := uFactor_apply h hn3 hq3 A φ
      rw [← hαeq] at this
      rw [ha']
      exact this
    obtain ⟨hrf, hcard, hbar, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hq3 hr hr2
        (by omega) a' ha'ord φ hσa hφord
    have hαh : α' = uConjAut h hn1 M * uFieldAut h hn1 φ * (uConjAut h hn1 M)⁻¹ := by
      have h1 : a' = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M *
          primeFormFieldHom h isPrimeFormGram_one φ *
          (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹ := by
        rw [← hM]
        group
      have h2 : α' = (MulAut.congr (uTransport h hn1)).symm a' := by
        rw [ha']
        exact ((MulAut.congr (uTransport h hn1)).symm_apply_apply α').symm
      rw [h2, h1, map_mul, map_mul, map_inv]
      rfl
    refine ⟨K, inferInstance, h, e, M, φ, hφord, hrf, hcard, hbar, fun y hy => ?_⟩
    have hfix : α' (uConjAut h hn1 M y) = uConjAut h hn1 M y := by
      rw [hαh]
      change (uConjAut h hn1 M) ((uFieldAut h hn1 φ) ((uConjAut h hn1 M)⁻¹ (uConjAut h hn1 M y))) = _
      rw [MulAut.inv_apply_self, hy]
    have h3 : e (autQuot α (e.symm (uConjAut h hn1 M y))) = uConjAut h hn1 M y := by
      have := hfix
      rw [hα'] at this
      simpa [MulAut.congr_apply] using this
    apply e.injective
    rw [h3, MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.UniquenessCase.UCK

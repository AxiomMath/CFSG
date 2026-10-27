module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements

public section

namespace CFSG.StandardType.GGQ2Frame.CoverComponents

open CFSG CFSG.Assembly CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private lemma l02qacv_conj_pow {M : Type*} [Group M] (x y : M) (n : ℕ) :
    (x * y * x⁻¹) ^ n = x * y ^ n * x⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

theorem automizerCoverEq_holds : AutomizerCoverEq := by
  intro G _ _ H A R _ hAH π ρ hρ hA hker hcop X φ
  have hρι : ∀ a : ↥A, π (Subgroup.inclusion hAH a) = ρ a := fun a => hρ a
  constructor
  · intro hφ
    rw [mem_ggAutomizer_iff] at hφ
    obtain ⟨g, hg, _hgn, hgc⟩ := hφ
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hhX, rfl⟩ := hg
    refine ⟨π h, Subgroup.mem_map.mpr ⟨h, hhX, rfl⟩, ?_⟩
    intro a
    have hconjH : Subgroup.inclusion hAH (φ a) =
        h * Subgroup.inclusion hAH a * h⁻¹ := by
      apply Subtype.ext
      simpa using hgc a
    calc
      ρ (φ a) = π (Subgroup.inclusion hAH (φ a)) := (hρι (φ a)).symm
      _ = π (h * Subgroup.inclusion hAH a * h⁻¹) := by rw [hconjH]
      _ = π h * π (Subgroup.inclusion hAH a) * (π h)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = π h * ρ a * (π h)⁻¹ := by rw [hρι a]
  · rintro ⟨y, hy, hconj⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨h₀, hh₀X, hy_eq⟩ := hy
    subst y
    rw [mem_ggAutomizer_iff]
    have key : ∀ a : ↥A,
        Subgroup.inclusion hAH (φ a) = h₀ * Subgroup.inclusion hAH a * h₀⁻¹ := by
      intro a
      set t : ↥H := (h₀ * Subgroup.inclusion hAH a * h₀⁻¹) *
        (Subgroup.inclusion hAH (φ a))⁻¹ with ht_def
      have htk : t ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simp only [ht_def, map_mul, map_inv]
        rw [hρι a, hρι (φ a), hconj a]
        group
      have htc : t ∈ Subgroup.center ↥H := hker htk
      have ht_mul : t * Subgroup.inclusion hAH (φ a) =
          h₀ * Subgroup.inclusion hAH a * h₀⁻¹ := by
        rw [ht_def]; group
      obtain ⟨n1, h1⟩ := (isPGroup_iff_pow_pow_eq_one.mp hA) a
      obtain ⟨n2, h2⟩ := (isPGroup_iff_pow_pow_eq_one.mp hA) (φ a)
      have hpow_a : a ^ (3 ^ max n1 n2) = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp
          (dvd_trans (orderOf_dvd_of_pow_eq_one h1) (pow_dvd_pow 3 (le_max_left n1 n2)))
      have hpow_φa : (φ a) ^ (3 ^ max n1 n2) = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp
          (dvd_trans (orderOf_dvd_of_pow_eq_one h2) (pow_dvd_pow 3 (le_max_right n1 n2)))
      have hcomm : Commute t (Subgroup.inclusion hAH (φ a)) :=
        (Subgroup.mem_center_iff.mp htc (Subgroup.inclusion hAH (φ a))).symm
      have ht_pow : t ^ (3 ^ max n1 n2) = 1 := by
        have hconjpow : (h₀ * Subgroup.inclusion hAH a * h₀⁻¹) ^ (3 ^ max n1 n2) = 1 := by
          rw [l02qacv_conj_pow, ← map_pow, hpow_a, map_one]
          group
        have hm : (t * Subgroup.inclusion hAH (φ a)) ^ (3 ^ max n1 n2) =
            t ^ (3 ^ max n1 n2) * (Subgroup.inclusion hAH (φ a)) ^ (3 ^ max n1 n2) :=
          hcomm.mul_pow _
        rw [← ht_mul, hm, ← map_pow, hpow_φa, map_one, mul_one] at hconjpow
        exact hconjpow
      have horder_dvd : orderOf t ∣ 3 ^ max n1 n2 := orderOf_dvd_of_pow_eq_one ht_pow
      have hker_dvd : orderOf t ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker htk
      have hcop3 : Nat.Coprime 3 (Nat.card π.ker) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop
      have hcop3N : Nat.Coprime (3 ^ max n1 n2) (Nat.card π.ker) := hcop3.pow_left _
      have hg1 : Nat.gcd (3 ^ max n1 n2) (Nat.card π.ker) = 1 := hcop3N
      have hdvd : orderOf t ∣ Nat.gcd (3 ^ max n1 n2) (Nat.card π.ker) :=
        Nat.dvd_gcd horder_dvd hker_dvd
      have horder1 : orderOf t = 1 := Nat.dvd_one.mp (hg1 ▸ hdvd)
      have ht1 : t = 1 := orderOf_eq_one_iff.mp horder1
      rw [ht1, one_mul] at ht_mul
      exact ht_mul
    have keyG : ∀ a : ↥A, ((φ a : ↥A) : G) = (h₀ : G) * (a : G) * (h₀ : G)⁻¹ := by
      intro a
      simpa only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv] using
        congrArg (fun x : ↥H => (x : G)) (key a)
    refine ⟨(h₀ : G), Subgroup.mem_map.mpr ⟨h₀, hh₀X, rfl⟩, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        have hmem : (h₀ : G) * b * (h₀ : G)⁻¹ = ((φ ⟨b, hb⟩ : ↥A) : G) :=
          (keyG ⟨b, hb⟩).symm
        rw [hmem]
        exact (φ ⟨b, hb⟩).2
      · intro hb'
        let a' : ↥A := φ.symm ⟨(h₀ : G) * b * (h₀ : G)⁻¹, hb'⟩
        have ha' : ((φ a' : ↥A) : G) = (h₀ : G) * b * (h₀ : G)⁻¹ := by
          simp [a']
        have hEq : (h₀ : G) * b * (h₀ : G)⁻¹ = (h₀ : G) * (a' : G) * (h₀ : G)⁻¹ :=
          ha'.symm.trans (keyG a')
        have hb_eq : b = (a' : G) :=
          mul_left_cancel (mul_right_cancel hEq)
        rw [hb_eq]
        exact a'.2
    · intro a
      exact keyG a

end

end CFSG.StandardType.GGQ2Frame.CoverComponents

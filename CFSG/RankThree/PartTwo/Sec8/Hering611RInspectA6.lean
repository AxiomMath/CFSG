module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank

section Cover

variable {H : Type} [Group H] [Finite H] (π : H →* alternatingGroup (Fin 6))

theorem a6_pow_three_of_pow_nine (g : alternatingGroup (Fin 6)) (h : g ^ 9 = 1) : g ^ 3 = 1 := by
  revert g
  decide +kernel

theorem card_eq_of_surjective (hπ : Function.Surjective π) :
    Nat.card H = 360 * Nat.card π.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (H ⧸ π.ker) = 360 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
      KFacts.card_alternatingGroup_six]
  rw [h1, h2]

theorem five_dvd_card (hπ : Function.Surjective π) : 5 ∣ Nat.card H := by
  rw [card_eq_of_surjective π hπ]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem eq_one_of_mem_ker_pow_nine (hker : ¬ 3 ∣ Nat.card π.ker) {z : H} (hz : z ∈ π.ker)
    (h9 : z ^ 9 = 1) : z = 1 := by
  have hord : orderOf z ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have hord' : orderOf z ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime 9 (Nat.card π.ker) := by
    have h3 : Nat.Coprime 3 (Nat.card π.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hker
    simpa using Nat.Coprime.pow_left 2 h3
  have : orderOf z ∣ Nat.gcd 9 (Nat.card π.ker) := Nat.dvd_gcd hord hord'
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem exists_elemAbelian_nine (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) :
    ∃ R : Subgroup H, IsElemAbelian 3 R ∧ Nat.card R = 9 ∧ R ⊓ π.ker = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hcard : Nat.card (R : Subgroup H) = 9 := by
    rw [Sylow.card_eq_multiplicity R, card_eq_of_surjective π hπ]
    have hk0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker]
    have : (Nat.factorization 360) 3 = 2 := by
      have h : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      simp
    rw [this]
    norm_num
  have hpow : ∀ x : (R : Subgroup H), (x : H) ^ 9 = 1 := fun x => by
    have := pow_card_eq_one' (G := (R : Subgroup H)) (x := x)
    rw [hcard] at this
    exact congrArg Subtype.val this
  refine ⟨R, ⟨?_, ?_⟩, hcard, ?_⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  · intro x hx
    have h9 : ((⟨x, hx⟩ : (R : Subgroup H)) : H) ^ 9 = 1 := hpow ⟨x, hx⟩
    have h39 : π (x ^ 3) ^ 9 = 1 := by
      rw [← map_pow, ← pow_mul, show 3 * 9 = 9 * 3 by norm_num, pow_mul]
      have : x ^ 9 = 1 := h9
      rw [this, one_pow, map_one]
    have hx3 : π x ^ 3 = 1 := by
      have h := a6_pow_three_of_pow_nine (π x)
        (by rw [← map_pow]; rw [show x ^ 9 = 1 from h9, map_one])
      exact h
    refine eq_one_of_mem_ker_pow_nine π hker (z := x ^ 3) ?_ ?_
    · rw [MonoidHom.mem_ker, map_pow, hx3]
    · rw [← pow_mul, show 3 * 9 = 9 * 3 by norm_num, pow_mul]
      rw [show x ^ 9 = 1 from h9, one_pow]
  · rw [eq_bot_iff]
    rintro z ⟨hzR, hzker⟩
    have h9 : z ^ 9 = 1 := hpow ⟨z, hzR⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_ker_pow_nine π hker hzker h9)

theorem eq_one_of_mem_center (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) {z : H}
    (hz : z ∈ Subgroup.center H) (h9 : z ^ 9 = 1) : z = 1 := by
  have hc : π z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨h, rfl⟩ := hπ a
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) h]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  exact eq_one_of_mem_ker_pow_nine π hker (MonoidHom.mem_ker.mpr hc) h9

end Cover

section Sub

variable {X : Type} [Group X] [Finite X]

@[expose] def IsA6Sub (P : Subgroup X) : Prop :=
  Group.IsPerfect P ∧
    Nonempty (P ⧸ aschbacherSolvableCore 3 ↥P ≃* alternatingGroup (Fin 6))

noncomputable def IsA6Sub.proj {P : Subgroup X} (e : P ⧸ aschbacherSolvableCore 3 ↥P ≃*
    alternatingGroup (Fin 6)) : ↥P →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' _)

theorem IsA6Sub.proj_surjective {P : Subgroup X} (e : P ⧸ aschbacherSolvableCore 3 ↥P ≃*
    alternatingGroup (Fin 6)) : Function.Surjective (IsA6Sub.proj e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem IsA6Sub.ker_proj {P : Subgroup X} (e : P ⧸ aschbacherSolvableCore 3 ↥P ≃*
    alternatingGroup (Fin 6)) : (IsA6Sub.proj e).ker = aschbacherSolvableCore 3 ↥P := by
  ext z
  simp [IsA6Sub.proj, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem IsA6Sub.not_dvd_ker {P : Subgroup X} (e : P ⧸ aschbacherSolvableCore 3 ↥P ≃*
    alternatingGroup (Fin 6)) : ¬ 3 ∣ Nat.card (IsA6Sub.proj e).ker := by
  rw [IsA6Sub.ker_proj]
  exact (solvable_prime_complement_core_characterization (H := ↥P) Nat.prime_three).2.2.1

theorem IsA6Sub.exists_elemAbelian_nine {P : Subgroup X} (h : IsA6Sub P) :
    ∃ R : Subgroup X, R ≤ P ∧ IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      ∀ z ∈ R, z ∈ Subgroup.center X → z = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := h
  obtain ⟨R, ⟨hcomm, hexp⟩, hcard, -⟩ := Hering611R.exists_elemAbelian_nine (IsA6Sub.proj e)
    (IsA6Sub.proj_surjective e) (IsA6Sub.not_dvd_ker e)
  refine ⟨R.map P.subtype, Subgroup.map_subtype_le R, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← ha, ← hb]
    have := hcomm.is_comm.comm (⟨a', ha'⟩ : R) ⟨b', hb'⟩
    exact congrArg (fun t : P => (t : X)) (congrArg Subtype.val this)
  · rintro _ ⟨a, ha, rfl⟩
    have := hexp a ha
    change (a : X) ^ 3 = 1
    rw [← Subgroup.coe_pow, this]
    rfl
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]
  · rintro _ ⟨a, ha, rfl⟩ hz
    have hz' : a ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp hz) g
    have h9 : a ^ 9 = 1 := by
      have := pow_card_eq_one' (G := (R : Subgroup ↥P)) (x := ⟨a, ha⟩)
      rw [hcard] at this
      exact congrArg Subtype.val this
    have := Hering611R.eq_one_of_mem_center (IsA6Sub.proj e) (IsA6Sub.proj_surjective e)
      (IsA6Sub.not_dvd_ker e) hz' h9
    rw [this]
    rfl

theorem IsA6Sub.eq_one_of_commute {P : Subgroup X} (h : IsA6Sub P) {z : X} (hz : z ∈ P)
    (hc : ∀ p ∈ P, p * z = z * p) (h9 : z ^ 9 = 1) : z = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := h
  have hz' : (⟨z, hz⟩ : P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  have h9' : (⟨z, hz⟩ : P) ^ 9 = 1 := Subtype.ext (by simpa using h9)
  have := Hering611R.eq_one_of_mem_center (IsA6Sub.proj e) (IsA6Sub.proj_surjective e)
    (IsA6Sub.not_dvd_ker e) hz' h9'
  exact congrArg Subtype.val this

theorem IsA6Sub.five_dvd_card {P : Subgroup X} (h : IsA6Sub P) : 5 ∣ Nat.card X := by
  obtain ⟨-, ⟨e⟩⟩ := h
  exact (Hering611R.five_dvd_card (IsA6Sub.proj e) (IsA6Sub.proj_surjective e)).trans
    (Subgroup.card_subgroup_dvd_card P)

theorem IsA6Sub.three_dvd_card {P : Subgroup X} (h : IsA6Sub P) : 3 ∣ Nat.card X := by
  obtain ⟨-, ⟨e⟩⟩ := h
  have h1 : 3 ∣ Nat.card P := by
    rw [Hering611R.card_eq_of_surjective (IsA6Sub.proj e) (IsA6Sub.proj_surjective e)]
    exact Dvd.dvd.mul_right (by norm_num) _
  exact h1.trans (Subgroup.card_subgroup_dvd_card P)

theorem IsA6Sub.ne_bot {P : Subgroup X} (hP : IsA6Sub P) : P ≠ ⊥ := by
  obtain ⟨R, hRP, -, hR9, -⟩ := hP.exists_elemAbelian_nine
  rintro rfl
  have h := Subgroup.card_le_of_le hRP
  rw [Subgroup.card_bot, hR9] at h
  omega

theorem IsA6Sub.card_eq_of_isSimpleGroup {P : Subgroup X} (hP : IsA6Sub P)
    [IsSimpleGroup ↥P] : Nat.card P = 360 := by
  obtain ⟨-, ⟨e6⟩⟩ := hP
  have hPcard := Hering611R.card_eq_of_surjective (IsA6Sub.proj e6) (IsA6Sub.proj_surjective e6)
  rw [IsA6Sub.ker_proj] at hPcard
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥P) with h | h
  · rw [hPcard, h, Subgroup.card_bot]
  · exfalso
    rw [h, Subgroup.card_top] at hPcard
    have : 0 < Nat.card P := Nat.card_pos
    omega

end Sub

end CFSG.RankThree.PartTwo.Sec8.Hering611R

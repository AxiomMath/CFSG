module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalTrace
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalMinNormal
import CFSG.CGT.PushingUpLit.SYMB.ProdCard
import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.CentreCubeOne
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Γ : Type*} [Group Γ]

open scoped commutatorElement

private theorem comap_scalars_commute (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    {x : Γ} (hx : x ∈ (StatedScalars ι K).comap ρ) (g : Γ) : g * x = x * g := by
  have hx' : ρ x ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  rw [Subgroup.mem_center_iff] at hx'
  exact hρ (by rw [map_mul, map_mul]; exact hx' (ρ g))

private theorem comap_scalars_le_center (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ) :
    (StatedScalars ι K).comap ρ ≤ Subgroup.center Γ := by
  intro x hx
  exact Subgroup.mem_center_iff.mpr (comap_scalars_commute ρ hρ hx)

private theorem comap_scalars_normal (ρ : Γ →* GL ι K) :
    ((StatedScalars ι K).comap ρ).Normal :=
  (StatedScalars.normal ι K).comap ρ

theorem isPGroup_two_scalars [Finite Γ] (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥) :
    IsPGroup 2 ((StatedScalars ι K).comap ρ) := by
  classical
  let Z := (StatedScalars ι K).comap ρ
  have hZcenter : Z ≤ Subgroup.center Γ := comap_scalars_le_center ρ hρ
  have h5ndvd : ¬ 5 ∣ Nat.card Z := by
    intro h5dvd
    have hZfin : Finite Z := Finite.of_injective (fun z : Z => (z : Γ)) Subtype.coe_injective
    let : Fintype Z := Fintype.ofFinite Z
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card (G := Z) 5
      (by simpa [Nat.card_eq_fintype_card] using h5dvd)
    have hzGord : orderOf (z : Γ) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact hzord
    let A : Subgroup Γ := Subgroup.zpowers (z : Γ)
    have hAcenter : A ≤ Subgroup.center Γ :=
      le_trans (Subgroup.zpowers_le.mpr z.2) hZcenter
    have hAnorm : A.Normal := Subgroup.normal_of_le_center hAcenter
    have hA5 : IsPGroup 5 A := by
      refine IsPGroup.of_card (p := 5) (n := 1) ?_
      rw [Nat.card_zpowers, hzGord]
      norm_num
    have hAbot : A = ⊥ := hO5 A hAnorm hA5
    have hzA : (z : Γ) ∈ A := Subgroup.mem_zpowers (z : Γ)
    have hz1 : (z : Γ) = 1 := by
      have hmem : (z : Γ) ∈ (⊥ : Subgroup Γ) := hAbot ▸ hzA
      simpa using hmem
    rw [hz1] at hzGord
    exact absurd hzGord (by norm_num)
  have hprime : ∀ d : ℕ, d.Prime → d ∣ Nat.card Z → d = 2 := by
    intro d hd hdvd
    rcases hΓ d hd (hdvd.trans (Subgroup.card_subgroup_dvd_card Z)) with h2 | h5
    · exact h2
    · exact absurd (h5 ▸ hdvd) h5ndvd
  have : Nonempty Z := ⟨⟨1, Z.one_mem⟩⟩
  have hZfin : Finite Z := Finite.of_injective (fun z : Z => (z : Γ)) Subtype.coe_injective
  refine IsPGroup.of_card (p := 2) (n := (Nat.card Z).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) ?_ ?_)
  · exact Nat.card_pos.ne'
  · intro d hd hdvd
    exact hprime d hd hdvd

private theorem isPGroup_two_of_sq_mem [Finite Γ] (ρ : Γ →* GL ι K)
    (hρ : Function.Injective ρ)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥)
    {N : Subgroup Γ} (hsq : ∀ x ∈ N, x * x ∈ (StatedScalars ι K).comap ρ) :
    IsPGroup 2 N := by
  let Z := (StatedScalars ι K).comap ρ
  have hZ2 : IsPGroup 2 Z := isPGroup_two_scalars ρ hρ hΓ hO5
  refine isPGroup_iff_pow_pow_eq_one.mpr fun x => ?_
  obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hZ2 ⟨(x : Γ) * x, hsq x x.2⟩
  have hk' : ((x : Γ) * x) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  show (x : Γ) ^ 2 ^ (k + 1) = 1
  rw [pow_succ' (2) k, pow_mul, pow_two]
  exact hk'

theorem isQuatType_of_elementary [Finite Γ] (hK : ringChar K ≠ 2) (ρ : Γ →* GL ι K)
    (hρ : Function.Injective ρ) (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥)
    (hab : ∀ A : Subgroup Γ, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → IsPGroup 2 A →
      A ≤ (StatedScalars ι K).comap ρ)
    {N : Subgroup Γ} [N.Normal] (hZN : (StatedScalars ι K).comap ρ < N) {r : ℕ} (hr : r.Prime)
    (hpow : ∀ x ∈ N, x ^ r ∈ (StatedScalars ι K).comap ρ)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ (StatedScalars ι K).comap ρ) :
    IsQuatType ρ N := by
  classical
  have hK' : ringChar K ≠ 2 := hK
  let Z := (StatedScalars ι K).comap ρ
  have hZ2 : IsPGroup 2 Z := isPGroup_two_scalars ρ hρ hΓ hO5
  have hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g :=
    fun z hz => comap_scalars_commute ρ hρ hz
  have hcz : ∀ x ∈ N, ∀ y ∈ N, (x * y * x⁻¹ * y⁻¹) ^ r = 1 := by
    intro x hx y hy
    set z : Γ := x * y * x⁻¹ * y⁻¹ with hzdef
    have hzZ : z ∈ Z := hcomm x hx y hy
    have hzcomm : ∀ w : Γ, z * w = w * z := fun w => (hZc z hzZ w).symm
    have hstep : x * y * x⁻¹ = z * y := by
      rw [hzdef]
      group
    have hpowk : ∀ k : ℕ, x * y ^ k * x⁻¹ = z ^ k * y ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc x * y ^ (k + 1) * x⁻¹
              = (x * y ^ k * x⁻¹) * (x * y * x⁻¹) := by group
            _ = (z ^ k * y ^ k) * (z * y) := by rw [ih, hstep]
            _ = z ^ (k + 1) * y ^ (k + 1) := by
                  rw [pow_succ, pow_succ, mul_assoc (z ^ k) (y ^ k) (z * y),
                    ← mul_assoc (y ^ k) z y, ← hzcomm (y ^ k)]
                  group
    have h1 := hpowk r
    have hyrZ : y ^ r ∈ Z := hpow y hy
    have hconj : x * y ^ r * x⁻¹ = y ^ r := by
      rw [hZc (y ^ r) hyrZ x]
      group
    have hzeq : z ^ r * y ^ r = y ^ r := h1.symm.trans hconj
    have hzr : z ^ r = 1 := by
      have := congrArg (fun w => w * (y ^ r)⁻¹) hzeq
      simpa [mul_assoc] using this
    exact hzr
  have hz_eq_one : ∀ x ∈ N, ∀ y ∈ N, r ≠ 2 → x * y * x⁻¹ * y⁻¹ = 1 := by
    intro x hx y hy hr2
    set z : Γ := x * y * x⁻¹ * y⁻¹ with hzdef
    have hzr : z ^ r = 1 := hcz x hx y hy
    have hzZ : z ∈ Z := hcomm x hx y hy
    obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow hZ2 ⟨z, hzZ⟩
    have hk' : orderOf z ∣ 2 ^ k := by
      rwa [Subgroup.orderOf_mk z hzZ] at hk
    have hdivr : orderOf z ∣ r := orderOf_dvd_of_pow_eq_one hzr
    rcases (Nat.dvd_prime hr).mp hdivr with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      apply hr2
      have hrdvd2k : r ∣ 2 ^ k := h1 ▸ hk'
      have hrdvd2 : r ∣ 2 := Nat.Prime.dvd_of_dvd_pow hr hrdvd2k
      rcases (Nat.dvd_prime Nat.prime_two).mp hrdvd2 with h | h
      · exact absurd h hr.ne_one
      · exact h
  have hNab_of_ne_two (hr2 : r ≠ 2) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have hz1 : x * y * x⁻¹ * y⁻¹ = 1 := hz_eq_one x hx y hy hr2
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hz1, one_mul]
  have hr_two : r = 2 := by
    by_contra hr2
    have hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := hNab_of_ne_two hr2
    obtain ⟨x, hxN, hxZ⟩ := SetLike.exists_of_lt hZN
    have hxrZ : x ^ r ∈ Z := hpow x hxN
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hZ2 ⟨x ^ r, hxrZ⟩
    have hxpow : x ^ (r * 2 ^ k) = 1 := by
      have hk' : ((x ^ r : Γ) ^ 2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rwa [← pow_mul] at hk'
    have hxorddvd : orderOf x ∣ r * 2 ^ k := orderOf_dvd_of_pow_eq_one hxpow
    have hxord_ne : orderOf x ≠ 0 := by
      intro h0
      have hz : r * 2 ^ k = 0 := Nat.eq_zero_of_zero_dvd (h0 ▸ hxorddvd)
      have hpos : 0 < r * 2 ^ k := Nat.mul_pos hr.pos (pow_pos (by norm_num) k)
      omega
    have hrdvdx : r ∣ orderOf x := by
      by_contra hrdvd
      have hcop : r.Coprime (orderOf x) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrdvd
      have hdvd2k : orderOf x ∣ 2 ^ k := hcop.symm.dvd_of_dvd_mul_left hxorddvd
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hxmem : x ∈ Subgroup.zpowers (x ^ r) :=
        Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simpa using hm⟩
      exact hxZ (Subgroup.zpowers_le.mpr hxrZ hxmem)
    have hr5 : r = 5 := by
      rcases hΓ r hr (hrdvdx.trans (orderOf_dvd_natCard x)) with h2 | h5
      · exact absurd h2 hr2
      · exact h5
    have h5dvdx : 5 ∣ orderOf x := hr5 ▸ hrdvdx
    let y : Γ := x ^ (orderOf x / 5)
    have hyord : orderOf y = 5 := orderOf_pow_orderOf_div hxord_ne h5dvdx
    have hyN : y ∈ N := N.pow_mem hxN _
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hy5 : y ^ 5 = 1 := (orderOf_eq_prime_iff.mp hyord).1
    have hyne : y ≠ 1 := (orderOf_eq_prime_iff.mp hyord).2
    let A : Subgroup Γ :=
      { carrier := {g | g ∈ N ∧ g ^ 5 = 1}
        one_mem' := ⟨N.one_mem, by norm_num⟩
        mul_mem' := by
          intro a b ha hb
          refine ⟨N.mul_mem ha.1 hb.1, ?_⟩
          have hcommab : Commute a b := hNab a ha.1 b hb.1
          rw [hcommab.mul_pow 5, ha.2, hb.2, one_mul]
        inv_mem' := by
          intro a ha
          refine ⟨N.inv_mem ha.1, ?_⟩
          rw [inv_pow, ha.2]
          simp }
    have hAnorm : A.Normal := by
      refine Subgroup.Normal.mk ?_
      rintro a ⟨haN, ha5⟩ g
      refine ⟨(inferInstance : N.Normal).conj_mem a haN g, ?_⟩
      rw [conj_pow, ha5]
      group
    have hA5 : IsPGroup 5 A := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro a
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa using a.2.2
    have hyA : y ∈ A := ⟨hyN, hy5⟩
    have hAne : A ≠ ⊥ := by
      intro hbot
      have hmem : y ∈ (⊥ : Subgroup Γ) := hbot ▸ hyA
      exact hyne (by simpa using hmem)
    exact hAne (hO5 A hAnorm hA5)
  subst r
  refine ⟨inferInstance, hZN.le, ?_, ?_, ?_⟩
  · intro x hx
    simpa [sq] using hpow x hx
  · intro x hx y hy
    have hzZ : x * y * x⁻¹ * y⁻¹ ∈ Z := hcomm x hx y hy
    have hzscalar : ρ (x * y * x⁻¹ * y⁻¹) ∈ StatedScalars ι K :=
      Subgroup.mem_comap.mp hzZ
    obtain ⟨u, hu⟩ := hzscalar
    have hz2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := hcz x hx y hy
    have hmap : ρ (x * y) = ρ (x * y * x⁻¹ * y⁻¹) * ρ (y * x) := by
      rw [← map_mul]
      congr 1
      group
    rcases isEmpty_or_nonempty ι with hιempty | hιne
    · left
      have : IsEmpty ι := hιempty
      apply hρ
      have hsub : (ρ (x * y) : GL ι K) = ρ (y * x) := Subsingleton.elim _ _
      exact hsub
    · let i : ι := Classical.choice hιne
      have hu2 : (u : K) ^ 2 = 1 := by
        have hsq : ρ (x * y * x⁻¹ * y⁻¹) * ρ (x * y * x⁻¹ * y⁻¹) = 1 := by
          rw [← map_mul, ← pow_two, hz2, map_one]
        have hmat : (ρ (x * y * x⁻¹ * y⁻¹) : Matrix ι ι K) *
            (ρ (x * y * x⁻¹ * y⁻¹) : Matrix ι ι K) = 1 := by
          have := congrArg (fun A : GL ι K => (A : Matrix ι ι K)) hsq
          simpa using this
        rw [← hu] at hmat
        have hentry := congrArg (fun A : Matrix ι ι K => A i i) hmat
        simpa [pow_two, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_mul] using hentry
      rcases (sq_eq_one_iff.mp hu2) with hu1 | huneg
      · left
        have hu1' : u = 1 := Units.ext (by simpa using hu1)
        apply hρ
        rw [hmap, ← hu, hu1', map_one, one_mul]
      · right
        have huneg' : u = -1 := Units.ext (by simpa using huneg)
        have hneg : ((Matrix.GeneralLinearGroup.scalar ι (-1 : Kˣ) : GL ι K) :
              Matrix ι ι K) * (ρ (y * x) : Matrix ι ι K) = -(ρ (y * x) : Matrix ι ι K) := by
          rw [Matrix.GeneralLinearGroup.coe_scalar]
          ext a b
          rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.neg_apply]
          simp
        have hfinal : (ρ (x * y) : Matrix ι ι K) =
            ((Matrix.GeneralLinearGroup.scalar ι (-1 : Kˣ) : GL ι K) : Matrix ι ι K) *
              (ρ (y * x) : Matrix ι ι K) := by
          rw [hmap, Units.val_mul, ← hu, huneg']
        rw [hfinal, hneg]
  · intro x hx hxc
    let C : Subgroup Γ := Subgroup.centralizer (N : Set Γ) ⊓ N
    have hCnormal : C.Normal := inferInstance
    have hCabelian : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp ha.1 b hb.2).symm
    have hCsq : ∀ a ∈ C, a * a ∈ Z := fun a ha => by
      have h := hpow a ha.2
      rwa [sq] at h
    have hC2 : IsPGroup 2 C := isPGroup_two_of_sq_mem ρ hρ hΓ hO5 hCsq
    have hCleZ : C ≤ Z := hab C hCnormal hCabelian hC2
    have hxC : x ∈ C := by
      refine ⟨?_, hx⟩
      show ∀ y ∈ (N : Set Γ), y * x = x * y
      intro y hy
      exact (hxc y hy).symm
    exact hCleZ hxC

theorem isQuatType_sup [Finite Γ] (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    {N₁ N₂ : Subgroup Γ} (h₁ : IsQuatType ρ N₁) (h₂ : IsQuatType ρ N₂)
    (hc : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    IsQuatType ρ (N₁ ⊔ N₂) ∧ Nat.card (N₁ ⊔ N₂ : Subgroup Γ) *
      Nat.card ((StatedScalars ι K).comap ρ) = Nat.card N₁ * Nat.card N₂ := by
  classical
  let Z := (StatedScalars ι K).comap ρ
  have h₁n : N₁.Normal := h₁.normal
  have h₂n : N₂.Normal := h₂.normal
  have hinf : N₁ ⊓ N₂ = Z := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact h₁.mem_of_comm x hx.1 (fun y hy => (hc y hy x hx.2).symm)
    · exact le_inf h₁.scalars_le h₂.scalars_le
  have hsq : ∀ x ∈ N₁ ⊔ N₂, x * x ∈ Z := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hmul : (x₁ * x₂) * (x₁ * x₂) = (x₁ * x₁) * (x₂ * x₂) := by
      calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
        _ = x₁ * (x₁ * x₂) * x₂ := by rw [hc x₁ hx₁ x₂ hx₂]
        _ = (x₁ * x₁) * (x₂ * x₂) := by group
    rw [hmul]
    exact Subgroup.mul_mem Z (h₁.sq_mem x₁ hx₁) (h₂.sq_mem x₂ hx₂)
  have hcomm' : ∀ x ∈ N₁ ⊔ N₂, ∀ y ∈ N₁ ⊔ N₂,
      x * y = y * x ∨ (ρ (x * y) : Matrix ι ι K) = -(ρ (y * x) : Matrix ι ι K) := by
    intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have hxy : (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := by
      calc (x₁ * x₂) * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
        _ = x₁ * (y₁ * x₂) * y₂ := by rw [(hc y₁ hy₁ x₂ hx₂).symm]
        _ = (x₁ * y₁) * (x₂ * y₂) := by group
    have hyx : (y₁ * y₂) * (x₁ * x₂) = (y₁ * x₁) * (y₂ * x₂) := by
      calc (y₁ * y₂) * (x₁ * x₂) = y₁ * (y₂ * x₁) * x₂ := by group
        _ = y₁ * (x₁ * y₂) * x₂ := by rw [(hc x₁ hx₁ y₂ hy₂).symm]
        _ = (y₁ * x₁) * (y₂ * x₂) := by group
    have hmatxy : (ρ (x₁ * x₂ * (y₁ * y₂)) : Matrix ι ι K) =
        (ρ (x₁ * y₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K) := by
      rw [hxy, map_mul, Units.val_mul]
    have hmatyx : (ρ (y₁ * y₂ * (x₁ * x₂)) : Matrix ι ι K) =
        (ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (y₂ * x₂) : Matrix ι ι K) := by
      rw [hyx, map_mul, Units.val_mul]
    rcases h₁.comm_or_anticomm x₁ hx₁ y₁ hy₁ with h1 | h1 <;>
      rcases h₂.comm_or_anticomm x₂ hx₂ y₂ hy₂ with h2 | h2
    · left
      calc (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := hxy
        _ = (y₁ * x₁) * (y₂ * x₂) := by rw [h1, h2]
        _ = (y₁ * y₂) * (x₁ * x₂) := hyx.symm
    · right
      have h1u : ρ (x₁ * y₁) = ρ (y₁ * x₁) := by rw [h1]
      calc (ρ (x₁ * x₂ * (y₁ * y₂)) : Matrix ι ι K)
          = (ρ (x₁ * y₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K) := hmatxy
        _ = (ρ (x₁ * y₁) : Matrix ι ι K) * -(ρ (y₂ * x₂) : Matrix ι ι K) := by rw [h2]
        _ = -((ρ (x₁ * y₁) : Matrix ι ι K) * (ρ (y₂ * x₂) : Matrix ι ι K)) := by
              rw [mul_neg]
        _ = -((ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (y₂ * x₂) : Matrix ι ι K)) := by rw [h1u]
        _ = -(ρ (y₁ * y₂ * (x₁ * x₂)) : Matrix ι ι K) := by rw [hmatyx]
    · right
      have h2u : ρ (x₂ * y₂) = ρ (y₂ * x₂) := by rw [h2]
      calc (ρ (x₁ * x₂ * (y₁ * y₂)) : Matrix ι ι K)
          = (ρ (x₁ * y₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K) := hmatxy
        _ = -(ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K) := by rw [h1]
        _ = -((ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K)) := by
              rw [neg_mul]
        _ = -((ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (y₂ * x₂) : Matrix ι ι K)) := by rw [h2u]
        _ = -(ρ (y₁ * y₂ * (x₁ * x₂)) : Matrix ι ι K) := by rw [hmatyx]
    · left
      have h1u : ρ (x₁ * y₁) = -(ρ (y₁ * x₁) : Matrix ι ι K) := h1
      have h2u : ρ (x₂ * y₂) = -(ρ (y₂ * x₂) : Matrix ι ι K) := h2
      apply hρ
      have hmat : (ρ ((x₁ * x₂) * (y₁ * y₂)) : Matrix ι ι K) =
          (ρ ((y₁ * y₂) * (x₁ * x₂)) : Matrix ι ι K) := by
        calc (ρ ((x₁ * x₂) * (y₁ * y₂)) : Matrix ι ι K)
            = (ρ (x₁ * x₂ * (y₁ * y₂)) : Matrix ι ι K) := rfl
          _ = (ρ (x₁ * y₁) : Matrix ι ι K) * (ρ (x₂ * y₂) : Matrix ι ι K) := hmatxy
          _ = (-(ρ (y₁ * x₁) : Matrix ι ι K)) * (-(ρ (y₂ * x₂) : Matrix ι ι K)) := by
                rw [h1u, h2u]
          _ = (ρ (y₁ * x₁) : Matrix ι ι K) * (ρ (y₂ * x₂) : Matrix ι ι K) := by
                rw [neg_mul_neg]
          _ = (ρ (y₁ * y₂ * (x₁ * x₂)) : Matrix ι ι K) := hmatyx.symm
          _ = (ρ ((y₁ * y₂) * (x₁ * x₂)) : Matrix ι ι K) := rfl
      exact Units.ext hmat
  have hcenter : ∀ x ∈ N₁ ⊔ N₂, (∀ y ∈ N₁ ⊔ N₂, x * y = y * x) → x ∈ Z := by
    intro x hx hxc
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hx₁Z : x₁ ∈ Z := by
      refine h₁.mem_of_comm x₁ hx₁ ?_
      intro y hy
      have h1' : (x₁ * x₂) * y = y * (x₁ * x₂) := hxc y (Subgroup.mem_sup_left hy)
      have h2' : x₂ * y = y * x₂ := (hc y hy x₂ hx₂).symm
      have key : (x₁ * y) * x₂ = (y * x₁) * x₂ := by
        calc (x₁ * y) * x₂ = x₁ * (y * x₂) := by group
          _ = x₁ * (x₂ * y) := by rw [← h2']
          _ = (x₁ * x₂) * y := by group
          _ = y * (x₁ * x₂) := h1'
          _ = (y * x₁) * x₂ := by group
      exact mul_right_cancel key
    have hx₂Z : x₂ ∈ Z := by
      refine h₂.mem_of_comm x₂ hx₂ ?_
      intro y hy
      have h1' : x₁ * y = y * x₁ := hc x₁ hx₁ y hy
      have h2' : (x₁ * x₂) * y = y * (x₁ * x₂) := hxc y (Subgroup.mem_sup_right hy)
      have key : x₁ * (x₂ * y) = x₁ * (y * x₂) := by
        calc x₁ * (x₂ * y) = (x₁ * x₂) * y := by group
          _ = y * (x₁ * x₂) := h2'
          _ = (y * x₁) * x₂ := by group
          _ = (x₁ * y) * x₂ := by rw [← h1']
          _ = x₁ * (y * x₂) := by group
      exact mul_left_cancel key
    exact Subgroup.mul_mem Z hx₁Z hx₂Z
  refine ⟨⟨Subgroup.sup_normal N₁ N₂, le_trans h₁.scalars_le le_sup_left, hsq, hcomm', hcenter⟩, ?_⟩
  have hcard := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute (C := N₁) (D := N₂) hc
  rw [hinf] at hcard
  exact hcard

private theorem isSolvable_of_two_five [Finite Γ]
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) :
    Group.IsSolvable Γ := by
  have hne : Nat.card Γ ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hdvd : Nat.card Γ ∣ 10 ^ Nat.card Γ := by
    rw [Nat.dvd_pow_self_iff hne (by norm_num : (10 : ℕ) ≠ 0)]
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ Nat.card Γ := Nat.dvd_of_mem_primeFactors hp
    have hp10 : (10 : ℕ) ≠ 0 := by norm_num
    rcases hΓ p hp' hpdvd with rfl | rfl
    · exact Nat.Prime.mem_primeFactors Nat.prime_two (by norm_num) hp10
    · exact Nat.Prime.mem_primeFactors Nat.prime_five (by norm_num) hp10
  have hdvd' : Nat.card Γ ∣ 2 ^ Nat.card Γ * 5 ^ Nat.card Γ := by
    refine hdvd.trans ?_
    rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_five hdvd'

omit [DecidableEq ι] in
private theorem card_cast_ne_zero (hK : ringChar K ≠ 2) (hι : Fintype.card ι = 4) :
    (Fintype.card ι : K) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [hι]
  have h4 : ((4 : ℕ) : K) = ((2 : ℕ) : K) * ((2 : ℕ) : K) := by norm_num
  rw [h4]
  exact mul_ne_zero h2 h2

private theorem card_lower_of_isQuatType [Finite Γ] (ρ : Γ →* GL ι K)
    (hρ : Function.Injective ρ)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥)
    {N : Subgroup Γ} (hN : IsQuatType ρ N)
    (hlt : (StatedScalars ι K).comap ρ < N) :
    4 * Nat.card ((StatedScalars ι K).comap ρ) ≤ Nat.card N := by
  classical
  let Z := (StatedScalars ι K).comap ρ
  have hZ2 : IsPGroup 2 Z := isPGroup_two_scalars ρ hρ hΓ hO5
  have : N.Normal := hN.normal
  have hN2 : IsPGroup 2 N := isPGroup_two_of_sq_mem ρ hρ hΓ hO5 hN.sq_mem
  have : (Z.subgroupOf N).Normal := Subgroup.normal_subgroupOf
  let Q := N ⧸ Z.subgroupOf N
  have hQ2 : IsPGroup 2 Q := hN2.to_quotient (Z.subgroupOf N)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  obtain ⟨x, hxN, hxZ⟩ := SetLike.exists_of_lt hlt
  have hxcomm : ¬ ∀ y ∈ N, x * y = y * x := by
    intro h
    exact hxZ (hN.mem_of_comm x hxN h)
  push Not at hxcomm
  obtain ⟨y, hyN, hxy⟩ := hxcomm
  let mkq : N → Q := fun n => QuotientGroup.mk (s := Z.subgroupOf N) n
  have hx1 : mkq ⟨x, hxN⟩ ≠ 1 := by
    intro h
    have hmem : (⟨x, hxN⟩ : N) ∈ Z.subgroupOf N := (QuotientGroup.eq_one_iff _).mp h
    exact hxZ (Subgroup.mem_subgroupOf.mp hmem)
  have hy1 : mkq ⟨y, hyN⟩ ≠ 1 := by
    intro h
    have hmem : (⟨y, hyN⟩ : N) ∈ Z.subgroupOf N := (QuotientGroup.eq_one_iff _).mp h
    exact hxy (comap_scalars_commute ρ hρ (Subgroup.mem_subgroupOf.mp hmem) x)
  have hxy1 : mkq ⟨x, hxN⟩ ≠ mkq ⟨y, hyN⟩ := by
    intro h
    have hmem : (⟨x, hxN⟩ : N)⁻¹ * ⟨y, hyN⟩ ∈ Z.subgroupOf N := (QuotientGroup.eq).mp h
    have hz : x⁻¹ * y ∈ Z := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    have hzcomm : x * (x⁻¹ * y) = (x⁻¹ * y) * x := comap_scalars_commute ρ hρ hz x
    have : x * y = y * x := by
      calc x * y = x * (x * (x⁻¹ * y)) := by group
        _ = x * ((x⁻¹ * y) * x) := by rw [hzcomm]
        _ = y * x := by group
    exact hxy this
  have hQ3 : 3 ≤ Nat.card Q := by
    have : Fintype Q := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    have hf : Function.Injective
        (![1, mkq ⟨x, hxN⟩, mkq ⟨y, hyN⟩] : Fin 3 → Q) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := Fintype.card_le_of_injective _ hf
    simpa using this
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> norm_num [hk] at hQ3
    · exact hge
  have hq4 : 4 ≤ Nat.card Q := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2
  have hcardN : Nat.card N = Nat.card Q * Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
    have h2 : Nat.card (Z.subgroupOf N) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv
    rw [h2] at h1
    exact h1
  rw [hcardN]
  exact Nat.mul_le_mul_right (Nat.card Z) hq4

theorem card_eq_of_isQuatType [Finite Γ] (hK : ringChar K ≠ 2) (hι : Fintype.card ι = 4)
    (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (h5 : 5 ∣ Nat.card Γ)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥)
    (hab : ∀ A : Subgroup Γ, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → IsPGroup 2 A →
      A ≤ (StatedScalars ι K).comap ρ)
    {N : Subgroup Γ} (hN : IsQuatType ρ N) (hlt : (StatedScalars ι K).comap ρ < N) :
    Nat.card N = 16 * Nat.card ((StatedScalars ι K).comap ρ) := by
  classical
  let Z := (StatedScalars ι K).comap ρ
  have hZ2 : IsPGroup 2 Z := isPGroup_two_scalars ρ hρ hΓ hO5
  have hι' : (Fintype.card ι : K) ≠ 0 := card_cast_ne_zero hK hι
  have hιne : Nonempty ι := by
    rw [← Fintype.card_pos_iff]
    omega
  have : Nonempty ι := hιne
  have : Nontrivial (Matrix ι ι K) := inferInstance
  have hNn : N.Normal := hN.normal
  have hN2 : IsPGroup 2 N := isPGroup_two_of_sq_mem ρ hρ hΓ hO5 hN.sq_mem
  have hZpos : 0 < Nat.card Z := by
    have : Nonempty Z := ⟨⟨1, Z.one_mem⟩⟩
    exact Nat.card_pos
  have h4N : 4 * Nat.card Z ≤ Nat.card N := card_lower_of_isQuatType ρ hρ hΓ hO5 hN hlt
  have hupper : Nat.card N ≤ 16 * Nat.card Z := by
    have h := card_le_of_isQuatType hK hι' ρ hρ hN
    rwa [hι, show (4 : ℕ) ^ 2 = 16 by norm_num] at h
  have hΓsolv : Group.IsSolvable Γ := isSolvable_of_two_five hΓ
  have : (Z.subgroupOf N).Normal := Subgroup.normal_subgroupOf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNq2 : IsPGroup 2 (N ⧸ Z.subgroupOf N) := hN2.to_quotient (Z.subgroupOf N)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNq2
  have hcardN : Nat.card N = 2 ^ k * Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
    have h2 : Nat.card (Z.subgroupOf N) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv
    rw [h2, hk] at h1
    exact h1
  have hnotsmall : ¬ Nat.card N ≤ 8 * Nat.card Z := by
    intro hsmall
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have : Fintype Γ := Fintype.ofFinite Γ
    obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card (G := Γ) 5
      (by simpa [Nat.card_eq_fintype_card] using h5)
    have hc5 : c ^ 5 = 1 := (orderOf_eq_prime_iff.mp hcord).1
    have hcN : ∀ x ∈ N, c * x * c⁻¹ ∈ N :=
      fun x hx => (inferInstance : N.Normal).conj_mem x hx c
    have hcC : ∀ x ∈ N, c * x = x * c :=
      commute_of_pow_five hlt.le (fun z hz => comap_scalars_commute ρ hρ hz) hZ2 hN.sq_mem
        hsmall hc5 hcN
    let X := Subgroup.centralizer (N : Set Γ)
    have hXn : X.Normal := Subgroup.normal_centralizer
    have hZX : Z ≤ X := by
      intro z hz
      show ∀ y ∈ (N : Set Γ), y * z = z * y
      intro y hy
      exact comap_scalars_commute ρ hρ hz y
    have hcX : c ∈ X := by
      show ∀ y ∈ (N : Set Γ), y * c = c * y
      intro y hy
      exact (hcC y hy).symm
    have hcZ : c ∉ Z := by
      intro hcZ
      obtain ⟨m, hm⟩ := IsPGroup.exists_orderOf_dvd_pow hZ2 ⟨c, hcZ⟩
      rw [Subgroup.orderOf_mk c hcZ, hcord] at hm
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hm
      norm_num at this
    have hZltX : Z < X := by
      refine lt_of_le_of_ne hZX ?_
      intro h
      exact hcZ (by rwa [← h] at hcX)
    have hZn : Z.Normal := comap_scalars_normal ρ
    obtain ⟨M, hMnormal, hZltM, hMleX, r, hr, hpowM, hcommM⟩ :=
      exists_normal_elementary_of_lt hΓsolv (Z := Z) (X := X) hZltX
    have hMn : M.Normal := hMnormal
    have hM : IsQuatType ρ M :=
      isQuatType_of_elementary hK ρ hρ hΓ hO5 hab hZltM hr hpowM hcommM
    have h4M : 4 * Nat.card Z ≤ Nat.card M :=
      card_lower_of_isQuatType ρ hρ hΓ hO5 hM hZltM
    have hcommute : ∀ x ∈ N, ∀ y ∈ M, x * y = y * x := by
      intro x hx y hy
      exact Subgroup.mem_centralizer_iff.mp (hMleX hy) x hx
    have hsup := isQuatType_sup ρ hρ hN hM hcommute
    have hsupUpper : Nat.card (N ⊔ M : Subgroup Γ) ≤ 16 * Nat.card Z := by
      have h := card_le_of_isQuatType hK hι' ρ hρ hsup.1
      rwa [hι, show (4 : ℕ) ^ 2 = 16 by norm_num] at h
    have hsupZ : Nat.card (N ⊔ M : Subgroup Γ) * Nat.card Z = Nat.card N * Nat.card M :=
      hsup.2
    have hprod : Nat.card N * Nat.card M = 16 * (Nat.card Z * Nat.card Z) := by
      have hupper2 : Nat.card N * Nat.card M ≤ 16 * (Nat.card Z * Nat.card Z) := by
        calc Nat.card N * Nat.card M = Nat.card (N ⊔ M : Subgroup Γ) * Nat.card Z := hsupZ.symm
          _ ≤ (16 * Nat.card Z) * Nat.card Z :=
              Nat.mul_le_mul_right (Nat.card Z) hsupUpper
          _ = 16 * (Nat.card Z * Nat.card Z) := by ring
      have hlower2 : 16 * (Nat.card Z * Nat.card Z) ≤ Nat.card N * Nat.card M := by
        have hmul : (4 * Nat.card Z) * (4 * Nat.card Z) ≤ Nat.card N * Nat.card M :=
          Nat.mul_le_mul h4N h4M
        calc 16 * (Nat.card Z * Nat.card Z) = (4 * Nat.card Z) * (4 * Nat.card Z) := by ring
          _ ≤ Nat.card N * Nat.card M := hmul
      exact le_antisymm hupper2 hlower2
    have hMle : Nat.card M ≤ 4 * Nat.card Z := by
      have h1 : 4 * Nat.card Z * Nat.card M ≤ Nat.card N * Nat.card M :=
        Nat.mul_le_mul_right (Nat.card M) h4N
      have h2 : Nat.card N * Nat.card M = (4 * Nat.card Z) * (4 * Nat.card Z) := by
        rw [hprod]
        ring
      have h3 : 4 * Nat.card Z * Nat.card M ≤ 4 * Nat.card Z * (4 * Nat.card Z) := by
        calc 4 * Nat.card Z * Nat.card M ≤ Nat.card N * Nat.card M := h1
          _ = 4 * Nat.card Z * (4 * Nat.card Z) := h2
      exact Nat.le_of_mul_le_mul_left h3 (Nat.mul_pos (by norm_num) hZpos)
    have hMle8 : Nat.card M ≤ 8 * Nat.card Z :=
      hMle.trans (Nat.mul_le_mul_right (Nat.card Z) (by norm_num : 4 ≤ 8))
    have hcM : ∀ x ∈ M, c * x = x * c :=
      commute_of_pow_five hM.scalars_le (fun z hz => comap_scalars_commute ρ hρ hz) hZ2
        hM.sq_mem hMle8 hc5 (fun x hx => hMnormal.conj_mem x hx c)
    have hcNM : ∀ x ∈ (N ⊔ M : Subgroup Γ), c * x = x * c := by
      intro x hx
      obtain ⟨n, hn, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      calc c * (n * m) = (c * n) * m := by group
        _ = (n * c) * m := by rw [hcC n hn]
        _ = n * (c * m) := by group
        _ = n * (m * c) := by rw [hcM m hm]
        _ = (n * m) * c := by group
    have hsupcard : Nat.card (N ⊔ M : Subgroup Γ) = 16 * Nat.card Z := by
      have hlower : (16 * Nat.card Z) * Nat.card Z ≤
          Nat.card (N ⊔ M : Subgroup Γ) * Nat.card Z := by
        calc (16 * Nat.card Z) * Nat.card Z = 16 * (Nat.card Z * Nat.card Z) := by ring
          _ = Nat.card N * Nat.card M := hprod.symm
          _ = Nat.card (N ⊔ M : Subgroup Γ) * Nat.card Z := hsupZ.symm
          _ ≤ Nat.card (N ⊔ M : Subgroup Γ) * Nat.card Z := le_rfl
      have hge : 16 * Nat.card Z ≤ Nat.card (N ⊔ M : Subgroup Γ) :=
        Nat.le_of_mul_le_mul_right hlower hZpos
      exact le_antisymm hsupUpper hge
    have hsupcard' : Nat.card (N ⊔ M : Subgroup Γ) = Fintype.card ι ^ 2 * Nat.card Z := by
      rw [hsupcard, hι]
      norm_num
    have hspan : Submodule.span K (Set.range fun x : (N ⊔ M : Subgroup Γ) => (ρ x : Matrix ι ι K)) = ⊤ :=
      span_eq_top_of_isQuatType hK hι' ρ hρ hsup.1 hsupcard'
    have hcommspan : ∀ s ∈ Set.range (fun x : (N ⊔ M : Subgroup Γ) => (ρ x : Matrix ι ι K)),
        (ρ c : Matrix ι ι K) * s = s * (ρ c : Matrix ι ι K) := by
      rintro s ⟨x, rfl⟩
      have hxc : c * (x : Γ) = (x : Γ) * c := hcNM x x.2
      have hunit : ρ c * ρ x = ρ x * ρ c := by
        rw [← map_mul, ← map_mul, hxc]
      have := congrArg (fun w : GL ι K => (w : Matrix ι ι K)) hunit
      simpa using this
    have hscalar : (ρ c : Matrix ι ι K) ∈ Set.range (Matrix.scalar ι) :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.mem_range_scalar_of_commute_span
        (ρ c) _ hspan hcommspan
    obtain ⟨a, ha⟩ := hscalar
    have ha0 : a ≠ 0 := by
      intro h0
      have hzero : (ρ c : Matrix ι ι K) = 0 := by
        rw [← ha, h0]
        ext i j
        simp [Matrix.scalar_apply]
      exact Units.ne_zero (ρ c) hzero
    have hmemScalars : ρ c ∈ StatedScalars ι K := by
      refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      exact ha
    exact hcZ (Subgroup.mem_comap.mpr hmemScalars)
  have hq4 : 4 ≤ 2 ^ k := by
    have h : 4 * Nat.card Z ≤ 2 ^ k * Nat.card Z := by
      rw [← hcardN]
      exact h4N
    exact Nat.le_of_mul_le_mul_right h hZpos
  have hq8 : 8 < 2 ^ k := by
    have h : 8 * Nat.card Z < 2 ^ k * Nat.card Z := by
      rw [← hcardN]
      exact Nat.lt_of_not_ge hnotsmall
    exact Nat.lt_of_mul_lt_mul_right h
  have hq16 : 2 ^ k ≤ 16 := by
    have h : 2 ^ k * Nat.card Z ≤ 16 * Nat.card Z := by
      rw [← hcardN]
      exact hupper
    exact Nat.le_of_mul_le_mul_right h hZpos
  have hk4 : k = 4 := by
    have hk_le : k ≤ 4 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hq16)
    have hk_ge : 3 < k := by
      have h8 : 2 ^ 3 < 2 ^ k := by simpa using hq8
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h8
    omega
  rw [hcardN, hk4]
  norm_num
  rfl

theorem exists_isQuatType [Finite Γ] (hK : ringChar K ≠ 2) (hι : Fintype.card ι = 4)
    (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (h5 : 5 ∣ Nat.card Γ)
    (hO5 : ∀ A : Subgroup Γ, A.Normal → IsPGroup 5 A → A = ⊥)
    (hab : ∀ A : Subgroup Γ, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → IsPGroup 2 A →
      A ≤ (StatedScalars ι K).comap ρ) :
    ∃ N : Subgroup Γ, IsQuatType ρ N ∧
      Nat.card N = 16 * Nat.card ((StatedScalars ι K).comap ρ) := by
  classical
  let Z := (StatedScalars ι K).comap ρ
  have hZn : Z.Normal := comap_scalars_normal ρ
  have hZ2 : IsPGroup 2 Z := isPGroup_two_scalars ρ hρ hΓ hO5
  have hΓsolv : Group.IsSolvable Γ := isSolvable_of_two_five hΓ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card (G := Γ) 5
    (by simpa [Nat.card_eq_fintype_card] using h5)
  have hcZ : c ∉ Z := by
    intro hcZ
    obtain ⟨m, hm⟩ := IsPGroup.exists_orderOf_dvd_pow hZ2 ⟨c, hcZ⟩
    rw [Subgroup.orderOf_mk c hcZ, hcord] at hm
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hm
    norm_num at this
  have hlt : Z < (⊤ : Subgroup Γ) := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    exact hcZ (by rw [h]; exact Subgroup.mem_top c)
  obtain ⟨M, hMnormal, hZltM, hMleTop, r, hr, hpowM, hcommM⟩ :=
    exists_normal_elementary_of_lt hΓsolv (Z := Z) (X := (⊤ : Subgroup Γ)) hlt
  have hMn : M.Normal := hMnormal
  have hM : IsQuatType ρ M :=
    isQuatType_of_elementary hK ρ hρ hΓ hO5 hab hZltM hr hpowM hcommM
  exact ⟨M, hM, card_eq_of_isQuatType hK hι ρ hρ hΓ h5 hO5 hab hM hZltM⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

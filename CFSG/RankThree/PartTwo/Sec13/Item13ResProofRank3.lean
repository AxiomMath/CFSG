module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG

section Central

variable {R : Type*} [Group R] {z : R}

omit [Group R] in
theorem pow_three_of_mem_zpowers [Group R] (hz3 : z ^ 3 = 1) {w : R}
    (hw : w ∈ Subgroup.zpowers z) : w ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]

theorem mul_pow_three_of_central (hzZ : z ∈ Subgroup.center R) (hz3 : z ^ 3 = 1)
    (hcomm : ∀ x y : R, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) (x y : R) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  obtain ⟨w, hw⟩ : ∃ w : R, w = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hwz : w ∈ Subgroup.zpowers z := hw ▸ hcomm y x
  have hwc : ∀ g : R, g * w = w * g := fun g => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    exact ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzZ k)) g)
  have hw3 : w ^ 3 = 1 := pow_three_of_mem_zpowers hz3 hwz
  have hyx : y * x = w * (x * y) := by rw [hw]; group
  have hmove : ∀ a b : R, a * (w * b) = w * (a * b) := fun a b => by
    rw [← mul_assoc, hwc a, mul_assoc]
  have hswap : ∀ Q : R, y * (x * Q) = w * (x * (y * Q)) := fun Q => by
    rw [← mul_assoc, hyx, mul_assoc, mul_assoc]
  have hswap1 : y * (x * y) = w * (x * (y * y)) := hswap y
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hswap1]
  simp only [hmove]
  rw [hswap]
  simp only [hmove]
  rw [hswap]
  simp only [hmove]
  have h3 : ∀ P : R, w * (w * (w * P)) = P := fun P => by
    rw [← mul_assoc, ← mul_assoc, ← pow_three', hw3, one_mul]
  rw [h3]

theorem commutator_mul_right_of_central (hzZ : z ∈ Subgroup.center R)
    (hcomm : ∀ x y : R, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) (x y₁ y₂ : R) :
    x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
      (x * y₁ * x⁻¹ * y₁⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) := by
  set w := x * y₂ * x⁻¹ * y₂⁻¹ with hw
  have hwz : w ∈ Subgroup.zpowers z := hcomm x y₂
  have hwc : ∀ g : R, g * w = w * g := fun g => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    exact ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzZ k)) g)
  calc x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ = x * y₁ * x⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹ := by
        group
    _ = x * y₁ * x⁻¹ * w * y₁⁻¹ := by rw [← hw]
    _ = x * y₁ * x⁻¹ * (w * y₁⁻¹) := by rw [mul_assoc]
    _ = x * y₁ * x⁻¹ * (y₁⁻¹ * w) := by rw [hwc]
    _ = (x * y₁ * x⁻¹ * y₁⁻¹) * w := by group

variable [Finite R]

theorem card_le_eightyOne_of_central (hzZ : z ∈ Subgroup.center R) (hz3 : z ^ 3 = 1)
    (hcube : ∀ x : R, x ^ 3 ∈ Subgroup.zpowers z)
    (hcomm : ∀ x y : R, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z)
    (hab : ∀ S : Subgroup R, (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) → (∀ x ∈ S, x ^ 3 = 1) →
      Nat.card S ≤ 9) :
    Nat.card R ≤ 81 := by
  classical
  by_contra hlt
  push Not at hlt
  have hZ3 : Nat.card (Subgroup.zpowers z) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hz3
  have hzc : ∀ w ∈ Subgroup.zpowers z, ∀ g : R, g * w = w * g := fun w hw g => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hk]
    exact ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzZ k)) g)
  have hz1 : z ≠ 1 := by
    rintro rfl
    have htop := hab ⊤ (fun a _ b _ => by
        have h1 := hcomm a b
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [h1, one_mul])
      (fun a _ => by
        have h1 := hcube a
        rwa [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1)
    rw [Subgroup.card_top] at htop
    omega
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  let κ : R →* R :=
    { toFun := fun x => x ^ 3
      map_one' := one_pow 3
      map_mul' := mul_pow_three_of_central hzZ hz3 hcomm }
  have hκr : κ.range ≤ Subgroup.zpowers z := by
    rintro _ ⟨x, rfl⟩
    exact hcube x
  have hR₁ : 27 < Nat.card κ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range κ
    have h2 : Nat.card κ.range ≤ 3 := (Subgroup.card_le_of_le hκr).trans hZ3
    by_contra hle
    push Not at hle
    have : Nat.card κ.ker * Nat.card κ.range ≤ 27 * 3 := Nat.mul_le_mul hle h2
    omega
  have hmemR₁ : ∀ x : R, x ∈ κ.ker ↔ x ^ 3 = 1 := fun x => MonoidHom.mem_ker
  obtain ⟨x, hxR₁, hxz⟩ : ∃ x ∈ κ.ker, x ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have := (Subgroup.card_le_of_le hall).trans hZ3
    omega
  have hx3 : x ^ 3 = 1 := (hmemR₁ x).mp hxR₁
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  let μ : κ.ker →* R :=
    { toFun := fun y => x * (y : R) * x⁻¹ * (y : R)⁻¹
      map_one' := by simp
      map_mul' := fun y₁ y₂ => by
        simp only [Subgroup.coe_mul]
        exact commutator_mul_right_of_central hzZ hcomm x y₁ y₂ }
  have hμr : μ.range ≤ Subgroup.zpowers z := by
    rintro _ ⟨y, rfl⟩
    exact hcomm x y
  have hC : 9 < Nat.card μ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range μ
    have h2 : Nat.card μ.range ≤ 3 := (Subgroup.card_le_of_le hμr).trans hZ3
    by_contra hle
    push Not at hle
    have : Nat.card μ.ker * Nat.card μ.range ≤ 9 * 3 := Nat.mul_le_mul hle h2
    omega
  have hmemC : ∀ y : κ.ker, y ∈ μ.ker → x * (y : R) = (y : R) * x := by
    intro y hy
    have h : x * (y : R) * x⁻¹ * (y : R)⁻¹ = 1 := MonoidHom.mem_ker.mp hy
    calc x * (y : R) = x * (y : R) * x⁻¹ * (y : R)⁻¹ * ((y : R) * x) := by group
      _ = (y : R) * x := by rw [h, one_mul]
  set T : Subgroup R := Subgroup.zpowers x ⊔ Subgroup.zpowers z with hT
  have hxzc : x * z = z * x := hzc z (Subgroup.mem_zpowers z) x
  have hTe : CFSG.Assembly.IsElemAbelian 3 T := isElemAbelian_zpowers_sup hx3 hz3 hxzc
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers z = ⊥ := by
    have hdvd3 : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers z : Subgroup R) ∣ 3 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers x ⊓ Subgroup.zpowers z ≤ Subgroup.zpowers x)
      rwa [Nat.card_zpowers, hxo] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers z = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hxo])
      have hxmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers z := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxz hxmem.2
  have hT9 : Nat.card T = 9 := by
    have hcz : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers z, a * b = b * a :=
      fun a _ b hb => hzc b hb a
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcz).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hxo, hzo] at h
    rw [hT, h]
  obtain ⟨y, hyC, hyT⟩ : ∃ y : κ.ker, y ∈ μ.ker ∧ (y : R) ∉ T := by
    by_contra hall
    push Not at hall
    have hle : μ.ker.map κ.ker.subtype ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      exact hall y hy
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective κ.ker.subtype_injective, hT9] at this
    omega
  have hy3 : (y : R) ^ 3 = 1 := (hmemR₁ y).mp y.2
  have hxy : x * (y : R) = (y : R) * x := hmemC y hyC
  have hyc : ∀ a ∈ T, ∀ b ∈ Subgroup.zpowers (y : R), a * b = b * a := by
    have hTC : T ≤ Subgroup.centralizer ({(y : R)} : Set R) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (hzc z (Subgroup.mem_zpowers z) (y : R)).symm
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h1 : a * (y : R) = (y : R) * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hTC ha)
    exact (Commute.zpow_right h1 k).eq
  set S : Subgroup R := T ⊔ Subgroup.zpowers (y : R) with hS
  have hSe : CFSG.Assembly.IsElemAbelian 3 S :=
    isElemAbelian_sup hTe (isElemAbelian_zpowers hy3) hyc
  have hS9 := hab S (fun a ha b hb => by
      have := hSe.1
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : S) ⟨b, hb⟩))
    (fun a ha => hSe.2 a ha)
  have hTS : T < S := lt_of_le_of_ne le_sup_left (fun h => hyT (by
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (y : R))))
  have hdvd : Nat.card T ∣ Nat.card S := Subgroup.card_dvd_of_le hTS.le
  have hne : Nat.card T ≠ Nat.card S := fun h =>
    hTS.ne (Subgroup.eq_of_le_of_card_ge hTS.le h.symm.le)
  rw [hT9] at hdvd hne
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have := Nat.le_of_dvd hSpos hdvd
  omega

end Central

theorem pRank_three_quotient_center_le_of_isSLThreePi {X : Type} [Group X] [Finite X]
    (hX : Sec4.IsSLThreePi X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : Nat.card (Subgroup.center X) = 3 := card_center_of_isSLThreePi hX
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 (by rw [hZ3])
  have hzZ : (z : X) ∈ Subgroup.center X := z.2
  have hzo : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hz3 : (z : X) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hZeq : Subgroup.center X = Subgroup.zpowers (z : X) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [hZ3, Nat.card_zpowers, hzo]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun Ebar _ hEbar => ?_
  set ρ := QuotientGroup.mk' (Subgroup.center X) with hρ
  set R : Subgroup X := Ebar.comap ρ with hR
  have hRcard : Nat.card R = 3 * Nat.card Ebar := by
    have h := QuotientGroup.card_preimage_mk (Subgroup.center X) (Ebar : Set (X ⧸ _))
    rw [hZ3] at h
    exact h
  have hmemZ : ∀ x : X, ρ x = 1 → x ∈ Subgroup.zpowers (z : X) := fun x hx => by
    rw [← hZeq]
    exact (QuotientGroup.eq_one_iff x).mp hx
  have hR81 : Nat.card R ≤ 81 := by
    refine card_le_eightyOne_of_central (R := R) (z := ⟨z, ?_⟩) ?_ ?_ ?_ ?_ ?_
    · change ρ (z : X) ∈ Ebar
      have h1 : ρ (z : X) = 1 := by
        rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hzZ
      rw [h1]
      exact Ebar.one_mem
    · rw [Subgroup.mem_center_iff]
      intro r
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzZ r)
    · exact Subtype.ext (by simpa using hz3)
    · intro r
      have h1 : ρ ((r : X) ^ 3) = 1 := by
        rw [map_pow]
        exact hEbar.2 _ r.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmemZ _ h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      simpa using hk
    · intro r s
      have hc : ρ (r : X) * ρ (s : X) = ρ (s : X) * ρ (r : X) := by
        have := hEbar.1
        exact congrArg Subtype.val (mul_comm' (⟨_, r.2⟩ : Ebar) ⟨_, s.2⟩)
      have h1 : ρ ((r : X) * s * (r : X)⁻¹ * (s : X)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmemZ _ h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      simpa using hk
    · intro S hSc hS3
      have h := Sec12.Item128StepsProof.card_le_nine_of_isSLThreePi hX (S.map (R.subtype))
        (by
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          exact congrArg Subtype.val (hSc a ha b hb))
        (by
          rintro _ ⟨a, ha, rfl⟩
          exact congrArg Subtype.val (hS3 a ha))
      rwa [Subgroup.card_map_of_injective R.subtype_injective] at h
  have : Nat.card Ebar ≤ 27 := by omega
  simpa using this

end CFSG.RankThree.PartTwo.Sec13.ResProof

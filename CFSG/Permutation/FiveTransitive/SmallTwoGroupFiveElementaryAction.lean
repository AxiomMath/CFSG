module

public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism

public section

namespace CFSG

namespace FiveTransitive.SmallTwoGroupFiveElementaryAction

open MulAction

theorem fixed_eq_one
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q)
    (q : Q) (hq : ∀ a : A, a • q = q) : q = 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h16 := TwoGroupFiveAutomorphism.card_eq_sixteen_of_nontrivial_action
    A Q hA hQ hcard hmove
  let C := FixedPoints.subgroup A Q
  have hmod : 16 % 5 = Nat.card C % 5 := by
    have h := hA.card_modEq_card_fixedPoints Q
    change Nat.card Q % 5 = Nat.card C % 5 at h
    rwa [h16] at h
  have hd : Nat.card C ∣ 16 := h16 ▸ Subgroup.card_subgroup_dvd_card C
  have hle : Nat.card C ≤ 16 := by
    rw [← h16]
    exact Nat.card_le_card_of_injective (fun c : C => c.val) Subtype.val_injective
  have hne : Nat.card C ≠ 16 := by
    intro hc
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (hc.trans h16.symm)
    obtain ⟨a, x, hx⟩ := hmove
    have hxc : x ∈ C := htop ▸ Subgroup.mem_top x
    exact hx (hxc a)
  have hc1 : Nat.card C = 1 := by
    interval_cases h : Nat.card C <;> norm_num at *
  have hc : C = ⊥ := Subgroup.card_eq_one.mp hc1
  have hqc : q ∈ C := hq
  rwa [hc, Subgroup.mem_bot] at hqc

theorem invariant_eq_top
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q)
    (H : Subgroup Q) (hH : H ≠ ⊥)
    (hstable : ∀ (a : A) (q : Q), q ∈ H → a • q ∈ H) : H = ⊤ := by
  classical
  let _ : MulDistribMulAction A H :=
    { smul := fun a q => ⟨a • q.val, hstable a q.val q.property⟩
      one_smul := fun q => Subtype.ext (one_smul A q.val)
      mul_smul := fun a b q => Subtype.ext (mul_smul a b q.val)
      smul_one := fun a => Subtype.ext (smul_one a)
      smul_mul := fun a q r => Subtype.ext (smul_mul' a q.val r.val) }
  let _ : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨q, hq⟩ := exists_ne (1 : H)
  have hmoveH : ∃ a : A, ∃ q : H, a • q ≠ q := by
    by_contra hn
    push Not at hn
    have he : q.val = 1 := fixed_eq_one hA hQ hcard hmove q.val
      (fun a => congrArg Subtype.val (hn a q))
    exact hq (Subtype.ext he)
  have hle : Nat.card H ≤ 16 := (Nat.card_le_card_of_injective
    (fun q : H => q.val) Subtype.val_injective).trans hcard
  have h16 := TwoGroupFiveAutomorphism.card_eq_sixteen_of_nontrivial_action
    A H hA (hQ.to_subgroup H) hle hmoveH
  have hQ16 := TwoGroupFiveAutomorphism.card_eq_sixteen_of_nontrivial_action
    A Q hA hQ hcard hmove
  exact Subgroup.eq_top_of_card_eq H (h16.trans hQ16.symm)

theorem elementary
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q) :
    Nat.card Q = 16 ∧ IsMulCommutative Q ∧ ∀ q : Q, q ^ 2 = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 := TwoGroupFiveAutomorphism.card_eq_sixteen_of_nontrivial_action
    A Q hA hQ hcard hmove
  let _ : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hcenter : Subgroup.center Q = ⊤ := by
    apply invariant_eq_top hA hQ hcard hmove (Subgroup.center Q)
      (ne_of_gt hQ.bot_lt_center)
    intro a q hq
    apply Subgroup.mem_center_iff.mpr
    intro g
    calc
      g * (a • q) = a • ((a⁻¹ • g) * q) := by rw [smul_mul', smul_inv_smul]
      _ = a • (q * (a⁻¹ • g)) := congrArg (fun x : Q => a • x)
        ((Subgroup.mem_center_iff.mp hq) (a⁻¹ • g))
      _ = (a • q) * g := by rw [smul_mul', smul_inv_smul]
  have hcomm : IsMulCommutative Q := Subgroup.center_eq_top_iff.mp hcenter
  let _ : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := isMulCommutative_iff.mp hcomm }
  let K : Subgroup Q := (powMonoidHom 2).ker
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [h16]; decide)
  have hu2 : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
  have hune : u ≠ 1 := by intro he; rw [he, orderOf_one] at hu; omega
  have hK : K ≠ ⊥ := by
    intro he
    have hum : u ∈ K := hu2
    rw [he, Subgroup.mem_bot] at hum
    exact hune hum
  have hKtop : K = ⊤ := by
    apply invariant_eq_top hA hQ hcard hmove K hK
    intro a q hq
    change (a • q) ^ 2 = 1
    change q ^ 2 = 1 at hq
    rw [← smul_pow', hq, smul_one]
  refine ⟨h16, hcomm, ?_⟩
  intro q
  have hq : q ∈ K := hKtop ▸ Subgroup.mem_top q
  exact hq

end FiveTransitive.SmallTwoGroupFiveElementaryAction

end CFSG

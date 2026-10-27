module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res6ProofHJ
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2InvolNine
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace Res162Seven

variable {X : Type} [Group X]

theorem mul_conj_mul_inv (σ : MulAut X) (x : X) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem conj_injective_of_center (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro l hl
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hl) y
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * l = l * y * l⁻¹ * l := by rw [h1]
    _ = l * y := by group

theorem eq_of_commute_conj (hZ : Subgroup.center X = ⊥) {σ : MulAut X} {e : X}
    (h : σ * MulAut.conj e = MulAut.conj e * σ) : σ e = e := by
  apply conj_injective_of_center hZ
  rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]

theorem eq_one_of_commute_conj
    [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (hZ : Subgroup.center X = ⊥)
    {E : Subgroup X} (hE9 : Nat.card E = 9) {y : MulAut X} {k : ℕ} (hy : y ^ 2 ^ k = 1)
    (hEy : ∀ e ∈ E, y * MulAut.conj e = MulAut.conj e * y) : y = 1 := by
  have hfin : Finite (MulAut X) :=
    Finite.of_injective (fun σ : MulAut X => (σ : X → X)) DFunLike.coe_injective
  by_contra hy1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hy1 (orderOf_eq_one_iff.mp (by simpa using hm))
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hτ2 : orderOf (τ : MulAut X) = 2 := by rw [Subgroup.orderOf_coe, hτ]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp τ.2
  have hfix : ∀ e ∈ E, (τ : MulAut X) e = e := by
    intro e he
    refine eq_of_commute_conj hZ ?_
    have hc : Commute y (MulAut.conj e) := hEy e he
    rw [← hj]
    exact (hc.zpow_left j).eq
  have hsq : (τ : MulAut X) ^ 2 = 1 := by
    rw [← hτ2]
    exact pow_orderOf_eq_one _
  have h1 := KFacts.ks152J2InvolNine X hX E hE9 τ hsq hfix
  rw [h1, orderOf_one] at hτ2
  omega

end Res162Seven

open Res162Seven in
theorem ks162J2TwoInner :
    KS162J2TwoInner := by
  intro X _ hX E hE9 P hP2 hEP
  classical
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by
    rw [KFacts.KS14.card_eq_of_j2 hX]
    norm_num)
  have hZ : Subgroup.center X = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 hX
  have hfin : Finite (MulAut X) :=
    Finite.of_injective (fun σ : MulAut X => (σ : X → X)) DFunLike.coe_injective
  set Inn := (MulAut.conj : X →* MulAut X).range with hInn
  have hconjInn : ∀ (σ : MulAut X) (ι : MulAut X), ι ∈ Inn → σ * ι * σ⁻¹ ∈ Inn := by
    rintro σ _ ⟨x, rfl⟩
    exact ⟨σ x, (mul_conj_mul_inv σ x).symm⟩
  intro σ hσ
  by_contra hσI
  set Eb := E.map (MulAut.conj : X →* MulAut X) with hEb
  have hEbInn : Eb ≤ Inn := Subgroup.map_le_range _ _
  set Y := {y : MulAut X // y ∈ P ∧ σ⁻¹ * y ∈ Inn} with hYdef
  have hact : ∀ (e : Eb) (y : Y), (e : MulAut X) * y.1 * (e : MulAut X)⁻¹ ∈ P ∧
      σ⁻¹ * ((e : MulAut X) * y.1 * (e : MulAut X)⁻¹) ∈ Inn := by
    intro e y
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEP e.2) y.1).mp y.2.1, ?_⟩
    have heI : (e : MulAut X) ∈ Inn := hEbInn e.2
    have h1 : σ⁻¹ * (e : MulAut X) * σ⁻¹⁻¹ ∈ Inn := hconjInn σ⁻¹ _ heI
    have e1 : σ⁻¹ * ((e : MulAut X) * y.1 * (e : MulAut X)⁻¹) =
        (σ⁻¹ * (e : MulAut X) * σ⁻¹⁻¹) * (σ⁻¹ * y.1) * (e : MulAut X)⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem h1 y.2.2) (inv_mem heI)
  let _ : MulAction Eb Y :=
    { smul := fun e y => ⟨(e : MulAut X) * y.1 * (e : MulAut X)⁻¹, hact e y⟩
      one_smul := fun y => by
        apply Subtype.ext
        change (1 : MulAut X) * y.1 * (1 : MulAut X)⁻¹ = y.1
        group
      mul_smul := fun e f y => by
        apply Subtype.ext
        change ((e : MulAut X) * f) * y.1 * ((e : MulAut X) * f)⁻¹ =
          (e : MulAut X) * ((f : MulAut X) * y.1 * (f : MulAut X)⁻¹) * (e : MulAut X)⁻¹
        group }
  have hcardY : Nat.card Y = Nat.card (P ⊓ Inn : Subgroup (MulAut X)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨σ⁻¹ * y.1, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hσ) y.2.1, y.2.2⟩⟩
        invFun := fun z => ⟨σ * z.1, mul_mem hσ (Subgroup.mem_inf.mp z.2).1, by
          rw [inv_mul_cancel_left]
          exact (Subgroup.mem_inf.mp z.2).2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hcardY]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP2.to_le inf_le_left)
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hEb3 : IsPGroup 3 Eb := hE3.map _
  have hfinY : Finite Y := Subtype.finite
  obtain ⟨y, hyfix⟩ := hEb3.nonempty_fixed_point_of_prime_not_dvd_card Y hY3
  have hEy : ∀ e ∈ E, y.1 * MulAut.conj e = MulAut.conj e * y.1 := by
    intro e he
    have hmem : MulAut.conj e ∈ Eb := Subgroup.mem_map_of_mem _ he
    have h := congrArg Subtype.val (hyfix ⟨MulAut.conj e, hmem⟩)
    change MulAut.conj e * y.1 * (MulAut.conj e)⁻¹ = y.1 at h
    calc y.1 * MulAut.conj e = (MulAut.conj e * y.1 * (MulAut.conj e)⁻¹) * MulAut.conj e := by
          rw [h]
      _ = MulAut.conj e * y.1 := by group
  obtain ⟨k, hk⟩ := hP2 ⟨y.1, y.2.1⟩
  have hk' : y.1 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hy1 := eq_one_of_commute_conj hX hZ hE9 hk' hEy
  have hyI := y.2.2
  rw [hy1, mul_one] at hyI
  exact hσI (by simpa using inv_mem hyI)

end CFSG.RankThree.PartTwo.Sec16

module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofJ2
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofTwoInner

public section

namespace CFSG.RankThree.PartTwo.Sec17

namespace Proof17Res8

variable {X : Type} [Group X]

theorem index_inner_of_j2
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    (MulAut.conj : X →* MulAut X).range.index = 2 := by
  obtain ⟨e⟩ := hX
  have hcardX : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 ⟨e⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcardX]; norm_num)
  have hZ : Subgroup.center X = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨e⟩
  have hAut : Nat.card (MulAut X) = 1209600 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      (CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model).2.2.2.2.1]
  have hInn : Nat.card (MulAut.conj : X →* MulAut X).range = 604800 := by
    rw [← hcardX]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (Sec16.Res162Seven.conj_injective_of_center hZ)).toEquiv).symm
  have h := (MulAut.conj : X →* MulAut X).range.card_mul_index
  rw [hInn, hAut] at h
  omega

theorem mem_inner_of_odd_pow (hidx : (MulAut.conj : X →* MulAut X).range.index = 2)
    (y : MulAut X) {m : ℕ} (hm : Odd m) (hy : y ^ m ∈ (MulAut.conj : X →* MulAut X).range) :
    y ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨j, rfl⟩ := hm
  have hsq := Subgroup.sq_mem_of_index_two hidx y
  have e : y = ((y ^ 2) ^ j)⁻¹ * y ^ (2 * j + 1) := by
    rw [← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e]
  exact mul_mem (inv_mem (pow_mem hsq j)) hy

end Proof17Res8

open Sec16.Res162Seven in
theorem ks1717J2Inner :
    KS1717J2Inner := by
  intro X _ hX B hB9 Q hQ3 hBQ
  classical
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by
    rw [KFacts.KS14.card_eq_of_j2 hX]
    norm_num)
  have hZ : Subgroup.center X = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 hX
  have hfin : Finite (MulAut X) :=
    Finite.of_injective (fun σ : MulAut X => (σ : X → X)) DFunLike.coe_injective
  set Inn := (MulAut.conj : X →* MulAut X).range with hInn
  have hidx : Inn.index = 2 := Proof17Res8.index_inner_of_j2 hX
  have hconjInn : ∀ (σ : MulAut X) (ι : MulAut X), ι ∈ Inn → σ * ι * σ⁻¹ ∈ Inn := by
    rintro σ _ ⟨x, rfl⟩
    exact ⟨σ x, (mul_conj_mul_inv σ x).symm⟩
  intro σ hσ
  by_contra hσI
  set Bb := B.map (MulAut.conj : X →* MulAut X) with hBb
  have hBbInn : Bb ≤ Inn := Subgroup.map_le_range _ _
  set Y := {y : MulAut X // y ∈ Q ∧ σ⁻¹ * y ∈ Inn} with hYdef
  have hact : ∀ (e : Bb) (y : Y), (e : MulAut X) * y.1 * (e : MulAut X)⁻¹ ∈ Q ∧
      σ⁻¹ * ((e : MulAut X) * y.1 * (e : MulAut X)⁻¹) ∈ Inn := by
    intro e y
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBQ e.2) y.1).mp y.2.1, ?_⟩
    have heI : (e : MulAut X) ∈ Inn := hBbInn e.2
    have h1 : σ⁻¹ * (e : MulAut X) * σ⁻¹⁻¹ ∈ Inn := hconjInn σ⁻¹ _ heI
    have e1 : σ⁻¹ * ((e : MulAut X) * y.1 * (e : MulAut X)⁻¹) =
        (σ⁻¹ * (e : MulAut X) * σ⁻¹⁻¹) * (σ⁻¹ * y.1) * (e : MulAut X)⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem h1 y.2.2) (inv_mem heI)
  let _ : MulAction Bb Y :=
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
  have hcardY : Nat.card Y = Nat.card (Q ⊓ Inn : Subgroup (MulAut X)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨σ⁻¹ * y.1, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hσ) y.2.1, y.2.2⟩⟩
        invFun := fun z => ⟨σ * z.1, mul_mem hσ (Subgroup.mem_inf.mp z.2).1, by
          rw [inv_mul_cancel_left]
          exact (Subgroup.mem_inf.mp z.2).2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hcardY]
    intro h3
    exact hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hBb3 : IsPGroup 3 Bb := hB3.map _
  have hfinY : Finite Y := Subtype.finite
  obtain ⟨y, hyfix⟩ := hBb3.nonempty_fixed_point_of_prime_not_dvd_card Y hY3
  have hBy : ∀ e ∈ B, y.1 * MulAut.conj e = MulAut.conj e * y.1 := by
    intro e he
    have hmem : MulAut.conj e ∈ Bb := Subgroup.mem_map_of_mem _ he
    have h := congrArg Subtype.val (hyfix ⟨MulAut.conj e, hmem⟩)
    change MulAut.conj e * y.1 * (MulAut.conj e)⁻¹ = y.1 at h
    calc y.1 * MulAut.conj e = (MulAut.conj e * y.1 * (MulAut.conj e)⁻¹) * MulAut.conj e := by
          rw [h]
      _ = MulAut.conj e * y.1 := by group
  have hyI : y.1 ∉ Inn := by
    intro hy
    apply hσI
    have h := mul_mem hy (inv_mem y.2.2)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y.1).ne'
  have hz : (y.1 ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hzB : ∀ e ∈ B, y.1 ^ m * MulAut.conj e = MulAut.conj e * y.1 ^ m := fun e he =>
    (Commute.pow_left (hBy e he) m).eq
  have hz1 := eq_one_of_commute_conj hX hZ hB9 hz hzB
  exact hyI (Proof17Res8.mem_inner_of_odd_pow hidx y.1 hm (by rw [hz1]; exact one_mem _))

end CFSG.RankThree.PartTwo.Sec17

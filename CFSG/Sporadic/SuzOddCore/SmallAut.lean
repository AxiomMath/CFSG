module

public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.Sporadic.SuzOddCore.SylowFusion

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem suzT_conj_mem'
    {t : Equiv.Perm (Fin 1782)} (ht : t ∈ suzT) {m : Equiv.Perm (Fin 1782)}
    (hm : m ∈ suzM) : t * m * t⁻¹ ∈ suzM :=
  suzT_conj_mem_suzM ht hm

@[expose] def suzConjT :
    suzT →* MulAut suzM where
  toFun t :=
    { toFun := fun m => ⟨t * m * t⁻¹, suzT_conj_mem' t.2 m.2⟩
      invFun := fun m => ⟨(t : Equiv.Perm (Fin 1782))⁻¹ * m * t, by
        have := suzT_conj_mem' (suzT.inv_mem t.2) m.2
        rwa [inv_inv] at this⟩
      left_inv := fun m => Subtype.ext (by simp [mul_assoc])
      right_inv := fun m => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun m n => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext m
    simp
  map_mul' s t := by
    ext m
    simp [mul_assoc]

theorem suzConjT_apply
    (t : suzT) (m : suzM) :
    ((suzConjT t m : suzM) : Equiv.Perm (Fin 1782)) = t * m * (t : Equiv.Perm (Fin 1782))⁻¹ :=
  rfl

theorem suzConjT_injective :
    Function.Injective suzConjT := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hc : (t : Equiv.Perm (Fin 1782)) ∈
      Subgroup.centralizer (suzM : Set (Equiv.Perm (Fin 1782))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := congrArg (fun α : MulAut suzM => ((α ⟨m, hm⟩ : suzM) : Equiv.Perm (Fin 1782))) ht
    simp only [suzConjT_apply, MulAut.one_apply] at this
    calc m * t = t * m * (t : Equiv.Perm (Fin 1782))⁻¹ * t := by rw [this]
      _ = t * m := by group
  rw [suzM_centralizer, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

theorem card_mulAut_suzM :
    Nat.card (MulAut suzM) = 896690995200 := by
  rw [← Nat.card_congr (MulAut.congr suzTheta).toEquiv, card_mulAut_suzP]

instance :

    Finite (MulAut suzM) := Nat.finite_of_card_ne_zero (by rw [card_mulAut_suzM]; norm_num)

theorem suzConjT_bijective :
    Function.Bijective suzConjT :=
  suzConjT_injective.bijective_of_nat_card_le (by rw [suzT_card, card_mulAut_suzM])

theorem suzConjT_map_suzM :
    (suzM.subgroupOf suzT).map suzConjT = (MulAut.conj : suzM →* MulAut suzM).range := by
  ext α
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    refine ⟨⟨t, ht⟩, ?_⟩
    ext m
    simp [suzConjT_apply, MulAut.conj_apply]
  · rintro ⟨m, rfl⟩
    refine ⟨⟨m, suzM_le_suzT m.2⟩, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact m.2, ?_⟩
    ext n
    simp [suzConjT_apply, MulAut.conj_apply]

theorem suzT_semidirect :
    Subgroup.zpowers suzV ⊓ suzM = ⊥ ∧ suzM ⊔ Subgroup.zpowers suzV = suzT := by
  refine ⟨?_, le_antisymm (sup_le suzM_le_suzT (Subgroup.zpowers_le.2 suzV_mem_suzT)) ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hg, hgM⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_bot]
    rw [zpow_eq_zpow_emod' k (show suzV ^ 2 = 1 by rw [pow_two]; exact suzV_sq)] at hgM ⊢
    have hk : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk with hk | hk
    · rw [hk, zpow_zero]
    · rw [hk, zpow_one] at hgM
      exact absurd hgM suzV_not_mem
  · rw [suzT, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left hg

instance suzM_normal_T_inst :
    (suzM.subgroupOf suzT).Normal := suzM_normal_T

theorem suzT_quot :
    Nonempty (suzT ⧸ suzM.subgroupOf suzT ≃* Multiplicative (ZMod 2)) := by
  have h : Nat.card (suzT ⧸ suzM.subgroupOf suzT) = 2 := by
    rw [← Subgroup.index_eq_card, suzM_index_T]
  exact ⟨mulEquivOfPrimeCardEq h (by simp)⟩

@[expose] def suzEquivM' :
    @MulEquiv Blueprint.NativeSporadic.Suz suzM (@MulOneClass.toMul _
    (@Monoid.toMulOneClass _ (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _ suzGroupStr))))
    _ := suzEquivM

@[expose] def suzConjTSuz :
    suzT →* MulAut Blueprint.NativeSporadic.Suz :=
  let _ : Group Blueprint.NativeSporadic.Suz := suzGroupStr
  (MulAut.congr suzEquivM'.symm).toMonoidHom.comp suzConjT

theorem suzConjTSuz_bijective :
    Function.Bijective suzConjTSuz := by
  let _ : Group Blueprint.NativeSporadic.Suz := suzGroupStr
  exact (MulAut.congr suzEquivM'.symm).bijective.comp suzConjT_bijective

theorem CTUC_Suz_small_full_automorphism_model :
    ValidSchreier smallChain ∧ smallChain.originalSubgroup = suzM ∧
    smallChain.base.toList = [0, 1, 2, 3, 4, 8] ∧
    CFSG.Certificates.Native.rawOrbitSizes 1782 smallStrongArrs smallBaseNat.toArray =
      [1782, 416, 100, 63, 32, 3] ∧
    (∀ d : Fin 1782, ∃ m ∈ suzM, m 0 = d) ∧
    Subgroup.centralizer (suzM : Set (Equiv.Perm (Fin 1782))) = ⊥ ∧
    suzV * suzV = 1 ∧ suzV ≠ 1 ∧ suzV ∉ suzM ∧
    suzM.map (MulAut.conj suzV).toMonoidHom = suzM ∧
    Function.Bijective suzConjT ∧
    (∀ (t : suzT) (m : suzM),
      ((suzConjT t m : suzM) : Equiv.Perm (Fin 1782)) = t * m * (t : Equiv.Perm (Fin 1782))⁻¹) ∧
    (suzM.subgroupOf suzT).map suzConjT = (MulAut.conj : suzM →* MulAut suzM).range ∧
    suzM ≤ suzT ∧ (suzM.subgroupOf suzT).Normal ∧
    Subgroup.zpowers suzV ⊓ suzM = ⊥ ∧ suzM ⊔ Subgroup.zpowers suzV = suzT ∧
    Nat.card suzT = 896690995200 ∧
    Nonempty (suzT ⧸ suzM.subgroupOf suzT ≃* Multiplicative (ZMod 2)) ∧
    Function.Bijective suzConjTSuz ∧
    (∀ (t : suzT) (s : Blueprint.NativeSporadic.Suz),
      suzEquivM (suzConjTSuz t s) = suzConjT t (suzEquivM s)) := by
  refine ⟨smallChain_valid, smallChain_originalSubgroup, smallChain_base_toList,
    smallChain_orbitSizes, suzM_transitive, suzM_centralizer, suzV_sq, suzV_ne_one,
    suzV_not_mem, suzV_conj_eq, suzConjT_bijective, suzConjT_apply, suzConjT_map_suzM,
    suzM_le_suzT, suzM_normal_T, suzT_semidirect.1, suzT_semidirect.2, suzT_card, suzT_quot,
    suzConjTSuz_bijective, fun t s => ?_⟩
  change suzEquivM' (suzEquivM'.symm (suzConjT t (suzEquivM' s))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end CFSG.Sporadic.SuzOddCore

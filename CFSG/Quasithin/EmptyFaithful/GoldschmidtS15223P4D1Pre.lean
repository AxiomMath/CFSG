module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Star
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Ovr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open CFSG.Quasithin.S15223P4.G (exists_mem_inf_of_rank pRank_three_le_two_of_hyp)

namespace CFSG.Quasithin.S15223P4.D1

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem isPGroup_K_inf_M (c : P4Ctx T Mc M H B₀ I X) : IsPGroup 2 ↥(oTwoUpper H ⊓ M) := by
  refine c.setting.qtfe.sylow.1.to_le (fun x hx => ?_)
  have h := c.inputs.hN.eq_inf
  rw [h]
  exact ⟨hx.2, oTwoUpper_le H hx.1⟩

omit [Finite G] in
theorem false_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {e : G} (he : e ∈ Q)
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) : False := by
  obtain ⟨k, hk⟩ := hQ ⟨e, he⟩
  have h2 : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact he1 (C1Pack12.eq_one_of_pow_two_pow_of_pow_three' h2 he3)

theorem exists_mem_orderOf_three (c : P4Ctx T Mc M H B₀ I X) (h3 : 3 ∣ Nat.card ↥X) :
    ∃ e ∈ oTwoUpper H ⊓ X, orderOf e = 3 := by
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  have hne := exists_mem_inf_of_rank (pRank_three_le_two_of_hyp c) c.X_le_I
    (hEK.trans c.K_le_I) (hEK.trans c.K_norm) hE hE9 h3
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨e, ⟨hEK he.1, he.2⟩, ?_⟩
  have he3 : e ^ 3 = 1 := hE.2 e he.1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  exact orderOf_eq_prime he3 he1'

theorem p4N1pre_of (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X)))
    (hnot : ¬ X ≤ Mc) : P4N1pre T Mc M H B₀ I X := by
  obtain ⟨ψ⟩ := exists_quotEquiv hcover c hF e
  have hA : IsSylowTwoOf (sOf152 T Mc M B₀ ⊓ X) X :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp c.comp) c.sylow
  have hAM0 : sOf152 T Mc M B₀ ⊓ X ≤ X ⊓ (Mc ⊓ I) :=
    le_inf inf_le_right (inf_le_left.trans (S_le_inf152 c.inputs))
  have hAMX : sOf152 T Mc M B₀ ⊓ X ≤ X ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans (S_le_T152.trans (T_le_M152 c.setting)))
  have parMX := isMaxParabolic2_inf_M hcover c ψ hF e hpar
  have cardMX := card_isMaxParabolic2 ψ hA hAMX parMX
  have h3X : 3 ∣ Nat.card ↥X := by
    have h1 : 3 ∣ Nat.card ↥(X ⊓ M) := ⟨Nat.card ↥(sOf152 T Mc M B₀ ⊓ X), cardMX⟩
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨e₀, he₀, he₀3⟩ := exists_mem_orderOf_three c h3X
  have he₀M0 : e₀ ∈ X ⊓ (Mc ⊓ I) := ⟨he₀.2, K_le_inf152 c.inputs he₀.1⟩
  have h3M0 : 3 ∣ Nat.card ↥(X ⊓ (Mc ⊓ I)) := by
    rw [← he₀3]
    exact Subgroup.orderOf_dvd_natCard _ he₀M0
  have hM0X : X ⊓ (Mc ⊓ I) ≠ X := fun h => hnot fun x hx => by
    have hx' : x ∈ X ⊓ (Mc ⊓ I) := by rw [h]; exact hx
    exact hx'.2.1
  have cardM0 := card_eq_of_overgroup ψ hA hAM0 inf_le_left hM0X h3M0
  have hne : X ⊓ (Mc ⊓ I) ≠ X ⊓ M := by
    intro heq
    have hKM0 := he₀M0
    rw [heq] at hKM0
    have he3 : e₀ ^ 3 = 1 := by rw [← he₀3]; exact pow_orderOf_eq_one e₀
    have he1 : e₀ ≠ 1 := fun h => by rw [h, orderOf_one] at he₀3; omega
    exact false_of_isPGroup_two (isPGroup_K_inf_M c) ⟨he₀.1, hKM0.2⟩ he3 he1
  exact ⟨hA, hnot, cardM0, cardMX, inf_eq_of_card hAM0 hAMX cardM0 cardMX hne,
    fun y hy hy3 hy1 => exists_inv_mem ψ hA hAMX parMX hy hy3 hy1⟩

end CFSG.Quasithin.S15223P4.D1

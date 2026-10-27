module

public import CFSG.Quasithin.EmptyFaithful.S151cY36
public import CFSG.Quasithin.EmptyFaithful.S151cShapeS3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

section OneAux151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

omit [Finite V] in
theorem commSeries_three_of_two {A : Subgroup (MulAut V)} (h : commSeries A 2 = ⊥) :
    commSeries A 3 = ⊥ := by
  have : commSeries A 3 = commSub (commSeries A 2) A := rfl
  rw [this, h]
  exact commSub_bot_left _

theorem qOf_eq_of_qstar_card_two (hV : ∀ v : V, v ^ 2 = 1) (hr : qhatOf X = (r : WithTop ℚ))
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hA2 : Nat.card A = 2) :
    qOf X = (r : WithTop ℚ) := by
  obtain ⟨r', hr', -, ⟨hArle, hAser⟩, -⟩ := hA
  have hrr : r' = r := by
    have := hr'.symm.trans hr
    exact_mod_cast this
  subst hrr
  obtain ⟨b, hbA, hb1, hbb, rfl⟩ := S152O4.exists_eq_zpowers_of_card_two hA2
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hbb
  have hquad : commSeries (Subgroup.zpowers b) 2 = ⊥ :=
    (isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hV hb2)
  apply le_antisymm
  · exact kq_le_iff.mpr ⟨Subgroup.zpowers b, hArle.1, hquad, hArle.2⟩
  · show (r' : WithTop ℚ) ≤ kq X 2
    refine le_kq_iff.mpr (fun B hB hBq => ?_)
    exact (kq_eq_coe_iff.mp hr).2 B hB (commSeries_three_of_two hBq)

omit [Finite V] in
theorem card_J_nine (hE : IsElemAbelian 3 (fittingOf J)) (hF9 : Nat.card (fittingOf J) = 9)
    (ht : ∃ t ∈ J, orderOf t = 2 ∧ (∀ f ∈ fittingOf J, t * f * t⁻¹ = f⁻¹) ∧
      J = fittingOf J ⊔ Subgroup.zpowers t) : Nat.card J = 2 * 9 := by
  obtain ⟨t, -, ht2, hinv, hJ⟩ := ht
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htn : t ∈ Subgroup.normalizer (fittingOf J : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hinv y hy]
      exact (fittingOf J).inv_mem hy
    · intro hy
      have h2 := hinv _ hy
      have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
        rw [hti]
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [htt]; group
      rw [e] at h2
      rw [h2]
      exact (fittingOf J).inv_mem hy
  have hinf : fittingOf J ⊓ Subgroup.zpowers t = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h3 : x ^ 3 = 1 := hE.2 x hx.1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    have h2 : (t ^ n) ^ 2 = 1 := by
      have hsq : t ^ 2 = 1 := by rw [pow_two]; exact htt
      calc (t ^ n) ^ 2 = (t ^ 2) ^ n := by
            rw [← zpow_natCast, ← zpow_natCast t 2, ← zpow_mul, ← zpow_mul, mul_comm]
        _ = 1 := by rw [hsq, one_zpow]
    calc t ^ n = (t ^ n) ^ 3 * ((t ^ n) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hcard := card_sup_of_normalizes (Subgroup.zpowers_le.mpr htn) hinf
  have : Nat.card J = Nat.card ↥(fittingOf J ⊔ Subgroup.zpowers t) := by rw [← hJ]
  rw [this, hcard, hF9, Nat.card_zpowers, ht2]

omit [Finite V] in
theorem card_J_E27 (hF27 : Nat.card (fittingOf J) = 27) (hexp : ∀ f ∈ fittingOf J, f ^ 3 = 1)
    (ht : ∃ t ∈ J, orderOf t = 2 ∧
      (∀ f ∈ fittingOf J, t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf J)).map (fittingOf J).subtype) ∧
      J = fittingOf J ⊔ Subgroup.zpowers t) : Nat.card J = 2 * 27 := by
  obtain ⟨t, -, ht2, hfr, hJ⟩ := ht
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hfwd : ∀ f ∈ fittingOf J, t * f * t⁻¹ ∈ fittingOf J := by
    intro f hf
    have h1 : t * f * t⁻¹ * f ∈ fittingOf J := Subgroup.map_subtype_le _ (hfr f hf)
    have h2 := (fittingOf J).mul_mem h1 ((fittingOf J).inv_mem hf)
    have e : t * f * t⁻¹ * f * f⁻¹ = t * f * t⁻¹ := by group
    rwa [e] at h2
  have htn : t ∈ Subgroup.normalizer (fittingOf J : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd y, fun hy => ?_⟩
    have h2 := hfwd _ hy
    have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
      rw [hti]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt]; group
    rwa [e] at h2
  have hinf : fittingOf J ⊓ Subgroup.zpowers t = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h3 : x ^ 3 = 1 := hexp x hx.1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    have h2 : (t ^ n) ^ 2 = 1 := by
      have hsq : t ^ 2 = 1 := by rw [pow_two]; exact htt
      calc (t ^ n) ^ 2 = (t ^ 2) ^ n := by
            rw [← zpow_natCast, ← zpow_natCast t 2, ← zpow_mul, ← zpow_mul, mul_comm]
        _ = 1 := by rw [hsq, one_zpow]
    calc t ^ n = (t ^ n) ^ 3 * ((t ^ n) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hcard := card_sup_of_normalizes (Subgroup.zpowers_le.mpr htn) hinf
  have : Nat.card J = Nat.card ↥(fittingOf J ⊔ Subgroup.zpowers t) := by rw [← hJ]
  rw [this, hcard, hF27, Nat.card_zpowers, ht2]

namespace OneBlock151c

theorem ne_bot (B : OneBlock151c X Tb Xc J r) : J ≠ ⊥ := by
  obtain ⟨A, hA⟩ := QhatStar_nonempty B.hyp.qhat B.hyp.le_two
  obtain ⟨r', -, -, ⟨hA2, -⟩, -⟩ := hA
  intro hJ
  have : A ≤ ⊥ := hJ ▸ hA2.1.le
  exact hA2.1.ne_bot (le_bot_iff.mp this)

theorem fix_tb_ne_bot (B : OneBlock151c X Tb Xc J r) : fixV Tb ≠ ⊥ := by
  have hU0 : (⊤ : Subgroup V) ≠ ⊥ := fun e =>
    B.ne_bot (eq_bot_of_commV_eq_bot (B.commV_top.trans e))
  have hpos := rk_inf_fixV_pos_of_isPGroup_two B.sq B.syl.2.1
    (fun _ _ u _ => Subgroup.mem_top _) hU0
  intro hbot
  rw [hbot, inf_bot_eq, rk_bot] at hpos
  exact lt_irrefl _ hpos

theorem qstar_card_two (B : OneBlock151c X Tb Xc J r) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card J = 2 * m) : ∃ A ∈ QhatStar X, Nat.card A = 2 := by
  have hqs := B.d217.1
  obtain ⟨A, hA⟩ := QhatStar_nonempty B.hyp.qhat B.hyp.le_two
  have hA' : A ∈ sylow2Of J := hqs ▸ hA
  have hrk : rk A = 1 := rk_eq_of_mem_sylow2Of hA' hm (by simpa using hcard)
  have hcardA : Nat.card A = 2 := by
    rw [card_eq_two_pow_of_isPGroup hA'.2.1, hrk]
    norm_num
  refine ⟨A, ?_, hcardA⟩
  rw [← QhatStar_Jhat B.qhat B.le_two, ← B.jdef]
  exact hA

theorem genTop_of_not_S3 (B : OneBlock151c X Tb Xc J r)
    (hnot : ¬ (Nonempty (↥J ≃* DihedralGroup 3) ∧ rk V = 4)) : GenTop J Tb :=
  genTop_of_concl B.sq B.hyp B.d217.2 hnot B.syl.2.1
    (fun τ hτ y hy => B.normal τ (B.tb_le hτ) y hy) B.fix_tb_ne_bot

theorem genTop_S3 (B : OneBlock151c X Tb Xc J r) (e : ↥J ≃* DihedralGroup 3) (hrk : rk V = 4)
    {m : ℕ} (hm : Odd m) (hX : Nat.card X = 2 * m) : GenTop J Tb := by
  have hcard : Nat.card V = 16 := by
    rw [card_eq_two_pow_rk B.sq, hrk]
    norm_num
  have hfix := hfix_order_three_of_equiv_D3 B.sq B.hyp.o2 B.hyp.comm_fitting e
  have hTbrk : rk Tb = 1 := rk_eq_of_mem_sylow2Of B.syl hm (by simpa using hX)
  have hTbcard : Nat.card Tb = 2 := by
    rw [card_eq_two_pow_of_isPGroup B.syl.2.1, hTbrk]
    norm_num
  have hsylJ : IsSylowTwoOf (Tb ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal (B.syl : IsSylowTwoOf Tb X) B.le B.normal.le_normalizer
  have hJcard : Nat.card J = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨t, htTJ, ht1⟩ : ∃ t ∈ Tb ⊓ J, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : Tb ⊓ J = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    apply hsylJ.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot, hJcard]
    norm_num
  have ht2 : t ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥Tb) (x := ⟨t, htTJ.1⟩)
    rw [hTbcard] at this
    exact congrArg Subtype.val this
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hTbeq : Subgroup.zpowers t = Tb :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htTJ.1)
      (by rw [Nat.card_zpowers, hord, hTbcard])
  unfold GenTop
  rw [← hTbeq]
  exact y36_closure_eq_top B.sq hcard e hfix htTJ.2 ht1 ht2

theorem qdata_two (B : OneBlock151c X Tb Xc J r) (hr : r = 2) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card J = 2 * m) :
    qhatOf X = ((2 : ℚ) : WithTop ℚ) ∧ qOf X = ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨A, hA, hA2⟩ := B.qstar_card_two hm hcard
  subst hr
  exact ⟨B.qhat, qOf_eq_of_qstar_card_two B.sq B.qhat hA hA2⟩

end OneBlock151c

structure CaseI151c (X Tb J : Subgroup (MulAut V)) : Prop where
  cases : Cases7Aut X Tb J
  twoNilp : TwoNilpAut X
  genTop : GenTop J Tb
  qdata : (qhatOf X = ((2 : ℚ) : WithTop ℚ) ∧ qOf X = ((2 : ℚ) : WithTop ℚ)) ∨
    (ACase3 X J ∧ qhatOf X = ((3 / 2 : ℚ) : WithTop ℚ) ∧ qOf X = ((2 : ℚ) : WithTop ℚ))

end OneAux151c

end CFSG.Quasithin

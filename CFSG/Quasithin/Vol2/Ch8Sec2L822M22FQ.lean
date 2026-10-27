module

public import CFSG.Quasithin.Background.HFCode22QTwo
public import CFSG.Quasithin.Background.HFCode22Dual
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Aux

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section Conj

variable {G : Type} [Group G] [Finite G]

abbrev CodeHyp22_m22f {V : Subgroup G} (hV : IsElemAbelian 2 V) (L₀ : Subgroup G) : Prop :=
  @CFSG.Quasithin.MathieuCode22 ↥V (commGroupOfElemAbelian hV) (CFSG.Quasithin.autOn L₀ V) ⊤ ⊥

theorem isOver_autOn_m22f {L₀ M V : Subgroup G} (hV : IsElemAbelian 2 V) (hLM : L₀ ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L₀ : Set G)) :
    @CFSG.Quasithin.H.Mathieu.IsOver ↥V (commGroupOfElemAbelian hV) (autOn L₀ V) (autOn M V) :=
  ⟨AutOn.autOn_mono hLM, AutOn.autOn_le_normalizer_autOn hMN⟩

theorem qInt_eq_two_m22f
    {L₀ T V : Subgroup G} (hV : IsElemAbelian 2 V) (hT : T ≤ Subgroup.normalizer (L₀ : Set G))
    (h : CodeHyp22_m22f hV L₀) (hnot : ¬ autOn T V ≤ autOn L₀ V) :
    qInt (L₀ ⊔ T) V hV = 2 := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  have hLX := isOver_autOn_m22f hV le_sup_left (sup_le (Subgroup.le_normalizer) hT)
  have hXL : ¬ autOn (L₀ ⊔ T) V ≤ autOn L₀ V := by
    intro hle
    exact hnot ((AutOn.autOn_mono le_sup_right).trans hle)
  exact CFSG.Quasithin.B45Mat.qOf_eq_two_code22 hLX h hXL

theorem not_isDualFFInt_m22f
    {L₀ T V : Subgroup G} (hV : IsElemAbelian 2 V) (hT : T ≤ Subgroup.normalizer (L₀ : Set G))
    (h : CodeHyp22_m22f hV L₀) :
    ¬ IsDualFFInt (L₀ ⊔ T) V hV := by
  have hLX := isOver_autOn_m22f hV le_sup_left (sup_le (Subgroup.le_normalizer) hT)
  exact CFSG.Quasithin.B45Mat.not_isDualFFInt_code22 hV hLX h

theorem not_le_autOn_of_T_m22f {L₀ T M V : Subgroup G} (hTM : T ≤ M)
    (hnot : ¬ autOn T V ≤ autOn L₀ V) : ¬ autOn M V ≤ autOn L₀ V := fun hle =>
  hnot ((AutOn.autOn_mono hTM).trans hle)

theorem two_le_qMin_m22f
    {L₀ M V : Subgroup G} (hV : IsElemAbelian 2 V) (hLM : L₀ ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L₀ : Set G)) (h : CodeHyp22_m22f hV L₀)
    (hnot : ¬ autOn M V ≤ autOn L₀ V) :
    2 ≤ qMin M V hV := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  have hLX := isOver_autOn_m22f hV hLM hMN
  have hq2 : qOf (autOn M V) ≤ ((2 : ℚ) : WithTop ℚ) :=
    CFSG.Quasithin.B45Mat.qOf_le_two_code22 hLX h hnot
  obtain ⟨A0, hA0, hquad, hr0⟩ := qOf_le_iff.1 hq2
  have hne : (Qset (autOn M V)).Nonempty :=
    ⟨A0, ⟨⟨hA0, hr0⟩, (isQuadratic_iff_commSeries_two A0).1 hquad⟩⟩
  unfold qMin
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨D, hD, rfl⟩
  obtain ⟨⟨hD2, hD3⟩, -⟩ := hD
  have hpos : 0 < rk D := hD2.rk_pos
  by_contra hlt
  have hlt' : ¬ 2 ≤ rk D := hlt
  have h1 : rk D = 1 := by omega
  have hcard : Nat.card D = 2 := by
    rw [CFSG.Quasithin.B45Mat.card_eq_two_pow_rk hD2.isElemAbelian2, h1]
    norm_num
  have hnt : Nontrivial D := (Finite.one_lt_card_iff_nontrivial).1 (by rw [hcard]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : D)
  have htD : (x : MulAut ↥V) ∈ D := x.2
  have ht2 : (x : MulAut ↥V) ^ 2 = 1 := hD2.isElemAbelian2.2 _ htD
  have ht1 : (x : MulAut ↥V) ≠ 1 := fun e => hx (Subtype.ext e)
  have hord : orderOf (x : MulAut ↥V) = 2 := orderOf_eq_prime ht2 ht1
  have hZ : Subgroup.zpowers (x : MulAut ↥V) = D := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 htD) ?_
    exact le_of_eq (by rw [Nat.card_zpowers, hord, hcard])
  have htX : (x : MulAut ↥V) ∈ autOn M V := hD2.1 htD
  have h3 : 3 ≤ rkIdx (fixV (Subgroup.zpowers (x : MulAut ↥V))) :=
    CFSG.Quasithin.H.Mathieu.code22_three_le_rkIdx hLX h htX hord
  have hr : rkIdx (fixV D) = rkIdx (fixV (Subgroup.zpowers (x : MulAut ↥V))) := by
    rw [hZ]
  have hrAV : rAV D = (rkIdx (fixV (Subgroup.zpowers (x : MulAut ↥V))) : ℚ) := by
    unfold rAV
    rw [h1, hr]
    simp
  have hle2 : rAV D ≤ 2 := hD3
  rw [hrAV] at hle2
  have h3' : (3 : ℚ) ≤ (rkIdx (fixV (Subgroup.zpowers (x : MulAut ↥V))) : ℚ) := by
    exact_mod_cast h3
  linarith

end Conj

end CFSG.Quasithin.H13

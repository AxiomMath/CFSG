module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonCfg2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonNotIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Setting

theorem s16e_two_card_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) {a : ℕ}
    (haut : Nat.card (MulAut ↥(lBar V₀ V hV L)) ∣ a) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * a := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ := s16e_two_cfg2 D hx h61 h127 h1214 hV hset hL hs hF
  have h1 := s16e_two_card_dvd_six_mul_aut F (hF.natFacts.endUnits J₀ hJ₀)
    (hF.natFacts.endUnits J₁ hJ₁)
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hset.hyp151 hV
  have h2 : Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) = Nat.card (MulAut ↥(lBar V₀ V hV L)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [h2] at h1
  exact h1.trans (Nat.mul_dvd_mul_left 6 haut)

end Setting

section Sigma

theorem s16e_two_pow_dvd_card (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) {p : ℕ} (hp : p ∈ D.sig) :
    p ^ 3 ∣ Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have hpr := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 hp
  obtain ⟨E, hEA, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (Mbar D.M V₀ V hV)
  have hdvdE : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hpr
  have hdvdV : p ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
    hdvdE.trans (Subgroup.card_dvd_of_le hEA)
  have hcardeq : Nat.card ↥(Mbar D.M V₀ V hV) =
      Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    (c23_card_mbar_v1Sub_eq D (r1217_of_twelve_seventeen D hx h61 h127 h1214) hset.hyp151 hV).symm
  rw [← hcardeq]
  exact hdvdV

theorem s16e_two_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) {a : ℕ}
    (hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * a)
    (harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 3 ∣ 6 * a) : D.sig = {3} := by
  have hkey : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    by_contra hp3
    exact harith p hpp hp2 hp3
      ((s16e_two_pow_dvd_card D hx h4 h61 h127 h1214 hV hset hp).trans hcard)
  obtain ⟨q, hq⟩ := hx.sig_nonempty
  ext p
  simp only [Set.mem_singleton_iff]
  exact ⟨hkey p, fun hp => by rw [hp]; exact (hkey q hq) ▸ hq⟩

theorem s16e_two_no_index_three_star (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (h3 : 3 ∈ D.sig)
    (N : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) (hN : N.Normal) : N.index ≠ 3 := by
  obtain ⟨ρ, -, -⟩ := s16e_star_equiv D (r1217_of_twelve_seventeen D hx h61 h127 h1214)
    hset.hyp151 hV
  haveI : (N.comap ρ.toMonoidHom).Normal := Subgroup.normal_comap _
  have hidx : (N.comap ρ.toMonoidHom).index = N.index :=
    Subgroup.index_comap_of_surjective N ρ.surjective
  intro h
  exact s16e_mbar_index_ne_three D h638 h3 hset.hyp16 hV (N.comap ρ.toMonoidHom)
    (hidx.trans h)

end Sigma

section Transitivity

theorem s16e_two_trans_star (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {P : s16e_two_NatPred (vStar D.M V₀ V hV L)}
    (hF : s16e_two_Fam D V₀ V L hV P) :
    ∀ I₁ ∈ irrSet (lStar D.M V₀ V hV L), ∀ I₂ ∈ irrSet (lStar D.M V₀ V hV L),
      ∃ g ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV, I₂ = I₁.map g.toMonoidHom := by
  intro I₁ hI₁ I₂ hI₂
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hnot := s16e_two_not_irr_til D hx h61 h127 h1214 hV hset hL hs hF
  have hT := s16e_two_trans_til D hV hconc hs hF.simple hF.perfect hnot
  obtain ⟨J₁, hJ₁, hκ₁⟩ := s16e_two_lift_irr D hx h61 h127 h1214 hV hset hL hs hF I₁ hI₁
  obtain ⟨J₂, hJ₂, hκ₂⟩ := s16e_two_lift_irr D hx h61 h127 h1214 hV hset hL hs hF I₂ hI₂
  obtain ⟨g, hg, hgJ⟩ := hT J₁ hJ₁ J₂ hJ₂
  obtain ⟨ρ, -, hρκ⟩ := s16e_two_kappa_equiv D h1217 hset.hyp151 hV
  refine ⟨((ρ ⟨g, hg⟩ : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
    MulAut (vStar D.M V₀ V hV L)), (ρ ⟨g, hg⟩).2, ?_⟩
  rw [← hκ₂, hgJ, ← hκ₁, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext v
  exact hρκ ⟨g, hg⟩ v

end Transitivity

section Transfer

theorem s16e_two_transfer (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) {N₂ : Subgroup (MulAut (vStar D.M V₀ V hV L))}
    (hsym : IsSym ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L)) 3)
    (hdir : IsInternalDirect
      (s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L)) N₂
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ Nonempty (↥L₀ ≃* ↥N₂) := by
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D (r1217_of_twelve_seventeen D hx h61 h127 h1214)
    hset.hyp151 hV
  have hK := s16e_two_map_cent ρ (s16e_two_lBar_le D hset.hyp151 hV)
    (s16e_two_lStar_le D hset.hyp151 hV) hρL
  exact ⟨s16e_two_isSym_transport ρ (inf_le_left : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV)
      (inf_le_left : s16e_two_cent _ _ ≤ _) hK hsym,
    s16e_two_direct_transport ρ (inf_le_left : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV) hK hdir⟩

theorem s16e_two_transfer_eq (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L)
    (hsym : IsSym ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L)) 3)
    (hdir : IsInternalDirect
      (s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L))
      (lStar D.M V₀ V hV L) (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D (r1217_of_twelve_seventeen D hx h61 h127 h1214)
    hset.hyp151 hV
  have hK := s16e_two_map_cent ρ (s16e_two_lBar_le D hset.hyp151 hV)
    (s16e_two_lStar_le D hset.hyp151 hV) hρL
  exact ⟨s16e_two_isSym_transport ρ (inf_le_left : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV)
      (inf_le_left : s16e_two_cent _ _ ≤ _) hK hsym,
    s16e_two_direct_transport_eq ρ (inf_le_left : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV)
      (s16e_two_lBar_le D hset.hyp151 hV) hK hρL hdir⟩

end Transfer

section Routes

private theorem s16e_two_inner_transport {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : ∀ φ : MulAut B, ∃ b : B, ∀ x : B, φ x = b * x * b⁻¹) :
    ∀ φ : MulAut A, ∃ a : A, ∀ x : A, φ x = a * x * a⁻¹ := by
  intro φ
  obtain ⟨b, hb⟩ := hB (e.symm.trans (φ.trans e))
  refine ⟨e.symm b, fun x => ?_⟩
  apply e.injective
  have h := hb (e x)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h

theorem s16e_two_route_inner (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P)
    (hinn : ∀ φ : MulAut ↥(lBar V₀ V hV L), ∃ h₀ : ↥(lBar V₀ V hV L),
      ∀ h : ↥(lBar V₀ V hV L), φ h = h₀ * h * h₀⁻¹) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ := s16e_two_cfg2 D hx h61 h127 h1214 hV hset hL hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D hset.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hset.hyp151 hV
  have hinn' := s16e_two_inner_of_aut F (s16e_two_inner_transport e hinn)
  have hsupH := s16e_two_sup_H_of_inner hHX hinn'
  have hsup : s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) ⊔
      s16e_two_fixIrr (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) =
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV := by
    refine le_antisymm (sup_le inf_le_left fun x hx => hx.1) ?_
    exact hsupH.symm.le.trans (sup_le_sup_left (s16e_two_le_fixIrr hHX) _)
  have hT := s16e_two_trans_star D hx h61 h127 h1214 hV hset hL hconc hs hF
  have hno3 := s16e_two_no_index_three_star D hx h61 h127 h1214 h638 hV hset h3
  have hsym := (s16e_two_isSym_direct_of_trans F hE₀ hE₁ hsup hT hno3).1
  exact s16e_two_transfer_eq D hx h61 h127 h1214 hV hset hsym
    (s16e_two_direct_of_sup_H hHX F.simple F.perfect hsupH)

theorem s16e_two_route_autFrom (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P)
    (hA : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → Z391.AutFromGroup (lStar D.M V₀ V hV L) J)
    (hcube : ¬ 3 ^ 3 ∣ Nat.card (MulAut ↥(lBar V₀ V hV L))) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ := s16e_two_cfg2 D hx h61 h127 h1214 hV hset hL hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D hset.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hset.hyp151 hV
  have hcube' : ¬ 3 ^ 3 ∣ Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) := by
    rwa [Nat.card_congr (MulAut.congr e).toEquiv]
  have hK3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) := by
    have h27 : 3 ^ 3 ∣ Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
      s16e_two_pow_dvd_card D hx h4 h61 h127 h1214 hV hset h3
    exact s16e_two_three_dvd_of_cube h27 (s16e_two_card_dvd_mul_aut F) hcube'
  have hsupH := s16e_two_sup_H_of_autFromGroup F hHX hE₀ hE₁ (hA J₀ hJ₀) hK3
  have hsup : s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) ⊔
      s16e_two_fixIrr (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) =
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV := by
    refine le_antisymm (sup_le inf_le_left fun x hx => hx.1) ?_
    exact hsupH.symm.le.trans (sup_le_sup_left (s16e_two_le_fixIrr hHX) _)
  have hno3 := s16e_two_no_index_three_star D hx h61 h127 h1214 h638 hV hset h3
  have hsym := s16e_two_isSym_of_sup F hE₀ hE₁ hsup hK3 hno3
  exact s16e_two_transfer_eq D hx h61 h127 h1214 hV hset hsym
    (s16e_two_direct_of_sup_H hHX F.simple F.perfect hsupH)

theorem s16e_two_route_outer (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P)
    (hrk : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → 4 ≤ rk ↥J)
    (hinv : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      2 ≤ rk ↥(commSub J (Subgroup.zpowers h)))
    (hAut : Nat.card (MulAut ↥(lBar V₀ V hV L)) ≤ 2 * Nat.card ↥(lBar V₀ V hV L)) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
          Nonempty (↥L₀ ≃* MulAut ↥(lBar V₀ V hV L)) := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ := s16e_two_cfg2 D hx h61 h127 h1214 hV hset hL hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D hset.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hset.hyp151 hV
  have hAut' : Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) ≤ 2 * Nat.card ↥(lStar D.M V₀ V hV L) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact hAut
  have hcard := s16e_two_card_le_of_aut F hAut'
  have hinv4 : ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := fun h hh h1 h2 =>
    s16e_two_rk_comm_ge F hh (hinv J₀ hJ₀ h hh h1 h2) (hinv J₁ hJ₁ h hh h1 h2)
  obtain ⟨t, htX, ht2, ht1, htrk⟩ := s16e_two_involution_star D hx h61 h127 h1214 hV hset hconc
  obtain ⟨hsup, hlt⟩ := s16e_two_sup_of_outer F hHX hE₀ hE₁ (hrk J₀ hJ₀) (hrk J₁ hJ₁) hinv4
    hcard htX ht2 ht1 htrk
  have hT := s16e_two_trans_star D hx h61 h127 h1214 hV hset hL hconc hs hF
  have hno3 := s16e_two_no_index_three_star D hx h61 h127 h1214 h638 hV hset h3
  obtain ⟨hsym, hdir⟩ := s16e_two_isSym_direct_of_trans F hE₀ hE₁ hsup hT hno3
  obtain ⟨eN⟩ := s16e_two_equiv_aut_of_outer F hE₀ hE₁ hlt hAut'
  obtain ⟨hK, L₀, hdir₀, ⟨eL⟩⟩ := s16e_two_transfer D hx h61 h127 h1214 hV hset hsym hdir
  exact ⟨hK, L₀, hdir₀, ⟨eL.trans (eN.trans (MulAut.congr e))⟩⟩

theorem s16e_two_route_outer_six (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P)
    (hrk : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → 4 ≤ rk ↥J)
    (hinv : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      2 ≤ rk ↥(commSub J (Subgroup.zpowers h)))
    (hcube : ¬ 3 ^ 3 ∣ Nat.card (MulAut ↥(lBar V₀ V hV L)))
    (hord : Nat.card ↥(lBar V₀ V hV L) = 360)
    (hnorm : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ →
      IsSym ↥(normalizer (autSub (lStar D.M V₀ V hV L) J : Set (MulAut ↥J))) 6) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ 6 := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ := s16e_two_cfg2 D hx h61 h127 h1214 hV hset hL hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D hset.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hset.hyp151 hV
  have hcube' : ¬ 3 ^ 3 ∣ Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) := by
    rwa [Nat.card_congr (MulAut.congr e).toEquiv]
  have hK3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) :=
    s16e_two_three_dvd_of_cube (s16e_two_pow_dvd_card D hx h4 h61 h127 h1214 hV hset h3)
      (s16e_two_card_dvd_mul_aut F) hcube'
  obtain ⟨eS⟩ := hnorm J₀ hJ₀
  have hN720 : Nat.card ↥(normalizer (autSub (lStar D.M V₀ V hV L) J₀ :
      Set (MulAut ↥J₀))) = 720 := by
    rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hH360 : Nat.card ↥(lStar D.M V₀ V hV L) = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact hord
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ≤
      2 * Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
        (lStar D.M V₀ V hV L)) * Nat.card ↥(lStar D.M V₀ V hV L) := by
    have h := s16e_two_card_le_of_normalizer F hHX hE₀ hE₁ hK3
    rw [hN720] at h
    rw [hH360]
    refine h.trans (le_of_eq ?_)
    ring
  have hinv4 : ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := fun h hh h1 h2 =>
    s16e_two_rk_comm_ge F hh (hinv J₀ hJ₀ h hh h1 h2) (hinv J₁ hJ₁ h hh h1 h2)
  obtain ⟨t, htX, ht2, ht1, htrk⟩ := s16e_two_involution_star D hx h61 h127 h1214 hV hset hconc
  obtain ⟨hsup, hlt⟩ := s16e_two_sup_of_outer F hHX hE₀ hE₁ (hrk J₀ hJ₀) (hrk J₁ hJ₁) hinv4
    hcard htX ht2 ht1 htrk
  have hT := s16e_two_trans_star D hx h61 h127 h1214 hV hset hL hconc hs hF
  have hno3 := s16e_two_no_index_three_star D hx h61 h127 h1214 h638 hV hset h3
  obtain ⟨hsym, hdir⟩ := s16e_two_isSym_direct_of_trans F hE₀ hE₁ hsup hT hno3
  obtain ⟨eN⟩ := s16e_two_equiv_normalizer_of_outer F hHX hE₀ hE₁ hlt
    (by rw [hN720, hH360])
  obtain ⟨hK, L₀, hdir₀, ⟨eL⟩⟩ := s16e_two_transfer D hx h61 h127 h1214 hV hset hsym hdir
  exact ⟨hK, L₀, hdir₀, ⟨eL.trans (eN.trans eS)⟩⟩

end Routes

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
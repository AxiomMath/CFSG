module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_two_pow_dvd_card {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig) :
    p ^ 2 ∣ Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have hpr := c.two_le_pRank_mbar hp
  obtain ⟨E, hEA, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (Mbar D.M V₀ V hV)
  have hdvdE : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hpr
  have hdvdV : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
    hdvdE.trans (Subgroup.card_dvd_of_le hEA)
  have hcardeq : Nat.card ↥(Mbar D.M V₀ V hV) =
      Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    (c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV).symm
  rw [← hcardeq]
  exact hdvdV

theorem s168e3_two_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {a : ℕ}
    (hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * a)
    (harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ 6 * a) : D.sig = {3} := by
  have hkey : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    by_contra hp3
    exact harith p hpp hp2 hp3
      ((s168e3_two_pow_dvd_card c hp).trans hcard)
  obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
  ext p
  simp only [Set.mem_singleton_iff]
  exact ⟨hkey p, fun hp => by rw [hp]; exact (hkey q hq) ▸ hq⟩

theorem s168e3_three_dvd_of_sq {a b m : ℕ} (hX : 3 ^ 2 ∣ a) (hab : a ∣ b * m)
    (hm : ¬ 3 ^ 2 ∣ m) : 3 ∣ b := by
  by_contra hb
  have hcop : Nat.Coprime (3 ^ 2) b :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb)
  exact hm (hcop.dvd_of_dvd_mul_left (hX.trans hab))

theorem s168e3_two_three_dvd_of_not_sq {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (h3 : 3 ∈ D.sig) {P : s16e_two_NatPred (vStar D.M V₀ V hV L)}
    (hF : s16e_two_Fam D V₀ V L hV P)
    (hnsq : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(lBar V₀ V hV L))) :
    3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) := by
  obtain ⟨_, _, _, _, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
  have hnsq' : ¬ 3 ^ 2 ∣ Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) := by
    rwa [Nat.card_congr (MulAut.congr e).toEquiv]
  exact s168e3_three_dvd_of_sq (s168e3_two_pow_dvd_card c h3)
    (s16e_two_card_dvd_mul_aut F) hnsq'

theorem s168e3_two_route_autFrom {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) (h3 : 3 ∈ D.sig)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P)
    (hA : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → Z391.AutFromGroup (lStar D.M V₀ V hV L) J)
    (hK3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L))) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D c.setting.hyp151 hV
  have hsupH := s16e_two_sup_H_of_autFromGroup F hHX hE₀ hE₁ (hA J₀ hJ₀) hK3
  have hsup : s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) ⊔
      s16e_two_fixIrr (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) =
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV := by
    refine le_antisymm (sup_le inf_le_left fun x hx => hx.1) ?_
    exact hsupH.symm.le.trans (sup_le_sup_left (s16e_two_le_fixIrr hHX) _)
  have hno3 := s16e_two_no_index_three_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214
    c.std.h638 hV c.setting h3
  have hsym := s16e_two_isSym_of_sup F hE₀ hE₁ hsup hK3 hno3
  exact s16e_two_transfer_eq D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting hsym
    (s16e_two_direct_of_sup_H hHX F.simple F.perfect hsupH)

theorem s168e3_two_route_outer_six {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (h3 : 3 ∈ D.sig) {P : s16e_two_NatPred (vStar D.M V₀ V hV L)}
    (hF : s16e_two_Fam D V₀ V L hV P)
    (hrk : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → 4 ≤ rk ↥J)
    (hinv : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ → ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      2 ≤ rk ↥(commSub J (Subgroup.zpowers h)))
    (hord : Nat.card ↥(lBar V₀ V hV L) = 360)
    (hnorm : ∀ J, P (lStar D.M V₀ V hV L) J ⊥ →
      IsSym ↥(normalizer (autSub (lStar D.M V₀ V hV L) J : Set (MulAut ↥J))) 6)
    (hK3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L))) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ 6 := by
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D c.setting.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
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
  obtain ⟨t, htX, ht2, ht1, htrk⟩ :=
    s16e_two_involution_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.conc
  obtain ⟨hsup, hlt⟩ := s16e_two_sup_of_outer F hHX hE₀ hE₁ (hrk J₀ hJ₀) (hrk J₁ hJ₁)
    hinv4 hcard htX ht2 ht1 htrk
  have hT := s16e_two_trans_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
    c.ne c.conc hs hF
  have hno3 := s16e_two_no_index_three_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214
    c.std.h638 hV c.setting h3
  obtain ⟨hsym, hdir⟩ := s16e_two_isSym_direct_of_trans F hE₀ hE₁ hsup hT hno3
  obtain ⟨eN⟩ := s16e_two_equiv_normalizer_of_outer F hHX hE₀ hE₁ hlt
    (by rw [hN720, hH360])
  obtain ⟨hK, L₀, hdir₀, ⟨eL⟩⟩ :=
    s16e_two_transfer D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting hsym hdir
  exact ⟨hK, L₀, hdir₀, ⟨eL.trans (eN.trans eS)⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

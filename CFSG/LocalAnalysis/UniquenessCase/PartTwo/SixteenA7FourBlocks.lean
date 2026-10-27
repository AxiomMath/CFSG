module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourFixers
import CFSG.Quasithin.H13.A6S1372L76R
import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
import CFSG.Quasithin.Background.SmithD321Ext
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd
public import CFSG.Quasithin.Background.FFC6P

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

structure S168e3A7FourSpaceData (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop where
  fixedKernel_eq_bot :
    commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥
  v1Sub_eq : v1Sub D.M V₀ V hV L = V₀
  gamma15_eq : gamma15 D.M V₀ V hV L = 4
  delta15_le : delta15 D.M V₀ V hV L ≤ 2

theorem s168e3_a7Four_spaceData
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) :
    S168e3A7FourSpaceData D V₀ V L hV := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
  let Z : Subgroup W := U₁ ⊓ fixV H
  have hspan : U₁ ⊔ fixV H = ⊤ := by
    simpa [U₁, H] using s168e3_commSub_lBar_sup_fixV_eq_top c
  have hUL : commSub U₁ H = U₁ := by
    have h := commSub_sup_fixV (H := H) (J := U₁) (Z := fixV H) le_rfl
    rw [hspan] at h
    exact h.symm
  have hst : H ≤ stabSub U₁ :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant
      (CFSG.Quasithin.SmithD321.commSub_isInv (⊤ : Subgroup W) H)
  have hrowKeep := hrow
  obtain ⟨α, hreal⟩ := hrow
  have hrealKeep := hreal
  obtain ⟨π, hπ⟩ := hreal
  have hfaith : ∀ x ∈ H, (∀ u ∈ U₁, x u = u) → x = 1 :=
    FFC.faithful_on_of_realizes (FFC.a7Four_faithful α) hπ
  have hrec : (FFModel.a7Four α).Realizes (autSub H U₁) (⊤ : Subgroup ↥U₁)
      (Z.comap U₁.subtype) :=
    CFSG.Quasithin.FFC.B59.realizes_comap hst hfaith hrealKeep
  have hcommV : commV (autSub H U₁) = ⊤ := by
    apply Subgroup.map_injective (f := U₁.subtype) U₁.subtype_injective
    rw [CFSG.Quasithin.B15P4.map_subtype_commV_autSub hst, hUL, Subgroup.map_top,
      Subgroup.range_subtype]
  have hfixcomap : Z.comap U₁.subtype = fixV (autSub H U₁) := by
    apply Subgroup.map_injective (f := U₁.subtype) U₁.subtype_injective
    rw [Subgroup.map_comap_eq, Subgroup.subtype_range, map_subtype_fixV_autSub hst]
    simp [Z]
  have hrowV : A7Four (autSub H U₁) (commV (autSub H U₁))
      (fixV (autSub H U₁) ⊓ commV (autSub H U₁)) := by
    rw [hcommV, inf_top_eq, ← hfixcomap]
    exact ⟨α, hrec⟩
  have hsqU₁ : ∀ v : ↥U₁, v * v = 1 := fun v =>
    Subtype.ext (by
      have h := s15_Infra_vtil_sq_eq_one V₀ V hV (v : W)
      rwa [pow_two] at h)
  have hfixY : fixV (autSub H U₁) = ⊥ :=
    CFSG.Quasithin.H13.A6.A6L76R.fixV_eq_bot_of_a7Four ↥U₁ (autSub H U₁) hsqU₁
      hcommV hrowV
  have hfix : U₁ ⊓ fixV H = ⊥ := by
    have hmap := map_subtype_fixV_autSub hst
    rw [hfixY, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hrowBot : A7Four H U₁ ⊥ := by
    have h := hrowKeep
    rw [show U₁ ⊓ fixV H = ⊥ from hfix] at h
    exact h
  have hcardU : Nat.card ↥U₁ = 16 :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four_bot hrowBot
  have hfixW : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ := by
    simpa [wTil, H, U₁, lBar] using hfix
  have hv1 : v1Sub D.M V₀ V hV L = V₀ :=
    s16e_v1Sub_eq_of_inf_fixV D hV hfixW
  have hwT : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ := hfixW
  have hgamma : gamma15 D.M V₀ V hV L = 4 := by
    rw [s16e_gamma15_eq_of_inf_fixV D hV hwT]
    have h2 : Nat.card ↥(wTil V₀ V hV L) = 2 ^ rk ↥(wTil V₀ V hV L) :=
      card_eq_two_pow_rk (fun v => by
        rw [pow_two]
        exact hsqU₁ v)
    have hcardW : Nat.card ↥(wTil V₀ V hV L) = 2 ^ 4 :=
      hcardU.trans (by norm_num)
    have hrk : rk ↥(wTil V₀ V hV L) = 4 := by
      have hpow : 2 ^ rk ↥(wTil V₀ V hV L) = 2 ^ 4 := by
        rw [← h2]
        exact hcardW
      exact Nat.pow_right_injective le_rfl hpow
    exact hrk
  have hV₀W : V₀ ≤ wSub V₀ V hV L :=
    s15_Two_le_wSub hV c.setting.hyp151.hyp125.pairFacts.le L
  have hdelta : delta15 D.M V₀ V hV L = mSub V₀ := by
    rw [delta15, hv1]
    exact congrArg mSub (inf_eq_left.mpr hV₀W)
  have hdeltaLe : delta15 D.M V₀ V hV L ≤ 2 := by
    rw [hdelta]
    exact c.setting.hyp16.small
  exact ⟨hfix, hv1, hgamma, hdeltaLe⟩

theorem s16h_blockBound_one_of_a7Four_of_five_le_p
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) p 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
  have hdata := s168e3_a7Four_spaceData c hrow
  have hcardU : Nat.card ↥U₁ = 16 := by
    have hfix : U₁ ⊓ fixV H = ⊥ := hdata.fixedKernel_eq_bot
    have hrowBot : A7Four H U₁ ⊥ := by
      have h := hrow
      rw [hfix] at h
      exact h
    exact CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four_bot hrowBot
  have hcomm : ∀ a b : ↥U₁, a * b = b * a := fun a b => mul_comm a b
  have hsq : ∀ a : ↥U₁, a * a = 1 := fun a => by
    apply Subtype.ext
    simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV (a : W)
  have h20160 : Nat.card (MulAut ↥U₁) = 20160 :=
    CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_mulAut_of_elemAb_sixteen hcomm hsq hcardU
  have hp2 : ¬ p ^ 2 ∣ Nat.card (MulAut ↥U₁) := by
    rw [h20160]
    intro hdiv
    have hpdvd : p ∣ 20160 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hdiv
    have h20160' : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
    rw [h20160'] at hpdvd
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      rcases hp.dvd_mul.mp hpdvd with h1 | h7
      · rcases hp.dvd_mul.mp h1 with h2 | h5
        · rcases hp.dvd_mul.mp h2 with h6 | h3
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow h6))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp
              (by norm_num : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h3)))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp
            (by norm_num : Nat.Prime 5)).mp h5)))
      · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp
          (by norm_num : Nat.Prime 7)).mp h7)))
    rcases hp_cases with rfl | rfl | rfl | rfl
    · omega
    · omega
    · norm_num at hdiv
    · norm_num at hdiv
  have hle1 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥U₁)) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveRanksNotLe.pRank_top_le_of_not_dvd_card hp
      (k := 1) (by simpa using hp2)
  intro E hE hEab
  have hEstab : E ≤ stabSub U₁ := by
    refine CFSG.Quasithin.B1.le_stabSub_of_invariant ?_
    intro g hg w hw
    exact CFSG.Quasithin.SmithD321.commSub_stab (D := (⊤ : Subgroup W)) (K := H) (g := g)
      (hE hg).2 (fun v _ => Subgroup.mem_top v) w hw
  have hcardmul := card_autSub_mul (A := E) (U := U₁) hEstab
  have hEab' : IsElemAbelian p (autSub E U₁) :=
    (hEab.subgroupOf (stabSub U₁)).map (resHom U₁)
  have hcardAuto : Nat.card (autSub E U₁) ≤ p := by
    obtain ⟨k, hk⟩ := hEab'.isPGroup.exists_card_eq
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank hp.one_lt le_top hEab' hk).trans hle1
    calc Nat.card (autSub E U₁) = p ^ k := hk
      _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  calc Nat.card E = Nat.card (autSub E U₁) * Nat.card ↥(E ⊓ centSub U₁) := hcardmul.symm
    _ ≤ p * Nat.card ↥(E ⊓ centSub U₁) := Nat.mul_le_mul_right _ hcardAuto
    _ = p ^ 1 * Nat.card ↥(E ⊓ centSub U₁) := by rw [pow_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

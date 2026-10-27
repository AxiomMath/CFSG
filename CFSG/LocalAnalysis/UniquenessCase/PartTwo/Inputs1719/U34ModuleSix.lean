module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NaturalO4PlusSU3
import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isIrrOn_of_isSU3_two_of_mParam_le_six
    (h128 : W4Lem12_8) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y K : Subgroup (MulAut W)} (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hKcomp : CFSG.Open.IsComponentOf K Y) (hSU : IsSU3 ↥K 2)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hbasic : IsBasicModule Y) (hfix : fixV K = ⊥) (hmY : E3.mParam Y ≤ 2 * 2 + 2) :
    CFSG.LocalAnalysis.RankThreeUC.IsIrrOn K := by
  classical
  have : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  let H : Subgroup (MulAut W) := ⨆ X ∈ conjSet K Y, X
  have hKmem : K ∈ conjSet K Y :=
    ⟨1, Y.one_mem, by ext x; simp [Subgroup.mem_map]⟩
  have hKH : K ≤ H := by
    rw [show H = ⨆ X ∈ conjSet K Y, X from rfl]
    exact le_iSup₂_of_le K hKmem le_rfl
  have hfixH : fixV H = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    have hvK : v ∈ fixV K := fun k hk => hv k (hKH hk)
    rwa [hfix] at hvK
  rcases h128 W hW Y hO2 hbasic K hKcomp H rfl with h1 | h2 | h3
  · have hd : 6 * 2 ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K 2 hSU le_rfl
    omega
  · obtain ⟨hsum, I, hI, hratio⟩ := h2
    have key : ∀ (Z : Subgroup W), Z = ⊥ →
        IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X Z)) →
        (E3.mParam (autSub (autQuot Y Z) (I.map (QuotientGroup.mk' Z))) : ℚ) *
          ((rk ↥(commV (autQuot K Z)) : ℚ) /
            (rk ↥(I.map (QuotientGroup.mk' Z)) : ℚ)) ≤ (E3.mParam Y : ℚ) →
        CFSG.LocalAnalysis.RankThreeUC.IsIrrOn K := by
      intro Z hZ hsum hratio
      subst hZ
      let Istar : Subgroup (W ⧸ (⊥ : Subgroup W)) :=
        I.map (QuotientGroup.mk' (⊥ : Subgroup W))
      let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K (⊥ : Subgroup W)) Istar
      let G1 : Subgroup (MulAut ↥Istar) := autSub (autQuot Y (⊥ : Subgroup W)) Istar
      change (E3.mParam G1 : ℚ) * ((rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) /
        (rk ↥Istar : ℚ)) ≤ (E3.mParam Y : ℚ) at hratio
      have hinfV : commV K ⊓ fixV K = ⊥ :=
        commV_inf_fixV_eq_bot_of_isDirSumOver hKcomp hfixH hsum
      have hC : fixV Lstar = ⊥ := fixV_autSub_autQuot_bot_eq_bot hI hinfV
      have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      have hrkI : rk ↥Istar = rk ↥I := by
        unfold rk
        change padicValNat 2 (Nat.card ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) =
          padicValNat 2 (Nat.card ↥I)
        rw [Subgroup.card_map_of_injective hinj]
      have hrkK : rk ↥(commV (autQuot K (⊥ : Subgroup W))) = rk ↥(commV K) := by
        rw [← map_commV_eq_commV_autQuot K ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le K)]
        unfold rk
        rw [Subgroup.card_map_of_injective hinj]
      have hIbot : (⊥ : Subgroup W) < I := by
        have h := hI.2.1
        rwa [hfix, inf_bot_eq] at h
      have hIstarNe : Istar ≠ ⊥ := by
        intro hbot
        have hle : I ≤ (⊥ : Subgroup W) := by
          rw [Subgroup.map_eq_bot_iff] at hbot
          rwa [QuotientGroup.ker_mk'] at hbot
        exact (not_le_of_gt hIbot) hle
      have hVexp : ∀ v : W ⧸ (⊥ : Subgroup W), v ^ 2 = 1 := by
        intro v
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
        rw [← QuotientGroup.mk_pow, hW u, QuotientGroup.mk_one]
      have hIstarPos : 0 < rk ↥Istar :=
        Nat.pos_of_ne_zero fun h0 =>
          hIstarNe ((rk_eq_zero_iff (V := W ⧸ (⊥ : Subgroup W)) hVexp (H := Istar)).1 h0)
      have he : rk ↥(commV (autQuot K (⊥ : Subgroup W))) ≤ rk ↥Istar + 6 := by
        by_cases hmI : E3.mParam G1 < 2 * 2 + 2
        · obtain ⟨hnat, h4⟩ :=
            altTwo_u34_of_mParam_autSub_lt hW hKY hKcomp hSU hsum hI hmI
          have hrkI12 : rk ↥Istar = 6 * 2 := by
            have hcardWq :=
              S17.card_of_cNatModSU3Sub (S17.cNatModStructSU3Sub_of_natSUn hnat rfl)
            rw [Subgroup.card_top] at hcardWq
            have hC1 : Nat.card ↥(fixV Lstar) = 1 := by
              rw [hC]; exact Subgroup.card_bot
            have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixV Lstar)
            rw [hC1, mul_one, hcardWq] at hc
            unfold rk
            rw [hc, padicValNat.prime_pow]
          rw [hrkI12] at hratio
          have hpos : (0 : ℚ) < ((6 * 2 : ℕ) : ℚ) := by norm_num
          rw [mul_div_assoc', div_le_iff₀ hpos] at hratio
          have h2 : E3.mParam G1 * rk ↥(commV (autQuot K (⊥ : Subgroup W))) ≤
              E3.mParam Y * (6 * 2) := by exact_mod_cast hratio
          have h5 : 4 * rk ↥(commV (autQuot K (⊥ : Subgroup W))) ≤ 4 * 18 := by
            calc 4 * rk ↥(commV (autQuot K (⊥ : Subgroup W)))
                ≤ E3.mParam G1 * rk ↥(commV (autQuot K (⊥ : Subgroup W))) :=
                  Nat.mul_le_mul_right _ h4
              _ ≤ E3.mParam Y * (6 * 2) := h2
              _ ≤ 6 * (6 * 2) := Nat.mul_le_mul_right _ hmY
              _ = 4 * 18 := by norm_num
          have h18 := Nat.le_of_mul_le_mul_left h5 (by norm_num)
          omega
        · push Not at hmI
          have hpos : (0 : ℚ) < (rk ↥Istar : ℚ) := by exact_mod_cast hIstarPos
          have hApos : (0 : ℚ) < (E3.mParam G1 : ℚ) := by
            have h0 : 0 < E3.mParam G1 := by omega
            exact_mod_cast h0
          have hABC : (E3.mParam G1 : ℚ) *
              (rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) ≤
              (E3.mParam G1 : ℚ) * (rk ↥Istar : ℚ) := by
            have hAC : (E3.mParam G1 : ℚ) *
                (rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) ≤
                (E3.mParam Y : ℚ) * (rk ↥Istar : ℚ) := by
              have h := hratio
              rw [mul_div_assoc', div_le_iff₀ hpos] at h
              exact_mod_cast h
            calc (E3.mParam G1 : ℚ) *
                  (rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ)
                ≤ (E3.mParam Y : ℚ) * (rk ↥Istar : ℚ) := hAC
              _ ≤ 6 * (rk ↥Istar : ℚ) :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hmY) (Nat.cast_nonneg _)
              _ ≤ (E3.mParam G1 : ℚ) * (rk ↥Istar : ℚ) :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hmI) (Nat.cast_nonneg _)
          have hB : rk ↥(commV (autQuot K (⊥ : Subgroup W))) ≤ rk ↥Istar := by
            have h2 := le_of_mul_le_mul_left hABC hApos
            exact_mod_cast h2
          omega
      have hIle : I ≤ commSub (⊤ : Subgroup W) K := by
        calc I = commSub I K := hI.1.symm
          _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
      have hSK : StableUnder K (commSub (⊤ : Subgroup W) K) :=
        fun x hx u hu => CFSG.Quasithin.Asc81c.commSub_stable' hx hu
      have hdK : 6 * 2 ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K 2 hSU le_rfl
      have hle : commSub (commSub (⊤ : Subgroup W) K) K ≤ I :=
        commSub_le_of_rk_lt_dMinDeg hW hIle hSK hI.2.2.1 (by
          rw [← CFSG.Quasithin.commV_eq_commSub]
          have hb : rk ↥(commV K) ≤ rk ↥I + 6 := by
            rw [← hrkK]
            calc rk ↥(commV (autQuot K (⊥ : Subgroup W))) ≤ rk ↥Istar + 6 := he
              _ = rk ↥I + 6 := by rw [hrkI]
          omega)
      have hperfS := CFSG.Quasithin.RonanF918.commSub_commSub_eq_of_perfect (L := K)
        (S := (⊤ : Subgroup W)) (fun _ _ _ _ => Subgroup.mem_top _)
      rw [hperfS] at hle
      have hIK : I = commSub (⊤ : Subgroup W) K := le_antisymm hIle hle
      have hsup : commSub (⊤ : Subgroup W) K ⊔ fixV K = ⊤ := by
        rw [← CFSG.Quasithin.commV_eq_commSub]
        exact commV_sup_fixV_eq_top_of_isDirSumOver hKcomp hsum
      have hItop : I = ⊤ := by
        have h := hsup
        rwa [← hIK, hfix, sup_bot_eq] at h
      intro U hU
      have hUI : U ≤ I := by
        rw [hItop]
        exact le_top
      have hN : I ⊓ fixV K ≤ U := by
        rw [hfix, inf_bot_eq]
        exact bot_le
      rcases hI.2.2.2.2 U hU hN hUI with h | h
      · exact Or.inl (by rw [h, hfix, inf_bot_eq])
      · exact Or.inr (by rw [h, hItop])
    exact key (fixV H) hfixH hsum hratio
  · obtain ⟨R, e, -, -, hsub, hnat, -, -⟩ := h3
    exact (false_of_isSubnormal_isNaturalO4Plus_of_isSU3 hSU hsub hnat).elim

theorem card_le_eight_of_isIrrOn_isSU3_two
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {K A : Subgroup (MulAut W)} (hSU : IsSU3 ↥K 2)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn K)
    (hAN : A ≤ Subgroup.normalizer (K : Set (MulAut W))) (hA : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ 8 := by
  classical
  have hsq : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hperf : Group.IsPerfect ↥K := ⟨hSU.1.1⟩
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hSU.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial ↥K)
    exact hxy (Subtype.ext (MulEquiv.ext fun w => Subsingleton.elim _ _))
  have hodd := CFSG.QuasithinUnique.Setup.X5.centralizer_odd hsq K hirr
  obtain ⟨eU⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel le_rfl
    (CFSG.Blueprint.LieModel.statedClassicalModel hSU.2 (by decide))
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType (↥K ⧸ Subgroup.center ↥K) 2 3
      ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    CFSG.GH74.Uniqueness.Bender.BenderType.unitary 2 le_rfl (eU.trans (MulEquiv.subgroupCongr
      (show CFSG.Open.PSU3 2 2 = CFSG.Theory.Comparator.PSU3Model 2 from rfl)))
  let f : ↥A →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
    (CFSG.QuasithinUnique.Setup.X5.normalizerAct K).comp (Subgroup.inclusion hAN)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc := CFSG.QuasithinUnique.Setup.X5.mem_centralizer_of_normalizerAct_eq_one K
      (a := Subgroup.inclusion hAN a) ha
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Setup.X5.eq_one_of_involution_mem_odd hodd hc
      (by simpa [pow_two] using hA a a.2)
  have hE := (hB.card_le_of_sq_eq_one_aut f.range (by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have hx : x * x = 1 := Subtype.ext (by simpa [pow_two] using hA x x.2)
    rw [hx, map_one])).1
  have hcard : Nat.card ↥A = Nat.card ↥f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  simpa using hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

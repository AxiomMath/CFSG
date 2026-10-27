module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltSmallSubgroups
public import CFSG.CGT.A8S.TopPerm
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFHolds
import CFSG.GroupTheory.Alt8InvolutionCentralizer
import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreRigid
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenSetting
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof
open Equiv

variable {G : Type} [Group G] [Finite G]

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem p19_16_of_nineThreeEight
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h8 : CFSG.AGLEmbedding.NineThreeEight H S Dsub) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Ndeg, rdeg, heven, h2r, hne0, hne2, hne4, ⟨eN⟩, φ, -, -⟩ := h8
  have hp3 : CFSG.Open.pRank 3 H ≤ 3 := ctx19_14_pRank_le h Nat.prime_three (by norm_num)
  have hNle : Ndeg ≤ 11 := by
    by_contra hcon
    exact (false_of_alternating (N := Ndeg) (by omega) eN hp3).elim
  set Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := CFSG.AGLEmbedding.barM H Dsub with hKb
  set Jb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    CFSG.AGLEmbedding.barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub) with hJb
  have hK := ctx19_14_isWeakSBlock h h11
  have hJle : Jb ≤ Kb := barM_inf_le H (Subgroup.normalizer (S : Set G)) Dsub
  have hN6 : 6 ≤ Ndeg := by
    obtain ⟨k, hk⟩ := heven
    rw [hk] at h2r hne0 hne2 hne4 hNle ⊢
    have hk5 : k ≤ 5 := by omega
    interval_cases k <;> omega
  have hKbcard : 2 * Nat.card Kb = Ndeg.factorial := by
    have hNontriv : Nontrivial (Fin Ndeg) := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      simp only [Fintype.card_fin]
      omega
    have hcard : Nat.card Kb = Nat.card (alternatingGroup (Fin Ndeg)) := Nat.card_congr eN.toEquiv
    rw [hcard, two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hcardQ : Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) =
      rdeg.factorial * (Ndeg - 2 * rdeg).factorial := by
    have hprod : Nat.card (Equiv.Perm (Fin rdeg) × Equiv.Perm (Fin (Ndeg - 2 * rdeg))) =
        rdeg.factorial * (Ndeg - 2 * rdeg).factorial := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin]
    exact (Nat.card_congr φ.toEquiv).trans hprod
  have hcardJb : Nat.card Jb =
      Nat.card (CFSG.pCore 2 ↥Jb) * Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) := by
    have h := Subgroup.card_mul_index (CFSG.pCore 2 ↥Jb)
    rw [Subgroup.index_eq_card] at h
    exact h.symm
  have hcardJb_le : Nat.card Jb ≤ Nat.card Kb := Subgroup.card_le_of_le hJle
  have hcardJb_dvd : Nat.card Jb ∣ Nat.card Kb := Subgroup.card_dvd_of_le hJle
  have hr5 : rdeg ≤ 5 := by omega
  interval_cases rdeg
  ·
    have hquot : Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) = Ndeg.factorial := by
      rw [hcardQ]
      simp
    have hge : Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) ≤ Nat.card Jb := by
      rw [hcardJb]
      exact Nat.le_mul_of_pos_left _ (Nat.card_pos)
    have h2 : 2 * Nat.card Jb ≤ Ndeg.factorial := by
      have h := Nat.mul_le_mul_left 2 hcardJb_le
      rwa [hKbcard] at h
    have hbig : 2 * Ndeg.factorial ≤ Ndeg.factorial := by
      calc 2 * Ndeg.factorial = 2 * Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) := by rw [hquot]
        _ ≤ 2 * Nat.card Jb := Nat.mul_le_mul_left 2 hge
        _ ≤ Ndeg.factorial := h2
    have hpos : 0 < Ndeg.factorial := Nat.factorial_pos _
    omega
  ·
    have hNle10 : Ndeg ≤ 10 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk] at h2r hne0 hne2 hne4 hNle ⊢
      omega
    have hNge8 : 8 ≤ Ndeg := by
      obtain ⟨k, hk⟩ := heven
      rw [hk] at h2r hne0 hne2 hne4
      omega
    interval_cases Ndeg
    ·
      have hquot : Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) = 720 := by
        rw [hcardQ]
        norm_num [Nat.factorial]
      have hKb20160 : Nat.card Kb = 20160 := by
        have h := hKbcard
        norm_num [Nat.factorial] at h
        omega
      have hcardJb' : Nat.card Jb = Nat.card (CFSG.pCore 2 ↥Jb) * 720 := by
        rw [hcardJb, hquot]
      have hP_dvd : Nat.card (CFSG.pCore 2 ↥Jb) ∣ 28 := by
        have hdvd : Nat.card (CFSG.pCore 2 ↥Jb) * 720 ∣ Nat.card Kb := by
          rw [← hcardJb']
          exact hcardJb_dvd
        have h28 : Nat.card (CFSG.pCore 2 ↥Jb) * 720 ∣ 28 * 720 := by
          rw [show (28 : ℕ) * 720 = 20160 by norm_num, ← hKb20160]
          exact hdvd
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h28
      have hP4 : Nat.card (CFSG.pCore 2 ↥Jb) ≤ 4 := by
        obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Jb)).exists_card_eq
        have hdvd : 2 ^ m ∣ 28 := hm ▸ hP_dvd
        have hm2 : m ≤ 2 := by
          by_contra hcon
          push Not at hcon
          have h8 : 2 ^ 3 ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
          have : 8 ∣ 28 := h8.trans hdvd
          norm_num at this
        calc Nat.card (CFSG.pCore 2 ↥Jb) = 2 ^ m := hm
          _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
          _ = 4 := by norm_num
      by_cases hPbot : CFSG.pCore 2 ↥Jb = ⊥
      ·
        set Y : Subgroup (alternatingGroup (Fin 8)) := (Jb.subgroupOf Kb).map eN.toMonoidHom
        have hY : Nonempty (↥Y ≃* Equiv.Perm (Fin 6)) := by
          have e1 : ↥Y ≃* ↥(Jb.subgroupOf Kb) :=
            (Subgroup.equivMapOfInjective (Jb.subgroupOf Kb) eN.toMonoidHom
              eN.injective).symm
          have e2 : ↥(Jb.subgroupOf Kb) ≃* ↥Jb := Subgroup.subgroupOfEquivOfLe hJle
          have e3 : ↥Jb ≃* (↥Jb ⧸ CFSG.pCore 2 ↥Jb) :=
            ((QuotientGroup.quotientMulEquivOfEq hPbot).trans
              QuotientGroup.quotientBot).symm
          exact ⟨e1.trans (e2.trans (e3.trans (φ.trans MulEquiv.uniqueProd)))⟩
        obtain ⟨eY⟩ := hY
        obtain ⟨a, b, hab, hYeq⟩ := eq_centralizer_swap_of_perm6_le_alt8 Y eY
        have hbar : (barOfInter D.M Dsub).map
            ((barMEquiv hK.le hK.inf_twoCore).trans eN).toMonoidHom = Y := by
          rw [ctx19_14_barOfInter_eq h h11]
          change ((CFSG.RankThree.PartTwo.Sec19.starIm Dsub (Subgroup.normalizer (S : Set G))).map
            (eN.toMonoidHom.comp (barMEquiv hK.le hK.inf_twoCore).toMonoidHom)) = Y
          rw [← Subgroup.map_map, map_starIm_barMEquiv hK.le hK.inf_twoCore]
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨3, Or.inl rfl, Or.inr
          ⟨⟨(barMEquiv hK.le hK.inf_twoCore).trans eN⟩,
            (barMEquiv hK.le hK.inf_twoCore).trans eN, a, b, hab, ?_⟩⟩)))
        rw [hbar, hYeq]
      ·
        have hQn : (CFSG.pCore 2 ↥Jb).Normal := CFSG.pCore_normal
        obtain ⟨E, hEn, hEne, hEle, hEsq, -⟩ :=
          CFSG.RankThree.PartTwo.Sec21.FF84.exists_normal_elemAbelian_of_pGroup
            (CFSG.pCore 2 ↥Jb) (hQn := hQn) CFSG.pCore_isPGroup hPbot
        obtain ⟨⟨z, hzE⟩, hz1E⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
        have hz1 : z ≠ 1 := fun h => hz1E (Subtype.ext h)
        have hz2 : z * z = 1 := hEsq z hzE
        have hconj_sub : conjugatesOf z ⊆ (E : Set ↥Jb) \ {1} := by
          intro w hw
          obtain ⟨u, hu⟩ := hw
          have hweq : w = (u : ↥Jb) * z * (u : ↥Jb)⁻¹ := by
            calc w = (w * (u : ↥Jb)) * (u : ↥Jb)⁻¹ := by group
              _ = ((u : ↥Jb) * z) * (u : ↥Jb)⁻¹ := by rw [← hu.eq]
              _ = (u : ↥Jb) * z * (u : ↥Jb)⁻¹ := by group
          rw [hweq]
          constructor
          · exact hEn.conj_mem z hzE (u : ↥Jb)
          · intro h1
            apply hz1
            have hz : z = (u : ↥Jb)⁻¹ * ((u : ↥Jb) * z * (u : ↥Jb)⁻¹) * (u : ↥Jb) := by
              group
            rw [hz, h1]
            group
        have hE2 : 2 ≤ Nat.card E := by
          have h1 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hEne
          omega
        have hconj_le : (conjugatesOf z).ncard ≤ 3 := by
          have h1 : (conjugatesOf z).ncard ≤ (((E : Set ↥Jb) \ {1})).ncard :=
            Set.ncard_le_ncard hconj_sub (Set.toFinite _)
          have h2 : ((E : Set ↥Jb)).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
          rw [Set.ncard_sdiff_singleton_of_mem (s := (E : Set ↥Jb)) E.one_mem, h2] at h1
          have hE4 : Nat.card E ≤ 4 := (Subgroup.card_le_of_le hEle).trans hP4
          omega
        have hzKb : ((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Kb := hJle z.2
        have hC_le : Nat.card (Subgroup.centralizer ({z} : Set ↥Jb)) ≤ 192 := by
          have h1 := CFSG.CGT.A8S.Perm8.card_centralizer_subtype Jb z
          have h2 := CFSG.CGT.A8S.Perm8.card_centralizer_subtype Kb
            ⟨((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H), hzKb⟩
          rw [h1]
          refine (Subgroup.card_le_of_le (inf_le_inf_right _ hJle)).trans ?_
          rw [← h2,
            CFSG.CGT.A8S.Perm8.card_centralizer_mulEquiv eN
              ⟨((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H), hzKb⟩]
          refine Nat.le_of_dvd (by norm_num)
            (CFSG.GroupTheory.card_centralizer_dvd_one_ninety_two ?_ ?_)
          · rw [← map_pow]
            have hz2' : (⟨((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H), hzKb⟩ : ↥Kb) ^ 2 = 1 := by
              apply Subtype.ext
              show ((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 = 1
              rw [pow_two]
              exact congrArg Subtype.val hz2
            rw [hz2', map_one]
          · intro h1
            have h2 : (⟨((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H), hzKb⟩ : ↥Kb) = 1 :=
              eN.injective (h1.trans (map_one eN).symm)
            have h3 : ((z : ↥Jb) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 :=
              congrArg (fun w : ↥Kb => (w : ↥H ⧸ CFSG.pCore 2 ↥H)) h2
            exact hz1 (Subtype.ext h3)
        have hJb1440 : 1440 ≤ Nat.card Jb := by
          rw [hcardJb']
          have hP2 : 2 ≤ Nat.card (CFSG.pCore 2 ↥Jb) := by
            rcases (CFSG.pCore_isPGroup (p := 2) (G := ↥Jb)).card_eq_or_dvd with h1 | h2
            · exact absurd ((Subgroup.card_eq_one).mp h1) hPbot
            · exact Nat.le_of_dvd Nat.card_pos h2
          have h := Nat.mul_le_mul_right 720 hP2
          norm_num at h
          exact h
        have hconj_ge : 8 ≤ (conjugatesOf z).ncard := by
          rw [← Subgroup.index_centralizer_eq_ncard (G := ↥Jb) z]
          by_contra hcon
          push Not at hcon
          have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set ↥Jb))
          have : Nat.card ↥Jb ≤ 192 * 7 := by
            calc Nat.card ↥Jb = Nat.card (Subgroup.centralizer ({z} : Set ↥Jb)) *
                (Subgroup.centralizer ({z} : Set ↥Jb)).index := hmul.symm
              _ ≤ 192 * 7 := Nat.mul_le_mul hC_le (by omega)
          omega
        omega
    ·
      exfalso
      obtain ⟨k, hk⟩ := heven
      omega
    ·
      have hquot : Nat.card (↥Jb ⧸ CFSG.pCore 2 ↥Jb) = 40320 := by
        rw [hcardQ]
        norm_num [Nat.factorial]
      have hKb1814400 : Nat.card Kb = 1814400 := by
        have h := hKbcard
        norm_num [Nat.factorial] at h
        omega
      have hcardJb' : Nat.card Jb = Nat.card (CFSG.pCore 2 ↥Jb) * 40320 := by
        rw [hcardJb, hquot]
      have hP_dvd : Nat.card (CFSG.pCore 2 ↥Jb) ∣ 45 := by
        have hdvd : Nat.card (CFSG.pCore 2 ↥Jb) * 40320 ∣ Nat.card Kb := by
          rw [← hcardJb']
          exact hcardJb_dvd
        have h45 : Nat.card (CFSG.pCore 2 ↥Jb) * 40320 ∣ 45 * 40320 := by
          rw [show (45 : ℕ) * 40320 = 1814400 by norm_num, ← hKb1814400]
          exact hdvd
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h45
      have hPbot : CFSG.pCore 2 ↥Jb = ⊥ := by
        obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Jb)).exists_card_eq
        have hdvd : 2 ^ m ∣ 45 := hm ▸ hP_dvd
        have hm0 : m = 0 := by
          by_contra hcon
          have hm1 : 1 ≤ m := by omega
          have h2 : 2 ∣ 2 ^ m := by
            obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
            rw [pow_succ]
            exact dvd_mul_left 2 (2 ^ m')
          have : 2 ∣ 45 := h2.trans hdvd
          norm_num at this
        have hcard1 : Nat.card (CFSG.pCore 2 ↥Jb) = 1 := by
          rw [hm, hm0, pow_zero]
        exact (Subgroup.card_eq_one).mp hcard1
      set Y : Subgroup (alternatingGroup (Fin 10)) := (Jb.subgroupOf Kb).map eN.toMonoidHom
      have hY : Nonempty (↥Y ≃* Equiv.Perm (Fin 8)) := by
        have e1 : ↥Y ≃* ↥(Jb.subgroupOf Kb) :=
          (Subgroup.equivMapOfInjective (Jb.subgroupOf Kb) eN.toMonoidHom
            eN.injective).symm
        have e2 : ↥(Jb.subgroupOf Kb) ≃* ↥Jb := Subgroup.subgroupOfEquivOfLe hJle
        have e3 : ↥Jb ≃* (↥Jb ⧸ CFSG.pCore 2 ↥Jb) :=
          ((QuotientGroup.quotientMulEquivOfEq hPbot).trans
            QuotientGroup.quotientBot).symm
        exact ⟨e1.trans (e2.trans (e3.trans (φ.trans MulEquiv.uniqueProd)))⟩
      obtain ⟨eY⟩ := hY
      obtain ⟨a, b, hab, hYeq⟩ := eq_centralizer_swap_of_perm8_le_alt10 Y eY
      have hbar : (barOfInter D.M Dsub).map
          ((barMEquiv hK.le hK.inf_twoCore).trans eN).toMonoidHom = Y := by
        rw [ctx19_14_barOfInter_eq h h11]
        change ((CFSG.RankThree.PartTwo.Sec19.starIm Dsub (Subgroup.normalizer (S : Set G))).map
          (eN.toMonoidHom.comp (barMEquiv hK.le hK.inf_twoCore).toMonoidHom)) = Y
        rw [← Subgroup.map_map, map_starIm_barMEquiv hK.le hK.inf_twoCore]
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨4, Or.inr rfl, Or.inr
        ⟨⟨(barMEquiv hK.le hK.inf_twoCore).trans eN⟩,
          (barMEquiv hK.le hK.inf_twoCore).trans eN, a, b, hab, ?_⟩⟩)))
      rw [hbar, hYeq]
  ·
    exact (CFSG.HardMathSupport.Cooperstein.Proving.not_nonempty_quotient_perm_prod
      (Or.inl rfl) ⟨φ⟩).elim
  ·
    exfalso
    obtain ⟨k, hk⟩ := heven
    rw [hk] at h2r hne0 hne2 hne4 hNle
    omega
  ·
    exfalso
    obtain ⟨k, hk⟩ := heven
    rw [hk] at h2r hne0 hne2 hne4 hNle
    omega
  ·
    exfalso
    obtain ⟨k, hk⟩ := heven
    rw [hk] at h2r hne0 hne2 hne4 hNle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

module

public import CFSG.LocalAnalysis.StandardType.GGF4H4TwistedAux1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder
import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64TwComp
import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64TwLin
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Res
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
import all CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Proj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggF4TWP_five_dvd_ordTwistedA {f : ℕ} (hf : 2 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    5 ∣ CFSG.Open.ordTwistedA 2 (2 ^ f) := by
  have hp5 : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 5 4 :=
    ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩
  have h2f : 5 ∣ 2 ^ (2 * f) - 1 := by
    rw [pow_mul']
    exact h5.trans (CFSG.Timmesfeld.Orders.add_one_dvd_sq_sub_one (2 ^ f))
  have h4 : 4 ∣ 2 * f := (hp5.dvd_sub_one_iff (by norm_num) (2 * f)).mp h2f
  exact ((CFSG.SeitzReduction.UnitaryPilot.profile_idxU (n := 2) (g := f) le_rfl
    (by omega)).prim 5 4 hp5 (by norm_num)).2
    ⟨2, by simp, Or.inl ⟨even_two, by omega⟩⟩

private theorem ggF4TWP_commute_of_fix {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (A : GL (Fin 6) F) (Y : ↥(LargeEvenSLGroup (Fin 6) F)) (ℓ : ℕ) (hgcd : ℓ.gcd 3 = 1)
    (hY : Y ^ ℓ = 1)
    (hfix : TableB.linConjAut (Fin 6) F A (QuotientGroup.mk Y) =
      (QuotientGroup.mk Y : LargeEvenProj (LargeEvenSLGroup (Fin 6) F))) :
    A * (Y : GL (Fin 6) F) = (Y : GL (Fin 6) F) * A := by
  rw [TableB.linConjAut_mk] at hfix
  have hnN : (MulAut.conjNormal A Y)⁻¹ * Y ∈
      (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) :=
    QuotientGroup.eq.1 hfix
  have hcomm : (MulAut.conjNormal A Y) * ((MulAut.conjNormal A Y)⁻¹ * Y) =
      ((MulAut.conjNormal A Y)⁻¹ * Y) * (MulAut.conjNormal A Y) :=
    (ggF4H4Psl64_mem_scalars_commute _ _ hnN).symm
  have hY'ℓ : (MulAut.conjNormal A Y) ^ ℓ = 1 := by
    rw [← map_pow, hY, map_one]
  have hnℓ : ((MulAut.conjNormal A Y)⁻¹ * Y) ^ ℓ = 1 := by
    have h := (Commute.mul_pow hcomm ℓ).symm
    rw [mul_inv_cancel_left, hY, hY'ℓ, one_mul] at h
    exact h
  have hn3 : ((MulAut.conjNormal A Y)⁻¹ * Y) ^ 3 = 1 :=
    ggF4H4Psl64_mem_scalars_pow_three hF _ hnN
  have hn1 : (MulAut.conjNormal A Y)⁻¹ * Y = 1 := by
    have hg : ((MulAut.conjNormal A Y)⁻¹ * Y) ^ (ℓ.gcd 3) = 1 := pow_gcd_eq_one.mpr ⟨hnℓ, hn3⟩
    rwa [hgcd, pow_one] at hg
  have hYY : MulAut.conjNormal A Y = Y := inv_mul_eq_one.mp hn1
  have hcoe : A * (Y : GL (Fin 6) F) * A⁻¹ = Y := by
    rw [← MulAut.conjNormal_apply, hYY]
  calc A * (Y : GL (Fin 6) F) = A * (Y : GL (Fin 6) F) * A⁻¹ * A := by group
    _ = (Y : GL (Fin 6) F) * A := by rw [hcoe]


theorem ggF4H4Psl64Twisted_of_balance (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) :
    GGF4H4Psl64Twisted := by
  intro G _ _ p B Bs x L D J ks hres _hB f hf2 hpf hLlab hJblk K hK hp5 hKlab hKc
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hI : GGThmIHyp p B x L := hcfg.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  obtain ⟨y₀, hnbr⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hres.1.1.2.2.1.2 y₀ K hnbr
  obtain ⟨hJlab, hJcenter⟩ := hJblk.2 hpf hLlab
  have hΛJ : LargeEvenInLambda2 (⟨.twA, 2, f⟩ : LargeEvenLabel) :=
    ⟨(by omega : 1 ≤ f), le_rfl, fun _ => hf2⟩
  have hΛK : LargeEvenInLambda2 (⟨.A, 5, 2⟩ : LargeEvenLabel) :=
    ⟨by norm_num, by norm_num, fun h => by norm_num at h⟩
  have hJlabOrd : SporadicShape.labOrd (⟨.twA, 2, f⟩ : LargeEvenLabel) =
      Nat.card (J ⧸ Subgroup.center J) := ggKSL_labOrd_eq hΛJ hJlab
  have hKlabOrd : SporadicShape.labOrd (⟨.A, 5, 2⟩ : LargeEvenLabel) =
      Nat.card (K ⧸ Subgroup.center K) := ggKSL_labOrd_eq hΛK hKlab
  have h5q : 5 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [← hJlabOrd]
    exact ggF4TWP_five_dvd_ordTwistedA hf2 (hp5 ▸ hpf)
  have h5J : 5 ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
    exact dvd_mul_of_dvd_left h5q _
  have hpJ : p ∣ Nat.card J := by rw [hp5]; exact h5J
  have hJK : J ≤ K := le_of_ggNbr hL hI hDJ hpJ hnbr
  rcases lt_or_ge f 3 with hf3 | hf3
  ·
    have hf_eq : f = 2 := by omega
    subst hf_eq
    have hJZ1 : Nat.card (Subgroup.center J) = 1 := by rw [hJcenter]; norm_num
    have hJZ : Subgroup.center J = ⊥ := Subgroup.eq_bot_of_card_eq _ hJZ1
    have hJcard : Nat.card J = SporadicShape.labOrd (⟨.twA, 2, 2⟩ : LargeEvenLabel) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J), hJZ1, mul_one,
        hJlabOrd]
    have h13J : 13 ∣ Nat.card J := by rw [hJcard]; decide
    have h17J : ¬ 17 ∣ Nat.card J := by rw [hJcard]; decide
    have hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
      ggIsComponentOf_inf_centralizer_nbr hcfg hnbr hJK
    have hKZ1 : Nat.card (Subgroup.center K) = 1 := by rw [hKc]; exact Subgroup.card_bot
    have hKcard : Nat.card K = SporadicShape.labOrd (⟨.A, 5, 2⟩ : LargeEvenLabel) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hKZ1, mul_one,
        hKlabOrd]
    have h169 : ¬ 13 ^ 2 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({x} : Set G)) := by
      intro h
      have h' : 13 ^ 2 ∣ SporadicShape.labOrd (⟨.A, 5, 2⟩ : LargeEvenLabel) :=
        hKcard ▸ h.trans (Subgroup.card_dvd_of_le inf_le_left)
      exact absurd h' (by decide)
    have hSS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
    have hx : x ∈ B := hSS.2.1
    have hxBs : x ∈ Bs := hcfg.2.1.1 hx
    have hx5 : x ^ 5 = 1 := by rw [← hp5]; exact hSS.1.1.2 x hx
    obtain ⟨-, lab', -, hraw'⟩ := ggInnerDiagOn_relabel hRig hInnK hΛK hKlab
    have hlab' : lab' = ⟨.A, 5, 2⟩ := by
      obtain ⟨R, _, I, Fs, -, -, θ, h, -⟩ :=
        largeEvenRawDatum_exists ((largeEvenRawDatum_legacy _ _).2 hraw')
      exact h
    subst hlab'
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy, CFSG.Assembly.LargeEvenRecipeLinear]
      at hraw'
    obtain ⟨F, hFf, hFfin, hFcard, -, -, θ, -, hBsN, hall⟩ := hraw'
    letI := hFf
    haveI := hFfin
    have hF : Nat.card F = 4 := hFcard
    obtain ⟨φ, hφI, hφ⟩ := hall x⁻¹ (Bs.inv_mem hxBs)
    obtain ⟨A, rfl⟩ := TableB.exists_eq_linConjAut hφI
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBsN hxBs
    have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥K)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hKc])
    let ι : ↥K →* LargeEvenProj (LargeEvenSLGroup (Fin 6) F) :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    have hιinj : Function.Injective ι := θ.injective.comp hmk
    have hιsurj : Function.Surjective ι := fun r => by
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨l, rfl⟩
    have hφσ : ∀ l : ↥K, TableB.linConjAut (Fin 6) F A (ι l) =
        ι (K.normalizerMonoidHom ⟨x, hxN⟩ l) := fun l =>
      hφ l (K.normalizerMonoidHom ⟨x, hxN⟩ l) (by
        show ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv])
    have hpow : ∀ n : ℕ, ∀ l : ↥K, TableB.linConjAut (Fin 6) F (A ^ n) (ι l) =
        ι ((K.normalizerMonoidHom ⟨x, hxN⟩ ^ n) l) := by
      intro n
      induction n with
      | zero => intro l; simp
      | succ n ih =>
        intro l
        rw [pow_succ A n, map_mul, MulAut.mul_apply, hφσ, ih,
          pow_succ (K.normalizerMonoidHom ⟨x, hxN⟩) n, MulAut.mul_apply]
    have hσ5 : K.normalizerMonoidHom ⟨x, hxN⟩ ^ 5 = 1 := by
      rw [← map_pow]
      have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 5 = 1 :=
        Subtype.ext (by simpa using hx5)
      rw [h1, map_one]
    have hA5 : TableB.linConjAut (Fin 6) F (A ^ 5) = 1 := by
      ext q
      obtain ⟨l, rfl⟩ := hιsurj q
      rw [hpow 5 l, hσ5, MulAut.one_apply, MulAut.one_apply]
    have hA5c : A ^ 5 ∈ Subgroup.center (GL (Fin 6) F) :=
      linConjAut_ker_le_center (d := 6) (by norm_num) (MonoidHom.mem_ker.2 hA5)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA5c
    obtain ⟨c, hc⟩ := hA5c
    have hA15 : A ^ 15 = 1 := by
      rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, ← hc, ← map_pow,
        ggF4H4Psl64_units_pow_three hF c, map_one]
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 13 h13J
    have hyC : (y : G) ∈ Subgroup.centralizer ({x} : Set G) := (hJcomp.1 y.2).2
    have hxy : (y : G) * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    let yK : ↥K := ⟨y, hJK y.2⟩
    have hσy : K.normalizerMonoidHom ⟨x, hxN⟩ yK = yK := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      show x * (y : G) * x⁻¹ = y
      rw [← hxy, mul_inv_cancel_right]
    have hyK13 : yK ^ 13 = 1 := by
      apply Subtype.ext
      have h := congrArg Subtype.val (hy ▸ pow_orderOf_eq_one y)
      simpa [yK] using h
    have hyK1 : yK ≠ 1 := by
      intro h
      have h' : y = 1 := by
        have h2 := congrArg Subtype.val h
        exact Subtype.ext h2
      rw [h', orderOf_one] at hy
      norm_num at hy
    have hιy13 : ι yK ^ 13 = 1 := by rw [← map_pow, hyK13, map_one]
    have hιy1 : ι yK ≠ 1 := fun h => hyK1 (hιinj (h.trans (map_one ι).symm))
    obtain ⟨Y, hYπ, hY13, hY1⟩ := ggF4H4Psl64_lift hF (ι yK) 27 13
      (by rw [show (27 : ℕ) = 13 * 2 + 1 by norm_num, pow_succ, pow_mul, hιy13, one_pow,
        one_mul])
      (by norm_num) hιy13 hιy1
    have hYfix : TableB.linConjAut (Fin 6) F A (QuotientGroup.mk Y) =
        (QuotientGroup.mk Y : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) := by
      rw [hYπ, hφσ, hσy]
    have hAY : A * (Y : GL (Fin 6) F) = (Y : GL (Fin 6) F) * A :=
      ggF4TWP_commute_of_fix hF A Y 13 (by norm_num) hY13 hYfix
    obtain ⟨U, hU17, hU1, hAU, hUSL⟩ := ggF4TWP_exists_seventeen_commute hF (Y : GL (Fin 6) F) A
      (by rw [← Subgroup.coe_pow, hY13, Subgroup.coe_one]) (fun h => hY1 (Subtype.ext h))
      hA15 hAY.symm
    let U' : ↥(LargeEvenSLGroup (Fin 6) F) := ⟨U, hUSL⟩
    have hU'17 : U' ^ 17 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hU17)
    have hU'fix : TableB.linConjAut (Fin 6) F A (QuotientGroup.mk U') =
        (QuotientGroup.mk U' : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) := by
      rw [TableB.linConjAut_mk]
      have h : MulAut.conjNormal A U' = U' := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        show A * U * A⁻¹ = U
        rw [hAU, mul_inv_cancel_right]
      rw [h]
    obtain ⟨k, hk⟩ := hιsurj (QuotientGroup.mk U')
    have hσk : K.normalizerMonoidHom ⟨x, hxN⟩ k = k := hιinj (by rw [← hφσ, hk, hU'fix])
    have hkC : (k : G) ∈ K ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h := congrArg Subtype.val hσk
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      calc (k : G) * x = x * k * x⁻¹ * x := by rw [h]
        _ = x * k := by group
    have hk17 : (k : G) ^ 17 = 1 := by
      have h : ι (k ^ 17) = ι 1 := by
        rw [map_pow, hk, ← QuotientGroup.mk_pow, hU'17, QuotientGroup.mk_one, map_one]
      rw [← Subgroup.coe_pow, hιinj h, Subgroup.coe_one]
    have hk1 : (k : G) ≠ 1 := by
      intro h
      have hk1' : k = 1 := Subtype.ext h
      rw [hk1', map_one] at hk
      have hmem : U' ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) :=
        (QuotientGroup.eq_one_iff U').mp hk.symm
      have h3 : U' ^ 3 = 1 := ggF4H4Psl64_mem_scalars_pow_three hF U' hmem
      have h1 : U' ^ (Nat.gcd 17 3) = 1 := pow_gcd_eq_one.mpr ⟨hU'17, h3⟩
      norm_num at h1
      exact hU1 (congrArg Subtype.val h1)
    have hN : ∀ P : Subgroup G, P ≤ J → Nat.card P = 13 →
        ∀ v ∈ K ⊓ Subgroup.centralizer ({x} : Set G),
          v ∈ Subgroup.normalizer (P : Set G) → v ^ 17 = 1 → v = 1 := by
      intro P hPJ hP13 v hvC hvN hv17
      by_contra hv1
      have hov : Nat.Coprime (orderOf v) (13 - 1) :=
        Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hv17) (by norm_num)
      have hcomm := CFSG.Quasithin.EmptyFaithfulMultiple.L3213.commute_of_normalizes_of_coprime
        (p := 13) hP13 hov hvN
      obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
        by_contra hne
        push Not at hne
        have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hne
        rw [hbot, Subgroup.card_bot] at hP13
        norm_num at hP13
      have ha13 : a ^ 13 = 1 := by
        have h : (⟨a, haP⟩ : ↥P) ^ Nat.card P = 1 := pow_card_eq_one'
        rw [hP13] at h
        simpa using congrArg Subtype.val h
      let aK : ↥K := ⟨a, hJK (hPJ haP)⟩
      let vK : ↥K := ⟨v, hvC.1⟩
      have haK13 : aK ^ 13 = 1 := Subtype.ext (by simpa [aK] using ha13)
      have hvK17 : vK ^ 17 = 1 := Subtype.ext (by simpa [vK] using hv17)
      have hιa13 : ι aK ^ 13 = 1 := by rw [← map_pow, haK13, map_one]
      have hιv17 : ι vK ^ 17 = 1 := by rw [← map_pow, hvK17, map_one]
      have hιa1 : ι aK ≠ 1 := fun h =>
        ha1 (congrArg Subtype.val (hιinj (h.trans (map_one ι).symm)))
      have hιv1 : ι vK ≠ 1 := fun h =>
        hv1 (congrArg Subtype.val (hιinj (h.trans (map_one ι).symm)))
      obtain ⟨Ya, hYaπ, hYa13, hYa1⟩ := ggF4H4Psl64_lift hF (ι aK) 27 13
        (by rw [show (27 : ℕ) = 13 * 2 + 1 by norm_num, pow_succ, pow_mul, hιa13, one_pow,
          one_mul])
        (by norm_num) hιa13 hιa1
      obtain ⟨V, hVπ, hV17, hV1⟩ := ggF4H4Psl64_lift hF (ι vK) 18 17
        (by rw [show (18 : ℕ) = 17 + 1 by norm_num, pow_succ, hιv17, one_mul])
        (by norm_num) hιv17 hιv1
      have hva : ι vK * ι aK = ι aK * ι vK := by
        rw [← map_mul, ← map_mul]
        exact congrArg ι (Subtype.ext (hcomm a haP))
      have hfix : TableB.linConjAut (Fin 6) F (V : GL (Fin 6) F) (QuotientGroup.mk Ya) =
          (QuotientGroup.mk Ya : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) := by
        rw [TableB.linConjAut_of_mem _ V.2, MulAut.conj_apply]
        have hV' : (QuotientGroup.mk (⟨(V : GL (Fin 6) F), V.2⟩ :
            ↥(LargeEvenSLGroup (Fin 6) F)) : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) =
            ι vK := hVπ
        rw [hV', hYaπ, hva, mul_inv_cancel_right]
      have hVY : (V : GL (Fin 6) F) * Ya = Ya * V :=
        ggF4TWP_commute_of_fix hF V Ya 13 (by norm_num) hYa13 hfix
      exact ggF4TWP_no_commute_thirteen_seventeen hF (Ya : GL (Fin 6) F) V
        (by rw [← Subgroup.coe_pow, hYa13, Subgroup.coe_one]) (fun h => hYa1 (Subtype.ext h))
        (by rw [← Subgroup.coe_pow, hV17, Subgroup.coe_one]) (fun h => hV1 (Subtype.ext h))
        hVY.symm
    exact ggF4TWP_false_of_component hJcomp hJZ h13J h17J h169 hN hkC hk17 hk1
  ·
    obtain ⟨r, hr, hrJ⟩ := SCFourCover.exists_ppd_dvd_ordTwistedA_two (m := f) hf2
    have hr6 : 0 < 6 * f := by omega
    have hdvd : r ∣ SporadicShape.labOrd (⟨.A, 5, 2⟩ : LargeEvenLabel) :=
      hrJ.trans (ggKSL_labOrd_dvd (J := J) (K := K) hJK hΛK hKlab hΛJ hJlab)
    obtain ⟨i, hi, hdvd2⟩ :=
      ((CFSG.SeitzReduction.F4Pilot.profile_idxA (n := 5) (f := 2) (by norm_num)
        (by norm_num)).prim r (6 * f) hr hr6).1 hdvd
    rw [Finset.mem_Icc] at hi
    have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd2
    omega

end CFSG.StandardType

end

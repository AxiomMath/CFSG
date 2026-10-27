module

public import CFSG.Quasithin.H13.A6S13821zs
public import CFSG.Quasithin.H13.A6S13821l
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.Vol2.Ch10.SecA

theorem not_isStrongFFModule_sl2 (hF10 : Facts10_1)
    {W : Type} [CommGroup W] [Finite W] (hV : ∀ v : W, v ^ 2 = 1)
    {Gs Ls A : Subgroup (MulAut W)} (hB : B4Hyp Gs Ls) (hA : IsFFStarOffender Gs A)
    (hc : B42Conclusion Gs Ls A) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hFn : Nat.card F = 2 ^ n) (eL : ↥Ls ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ IsStrongFFModule Gs := by
  intro hstrong
  have hsh : IsShapeGroup ↥Ls := Or.inl ⟨n, hn, F, inferInstance, inferInstance, hFn, ⟨eL⟩⟩
  have hcard := shapeCard_of_isShapeGroup hsh
  have card_false : ∀ {N : ℕ}, Nat.card ↥Ls = N → ¬ ShapeCard N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  have hGL : Gs ≤ Subgroup.normalizer (Ls : Set (MulAut W)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting Gs
  have one_le : ∀ {K : Type} [Field K] [Finite K] {m : ℕ}, Nat.card K = 2 ^ m → 1 ≤ m := by
    intro K _ _ m hK
    by_contra h
    have h0 : m = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  have hcardL : Nat.card ↥Ls = 2 ^ n * (2 ^ n * 2 ^ n - 1) := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFn]
    have e2 : ∀ q : ℕ, ∏ j ∈ Finset.Icc 2 2, (q ^ j - 1) = q ^ 2 - 1 := fun q => by
      rw [Finset.Icc_self, Finset.prod_singleton]
    rw [e2]
    ring_nf
  have : Nontrivial ↥Ls := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardL]
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 15 ≤ 2 ^ n * 2 ^ n - 1 := by
      have : 16 ≤ 2 ^ n * 2 ^ n := by nlinarith
      omega
    nlinarith
  rcases B69.b42_strong hV hc hstrong with ⟨-, ⟨m, hnat⟩, -⟩ | ⟨⟨m, hsp, hJ⟩, -⟩ |
      ⟨-, m, hm, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩
  ·
    obtain ⟨K', _, _, hK'c, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hK'c
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      have h168 := card_eq_of_binaryNaturalSL hnat (by norm_num)
      have e3 : ∏ j ∈ Finset.Icc 2 3, (2 ^ j - 1) = 21 := by decide
      rw [e3] at h168
      norm_num at h168
      rw [hcardL] at h168
      have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      generalize 2 ^ n = q at hq h168
      rcases Nat.lt_or_ge q 6 with hlt | hge
      · interval_cases q <;> omega
      · have h1 : 35 ≤ q * q - 1 := by
          have : 36 ≤ q * q := by nlinarith
          omega
        have : 6 * 35 ≤ q * (q * q - 1) := Nat.mul_le_mul hge h1
        omega
    · refine card_false ?_ (not_shapeCard_SL_three h2)
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hK'c]
  ·
    obtain ⟨K', _, _, hK'c, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le hK'c
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      obtain ⟨N, hN, ⟨eN⟩⟩ := exists_normal_of_equiv e hLJ ((B6.ffJ_le Gs).trans hGL)
      have hq : CFSG.IsQuasisimple ↥N :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hB.2.2.1
      have h360 := hF10.sp4Two K' (by rw [hK'c]; norm_num) N hN hq
      exact card_false (by rw [← Nat.card_congr eN.toEquiv, h360]) not_shapeCard_360
    · have hJL := hJ (by omega)
      rw [hJL] at e
      refine card_false ?_ (not_shapeCard_Sp4 h1)
      rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hK'c]
  ·
    obtain ⟨K', _, _, hK'c, ⟨e⟩⟩ := hnat.exists_equiv
    have hK'2 : Nat.card K' = 2 := by rw [hK'c]; norm_num
    rcases hm with rfl | rfl
    · refine card_false ?_ not_shapeCard_20160
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hK'2]
    · refine card_false ?_ not_shapeCard_9999360
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hK'2]
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 4) (by norm_num)) π hR.1
    refine card_false ?_ not_shapeCard_20160
    rw [← Nat.card_congr e.toEquiv]
    rw [card_statedSL, card_SL_four_two]

section Offender

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem isStrongFFModule_of_lt {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hQS : InternalSec.QSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)))
    {B : Subgroup G} (hB : IsF918B T L V₁ Vp H (conjClosure K T) B)
    (hlt : (centralizerMod (centralizerMod V₁ I (conjClosure K T)) I B).relIndex I <
      (B ⊓ pCoreOf 2 H).relIndex B) :
    IsStrongFFModule (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) := by
  classical
  set K₀ := conjClosure K T with hK₀def
  set U := subM V₁ (conjClosure I H) I with hU
  set C' := (U ⊓ fixV (autIH V₁ I H K₀)).subgroupOf U with hC'
  set X := autSub (autIH V₁ I H K₀ ⊔ autIH V₁ I H T) U with hX
  set C := centralizerMod V₁ I K₀ with hC
  set CB := centralizerMod C I B with hCB
  have hTH : T ≤ H := hF.T_le_H
  have hBT : B ≤ T := hB.1.trans hF.pCoreOf_L₁T_le_T
  have hBH : B ≤ H := hBT.trans hTH
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  set ψ := actH hF.H_le_normalizer_V₁ hIH with hψ
  obtain ⟨-, hfT, -, -, -⟩ := hF.F918_3 hIU hirr hB (Or.inl rfl)
  obtain ⟨-, hfH, hmemQ, -, -⟩ := hF.F918_3 hIU hirr hB (Or.inr rfl)
  have hIT : conjClosure I T ≤ I := conjClosure_le fun t ht i hi =>
    (Subgroup.mem_normalizer_iff.mp (hTI ht) i).mp hi
  set Bb := autIH V₁ I H B with hBb
  have hBbU : Bb ≤ stabSub U := A6L32.autIH_le_stabSub_of hF hIU hV₁I hBH (hBT.trans hTI)
  set A := autSub Bb U with hA
  have hAX : A ≤ X :=
    autSub_mono (le_sup_of_le_right (autOn_le_autOn _ (secImg_mono hBT))) U
  have hAst : A ≤ stabSub ⊤ ⊓ stabSub C' := fun a ha =>
    ⟨InternalSec.mem_stabSub_top a, hQS.stab (hAX ha)⟩
  set Abar := autSec A ⊤ C' with hAbar
  have hAbarle : Abar ≤ autSec X ⊤ C' := autSec_mono hAX ⊤ C'
  have hcard1 : Nat.card ↥Abar = Nat.card ↥A :=
    InternalSec.card_autSec_eq hQS.stab hQS.inf_centSec_eq_bot hAX
  have hcard2 : Nat.card ↥A = Nat.card ↥Bb := by
    have h := card_autSub_mul hBbU
    have hbot : Bb ⊓ centSub U = ⊥ := by
      rw [eq_bot_iff]
      rintro γ ⟨hγ, hγc⟩
      rw [hBb, autIH_eq_map hF hBH] at hγ
      obtain ⟨b, hb, rfl⟩ := hγ
      rw [Subgroup.mem_bot]
      refine hF.actH_eq_one_of_mem_pCoreOf hIU (hfT b (Subgroup.mem_subgroupOf.mp hb) ?_)
      intro i hi
      have hiI : i ∈ I := hIT hi
      have hiIH : i ∈ conjClosure I H := le_conjClosure I H hiI
      have h1 := congrArg (fun w : ↥(tildeOf V₁ (conjClosure I H)) =>
        (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))
        (hγc (modMk hIHN i hiIH) ((modMk_mem_subM_iff hIHN hV₁I hiIH).mpr hiI))
      rw [actH_apply_coe] at h1
      refine commutator_mem_of_secMk_commute
        (x := ⟨(b : G), hF.H_le_normalizer_V₁ b.2⟩) (y := ⟨i, hIHN hiIH⟩) ?_
      have h3 := congrArg (· * secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        ⟨(b : G), hF.H_le_normalizer_V₁ b.2⟩) h1
      simp only [inv_mul_cancel_right] at h3
      exact h3
    rw [hbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hcard3 : Nat.card ↥Bb = (B ⊓ pCoreOf 2 H).relIndex B := by
    have h := card_autOn_secImg (hBH.trans hF.H_le_normalizer_V₁) hIHN (hBH.trans hIH)
    rw [hF.centralizerMod_eq_inf_pCoreOf le_rfl (hBH.trans hF.H_le_normalizer_V₁) hIHU hfH] at h
    exact h
  let θ : ↥I →* ↥U :=
    { toFun := fun i => ⟨modMk hIHN (i : G) (le_conjClosure I H i.2),
        (modMk_mem_subM_iff hIHN hV₁I _).mpr i.2⟩
      map_one' := by
        apply Subtype.ext
        exact modMk_one hIHN
      map_mul' := fun a b => by
        apply Subtype.ext
        exact modMk_mul hIHN (le_conjClosure I H a.2) (le_conjClosure I H b.2) }
  have hθ : ∀ i : ↥I, ((θ i : ↥U) : ↥(tildeOf V₁ (conjClosure I H))) =
      modMk hIHN (i : G) (le_conjClosure I H i.2) := fun i => rfl
  let f : ↥I →* Sec (⊤ : Subgroup ↥U) C' := (InternalSec.secMk C').comp θ
  have hV₁C : V₁ ≤ C := le_centralizerMod hF.H_le_normalizer_V₁ hF.K₀_le_H hV₁I
  have hsubC := subM_centralizerMod hF.H_le_normalizer_V₁ hIHN hIH hF.K₀_le_H hV₁I
    (le_conjClosure I H)
  have hθC : ∀ z : ↥I, θ z ∈ C' ↔ (z : G) ∈ C := by
    intro z
    have hz := (modMk_mem_subM_iff hIHN hV₁C (le_conjClosure I H z.2)).symm
    rw [hsubC] at hz
    rw [hC', Subgroup.mem_subgroupOf, hθ z]
    refine Iff.trans ?_ hz.symm
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun a => h2 a a.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun γ hγ => h2 ⟨γ, hγ⟩⟩
  have hf1 : ∀ z : ↥I, f z = 1 ↔ (z : G) ∈ C := by
    intro z
    show InternalSec.secMk C' (θ z) = 1 ↔ _
    rw [InternalSec.secMk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hθC z
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, rfl⟩ := InternalSec.secMk_surjective C' y
    obtain ⟨a, haIH, haw⟩ := exists_mk_of_mem_tilde (w : ↥(tildeOf V₁ (conjClosure I H)))
    have haI : (a : G) ∈ I := by
      have h1 : ((w : ↥(tildeOf V₁ (conjClosure I H))) :
          SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ I := w.2
      rw [← haw] at h1
      exact (secMk_mem_tildeOf_iff hV₁I).mp h1
    refine ⟨⟨(a : G), haI⟩, ?_⟩
    show InternalSec.secMk C' (θ ⟨(a : G), haI⟩) = InternalSec.secMk C' w
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact haw
  have hker : f.ker = C.subgroupOf I := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hf1 z
  have hfix : (CB.subgroupOf I).map f ≤ fixV Abar := by
    rintro _ ⟨i, hi, rfl⟩ a ha
    obtain ⟨g, hgA, rfl⟩ := (Bridge.mem_autSec_iff_secHom hAst).1 ha
    show Bridge.secHom ⊤ C' g (InternalSec.secMk C' (θ i)) = InternalSec.secMk C' (θ i)
    rw [InternalSec.secHom_secMk]
    obtain ⟨g', hg'B, hg'g⟩ := mem_autSub.mp hgA
    rw [hBb, autIH_eq_map hF hBH] at hg'B
    obtain ⟨b, hb, hbg⟩ := hg'B
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hiCB : (i : G) ∈ CB := Subgroup.mem_subgroupOf.mp hi
    have hbiI : (b : G) * (i : G) * (b : G)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hTI (hBT hbB)) _).mp i.2
    have hgi : (g : MulAut ↥U) (θ i) = θ ⟨_, hbiI⟩ := by
      rw [← hg'g]
      apply Subtype.ext
      rw [resHom_apply]
      show (g' : MulAut _) (modMk hIHN (i : G) (le_conjClosure I H i.2)) =
        modMk hIHN ((b : G) * (i : G) * (b : G)⁻¹) (le_conjClosure I H hbiI)
      rw [← hbg]
      exact actH_modMk hF.H_le_normalizer_V₁ hIHN hIH b (le_conjClosure I H i.2)
    rw [hgi]
    show f ⟨_, hbiI⟩ = f i
    have hq : f (⟨_, hbiI⟩ * i⁻¹) = 1 := by
      rw [hf1]
      show (b : G) * (i : G) * (b : G)⁻¹ * (i : G)⁻¹ ∈ C
      have h1 := C.inv_mem (hiCB.2.2 (b : G) hbB)
      have e : ((i : G) * (b : G) * (i : G)⁻¹ * (b : G)⁻¹)⁻¹ =
          (b : G) * (i : G) * (b : G)⁻¹ * (i : G)⁻¹ := by group
      rwa [e] at h1
    rw [map_mul, map_inv, mul_inv_eq_one] at hq
    exact hq
  have hCI : C ≤ I := centralizerMod_le_left _ _ _
  have hCCB : C ≤ CB := by
    intro x hx
    refine ⟨hx.1, ?_, fun b hb => ?_⟩
    · exact HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 (hCI.trans hIU)
        (hIU hx.1)
    · have hbC : b * x⁻¹ * b⁻¹ ∈ C := by
        have hBC : B ≤ Subgroup.normalizer (C : Set G) :=
          le_normalizer_centralizerMod (hBH.trans hF.H_le_normalizer_V₁) (hBT.trans hTI)
            (fun b' hb' => le_normalizer_conjClosure K T (hBT hb'))
        exact (Subgroup.mem_normalizer_iff.mp (hBC hb) _).mp (C.inv_mem hx)
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      exact C.mul_mem hx hbC
  have hcardC : Nat.card ↥(C.subgroupOf I) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCI).toEquiv
  have hSec : Nat.card (Sec (⊤ : Subgroup ↥U) C') * Nat.card ↥C = Nat.card ↥I := by
    have h := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥I) f
    rw [Subgroup.map_top_of_surjective f hfsurj, top_inf_eq, hker, hcardC, Subgroup.card_top,
      Subgroup.card_top] at h
    exact h
  have hCBc : Nat.card ↥((CB.subgroupOf I).map f) * Nat.card ↥C = Nat.card ↥CB := by
    have h := B1More.card_map_mul_card_inf_ker (CB.subgroupOf I) f
    have hinf : CB.subgroupOf I ⊓ f.ker = C.subgroupOf I := by
      rw [hker]
      exact inf_eq_right.mpr fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hCCB (Subgroup.mem_subgroupOf.mp hx))
    rw [hinf, hcardC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (centralizerMod_le_left _ _ _ : CB ≤ I)).toEquiv] at h
    exact h
  have hy : CB.relIndex I * Nat.card ↥CB = Nat.card ↥I := by
    have h := Subgroup.relIndex_mul_card CB I
    rwa [inf_eq_left.mpr (centralizerMod_le_left _ _ _ : CB ≤ I)] at h
  have hfixc : Nat.card ↥((CB.subgroupOf I).map f) ≤ Nat.card ↥(fixV Abar) :=
    Subgroup.card_le_of_le hfix
  have hAbarc : Nat.card ↥Abar = (B ⊓ pCoreOf 2 H).relIndex B := by
    rw [hcard1, hcard2, hcard3]
  refine ⟨Abar, hAbarle, ?_, ?_, ?_⟩
  · intro h
    have h1 : Nat.card ↥Abar = 1 := by rw [h, Subgroup.card_bot]
    rw [hAbarc] at h1
    have := relIndex_ne_zero' CB I
    omega
  · exact isElemAbelian2_autSec ⊤ C' (isElemAbelian2_autSub U hmemQ.1.1.2.2)
  · have hCpos : 0 < Nat.card ↥C := Nat.card_pos
    have hFpos : 0 < Nat.card ↥(fixV Abar) := Nat.card_pos
    rw [hAbarc]
    refine Nat.lt_of_mul_lt_mul_right (a := Nat.card ↥C) ?_
    rw [hSec, ← hy, ← hCBc]
    calc CB.relIndex I * (Nat.card ↥((CB.subgroupOf I).map f) * Nat.card ↥C)
        ≤ CB.relIndex I * (Nat.card ↥(fixV Abar) * Nat.card ↥C) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hfixc)
      _ < (B ⊓ pCoreOf 2 H).relIndex B * (Nat.card ↥(fixV Abar) * Nat.card ↥C) :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hFpos hCpos)
      _ = (B ⊓ pCoreOf 2 H).relIndex B * Nat.card ↥(fixV Abar) * Nat.card ↥C := by ring

end Offender

end CFSG.Quasithin.H13.A6.A6S20

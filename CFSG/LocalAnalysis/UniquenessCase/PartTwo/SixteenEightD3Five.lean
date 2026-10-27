module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenTenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1SigCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem s16e_d3_isElemAbelian {X : Type*} [Group X] {p n : ℕ} {E : Subgroup X}
    (hE : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E := by
  obtain ⟨e⟩ := hE
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun a ha => ?_⟩
  · have h1 : e a * e b = e b * e a := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  · have h1 : e (⟨a, ha⟩ ^ p) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    have h2 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2

private theorem s16e_d3_isElemAbelian_map {A B : Type*} [Group A] [Group B] {p : ℕ}
    {N : Subgroup A} (hN : IsElemAbelian p N) (e : A ≃* B) :
    IsElemAbelian p (N.map e.toMonoidHom) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => ?_
    obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    show (x : B) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hN.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro x ⟨a, ha, hax⟩
    rw [← hax, ← map_pow, hN.2 a ha, map_one]

private theorem s16e_d3_isElemAbelian_comap {A B : Type*} [Group A] [Group B] {p : ℕ}
    {K : Subgroup B} (hK : IsElemAbelian p K) (f : A →* B) (hf : Function.Injective f) :
    IsElemAbelian p (K.comap f) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    apply hf
    show f ((x : A) * (y : A)) = f ((y : A) * (x : A))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hK.1.is_comm.comm ⟨f x, x.2⟩ ⟨f y, y.2⟩)
  · intro x hx
    apply hf
    show f ((x : A) ^ p) = f 1
    rw [map_pow, map_one]
    exact hK.2 (f x) hx

private theorem s16e_d3_card_subgroupOf_of_le {A : Type*} [Group A] {E U : Subgroup A}
    (hU : U ≤ E) : Nat.card ↥(U.subgroupOf E) = Nat.card U := by
  rw [← Subgroup.card_subtype E (U.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hU]

private theorem s16e_d3_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem s16e_d3_normal_subgroupOf {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} (h : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    (L.subgroupOf A).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := h g g.2
  have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
      L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hg] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem s16e_d3_exists_xbar (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 4 ≤ r)
    (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L))
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal ∧ IsElemAbelian p Xbar ∧
      Nat.card Xbar = p ^ r ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  obtain ⟨t, htA, ht2, ht1, htrk, hW⟩ := id hconc
  obtain ⟨hLt, m, hD⟩ := s16e_core_deltaSym hp (by omega) hE hwT hW
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  have hLcomm : lBar V₀ V hV L ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ :=
    s16e_comm_le_commutator hpp (by omega) hLA hLn hE hLt hD
  have hpf := hset.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨Φ, -⟩ := s15_Three_barImage_equiv hV hMs
  let Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map Φ.symm.toMonoidHom
  have hNsub : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    s16e_d3_normal_subgroupOf hLn
  have hXnorm : Xbar.Normal := hNsub.map Φ.symm.toMonoidHom Φ.symm.surjective
  have hXcard : Nat.card Xbar = p ^ r := by
    rw [show Xbar = _ from rfl, Subgroup.card_map_of_injective Φ.symm.injective,
      s16e_d3_card_subgroupOf_of_le hLA, A38.card_eq_of_isElemAbelianOfRank hpp hE]
  have hel : IsElemAbelian p (lBar V₀ V hV L) := s16e_d3_isElemAbelian hE
  have hel' : IsElemAbelian p ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) :=
    s16e_d3_isElemAbelian_comap hel (Mbar D.M V₀ V hV).subtype (Subgroup.subtype_injective _)
  have hXel : IsElemAbelian p Xbar := by
    rw [show Xbar = _ from rfl]
    exact s16e_d3_isElemAbelian_map hel' Φ.symm
  have hmapc : (⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)),
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆).map Φ.toMonoidHom =
      ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)), (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top]
    have hrange : Φ.toMonoidHom.range = (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) :=
      MonoidHom.range_eq_top.mpr Φ.surjective
    rw [hrange]
  have hXc : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)),
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆ := by
    have h1 : Xbar.map Φ.toMonoidHom ≤
        ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)), (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := by
      rw [show Xbar = _ from rfl, Subgroup.map_map]
      have hcomp : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [hcomp, Subgroup.map_id, ← s16e_d3_subgroupOf_commutator_self (Mbar D.M V₀ V hV)]
      exact fun z hz => hLcomm (Subgroup.mem_subgroupOf.mp hz)
    intro x hx
    have hxmap : Φ x ∈ Xbar.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
    have hxcomm : Φ x ∈ ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)),
        (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := h1 hxmap
    rw [← hmapc] at hxcomm
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxcomm
    rwa [Φ.injective hyx] at hy
  exact ⟨Xbar, hXnorm, hXel, hXcard, hXc⟩

private theorem s16e_d3_pRank_bot {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine CFSG.SectionRank.pRank_le hp ?_
  intro E hE _
  have hE' : E = ⊥ := le_bot_iff.1 hE
  simp [hE']

private theorem s16e_d3_rankThreeGamma_le (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h77 : F07.R77Eq D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hYp : IsPGroup p Y) (hYnc : ¬ IsCyclic Y)
    (hYexp : ∀ x ∈ Y, x ^ p = 1) (hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥)
    (hrk : ∀ q ∈ D.sig, CFSG.Open.pRank q (D.M ⊓ normalizer (Y : Set G)) =
      CFSG.Open.pRank q D.M) :
    rankThreeGamma 1 p Y ≤ D.M := by
  by_cases hpσ : p ∈ D.sig
  · haveI : Fact p.Prime := ⟨hp⟩
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
      hSg.sig1_sp p (h1219 ▸ hpσ)
    unfold rankThreeGamma
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q hQY hQ1 => ?_
    have hQne : Q ≠ ⊥ := by
      intro hb
      rw [hb, s16e_d3_pRank_bot hp.one_lt] at hQ1
      omega
    exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le hsp hQne (hYp.to_le hQY)
      (hQY.trans hYM)
  · obtain ⟨q, hq⟩ := hSg.nonempty
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
      hSg.sig1_sp q (h1219 ▸ hq)
    obtain ⟨hqpr, hq2⟩ := D.sig_prime q hq
    have h2 : 2 < CFSG.Open.pRank q (D.M ⊓ normalizer (Y : Set G)) := by
      rw [hrk q hq]
      exact lt_of_lt_of_le (by norm_num) (hSg.three_le q hq)
    refine h77 (le_of_eq h1219) q hq hq2 hsp p hp hp2 hpσ Y hYM hYp hYnc hYexp hYcl h2 ?_
    exact (hrk q hq).symm

theorem s16e_d3_inP11 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1110 : R1110Core D) (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (h11 : F11.Hyp11 D V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 < n) (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) (hXn : Xbar.Normal)
    (hXe : IsElemAbelian p Xbar) (hXc : Nat.card Xbar = p ^ n)
    (hXd : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    F11.InP11 D (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) := by
  haveI := hXn
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
  have hXn' : D.M ≤ normalizer ((F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) : Set G) :=
    fun g hg => uc22p22u_mem_normalizer_barPreimage11 hg
  obtain ⟨hexp, hcl, hcard, hrk⟩ :=
    (h1110 V₀ V h11 p hp hp2 P hP).2.2 n hn Xbar hXn hXe hXc hXd
  have hPM : P ≤ D.M := (uc22p22u_sylow_O2p hp hp2 hP).1
  have hYT : Y ≤ P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar :=
    (Subgroup.closure_le (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)).2 fun x hx => hx.1
  have hTP : (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) ≤ P := by
    calc P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar ≤ P ⊓ ⁅D.M, D.M⁆ := inf_le_left
      _ ≤ P := inf_le_left
  have hYP : Y ≤ P := hYT.trans hTP
  have hYM : Y ≤ D.M := hYP.trans hPM
  have hYp : IsPGroup p Y := hP.isPGroup.to_le hYP
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hc
    haveI := hc
    have h1 : Monoid.exponent ↥Y ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hexp g.1 g.2)
    rw [IsCyclic.exponent_eq_card] at h1
    have h2 : Nat.card ↥Y ≤ p := Nat.le_of_dvd hp.pos h1
    have h3 : p ^ 2 ≤ Nat.card ↥Y := (Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ n)).trans hcard
    have h4 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥ := by
    rcases hcl with hcomm | ⟨-, hle⟩
    · have hb : ⁅Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
        ((Subgroup.le_centralizer_iff_isMulCommutative).2 hcomm)
      rw [hb, Subgroup.commutator_bot_left]
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans inf_le_right)
  have hΓ : rankThreeGamma 1 p Y ≤ D.M :=
    s16e_d3_rankThreeGamma_le D hSg h1219 h77 hp hp2 hYM hYp hYnc hexp hYcl
      (fun q hq => s11_TenP_pRank_inf_normalizer hp hp2 hP hXn' (D.sig_prime q hq).1
        (D.sig_prime q hq).2)
  refine ⟨p, hp, hp2, hYM, hYp, hexp, hYnc, ?_, hΓ, Or.inr ?_⟩
  · exact s11_TenP_permutes hp hp2 hP hXn' D.sylowM
  · exact ⟨Y, hYnc, s11_TenP_exists_isSylowOf_le_normalizer hp hp2 hP hXn', hΓ⟩

theorem s16e_d3_inPStar (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1110 : R1110Core D) (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (h11 : F11.Hyp11 D V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 2 < n) (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) (hXn : Xbar.Normal)
    (hXe : IsElemAbelian p Xbar) (hXc : Nat.card Xbar = p ^ n)
    (hXd : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    InPStar D V₀ (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) := by
  have hP11 : F11.InP11 D
      (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) :=
    s16e_d3_inP11 D hSg h1219 h1110 h77 h11 hp hp2 (by omega) Xbar hXn hXe hXc hXd hP
  refine ⟨hP11, fun _ => ⟨p, hp, ?_, Or.inl ?_⟩⟩
  · exact hP.isPGroup.to_le (by
      rw [F11.Omega1p]
      refine (Subgroup.closure_le P).2 fun x hx => ?_
      have hle : (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) ≤ P :=
        (inf_le_left.trans inf_le_left : _ ≤ P)
      exact hle hx.1)
  · have hcard : p ^ n ≤ Nat.card (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓
        F11.barPreimage11 D.M V₀ V Xbar)) := by
      obtain ⟨-, -, hcard, -⟩ :=
        (h1110 V₀ V h11 p hp hp2 P hP).2.2 n (by omega) Xbar hXn hXe hXc hXd
      exact hcard
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt hn) hcard

theorem s16e_d3_sig_five (D : Data G) (hSg : UC6S846.SigmaStd D) (h127 : R127 D)
    (h1110 : R1110Core D) (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D)
    (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hE : IsElemAbelianOfRank 7 5 ↥(lBar V₀ V hV L))
    (hsig : ∀ q ∈ D.sig, q = 3 ∨ q = 7) (hm : 2 < mBar D.M V₀ V hV) : 7 ∈ D.sig := by
  by_contra h7
  have h3mem : 3 ∈ D.sig := by
    obtain ⟨q, hq⟩ := hSg.nonempty
    rcases hsig q hq with h | h
    · exact h ▸ hq
    · exact absurd (h ▸ hq) h7
  have hH125 : Hyp125 D V₀ V := hset.hyp16.hyp125
  have h1219' : D.sig = D.sig1 := h1219 V₀ V hH125
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    hSg.sig1_sp 3 (h1219' ▸ h3mem)
  have hk : D.k = 1 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    rw [if_pos hsp]
  have hmGT : MBarGT D.M V₀ V (D.k + 1) := by
    rw [Hyp125.mBarGT_iff_lt_mBar hH125 (D.k + 1), hk]
    exact hm
  have hpf := hH125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  obtain ⟨Xbar, hXn, hXe, hXc, hXd⟩ :=
    s16e_d3_exists_xbar D hV hset hconc hs (Or.inr rfl) (by norm_num) hE
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 hH125
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 (F11.O2p 7 D.M)
  exact twelve_twelve D h63 h126 h1211 h111 h6161ii hH125 hmGT _
    (s16e_d3_inPStar D hSg h1219' h1110 h77 hH11 (by norm_num) (by norm_num) (by norm_num)
      Xbar hXn hXe hXc hXd hP)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

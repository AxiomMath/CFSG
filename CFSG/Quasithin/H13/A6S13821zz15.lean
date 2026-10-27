module

public import CFSG.Quasithin.H13.A6S13821zz14

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_sq_of_qOf {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hQS : InternalSec.QSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)))
    (hq : ((1 / 2 : ℚ) : WithTop ℚ) ≤ qOf (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔
        autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))))
    {B : Subgroup G} (hB : IsF918B T L V₁ Vp H (conjClosure K T) B) :
    (B ⊓ pCoreOf 2 H).relIndex B ≤
      ((centralizerMod (centralizerMod V₁ I (conjClosure K T)) I B).relIndex I) ^ 2 := by
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
  obtain ⟨-, hfT, -, -, -⟩ := hF.F918_3 hIU hirr hB (Or.inl rfl)
  obtain ⟨-, hfH, hmemQ, -, -⟩ := hF.F918_3 hIU hirr hB (Or.inr rfl)
  have hIT : conjClosure I T ≤ I := conjClosure_le fun t ht i hi =>
    (Subgroup.mem_normalizer_iff.mp (hTI ht) i).mp hi
  set Bb := autIH V₁ I H B with hBb
  have hBbU : Bb ≤ CFSG.Quasithin.stabSub U :=
    A6L32.autIH_le_stabSub_of hF hIU hV₁I hBH (hBT.trans hTI)
  set A := autSub Bb U with hA
  have hAX : A ≤ X :=
    autSub_mono (le_sup_of_le_right (autOn_le_autOn _ (secImg_mono hBT))) U
  have hAst : A ≤ CFSG.Quasithin.stabSub ⊤ ⊓ CFSG.Quasithin.stabSub C' := fun a ha =>
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
    have hq' : f (⟨_, hbiI⟩ * i⁻¹) = 1 := by
      rw [hf1]
      show (b : G) * (i : G) * (b : G)⁻¹ * (i : G)⁻¹ ∈ C
      have h1 := C.inv_mem (hiCB.2.2 (b : G) hbB)
      have e : ((i : G) * (b : G) * (i : G)⁻¹ * (b : G)⁻¹)⁻¹ =
          (b : G) * (i : G) * (b : G)⁻¹ * (i : G)⁻¹ := by group
      rwa [e] at h1
    rw [map_mul, map_inv, mul_inv_eq_one] at hq'
    exact hq'
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
  have hAbarc : Nat.card ↥Abar = (B ⊓ pCoreOf 2 H).relIndex B := by
    rw [hcard1, hcard2, hcard3]
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hidx : ((CB.subgroupOf I).map f).index = CB.relIndex I := by
    have h1 := Subgroup.index_mul_card ((CB.subgroupOf I).map f)
    have h2 : ((CB.subgroupOf I).map f).index * Nat.card ↥((CB.subgroupOf I).map f) *
        Nat.card ↥C = CB.relIndex I * Nat.card ↥((CB.subgroupOf I).map f) * Nat.card ↥C := by
      rw [h1, hSec, ← hy, ← hCBc]
      ring
    have hpos : 0 < Nat.card ↥((CB.subgroupOf I).map f) * Nat.card ↥C :=
      Nat.mul_pos Nat.card_pos hCpos
    rw [mul_assoc, mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hAel : IsElemAbelian2 A := isElemAbelian2_autSub U hmemQ.1.1.2.2
  have hAbarel : IsElemAbelian2 Abar := isElemAbelian2_autSec ⊤ C' hAel
  have hβ1 : 0 < (B ⊓ pCoreOf 2 H).relIndex B := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  have hAbar1 : Abar ≠ ⊥ := by
    intro h
    have hB1 : ¬ B ≤ pCoreOf 2 H := hB.2.1.2.2.1
    have h1 : Nat.card ↥Abar = 1 := by rw [h, Subgroup.card_bot]
    rw [hAbarc] at h1
    apply hB1
    rw [Subgroup.relIndex_eq_one] at h1
    exact fun b hb => (h1 hb).2
  have hquad : commSeries Abar 2 = ⊥ :=
    InternalSec.commSeries_autSec_eq_bot hAst (commSeries_autSub_eq_bot hBbU hmemQ.2)
  have hr := le_kq_iff.mp hq Abar ⟨hAbarle, hAbar1, hAbarel⟩ hquad
  have hrk := hAbarel.rk_pos hAbar1
  have hrk2 : rk ↥Abar ≤ 2 * rkIdx (fixV Abar) := by
    unfold rAV at hr
    have hrkq : (0 : ℚ) < (rk ↥Abar : ℚ) := by exact_mod_cast hrk
    rw [le_div_iff₀ hrkq] at hr
    have : (rk ↥Abar : ℚ) ≤ 2 * (rkIdx (fixV Abar) : ℚ) := by linarith
    exact_mod_cast this
  have hpow : 2 ^ rkIdx (fixV Abar) ≤ (fixV Abar).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) pow_padicValNat_dvd
  have hmono : (fixV Abar).index ≤ ((CB.subgroupOf I).map f).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hfix)
  rw [← hAbarc, B45Mat.card_eq_two_pow_rk hAbarel, ← hidx]
  calc 2 ^ rk ↥Abar ≤ 2 ^ (2 * rkIdx (fixV Abar)) := Nat.pow_le_pow_right (by norm_num) hrk2
    _ = (2 ^ rkIdx (fixV Abar)) ^ 2 := by rw [mul_comm, pow_mul]
    _ ≤ ((CB.subgroupOf I).map f).index ^ 2 := Nat.pow_le_pow_left (hpow.trans hmono) 2

theorem exists_ff_quot_sl3 {T V L V₁ Vp H K I : Subgroup G} (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hq : qOf (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) = ((1 / 2 : ℚ) : WithTop ℚ))
    {c : G} (hcH : c ∈ H) (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K)
    (hJN : K ⊔ T ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G))
    (hRc : ∀ b ∈ pCoreOf 2 (L₁Of L V₁ ⊔ T), c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H) :
    ∃ B : Subgroup G, IsF918B T L V₁ Vp H (conjClosure K T) B ∧
      (centralizerMod (I ⊔ conjSub c I) (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
        (B ⊓ pCoreOf 2 H).relIndex B := by
  classical
  have h1 := hF.toHypF98.toHypF91
  have hTH : T ≤ H := hF.T_le_H
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hcU : c ∈ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    le_normalizer_conjClosure Vp H hcH
  have hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G) := hHV₁ hcH
  have hirr := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  have hIc : conjSub c I ≤ conjClosure Vp H := by
    rw [← conjSub_eq_of_mem_normalizer hcU]
    exact conjSub_mono c hIU
  have hJU : I ⊔ conjSub c I ≤ conjClosure Vp H := sup_le hIU hIc
  have hV₁J : V₁ ≤ I ⊔ conjSub c I := hV₁I.trans le_sup_left
  obtain ⟨B, hB, -⟩ := hF.F918_2
  have hBT : B ≤ T := hB.1.trans hF.pCoreOf_L₁T_le_T
  have hUab := hF.toHypF98.F911_3
  have hJI : I ⊔ conjSub c I ≤ Subgroup.normalizer (I : Set G) :=
    hJU.trans (HypF91.le_normalizer_of_isElemAbelian_le hUab hIU)
  have hBcQ : ∀ b ∈ B, c⁻¹ * b * c ∈ T := by
    intro b hb
    have hq := hRc b (hB.1 hb)
    have hq' : c⁻¹ * b * c * b⁻¹ ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).mp
        ((pCoreOf 2 H).inv_mem hq)
      have e : c⁻¹ * (c * b * c⁻¹ * b⁻¹)⁻¹ * c⁻¹⁻¹ = c⁻¹ * b * c * b⁻¹ := by group
      rwa [e] at this
    have e : c⁻¹ * b * c = (c⁻¹ * b * c * b⁻¹) * b := by group
    rw [e]
    exact T.mul_mem (isSylowTwoOf_pCoreOf_le h1.sylow_H hq') (hBT hb)
  have hBI' : B ≤ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_conjSub (hTI (hBcQ b hb))
  have hV₁C : V₁ ≤ centralizerMod V₁ I (conjClosure K T) :=
    le_centralizerMod hHV₁ hF.K₀_le_H hV₁I
  have hIC : I ≤ Subgroup.normalizer (centralizerMod V₁ I (conjClosure K T) : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le (isElemAbelian_mono hUab hIU)
      (centralizerMod_le_left _ _ _)
  have hI'C' : conjSub c I ≤
      Subgroup.normalizer (centralizerMod V₁ (conjSub c I) (conjClosure K T) : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le (isElemAbelian_mono hUab hIc)
      (centralizerMod_le_left _ _ _)
  have hII' : I ⊓ conjSub c I ≤ centralizerMod V₁ (conjSub c I) (conjClosure K T) := by
    intro x hx
    have h3 := hII hx
    refine ⟨hx.2, h3.2.1, ?_⟩
    rw [hK₀]
    exact h3.2.2
  have hcount := relIndex_mul_le_sup (B := B) hV₁I le_sup_left le_sup_right hJI
    (hBT.trans hTI) hBI' hV₁C hIC hI'C' hII'
  have hCc : conjSub c (centralizerMod V₁ I (conjClosure K T)) =
      centralizerMod V₁ (conjSub c I) (conjClosure K T) := by
    rw [conjSub_centralizerMod, conjSub_eq_of_mem_normalizer hcV₁,
      conjSub_eq_of_mem_normalizer (hF.K₀_normal hcH)]
  have hV₁c : V₁ ≤ conjSub c I := by
    have h3 := conjSub_mono c hV₁I
    rwa [conjSub_eq_of_mem_normalizer hcV₁] at h3
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjSub c I, q * u * q⁻¹ * u⁻¹ ∈ V₁ := by
    intro q hq u hu
    rw [h1.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 u (hIc hu)
  have hconj := relIndex_centralizerMod_conjSub (V₁ := V₁)
    (C := centralizerMod V₁ I (conjClosure K T)) (I := I) (B := B) (Q := pCoreOf 2 H) (c := c)
    (hCc ▸ le_centralizerMod hHV₁ hF.K₀_le_H hV₁c) (fun b hb => hRc b (hB.1 hb)) hQc hBI'
  rw [hCc] at hconj
  rw [hconj] at hcount
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hT := A6L32.autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hx := relIndex_le_sq_of_qOf hF hV₁I hIU hirr hTI hQS hq.ge hB
  have hUJ : conjClosure Vp H ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hUab hJU
  have hBJ : B ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G) :=
    hBT.trans (le_sup_right.trans hJN)
  have hmul := (relIndex_mul_le_relIndex hV₁J hJU hUJ hBJ (B := B)).trans hB.2.1.2.2.2.2
  refine ⟨B, hB, ?_⟩
  have hβ : 0 < (B ⊓ pCoreOf 2 H).relIndex B := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  have hβa : (B ⊓ pCoreOf 2 H).relIndex B ≤
      (centralizerMod V₁ (I ⊔ conjSub c I) B).relIndex (I ⊔ conjSub c I) :=
    hx.trans (by rw [sq]; exact hcount)
  refine Nat.le_of_mul_le_mul_left ?_ hβ
  calc (B ⊓ pCoreOf 2 H).relIndex B *
        (centralizerMod (I ⊔ conjSub c I) (conjClosure Vp H) B).relIndex (conjClosure Vp H)
      ≤ (centralizerMod V₁ (I ⊔ conjSub c I) B).relIndex (I ⊔ conjSub c I) *
        (centralizerMod (I ⊔ conjSub c I) (conjClosure Vp H) B).relIndex (conjClosure Vp H) :=
        Nat.mul_le_mul_right _ hβa
    _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hmul
    _ = (B ⊓ pCoreOf 2 H).relIndex B * (B ⊓ pCoreOf 2 H).relIndex B := sq _

theorem fixProp_layer2_sl3 (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    {T V L V₁ Vp H K I T₀ : Subgroup G} (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))]
    (hq : qOf (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) = ((1 / 2 : ℚ) : WithTop ℚ))
    {c : G} (hcH : c ∈ H) (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K)
    (hJN : K ⊔ T ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G))
    (hRc : ∀ b ∈ pCoreOf 2 (L₁Of L V₁ ⊔ T), c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H)
    (hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤)
    (hs : IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hoddZ : Odd (Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))))
    (hsyl : IsSylowTwoOf T₀ K) :
    S1565.FixProp ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H)).comp
        (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp)))
      ((K ⊓ Subgroup.normalizer (T₀ : Set G)).subgroupOf K)
      (subM V₁ (conjClosure Vp H) (I ⊔ conjSub c I)) ⊤ := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hIc : conjSub c I ≤ conjClosure Vp H := by
    rw [← conjSub_eq_of_mem_normalizer (hHU hcH)]
    exact conjSub_mono c hIU
  have hJU : I ⊔ conjSub c I ≤ conjClosure Vp H := sup_le hIU hIc
  have hV₁J : V₁ ≤ I ⊔ conjSub c I := hV₁I.trans le_sup_left
  by_cases hnt : ∀ k ∈ K, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ I ⊔ conjSub c I
  ·
    intro w _ _ x _
    obtain ⟨u, huU, -, rfl⟩ := exists_modMk_of_mem_subM hUN (hV₁I.trans hIU)
      (Subgroup.mem_subgroupOf.mpr w.2)
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH x.2)) u).mp huU
    change actH hHV₁ hHU ⟨(x : G), hKH x.2⟩ (modMk hUN u huU) * (modMk hUN u huU)⁻¹ ∈ _
    rw [actH_modMk hHV₁ hUN hHU _ huU, ← modMk_inv hUN huU,
      ← modMk_mul hUN hxu ((conjClosure Vp H).inv_mem huU), modMk_mem_subM_iff hUN hV₁J]
    exact hnt x x.2 u huU
  · obtain ⟨B, hB, hle⟩ := exists_ff_quot_sl3 hSQ hF hK₀ hV₁I hIU hirrT hTI hq hcH hII hJN hRc
    exact fixProp_quot_of_ff hA21 hB51 hSQ hF hK₀ hV₁J hJU hJN hnt hB hle hperf hs hn hcard
      hoddZ hsyl

end CFSG.Quasithin.H13.A6.A6S20

module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KLine
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
public import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem omega4_cons : ∀ a b c d' : F3,
    omega4 ![a, b, c * 2, d' * 2] ![1, 0, 0, 0] = c ∧
      omega4 ![a, b, c * 2, d' * 2] ![0, 1, 0, 0] = d' ∧
      omega4 ![a, b, c * 2, d' * 2] ![0, 0, 1, 0] = a ∧
      omega4 ![a, b, c * 2, d' * 2] ![0, 0, 0, 1] = b := by
  decide +kernel

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem ker_centralizes_d {κ : G} (hκ : κ ∈ NQ Q d) (hM : Mg d a₀ a₁ f₀ f₁ κ = 1) :
    κ * d * κ⁻¹ = d := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (NQ_conj_d hκ)
  have hom := h.Mg_omega (m := m) hκ.1 hm.symm ![1, 0, 0, 0] ![0, 0, 1, 0]
  rw [hM] at hom
  simp only [Matrix.one_mulVec] at hom
  have h1 : omega4 ![1, 0, 0, 0] ![0, 0, 1, 0] = 1 := by decide
  rw [h1, mul_one] at hom
  have h2 : (m : ZMod 3) = ((1 : ℤ) : ZMod 3) := by rw [← hom]; simp
  have h3 := (ZMod.intCast_eq_intCast_iff m 1 3).mp h2
  have hord : orderOf d = 3 := orderOf_eq_prime h.hd3 h.hd1
  rw [← hm]
  have h4 : d ^ m = d ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, hord]; simpa using h3
  rw [h4, zpow_one]


theorem ker_decomp {κ : G} (hκ : κ ∈ NQ Q d) (hM : Mg d a₀ a₁ f₀ f₁ κ = 1) :
    ∃ q₀ ∈ Q, ∀ y ∈ Q, (q₀⁻¹ * κ) * y * (q₀⁻¹ * κ)⁻¹ = y := by
  have hC := h.hC
  have hκd := h.ker_centralizes_d hκ hM
  have hz : ∀ y ∈ Q, y⁻¹ * (κ * y * κ⁻¹) ∈ Subgroup.zpowers d := by
    intro y hy
    refine h.Phi_eq hy (h.conj_mem hκ.1 hy) ?_
    rw [h.Mg_apply hκ.1 (NQ_conj_d hκ) hy, hM, Matrix.one_mulVec]
  obtain ⟨lam, hlam⟩ : ∃ lam : G → F3, ∀ y, lam y = dl d (y⁻¹ * (κ * y * κ⁻¹)) :=
    ⟨fun y => dl d (y⁻¹ * (κ * y * κ⁻¹)), fun y => rfl⟩
  have hlam_add : ∀ y ∈ Q, ∀ y' ∈ Q, lam (y * y') = lam y + lam y' := by
    intro y hy y' hy'
    have hcomm : y'⁻¹ * (y⁻¹ * (κ * y * κ⁻¹)) = (y⁻¹ * (κ * y * κ⁻¹)) * y'⁻¹ :=
      hC.hzc _ (hz y hy) y'⁻¹ (Q.inv_mem hy')
    have e : (y * y')⁻¹ * (κ * (y * y') * κ⁻¹) =
        (y⁻¹ * (κ * y * κ⁻¹)) * (y'⁻¹ * (κ * y' * κ⁻¹)) := by
      calc (y * y')⁻¹ * (κ * (y * y') * κ⁻¹)
          = y'⁻¹ * (y⁻¹ * (κ * y * κ⁻¹)) * (κ * y' * κ⁻¹) := by group
        _ = (y⁻¹ * (κ * y * κ⁻¹)) * y'⁻¹ * (κ * y' * κ⁻¹) := by rw [hcomm]
        _ = (y⁻¹ * (κ * y * κ⁻¹)) * (y'⁻¹ * (κ * y' * κ⁻¹)) := by group
    rw [hlam, hlam, hlam, e, dl_mul hC.hd3 hC.hd1 (hz y hy) (hz y' hy')]
  obtain ⟨w, hw⟩ : ∃ w : V4, w = ![lam f₀, lam f₁, lam a₀ * 2, lam a₁ * 2] := ⟨_, rfl⟩
  have hq₀ : rep d a₀ a₁ f₀ f₁ w ∈ Q := h.rep_mem w
  have hom_q : ∀ y ∈ Q, om d (rep d a₀ a₁ f₀ f₁ w) y = lam y := by
    intro y hy
    refine h.ext_add (fun y => om d (rep d a₀ a₁ f₀ f₁ w) y) lam ?_ hlam_add ?_ ?_ ?_ ?_ ?_ y hy
    · intro x hx y hy
      exact hC.om_add_right hq₀ hx hy
    · show om d (rep d a₀ a₁ f₀ f₁ w) a₀ = lam a₀
      rw [← h.omega4_Phi hq₀ h.ha₀Q, h.Phi_rep, h.Phi_a₀, hw]
      exact (omega4_cons _ _ _ _).1
    · show om d (rep d a₀ a₁ f₀ f₁ w) a₁ = lam a₁
      rw [← h.omega4_Phi hq₀ h.ha₁Q, h.Phi_rep, h.Phi_a₁, hw]
      exact (omega4_cons _ _ _ _).2.1
    · show om d (rep d a₀ a₁ f₀ f₁ w) f₀ = lam f₀
      rw [← h.omega4_Phi hq₀ h.hf₀, h.Phi_rep, h.Phi_f₀, hw]
      exact (omega4_cons _ _ _ _).2.2.1
    · show om d (rep d a₀ a₁ f₀ f₁ w) f₁ = lam f₁
      rw [← h.omega4_Phi hq₀ h.hf₁, h.Phi_rep, h.Phi_f₁, hw]
      exact (omega4_cons _ _ _ _).2.2.2
    · show om d (rep d a₀ a₁ f₀ f₁ w) d = lam d
      rw [hC.om_d_right hq₀, hlam, hκd, inv_mul_cancel, dl_one hC.hd3 hC.hd1]
  refine ⟨rep d a₀ a₁ f₀ f₁ w, hq₀, fun y hy => ?_⟩
  have hzy := hz y hy
  have hcm := hC.hcm y hy _ hq₀
  have hdl : dl d (y⁻¹ * (κ * y * κ⁻¹)) = dl d (cm (rep d a₀ a₁ f₀ f₁ w) y) := by
    rw [← hlam]; exact (hom_q y hy).symm
  have heq : y⁻¹ * (κ * y * κ⁻¹) = cm (rep d a₀ a₁ f₀ f₁ w) y := by
    calc y⁻¹ * (κ * y * κ⁻¹) = d ^ (dl d (y⁻¹ * (κ * y * κ⁻¹))).val :=
          (dl_zpow_val hC.hd3 hC.hd1 hzy).symm
      _ = d ^ (dl d (cm (rep d a₀ a₁ f₀ f₁ w) y)).val := by rw [hdl]
      _ = cm (rep d a₀ a₁ f₀ f₁ w) y := dl_zpow_val hC.hd3 hC.hd1 hcm
  unfold cm at heq
  have heq2 : κ * y * κ⁻¹ = rep d a₀ a₁ f₀ f₁ w * y * (rep d a₀ a₁ f₀ f₁ w)⁻¹ := by
    have := congrArg (fun z => y * z) heq
    simpa using this
  calc (rep d a₀ a₁ f₀ f₁ w)⁻¹ * κ * y * ((rep d a₀ a₁ f₀ f₁ w)⁻¹ * κ)⁻¹
      = (rep d a₀ a₁ f₀ f₁ w)⁻¹ * (κ * y * κ⁻¹) * rep d a₀ a₁ f₀ f₁ w := by group
    _ = y := by rw [heq2]; group

end SympBasis

theorem conj_mem_Y_of_centralizes {L F Q : Subgroup G} {e c : G}
    (hL : L ∈ thetaComponentsAt 3 e)
    (huniq : ∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = L) (h3 : 3 ∣ Nat.card L)
    (heQ : e ∈ Q) (hFQ : F ≤ Q) (hc : ∀ q ∈ Q, c * q * c⁻¹ = q) :
    ∀ y ∈ y2128Of L F Q, c * y * c⁻¹ ∈ y2128Of L F Q := by
  have hce : c ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hc e heQ
    calc c * e = c * e * c⁻¹ * c := by group
      _ = e * c := by rw [this]
  have hLmap : L.map (MulAut.conj c).toMonoidHom = L :=
    huniq _ (Sec6.map_conj_mem_thetaComponentsAt hce hL) (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]; exact h3)
  have hLc : ∀ u ∈ L, c * u * c⁻¹ ∈ L := by
    intro u hu
    rw [← hLmap]
    exact ⟨u, hu, by simp⟩
  have hmain : y2128Of L F Q ≤ (y2128Of L F Q).comap (MulAut.conj c).toMonoidHom := by
    unfold y2128Of
    refine sup_le ?_ ?_
    · intro u hu
      rw [Subgroup.mem_comap]
      have hnorm : c * u * c⁻¹ ∈ Subgroup.normalizer (F : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun f hf => ?_
        have hf' : c⁻¹ * f * c = f := by
          have := hc f (hFQ hf)
          calc c⁻¹ * f * c = c⁻¹ * (c * f * c⁻¹) * c := by rw [this]
            _ = f := by group
        have huf : u * f * u⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hu.2 f).mp hf
        have heq : c * u * c⁻¹ * f * (c * u * c⁻¹)⁻¹ = u * f * u⁻¹ := by
          calc c * u * c⁻¹ * f * (c * u * c⁻¹)⁻¹ = c * (u * (c⁻¹ * f * c) * u⁻¹) * c⁻¹ := by group
            _ = c * (u * f * u⁻¹) * c⁻¹ := by rw [hf']
            _ = u * f * u⁻¹ := hc _ (hFQ huf)
        rw [heq]; exact huf
      exact Subgroup.mem_sup_left (show c * u * c⁻¹ ∈ L ⊓ Subgroup.normalizer (F : Set G) from
        ⟨hLc u hu.1, hnorm⟩)
    · intro q hq
      rw [Subgroup.mem_comap]
      show c * q * c⁻¹ ∈ _
      rw [hc q hq]
      exact Subgroup.mem_sup_right hq
  intro y hy
  exact hmain hy


theorem stage_line {A E U : Subgroup G} {c : G} {L : Subgroup G} {d : G} {U₀ : Subgroup G}
    {a : G} {X : Subgroup G} (hE : Config2119End G A E U c L d U₀ a X)
    (h23 : Concl2123 L X c d) (h24 : Concl2124 A L X d) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))) {F : G → Subgroup G}
    (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hQX : IsExtra2127 (q2127Of A d F))
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    (hL : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
      Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P)
    {a₀ a₁ f₀ f₁ : G} (hS : SympBasis A (q2127Of A d F) d a₀ a₁ f₀ f₁)
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F))) :
    ∃ t₀ t x : G, LineSetup A (q2127Of A d F) (CFSG.Open.thompsonSubgroup P) (F e ⊓ Lf e)
      (y2128Of (Lf e) (F e) (q2127Of A d F)) d a₀ a₁ f₀ f₁ e t₀ t x ∧
      ∀ κ ∈ NQ (q2127Of A d F) d, Mg d a₀ a₁ f₀ f₁ κ = 1 →
        ∀ y ∈ y2128Of (Lf e) (F e) (q2127Of A d F),
          κ * y * κ⁻¹ ∈ y2128Of (Lf e) (F e) (q2127Of A d F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t₀, ht₀Y, -, -, ht₀D⟩ := item2119EndShareTWeak_holds G A E U c L d U₀ a X hE h23 h24 Lf
    hLf h26 F hF h27 hQ hQX h28 hL e he hed P hP
  have hL' := hL e he hed P hP
  have hLine := Hering2119S.lineAbs_of_config hE hLf h26 hF h27 hQ hQX h28 he hed hL'
  set Q := q2127Of A d F with hQdef
  set Y := y2128Of (Lf e) (F e) Q with hYdef
  set D := CFSG.Open.thompsonSubgroup P with hDdef
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQ.2.2.1] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((hF e he hed).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF27 : Nat.card (F e) = 27 := (hF e he hed).2.1
  have hdF : d ∈ F e := Item2119End2Proof.mem_of_isQOf2127 hA27 hF27 hFc (hAFQ e he hed)
    (hQ.2.2.2.2 e he hed).1 hQ.2.1 hdA hdc
  have hdL : d ∈ Lf e := (hLf e he hed).2.2.2.2.1
  have hdD : d ∈ D := hL'.2.2.2 ⟨hdF, hdL⟩
  have hDY : D ≤ Y := (Item2119End8Proof.thompsonSubgroup_le P).trans hP.le
  have hTD : TData A Q D (F e ⊓ Lf e) Y d e t₀ :=
    { hAe := hAe, hA27 := hA27, hdA := hdA, hd1 := hd1, hQX := hQX, hQS := hQ.1
      hAQ := le_sup_left.trans (hAFQ e he hed), hQC := hQ.2.1, hdc := hdc, heA := he, hed := hed
      hDe := hL'.1, hD81 := hL'.2.1, hdD := hdD, hDY := hDY, hQY := le_sup_right
      hLA := hLine
      h729 := fun R hR3 hRY => Item2119End8Proof.card_le_729 hAe hA27 h27 hQ hF h28 he hed hR3 hRY
      hrank := fun b hb hbd X hX3 hXc hXC =>
        Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 hb hbd hX3 hXc hXC
      ht₀Y := ht₀Y, ht₀D := ht₀D }
  obtain ⟨t, htY, htNP, htN, htC, -, htD⟩ := hTD.exists_t'
  have hx : ∃ x ∈ D, x ∉ Q := by
    by_contra hall
    push Not at hall
    have h1 : D ⊓ Q = D := inf_eq_left.mpr hall
    have h27' := hTD.card_QD.2
    rw [h1, hL'.2.1] at h27'
    norm_num at h27'
  obtain ⟨x, hxD, hxQ⟩ := hx
  have hFQ : F e ≤ Q := (le_sup_right : F e ≤ A ⊔ F e).trans (hAFQ e he hed)
  have hMQ : F e ⊓ Lf e ≤ Q := inf_le_left.trans hFQ
  have hLe := hLf e he hed
  have hfus : ∀ m ∈ F e ⊓ Lf e, ∃ w : G, w * e * w⁻¹ = e ∧
      w * m * w⁻¹ ∈ Subgroup.zpowers d := by
    intro m hm
    by_cases hm1 : m = 1
    · refine ⟨1, by group, ?_⟩
      rw [hm1]
      simpa using Subgroup.one_mem (Subgroup.zpowers d)
    · obtain ⟨w, hwL, hw⟩ := (Item2119End8Proof.facts_H (hF e he hed) hLe h26
        (h28 e he hed)).2 m hm d ⟨hdF, hdL⟩ hm1 hd1
      have hwC := Sec6.le_centralizer_of_mem_thetaComponentsAt hLe.1 hwL.1
      have hwe := Subgroup.mem_centralizer_singleton_iff.mp hwC
      refine ⟨w, ?_, ?_⟩
      · calc w * e * w⁻¹ = e * w * w⁻¹ := by rw [hwe]
          _ = e := by group
      · rw [hw]; exact Subgroup.mem_zpowers d
  have h81 : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ R : Subgroup G, IsPGroup 3 R →
      R ≤ Subgroup.centralizer ({b} : Set G) → Nat.card R ≤ 81 := by
    intro b hb hbd R hR3 hRC
    have h1 := Item2119End6Proof.card_le_three_pow_of_isPGroup hRC hR3
    rwa [← (h27 b hb hbd).card_eq, (hQ.2.2.2.2 b hb hbd).1] at h1
  refine ⟨t₀, t, x, ⟨hS, hTD, hxD, hxQ, htN, ?_, htD, ?_, hMQ, hfus, h81⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp htC
  · intro b hb
    exact hTD.delta_mem htY htNP htD hb
  · intro κ hκ hκM y hy
    obtain ⟨q₀, hq₀, hcq⟩ := hS.ker_decomp hκ hκM
    have hy' := conj_mem_Y_of_centralizes hLe.1 hLe.2.2.1 hLe.2.1 (hTD.hAQ he) hFQ hcq y hy
    have e1 : κ * y * κ⁻¹ = q₀ * ((q₀⁻¹ * κ) * y * (q₀⁻¹ * κ)⁻¹) * q₀⁻¹ := by group
    rw [e1]
    have hQY : Q ≤ Y := le_sup_right
    exact Y.mul_mem (Y.mul_mem (hQY hq₀) hy') (Y.inv_mem (hQY hq₀))

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

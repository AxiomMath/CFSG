module

public import CFSG.Quasithin.Background.S1549DBr
public import CFSG.Quasithin.Background.S1549DA6Geo

public section

namespace CFSG.Quasithin

namespace S1549E

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
open scoped commutatorElement Pointwise

@[expose] def ERankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    LCtx hb od L → Y0 T Mc M ≤ conjClosure L T → ∀ e : ℕ, 1 < e →
      IsLieOver2e ↥(StarOf T M V₁ H L) e →
        conjClosure L T = L ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
          Nonempty (↥(StarOf T M V₁ H L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))

@[expose] def L2OffenderNatural : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X L S Q B : Subgroup (MulAut V)) (K : Type) [Field K] [Finite K] (e : ℕ), 2 ≤ e →
      Nat.card K = 2 ^ e → Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) → L ≤ X →
      (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) → IsSylowTwoOf S X → X ≤ L ⊔ S → pCoreOf 2 X = ⊥ →
      B51Hyp (ffJ X) L → S ≤ Q → Q ≤ X → IsFFStarOffender X B → B ≤ pCoreOf 2 Q →
      ∀ y ∈ Q ⊓ L, orderOf y = 3 → ∀ u ∈ commV L, y u = u → u ∈ fixV L

theorem exists_finset_card_four_EB {K : Type} [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
  exact ⟨s, hs⟩

theorem isQuasisimple_SL2_EB {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have h4' := exists_finset_card_four_EB h4
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4')
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4')
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  simp only [not_exists, not_not] at hab
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) K) ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (Matrix.SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isQuasisimple_of_equiv_EB {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y :=
  h.of_mulEquiv e.symm

theorem isQuasisimple_of_equiv_statedSL_two_EB {Y : Type} [Group Y] {K : Type} [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) :
    CFSG.IsQuasisimple Y :=
  isQuasisimple_of_equiv_EB e.symm (isQuasisimple_of_equiv_EB
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K) (isQuasisimple_SL2_EB h4))

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem starHom_Y0_zvec {H : Subgroup G}
    (h : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {a : G} (haS : a ∈ ZS153 T M V₁) {x : ↥H} (hx : (x : G) ∈ Y0 T Mc M) :
    starHom h x (vecOf h a (le_conjClosure _ _ haS)) = vecOf h a (le_conjClosure _ _ haS) := by
  rw [starHom_vecOf, vecOf_eq_vecOf_iff]
  have hc : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := (Y0_le T Mc M hx).2
  have haV : a ∈ VZ T M := (inf_le_left : ZS153 T M V₁ ≤ VZ T M) haS
  have hcomm : (x : G) * a = a * (x : G) :=
    (Subgroup.mem_centralizer_iff.mp hc a haV).symm
  have e : (x : G) * a * (x : G)⁻¹ = a := by
    rw [hcomm]
    group
  rw [e]
  simp

section Endgame

variable {V : Type} [CommGroup V] [Finite V]

theorem e_endgame (hEb : L2OffenderNatural) (hV : ∀ v : V, v ^ 2 = 1)
    {X L S Q B : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K] {e : ℕ} (he : 2 ≤ e)
    (hK : Nat.card K = 2 ^ e) (hiso : Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)))
    (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hS : IsSylowTwoOf S X)
    (hXLS : X ≤ L ⊔ S) (hO2 : pCoreOf 2 X = ⊥) (hB51 : B51Hyp (ffJ X) L) (hSQ : S ≤ Q) (hQX : Q ≤ X)
    (hoff : IsFFStarOffender X B) (hBQ : B ≤ pCoreOf 2 Q) {z : V} (hzS : ∀ s ∈ S, s z = z)
    (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤) {y : MulAut V} (hyQ : y ∈ Q ⊓ L)
    (hy3 : orderOf y = 3) (hyz : y z = z) : False := by
  classical
  have htop := commV_L_sup_fixV_L_eq_top hV hLX hLn hS hXLS hzS hgen
  obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top z)
  have hycfix : y c = c := hc y hyQ.2
  have hyu : y u = u := by
    have h1 : y (u * c) = u * c := by
      rw [huc]
      exact hyz
    rw [map_mul, hycfix] at h1
    exact mul_right_cancel h1
  have hufix : u ∈ fixV L :=
    hEb V hV X L S Q B K e he hK hiso hLX hLn hS hXLS hO2 hB51 hSQ hQX hoff hBQ y hyQ hy3 u hu hyu
  have hzfix : z ∈ fixV L := by
    rw [← huc]
    exact (fixV L).mul_mem hufix hc
  have hfix : fixV L = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hgen, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact S1549D.fixV_invariant hLn hg hzfix
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3
    omega
  apply hy1
  apply MulEquiv.ext
  intro v
  exact (hfix ▸ Subgroup.mem_top v : v ∈ fixV L) y hyQ.2

end Endgame

theorem _root_.CFSG.Quasithin.S1549C.input49E_of_named_inputs
    (hEa : ERankOne) (hEb : L2OffenderNatural) : S1549C.Input49E := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L lctx hk e' he' hLie
  classical
  obtain ⟨heq, K, hKf, hKfin, hKc, ⟨iso⟩⟩ :=
    hEa G T Mc M V₁ V₂ t cx H hb W B od L lctx hk e' he' hLie
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hLH : L ≤ H := (le_of_mem_cComp lctx.comp).trans (preStar_le _ _)
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := le_sup_left.trans hb.adm.hY0
  have hY0L : Y0 T Mc M ≤ L := hk.trans (le_of_eq heq)
  have hHeq : H = L ⊔ T := by
    calc H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := lctx.eq
      _ = L ⊔ Y0 T Mc M ⊔ T := by rw [heq]
      _ = L ⊔ T := by rw [sup_eq_left.mpr hY0L]
  have hTnL : ∀ y ∈ T, ∀ l' ∈ L, y * l' * y⁻¹ ∈ L := fun y hy l' hl' =>
    heq ▸ mem_conjClosure hy hl'
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hHeq]
    refine sup_le Subgroup.le_normalizer ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hTnL x hx l hl, fun hl => by simpa [mul_assoc] using hTnL x⁻¹ (T.inv_mem hx) _ hl⟩
  have iso' : Nonempty (↥(starOfSub h L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) := by
    rw [← starOf_eq_starOfSub cx hb hLH]
    exact ⟨iso⟩
  obtain ⟨iso''⟩ := iso'
  have h4 : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) he'
  have hLq : CFSG.IsQuasisimple ↥(starOfSub h L) := isQuasisimple_of_equiv_statedSL_two_EB h4 iso''
  have hLs : SQTKGroup ↥(starOfSub h L) := sqtkGroup_starOfSub cx hb hLH
  have hLX : starOfSub h L ≤ starOfSub h H := starOfSub_mono h hLH
  have hXLS : starOfSub h H ≤ starOfSub h L ⊔ starOfSub h T := by
    rw [congrArg (starOfSub h) hHeq, starOfSub_sup h hLH hTH]
  have hLn : ∀ x ∈ starOfSub h H, ∀ l ∈ starOfSub h L, x * l * x⁻¹ ∈ starOfSub h L := by
    intro x hx l hl
    obtain ⟨x', -, rfl⟩ := (mem_starOfSub h).mp hx
    obtain ⟨l', hl'L, rfl⟩ := (mem_starOfSub h).mp hl
    refine (mem_starOfSub h).mpr ⟨x' * l' * x'⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hHL x'.2) (l' : G)).mp hl'L
    simpa using this
  have hS : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
    rw [starOfSub_H h]
    exact isSylowTwoOf_starOfSub_T h
  have hO2 : pCoreOf 2 (starOfSub h H) = ⊥ := pCoreOf_starOfSub_H h
  have hLJ := starOfSub_le_ffJ cx hb od lctx
  have hB51 := b51Hyp_ffJ (V := UTil T M V₁ H) hLn hLq hLs hS hXLS hO2 hLJ
  have hQX : starOfSub h (Y0 T Mc M ⊔ T) ≤ starOfSub h H := starOfSub_mono h (sup_le hY0H hTH)
  have hSQ : starOfSub h T ≤ starOfSub h (Y0 T Mc M ⊔ T) := starOfSub_mono h le_sup_right
  have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
    have := od.off
    rwa [starOf_eq_starOfSub cx hb le_rfl] at this
  have hWH : W ≤ H := (od.W_le.trans (pCoreOf_le 2 _)).trans (sup_le hY0H hTH)
  have hBQ : B ≤ pCoreOf 2 (starOfSub h (Y0 T Mc M ⊔ T)) := by
    have h1 : B ≤ starOfSub h (pCoreOf 2 (Y0 T Mc M ⊔ T)) := by
      have := od.B_le
      rw [starOf_eq_starOfSub cx hb hWH] at this
      exact this.trans (starOfSub_mono h od.W_le)
    exact h1.trans (starOfSub_pCoreOf_le h (sup_le hY0H hTH))
  obtain ⟨a, haS, haZ⟩ := exists_zvec cx.c
  have hzS : ∀ s ∈ starOfSub h T, s (vecOf h a (le_conjClosure _ _ haS)) =
      vecOf h a (le_conjClosure _ _ haS) := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := (mem_starOfSub h).mp hs
    exact starHom_T_zvec cx.c h haS hxT
  have hgen : Subgroup.closure {v | ∃ g ∈ starOfSub h H,
      g (vecOf h a (le_conjClosure _ _ haS)) = v} = ⊤ := by
    have := closure_orbit_zvec cx.c h haS haZ
    rwa [← starOfSub_H h] at this
  have h3 : ∃ y₀ : G, y₀ ∈ M ⊓ H ∧ orderOf y₀ = 3 := by
    by_contra hno
    push Not at hno
    have hθ : thetaOf (M ⊓ H) = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hx, hx3⟩
      exact absurd hx3 (hno x hx)
    have hY0 : Y0 T Mc M = ⊥ := hb.claimB.trans hθ
    have hcomm : L = ⁅L, Y0 T Mc M⁆ := lctx.comm
    rw [hY0, Subgroup.commutator_bot_right] at hcomm
    exact ne_bot_of_mem_cComp lctx.comp hcomm
  obtain ⟨y₀, hy₀MH, hy₀3⟩ := h3
  have hy₀Y : y₀ ∈ Y0 T Mc M := by
    rw [hb.claimB]
    exact Subgroup.subset_closure ⟨hy₀MH, hy₀3⟩
  have hy₀H : y₀ ∈ H := hy₀MH.2
  let x₀ : ↥H := ⟨y₀, hy₀H⟩
  have hyL : starHom h x₀ ∈ starOfSub h L := (mem_starOfSub h).mpr ⟨x₀, hY0L hy₀Y, rfl⟩
  have hyQ : starHom h x₀ ∈ starOfSub h (Y0 T Mc M ⊔ T) :=
    (mem_starOfSub h).mpr ⟨x₀, (le_sup_left : Y0 T Mc M ≤ Y0 T Mc M ⊔ T) hy₀Y, rfl⟩
  have hy1 : starHom h x₀ ≠ 1 := by
    intro h1
    have hq : (x₀ : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h x₀).mp h1
    obtain ⟨k, hk2⟩ := pCoreOf_isPGroup 2 H ⟨(x₀ : G), hq⟩
    have hpow : y₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk2
    have hdvd : 3 ∣ 2 ^ k := hy₀3 ▸ orderOf_dvd_of_pow_eq_one hpow
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hy3 : orderOf (starHom h x₀) = 3 := by
    have hx3 : x₀ ^ 3 = 1 := by
      apply Subtype.ext
      show y₀ ^ 3 = 1
      rw [← hy₀3]
      exact pow_orderOf_eq_one y₀
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hy1
  have hyz := starHom_Y0_zvec (Mc := Mc) h haS (x := x₀) hy₀Y
  exact e_endgame hEb hV he' hKc ⟨iso''⟩ hLX hLn hS hXLS hO2 hB51 hSQ hQX hoff hBQ hzS hgen
    ⟨hyQ, hyL⟩ hy3 hyz

end S1549E

end CFSG.Quasithin

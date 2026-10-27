module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOFix
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

theorem frameSignSwap_mem_gspFixPerp (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    frameSignSwap Q e u c t a ∈ gspFixPerp (QuadraticMap.polarBilin Q) (U a) := by
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have hw : u a + (e a : V ≃ₗ[F] V) (u a) ∈ U a :=
    add_mem (hF.mem a) (hF.maps_to a (u a) (hF.mem a))
  have hT : frameSignSwap Q e u c t a =
      Tsp hB (u a + (e a : V ≃ₗ[F] V) (u a)) (t * c)⁻¹ := rfl
  rw [hT]
  exact Tsp_mem_gspFixPerp hB hw (t * c)⁻¹

theorem frameSignSwap_mul_self (a : Fin k) :
    frameSignSwap Q e u c t a * frameSignSwap Q e u c t a = 1 := by
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have hT : frameSignSwap Q e u c t a =
      Tsp hB (u a + (e a : V ≃ₗ[F] V) (u a)) (t * c)⁻¹ := rfl
  rw [hT]
  exact Tsp_mul_self hB _ _

theorem frameSignSwap_app_u (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    (frameSignSwap Q e u c t a).app (u a) = (e a : V ≃ₗ[F] V) (u a) := by
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  have hBuw : polarBilin Q (u a) (u a + (e a : V ≃ₗ[F] V) (u a)) = t * c := by
    rw [map_add, hB.self_eq_zero, zero_add, polarBilin_apply_apply]
    exact hF.polar_eq a
  have hT : frameSignSwap Q e u c t a =
      Tsp hB (u a + (e a : V ≃ₗ[F] V) (u a)) (t * c)⁻¹ := rfl
  rw [hT, Tsp_app, hBuw, inv_mul_cancel₀ htc, one_smul]
  rw [← add_assoc, hV2 (u a), zero_add]

theorem frameSignSwap_app_eu (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    (frameSignSwap Q e u c t a).app ((e a : V ≃ₗ[F] V) (u a)) = u a := by
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  have hBeuw : polarBilin Q ((e a : V ≃ₗ[F] V) (u a))
      (u a + (e a : V ≃ₗ[F] V) (u a)) = t * c := by
    rw [map_add, hB.self_eq_zero, add_zero, polarBilin_apply_apply, polar_comm]
    exact hF.polar_eq a
  have hT : frameSignSwap Q e u c t a =
      Tsp hB (u a + (e a : V ≃ₗ[F] V) (u a)) (t * c)⁻¹ := rfl
  rw [hT, Tsp_app, hBeuw, inv_mul_cancel₀ htc, one_smul]
  rw [add_comm ((e a : V ≃ₗ[F] V) (u a)), add_assoc, hV2 ((e a : V ≃ₗ[F] V) (u a)), add_zero]

theorem frameSignSwap_conj_self (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    frameSignSwap Q e u c t a * omegaToGsp Q (e a) * frameSignSwap Q e u c t a =
      (omegaToGsp Q (e a))⁻¹ := by
  classical
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  let ρ : V ≃ₗ[F] V := (e a : V ≃ₗ[F] V)
  let w : V := u a + ρ (u a)
  let T : Gsp (polarBilin Q) := frameSignSwap Q e u c t a
  have hT : T = Tsp hB w (t * c)⁻¹ := rfl
  have hu : u a ∈ U a := hF.mem a
  have hρu : ρ (u a) ∈ U a := hF.maps_to a (u a) hu
  have hwU : w ∈ U a := add_mem hu hρu
  have hBuw : polarBilin Q (u a) w = t * c := by
    dsimp [w]
    rw [map_add, hB.self_eq_zero, zero_add, polarBilin_apply_apply]
    exact hF.polar_eq a
  have hBρuw : polarBilin Q (ρ (u a)) w = t * c := by
    dsimp [w]
    rw [map_add, hB.self_eq_zero, add_zero, polarBilin_apply_apply, polar_comm]
    exact hF.polar_eq a
  have hTu : T.app (u a) = ρ (u a) := by
    rw [hT, Tsp_app, hBuw, inv_mul_cancel₀ htc, one_smul]
    dsimp [w]
    rw [← add_assoc, hV2 (u a), zero_add]
  have hTρu : T.app (ρ (u a)) = u a := by
    rw [hT, Tsp_app, hBρuw, inv_mul_cancel₀ htc, one_smul]
    dsimp [w]
    rw [add_comm (ρ (u a)) (u a + ρ (u a)), add_assoc, hV2 (ρ (u a)), add_zero]
  have hρinv : ρ⁻¹ (u a) = ρ (u a) + t • u a := by
    refine (LinearEquiv.symm_apply_eq (e := ρ)).2 ?_
    rw [map_add, map_smul, hF.rot a]
    rw [add_comm (t • ρ (u a)) (u a), add_assoc, hV2 (t • ρ (u a)), add_zero]
  have hli : LinearIndependent F ![u a, ρ (u a)] := by
    rw [linearIndependent_fin2]
    constructor
    · intro h0
      have h0' : ρ (u a) = 0 := by simpa using h0
      have h := hF.polar_eq a
      rw [h0', polar_zero_right] at h
      exact htc h.symm
    · intro s hs
      have hs' : s • ρ (u a) = u a := by simpa using hs
      have h := hF.polar_eq a
      have hzero : polar Q (u a) (ρ (u a)) = 0 := by
        have h1 : polar Q (u a) (ρ (u a)) = polar Q (s • ρ (u a)) (ρ (u a)) := by
          congr 1
          exact hs'.symm
        rw [h1, polar_smul_left, polar_self, two_smul, CharTwo.add_self_eq_zero, smul_zero]
      rw [hzero] at h
      exact htc h.symm
  have hspan : Submodule.span F (Set.range ![u a, ρ (u a)]) = U a := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro y hy
      obtain ⟨i, rfl⟩ := hy
      fin_cases i
      · simpa using hu
      · simpa using hρu
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hF.finrank_eq a]
  have hLHSu : (T * omegaToGsp Q (e a) * T).app (u a) = ρ (u a) + t • u a := by
    rw [Gsp.app_mul, Gsp.app_mul, hTu, omegaToGsp_app]
    change T.app (ρ (ρ (u a))) = ρ (u a) + t • u a
    rw [hF.rot a, Gsp.map_add, Gsp.map_smul, hTρu, hTu, add_comm]
  have hLHSρu : (T * omegaToGsp Q (e a) * T).app (ρ (u a)) = u a := by
    rw [Gsp.app_mul, Gsp.app_mul, hTρu, omegaToGsp_app]
    change T.app (ρ (u a)) = u a
    rw [hTρu]
  have hcoe : (((e a)⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) = ρ⁻¹ := by
    simp [ρ]
  have hRHSu : ((omegaToGsp Q (e a))⁻¹).app (u a) = ρ (u a) + t • u a := by
    rw [← map_inv, omegaToGsp_app, hcoe]
    exact hρinv
  have hRHSρu : ((omegaToGsp Q (e a))⁻¹).app (ρ (u a)) = u a := by
    rw [← map_inv, omegaToGsp_app, hcoe]
    exact ρ.symm_apply_apply (u a)
  have hTz : ∀ z ∈ polarPerp Q (U a), T.app z = z := by
    intro z hz
    rw [hT, Tsp_app]
    have hzB : polarBilin Q z w = 0 := by
      rw [polarBilin_apply_apply, polar_comm]
      exact mem_polarPerp_iff.1 hz w hwU
    rw [hzB, mul_zero, zero_smul, add_zero]
  have hωz : ∀ z ∈ polarPerp Q (U a), (omegaToGsp Q (e a)).app z = z := by
    intro z hz
    rw [omegaToGsp_app]
    exact hF.apply_of_perp a z hz
  have hωinvz : ∀ z ∈ polarPerp Q (U a), ((omegaToGsp Q (e a))⁻¹).app z = z := by
    intro z hz
    have h := Gsp.app_inv_app (omegaToGsp Q (e a)) z
    rwa [hωz z hz] at h
  have hstep : ∀ y ∈ Submodule.span F (Set.range ![u a, ρ (u a)]),
      (T * omegaToGsp Q (e a) * T).app y = ((omegaToGsp Q (e a))⁻¹).app y := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ =>
      (T * omegaToGsp Q (e a) * T).app y = ((omegaToGsp Q (e a))⁻¹).app y) ?_ ?_ ?_ ?_ hy
    · rintro y hy
      obtain ⟨i, rfl⟩ := hy
      fin_cases i
      · simpa using hLHSu.trans hRHSu.symm
      · simpa using hLHSρu.trans hRHSρu.symm
    · rw [Gsp.map_zero', Gsp.map_zero']
    · intro y z _ _ hy hz
      rw [Gsp.map_add, Gsp.map_add, hy, hz]
    · intro r y _ hy
      rw [Gsp.map_smul, Gsp.map_smul, hy]
  have hLz : ∀ z ∈ polarPerp Q (U a), (T * omegaToGsp Q (e a) * T).app z = z := by
    intro z hz
    rw [Gsp.app_mul, Gsp.app_mul, hTz z hz, hωz z hz, hTz z hz]
  refine Gsp.ext' fun x => ?_
  change (T * omegaToGsp Q (e a) * T).app x = ((omegaToGsp Q (e a))⁻¹).app x
  have hx : x ∈ U a ⊔ polarPerp Q (U a) := by
    rw [(isCompl_polarPerp (hF.nondeg a)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hy' : y ∈ Submodule.span F (Set.range ![u a, ρ (u a)]) := by
    rw [hspan]
    exact hy
  rw [Gsp.map_add, Gsp.map_add, hstep y hy', hLz z hz, hωinvz z hz]

theorem frameSignSwap_commute_of_ne (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k}
    (hab : b ≠ a) :
    frameSignSwap Q e u c t a * omegaToGsp Q (e b) =
      omegaToGsp Q (e b) * frameSignSwap Q e u c t a := by
  have hB : LinearMap.BilinForm.IsAlt (polarBilin Q) :=
    CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  let w : V := u a + (e a : V ≃ₗ[F] V) (u a)
  let T : Gsp (polarBilin Q) := frameSignSwap Q e u c t a
  have hT : T = Tsp hB w (t * c)⁻¹ := rfl
  have hwU : w ∈ U a :=
    add_mem (hF.mem a) (hF.maps_to a (u a) (hF.mem a))
  have hwperp : w ∈ polarPerp Q (U b) := by
    refine mem_polarPerp_iff.2 fun y hy => ?_
    have h1 : polar Q y (u a) = 0 := hF.perp b a hab y hy (u a) (hF.mem a)
    have h2 : polar Q y ((e a : V ≃ₗ[F] V) (u a)) = 0 :=
      hF.perp b a hab y hy ((e a : V ≃ₗ[F] V) (u a)) (hF.maps_to a (u a) (hF.mem a))
    rw [show w = u a + (e a : V ≃ₗ[F] V) (u a) from rfl, polar_add_right, h1, h2, add_zero]
  have hfix : (omegaToGsp Q (e b)).app w = w := by
    rw [omegaToGsp_app]
    exact hF.apply_of_perp b w hwperp
  refine Gsp.ext' fun x => ?_
  change T.app ((omegaToGsp Q (e b)).app x) = (omegaToGsp Q (e b)).app (T.app x)
  simp only [hT, Tsp_app hB]
  rw [Gsp.map_add, Gsp.map_smul, hfix]
  congr 1
  rw [← Gsp.form_app (omegaToGsp Q (e b)) x w, hfix]

theorem frameSignSwap_conj_torus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hF : IsCoherentFrame Q p U e E u c t)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτ : ∀ j, τ (Pi.mulSingle j (Multiplicative.ofAdd 1)) = e j) (a : Fin k)
    (f : Fin k → Multiplicative (ZMod p)) :
    frameSignSwap Q e u c t a * omegaToGsp Q (τ f) * (frameSignSwap Q e u c t a)⁻¹ =
      omegaToGsp Q (τ (CFSG.StandardType.SpCoord.sgnAut a f)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let T : Gsp (polarBilin Q) := frameSignSwap Q e u c t a
  let L : (Fin k → Multiplicative (ZMod p)) →* Gsp (polarBilin Q) :=
    (MulAut.conj T).toMonoidHom.comp ((omegaToGsp Q).comp (τ : _ →* ↥(orthDerived Q)))
  let R : (Fin k → Multiplicative (ZMod p)) →* Gsp (polarBilin Q) :=
    (omegaToGsp Q).comp (τ.comp (CFSG.StandardType.SpCoord.sgnAut a).toMonoidHom)
  have hLR : L = R := by
    refine CFSG.StandardType.SpCoord.hom_ext_mulSingle (F₁ := L) (F₂ := R) fun j => ?_
    have hL : L (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
        T * omegaToGsp Q (e j) * T⁻¹ := by
      dsimp [L]
      rw [hτ j]
    rw [hL]
    dsimp [R]
    by_cases hja : j = a
    · rw [hja]
      rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_self, map_inv, hτ a, map_inv]
      rw [inv_eq_of_mul_eq_one_right (frameSignSwap_mul_self (Q := Q) (e := e) (u := u)
        (c := c) (t := t) a)]
      exact frameSignSwap_conj_self hQ hF a
    · rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_of_ne (i := a) (j := j) hja, hτ j]
      rw [frameSignSwap_commute_of_ne hF hja, mul_assoc, mul_inv_cancel, mul_one]
  have h := congrArg (fun φ : (Fin k → Multiplicative (ZMod p)) →* Gsp (polarBilin Q) => φ f)
    hLR
  simpa [L, R] using h

theorem sgnAut_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (CFSG.StandardType.SpCoord.sgnAut (p := p) (k := k)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  intro i i' h
  by_contra hne
  have hval := congrArg
    (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) =>
      φ (Pi.mulSingle i (Multiplicative.ofAdd 1))) h
  rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_self,
    CFSG.StandardType.SpCoord.sgnAut_mulSingle_of_ne (i := i') (j := i) hne] at hval
  have hneg : (Pi.mulSingle i (Multiplicative.ofAdd ((-1 : ZMod p))) :
      Fin k → Multiplicative (ZMod p)) = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
    simpa only [← Pi.mulSingle_inv, ← ofAdd_neg] using hval
  exact ZMod.neg_one_ne_one
    (CFSG.StandardType.SpCoord.mulSingle_ofAdd_eq_iff (x := (-1 : ZMod p)) (y := 1)
      (neg_ne_zero.mpr one_ne_zero) hneg).2

theorem omPlusRefl_ne_sgnAut (hp : p.Prime) (x : CFSG.StandardType.OmPlusIdx k) (a : Fin k) :
    CFSG.StandardType.omPlusRefl p x ≠ CFSG.StandardType.SpCoord.sgnAut a := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  have hneg1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hval := congrArg
    (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) =>
      φ (Pi.mulSingle i (Multiplicative.ofAdd 1))) h
  cases s
  · rw [CFSG.StandardType.omPlusRefl_false (p := p) (i := i) (j := j) hij,
      CFSG.StandardType.SpCoord.permAut_mulSingle, Equiv.swap_apply_left] at hval
    by_cases hai : a = i
    · rw [hai] at hval
      rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_self] at hval
      have hneg : (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)) :
          Fin k → Multiplicative (ZMod p)) = Pi.mulSingle i (Multiplicative.ofAdd (-1)) := by
        simpa only [← Pi.mulSingle_inv, ← ofAdd_neg] using hval
      exact absurd (CFSG.StandardType.SpCoord.mulSingle_ofAdd_eq_iff
        (x := (1 : ZMod p)) (y := (-1 : ZMod p)) one_ne_zero hneg).1 (ne_of_lt hij).symm
    · rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_of_ne (i := a) (j := i) (Ne.symm hai)]
        at hval
      exact absurd (CFSG.StandardType.SpCoord.mulSingle_ofAdd_eq_iff
        (x := (1 : ZMod p)) (y := 1) one_ne_zero hval).1 (ne_of_lt hij).symm
  · rw [CFSG.StandardType.omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply,
      MulAut.mul_apply, CFSG.StandardType.SpCoord.permAut_mulSingle, Equiv.swap_apply_left,
      CFSG.StandardType.SpCoord.sgnAut_mulSingle_self, ← Pi.mulSingle_inv,
      CFSG.StandardType.SpCoord.sgnAut_mulSingle_of_ne (i := i) (j := j)
        (Ne.symm (ne_of_lt hij))] at hval
    by_cases hai : a = i
    · rw [hai] at hval
      rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_self] at hval
      have hneg : (Pi.mulSingle j (Multiplicative.ofAdd ((-1 : ZMod p))) :
          Fin k → Multiplicative (ZMod p)) =
          Pi.mulSingle i (Multiplicative.ofAdd ((-1 : ZMod p))) := by
        simpa only [← Pi.mulSingle_inv, ← ofAdd_neg] using hval
      exact absurd (CFSG.StandardType.SpCoord.mulSingle_ofAdd_eq_iff
        (x := (-1 : ZMod p)) (y := (-1 : ZMod p)) hneg1 hneg).1 (ne_of_lt hij).symm
    · rw [CFSG.StandardType.SpCoord.sgnAut_mulSingle_of_ne (i := a) (j := i) (Ne.symm hai)]
        at hval
      have hneg : (Pi.mulSingle j (Multiplicative.ofAdd ((-1 : ZMod p))) :
          Fin k → Multiplicative (ZMod p)) = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
        simpa only [← Pi.mulSingle_inv, ← ofAdd_neg] using hval
      exact absurd (CFSG.StandardType.SpCoord.mulSingle_ofAdd_eq_iff
        (x := (-1 : ZMod p)) (y := 1) hneg1 hneg).1 (ne_of_lt hij).symm

theorem sumElim_omPlusRefl_sgnAut_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (Sum.elim (CFSG.StandardType.omPlusRefl p)
      (CFSG.StandardType.SpCoord.sgnAut (p := p) (k := k))) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hxy : x = y :=
        CFSG.StandardType.omPlusRefl_injective (m := k) hp hp2 (by simpa using h)
      rw [hxy]
    | inr b =>
      exact absurd (by simpa using h)
        (omPlusRefl_ne_sgnAut (k := k) hp x b)
  | inr a =>
    cases y with
    | inl y =>
      exact absurd (by simpa using h.symm)
        (omPlusRefl_ne_sgnAut (k := k) hp y a)
    | inr b =>
      have hab : a = b := sgnAut_injective (k := k) hp hp2 (by simpa using h)
      rw [hab]

end CFSG.StandardType.SpNsRootGen

end

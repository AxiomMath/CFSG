module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rk_le_two_mul_of_singular_omegaPlus
    {W : Type} [CommGroup W] [Finite W]
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F))
    (E : Subgroup W) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE : ∀ x ∈ E, quadPlus 2 F (Multiplicative.toAdd (ψ x)) = 0) :
    rk E ≤ 2 * n := by
  classical
  let φ : ↥E → (Fin 2 ⊕ Fin 2 → F) := fun x => Multiplicative.toAdd (ψ (x : W))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ψ (x : W) = ψ (y : W) := by
      rw [← Multiplicative.ofAdd.injective.eq_iff, ← Multiplicative.ofAdd.injective.eq_iff]
      change Multiplicative.ofAdd (φ x) = Multiplicative.ofAdd (φ y)
      rw [hxy]
    exact Subtype.ext (ψ.injective h1)
  let S : Set (Fin 2 ⊕ Fin 2 → F) := Set.range φ
  have hSq : ∀ v ∈ S, quadPlus 2 F v = 0 := by
    rintro v ⟨x, rfl⟩
    exact hE x x.2
  have hSpol : ∀ u ∈ S, ∀ v ∈ S, QuadraticMap.polar (quadPlus 2 F) u v = 0 := by
    rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
    have hsum : φ (x * y) = φ x + φ y := by
      change Multiplicative.toAdd (ψ ((x : W) * (y : W))) =
        Multiplicative.toAdd (ψ (x : W)) + Multiplicative.toAdd (ψ (y : W))
      rw [map_mul, toAdd_mul]
    have h0 : quadPlus 2 F (φ x + φ y) = 0 := by
      rw [← hsum]
      exact hE (x * y) (x * y).2
    have hx : quadPlus 2 F (φ x) = 0 := hE x x.2
    have hy : quadPlus 2 F (φ y) = 0 := hE y y.2
    rw [QuadraticMap.polar, h0, hx, hy]
    ring
  let U : Submodule F (Fin 2 ⊕ Fin 2 → F) := Submodule.span F S
  have hUQ : ∀ u ∈ U, quadPlus 2 F u = 0 :=
    fun u hu => CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hSq hSpol hu
  have hdim : Module.finrank F U ≤ 2 :=
    CFSG.StandardType.TableBOrth.finrank_le_of_singular_qPlus (m := 2) U hUQ
  have hcard : Nat.card ↥U ≤ 2 ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
    calc (2 ^ n) ^ Module.finrank F U = 2 ^ (n * Module.finrank F U) := by rw [pow_mul]
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  exact rk_le_mul_of_card_le E φ hφinj hE2 U.toAddSubgroup
    (fun x => Submodule.subset_span ⟨x, rfl⟩) hcard

@[expose] def R18_16_3wAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_3 D V₀ V p L h → ((2 * S17.nOf L + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V

section Certified


theorem nonsingular_centralizer_le_case3 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h143 : R18_14_3At D V₀ V p L h)
    (hK : K_Omega4Plus_nonsingPoint)
    (hCV : p ∣ Nat.card (F11.CTilde D.M V₀ V)) {f : ℕ}
    (hf2 : 2 ≤ f)
    (hO : IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 f)
    (hNat : NatOmegaPlus (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadPlus 2 F)))
    (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaPlus
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) F ε ψ)
    (x : IntMod V h.hyp125.isElemAbelian) (hx0 : x.val ∉ V₀)
    (hns : StatedQuadPlus 2 F
      (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem))) ≠ 0) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
    exact (isOmegaPlus_barSub_cong h h1742 hO).2.2.2
  have hL2 : IsL2 (Bar2 (Opp p (centVec H
      (tilOf V₀ V hV x.val x.val_mem)))) f :=
    (h143 f hf2 hO F hF ε ψ hψ x.val x.val_mem hx0).2 (by simpa using hns)
  obtain ⟨P, hPH, hPperf, hPdvd, hPfix⟩ :=
    hK H p f hf2 hO hNat h.p_prime hcong F hF ε ψ hψ
      (tilOf V₀ V hV x.val x.val_mem) (by simpa using hns)
  have hHM : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.X_le_M
  have hPcent : P ≤ ptCent (Mbar D.M V₀ V hV)
      (mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) := by
    refine le_inf (hPH.trans hHM) ?_
    intro e he
    rw [MulAction.mem_stabilizer_iff]
    have h1 := hPfix e he
    simpa [tilOf] using h1
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    omega
  obtain ⟨Q, hQM, hQp, hQc⟩ :=
    exists_noncyclic_cent_of_perfect_bar D h.p_prime h.p_ne_two hV h.hyp125.pairFacts hcase h4
      (IntMod.mk hV ⟨x.val, x.val_mem⟩) hx0 hPcent hPperf hPdvd hCV
  exact centralizer_le_of_noncyclic D h61 h.hp (hQM.trans inf_le_left) hQp hQc
    (fun h1 => hx0 (h1 ▸ V₀.one_mem))
    ⟨1, by simpa using hV.2 x.val x.val_mem⟩ (hQM.trans inf_le_right)

theorem rk_imgTil_le_case3 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h143 : R18_14_3At D V₀ V p L h)
    (hK : K_Omega4Plus_nonsingPoint) (hCV : p ∣ Nat.card (F11.CTilde D.M V₀ V))
    (hs : P18_13_3 D V₀ V p L h) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V h.hyp125.isElemAbelian U) ≤ 2 * S17.nOf L := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  obtain ⟨f, hO, hNat⟩ := hs
  obtain ⟨-, hnof, hf2, -⟩ := isOmegaPlus_barSub_cong h h1742 hO
  obtain ⟨F, hF, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natOmegaPlus hNat
  have htil : ∀ x : IntMod V hV,
      tilOf V₀ V hV x.val x.val_mem = mkTil V₀ V hV x := by
    intro x
    change mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) = mkTil V₀ V hV x
    exact congrArg (mkTil V₀ V hV) (IntMod.val_injective rfl)
  have hSing : ∀ x : IntMod V hV, x.val ∈ U → x.val ∉ V₀ →
      quadPlus 2 F (Multiplicative.toAdd (ψ (mkTil V₀ V hV x))) = 0 := by
    intro x hxU hx0
    by_contra hns
    have hns' : StatedQuadPlus 2 F
        (Multiplicative.toAdd (ψ (tilOf V₀ V hV x.val x.val_mem))) ≠ 0 := by
      rwa [htil x, ← coe_quadPlus]
    exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
      (nonsingular_centralizer_le_case3 D h61 h h1742 h143 hK hCV hf2 hO hNat hFcard
        ε ψ hψ x hx0 hns'))
  have hWtSing : ∀ y ∈ imgTil V₀ V hV U,
      quadPlus 2 F (Multiplicative.toAdd (ψ y)) = 0 := by
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U y).1 hy
    by_cases hx0 : x.val ∈ V₀
    · have h1 : mkTil V₀ V hV x = 1 :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx0
      rw [h1, map_one, toAdd_one]
      simp
    · exact hSing x hxU hx0
  have hrk : rk ↥(imgTil V₀ V hV U) ≤ 2 * f :=
    rk_le_two_mul_of_singular_omegaPlus hFcard ψ _
      (fun y _ => by simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV y) hWtSing
  rw [hnof]
  exact hrk

theorem eighteen_sixteen_three_weak_of_pCV (D : Data G) (h61 : UC6.R6_1 D)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h143 : R18_14_3At D V₀ V p L h)
    (hK : K_Omega4Plus_nonsingPoint) (hCV : p ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    R18_16_3wAt D V₀ V p L h := by
  intro hs
  have hs1 := hs
  obtain ⟨f, hO, hNat⟩ := hs
  obtain ⟨-, hnof, -, -⟩ := isOmegaPlus_barSub_cong h h1742 hO
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) = 4 * S17.nOf L := by
    rw [hnof]
    exact rk_top_eq_four_mul_of_natOmegaPlus hNat
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_rMV_of_forall_rk_imgTil_le D h.hyp125
    (b := 2 * S17.nOf L) (c := 2 * S17.nOf L + mSub V₀) ?_ ?_
  · have hsub := rk_top_vtil_add_mSub V₀ V h.hyp125.isElemAbelian h.hyp125.pairFacts.le
    rw [hrk] at hsub
    omega
  · intro U hUV hUC
    exact rk_imgTil_le_case3 D h61 h h1742 h143 hK hCV hs1 hUV hUC

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

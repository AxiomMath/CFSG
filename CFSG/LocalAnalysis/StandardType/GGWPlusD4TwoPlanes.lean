module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoPieces
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldFrame
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearQuadratic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.SUTB
  CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private theorem grng_finrank_le_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {S : Finset (GL (Fin (2 * 4)) K)}
    (hS : GenPieceSet (polB (coordinateQuadPlus 4 K)) A S)
    {y : GL (Fin (2 * 4)) K} (hy : y ∈ S) :
    finrank K (grng y) ≤ 2 := by
  classical
  let Q := coordinateQuadPlus 4 K
  let B := polB Q
  let V := Fin (2 * 4) → K
  let U := grng y
  have hyA : y ∈ A := hS.mem y hy
  have hy1 : y ≠ 1 := hS.ne_one y hy
  have hU : NondegOn B U := nondegOn_grng hA hyA
  have hpow : glin y ^ 3 = 1 := hA.lin_pow hyA
  have hfix : ∀ u ∈ U, glin y u = u → u = 0 := fun u hu => eq_zero_of_mem_grng hA hyA hu
  have hUinv : ∀ u ∈ U, glin y u ∈ U := grng_inv (hA := hA) (y := y) (a := y) hyA hyA
  have heven : Even (finrank K U) :=
    CFSG.StandardType.TwoThree.even_finrank_of_fpf hK hpow hUinv hfix
  have hpos : 0 < finrank K U := by
    have hne : finrank K U ≠ 0 := by
      intro h0
      exact grng_ne_bot hy1 ((Submodule.finrank_eq_zero).mp h0)
    exact Nat.pos_of_ne_zero hne
  have hge2 : 2 ≤ finrank K U := by
    rcases heven with ⟨k, hk⟩
    omega
  have hnot3 : ¬ 3 ≤ finrank K U := by
    intro hdim
    have hQne : ∃ v ∈ U, Q v ≠ 0 := by
      by_contra h
      push Not at h
      have hUbot : U = ⊥ := by
        refine (Submodule.eq_bot_iff U).mpr fun m hm => ?_
        apply hU m hm
        intro n hn
        have hq := quad_add (Q := Q) n m
        have hnm : n + m ∈ U := U.add_mem hn hm
        have h1 : Q (n + m) = 0 := h _ hnm
        have hn0 : Q n = 0 := h _ hn
        have hm0 : Q m = 0 := h _ hm
        rw [h1, hn0, hm0, zero_add, zero_add] at hq
        simpa [B, polB_apply] using hq.symm
      exact grng_ne_bot hy1 hUbot
    obtain ⟨v, hvU, hvQ⟩ := hQne
    have hv0 : v ≠ 0 := by
      intro h0
      exact hvQ (by rw [h0]; exact map_zero Q)
    set w : V := glin y v with hwdef
    have hwU : w ∈ U := hUinv v hvU
    have hwne : w ≠ 0 := by
      intro hw0
      apply hv0
      have h := congrArg (glin y⁻¹) hw0
      simpa [hwdef, glin_inv_apply] using h
    have hwv : w ≠ v := by
      intro hwv
      rw [hwdef] at hwv
      exact hv0 (hfix v hvU hwv)
    have hquad0 :=
      CFSG.StandardType.TwoThree.sum_apply_eq_zero (K := K) (V := V) hpow hUinv hfix hvU
    have hquad : (v + glin y v) + glin y (glin y v) = 0 := by
      simpa only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, sq]
        using hquad0
    have hnegV : ∀ x : V, -x = x := by
      intro x
      have hxx : x + x = 0 := by
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have h := congrArg (fun a : K => a • x) h2
        simpa [two_smul] using h
      exact neg_eq_of_add_eq_zero_left hxx
    have hx2 : glin y (glin y v) = v + glin y v := by
      have hneg := neg_eq_of_add_eq_zero_right hquad
      exact hneg.symm.trans (hnegV (v + glin y v))
    have hQylin : ∀ x : V, Q (glin y x) = Q x := by
      intro x
      have hyIso : y ∈ matrixIsometries Q := matrixDerived_le_isometries Q (hA.le hyA)
      have h := (mem_matrixIsometries_iff Q y).mp hyIso x
      rw [glin_apply, ← matrixLinearEquiv_apply]
      exact h
    have hQvw : Q (v + w) = Q v := by
      have hvadd : v + w = glin y w := by
        rw [hwdef]
        exact hx2.symm
      rw [hvadd, hQylin w, hwdef, hQylin v]
    have hQw : Q w = Q v := by
      rw [hwdef]
      exact hQylin v
    have hpolar : QuadraticMap.polar Q v w = Q v := by
      have hq := quad_add (Q := Q) v w
      rw [hQvw, hQw] at hq
      rw [CharTwo.add_self_eq_zero, zero_add] at hq
      exact hq.symm
    have hBvw : B v w ≠ 0 := by
      change polB Q v w ≠ 0
      rw [polB_apply, hpolar]
      exact hvQ
    have hBwv : B w v ≠ 0 := by
      have hs : B w v = B v w := hA.symm.eq w v
      rw [hs]
      exact hBvw
    have halt : B.IsAlt := CFSG.SeitzReduction.polarBilin_isAlt Q
    have hG : B v v * B w w - B v w * B w v ≠ 0 := by
      rw [halt v, halt w, zero_mul, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hBvw hBwv)
    obtain ⟨hLfr0, hLsep0⟩ :=
      CFSG.LinearGroups.span_pair_nondegenerate (B := B) (u₁ := v) (u₂ := w) hG
    set L : Submodule K V := Submodule.span K ({v, w} : Set V) with hLdef
    have hLfr : finrank K L = 2 := by simpa [hLdef] using hLfr0
    have hLsep : (B.domRestrict₁₂ L L).SeparatingLeft := by simpa [hLdef] using hLsep0
    have hLnondeg : NondegOn B L := by
      intro m hm horth
      have hm0 : (⟨m, hm⟩ : L) = 0 := by
        apply hLsep
        intro n
        rw [LinearMap.domRestrict₁₂_apply]
        have hs : B m n.1 = B n.1 m := hA.symm.eq m n.1
        rw [hs]
        exact horth n.1 n.2
      exact congrArg Subtype.val hm0
    have hL_sub_U : L ≤ U := by
      rw [hLdef]
      refine Submodule.span_le.mpr ?_
      intro x hx
      rcases (show x = v ∨ x = w from by simpa using hx) with rfl | rfl
      · exact hvU
      · exact hwU
    have hvL : v ∈ L := by
      rw [hLdef]
      exact Submodule.subset_span (by simp)
    have hwL : w ∈ L := by
      rw [hLdef]
      exact Submodule.subset_span (by simp)
    have hL_y_inv : ∀ z ∈ L, glin y z ∈ L := by
      have hmap : Submodule.map (glin y) L ≤ L := by
        rw [hLdef, Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · rw [← hwdef]
          exact hwL
        · rw [hwdef, hx2, ← hwdef]
          exact L.add_mem hvL hwL
      intro z hz
      exact hmap ⟨z, hz, rfl⟩
    have hL_y_pow : ∀ k : ℕ, ∀ z ∈ L, (glin y ^ k) z ∈ L := by
      intro k
      induction k with
      | zero => intro z hz; simpa using hz
      | succ k ih =>
          intro z hz
          rw [pow_succ, Module.End.mul_apply]
          exact ih (glin y z) (hL_y_inv z hz)
    have hLinv : ∀ a ∈ A, ∀ z ∈ L, glin a z ∈ L := by
      intro a ha z hz
      obtain ⟨k, hk⟩ := hS.cyc y hy a ha
      rw [hk z (hL_sub_U hz)]
      have h := hL_y_pow k z hz
      simpa [glin_pow] using h
    obtain ⟨g, hgA, hgL, hgOrth⟩ :=
      GenMax.exists_mem_restrict (hA := hA) (W := L) (c := y) hLnondeg hLinv hyA
    have hLorth_fr : finrank K (L.orthogonalBilin B) = 6 := by
      have h := OrdPFieldNsOm.finrank_add_finrank_orth (B := B) (X := L) hLnondeg
      omega
    have hsup_le : finrank K ↥(U ⊔ L.orthogonalBilin B) ≤ 8 := by
      have h := Submodule.finrank_mono (le_top : U ⊔ L.orthogonalBilin B ≤ ⊤)
      simpa using h
    have hinf_pos : 0 < finrank K ↥(U ⊓ L.orthogonalBilin B) := by
      have hfr := Submodule.finrank_sup_add_finrank_inf_eq U (L.orthogonalBilin B)
      omega
    have hinf_ne : U ⊓ L.orthogonalBilin B ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hinf_pos
      omega
    obtain ⟨z, hzmem, hz0⟩ := (Submodule.ne_bot_iff _).mp hinf_ne
    have hzU : z ∈ U := hzmem.1
    have hzOrth : z ∈ L.orthogonalBilin B := hzmem.2
    have hgz : glin g z = z := hgOrth z hzOrth
    have hgw : glin g w = glin y w := hgL w hwL
    obtain ⟨k, hk⟩ := hS.cyc y hy g hgA
    have hgv : glin g v = glin y v := hgL v hvL
    have hkv : (glin y ^ k) v = glin y v := by
      rw [← glin_pow]
      exact (hk v hvU).symm.trans hgv
    set r : ℕ := k % 3 with hr
    have hrlt : r < 3 := by
      rw [hr]
      exact Nat.mod_lt k (by norm_num)
    have hkpow : (glin y) ^ k = (glin y) ^ r := by
      simpa [hr] using pow_eq_pow_mod k hpow
    have hkrv : (glin y ^ r) v = glin y v := by
      rw [← hkpow]
      exact hkv
    interval_cases r
    · exact hv0 (hfix v hvU hkrv.symm)
    · have hky : glin (y ^ k) = glin y := by
        rw [glin_pow, hkpow, pow_one]
      have hzfix : glin (y ^ k) z = z := (hk z hzU).symm.trans hgz
      rw [hky] at hzfix
      exact hz0 (hfix z hzU hzfix)
    · have hfixw : glin y w = w := by
        rw [hwdef]
        have h := hkrv
        simpa [pow_two, Module.End.mul_apply] using h
      exact hwne (hfix w hwU hfixw)
  exact Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot3)

private theorem grng_finrank_eq_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {S : Finset (GL (Fin (2 * 4)) K)}
    (hS : GenPieceSet (polB (coordinateQuadPlus 4 K)) A S)
    {y : GL (Fin (2 * 4)) K} (hy : y ∈ S) :
    finrank K (grng y) = 2 := by
  classical
  let Q := coordinateQuadPlus 4 K
  let B := polB Q
  let U := grng y
  have hyA : y ∈ A := hS.mem y hy
  have hy1 : y ≠ 1 := hS.ne_one y hy
  have hpow : glin y ^ 3 = 1 := hA.lin_pow hyA
  have hfix : ∀ u ∈ U, glin y u = u → u = 0 := fun u hu => eq_zero_of_mem_grng hA hyA hu
  have hUinv : ∀ u ∈ U, glin y u ∈ U := grng_inv (hA := hA) (y := y) (a := y) hyA hyA
  have heven : Even (finrank K U) :=
    CFSG.StandardType.TwoThree.even_finrank_of_fpf hK hpow hUinv hfix
  have hpos : 0 < finrank K U := by
    have hne : finrank K U ≠ 0 := by
      intro h0
      exact grng_ne_bot hy1 ((Submodule.finrank_eq_zero).mp h0)
    exact Nat.pos_of_ne_zero hne
  have hle : finrank K U ≤ 2 := grng_finrank_le_two hK hA hS hy
  have hge : 2 ≤ finrank K U := by
    rcases heven with ⟨k, hk⟩
    omega
  exact le_antisymm hle hge

theorem genMax_pieces_planes_of_card_27 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {S : Finset (GL (Fin (2 * 4)) K)} (hS : GenPieceSet (polB (coordinateQuadPlus 4 K)) A S)
    (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1) (hcard : Nat.card A = 27) :
    S.card = 3 ∧ (∀ y ∈ S, finrank K (grng y) = 2) ∧
      finrank K ((genPieceSpan S).orthogonalBilin (polB (coordinateQuadPlus 4 K))) = 2 := by
  classical
  let Q := coordinateQuadPlus 4 K
  let B := polB Q
  have hcard3 : S.card = 3 := by
    have h1 := genMax_card_eq_pow_pieces hA hS hterm
    have h2 : 3 ^ S.card = 27 := by rw [← h1]; exact hcard
    have h3 : 3 ^ S.card = 3 ^ 3 := by simpa using h2
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hpiece : ∀ y ∈ S, finrank K (grng y) = 2 := fun y hy =>
    grng_finrank_eq_two hK hA hS hy
  have hspan : finrank K (genPieceSpan S) = 6 := by
    have h := OrdPFieldNsOm.finrank_genPieceSpan (hA := hA) (hS := hS) (r := 2) hpiece
    rw [h]
    omega
  have hnd : NondegOn B (genPieceSpan S) := (GenPieceSet.nondegOn_card hA hS).1
  have horth : finrank K ((genPieceSpan S).orthogonalBilin B) = 2 := by
    have h := OrdPFieldNsOm.finrank_add_finrank_orth (B := B) (X := genPieceSpan S) hnd
    omega
  exact ⟨hcard3, hpiece, by simpa [B, Q] using horth⟩

end CFSG.StandardType

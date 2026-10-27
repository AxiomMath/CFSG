module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGLargeCartanRank
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
import CFSG.LocalAnalysis.StandardType.GGRCCardJoin
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
import TauCeti.GroupTheory.Coxeter.Geometric
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l04fFRC_ord_card_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) := by
    have h := coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)
      (hc.symm ▸ ggIntCartan_E₆)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E6 = (CoxeterMatrix.E₆).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) =
      Nat.card (CoxeterMatrix.E₆).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E6

private theorem l04fFRC_ord_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 :=
    CFSG.LieType.Chevalley.cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) := by
    have h := coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)
      (hc.symm ▸ ggIntCartan_E₇)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E7 = (CoxeterMatrix.E₇).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E7) =
      Nat.card (CoxeterMatrix.E₇).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E7

theorem l04fFRC_ord_card_coxeterF4 :
    Nat.card (CoxeterMatrix.F₄).Group = 1152 := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
      ⟨by decide, fun i => by fin_cases i <;> decide⟩
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .F4 = (CoxeterMatrix.F₄).Group :=
    congrArg CoxeterMatrix.Group hmat
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .F4) =
      Nat.card (CoxeterMatrix.F₄).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.Monster.B.Geometry.card_f4WeylGroup

lemma l04fFRC_card_coxeterG2 : Nat.card (CoxeterMatrix.G₂).Group = 12 := by
  let cs := (CoxeterMatrix.G₂).toCoxeterSystem
  have hs : cs.simple 0 * cs.simple 0 = 1 := cs.simple_mul_simple_self 0
  have ht : cs.simple 1 * cs.simple 1 = 1 := cs.simple_mul_simple_self 1
  have hs1 : cs.simple 0 ≠ 1 := cs.simple_ne_one 0
  have ht1 : cs.simple 1 ≠ 1 := cs.simple_ne_one 1
  have hn : orderOf (cs.simple 0 * cs.simple 1) = 6 := by
    rw [cs.orderOf_simple_mul_simple]
    decide
  have hgen : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set (CoxeterMatrix.G₂).Group) = ⊤ := by
    rw [← cs.subgroup_closure_range_simple]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
    · intro hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by
        have h : i.val = 0 ∨ i.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> simp
  have e : DihedralGroup 6 ≃* (CoxeterMatrix.G₂).Group :=
    TauCeti.dihedralGroupMulEquiv (s := cs.simple 0) (t := cs.simple 1) (n := 6)
      hs ht hs1 ht1 hn hgen
  calc Nat.card (CoxeterMatrix.G₂).Group = Nat.card (DihedralGroup 6) :=
        (Nat.card_congr e.toEquiv).symm
    _ = 12 := by rw [DihedralGroup.nat_card]

private theorem l04fFRC_weyl_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M) {N : ℕ}
    (hcard : Fintype.card ι ≤ N) (hN : 11 ≤ N) :
    Nat.card M.Group ≤ 2 ^ N * N.factorial := by
  by_cases hr : 8 ≤ Fintype.card ι
  · rcases ggRC_card_weyl_le M hM hr with h | ⟨h8, hord⟩
    · calc Nat.card M.Group ≤ 2 ^ Fintype.card ι * (Fintype.card ι).factorial := h
        _ ≤ 2 ^ N * N.factorial :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hcard)
              (Nat.factorial_le hcard)
    · rw [hord]
      have h11 : 696729600 ≤ 2 ^ 11 * Nat.factorial 11 := by norm_num
      exact le_trans h11
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN) (Nat.factorial_le hN))
  · rcases hM with ⟨n, e, hn, hAD⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
    · rcases hAD with hA | hBD
      ·
        have hcardI : Fintype.card ι = n := by
          rw [← Fintype.card_congr e, Fintype.card_fin]
        rw [hcardI] at hcard
        calc Nat.card M.Group = Nat.card (CoxeterMatrix.A n).Group := by
              rw [hA]
              exact Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv
          _ = (n + 1).factorial := l05nK3a_card_coxeterA n
          _ = (n + 1) * n.factorial := Nat.factorial_succ n
          _ ≤ 2 ^ N * N.factorial := by
              refine Nat.mul_le_mul ?_ (Nat.factorial_le hcard)
              calc n + 1 ≤ 2 ^ n := Nat.succ_le_iff.mpr Nat.lt_two_pow_self
                _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hcard
      · rcases hBD with ⟨hn2, hB⟩ | ⟨hn4, hD⟩
        ·
          have hcardI : Fintype.card ι = n := by
            rw [← Fintype.card_congr e, Fintype.card_fin]
          rw [hcardI] at hcard
          calc Nat.card M.Group = Nat.card (CoxeterMatrix.B n).Group := by
                rw [hB]
                exact Nat.card_congr ((CoxeterMatrix.B n).reindexGroupEquiv e).toEquiv
            _ ≤ 2 ^ n * n.factorial := card_coxeterB_le n
            _ ≤ 2 ^ N * N.factorial :=
                Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hcard)
                  (Nat.factorial_le hcard)
        ·
          have hcardI : Fintype.card ι = n := by
            rw [← Fintype.card_congr e, Fintype.card_fin]
          rw [hcardI] at hcard
          calc Nat.card M.Group = Nat.card (ggCoxeterMatrixD n).Group := by
                rw [hD]
                exact Nat.card_congr ((ggCoxeterMatrixD n).reindexGroupEquiv e).toEquiv
            _ ≤ 2 ^ n * n.factorial := by
                calc Nat.card (ggCoxeterMatrixD n).Group ≤ 2 ^ (n - 1) * n.factorial :=
                      SpJoinRefl.card_coxeterD_le n (by omega)
                  _ ≤ 2 ^ n * n.factorial :=
                      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)) le_rfl
            _ ≤ 2 ^ N * N.factorial :=
                Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hcard)
                  (Nat.factorial_le hcard)
    ·
      have hcardI : Fintype.card ι = 6 := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      have hbound : 51840 ≤ 2 ^ N * N.factorial := by
        have h11 : 51840 ≤ 2 ^ 11 * Nat.factorial 11 := by norm_num
        exact le_trans h11
          (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN) (Nat.factorial_le hN))
      calc Nat.card M.Group = Nat.card (CoxeterMatrix.E₆).Group := by
            rw [hE6]
            exact Nat.card_congr ((CoxeterMatrix.E₆).reindexGroupEquiv e).toEquiv
        _ = 51840 := l04fFRC_ord_card_coxeterE6
        _ ≤ 2 ^ N * N.factorial := hbound
    ·
      have hbound : 2903040 ≤ 2 ^ N * N.factorial := by
        have h11 : 2903040 ≤ 2 ^ 11 * Nat.factorial 11 := by norm_num
        exact le_trans h11
          (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN) (Nat.factorial_le hN))
      calc Nat.card M.Group = Nat.card (CoxeterMatrix.E₇).Group := by
            rw [hE7]
            exact Nat.card_congr ((CoxeterMatrix.E₇).reindexGroupEquiv e).toEquiv
        _ = 2903040 := l04fFRC_ord_card_coxeterE7
        _ ≤ 2 ^ N * N.factorial := hbound
    ·
      exfalso
      have hcardI : Fintype.card ι = 8 := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      omega
    ·
      have hbound : 1152 ≤ 2 ^ N * N.factorial := by
        have h11 : 1152 ≤ 2 ^ 11 * Nat.factorial 11 := by norm_num
        exact le_trans h11
          (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN) (Nat.factorial_le hN))
      calc Nat.card M.Group = Nat.card (CoxeterMatrix.F₄).Group := by
            rw [hF4]
            exact Nat.card_congr ((CoxeterMatrix.F₄).reindexGroupEquiv e).toEquiv
        _ = 1152 := l04fFRC_ord_card_coxeterF4
        _ ≤ 2 ^ N * N.factorial := hbound
    ·
      have hbound : 12 ≤ 2 ^ N * N.factorial := by
        have h11 : 12 ≤ 2 ^ 11 * Nat.factorial 11 := by norm_num
        exact le_trans h11
          (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN) (Nat.factorial_le hN))
      calc Nat.card M.Group = Nat.card (CoxeterMatrix.G₂).Group := by
            rw [hG2]
            exact Nat.card_congr ((CoxeterMatrix.G₂).reindexGroupEquiv e).toEquiv
        _ = 12 := l04fFRC_card_coxeterG2
        _ ≤ 2 ^ N * N.factorial := hbound

private theorem l04fFRC_row_dvd {p : ℕ} {labJ labX : LargeEvenLabel}
    (h : ggRowTwoNode p labJ labX) (hr : 10 ≤ labX.rank) : p ∣ labX.rank + 1 := by
  rcases h with ⟨-, -, hdvd, hX⟩ | ⟨-, -, hdvd, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    simpa using hdvd
  · subst hX
    simpa using hdvd
  · subst hX
    simp at hr
  · subst hX
    simp at hr

theorem ggLargeRowCard_of_inputs
    (hOrb : GGResCentBoundInput) (hX : GGResXDichotomyInput)
    (hNoSeven : GGLargeRowNoSevenAtL) (hDim : GGLargeRowDimKnown) : GGLargeRowCard := by
  intro G _ _ p _ B Bs x L D J y K N hH hrow
  change Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs) ≤
    p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial))
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hrow0 : GGResRowAt (ggRowLargeN N) p J K := hrow
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr2, hr10, hrN⟩ := hrow
  have hN : 11 ≤ N := by omega
  have hpN : p ∣ N := by
    have h := l04fFRC_row_dvd hr2 hr10
    rwa [hrN] at h
  have hjoin : Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs) ≤
      Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := by
    rw [sup_comm]
    exact ggRC_card_join_le hOrb hH hx
  have hBs : Nat.card ↥Bs ≤ p ^ N := hDim G p B Bs x L D J y K N hH hrow0
  have hL : GGResXDatum p Bs L := by
    rcases (hX G p B Bs x L D J y K hH).1 with h | h
    · exact h
    · exact absurd h (hNoSeven G p B Bs x L D J y K N hH hrow0)
  obtain ⟨Λ, iΛF, iΛD, M, C, V₀, iVadd, iVmod, ι₀, φ, h, α, hM, hC, hφ, hrefl, hpair,
    ⟨f, hf⟩, hclos⟩ := hL
  let := iΛF
  let := iΛD
  let := iVadd
  let := iVmod
  have hcard_AL : Nat.card ↥(ggAutomizer L Bs) = Nat.card M.Group :=
    (Nat.card_congr f.toEquiv).symm
  have : Finite V₀ := Finite.of_equiv (Additive ↥Bs) ι₀.toEquiv
  have : Module.Finite (ZMod p) V₀ := Module.Finite.of_finite
  have hcardVadd : Nat.card (Additive ↥Bs) = Nat.card V₀ := Nat.card_congr ι₀.toEquiv
  have hcardV : Nat.card V₀ = Nat.card ↥Bs :=
    hcardVadd.symm.trans (Nat.card_congr Additive.toMul)
  have hpow : p ^ Module.finrank (ZMod p) V₀ = Nat.card V₀ :=
    FiniteField.pow_finrank_eq_natCard p V₀
  have h1p : 1 < p := by
    have hpp : p.Prime := Fact.out
    have hp2le : 2 ≤ p := hpp.two_le
    omega
  have hfin_le : Module.finrank (ZMod p) V₀ ≤ N := by
    have hle : p ^ Module.finrank (ZMod p) V₀ ≤ p ^ N := by
      rw [hpow, hcardV]
      exact hBs
    exact (Nat.pow_le_pow_iff_right h1p).mp hle
  have hrank : Fintype.card Λ ≤ N :=
    ggLargeCartan_rank_le hp2 hN hpN hM hC h α hpair hfin_le
  have hweyl : Nat.card M.Group ≤ 2 ^ N * N.factorial :=
    l04fFRC_weyl_card_le M hM hrank hN
  have hAL : Nat.card ↥(ggAutomizer L Bs) ≤ 2 ^ N * N.factorial := by
    rw [hcard_AL]
    exact hweyl
  calc Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs)
      ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := hjoin
    _ ≤ p ^ N * ((p - 1) * 6 * (2 ^ N * N.factorial)) :=
        Nat.mul_le_mul hBs (Nat.mul_le_mul le_rfl hAL)
    _ = p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial)) := by ring

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryHeartAutomizer
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.TableBUE
open CFSG.StandardType.TableBUD CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct
open CFSG.StandardType.InndiagSU CFSG.StandardType.QTwoUnitary
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)


variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem qTwoFramePerm_mem_normalizer_full
    (hd3 : 3 ≤ d) (hdq : (d, 2 ^ 1) ≠ (3, 2))
    (hUnit : ∀ x : Kˣ, ((x : Kˣ) : K) ^ (2 ^ 1 + 1) = 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    (hfr : ∀ e ∈ E, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct h Q hQ e σ)
    (hex : ∀ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 →
      ∃ e ∈ E, TableBUD.FrameAct h Q hQ e σ)
    (π : Equiv.Perm (Fin d)) :
    qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π ∈
      Subgroup.normalizer (E : Set (MulAut
        (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) := by
  classical
  have hmem : ∀ (τ : Equiv.Perm (Fin d)) (e : MulAut
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))), e ∈ E →
      qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹ ∈ E := by
    intro τ e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    let z : Fin d := ⟨0, by omega⟩
    let c : Kˣ := (σ (τ.symm z))⁻¹
    let w : Fin d → Kˣ := fun k => c * σ (τ.symm k)
    have hw0 : w z = 1 := by
      dsimp [w, c, z]
      rw [inv_mul_cancel]
    have hact : TableBUD.FrameAct h Q hQ
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e *
          (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹) w := by
      have h := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
        (hσn := hσn) (he := hfrσ) (π := τ)
      simpa [w, c, Function.comp] using h.smul c
    obtain ⟨e', he', hfr'⟩ := hex w hw0
    have hwn : ∀ k, ((w k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := fun k => hUnit (w k)
    have huniq := TableBUD.FrameAct.unique (K := K) (n := 1) (d := d)
      (h := h) (Q := Q) (hQ := hQ) hwn hact hfr'
    rw [huniq]
    exact he'
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hmem π e he
  · intro he
    have hπinv : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π⁻¹ =
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π)⁻¹ :=
      map_inv (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)) π
    have h := hmem (π⁻¹)
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π * e *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π)⁻¹) he
    simpa [hπinv, mul_assoc] using h

theorem four_dvd_ggAutomizer_frameBlock_full
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 4 ≤ d)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    (hfr : ∀ e ∈ E, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct h Q hQ e σ)
    (hex : ∀ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 →
      ∃ e ∈ E, TableBUD.FrameAct h Q hQ e σ)
    (I : Finset (Fin d)) (hI : 4 ≤ I.card) :
    4 ∣ Nat.card ↥(ggAutomizer
      (((TableBUE.blockSU (K := K) (n := 1) I).map (frameMk h Q hQ)).map
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) E) := by
  classical
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro hcon
    have hd3' : d = 3 := congrArg Prod.fst hcon
    omega
  have h3unit : ∀ x : Kˣ, x ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, hK]
      norm_num
    intro x
    rw [← hcard]
    exact pow_card_eq_one'
  have hUnit : ∀ x : Kˣ, ((x : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro x
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      h3unit x, Units.val_one]
  let z : Fin d := ⟨0, by omega⟩
  obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq hI
  obtain ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, hTeq⟩ :=
    Finset.card_eq_four.mp hTcard
  have haI : a ∈ I := hTI (by rw [hTeq]; simp)
  have hbI : b ∈ I := hTI (by rw [hTeq]; simp)
  have hcI : c ∈ I := hTI (by rw [hTeq]; simp)
  have heI : e ∈ I := hTI (by rw [hTeq]; simp)
  haveI : Nontrivial Kˣ := by
    have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]; norm_num
    exact (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : Kˣ)
  let x : Fin d := if a = z then b else a
  let y : Fin d := if c = z then e else c
  have hxmem : x = a ∨ x = b := by
    dsimp [x]
    split <;> simp
  have hymem : y = c ∨ y = e := by
    dsimp [y]
    split <;> simp
  have hxz : x ≠ z := by
    dsimp [x]
    split_ifs with ha
    · exact fun hbz => hab (ha.trans hbz.symm)
    · exact ha
  have hyz : y ≠ z := by
    dsimp [y]
    split_ifs with hc
    · exact fun hez => hce (hc.trans hez.symm)
    · exact hc
  have hxcd : x ≠ c ∧ x ≠ e := by
    constructor
    · rcases hxmem with hx | hx
      · rw [hx]; exact hac
      · rw [hx]; exact hbc
    · rcases hxmem with hx | hx
      · rw [hx]; exact hae
      · rw [hx]; exact hbe
  have hyab : y ≠ a ∧ y ≠ b := by
    constructor
    · rcases hymem with hy | hy
      · rw [hy]; exact hac.symm
      · rw [hy]; exact hae.symm
    · rcases hymem with hy | hy
      · rw [hy]; exact hbc.symm
      · rw [hy]; exact hbe.symm
  let w0 : Fin d → Kˣ := Function.update (1 : Fin d → Kˣ) x ζ
  let w1 : Fin d → Kˣ := Function.update (1 : Fin d → Kˣ) y ζ
  have hw0z : w0 z = 1 := by
    simp [w0, Function.update, hxz.symm]
  have hw1z : w1 z = 1 := by
    simp [w1, Function.update, hyz.symm]
  have hw0c : w0 c = 1 := by
    simp [w0, Function.update, hxcd.1.symm]
  have hw0e : w0 e = 1 := by
    simp [w0, Function.update, hxcd.2.symm]
  have hw1a : w1 a = 1 := by
    simp [w1, Function.update, hyab.1.symm]
  have hw1b : w1 b = 1 := by
    simp [w1, Function.update, hyab.2.symm]
  have hw0ab : w0 a ≠ w0 b := by
    rcases hxmem with hx | hx
    · simpa [w0, Function.update, hx, hab, hab.symm] using hζ
    · simpa [w0, Function.update, hx, hab, hab.symm] using hζ.symm
  have hw1cd : w1 c ≠ w1 e := by
    rcases hymem with hy | hy
    · simpa [w1, Function.update, hy, hce, hce.symm] using hζ
    · simpa [w1, Function.update, hy, hce, hce.symm] using hζ.symm
  obtain ⟨e0, he0, hfr0⟩ := hex w0 hw0z
  obtain ⟨e2, he2, hfr2⟩ := hex w1 hw1z
  have hmoved1 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap a b) * e0 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap a b))⁻¹ ≠ e0 :=
    qTwoFramePerm_moves_of_weight_ne (h := h) (Q := Q) (hQ := hQ) (E := E)
      he0 hK hd3 hdq (fun k => hUnit (w0 k)) hfr0 hab hw0ab
  have hmoved2 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c e) * e2 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c e))⁻¹ ≠ e2 :=
    qTwoFramePerm_moves_of_weight_ne (h := h) (Q := Q) (hQ := hQ) (E := E)
      he2 hK hd3 hdq (fun k => hUnit (w1 k)) hfr2 hce hw1cd
  have hw0fix : w0 ∘ ⇑(Equiv.swap c e).symm = w0 := by
    funext i
    dsimp only [Function.comp_apply]
    by_cases hic : i = c
    · subst hic
      rw [Equiv.symm_swap, Equiv.swap_apply_left, hw0c, hw0e]
    · by_cases hie : i = e
      · subst hie
        rw [Equiv.symm_swap, Equiv.swap_apply_right, hw0c, hw0e]
      · have hfix : (Equiv.swap c e) i = i := Equiv.swap_apply_of_ne_of_ne hic hie
        rw [Equiv.symm_swap, hfix]
  have hfix2 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c e) * e0 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c e))⁻¹ = e0 := by
    have hact := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
      (hσn := fun k => hUnit (w0 k)) (he := hfr0) (π := Equiv.swap c e)
    rw [hw0fix] at hact
    exact TableBUD.FrameAct.unique (hσ := fun k => hUnit (w0 k)) hact hfr0
  let q := qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
  let s1 := q (Equiv.swap a b)
  let s2 := q (Equiv.swap c e)
  let J0 := ((TableBUE.blockSU (K := K) (n := 1) I).map (frameMk h Q hQ)).map
    (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)) →* MulAut _)
  have hJ1 : s1 ∈ J0 := by
    refine ⟨frameMk h Q hQ (LineU.permSU h (Equiv.swap a b)), ?_, rfl⟩
    refine ⟨LineU.permSU h (Equiv.swap a b), ?_, rfl⟩
    apply UnitAct.permSU_mem_blockSU_of_fixes_compl
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne
      (fun hia => hi (hia.symm ▸ haI)) (fun hib => hi (hib.symm ▸ hbI))
  have hJ2 : s2 ∈ J0 := by
    refine ⟨frameMk h Q hQ (LineU.permSU h (Equiv.swap c e)), ?_, rfl⟩
    refine ⟨LineU.permSU h (Equiv.swap c e), ?_, rfl⟩
    apply UnitAct.permSU_mem_blockSU_of_fixes_compl
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne
      (fun hic => hi (hic.symm ▸ hcI)) (fun hie => hi (hie.symm ▸ heI))
  have hN1 : s1 ∈ Subgroup.normalizer (E : Set _) :=
    qTwoFramePerm_mem_normalizer_full (h := h) (Q := Q) (hQ := hQ) hd3 hdq hUnit
      hfr hex (Equiv.swap a b)
  have hN2 : s2 ∈ Subgroup.normalizer (E : Set _) :=
    qTwoFramePerm_mem_normalizer_full (h := h) (Q := Q) (hQ := hQ) hd3 hdq hUnit
      hfr hex (Equiv.swap c e)
  have hsq1 : s1 * s1 = 1 := by
    change q (Equiv.swap a b) * q (Equiv.swap a b) = 1
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hsq2 : s2 * s2 = 1 := by
    change q (Equiv.swap c e) * q (Equiv.swap c e) = 1
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hnodup : [a, b, c, e].Nodup := by simp [hab, hac, hae, hbc, hbe, hce]
  have hπcomm : Equiv.swap a b * Equiv.swap c e = Equiv.swap c e * Equiv.swap a b :=
    (Equiv.Perm.disjoint_swap_swap hnodup).commute.eq
  have hscomm : s1 * s2 = s2 * s1 := by
    change q (Equiv.swap a b) * q (Equiv.swap c e) = q (Equiv.swap c e) * q (Equiv.swap a b)
    rw [← map_mul, ← map_mul, hπcomm]
  have hs1 : s1 ≠ 1 := by
    intro h
    apply hmoved1
    change s1 * e0 * s1⁻¹ = e0
    simp only [h, one_mul, inv_one, mul_one]
  have hs2 : s2 ≠ 1 := by
    intro h
    apply hmoved2
    change s2 * e2 * s2⁻¹ = e2
    simp only [h, one_mul, inv_one, mul_one]
  have hsne : s1 ≠ s2 := by
    intro h
    apply hmoved1
    change s1 * e0 * s1⁻¹ = e0
    rw [h]
    exact hfix2
  have hker : ∀ x ∈ Subgroup.closure ({s1, s2} : Set _),
      (∀ t ∈ E, x * t * x⁻¹ = t) → x = 1 := by
    intro x hx hcent
    have hc := QTwoCav.closure_pair_eq_four hsq1 hsq2 hscomm hs1 hs2 hsne
    change x ∈ (Subgroup.closure ({s1, s2} : Set _) : Set _) at hx
    rw [hc] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · apply False.elim
      apply hmoved1
      have h := hcent e0 he0
      have heq : (s1 * s2) * e0 * (s1 * s2)⁻¹ = s1 * e0 * s1⁻¹ := by
        calc (s1 * s2) * e0 * (s1 * s2)⁻¹ = s1 * (s2 * e0 * s2⁻¹) * s1⁻¹ := by group
          _ = s1 * e0 * s1⁻¹ := by rw [hfix2]
      exact heq.symm.trans h
    · exact False.elim (hmoved1 (hcent e0 he0))
    · exact False.elim (hmoved2 (hcent e2 he2))
    · rfl
  exact QTwoCav.four_dvd_ggAutomizer_of_two_independent_involutions
    hJ1 hJ2 hN1 hN2 hsq1 hsq2 hscomm hs1 hs2 hsne hker

end CFSG.StandardType.QTwoUnitaryCav

end

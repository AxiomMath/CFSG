module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTorusWeight
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisWeights
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusTwoCoord
public import Lean.Elab.Tactic.Omega
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private lemma spFW_odd_card_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card K - 1) := by
  let F : Fintype K := Fintype.ofFinite K
  have hmod : F.card % 2 = 0 :=
    @FiniteField.even_card_of_char_two K _ F (ringChar.eq K 2)
  have heven : Even (Nat.card K) := by
    rw [@Nat.card_eq_fintype_card K F]
    exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hmod)
  have hle : 1 ≤ Nat.card K := by
    rw [@Nat.card_eq_fintype_card K F]
    exact (@Fintype.card_pos_iff K F).mpr ⟨(0 : K)⟩
  exact Nat.Even.sub_odd hle heven (by norm_num : Odd 1)

private lemma spFW_mcast {K : Type} [Field K] [Finite K] [CharP K 2] :
    ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := by
  let F : Fintype K := Fintype.ofFinite K
  have hle : 1 ≤ Nat.card K := by
    rw [@Nat.card_eq_fintype_card K F]
    exact (@Fintype.card_pos_iff K F).mpr ⟨(0 : K)⟩
  exact Nat.cast_sub hle

private lemma spFW_intCast_spAct {n m : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (f : Fin n → ℤ) :
    (fun c => ((spAct π s f c : ℤ) : ZMod m)) =
      omqSignedAct π s (fun c => (f c : ZMod m)) := by
  funext c
  simp only [spAct, omqSignedAct, Int.cast_mul]

private lemma spFW_not_dvd_of_zmod_ne {m : ℕ} {x y : ℤ}
    (h : (x : ZMod m) ≠ (y : ZMod m)) : ¬ (m : ℤ) ∣ x - y := by
  intro hd
  apply h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  simpa [neg_sub] using (dvd_neg.mpr hd)

private lemma spFW_single_two {n m : ℕ} {e : Fin n → ℤ} {z o : Fin n} (hzo : z ≠ o)
    (he : ∀ c : Fin n, c ≠ z → c ≠ o → e c = 0) :
    (fun c => (e c : ZMod m)) =
      Pi.single z (e z : ZMod m) + Pi.single o (e o : ZMod m) := by
  funext c
  by_cases hcz : c = z
  · subst hcz
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hzo, add_zero]
  · by_cases hco : c = o
    · subst hco
      rw [Pi.add_apply, Pi.single_eq_of_ne hzo.symm, Pi.single_eq_same, zero_add]
    · rw [Pi.add_apply, Pi.single_eq_of_ne hcz, Pi.single_eq_of_ne hco,
        add_zero, he c hcz hco, Int.cast_zero]

open CFSG.StandardType in
private lemma spFW_four_data {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    {e : Fin n → ℤ} (he : ∀ c : Fin n, 2 ≤ c.val → e c = 0)
    (he0 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨0, by omega⟩)
    (he1 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨1, by omega⟩)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ)
      (uZ : Fin 4 → Fin n → ZMod (Nat.card K - 1)),
      (∀ i, SpIsSign (t i)) ∧ Function.Injective uZ ∧
      (∀ i, (fun c => (((spAct (σ i) (t i) e) c : ℤ) : ZMod (Nat.card K - 1))) = uZ i) ∧
      (∀ i j, uZ i ≠ omqSignedAct π s (uZ j)) := by
  classical
  let m : ℕ := Nat.card K - 1
  have hm : Odd m := spFW_odd_card_sub_one
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  have hzo : z ≠ o := by simp [z, o]
  let A : ZMod m := (e z : ZMod m)
  let B : ZMod m := (e o : ZMod m)
  have hA : A ≠ 0 := fun h =>
    he0 (by rw [← spFW_mcast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e z) m).mp h)
  have hB : B ≠ 0 := fun h =>
    he1 (by rw [← spFW_mcast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e o) m).mp h)
  have hx' : (π z = z ∧ s z = -1) ∨ (π z = o ∧ π o = z ∧ s z = s o) := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2, by rw [h3, h4]⟩
  obtain ⟨uZ, huZinj, huZmem, huZmove⟩ :=
    omq_exists_four_orbit_two_coord (n := n) (m := m) hn hm (A := A) (B := B) hA hB
      (a := z) (b := o) hzo hs hx'
  choose σ t ht hprod hact using huZmem
  have he' : ∀ c : Fin n, c ≠ z → c ≠ o → e c = 0 := by
    intro c hcz hco
    apply he c
    have h1 : c.val ≠ 0 := fun h => hcz (Fin.ext h)
    have h2 : c.val ≠ 1 := fun h => hco (Fin.ext h)
    omega
  have hsingle : (fun c => (e c : ZMod m)) = Pi.single z A + Pi.single o B :=
    spFW_single_two hzo he'
  refine ⟨σ, t, uZ, ht, huZinj, ?_, huZmove⟩
  intro i
  rw [← hact i, ← hsingle]
  exact spFW_intCast_spAct (σ i) (t i) e

private lemma spFW_char_inj {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k] {n : ℕ}
    (ι : K →+* k) {uZ : Fin 4 → Fin n → ZMod (Nat.card K - 1)} {uI : Fin 4 → Fin n → ℤ}
    (hcast : ∀ i, (fun c => (uI i c : ZMod (Nat.card K - 1))) = uZ i)
    (huZinj : Function.Injective uZ) :
    Function.Injective (fun i => spTorusChar ι (uI i)) := by
  have hmc : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := spFW_mcast
  intro i j hij
  by_contra hne
  have hzu : uZ i ≠ uZ j := fun h => hne (huZinj h)
  obtain ⟨c, hc⟩ : ∃ c, uZ i c ≠ uZ j c := by
    by_contra h
    push Not at h
    exact hzu (funext h)
  have hne' : (uI i c : ZMod (Nat.card K - 1)) ≠ (uI j c : ZMod (Nat.card K - 1)) := by
    rw [congrFun (hcast i) c, congrFun (hcast j) c]
    exact hc
  exact (spTorusChar_ne_of_not_dvd (a := c) ι (by
    rw [← hmc]
    exact spFW_not_dvd_of_zmod_ne hne')) hij

private lemma spFW_char_move {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k] {n : ℕ}
    (ι : K →+* k) {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    {uZ : Fin 4 → Fin n → ZMod (Nat.card K - 1)} {uI : Fin 4 → Fin n → ℤ}
    (hcast : ∀ i, (fun c => (uI i c : ZMod (Nat.card K - 1))) = uZ i)
    (huZmove : ∀ i j, uZ i ≠ omqSignedAct π s (uZ j)) :
    ∀ i j, spTorusChar ι (uI i) ≠ spTorusChar ι (spAct π s (uI j)) := by
  have hmc : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := spFW_mcast
  intro i j
  have hzu := huZmove i j
  obtain ⟨c, hc⟩ : ∃ c, uZ i c ≠ omqSignedAct π s (uZ j) c := by
    by_contra h
    push Not at h
    exact hzu (funext h)
  have hspj : (fun c => ((spAct π s (uI j) c : ℤ) : ZMod (Nat.card K - 1))) =
      omqSignedAct π s (uZ j) := by
    rw [spFW_intCast_spAct, hcast j]
  have hne' : (uI i c : ZMod (Nat.card K - 1)) ≠
      ((spAct π s (uI j) c : ℤ) : ZMod (Nat.card K - 1)) := by
    rw [congrFun (hcast i) c, congrFun hspj c]
    exact hc
  exact spTorusChar_ne_of_not_dvd (a := c) ι (by
    rw [← hmc]
    exact spFW_not_dvd_of_zmod_ne hne')

open CFSG.StandardType in
private lemma spFW_four_weights {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k]
    {n : ℕ} (hn : 3 ≤ n) (ι : K →+* k) {e : Fin n → ℤ}
    (he : ∀ c : Fin n, 2 ≤ c.val → e c = 0)
    (he0 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨0, by omega⟩)
    (he1 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨1, by omega⟩)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spTorusChar ι (spAct (σ i) (t i) e)) ∧
      ∀ i j, spTorusChar ι (spAct (σ i) (t i) e) ≠
        spTorusChar ι (spAct π s (spAct (σ j) (t j) e)) := by
  obtain ⟨σ, t, uZ, ht, huZinj, hcast, huZmove⟩ := spFW_four_data hn he he0 he1 hs hx
  let uI : Fin 4 → Fin n → ℤ := fun i => spAct (σ i) (t i) e
  have hcastI : ∀ i, (fun c => (uI i c : ZMod (Nat.card K - 1))) = uZ i := hcast
  have hinj : Function.Injective (fun i => spTorusChar ι (uI i)) :=
    spFW_char_inj ι hcastI huZinj
  have hmove : ∀ i j, spTorusChar ι (uI i) ≠ spTorusChar ι (spAct π s (uI j)) :=
    spFW_char_move ι hcastI huZmove
  exact ⟨σ, t, ht, by simpa only [uI] using hinj, by simpa only [uI] using hmove⟩

theorem four_le_finrank_range_sub_one_of_weight {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] (ι : K →+* k) {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k (StatedSp n K) V)
    {e : Fin n → ℤ} (he : ∀ a : Fin n, 2 ≤ a.val → e a = 0)
    (he0 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨0, by omega⟩)
    (he1 : ¬ ((Nat.card K : ℤ) - 1) ∣ e ⟨1, by omega⟩) {v : V} (hv : v ≠ 0)
    (hve : v ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι e)) {y : StatedSp n K}
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  let D := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum n K
  obtain ⟨g, π, s, hs, hx, hgmat⟩ :=
    exists_conj_mat_eq_spMonoPerm (n := n) (by omega) hy hy1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_mat_eq (g := g * y * g⁻¹) hs hgmat
  obtain ⟨σ, t, ht, hinj, hmove⟩ := spFW_four_weights hn ι he he0 he1 hs hx
  choose w hw using fun i => exists_spRealizes_of_spIsSign (σ i) (ht i)
  let wVec : Fin 4 → V := fun i => ρ (D.nW (w i)) v
  have hwv : ∀ i, wVec i ∈ weightSpace (ρ.comp (diagHom n K))
      (spTorusChar ι (spAct (σ i) (t i) e)) :=
    fun i => nW_mem_weightSpace ι ρ (hw i) (ht i) hve
  have hwnz : ∀ i, wVec i ≠ 0 := by
    intro i h0
    apply hv
    have h1 := congrArg (fun z => ρ (D.nW (w i))⁻¹ z) h0
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  have hTv : ∀ i, ρ (D.nW x) (wVec i) ∈ weightSpace (ρ.comp (diagHom n K))
      (spTorusChar ι (spAct π s (spAct (σ i) (t i) e))) :=
    fun i => nW_mem_weightSpace ι ρ hxr hs (hwv i)
  have h4 : 4 ≤ Module.finrank k (LinearMap.range (ρ (D.nW x) - 1)) :=
    le_finrank_range_sub_one_of_weightSpace (ρ.comp (diagHom n K)) (ρ (D.nW x))
      (fun i => spTorusChar ι (spAct (σ i) (t i) e))
      (fun i => spTorusChar ι (spAct π s (spAct (σ i) (t i) e)))
      hinj hmove wVec hwnz hwv hTv
  rw [hxw] at h4
  rw [CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.finrank_range_rep_conj_sub_one ρ g y] at h4
  exact h4

end CFSG.LocalAnalysis.WeakClosure81

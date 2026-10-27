module

public import CFSG.RankThree.PartOne.K1214.PAct
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartOne.K1214

open Finset

section Lift

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem pow_intertwine (red : M →+ N) {a : AddMonoid.End M} {ā : AddMonoid.End N}
    (h : ∀ v, ā (red v) = red (a v)) (n : ℕ) (v : M) : (ā ^ n) (red v) = red ((a ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    show ā ((ā ^ n) (red v)) = red (a ((a ^ n) v))
    rw [ih, h]

end Lift

variable {p : ℕ} {r e : ℕ}

@[expose] def redMod (p r e : ℕ) (he : 1 ≤ e) : (Fin r → ZMod (p ^ e)) →+ (Fin r → ZMod p) :=
  AddMonoidHom.compLeft (ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p)).toAddMonoidHom
    (Fin r)

theorem redMod_apply (he : 1 ≤ e) (v : Fin r → ZMod (p ^ e)) (i : Fin r) :
    redMod p r e he v i = ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) (v i) := rfl

@[expose] def liftMod (p r e : ℕ) (w : Fin r → ZMod p) : Fin r → ZMod (p ^ e) :=
  fun i => ((w i).val : ZMod (p ^ e))

theorem redMod_liftMod [NeZero p] (he : 1 ≤ e) (w : Fin r → ZMod p) :
    redMod p r e he (liftMod p r e w) = w := by
  funext i
  rw [redMod_apply]
  show ZMod.castHom _ (ZMod p) (((w i).val : ℕ) : ZMod (p ^ e)) = w i
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem exists_of_redMod_eq_zero [Fact p.Prime] (he : 1 ≤ e) {v : Fin r → ZMod (p ^ e)}
    (hv : redMod p r e he v = 0) : ∃ u : Fin r → ZMod (p ^ e), v = p • u := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hi : ∀ i, ∃ t : ℕ, (v i).val = p * t := fun i => by
    have h0 := congrFun hv i
    rw [redMod_apply] at h0
    have h1 : (((v i).val : ℕ) : ZMod p) = 0 := by
      have e1 : v i = (((v i).val : ℕ) : ZMod (p ^ e)) := (ZMod.natCast_zmod_val (v i)).symm
      rw [e1, map_natCast] at h0
      exact h0
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  choose t ht using hi
  refine ⟨fun i => (t i : ZMod (p ^ e)), ?_⟩
  funext i
  have : v i = ((v i).val : ZMod (p ^ e)) := (ZMod.natCast_zmod_val (v i)).symm
  rw [this, ht i]
  simp [nsmul_eq_mul]

theorem pd_pow_rank [Fact p.Prime] (he : 1 ≤ e) {δ : AddMonoid.End (Fin r → ZMod (p ^ e))}
    (hg : (1 + δ) ^ p = 1) : PD p 1 (δ ^ r) := by
  classical
  have hp : p.Prime := Fact.out
  set red := redMod p r e he with hred
  have hsurj : Function.Surjective red := fun w => ⟨liftMod p r e w, redMod_liftMod he w⟩
  have hpV : ∀ w : Fin r → ZMod p, p • w = 0 := fun w => by
    funext i
    simp [nsmul_eq_mul]
  have hker : red.ker ≤ (red.comp δ).ker := by
    intro v hv
    obtain ⟨u, rfl⟩ := exists_of_redMod_eq_zero he (AddMonoidHom.mem_ker.1 hv)
    rw [AddMonoidHom.mem_ker]
    show red (δ (p • u)) = 0
    rw [map_nsmul, map_nsmul, hpV]
  let δb : AddMonoid.End (Fin r → ZMod p) :=
    red.liftOfRightInverse (liftMod p r e) (redMod_liftMod he) ⟨red.comp δ, hker⟩
  have hδb : ∀ v, δb (red v) = red (δ v) := fun v =>
    red.liftOfRightInverse_comp_apply (liftMod p r e) (redMod_liftMod he) ⟨red.comp δ, hker⟩ v
  have hδb' : ∀ v, (1 + δb) (red v) = red ((1 + δ) v) := fun v => by
    show red v + δb (red v) = red (v + δ v)
    rw [hδb, map_add]
  have hpowb : (1 + δb) ^ p = 1 := by
    apply AddMonoidHom.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    have h1 := pow_intertwine red hδb' p v
    rw [hg] at h1
    exact h1
  have hz : ∀ x : AddMonoid.End (Fin r → ZMod p), p • x = 0 := fun x =>
    AddMonoidHom.ext fun w => hpV _
  have hpow0 : δb ^ p = 0 := by
    have hbin := one_add_pow_eq hp.two_le δb
    rw [hpowb, Finset.sum_Ico_succ_top hp.two_le, Nat.choose_self, one_smul] at hbin
    have hsum : ∑ j ∈ Finset.Ico 2 p, (p.choose j) • δb ^ j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hj2, hjp⟩ := Finset.mem_Ico.1 hj
      obtain ⟨c', hc'⟩ := hp.dvd_choose_self (by omega) hjp
      rw [hc', mul_smul, hz]
    rw [hsum, hz, zero_add, add_zero] at hbin
    have h1 : (1 : AddMonoid.End (Fin r → ZMod p)) + δb ^ p = 1 + 0 := by
      rw [add_zero]
      exact hbin.symm
    exact add_left_cancel h1
  let δL : Module.End (ZMod p) (Fin r → ZMod p) := AddMonoidHom.toZModLinearMap p δb
  have hδL : ∀ n : ℕ, ∀ w, (δL ^ n) w = (δb ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ']
      show δL ((δL ^ n) w) = δb ((δb ^ n) w)
      rw [ih]
      rfl
  have hδLp : δL ^ p = 0 := LinearMap.ext fun w => by
    rw [hδL, hpow0]
    rfl
  have hker2 : LinearMap.ker (δL ^ p) ≤ LinearMap.ker (δL ^ r) := by
    have := Module.End.ker_pow_le_ker_pow_finrank (K := ZMod p) (V := Fin r → ZMod p) δL p
    rwa [Module.finrank_fin_fun] at this
  have hδLr : δL ^ r = 0 := by
    apply LinearMap.ext
    intro w
    have hw : w ∈ LinearMap.ker (δL ^ p) := by
      rw [hδLp]
      simp
    exact LinearMap.mem_ker.1 (hker2 hw)
  intro v
  have h0 : redMod p r e he ((δ ^ r) v) = 0 := by
    rw [← pow_intertwine red hδb r v, ← hδL r (red v), hδLr]
    rfl
  obtain ⟨u, hu⟩ := exists_of_redMod_eq_zero he h0
  exact ⟨u, by rw [pow_one]; exact hu⟩

theorem exists_of_nsmul_eq_zero [Fact p.Prime] (he : 1 ≤ e) {v : Fin r → ZMod (p ^ e)}
    (hv : p • v = 0) : ∃ y : Fin r → ZMod (p ^ e), v = (p ^ (e - 1)) • y := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hi : ∀ i, ∃ t : ℕ, (v i).val = p ^ (e - 1) * t := fun i => by
    have h0 := congrFun hv i
    have e1 : v i = (((v i).val : ℕ) : ZMod (p ^ e)) := (ZMod.natCast_zmod_val (v i)).symm
    have h1 : ((p * (v i).val : ℕ) : ZMod (p ^ e)) = 0 := by
      have : (p • v) i = p • v i := rfl
      rw [this, e1] at h0
      simpa [nsmul_eq_mul] using h0
    have h2 : p ^ e ∣ p * (v i).val := (ZMod.natCast_eq_zero_iff _ _).1 h1
    have h3 : p * p ^ (e - 1) ∣ p * (v i).val := by
      have : p * p ^ (e - 1) = p ^ e := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]
      exact h2
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos h3
  choose t ht using hi
  refine ⟨fun i => (t i : ZMod (p ^ e)), ?_⟩
  funext i
  have e1 : v i = (((v i).val : ℕ) : ZMod (p ^ e)) := (ZMod.natCast_zmod_val (v i)).symm
  rw [e1, ht i]
  simp [nsmul_eq_mul]

theorem act_lemma_add [Fact p.Prime] (hp5 : 5 ≤ p) (hr : r = 1 ∨ r = 2) (he1 : 1 ≤ e)
    (he : r = 1 ∨ 2 ≤ e) {δ : AddMonoid.End (Fin r → ZMod (p ^ e))} (hg : (1 + δ) ^ p = 1) :
    (∀ v, ∃ w, δ v = (p ^ (e - 1)) • w) ∧ (∀ v, p • v = 0 → δ v = 0) := by
  have hp : p.Prime := Fact.out
  have hexp : ∀ v : Fin r → ZMod (p ^ e), (p ^ e) • v = 0 := fun v => by
    funext i
    simp [nsmul_eq_mul]
  have hH1 : ∀ v : Fin r → ZMod (p ^ e), p • v = 0 → ∃ y, v = (p ^ (e - 1)) • y :=
    fun v hv => exists_of_nsmul_eq_zero he1 hv
  have h1 : PD p 1 (δ ^ r) := pd_pow_rank he1 hg
  have h2 : PD p 1 (δ ^ 2) := by
    rcases hr with rfl | rfl
    · rw [pow_one] at h1
      have := h1.mul h1
      rw [← sq] at this
      exact this.mono (by norm_num)
    · exact h1
  have hδ1 : PD p 1 δ := by
    rcases hr with rfl | rfl
    · rw [pow_one] at h1
      exact h1
    · have he2 : 2 ≤ e := by
        rcases he with h | h
        · omega
        · exact h
      have hodd : Odd p := hp.odd_of_ne_two (by omega)
      obtain ⟨m, hm⟩ := hodd
      refine pd_step (k := 0) hp hH1 (by omega) hg ?_ ?_
      · intro j hj2 _
        have : δ ^ j = δ ^ 2 * δ ^ (j - 2) := by
          rw [← pow_add]
          congr 1
          omega
        rw [this]
        exact (h2.mul (PD.zero_left _)).mono (by norm_num)
      · have hm2 : 2 ≤ m := by omega
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h3 : PD p ((m' + 1) * 1) ((δ ^ 2) ^ (m' + 1)) := h2.pow m'
        have h4 : δ ^ p = (δ ^ 2) ^ (m' + 1) * δ := by
          calc δ ^ p = δ ^ (2 * (m' + 1) + 1) := congrArg (fun n : ℕ => δ ^ n) hm
            _ = δ ^ (2 * (m' + 1)) * δ := pow_succ _ _
            _ = (δ ^ 2) ^ (m' + 1) * δ := by rw [pow_mul]
        rw [h4]
        exact (h3.mul (PD.zero_left δ)).mono (by omega)
  have hmain := pd_induct hp hp5 hH1 hg hδ1
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · by_cases he2 : 2 ≤ e
    · exact hmain (e - 1) (by omega) le_rfl v
    · have : e = 1 := by omega
      subst this
      exact ⟨δ v, by simp⟩
  · by_cases he2 : 2 ≤ e
    · obtain ⟨y, rfl⟩ := hH1 v hv
      obtain ⟨w, hw⟩ := hmain (e - 1) (by omega) le_rfl y
      rw [map_nsmul, hw, ← mul_nsmul', ← pow_add]
      have : p ^ (e - 1 + (e - 1)) = p ^ e * p ^ (e - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, mul_nsmul, hexp w, smul_zero]
    · have he1' : e = 1 := by omega
      obtain ⟨w, hw⟩ := hδ1 v
      have hp1 : p ^ 1 = p ^ e := by rw [he1']
      rw [hw, hp1]
      exact hexp w

end CFSG.RankThree.PartOne.K1214

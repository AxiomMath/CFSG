module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeCartan_rank_le {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 11 ≤ N) (hpN : p ∣ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdim : Module.finrank (ZMod p) V ≤ N) : Fintype.card Λ ≤ N := by
  classical
  by_contra hle
  push Not at hle
  set r : ℕ := Fintype.card Λ with hr
  have hrN : N < r := hle
  let L : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  have hdom : Module.finrank (ZMod p) (Λ → ZMod p) = r := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hrange_le : Module.finrank (ZMod p) L.range ≤ N :=
    (Submodule.finrank_le L.range).trans hdim
  have hker_ge : r - N ≤ Module.finrank (ZMod p) L.ker := by omega
  have hker_ne : L.ker ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod p) L.ker = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨c, hc_mem, hc_ne⟩ := (Submodule.ne_bot_iff L.ker).mp hker_ne
  have hcL : L c = 0 := LinearMap.mem_ker.mp hc_mem
  have hmul : (C.map fun x : ℤ => (x : ZMod p)).mulVec c = 0 := by
    funext j
    have hα : α j (L c) = 0 := by rw [hcL, map_zero]
    rw [Fintype.linearCombination_apply, map_sum] at hα
    rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
    calc ∑ i, (C.map fun x : ℤ => (x : ZMod p)) j i * c i
        = ∑ i, c i * (C j i : ZMod p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.map_apply, mul_comm]
      _ = 0 := by
          simpa only [map_smul, smul_eq_mul, hpair] using hα
  have hdet0 : (C.map fun x : ℤ => (x : ZMod p)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc_ne, hmul⟩
  have hdet : ((C.det : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_det C]
    exact hdet0
  have hp : p.Prime := Fact.out
  have h7 : 7 ≤ Fintype.card Λ := by omega
  obtain ⟨n, e, hn1, hMre⟩ := ggRC_typeA_of_dvd_det hp hp2 hM hC h7 hdet
  have hnr : n = r := by
    have hcard := Fintype.card_congr e
    simp only [Fintype.card_fin] at hcard
    omega
  have hentry : ∀ i j : Fin n, C (e i) (e j) = CartanMatrix.A n i j :=
    ggIndep_cartan_of_reindex e hC hMre
  have hCdet : C.det = (n : ℤ) + 1 := by
    have hCeq : C = (Matrix.reindex e e) (CartanMatrix.A n) := by
      ext a b
      rw [Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [← hentry (e.symm a) (e.symm b)]
      simp
    rw [hCeq, Matrix.det_reindex_self, CartanMatrix.A_det]
  have hp_dvd_n1 : p ∣ n + 1 := by
    have hdvd : (p : ℤ) ∣ C.det := (ZMod.intCast_zmod_eq_zero_iff_dvd C.det p).1 hdet
    rw [hCdet] at hdvd
    exact_mod_cast hdvd
  have hrow : ∀ x : L.ker, ∀ j : Fin n,
      ∑ k : Fin n, (CartanMatrix.A n j k : ZMod p) * (x : Λ → ZMod p) (e k) = 0 := by
    intro x j
    have hα : α (e j) (L x) = 0 := by rw [LinearMap.mem_ker.mp x.2, map_zero]
    rw [Fintype.linearCombination_apply, map_sum] at hα
    have hsum : ∑ i : Λ, (x : Λ → ZMod p) i * (C (e j) i : ZMod p) = 0 := by
      simpa only [map_smul, smul_eq_mul, hpair] using hα
    calc ∑ k : Fin n, (CartanMatrix.A n j k : ZMod p) * (x : Λ → ZMod p) (e k)
        = ∑ k : Fin n, (x : Λ → ZMod p) (e k) * (CartanMatrix.A n j k : ZMod p) := by
          refine Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = ∑ k : Fin n, (x : Λ → ZMod p) (e k) * (C (e j) (e k) : ZMod p) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← hentry j k]
      _ = ∑ i : Λ, (x : Λ → ZMod p) i * (C (e j) i : ZMod p) :=
          Equiv.sum_comp e (fun i : Λ => (x : Λ → ZMod p) i * (C (e j) i : ZMod p))
      _ = 0 := hsum
  have hker_le_one : Module.finrank (ZMod p) L.ker ≤ 1 := by
    by_cases hbot : L.ker = ⊥
    · rw [hbot, finrank_bot]
      omega
    · obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff L.ker).mp hbot
      refine finrank_le_one (R := ZMod p) ⟨v, hv_mem⟩ ?_
      rintro ⟨w, hw_mem⟩
      let v' : Fin n → ZMod p := fun k => (v : Λ → ZMod p) (e k)
      let w' : Fin n → ZMod p := fun k => (w : Λ → ZMod p) (e k)
      have hv'A : ∀ j, ∑ k : Fin n, (CartanMatrix.A n j k : ZMod p) * v' k = 0 := by
        intro j; simpa [v'] using hrow ⟨v, hv_mem⟩ j
      have hw'A : ∀ j, ∑ k : Fin n, (CartanMatrix.A n j k : ZMod p) * w' k = 0 := by
        intro j; simpa [w'] using hrow ⟨w, hw_mem⟩ j
      have hv'ne : v' ≠ 0 := by
        intro hv0
        apply hv_ne
        funext i
        obtain ⟨k, rfl⟩ := e.surjective i
        simpa [v'] using congrFun hv0 k
      obtain ⟨l, hl⟩ := ggCartanA_ker_le_one (p := p) (N := n) v' w' hv'A hw'A hv'ne
      refine ⟨l, ?_⟩
      apply Subtype.ext
      funext i
      obtain ⟨k, rfl⟩ := e.surjective i
      have hk := congrFun hl k
      simpa [v', w', Pi.smul_apply, smul_eq_mul] using hk.symm
  have hr_eq : r = N + 1 := by omega
  have hp_dvd_two : p ∣ 2 := by
    have h1 : p ∣ N + 2 := by
      simpa [hr_eq] using (show p ∣ r + 1 by rw [← hnr]; exact hp_dvd_n1)
    have h2 := Nat.dvd_sub h1 hpN
    simpa using h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp_dvd_two)

end CFSG.StandardType

end

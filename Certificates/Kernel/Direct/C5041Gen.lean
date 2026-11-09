module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs

public section

namespace CertificateChecks.KernelDirect.C5041

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3 CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model
open Equiv Perm

variable {n : ℕ}

theorem keyA_inj {g h : Amb n} (e : keyA n g = keyA n h) : g = h := by
  unfold keyA at e
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp)
  rw [List.map_inj_left] at e1 e2
  exact Prod.ext (Equiv.ext fun i => Fin.ext (e1 i (List.mem_finRange i)))
    (Equiv.ext fun i => Fin.ext (e2 i (List.mem_finRange i)))

def idxIn (el : Vector (Amb n) 64) (g : Amb n) : Fin 64 :=
  ⟨((List.finRange 64).map fun i => keyA n (el.get i)).idxOf (keyA n g) % 64,
    Nat.mod_lt _ (by decide)⟩

theorem get_idxIn (el : Vector (Amb n) 64) (g : Amb n) (k : Fin 64) (hk : el.get k = g) :
    el.get (idxIn el g) = g := by
  have hmem : keyA n g ∈ (List.finRange 64).map fun i => keyA n (el.get i) :=
    List.mem_map.2 ⟨k, List.mem_finRange k, by rw [hk]⟩
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hget := List.getElem_idxOf hlt
  have hlt' : ((List.finRange 64).map fun i => keyA n (el.get i)).idxOf (keyA n g) < 64 := by
    simpa using hlt
  apply keyA_inj
  rw [← hget]
  simp only [idxIn, Nat.mod_eq_of_lt hlt', List.getElem_map, List.getElem_finRange]
  rfl

theorem vget_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) : (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  rfl

theorem mulT_mkTab [NeZero n] (i j : Fin 64) :
    (mkTab n).mulT i j = idxIn (mkTab n).el ((mkTab n).el.get i * (mkTab n).el.get j) := by
  simp only [Tab.mulT, mkTab, vget_ofFn, idxIn]

theorem mulT_mkTab_spec [NeZero n] (hn : n = 6 ∨ n = 7) (h1 : ∀ i, (mkTab n).el.get i ∈ Tl n)
    (h2 : ∀ g ∈ Tl n, ∃ i, (mkTab n).el.get i = g) (i j : Fin 64) :
    (mkTab n).el.get ((mkTab n).mulT i j) = (mkTab n).el.get i * (mkTab n).el.get j := by
  rw [mulT_mkTab]
  have hm : (mkTab n).el.get i * (mkTab n).el.get j ∈ Tl n :=
    (mem_T0_iff n hn _).1 (mul_mem ((mem_T0_iff n hn _).2 (h1 i)) ((mem_T0_iff n hn _).2 (h1 j)))
  obtain ⟨k, hk⟩ := h2 _ hm
  exact get_idxIn _ _ k hk

theorem mem_triples {a b c : Fin n} (h1 : a < b) (h2 : b < c) : (a, b, c) ∈ triples n := by
  simp only [triples, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨a, b, c, by simp [h1, h2]⟩

theorem cyc3_rot {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cyc3 a b c = cyc3 b c a := by
  ext x
  simp only [cyc3, Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem mem_o3_one {p q r : Fin n} (h1 : p < q) (h2 : q < r) :
    cyc3 p q r ∈ o3List n ∧ cyc3 p r q ∈ o3List n := by
  simp only [o3List, List.mem_append, List.mem_flatMap]
  exact ⟨Or.inl ⟨(p, q, r), mem_triples h1 h2, by simp⟩,
    Or.inl ⟨(p, q, r), mem_triples h1 h2, by simp⟩⟩

theorem cyc3_sorted {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p q r : Fin n, p < q ∧ q < r ∧ (p = a ∨ p = b ∨ p = c) ∧ (q = a ∨ q = b ∨ q = c) ∧
      (r = a ∨ r = b ∨ r = c) ∧ (cyc3 a b c = cyc3 p q r ∨ cyc3 a b c = cyc3 p r q) := by
  have r1 := cyc3_rot hab hac hbc
  have r2 := cyc3_rot hbc hab.symm hac.symm
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, by simp, by simp, by simp, Or.inl rfl⟩
  · exact ⟨a, c, b, h2, h3, by simp, by simp, by simp, Or.inr rfl⟩
  · exact absurd (h1.trans h3) (lt_asymm h2)
  · exact ⟨c, a, b, h2, h1, by simp, by simp, by simp, Or.inl (r1.trans r2)⟩
  · exact ⟨b, a, c, h1, h2, by simp, by simp, by simp, Or.inr r1⟩
  · exact absurd (h1.trans h2) (lt_asymm h3)
  · exact ⟨b, c, a, h3, h2, by simp, by simp, by simp, Or.inl r1⟩
  · exact ⟨c, b, a, h3, h1, by simp, by simp, by simp, Or.inr (r1.trans r2)⟩

theorem mem_o3_cyc3 {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cyc3 a b c ∈ o3List n := by
  obtain ⟨p, q, r, h1, h2, -, -, -, e | e⟩ := cyc3_sorted hab hac hbc <;> rw [e]
  · exact (mem_o3_one h1 h2).1
  · exact (mem_o3_one h1 h2).2

theorem mem_o3_two {p q r d e f : Fin n} (h1 : p < q) (h2 : q < r) (h3 : d < e) (h4 : e < f)
    (hpd : p < d) (hpe : p ≠ e) (hpf : p ≠ f) (hqd : q ≠ d) (hqe : q ≠ e) (hqf : q ≠ f)
    (hrd : r ≠ d) (hre : r ≠ e) (hrf : r ≠ f) (x y : Perm (Fin n))
    (hx : x = cyc3 p q r ∨ x = cyc3 p r q) (hy : y = cyc3 d e f ∨ y = cyc3 d f e) :
    x * y ∈ o3List n := by
  simp only [o3List, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨(p, q, r), mem_triples h1 h2, (d, e, f), mem_triples h3 h4, ?_⟩
  rw [if_pos ⟨hpd, hpe, hpf, hqd, hqe, hqf, hrd, hre, hrf⟩]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

theorem mem_o3_cyc3_mul {a b c d e f : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hc : cyc3 a b c * cyc3 d e f = cyc3 d e f * cyc3 a b c) :
    cyc3 a b c * cyc3 d e f ∈ o3List n := by
  obtain ⟨p, q, r, h1, h2, hp, hq, hr, hx⟩ := cyc3_sorted hab hac hbc
  obtain ⟨p', q', r', h3, h4, hp', hq', hr', hy⟩ := cyc3_sorted hde hdf hef
  have ne : ∀ u v : Fin n, (u = a ∨ u = b ∨ u = c) → (v = d ∨ v = e ∨ v = f) → u ≠ v := by
    rintro u v (rfl | rfl | rfl) (rfl | rfl | rfl) <;> assumption
  rcases lt_or_gt_of_ne (ne p p' hp hp') with hpp | hpp
  · exact mem_o3_two h1 h2 h3 h4 hpp (ne _ _ hp hq') (ne _ _ hp hr') (ne _ _ hq hp')
      (ne _ _ hq hq') (ne _ _ hq hr') (ne _ _ hr hp') (ne _ _ hr hq') (ne _ _ hr hr') _ _ hx hy
  · rw [hc]
    exact mem_o3_two h3 h4 h1 h2 hpp (ne _ _ hq hp').symm (ne _ _ hr hp').symm
      (ne _ _ hp hq').symm (ne _ _ hq hq').symm (ne _ _ hr hq').symm (ne _ _ hp hr').symm
      (ne _ _ hq hr').symm (ne _ _ hr hr').symm _ _ hy hx

theorem eq_cyc3 {g : Perm (Fin n)} (hg : g.IsThreeCycle) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ g.support ∧ b ∈ g.support ∧ c ∈ g.support ∧
      g = cyc3 a b c := by
  obtain ⟨a, ha⟩ : g.support.Nonempty := Finset.card_pos.1 (by rw [hg.card_support]; omega)
  have e := hg.eq_swap_mul_swap_iff_mem_support.2 ha
  have nd := hg.nodup_iff_mem_support.2 ha
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at nd
  exact ⟨a, g a, g (g a), nd.1.1, nd.1.2, nd.2, ha, apply_mem_support.2 ha,
    apply_mem_support.2 (apply_mem_support.2 ha), e⟩

theorem mem_o3List (hn : n ≤ 8) (σ : Perm (Fin n)) (h1 : σ ≠ 1) (h3 : σ * σ * σ = 1) :
    σ ∈ o3List n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : σ ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h3
  have hct := cycleType_of_pow_prime_eq_one hp
  have hpos : 0 < Multiset.card σ.cycleType := card_cycleType_pos.2 h1
  have hsum := sum_cycleType_le σ
  rw [hct, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  obtain hk | hk : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 := by omega
  · have h3c : σ.IsThreeCycle := by
      unfold IsThreeCycle
      rw [hct, hk]
      rfl
    obtain ⟨a, b, c, hab, hac, hbc, -, -, -, rfl⟩ := eq_cyc3 h3c
    exact mem_o3_cyc3 hab hac hbc
  · obtain ⟨x, hx⟩ : σ.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, support_eq_empty_iff])
    have hf : σ.cycleOf x ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hx
    have hfc : (σ.cycleOf x).cycleType = {3} := by
      have hle := cycleType_le_of_mem_cycleFactorsFinset hf
      rw [(mem_cycleFactorsFinset_iff.1 hf).1.cycleType] at hle ⊢
      rw [hct, hk, Multiset.singleton_le] at hle
      rw [Multiset.eq_of_mem_replicate hle]
    have hgc : (σ * (σ.cycleOf x)⁻¹).cycleType = {3} := by
      rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub hf, hfc, hct, hk]
      decide
    have hd := disjoint_mul_inv_of_mem_cycleFactorsFinset hf
    obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, ef⟩ := eq_cyc3 (g := σ.cycleOf x) hfc
    obtain ⟨d, e, f, hde, hdf, hef, hd', he, hf', eg⟩ := eq_cyc3 (g := σ * (σ.cycleOf x)⁻¹) hgc
    have ne : ∀ u v : Fin n, u ∈ (σ * (σ.cycleOf x)⁻¹).support → v ∈ (σ.cycleOf x).support →
        u ≠ v := fun u v hu hv h => Finset.disjoint_left.1 hd.disjoint_support hu (h ▸ hv)
    have hcomm := hd.commute.eq
    have key : σ = cyc3 a b c * cyc3 d e f := by
      rw [← ef, ← eg, ← hcomm]
      group
    have hc' : cyc3 a b c * cyc3 d e f = cyc3 d e f * cyc3 a b c := by
      rw [← ef, ← eg]
      exact hcomm.symm
    rw [key]
    exact mem_o3_cyc3_mul hab hac hbc hde hdf hef (ne _ _ hd' ha).symm (ne _ _ he ha).symm
      (ne _ _ hf' ha).symm (ne _ _ hd' hb).symm (ne _ _ he hb).symm (ne _ _ hf' hb).symm
      (ne _ _ hd' hc).symm (ne _ _ he hc).symm (ne _ _ hf' hc).symm hc'

end CertificateChecks.KernelDirect.C5041

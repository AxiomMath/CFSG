module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Refl
public import CFSG.LocalAnalysis.StandardType.GGFrameE78TXLinear
public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

private theorem fe_noncomm_path_stays {n : ℕ} {T P : Set (FEMat n)}
    (hclosed : ∀ a ∈ P, ∀ b ∈ T, a * b ≠ b * a → b ∈ P)
    {r t : FEMat n} (hr : r ∈ P)
    (hpath : Relation.ReflTransGen
      (fun a b => a ∈ T ∧ b ∈ T ∧ a * b ≠ b * a) r t) : t ∈ P := by
  induction hpath with
  | refl => exact hr
  | @tail b c _ hstep ih => exact hclosed b ih c hstep.2.1 hstep.2.2

theorem feTx_endPair_of_connected
    {n : ℕ} (hn : n = 7 ∨ n = 8) {x : FEVec n} (hx : x ≠ 0)
    (hconn : ∀ r ∈ feTx n x, ∀ t ∈ feTx n x,
      Relation.ReflTransGen
        (fun a b => a ∈ feTx n x ∧ b ∈ feTx n x ∧ a * b ≠ b * a) r t) :
    ∃ d : ℕ,
      (∀ r ∈ feTx n x, Set.ncard {t | t ∈ feTx n x ∧ r * t ≠ t * r} = d) ∧
      frameEndPair n (Set.ncard (feTx n x)) (some d) := by
  rcases (frameE78_facts hn).2 x hx with hsplit | ⟨d, hdeg, hpairs⟩
  · obtain ⟨P, Q, hPQ, hdisj, hP, hQ, _, _, hcomm⟩ := hsplit
    obtain ⟨r, hr⟩ := hP
    obtain ⟨t, ht⟩ := hQ
    have hrT : r ∈ feTx n x := hPQ ▸ Set.mem_union_left Q hr
    have htT : t ∈ feTx n x := hPQ ▸ Set.mem_union_right P ht
    have hclosed : ∀ a ∈ P, ∀ b ∈ feTx n x, a * b ≠ b * a → b ∈ P := by
      intro a ha b hb hne
      have hb' : b ∈ P ∪ Q := hPQ.symm ▸ hb
      rcases hb' with hbP | hbQ
      · exact hbP
      · exact (hne (hcomm a ha b hbQ)).elim
    have htP := fe_noncomm_path_stays hclosed hr (hconn r hrT t htT)
    exact (Set.disjoint_left.mp hdisj htP ht).elim
  · exact ⟨d, hdeg, by simpa [frameEndPair] using hpairs⟩

theorem feTx_subset_closure
    {n : ℕ} (hn : n = 7 ∨ n = 8)
    {x : FEVec n} (hx : x ≠ 0) {Tp : Set (FEMat n)}
    (hTp : Tp ⊆ feTx n x)
    (hC : ∀ v : FEVec n, (∀ r ∈ Tp, r.mulVec v = v) →
      ∃ c : ZMod 3, v = c • x)
    (hnorm : ∀ t ∈ feTx n x, ∀ a ∈ Submonoid.closure Tp,
      t * a * t ∈ Submonoid.closure Tp) :
    feTx n x ⊆ (Submonoid.closure Tp : Set (FEMat n)) := by
  intro t ht
  change t ∈ Submonoid.closure Tp
  by_contra htH
  have hcomm : ∀ r ∈ Tp, t * r = r * t := by
    intro r hr
    have hrT : r ∈ feT n := (hTp hr).1
    have hrH : r ∈ Submonoid.closure Tp := Submonoid.subset_closure hr
    rcases (frameE78_facts hn).1 t ht.1 r hrT with heq | hc | hbraid
    · exact (htH (by simpa only [heq] using hrH)).elim
    · exact hc
    · have hrtH := (Submonoid.closure Tp).mul_mem
        ((Submonoid.closure Tp).mul_mem hrH (hnorm t ht r hrH)) hrH
      have heq : r * (t * r * t) * r = t := by
        calc
          r * (t * r * t) * r = (r * r) * t * (r * r) := by
            rw [hbraid]
            simp only [mul_assoc]
          _ = t := by simp only [feT_mul_self hrT, one_mul, mul_one]
      exact (htH (heq ▸ hrtH)).elim
  obtain ⟨v, hv, htv, htline⟩ := feT_negative_line ht.1
  have hfix : ∀ r ∈ Tp, r.mulVec v = v := by
    intro r hr
    have hrT := (hTp hr).1
    have hrne : r ≠ t := by
      intro heq
      exact htH (heq ▸ Submonoid.subset_closure hr)
    exact fe_reflections_commute_fix_negative
      (feT_mul_self hrT) (feT_mul_self ht.1)
      (feT_negative_line hrT) ⟨v, hv, htv, htline⟩
      (hcomm r hr).symm hrne v htv
  obtain ⟨c, hcv⟩ := hC v hfix
  have hc : c ≠ 0 := by
    intro hc
    exact hv (by simpa only [hc, zero_smul] using hcv)
  have htv' : t.mulVec v = v := by
    rw [hcv, Matrix.mulVec_smul, ht.2]
  have hvneg : v = -v := htv'.symm.trans htv
  have hzero : (2 : ZMod 3) • v = 0 := by
    simpa only [two_smul] using (neg_eq_iff_add_eq_zero.mp hvneg.symm)
  have hcxzero : ((2 : ZMod 3) * c) • x = 0 := by
    simpa only [hcv, smul_smul] using hzero
  exact (mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) hc)
    ((smul_eq_zero_iff_left hx).mp hcxzero)

theorem feTx_eq_and_endPair
    {n : ℕ} (hn : n = 7 ∨ n = 8)
    {x : FEVec n} (hx : x ≠ 0) {Tp : Set (FEMat n)}
    (hTp : Tp ⊆ feTx n x)
    (hC : ∀ v : FEVec n, (∀ r ∈ Tp, r.mulVec v = v) →
      ∃ c : ZMod 3, v = c • x)
    (hnorm : ∀ t ∈ feTx n x, ∀ a ∈ Submonoid.closure Tp,
      t * a * t ∈ Submonoid.closure Tp)
    (hfull : ∀ t ∈ feT n, t ∈ Submonoid.closure Tp → t ∈ Tp)
    (hconn : ∀ r ∈ Tp, ∀ t ∈ Tp,
      Relation.ReflTransGen
        (fun a b => a ∈ Tp ∧ b ∈ Tp ∧ a * b ≠ b * a) r t) :
    Tp = feTx n x ∧ ∃ d : ℕ,
      (∀ r ∈ Tp, Set.ncard {t | t ∈ Tp ∧ r * t ≠ t * r} = d) ∧
      frameEndPair n (Set.ncard Tp) (some d) := by
  have hEq : Tp = feTx n x := Set.Subset.antisymm hTp
    (fun t ht => hfull t ht.1 (feTx_subset_closure hn hx hTp hC hnorm ht))
  refine ⟨hEq, ?_⟩
  rw [hEq] at hconn ⊢
  exact feTx_endPair_of_connected hn hx hconn

end CFSG.StandardType.FrameRoute

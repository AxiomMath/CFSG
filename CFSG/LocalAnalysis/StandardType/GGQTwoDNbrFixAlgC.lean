module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlg
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlgB

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def plnf_t {k : ℕ} (j : Fin k) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.swap (Fin.castSucc j) (Fin.succ j)

private lemma plnf_t_comm {k : ℕ} {i j : Fin k} (h : i.val + 2 ≤ j.val) :
    plnf_t i * plnf_t j = plnf_t j * plnf_t i := by
  have hnd : [Fin.castSucc i, Fin.succ i, Fin.castSucc j, Fin.succ j].Nodup := by
    simp [Fin.ext_iff]
    omega
  exact (Equiv.Perm.disjoint_swap_swap hnd).commute

private lemma plnf_t_not_comm {k : ℕ} {j j' : Fin k} (h : j.val + 1 = j'.val) :
    plnf_t j * plnf_t j' ≠ plnf_t j' * plnf_t j := by
  intro hc
  have hne1 : Fin.castSucc j ≠ Fin.castSucc j' := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]
    omega
  have hne2 : Fin.castSucc j ≠ Fin.succ j' := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have e1 : Fin.succ j = Fin.castSucc j' :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  have h2 : (plnf_t j * plnf_t j') (Fin.castSucc j) = Fin.succ j := by
    simp only [plnf_t, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_left]
  have h3 : (plnf_t j' * plnf_t j) (Fin.castSucc j) = Fin.succ j' := by
    simp only [plnf_t, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, e1, Equiv.swap_apply_left]
  have h4 := congrArg (fun σ => σ (Fin.castSucc j)) hc
  simp only [h2, h3] at h4
  have h5 := congrArg Fin.val h4
  simp only [Fin.val_succ] at h5
  omega

private lemma plnf_disjoint_iff {m : ℕ} (c d c' d' : Fin m) :
    Disjoint ({c, d} : Finset (Fin m)) {c', d'} ↔ (c ≠ c' ∧ c ≠ d' ∧ d ≠ c' ∧ d ≠ d') := by
  simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro h
    exact ⟨(h (Or.inl rfl)).1, (h (Or.inl rfl)).2, (h (Or.inr rfl)).1, (h (Or.inr rfl)).2⟩
  · rintro ⟨h1, h2, h3, h4⟩ a (rfl | rfl)
    · exact ⟨h1, h2⟩
    · exact ⟨h3, h4⟩

private lemma plnf_pair_eq_iff {m : ℕ} (c d c' d' : Fin m) :
    ({c, d} : Finset (Fin m)) = {c', d'} ↔ ((c = c' ∧ d = d') ∨ (c = d' ∧ d = c')) := by
  rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]

theorem qtwoDNbr_fix_card_le_of_act {m k : ℕ} (hk : 4 ≤ k)
    (act : Equiv.Perm (Fin (k + 1)) → DVec m → DVec m)
    (hmul : ∀ σ τ v, act (σ * τ) v = act σ (act τ v))
    (hfaith : ∀ σ τ, (∀ v, act σ v = act τ v) → σ = τ)
    (hτ : ∀ j : Fin k, ∃ (s : Bool) (c d : Fin m), c ≠ d ∧
        ∀ v, act (Equiv.swap (Fin.castSucc j) (Fin.succ j)) v = dTau m s c d v) :
    k + 1 ≤ m ∧ Nat.card {v : DVec m // ∀ σ : Equiv.Perm (Fin (k + 1)), act σ v = v} ≤
      3 ^ (m - k) := by
  choose s c d hcd hact' using hτ
  have hact : ∀ (j : Fin k) (v : DVec m), act (plnf_t j) v = dTau m (s j) (c j) (d j) v :=
    hact'
  have hcomm : ∀ i j : Fin k, i.val + 2 ≤ j.val → ∀ v : DVec m,
      dTau m (s i) (c i) (d i) (dTau m (s j) (c j) (d j) v) =
        dTau m (s j) (c j) (d j) (dTau m (s i) (c i) (d i) v) := by
    intro i j hij v
    have h := congrArg (fun σ => act σ v) (plnf_t_comm hij)
    simp only [hmul, hact] at h
    exact h
  have hncomm : ∀ i j : Fin k, i.val + 1 = j.val → ¬ ∀ v : DVec m,
      dTau m (s i) (c i) (d i) (dTau m (s j) (c j) (d j) v) =
        dTau m (s j) (c j) (d j) (dTau m (s i) (c i) (d i) v) := by
    intro i j hij hv
    refine plnf_t_not_comm hij (hfaith _ _ fun v => ?_)
    simp only [hmul, hact]
    exact hv v
  let S : Fin k → Finset (Fin m) := fun j => {c j, d j}
  have hcard : ∀ j, (S j).card = 2 := fun j => Finset.card_pair (hcd j)
  have hadj : ∀ i j : Fin k, i.val + 1 = j.val → ¬ Disjoint (S i) (S j) ∧ S i ≠ S j := by
    intro i j hij
    refine ⟨fun hd => hncomm i j hij ?_, fun heq => hncomm i j hij ?_⟩
    · exact (dTau_comm_iff m (s i) (s j) (hcd i) (hcd j)).mpr
        (Or.inl ((plnf_disjoint_iff _ _ _ _).mp hd))
    · exact (dTau_comm_iff m (s i) (s j) (hcd i) (hcd j)).mpr
        (Or.inr ((plnf_pair_eq_iff _ _ _ _).mp heq))
  have hfar : ∀ i j : Fin k, i.val + 2 ≤ j.val → Disjoint (S i) (S j) ∨ S i = S j := by
    intro i j hij
    rcases (dTau_comm_iff m (s i) (s j) (hcd i) (hcd j)).mp (hcomm i j hij) with h | h
    · exact Or.inl ((plnf_disjoint_iff _ _ _ _).mpr h)
    · exact Or.inr ((plnf_pair_eq_iff _ _ _ _).mpr h)
  choose w hwS hwfresh using exists_fresh_of_path hk S hcard hadj hfar
  have hw : ∀ j, w j = c j ∨ w j = d j := fun j => by
    simpa [S] using hwS j
  have htri : ∀ i j : Fin k, i < j → w j ≠ c i ∧ w j ≠ d i := fun i j hij => by
    have := hwfresh j i hij
    simpa [S, not_or] using this
  obtain ⟨hkm, hcount⟩ := dFix_card_le_of_triangular (by omega : 0 < k) c d w
    (fun j => if s j then (-1 : ZMod 3) else 1) hcd hw htri
  refine ⟨hkm, le_trans ?_ hcount⟩
  let Ψ : {v : DVec m // ∀ σ : Equiv.Perm (Fin (k + 1)), act σ v = v} →
      {v : DVec m // ∀ j, v (c j) = (if s j then (-1 : ZMod 3) else 1) * v (d j) ∧
        v (d j) = (if s j then (-1 : ZMod 3) else 1) * v (c j)} :=
    fun v => ⟨v.1, fun j => dTau_coord_of_fix m (s j) (hcd j) (by
      rw [← hact j v.1]
      exact v.2 (plnf_t j))⟩
  refine Nat.card_le_card_of_injective Ψ fun v v' h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

end CFSG.StandardType.QTwo

end

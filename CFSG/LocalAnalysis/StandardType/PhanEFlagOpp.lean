module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBuilding

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n m : ℕ}

@[expose] def Opp (E F : FlagK K n) : Prop :=
  ∀ j, j ≤ n → E.E j ⊓ F.E (n - j) = ⊥

private lemma q2cFO_revPerm_val (k : Fin n) :
    ((Fin.revPerm : Equiv.Perm (Fin n)) k).val = n - (k.val + 1) := rfl

private lemma q2cFO_eq_revPerm_of_le {σ : Equiv.Perm (Fin n)}
    (h : ∀ k : Fin n, ((Fin.revPerm : Equiv.Perm (Fin n)) k).val ≤ (σ k).val) :
    σ = Fin.revPerm := by
  have hsum : ∑ k : Fin n, (σ k).val =
      ∑ k : Fin n, ((Fin.revPerm : Equiv.Perm (Fin n)) k).val := by
    rw [Equiv.sum_comp σ (fun k : Fin n => k.val),
      Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun k : Fin n => k.val)]
  have hsum0 : ∑ k : Fin n,
      ((σ k).val - ((Fin.revPerm : Equiv.Perm (Fin n)) k).val) = 0 := by
    have h1 : ∑ k : Fin n, (((Fin.revPerm : Equiv.Perm (Fin n)) k).val +
        ((σ k).val - ((Fin.revPerm : Equiv.Perm (Fin n)) k).val)) =
        ∑ k : Fin n, (σ k).val :=
      Finset.sum_congr rfl fun k _ => Nat.add_sub_cancel' (h k)
    rw [Finset.sum_add_distrib] at h1
    omega
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun k _ => Nat.zero_le _)).mp hsum0
  apply Equiv.ext
  intro k
  exact Fin.ext (le_antisymm (Nat.sub_eq_zero_iff_le.mp (hzero k (Finset.mem_univ k))) (h k))

private lemma q2cFO_finrank_span_image (b : Fin n → (Fin n → K)) (hb : LinearIndependent K b)
    (S : Finset (Fin n)) :
    finrank K (Submodule.span K (b '' (S : Set (Fin n)))) = S.card := by
  have hrange : Set.range (fun x : S => b x.1) = b '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card]
  · exact Fintype.card_coe S
  · exact hb.comp _ Subtype.val_injective

private lemma q2cFO_card_filter_le (j : ℕ) (hj : j ≤ n) :
    (Finset.univ.filter fun k : Fin n => n - j ≤ k.val).card = j := by
  rw [← Fintype.card_subtype (fun k : Fin n => n - j ≤ k.val)]
  let e : {k : Fin n // n - j ≤ k.val} ≃ Fin j :=
    { toFun := fun k => ⟨k.val.val - (n - j), by omega⟩
      invFun := fun m => ⟨⟨m.val + (n - j), by omega⟩, by simp⟩
      left_inv := fun k => by ext; simp; omega
      right_inv := fun m => by ext; simp }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem opp_iff_relPos_rev (E F : FlagK K n) : Opp E F ↔ relPos E F = Fin.revPerm := by
  constructor
  · intro h
    apply q2cFO_eq_revPerm_of_le
    intro k
    have hpos := hasPos_relPos E F
    have hk1 : k.val + 1 ≤ n := by omega
    have hj : n - (k.val + 1) ≤ n := by omega
    have hrk : rk E F (k.val + 1) (n - (k.val + 1)) = 0 := by
      unfold rk
      rw [h (k.val + 1) hk1, finrank_bot]
    have hperm : permRk (relPos E F) (k.val + 1) (n - (k.val + 1)) = 0 := by
      rw [← hpos (k.val + 1) (n - (k.val + 1)) hk1 hj, hrk]
    have hempty : (Finset.univ.filter fun a : Fin n =>
        a.val < k.val + 1 ∧ (relPos E F a).val < n - (k.val + 1)) = ∅ :=
      Finset.card_eq_zero.mp (by simpa [permRk] using hperm)
    have hk := Finset.eq_empty_iff_forall_notMem.mp hempty k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hle : n - (k.val + 1) ≤ (relPos E F k).val :=
      not_lt.mp fun hlt => hk ⟨by omega, hlt⟩
    rwa [q2cFO_revPerm_val k]
  · intro h
    intro j hj
    have hpos : HasPos E F (Fin.revPerm) := hasPos_iff.mpr h
    have hperm : permRk (Fin.revPerm : Equiv.Perm (Fin n)) j (n - j) = 0 := by
      rw [permRk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      rw [q2cFO_revPerm_val k] at hk
      omega
    have hrk : rk E F j (n - j) = 0 := by
      rw [hpos j (n - j) hj (by omega), hperm]
    exact Submodule.finrank_eq_zero.mp (by simpa [rk] using hrk)

theorem opp_iff_flagδ_eq_longest (E F : FlagK K (m + 1)) :
    Opp E F ↔ flagδ m E F = longest (symCox m) Set.univ := by
  rw [opp_iff_relPos_rev, flagδ, longest_symCox_univ]
  constructor
  · intro h
    rw [h]
    exact Fin.revPerm_symm
  · intro h
    have h2 : relPos E F = (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹ := by
      rw [← inv_inv (relPos E F), h]
    exact h2.trans Fin.revPerm_symm

theorem opp_iff_length_flagδ (E F : FlagK K (m + 1)) :
    Opp E F ↔ (symCox m).length (flagδ m E F) = (m + 1) * m / 2 := by
  rw [opp_iff_relPos_rev, symCox_length, flagδ, invCount_inv]
  constructor
  · intro h
    rw [h, invCount_revPerm, Nat.add_sub_cancel]
  · intro h
    exact eq_revPerm_of_invCount_eq (by simpa using h)

theorem exists_opp (E : FlagK K n) : ∃ F, Opp E F := by
  obtain ⟨b, σ, hb, hE, -⟩ := exists_adapted E E
  let F : FlagK K n :=
    { E := fun j => Submodule.span K
        (b '' (↑(Finset.univ.filter fun k : Fin n => n - j ≤ k.val) : Set (Fin n)))
      mono := by
        intro a c hac
        apply Submodule.span_mono
        rintro v ⟨k, hk, rfl⟩
        exact ⟨k, by
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          omega, rfl⟩
      dim := by
        intro j hj
        rw [q2cFO_finrank_span_image b hb]
        exact q2cFO_card_filter_le j hj
      top := by
        intro j hj
        have hset : (Finset.univ.filter fun k : Fin n => n - j ≤ k.val) = Finset.univ := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun _ => trivial, fun _ => by omega⟩
        rw [hset]
        have hrange : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) =
            {k : Fin n | k.val < n} := by
          ext k
          simp
        rw [hrange, ← hE n le_rfl, E.top n le_rfl] }
  refine ⟨F, ?_⟩
  intro j hj
  have hFset : (↑(Finset.univ.filter fun k : Fin n => n - (n - j) ≤ k.val) : Set (Fin n)) =
      {k : Fin n | j ≤ k.val} := by
    ext k
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    omega
  have hdisj : Disjoint ({k : Fin n | k.val < j} : Set (Fin n)) {k : Fin n | j ≤ k.val} := by
    rw [Set.disjoint_left]
    intro k hk1 hk2
    simp only [Set.mem_setOf_eq] at hk1 hk2
    omega
  have hdj := hb.disjoint_span_image hdisj
  rw [hE j hj]
  change Submodule.span K (b '' {k : Fin n | k.val < j}) ⊓
    Submodule.span K (b '' (↑(Finset.univ.filter fun k : Fin n =>
      n - (n - j) ≤ k.val) : Set (Fin n))) = ⊥
  rw [hFset]
  exact disjoint_iff.mp hdj

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

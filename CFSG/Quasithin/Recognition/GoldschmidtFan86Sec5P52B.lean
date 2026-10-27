module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52S
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def rayArc (v : ℕ → V) (hadj : ∀ j, Γ.Adj (v j) (v (j + 1))) (hnb : ∀ j, v j ≠ v (j + 2))
    (s : ℕ) : Arc Γ s where
  vert := v
  adj i _ := hadj i
  nb i _ := hnb i

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem ray_fixes {v : ℕ → V} (hadj : ∀ j, Γ.Adj (v j) (v (j + 1))) (hnb : ∀ j, v j ≠ v (j + 2))
    {g : G} {k : ℕ} (h0 : g • v 0 = v 0) (hk : g • v k = v k) : ∀ l, l ≤ k → g • v l = v l :=
  Arc.fixes_of_ends F.isTree F.adj_smul (rayArc v hadj hnb k) h0 hk

theorem exists_smul_edge {β β' w w' : V} (hββ' : Γ.Adj β β') (hww' : Γ.Adj w w')
    (h : Fan86.valence Γ w = Fan86.valence Γ β) : ∃ k : G, k • β = w ∧ k • β' = w' := by
  obtain ⟨p⟩ := F.isTree.connected.preconnected β w
  obtain ⟨n, hn⟩ := (F.walk_even_iff p).1 h
  obtain ⟨g, hg⟩ := F.exists_smul_of_walk_even n p (by omega)
  have h1 : Γ.Adj w (g • β') := by
    have := (F.adj_smul g β β').2 hββ'
    rwa [hg] at this
  obtain ⟨g', hg', hg'b⟩ := F.loc_trans w _ _ h1 hww'
  refine ⟨g' * g, ?_, ?_⟩
  · rw [mul_smul, hg, MulAction.mem_stabilizer_iff.1 hg']
  · rw [mul_smul, hg'b]

theorem relIndex_edge_eq {β β' w w' : V} (hββ' : Γ.Adj β β') (hww' : Γ.Adj w w')
    (h : Fan86.valence Γ w = Fan86.valence Γ β) :
    (nbrStab Γ G w).relIndex (MulAction.stabilizer G w ⊓ MulAction.stabilizer G w') =
      (nbrStab Γ G β).relIndex (MulAction.stabilizer G β ⊓ MulAction.stabilizer G β') := by
  obtain ⟨k, hk1, hk2⟩ := F.exists_smul_edge hββ' hww' h
  subst hk1 hk2
  set f : G →* G := (MulAut.conj k).toMonoidHom with hfdef
  have hinj : Function.Injective f := (MulAut.conj k).injective
  have hmap : (MulAction.stabilizer G β ⊓ MulAction.stabilizer G β').map f =
      (MulAction.stabilizer G β).map f ⊓ (MulAction.stabilizer G β').map f :=
    Subgroup.map_inf _ _ f hinj
  rw [F.nbrStab_smul, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hmap]
  exact Subgroup.relIndex_map_map_of_injective _ _ hinj


theorem relIndex_chain {v : ℕ → V} (hadj : ∀ j, Γ.Adj (v j) (v (j + 1)))
    (hnb : ∀ j, v j ≠ v (j + 2)) {m : ℕ} (f : ℕ → ℕ)
    (hf : ∀ j, 1 ≤ j → j < m → (nbrStab Γ G (v j)).relIndex
      (MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1))) ≤ f j) :
    ∀ k, 1 ≤ k → k ≤ m → (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)).relIndex
      (nbrStab Γ G (v 0)) ≤ ∏ j ∈ Finset.Ico 1 k, f j := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    have : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v 1) = nbrStab Γ G (v 0) :=
      inf_eq_left.2 fun g hg => MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg _ (hadj 0))
    rw [this, Subgroup.relIndex_self]
    simp
  | succ k hk ih =>
    intro hkm
    have hS : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v (k + 1)) ≤
        nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k) := by
      rintro g ⟨hg0, hg1⟩
      refine ⟨hg0, MulAction.mem_stabilizer_iff.2 ?_⟩
      exact F.ray_fixes hadj hnb (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg0))
        (MulAction.mem_stabilizer_iff.1 hg1) k (by omega)
    have hSK : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k) ≤ nbrStab Γ G (v 0) := inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hS hSK
    have hkey : (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v (k + 1))).relIndex
        (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) ≤ f k := by
      have hk1' : v (k - 1) = v (k - 1) := rfl
      have hadj1 : Γ.Adj (v k) (v (k - 1)) := by
        have := (hadj (k - 1)).symm
        rwa [show k - 1 + 1 = k by omega] at this
      have hne : v (k - 1) ≠ v (k + 1) := by
        have := hnb (k - 1)
        rwa [show k - 1 + 2 = k + 1 by omega] at this
      have heq : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v (k + 1)) =
          (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) ⊓ nbrStab Γ G (v k) := by
        ext g
        constructor
        · rintro ⟨hg0, hg1⟩
          refine ⟨hS ⟨hg0, hg1⟩, ?_⟩
          have hg0' := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg0)
          have hfix := F.ray_fixes hadj hnb hg0' (MulAction.mem_stabilizer_iff.1 hg1)
          refine mem_nbrStab.2 ?_
          exact F.frobenius_two (v k) (v (k - 1)) (v (k + 1)) hadj1 (hadj k) hne g
            (MulAction.mem_stabilizer_iff.2 (hfix k (by omega))) (hfix (k - 1) (by omega))
            (hfix (k + 1) le_rfl)
        · rintro ⟨⟨hg0, hgk⟩, hgK⟩
          exact ⟨hg0, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hgK _ (hadj k))⟩
      have hSE : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k) ≤
          MulAction.stabilizer G (v k) ⊓ MulAction.stabilizer G (v (k - 1)) := by
        rintro g ⟨hg0, hgk⟩
        refine ⟨hgk, MulAction.mem_stabilizer_iff.2 ?_⟩
        exact F.ray_fixes hadj hnb (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg0))
          (MulAction.mem_stabilizer_iff.1 hgk) (k - 1) (by omega)
      rw [heq, inf_comm (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) (nbrStab Γ G (v k)),
        Subgroup.inf_relIndex_right]
      have := F.finite_stabilizer_inf (v k) (v (k - 1))
      calc (nbrStab Γ G (v k)).relIndex (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k))
          ≤ (nbrStab Γ G (v k)).relIndex
            (MulAction.stabilizer G (v k) ⊓ MulAction.stabilizer G (v (k - 1))) :=
            Subgroup.relIndex_le_of_le_right hSE (relIndex_ne_zero_of_finite _ _)
        _ ≤ f k := hf k hk (by omega)
    have := ih (by omega)
    rw [← hmul, Finset.prod_Ico_succ_top hk]
    calc (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v (k + 1))).relIndex
          (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) *
        (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)).relIndex (nbrStab Γ G (v 0))
        ≤ f k * ∏ j ∈ Finset.Ico 1 k, f j := Nat.mul_le_mul hkey this
      _ = (∏ j ∈ Finset.Ico 1 k, f j) * f k := mul_comm _ _

end FanTree

end CFSG.Quasithin.Fan86

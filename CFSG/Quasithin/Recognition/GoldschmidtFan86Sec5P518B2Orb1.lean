module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52B
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem relIndex_chain_img (F : FanTree Γ G) {v : ℕ → V} (hadj : ∀ j, Γ.Adj (v j) (v (j + 1)))
    (hnb : ∀ j, v j ≠ v (j + 2)) {m : ℕ} (f : ℕ → ℕ)
    (hf : ∀ j, 1 ≤ j → j < m → (nbrStab Γ G (v j)).relIndex
      (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v j)) ≤ f j) :
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
      rw [heq, inf_comm (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) (nbrStab Γ G (v k)),
        Subgroup.inf_relIndex_right]
      exact hf k hk (by omega)
    have := ih (by omega)
    rw [← hmul, Finset.prod_Ico_succ_top hk]
    calc (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v (k + 1))).relIndex
          (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)) *
        (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v k)).relIndex (nbrStab Γ G (v 0))
        ≤ f k * ∏ j ∈ Finset.Ico 1 k, f j := Nat.mul_le_mul hkey this
      _ = (∏ j ∈ Finset.Ico 1 k, f j) * f k := mul_comm _ _

theorem edge_relIndex_le_two (F : FanTree Γ G) {v a : V} (hv : valence Γ v = 3)
    (ha : Γ.Adj v a) : (nbrStab Γ G v).relIndex
      (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) ≤ 2 := by
  obtain ⟨φ, -, hidx, hdvd, -⟩ := F.exists_edge_char ha
  rw [hidx]
  have h1 : valence Γ v - 1 = 2 := by omega
  have h2 : Nat.card φ.range ∣ 2 := by
    rw [← h1]
    exact hdvd
  exact Nat.le_of_dvd (by norm_num) h2

theorem ncard_orbit_eq_relIndex {α : Type*} [MulAction G α] (P : Subgroup G) (x : α) :
    Set.ncard {w : α | ∃ g ∈ P, w = g • x} = (MulAction.stabilizer G x).relIndex P := by
  have h1 := MulAction.index_stabilizer (G := P) (x := x)
  have h2 : MulAction.stabilizer P x = (MulAction.stabilizer G x).subgroupOf P := by
    ext g
    simp [MulAction.mem_stabilizer_iff]
  rw [Subgroup.relIndex, ← h2, h1]
  congr 1
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

end P518

end CFSG.Quasithin.Fan86

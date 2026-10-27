module

public import CFSG.Quasithin.EmptyFaithful.ModDData
public import CFSG.Quasithin.Recognition.CertU33DcPG

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

@[expose] def stabπ (π : U33G →* Equiv.Perm (Fin 63)) : Subgroup U33G :=
  (MulAction.stabilizer (Equiv.Perm (Fin 63)) (0 : Fin 63)).comap π

theorem mem_stabπ {π : U33G →* Equiv.Perm (Fin 63)} {g : U33G} : g ∈ stabπ π ↔ π g 0 = 0 := by
  simp [stabπ, MulAction.mem_stabilizer_iff]

theorem vHom_gen (i : Fin 5) : vHom (u33GenPG i.val) = vImg i := by
  rw [u33GenPG_of, vHom_of]

theorem lHom_gen (i : Fin 5) : lHom (u33GenPG i.val) = lImg i := by
  rw [u33GenPG_of, lHom_of]

@[expose] def gOfWord (w : List (Fin 5 × Bool)) : U33G :=
  (w.map fun l => cond l.2 (PresentedGroup.of l.1 : U33G) (PresentedGroup.of l.1 : U33G)⁻¹).prod

theorem hom_gOfWord (π : U33G →* Equiv.Perm (Fin 63)) (img : Fin 5 → Equiv.Perm (Fin 63))
    (h : ∀ i, π (PresentedGroup.of i) = img i) (w : List (Fin 5 × Bool)) :
    π (gOfWord w) = evalW img w := by
  induction w with
  | nil => simp [gOfWord, evalW]
  | cons l w ih =>
    simp only [gOfWord, evalW, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, ih]
    congr 1
    rcases l with ⟨i, b⟩
    cases b <;> simp [h i]

theorem vHom_trans : ∀ j : Fin 63, ∃ g : U33G, vHom g 0 = j := fun j =>
  ⟨gOfWord (u33Word (vTab.getD j.val "")), by
    rw [hom_gOfWord vHom vImg vHom_of]
    exact vTab_spec j⟩

theorem lHom_trans : ∀ j : Fin 63, ∃ g : U33G, lHom g 0 = j := fun j =>
  ⟨gOfWord (u33Word (lTab.getD j.val "")), by
    rw [hom_gOfWord lHom lImg lHom_of]
    exact lTab_spec j⟩

theorem index_stabπ (π : U33G →* Equiv.Perm (Fin 63)) (htr : ∀ j, ∃ g, π g 0 = j) :
    (stabπ π).index = 63 := by
  let _ : MulAction U33G (Fin 63) := MulAction.compHom (Fin 63) π
  have h1 : stabπ π = MulAction.stabilizer U33G (0 : Fin 63) := by
    ext g
    simp [mem_stabπ, MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def]
  have h2 : MulAction.orbit U33G (0 : Fin 63) = Set.univ := by
    ext j
    simp only [MulAction.mem_orbit_iff, Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := htr j
    exact ⟨g, by simpa [MulAction.compHom_smul_def] using hg⟩
  rw [h1, MulAction.index_stabilizer, h2]
  simp


theorem card_stabπ (π : U33G →* Equiv.Perm (Fin 63)) (htr : ∀ j, ∃ g, π g 0 = j) :
    Nat.card (stabπ π) = 96 := by
  have h := Subgroup.card_mul_index (stabπ π)
  rw [index_stabπ π htr, card_u33Pres] at h
  omega

theorem A_not_le_B : ¬ u33Data.A ≤ u33Data.B := by
  intro h
  apply u33Data.T_ne_A
  rw [← u33Data.inf_AB]
  exact inf_eq_left.2 h

theorem B_not_le_A : ¬ u33Data.B ≤ u33Data.A := by
  intro h
  apply u33Data.T_ne_B
  rw [← u33Data.inf_AB]
  exact inf_eq_right.2 h

theorem stab_vHom : stabπ vHom = u33Data.A := by
  have hA : u33Data.A ≤ stabπ vHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    obtain ⟨h0, h1, h2, h3⟩ := vImg_fix
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_stabπ.2 (by
        have := vHom_gen 0
        simp only [Fin.val_zero] at this
        show vHom (u33GenPG 0) 0 = 0
        rw [this]; exact h0)
    · exact mem_stabπ.2 (by
        have := vHom_gen 1
        show vHom (u33GenPG 1) 0 = 0
        rw [show (1 : ℕ) = (1 : Fin 5).val from rfl, this]; exact h1)
    · exact mem_stabπ.2 (by
        have := vHom_gen 2
        show vHom (u33GenPG 2) 0 = 0
        rw [show (2 : ℕ) = (2 : Fin 5).val from rfl, this]; exact h2)
    · exact mem_stabπ.2 (by
        have := vHom_gen 3
        show vHom (u33GenPG 3) 0 = 0
        rw [show (3 : ℕ) = (3 : Fin 5).val from rfl, this]; exact h3)
  have hT : u33Data.T ≤ stabπ vHom := u33Data.T_le_A.trans hA
  have hcard := card_stabπ vHom vHom_trans
  rcases u33Data.lattice _ hT with h | h | h | h
  · rw [h, u33_card_T] at hcard
    omega
  · exact h
  · rw [h] at hA
    exact absurd hA A_not_le_B
  · rw [h, Subgroup.card_top, card_u33Pres] at hcard
    omega

theorem stab_lHom : stabπ lHom = u33Data.B := by
  have hB : u33Data.B ≤ stabπ lHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    obtain ⟨h0, h1, h2, h4⟩ := lImg_fix
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_stabπ.2 (by
        have := lHom_gen 0
        simp only [Fin.val_zero] at this
        show lHom (u33GenPG 0) 0 = 0
        rw [this]; exact h0)
    · exact mem_stabπ.2 (by
        have := lHom_gen 1
        show lHom (u33GenPG 1) 0 = 0
        rw [show (1 : ℕ) = (1 : Fin 5).val from rfl, this]; exact h1)
    · exact mem_stabπ.2 (by
        have := lHom_gen 2
        show lHom (u33GenPG 2) 0 = 0
        rw [show (2 : ℕ) = (2 : Fin 5).val from rfl, this]; exact h2)
    · exact mem_stabπ.2 (by
        have := lHom_gen 4
        show lHom (u33GenPG 4) 0 = 0
        rw [show (4 : ℕ) = (4 : Fin 5).val from rfl, this]; exact h4)
  have hT : u33Data.T ≤ stabπ lHom := u33Data.T_le_B.trans hB
  have hcard := card_stabπ lHom lHom_trans
  rcases u33Data.lattice _ hT with h | h | h | h
  · rw [h, u33_card_T] at hcard
    omega
  · rw [h] at hB
    exact absurd hB B_not_le_A
  · exact h
  · rw [h, Subgroup.card_top, card_u33Pres] at hcard
    omega

end CFSG.Quasithin.ModD

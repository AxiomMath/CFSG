module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Act

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Vol2Native.A312L Matrix

theorem listHom_eq_of_tab {α : Type} [MulAction G24 α] [DecidableEq α]
    (act' : List ℕ → α → α) (hact : ∀ (g : G24) (x : α), g • x = act' (tab 24 g) x)
    (Z : Subgroup G24) (L : List α) (hnd : L.Nodup) (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L)
    (z : ↥Z) (σ : Equiv.Perm (Fin L.length))
    (h : L.map (fun x => L.idxOf (act' (tab 24 z.1) x)) = tab L.length σ) :
    listHom Z L hnd hZ z = σ :=
  eq_of_tab_eq (n := L.length) (by rw [tab_listHom act' hact Z L hnd hZ z]; exact h)

theorem tab_rho8 (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    tab 7 (Seven.rho Seven.lab8 g) = (List.finRange 7).map (fun x =>
      ((Seven.idxOf Seven.vec8 ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Seven.vec8 x) : Fin 7) :
        ℕ)) := by
  unfold tab
  refine List.map_congr_left (fun x _ => ?_)
  rw [Equiv.Perm.smul_def, Seven.rho8_apply]

theorem card_rho8_range : Nat.card (Seven.rho Seven.lab8).range = 168 := by
  rw [← Seven.card_slThree]
  exact (Nat.card_congr (MonoidHom.ofInjective (Seven.rho_injective Seven.lab8)).toEquiv).symm

theorem sl3_quotient_of_range {A : Type} [Group A] (f : A →* Equiv.Perm (Fin 7))
    (hle : f.range ≤ (Seven.rho Seven.lab8).range) (hcard : 168 ≤ Nat.card f.range) :
    Nonempty (A ⧸ f.ker ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hrange : f.range = (Seven.rho Seven.lab8).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_rho8_range]; exact hcard)
  exact ⟨(QuotientGroup.quotientKerEquivRange f).trans
    ((MulEquiv.subgroupCongr hrange).trans
      (MonoidHom.ofInjective (Seven.rho_injective Seven.lab8)).symm)⟩

@[expose] def M4 : Fin 5 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 1, 1, 0; 1, 0, 1], !![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 0, 1; 1, 1, 0],
    1, !![1, 1, 1; 1, 0, 0; 1, 0, 1]]

@[expose] def M6 : Fin 5 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 1, 0, 1],
    1, !![1, 1, 1; 1, 0, 1; 1, 0, 0]]

theorem M4_det : ∀ i, (M4 i).det = 1 := by
  intro i
  fin_cases i <;> simp [M4, Matrix.det_fin_three] <;> decide

theorem M6_det : ∀ i, (M6 i).det = 1 := by
  intro i
  fin_cases i <;> simp [M6, Matrix.det_fin_three] <;> decide

@[expose] def M4sl (i : Fin 5) : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨M4 i, M4_det i⟩

@[expose] def M6sl (i : Fin 5) : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨M6 i, M6_det i⟩

@[expose] def M4tab : List (List ℕ) :=
  [[3, 1, 2, 0, 6, 5, 4], [0, 4, 6, 3, 1, 5, 2], [3, 2, 1, 0, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6],
    [3, 0, 6, 4, 5, 2, 1]]

@[expose] def M6tab : List (List ℕ) :=
  [[0, 2, 1, 3, 6, 5, 4], [0, 4, 6, 3, 1, 5, 2], [3, 1, 2, 0, 6, 5, 4], [0, 1, 2, 3, 4, 5, 6],
    [3, 0, 4, 6, 5, 1, 2]]

theorem tab_rho_M4 (i : Fin 5) : tab 7 (Seven.rho Seven.lab8 (M4sl i)) = M4tab.getD i [] := by
  rw [tab_rho8]
  fin_cases i <;> decide

theorem tab_rho_M6 (i : Fin 5) : tab 7 (Seven.rho Seven.lab8 (M6sl i)) = M6tab.getD i [] := by
  rw [tab_rho8]
  fin_cases i <;> decide

end CFSG.Quasithin.A312M24

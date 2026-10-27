module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBData8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBData16

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open CFSG.QuasithinUnique.A6Facts Subgroup

@[expose] def blk : Equiv.Perm (Fin 8) × Equiv.Perm (Fin 8) →* P16 :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin 8) (Fin 8))

theorem blk_apply (p : Equiv.Perm (Fin 8) × Equiv.Perm (Fin 8)) :
    blk p = Equiv.permCongrHom finSumFinEquiv (Equiv.Perm.sumCongr p.1 p.2) :=
  rfl

theorem blk_injective : Function.Injective blk :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Equiv.Perm.sumCongrHom_injective

theorem sig_eq : sig = Equiv.permCongrHom finSumFinEquiv (Equiv.sumComm (Fin 8) (Fin 8)) := by
  decide

theorem sig_mul_sig : sig * sig = 1 := by decide

theorem sig_mul_blk (g h : Equiv.Perm (Fin 8)) : sig * blk (g, h) = blk (h, g) * sig := by
  rw [blk_apply, blk_apply, sig_eq, ← map_mul, ← map_mul]
  congr 1
  ext x
  cases x <;> rfl

theorem blk_mul_sig_ne_one (p : Equiv.Perm (Fin 8) × Equiv.Perm (Fin 8)) : blk p * sig ≠ 1 := by
  intro h
  have h0 := congrArg (fun σ : P16 => σ (finSumFinEquiv (m := 8) (n := 8) (Sum.inl 0))) h
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sig_eq, blk_apply, Equiv.Perm.coe_one,
    id_eq] at h0
  simp [Equiv.permCongrHom, Equiv.permCongr_apply] at h0

theorem blk_g1 : blk (NFF7.g1, 1) = a1 := by decide
theorem blk_pb : blk (pb, 1) = b1 := by decide
theorem blk_g1' : blk (1, NFF7.g1) = a2 := by decide
theorem blk_pb' : blk (1, pb) = b2 := by decide
theorem blk_pu : blk (pu, 1) = u1 := by decide
theorem blk_pv : blk (pv, 1) = v1 := by decide
theorem blk_pu' : blk (1, pu) = u2 := by decide
theorem blk_pv' : blk (1, pv) = v2 := by decide
theorem blk_g2 : blk (NFF7.g2, 1) = d1 := by decide
theorem blk_g2' : blk (1, NFF7.g2) = d2 := by decide

theorem d1_conj_sig : d1 * sig * d1⁻¹ * sig⁻¹ = d1 * d2 := by decide

theorem map_closure_list {G H : Type} [Group G] [Group H] (f : G →* H) (l : List G) :
    (closure {g | g ∈ l}).map f = closure {g | g ∈ l.map f} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_map]

theorem L01_eq : L01 = H0.map (blk.comp (MonoidHom.inl _ _)) := by
  rw [H0, map_closure_list, L01]
  congr 3
  simp [blk_g1, blk_pb]

theorem L02_eq : L02 = H0.map (blk.comp (MonoidHom.inr _ _)) := by
  rw [H0, map_closure_list, L02]
  congr 3
  simp [blk_g1', blk_pb']

theorem mem_TB {i : Fin 4} {g : P16} (hg : g ∈ [u1, v1, u2, v2] ++ bGens i) : g ∈ TB i :=
  subset_closure hg

theorem d2_mem_TB3 : d2 ∈ TB 3 := by
  rw [d2_eq]
  exact mul_mem (mul_mem (mem_TB (by simp [bGens])) (mem_TB (by simp [bGens])))
    (mem_TB (by simp [bGens]))

theorem blk_mem_TB3 {g h : Equiv.Perm (Fin 8)} (hg : g ∈ D16) (hh : h ∈ D16) :
    blk (g, h) ∈ TB 3 := by
  have e : blk (g, h) = blk.comp (MonoidHom.inl _ _) g * blk.comp (MonoidHom.inr _ _) h := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  rw [e]
  refine mul_mem ?_ ?_
  · have h1 : D16.map (blk.comp (MonoidHom.inl _ _)) ≤ TB 3 := by
      rw [D16, map_closure_list, closure_le]
      intro x hx
      simp only [List.map_cons, List.map_nil, MonoidHom.comp_apply, MonoidHom.inl_apply,
        blk_pu, blk_pv, blk_g2, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact mem_TB (by simp [bGens])
    exact h1 (mem_map_of_mem _ hg)
  · have h1 : D16.map (blk.comp (MonoidHom.inr _ _)) ≤ TB 3 := by
      rw [D16, map_closure_list, closure_le]
      intro x hx
      simp only [List.map_cons, List.map_nil, MonoidHom.comp_apply, MonoidHom.inr_apply,
        blk_pu', blk_pv', blk_g2', Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_TB (by simp [bGens])
      · exact mem_TB (by simp [bGens])
      · exact d2_mem_TB3
    exact h1 (mem_map_of_mem _ hh)

theorem card_H0 : Nat.card H0 = 168 := by
  rw [H0, card_closure_eq_of_tblN h_gens h_tbl h_nodup, h_length]

theorem mem_H0_iff (σ : Equiv.Perm (Fin 8)) :
    σ ∈ H0 ↔ codeN 8 σ ∈ Core.buildCodes (List.range 8) hGenC hTree :=
  (mem_closure_iff_of_tblN h_gens h_tbl).1 σ

theorem D_le_H0 : D ≤ H0 := by
  rw [D, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (mem_H0_iff _).2 pu_mem_h
  · exact (mem_H0_iff _).2 pv_mem_h

theorem card_D : Nat.card D = 8 := by
  rw [D, card_closure_eq_of_tblN d_gens d_tbl d_nodup, d_length]

theorem mem_D_iff (σ : Equiv.Perm (Fin 8)) : σ ∈ D ↔ codeN 8 σ ∈ dLit := by
  rw [d_build]
  exact (mem_closure_iff_of_tblN d_gens d_tbl).1 σ

theorem mem_D16_iff (σ : Equiv.Perm (Fin 8)) : σ ∈ D16 ↔ codeN 8 σ ∈ eLit := by
  rw [e_build]
  exact (mem_closure_iff_of_tblN e_gens e_tbl).1 σ

theorem mem_D16_of_normalizes {g : Equiv.Perm (Fin 8)} (hg : g ∈ NFF7.G0)
    (hu : g * pu * g⁻¹ ∈ D) (hv : g * pv * g⁻¹ ∈ D) : g ∈ D16 := by
  rw [mem_D16_iff]
  refine norm_check _ ((NFF7.mem_G0_iff g).1 hg) ⟨_, (mem_D_iff _).1 hu, ?_⟩
    ⟨_, (mem_D_iff _).1 hv, ?_⟩
  · rw [← codeN_mul, ← codeN_mul, inv_mul_cancel_right]
  · rw [← codeN_mul, ← codeN_mul, inv_mul_cancel_right]

theorem D16_split {g : Equiv.Perm (Fin 8)} (hg : g ∈ D16) :
    g ∈ D ∨ ∃ d ∈ D, g = d * NFF7.g2 := by
  rcases split_check _ ((mem_D16_iff g).1 hg) with h | ⟨c, hc, hgc⟩
  · exact Or.inl ((mem_D_iff g).2 h)
  · rw [d_build] at hc
    obtain ⟨d, hd, rfl⟩ := (mem_closure_iff_of_tblN d_gens d_tbl).2 c hc
    exact Or.inr ⟨d, hd, codeN_injective (by rw [codeN_mul]; exact hgc)⟩

theorem pw_mem_G0 : pw ∈ NFF7.G0 := (NFF7.mem_G0_iff pw).2 pw_mem_g

theorem g1_mem_G0 : NFF7.g1 ∈ NFF7.G0 := subset_closure (by simp)

theorem card_TD : Nat.card TD = 64 := by
  rw [TD, card_closure_eq_of_tblN td_gens td_tbl td_nodup, td_length]

theorem sig_not_mem_TD : sig ∉ TD := by
  rw [TD, (mem_closure_iff_of_tblN td_gens td_tbl).1]
  exact sig_not_td

theorem d1sig_not_mem_TD : d1 * sig ∉ TD := by
  rw [TD, (mem_closure_iff_of_tblN td_gens td_tbl).1]
  exact d1sig_not_td

theorem card_TB0 : Nat.card (TB 0) = 128 := by
  rw [TB, card_closure_eq_of_tblN tb0_gens tb0_tbl tb0_nodup, tb0_length]

theorem card_TB1 : Nat.card (TB 1) = 256 := by
  rw [TB, card_closure_eq_of_tblN tb1_gens tb1_tbl tb1_nodup, tb1_length]

theorem card_TB2 : Nat.card (TB 2) = 256 := by
  rw [TB, card_closure_eq_of_tblN tb2_gens tb2_tbl tb2_nodup, tb2_length]

theorem card_TB3 : Nat.card (TB 3) = 512 := by
  rw [TB, card_closure_eq_of_tblN tb3_gens tb3_tbl tb3_nodup, tb3_length]

theorem mem_GB {i : Fin 4} {g : P16} (hg : g ∈ [a1, b1, a2, b2] ++ bGens i) : g ∈ GB i :=
  subset_closure hg

theorem L01_le_GB (i : Fin 4) : L01 ≤ GB i := by
  rw [L01, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact mem_GB (by simp)

theorem L02_le_GB (i : Fin 4) : L02 ≤ GB i := by
  rw [L02, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact mem_GB (by simp)

theorem u1_mem_L01 : u1 ∈ L01 := by
  rw [L01_eq, ← blk_pu]
  exact mem_map_of_mem _ (D_le_H0 (subset_closure (by simp)))

theorem v1_mem_L01 : v1 ∈ L01 := by
  rw [L01_eq, ← blk_pv]
  exact mem_map_of_mem _ (D_le_H0 (subset_closure (by simp)))

theorem u2_mem_L02 : u2 ∈ L02 := by
  rw [L02_eq, ← blk_pu']
  exact mem_map_of_mem _ (D_le_H0 (subset_closure (by simp)))

theorem v2_mem_L02 : v2 ∈ L02 := by
  rw [L02_eq, ← blk_pv']
  exact mem_map_of_mem _ (D_le_H0 (subset_closure (by simp)))

theorem TB_le_GB (i : Fin 4) : TB i ≤ GB i := by
  rw [TB, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | hx
  · exact L01_le_GB i u1_mem_L01
  · exact L01_le_GB i v1_mem_L01
  · exact L02_le_GB i u2_mem_L02
  · exact L02_le_GB i v2_mem_L02
  · exact mem_GB (List.mem_append_right _ hx)

theorem sup_TB_eq_GB (i : Fin 4) : L01 ⊔ L02 ⊔ TB i = GB i := by
  refine le_antisymm (sup_le (sup_le (L01_le_GB i) (L02_le_GB i)) (TB_le_GB i)) ?_
  rw [GB, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | hx
  · exact mem_sup_left (mem_sup_left (subset_closure (by simp)))
  · exact mem_sup_left (mem_sup_left (subset_closure (by simp)))
  · exact mem_sup_left (mem_sup_right (subset_closure (by simp)))
  · exact mem_sup_left (mem_sup_right (subset_closure (by simp)))
  · exact mem_sup_right (mem_TB (List.mem_append_right _ hx))

end CFSG.LocalAnalysis.WeakClosure81.NGM

module

public import CFSG.Quasithin.H13.GoldschmidtI51Q0
public import CFSG.Quasithin.H13.GoldschmidtI51Sym
public import CFSG.Quasithin.H13.GoldschmidtI51Hyp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

theorem exists_odd (hD : IsDSystem .C3 Gs) {x y : G ⧸ Gs 0} (hxy : x ≠ y) :
    ∃ w, OddTriple Gs x y w := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hy' : (g : G)⁻¹ • y ≠ oPt Gs := fun h => hxy (by
    rw [inv_smul_eq_iff] at h
    rw [h, smul_oPt'])
  have key : ∀ w, OddTriple Gs (oPt Gs) ((g : G)⁻¹ • y) w →
      ∃ w', OddTriple Gs ((g : G⧸ Gs 0)) y w' := fun w hw => by
    refine ⟨(g : G) • w, ?_⟩
    have := hw.smul (g : G)
    rwa [smul_oPt', smul_inv_smul] at this
  by_cases hc : Col Gs (oPt Gs) ((g : G)⁻¹ • y)
  · obtain ⟨w, hw⟩ := odd_col hD ⟨hy', hc⟩
    exact key w hw
  · obtain ⟨w, hw⟩ := odd_hyp hD (mem_D2_of_not_col hD hc)
    exact key w hw

noncomputable def formData (hD : IsDSystem .C3 Gs) : FormData G (G ⧸ Gs 0) where
  f p q := by classical exact if Col Gs p q then 0 else 1
  symm x y := by
    classical
    by_cases h : Col Gs x y
    · simp [h, col_symm h]
    · have : ¬ Col Gs y x := fun h' => h (col_symm h')
      simp [h, this]
  diag x := by
    classical
    simp [col_refl]
  inv g x y := by
    classical
    simp [col_smul]
  ne := by
    classical
    have hne : (D2 Gs).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [ncard_D2 hD]; norm_num)
    obtain ⟨z, hz⟩ := hne
    exact ⟨oPt Gs, z, by simp [hz.1]⟩
  add x y hxy := by
    classical
    obtain ⟨w, hw⟩ := exists_odd hD hxy
    refine ⟨w, fun p => ?_⟩
    have h := hw p
    by_cases hx : Col Gs x p <;> by_cases hy : Col Gs y p <;> by_cases hz : Col Gs w p <;>
      simp [hx, hy, hz] at h ⊢
    decide
  trans := inferInstance

theorem stmtI_5_1_C3 (hD : IsDSystem .C3 Gs) : LieModel G .PSp 3 2 1 := by
  classical
  have : Fintype (G ⧸ Gs 0) := Fintype.ofFinite _
  exact lieModel_sp62_of_formData (formData hD) (card_Omega hD)
    (fun g hg => faithful hD hg) (card_G_ge hD)

end CFSG.Quasithin.H13.I51

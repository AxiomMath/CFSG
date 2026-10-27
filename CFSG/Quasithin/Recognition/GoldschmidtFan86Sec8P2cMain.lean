module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cBall
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87C

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.F87

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_3c {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) : Fan83c F L := by
  intro α D hne i l₁ l₂ hZ
  have h71c : Fan71c F L := h7.2.2.1
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨c, hc, rfl⟩
    rcases P2c.fcomm_pair_mem D h7 h512 hZ hc with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  · have hex : ∃ c ∈ D.calpha, fcomm (L.z l₁ * L.z l₂) c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      refine hne (le_antisymm (fun c hc => ?_) (Subgroup.zpowers_le.2 (z_mem_calpha h7 D)))
      have hfin : ∀ k : Fin 5, k + 1 ≠ k := by decide
      have hji : i + 1 ≠ i := hfin i
      obtain ⟨t, hts, -, -, hyt⟩ := P2c.pair_alpha_third D h71c h81 hZ hji
      have hcy : c * (L.z l₁ * L.z l₂) = (L.z l₁ * L.z l₂) * c :=
        (fcomm_eq_one_iff.1 (hcon c hc)).symm
      have hcH := calpha_le_ballStab h7 D hc
      refine P2c.calpha_mem_zpowers D h7 hc (j := i + 1) ?_
      refine P2c.mem_ballStab_two_of F (mem_ballStab.1 hcH _ (by
        rw [D.dist_start_beta F]; norm_num)) fun u hu => ?_
      have hmem : u ∈ Γ.neighborSet (D.beta (i + 1)) := hu
      rw [hts] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact ⟨mem_ballStab.1 hcH _ (by rw [SimpleGraph.dist_self]; norm_num),
          (Subgroup.mem_inf.1 hc).1⟩
      · exact ⟨mem_ballStab.1 hcH _ (by rw [D.dist_start_alpha F]),
          P2c.calpha_mem_nbrStab_alpha D h7 hc (i + 1)⟩
      · refine ⟨mem_ballStab.1 hcH _ ?_, ?_⟩
        · have := F.isTree.connected.dist_triangle (u := α) (v := D.beta (i + 1)) (w := u)
          have h1 := D.dist_start_beta F (i + 1)
          have h2 : Γ.dist (D.beta (i + 1)) u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 (by
            have : u ∈ Γ.neighborSet (D.beta (i + 1)) := by rw [hts]; simp
            exact this)
          omega
        · exact P2c.mem_nbrStab_of_comm F hyt hcy
            (P2c.calpha_mem_nbrStab_alpha D h7 hc (i + 1))
    obtain ⟨c, hc, hne1⟩ := hex
    have hc1 := (P2c.fcomm_pair_mem D h7 h512 hZ hc).resolve_left hne1
    rw [Subgroup.zpowers_le, ← hc1]
    exact Subgroup.subset_closure ⟨c, hc, rfl⟩

end CFSG.Quasithin.Fan86

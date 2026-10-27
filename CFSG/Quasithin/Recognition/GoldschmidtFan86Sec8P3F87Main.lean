module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Com
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Path

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace F87

variable {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem InZ.exists_pow {e : G} (he : InZ L α e) : ∃ f : Fin 2, e = L.z α ^ (f : ℕ) := by
  rcases he with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

end F87

open F87 in
theorem fan_8_7 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h512 : Fan512 F L)
    (h82 : Fan82a F L) (h83 : Fan83 F L) (h84 : Fan84a F L) : Fan87 F L := by
  intro α D δ' hY i j hij w hfix hord hsq
  obtain ⟨e₁, e₂, e₃, hsq⟩ := hsq
  have h71c : Fan71c F L := h7.2.2.1
  have hα : valence Γ α = 5 := D.val
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hzc : ∀ s s', L.z (D.alpha s) * L.z (D.alpha s') = L.z (D.alpha s') * L.z (D.alpha s) :=
    fun s s' => zGroup_comm h71c (hzV s) (hzV s')
  have hpath := D.pathSet_branches F h71c hij (a := 2) (b := 2) (by norm_num) (by norm_num)
  have hfix' : ∀ v ∈ pathSet Γ ((D.P i).vert 2) ((D.P j).vert 2), w • v = v := hfix
  have wβi : w • D.beta i = D.beta i :=
    hfix' ((D.P i).vert 1) (by rw [hpath]; exact Or.inl ⟨1, by norm_num, rfl⟩)
  have wβj : w • D.beta j = D.beta j :=
    hfix' ((D.P j).vert 1) (by rw [hpath]; exact Or.inr ⟨1, by norm_num, rfl⟩)
  have wαi : w • D.alpha i = D.alpha i :=
    hfix' ((D.P i).vert 2) (by rw [hpath]; exact Or.inl ⟨2, by norm_num, rfl⟩)
  have wαj : w • D.alpha j = D.alpha j :=
    hfix' ((D.P j).vert 2) (by rw [hpath]; exact Or.inr ⟨2, by norm_num, rfl⟩)
  have hwK : w ∈ nbrStab Γ G α :=
    F.fix_two_nbrs (D.adj_start_beta i) (D.adj_start_beta j)
      (fun h => hij (D.beta_injective F h71c h)) wβi wβj
  have hi : fcomm w (L.z (D.alpha i)) = 1 :=
    fcomm_eq_one_iff.2 ((h71c.comm_z_iff (D.valence_alpha F i) w).2 wαi)
  have hj : fcomm w (L.z (D.alpha j)) = 1 :=
    fcomm_eq_one_iff.2 ((h71c.comm_z_iff (D.valence_alpha F j) w).2 wαj)
  obtain ⟨⟨hmi, hmj, hai, haj, ham, hbi, hbj, hbm, hab⟩, -, -⟩ := fin5_midlab_facts i j hij
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := fin5_kstar_facts i j hij
  obtain ⟨Q1, Q2, Q3⟩ := label_quads h7 h82 D hij
  have hcl := classify h7 h512 h82 h83 D hY hij hwK hi hj
  rcases hcl with hH | hH | hH | hH
  ·
    obtain ⟨v, hv, c, hc, h4, hw, hww⟩ := solo_cases h7 h84 D hH hord
    exact Or.inr (Or.inr (Or.inr ⟨v, hv, c, hc, h4, hw, hww⟩))
  ·
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ ballStab Γ G 2 α,
        w = D.y δ' (kstar i j) * D.y δ' (kstar j i) * h := ⟨_, hH, by group⟩
    rcases pair_cases h7 h512 h83 h84 D hY hab hh with ⟨hV, ε, hε, hsqε⟩ |
        ⟨v, hv, c, hc, h4, rfl, ε, hε, hsqε⟩
    · obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k1, k2] at hsqε
      exact Or.inl ⟨h, hV, f, rfl, by rw [hsqε, hzc j i]⟩
    · exfalso
      obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k1, k2, Q1] at hsqε
      exact no_rel h7 h82 D hij hmi.symm hmj.symm 0 0 f e₁ e₂ e₃ (by
        simpa using hsqε.symm.trans hsq)
  ·
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ ballStab Γ G 2 α,
        w = D.y δ' (kstar i j) * D.y δ' (midlab i j) * h := ⟨_, hH, by group⟩
    rcases pair_cases h7 h512 h83 h84 D hY ham hh with ⟨hV, ε, hε, hsqε⟩ |
        ⟨v, hv, c, hc, h4, rfl, ε, hε, hsqε⟩
    · exfalso
      obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k3, k4] at hsqε
      exact no_rel h7 h82 D hij hbi.symm hbj.symm 0 1 f e₁ e₂ e₃ (by
        simpa using hsqε.symm.trans hsq)
    · obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k3, k4, Q2] at hsqε
      exact Or.inr (Or.inl ⟨v, hv, c, hc, h4, f, by group, hsqε⟩)
  ·
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ ballStab Γ G 2 α,
        w = D.y δ' (kstar j i) * D.y δ' (midlab i j) * h := ⟨_, hH, by group⟩
    rcases pair_cases h7 h512 h83 h84 D hY hbm hh with ⟨hV, ε, hε, hsqε⟩ |
        ⟨v, hv, c, hc, h4, rfl, ε, hε, hsqε⟩
    · exfalso
      obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k5, k6] at hsqε
      exact no_rel h7 h82 D hij hai.symm haj.symm 1 0 f e₁ e₂ e₃ (by
        simpa using hsqε.symm.trans hsq)
    · obtain ⟨f, rfl⟩ := InZ.exists_pow hε
      rw [k5, k6, Q3] at hsqε
      exact Or.inr (Or.inr (Or.inl ⟨v, hv, c, hc, h4, f, by group, hsqε⟩))

end CFSG.Quasithin.Fan86

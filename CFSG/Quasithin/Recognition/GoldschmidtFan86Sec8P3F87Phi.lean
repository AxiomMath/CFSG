module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Sib
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87V
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem mem_ballStab_of_fcomm (h7 : Fan7 F L) (D : D10Set L α) {g : G}
    (hg : g ∈ nbrStab Γ G α) (h : ∀ s, fcomm g (L.z (D.alpha s)) = 1) :
    g ∈ ballStab Γ G 2 α := by
  have h71c : Fan71c F L := h7.2.2.1
  have hgs : g • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hg)
  have hfix : ∀ s, g • D.alpha s = D.alpha s := fun s =>
    (h71c.comm_z_iff (D.valence_alpha F s) g).1 (fcomm_eq_one_iff.1 (h s))
  refine mem_ballStab.2 fun w hw => ?_
  have hd : Γ.dist α w = 0 ∨ Γ.dist α w = 1 ∨ Γ.dist α w = 2 := by omega
  rcases hd with h0 | h1 | h2
  · have := F.isTree.connected.dist_eq_zero_iff.1 h0
    subst this
    exact hgs
  · exact mem_nbrStab.1 hg w (SimpleGraph.dist_eq_one_iff_adj.1 h1)
  · obtain ⟨β, hβw, hαβ⟩ := IsTree.exists_adj_dist_succ F.isTree (u := α) (v := w) (n := 1) h2
    obtain ⟨s, rfl⟩ := D.exists_beta_eq F h71c (SimpleGraph.dist_eq_one_iff_adj.1 hαβ)
    have hk : g ∈ nbrStab Γ G (D.beta s) :=
      F.fix_two_nbrs (D.adj_start_beta s).symm (D.adj_beta_alpha s) (D.alpha_ne_start s).symm hgs
        (hfix s)
    exact mem_nbrStab.1 hk w hβw

theorem prod_fcomm_eq_one (h7 : Fan7 F L) (h512 : Fan512 F L) (h82 : Fan82a F L)
    (D : D10Set L α) {g : G} (hg : g ∈ nbrStab Γ G α) :
    prodFive (fun s => fcomm g (L.z (D.alpha s))) = 1 := by
  have hz : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have key : fcomm g (L.z (D.alpha 0) * L.z (D.alpha 1) * L.z (D.alpha 2) * L.z (D.alpha 3) *
      L.z (D.alpha 4)) = prodFive (fun s => fcomm g (L.z (D.alpha s))) := by
    unfold prodFive
    rw [fcomm_mul_V h7 h512 D.val hg
        (mul_mem (mul_mem (mul_mem (hz 0) (hz 1)) (hz 2)) (hz 3)) (hz 4),
      fcomm_mul_V h7 h512 D.val hg (mul_mem (mul_mem (hz 0) (hz 1)) (hz 2)) (hz 3),
      fcomm_mul_V h7 h512 D.val hg (mul_mem (hz 0) (hz 1)) (hz 2),
      fcomm_mul_V h7 h512 D.val hg (hz 0) (hz 1)]
  rw [← key]
  have := h82 α D
  unfold prodFive at this
  rw [this]
  simp [fcomm]

theorem fcomm_quot (hα : valence Γ α = 5) {g₁ g₂ z : G} (hg₁ : g₁ ∈ MulAction.stabilizer G α)
    (hg₂ : g₂ ∈ MulAction.stabilizer G α) (h1 : InZ L α (fcomm g₁ z))
    (h2 : fcomm g₂ z = fcomm g₁ z) : fcomm (g₁⁻¹ * g₂) z = 1 := by
  have e1 : fcomm g₁⁻¹ z = g₁ * (fcomm g₁ z)⁻¹ * g₁⁻¹ := by
    unfold fcomm
    group
  rw [fcomm_mul_left, e1, h2, (InZ.conj hα hg₁ (InZ.inv hα h1)).2,
    (InZ.conj hα hg₂ (InZ.inv hα h1)).1, inv_mul_cancel]

theorem y_mem_nbrStab (h83a : Fan83a F L) (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ')
    (k : Fin 5) : D.y δ' k ∈ nbrStab Γ G α := by
  rw [h83a α D δ' hY]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, rfl⟩)

theorem fcomm_pair (h83b : Fan83b F L) (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ')
    (hyK : ∀ k, D.y δ' k ∈ nbrStab Γ G α) (hα : valence Γ α = 5) {k l : Fin 5} (hkl : k ≠ l)
    (s : Fin 5) : fcomm (D.y δ' k * D.y δ' l) (L.z (D.alpha s)) =
      if s = k ∨ s = l then L.z α else 1 := by
  have hl : D.y δ' l ∈ MulAction.stabilizer G α := F.nbrStab_le_stabilizer α (hyK l)
  have hk' := h83b α D δ' hY k s
  have hl' := h83b α D δ' hY l s
  have hZk : InZ L α (fcomm (D.y δ' k) (L.z (D.alpha s))) := by
    rw [hk']
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [fcomm_mul_left, (InZ.conj hα hl hZk).1, hk', hl']
  by_cases hsk : s = k
  · subst hsk
    simp [hkl, Ne.symm hkl]
  · by_cases hsl : s = l
    · subst hsl
      simp [hsk, hkl]
    · have := L.z_mul_self hα
      simp [hsk, hsl, Ne.symm hsk, Ne.symm hsl, this]

set_option linter.unusedSimpArgs false in
open scoped IsMulCommutative in
theorem classify (h7 : Fan7 F L) (h512 : Fan512 F L) (h82 : Fan82a F L) (h83 : Fan83 F L)
    (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) {w : G}
    (hw : w ∈ nbrStab Γ G α) (hi : fcomm w (L.z (D.alpha i)) = 1)
    (hj : fcomm w (L.z (D.alpha j)) = 1) :
    w ∈ ballStab Γ G 2 α ∨
    (D.y δ' (kstar i j) * D.y δ' (kstar j i))⁻¹ * w ∈ ballStab Γ G 2 α ∨
    (D.y δ' (kstar i j) * D.y δ' (midlab i j))⁻¹ * w ∈ ballStab Γ G 2 α ∨
    (D.y δ' (kstar j i) * D.y δ' (midlab i j))⁻¹ * w ∈ ballStab Γ G 2 α := by
  obtain ⟨h83a, h83b, -⟩ := h83
  have h71c : Fan71c F L := h7.2.2.1
  have hα : valence Γ α = 5 := D.val
  have hyK := y_mem_nbrStab h83a D hY
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hφ : ∀ s, InZ L α (fcomm w (L.z (D.alpha s))) := fun s =>
    fcomm_mem_Z h7 h512 hα hw (hzV s)
  have hzαV : L.z α ∈ L.zGroup 2 α := z_mem_zGroup (by simp) hα
  have hφV : ∀ s, fcomm w (L.z (D.alpha s)) ∈ L.zGroup 2 α := fun s => by
    rcases hφ s with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact hzαV
  have hre : fcomm w (L.z (D.alpha i)) * fcomm w (L.z (D.alpha j)) *
      fcomm w (L.z (D.alpha (kstar i j))) * fcomm w (L.z (D.alpha (kstar j i))) *
      fcomm w (L.z (D.alpha (midlab i j))) = 1 := by
    have := isMulCommutative_zGroup (α := α) h71c
    have h := prodFive_reindex
      (fun s => (⟨fcomm w (L.z (D.alpha s)), hφV s⟩ : ↥(L.zGroup 2 α))) hij
    have h1 : prodFive
        (fun s => (⟨fcomm w (L.z (D.alpha s)), hφV s⟩ : ↥(L.zGroup 2 α))) = 1 :=
      Subtype.ext (by simpa [prodFive] using prod_fcomm_eq_one h7 h512 h82 D hw)
    rw [h1] at h
    simpa using (congrArg Subtype.val h).symm
  rw [hi, hj, one_mul, one_mul] at hre
  obtain ⟨⟨hmi, hmj, hai, haj, ham, hbi, hbj, hbm, hab⟩, -, hall⟩ := fin5_midlab_facts i j hij
  have key : ∀ k l, k ≠ l →
      (∀ s, fcomm w (L.z (D.alpha s)) = if s = k ∨ s = l then L.z α else 1) →
      (D.y δ' k * D.y δ' l)⁻¹ * w ∈ ballStab Γ G 2 α := by
    intro k l hkl hs
    have hYK : D.y δ' k * D.y δ' l ∈ nbrStab Γ G α := mul_mem (hyK k) (hyK l)
    refine mem_ballStab_of_fcomm h7 D (mul_mem (inv_mem hYK) hw) fun s => ?_
    refine fcomm_quot (L := L) hα (F.nbrStab_le_stabilizer α hYK)
      (F.nbrStab_le_stabilizer α hw) ?_ ?_
    · rw [fcomm_pair h83b D hY hyK hα hkl s]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rw [fcomm_pair h83b D hY hyK hα hkl s, hs s]
  have hmi' := hmi.symm
  have hmj' := hmj.symm
  have hai' := hai.symm
  have haj' := haj.symm
  have ham' := ham.symm
  have hbi' := hbi.symm
  have hbj' := hbj.symm
  have hbm' := hbm.symm
  have hab' := hab.symm
  have hz1 := L.z_ne_one hα
  have hzz := L.z_mul_self hα
  rcases hφ (kstar i j) with ha | ha <;> rcases hφ (kstar j i) with hb | hb <;>
    rcases hφ (midlab i j) with hm | hm <;> rw [ha, hb, hm] at hre
  · left
    exact mem_ballStab_of_fcomm h7 D hw fun s => by
      rcases hall s with h | h | h | h | h <;> rw [h] <;> assumption
  · exact absurd (by simpa using hre) hz1
  · exact absurd (by simpa using hre) hz1
  · right; right; right
    refine key _ _ hbm fun s => ?_
    rcases hall s with h | h | h | h | h <;> rw [h] <;> simp [hmi, hmi', hmj, hmj', hai, hai', haj,
      haj', ham, ham', hbi, hbi', hbj, hbj', hbm, hbm', hab, hab', hi, hj, ha, hb, hm]
  · exact absurd (by simpa using hre) hz1
  · right; right; left
    refine key _ _ ham fun s => ?_
    rcases hall s with h | h | h | h | h <;> rw [h] <;> simp [hmi, hmi', hmj, hmj', hai, hai', haj,
      haj', ham, ham', hbi, hbi', hbj, hbj', hbm, hbm', hab, hab', hi, hj, ha, hb, hm]
  · right; left
    refine key _ _ hab fun s => ?_
    rcases hall s with h | h | h | h | h <;> rw [h] <;> simp [hmi, hmi', hmj, hmj', hai, hai', haj,
      haj', ham, ham', hbi, hbi', hbj, hbj', hbm, hbm', hab, hab', hi, hj, ha, hb, hm]
  · exact absurd (by simpa [hzz] using hre) hz1

end CFSG.Quasithin.Fan86.F87

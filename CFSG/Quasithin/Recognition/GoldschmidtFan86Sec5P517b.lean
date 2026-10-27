module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Prod
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

open P62

variable (F : FanTree Γ G) {α : V} {z : G} (h : Lab5 Γ α z) {N : Subgroup G}
include F h

theorem lb_not_mem (h40 : Fan40 F) (hN : ∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hH : ∀ l m : V, Γ.dist α l = 2 → Γ.dist α m = 2 → Γ.dist l m = 4 →
      P514.Lb z α l * P514.Lb z α m ∉ N) {l : V} (hl : Γ.dist α l = 2) :
    P514.Lb z α l ∉ N := by
  intro hln
  obtain ⟨ν, hν⟩ := exists_br F hl
  obtain ⟨ν', hν'a, hν'⟩ := F.exists_adj_ne α ν
  obtain ⟨m, hm, hmα⟩ := F.exists_adj_ne ν' α
  have hbr : Br Γ α ν' m := ⟨hν'a, hm, hmα⟩
  obtain ⟨k, hk, hkm⟩ := exists_stab_smul_br F h40 h.val5 hν hbr
  have hmN : P514.Lb z α m ∈ N := by
    rw [← hkm, ← lb_conj F h hl k]
    exact hN k hk _ hln
  exact hH l m hl (Br.dist_two F hbr) (dist_four F hν hbr hν'.symm) (N.mul_mem hln hmN)

theorem same_branch_mem (hzN : z ∈ N) {ν l l' : V} (hν : Br Γ α ν l) (hν' : Br Γ α ν l') :
    P514.Lb z α l * P514.Lb z α l' ∈ N := by
  have hl := Br.dist_two F hν
  by_cases hll : l = l'
  · rw [← hll, lb_sq F h hl]
    exact N.one_mem
  · rw [sib F h hν hν' hll, ← mul_assoc, lb_sq F h hl, one_mul]
    exact hzN

theorem lb_mul_comm {l m : V} (hl : Γ.dist α l = 2) (hm : Γ.dist α m = 2) :
    ∃ e ∈ Subgroup.zpowers z,
      P514.Lb z α l * P514.Lb z α m = P514.Lb z α m * P514.Lb z α l * e := by
  refine ⟨fcomm (P514.Lb z α l) (P514.Lb z α m), comm_lab F h hl hm, ?_⟩
  unfold fcomm
  group

theorem lb_comm_zpow {l : V} (hl : Γ.dist α l = 2) {e : G} (he : e ∈ Subgroup.zpowers z) :
    e * P514.Lb z α l = P514.Lb z α l * e := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  exact (Commute.zpow_left (show Commute z (P514.Lb z α l) from (lb_comm_z F h hl).symm) n).eq

local notation "lb" => P514.Lb z α

theorem key_step (hzN : z ∈ N) (hN : ∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hH : ∀ l m : V, Γ.dist α l = 2 → Γ.dist α m = 2 → Γ.dist l m = 4 → lb l * lb m ∉ N)
    {l₁ l₂ l₃ ν₁ ν₂ ν₃ : V} {s : G} (h1 : Br Γ α ν₁ l₁) (h2 : Br Γ α ν₂ l₂)
    (h3 : Br Γ α ν₃ l₃) (hs : s ∈ MulAction.stabilizer G α) (hs1 : s • ν₁ = ν₂)
    (hs2 : s • ν₂ = ν₁) (hs3 : s • ν₃ ≠ ν₃) (hP : lb l₁ * lb l₂ * lb l₃ ∈ N) : False := by
  have hsα : s • α = α := MulAction.mem_stabilizer_iff.1 hs
  have d1 := Br.dist_two F h1
  have d2 := Br.dist_two F h2
  have d3 := Br.dist_two F h3
  have b1 : Br Γ α ν₂ (s • l₁) := by
    have := Br.smul F s h1
    rwa [hsα, hs1] at this
  have b2 : Br Γ α ν₁ (s • l₂) := by
    have := Br.smul F s h2
    rwa [hsα, hs2] at this
  have b3 : Br Γ α (s • ν₃) (s • l₃) := by
    have := Br.smul F s h3
    rwa [hsα] at this
  have hd3 : Γ.dist α (s • l₃) = 2 := Br.dist_two F b3
  have hconj : s * (lb l₁ * lb l₂ * lb l₃) * s⁻¹ = lb (s • l₁) * lb (s • l₂) * lb (s • l₃) := by
    rw [← lb_conj F h d1 s, ← lb_conj F h d2 s, ← lb_conj F h d3 s]
    group
  have hCN : Subgroup.zpowers z ≤ N := Subgroup.zpowers_le.2 hzN
  obtain ⟨c₂, hc₂C, e₂⟩ : ∃ c₂, c₂ ∈ Subgroup.zpowers z ∧ lb (s • l₁) = lb l₂ * c₂ := by
    rcases label_br F h b1 h2 with e | e
    · exact ⟨1, Subgroup.one_mem _, by rw [e, mul_one]⟩
    · exact ⟨z, Subgroup.mem_zpowers z, e⟩
  obtain ⟨c₃, hc₃C, e₃⟩ : ∃ c₃, c₃ ∈ Subgroup.zpowers z ∧ lb (s • l₂) = lb l₁ * c₃ := by
    rcases label_br F h b2 h1 with e | e
    · exact ⟨1, Subgroup.one_mem _, by rw [e, mul_one]⟩
    · exact ⟨z, Subgroup.mem_zpowers z, e⟩
  have hPs := hN s hs _ hP
  rw [hconj, e₂, e₃] at hPs
  obtain ⟨c₁, hc₁C, hab⟩ := lb_mul_comm F h d1 d2
  have key := key_alg (N := N) (hCN hc₁C) (hCN hc₂C) (hCN hc₃C)
    (lb_comm_zpow F h d1 hc₂C).symm (lb_comm_zpow F h hd3 hc₂C) (lb_comm_zpow F h hd3 hc₃C)
    (lb_comm_zpow F h hd3 hc₁C) hab hP hPs
  rw [lb_inv F h d3] at key
  exact hH l₃ (s • l₃) d3 hd3 (dist_four F h3 b3 (Ne.symm hs3)) key

theorem triple_not_mem (h40 : Fan40 F) (hzN : z ∈ N)
    (hN : ∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hH : ∀ l m : V, Γ.dist α l = 2 → Γ.dist α m = 2 → Γ.dist l m = 4 → lb l * lb m ∉ N)
    {l₁ l₂ l₃ : V} (h1 : Γ.dist α l₁ = 2) (h2 : Γ.dist α l₂ = 2) (h3 : Γ.dist α l₃ = 2) :
    lb l₁ * lb l₂ * lb l₃ ∉ N := by
  intro hP
  obtain ⟨ν₁, hν₁⟩ := exists_br F h1
  obtain ⟨ν₂, hν₂⟩ := exists_br F h2
  obtain ⟨ν₃, hν₃⟩ := exists_br F h3
  have hno : ∀ {l : V}, Γ.dist α l = 2 → lb l ∉ N := fun hl => lb_not_mem F h h40 hN hH hl
  have hCN : Subgroup.zpowers z ≤ N := Subgroup.zpowers_le.2 hzN
  by_cases e12 : ν₁ = ν₂
  · subst e12
    have hab := same_branch_mem F h hzN hν₁ hν₂
    apply hno h3
    have := N.mul_mem (N.inv_mem hab) hP
    rwa [inv_mul_cancel_left] at this
  by_cases e23 : ν₂ = ν₃
  · subst e23
    have hbc := same_branch_mem F h hzN hν₂ hν₃
    apply hno h1
    have h6 := N.mul_mem hP (N.inv_mem hbc)
    have e : lb l₁ * lb l₂ * lb l₃ * (lb l₂ * lb l₃)⁻¹ = lb l₁ := by group
    rwa [e] at h6
  obtain ⟨e, he, hbc⟩ := lb_mul_comm F h h2 h3
  by_cases e13 : ν₁ = ν₃
  · subst e13
    have hac := same_branch_mem F h hzN hν₁ hν₃
    apply hno h2
    have hP' : lb l₁ * lb l₃ * (lb l₂ * e) ∈ N := by
      have : lb l₁ * lb l₃ * (lb l₂ * e) = lb l₁ * lb l₂ * lb l₃ := by
        calc lb l₁ * lb l₃ * (lb l₂ * e) = lb l₁ * (lb l₃ * lb l₂ * e) := by simp only [mul_assoc]
          _ = lb l₁ * (lb l₂ * lb l₃) := by rw [← hbc]
          _ = lb l₁ * lb l₂ * lb l₃ := by simp only [mul_assoc]
      rw [this]
      exact hP
    have h6 := N.mul_mem (N.inv_mem hac) hP'
    rw [inv_mul_cancel_left] at h6
    have := N.mul_mem h6 (N.inv_mem (hCN he))
    rwa [mul_inv_cancel_right] at this
  rcases swap_third F h.val5 hν₁.1 hν₂.1 hν₃.1 e12 e13 with ⟨s, hs, s1, s2, s3⟩ |
      ⟨s, hs, s1, s2, s3⟩
  · exact key_step F h hzN hN hH hν₁ hν₂ hν₃ hs s1 s2 s3 hP
  · refine key_step F h hzN hN hH hν₁ hν₃ hν₂ hs s1 s2 s3 ?_
    obtain ⟨e', he', hcb⟩ := lb_mul_comm F h h3 h2
    have : lb l₁ * lb l₃ * lb l₂ = lb l₁ * lb l₂ * lb l₃ * e' := by
      calc lb l₁ * lb l₃ * lb l₂ = lb l₁ * (lb l₃ * lb l₂) := by simp only [mul_assoc]
        _ = lb l₁ * (lb l₂ * lb l₃ * e') := by rw [hcb]
        _ = lb l₁ * lb l₂ * lb l₃ * e' := by simp only [mul_assoc]
    rw [this]
    exact N.mul_mem hP (hCN he')

end P517

theorem fan517b (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (hXi : ∃ T : Track Γ G, InXi T) :
    Fan40 F → ∀ (α : V) (z : G) (N : Subgroup G), valence Γ α ≠ 3 → z ∈ Cinv G α → z ∈ N →
      N ≤ MulAction.stabilizer G α → (∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      (∀ g h : G, Γ.dist α (g • α) = 2 → Γ.dist α (h • α) = 2 → Γ.dist (g • α) (h • α) = 4 →
        g * z * g⁻¹ * (h * z * h⁻¹) ∉ N) →
      ∀ g₁ g₂ g₃ : G, Γ.dist α (g₁ • α) = 2 → Γ.dist α (g₂ • α) = 2 → Γ.dist α (g₃ • α) = 2 →
        g₁ * z * g₁⁻¹ * (g₂ * z * g₂⁻¹) * (g₃ * z * g₃⁻¹) ∉ N := by
  intro h40 α z N hα hz hzN _ hN hH g₁ g₂ g₃ d₁ d₂ d₃
  have h35 : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence α
  have h := P517.lab5_of F h510 h511 h53a h40 hXi hz (by omega)
  have hH' : ∀ l m : V, Γ.dist α l = 2 → Γ.dist α m = 2 → Γ.dist l m = 4 →
      P514.Lb z α l * P514.Lb z α m ∉ N := by
    intro l m hl hm hlm
    obtain ⟨g, hg⟩ := P517.exists_conj_of_dist F h hl
    obtain ⟨g', hg'⟩ := P517.exists_conj_of_dist F h hm
    subst hg hg'
    rw [P514.Lb_eq h.cinv rfl, P514.Lb_eq h.cinv rfl]
    exact hH g g' hl hm hlm
  have e : ∀ g : G, g * z * g⁻¹ = P514.Lb z α (g • α) := fun g => (P514.Lb_eq h.cinv rfl).symm
  rw [e g₁, e g₂, e g₃]
  exact P517.triple_not_mem F h h40 hzN hN hH' d₁ d₂ d₃

end CFSG.Quasithin.Fan86

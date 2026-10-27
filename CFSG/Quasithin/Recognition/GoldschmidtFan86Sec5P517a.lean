module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517Lab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

theorem fcomm_eq_one {a b : G} (h : a * b = b * a) : fcomm a b = 1 := by
  unfold fcomm
  calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
    _ = a⁻¹ * b⁻¹ * (b * a) := by rw [h]
    _ = 1 := by group

theorem fcomm_closure {S : Set G} {z : G} (hcz : ∀ s ∈ S, s * z = z * s)
    (hS : ∀ s ∈ S, ∀ t ∈ S, fcomm s t ∈ Subgroup.zpowers z) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, fcomm x y ∈ Subgroup.zpowers z := by
  have hcen : ∀ x ∈ Subgroup.closure S, x * z = z * x := by
    intro x hx
    have : Subgroup.closure S ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.1 hk]
      exact (hcz s hs).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  have hC : ∀ c ∈ Subgroup.zpowers z, ∀ x ∈ Subgroup.closure S, x * c = c * x := by
    intro c hc x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (show Commute x z from hcen x hx) n).eq
  have claim1 : ∀ s ∈ S, ∀ y ∈ Subgroup.closure S, fcomm s y ∈ Subgroup.zpowers z := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hS s hs t ht
    | one => simp [fcomm]
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      have hcomm : y₂ * fcomm s y₁ = fcomm s y₁ * y₂ := hC _ ih₁ y₂ hy₂
      have e : fcomm s (y₁ * y₂) = s⁻¹ * y₂⁻¹ * s * (fcomm s y₁ * y₂) := by unfold fcomm; group
      have e2 : fcomm s y₂ * fcomm s y₁ = s⁻¹ * y₂⁻¹ * s * (y₂ * fcomm s y₁) := by
        unfold fcomm; group
      rw [e, ← hcomm, ← e2]
      exact Subgroup.mul_mem _ ih₂ ih₁
    | inv y hy ih =>
      have hcomm : y * (fcomm s y)⁻¹ = (fcomm s y)⁻¹ * y :=
        hC _ (Subgroup.inv_mem _ ih) y hy
      have e : fcomm s y⁻¹ = y * (fcomm s y)⁻¹ * y⁻¹ := by unfold fcomm; group
      rw [e, hcomm]
      simpa using Subgroup.inv_mem _ ih
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact claim1 s hs y hy
  | one => simp [fcomm]
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    have hcomm : x₂ * fcomm x₁ y = fcomm x₁ y * x₂ := hC _ ih₁ x₂ hx₂
    have hinv : x₂⁻¹ * fcomm x₁ y = fcomm x₁ y * x₂⁻¹ := by
      calc x₂⁻¹ * fcomm x₁ y = x₂⁻¹ * (fcomm x₁ y * x₂) * x₂⁻¹ := by group
        _ = x₂⁻¹ * (x₂ * fcomm x₁ y) * x₂⁻¹ := by rw [← hcomm]
        _ = fcomm x₁ y * x₂⁻¹ := by group
    have e : fcomm (x₁ * x₂) y = fcomm x₁ y * fcomm x₂ y := by
      calc fcomm (x₁ * x₂) y = x₂⁻¹ * (fcomm x₁ y * y⁻¹) * x₂ * y := by unfold fcomm; group
        _ = (x₂⁻¹ * fcomm x₁ y) * y⁻¹ * x₂ * y := by group
        _ = (fcomm x₁ y * x₂⁻¹) * y⁻¹ * x₂ * y := by rw [hinv]
        _ = fcomm x₁ y * fcomm x₂ y := by unfold fcomm; group
    rw [e]
    exact Subgroup.mul_mem _ ih₁ ih₂
  | inv x hx ih =>
    have hcomm : x * (fcomm x y)⁻¹ = (fcomm x y)⁻¹ * x := hC _ (Subgroup.inv_mem _ ih) x hx
    have e : fcomm x⁻¹ y = x * (fcomm x y)⁻¹ * x⁻¹ := by unfold fcomm; group
    rw [e, hcomm]
    simpa using Subgroup.inv_mem _ ih

variable (F : FanTree Γ G) {α : V} {z : G} (h : Lab5 Γ α z)
include F h

theorem zBall_cases {w : G} (hw : w ∈ zBall Γ α z 2) :
    w = z ∨ ∃ l, Γ.dist α l = 2 ∧ w = P514.Lb z α l := by
  obtain ⟨g, hg, rfl⟩ := hw
  have hcases : Γ.dist α (g • α) = 0 ∨ Γ.dist α (g • α) = 1 ∨ Γ.dist α (g • α) = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · left
    have h' : α = g • α := F.isTree.connected.dist_eq_zero_iff.1 h0
    have hgs : g ∈ MulAction.stabilizer G α := MulAction.mem_stabilizer_iff.2 h'.symm
    rw [h.cinv.2.2.2 g hgs]
    group
  · exfalso
    have hadj := dist_eq_one_iff_adj.1 h1
    have hne := F.alternating _ _ hadj
    have hv := F.valence_smul_eq g α
    change valence Γ α ≠ valence Γ (g • α) at hne
    omega
  · exact Or.inr ⟨g • α, h2, (P514.Lb_eq h.cinv rfl).symm⟩

theorem zBall_mem_nbrStab {w : G} (hw : w ∈ zBall Γ α z 2) : w ∈ nbrStab Γ G α := by
  rcases zBall_cases F h hw with rfl | ⟨l, hl, rfl⟩
  · exact P62.cinv_mem_nbrStab F h.cinv
  · exact lb_ker F h hl

theorem fan517a_of : Subgroup.closure (zBall Γ α z 2) ≤ nbrStab Γ G α ∧
    ∀ x ∈ Subgroup.closure (zBall Γ α z 2), ∀ y ∈ Subgroup.closure (zBall Γ α z 2),
      fcomm x y ∈ Subgroup.zpowers z := by
  refine ⟨(Subgroup.closure_le _).2 fun w hw => zBall_mem_nbrStab F h hw, ?_⟩
  refine fcomm_closure (fun s hs => ?_) fun s hs t ht => ?_
  · exact h.cinv.2.2.2 s (F.nbrStab_le_stabilizer α (zBall_mem_nbrStab F h hs))
  · obtain hs' | ⟨l, hl, hs'⟩ := zBall_cases F h hs
    all_goals obtain ht' | ⟨m, hm, ht'⟩ := zBall_cases F h ht
    · rw [hs', ht']
      rw [fcomm_eq_one rfl]
      exact Subgroup.one_mem _
    · rw [hs', ht', fcomm_eq_one (lb_comm_z F h hm).symm]
      exact Subgroup.one_mem _
    · rw [hs', ht', fcomm_eq_one (lb_comm_z F h hl)]
      exact Subgroup.one_mem _
    · rw [hs', ht']
      exact comm_lab F h hl hm

end P517

theorem fan517a (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (hXi : ∃ T : Track Γ G, InXi T) : Fan517a F := by
  intro h40 α z hα hz
  have h35 : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence α
  exact P517.fan517a_of F (P517.lab5_of F h510 h511 h53a h40 hXi hz (by omega))

end CFSG.Quasithin.Fan86

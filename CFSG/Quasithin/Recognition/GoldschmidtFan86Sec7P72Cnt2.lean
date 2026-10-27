module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Cnt1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Asm1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Key3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem br_data (F : FanTree Γ G) {α ν l : V} (hα : valence Γ α = 5) (b : Br Γ α ν l) :
    Γ.dist α l ≤ 2 ∧ valence Γ l = 5 :=
  ⟨by rw [SimpleGraph.dist_comm, b.dist_alpha F.isTree], (b.valence F hα).2⟩

theorem zGroup_card_le (h : Fan71c F L) (hlab : Lab3 F L) {α : V} (hα : valence Γ α = 5) :
    Finite ↥(L.zGroup 2 α) ∧ Nat.card ↥(L.zGroup 2 α) ≤ 2 ^ 5 := by
  classical
  obtain ⟨x1, x2, x3, x4, a01, a12, a23, a34, n02, n13, n24⟩ := exists_arc4 F α
  have A : Arc4 Γ α x1 x2 x3 x4 := ⟨a01, a12, a23, a34, n02, n13, n24⟩
  obtain ⟨y₁, y₂, hy₁, hy₂, hnd, hall⟩ := exists_pairs F h hα A
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10⟩ := hnd
  obtain ⟨la, hla, hlaα⟩ := F.exists_adj_ne y₁ α
  obtain ⟨lc, hlc, hlcα⟩ := F.exists_adj_ne y₂ α
  have ba : Br Γ α y₁ la := ⟨hy₁, hla, hlaα⟩
  have bc : Br Γ α y₂ lc := ⟨hy₂, hlc, hlcα⟩
  have ba' := br_smul_s h hα A ba
  have bc' := br_smul_s h hα A bc
  have bx : Br Γ α x1 x2 := ⟨a01, a12, n02.symm⟩
  have hkey := key h hlab hα A ba bc (fun e => n1 e.symm) (fun e => n3 e.symm) n6
    (fun e => n8 e.symm)
  let S : Finset G := {L.z α, L.z la, L.z (L.z x4 • la), L.z lc, L.z (L.z x4 • lc)}
  have hSd : ∀ x ∈ S, ∃ δ, Γ.dist α δ ≤ 2 ∧ valence Γ δ = 5 ∧ x = L.z δ := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨α, by rw [SimpleGraph.dist_self]; omega, hα, rfl⟩
    · exact ⟨la, (br_data F hα ba).1, (br_data F hα ba).2, rfl⟩
    · exact ⟨_, (br_data F hα ba').1, (br_data F hα ba').2, rfl⟩
    · exact ⟨lc, (br_data F hα bc).1, (br_data F hα bc).2, rfl⟩
    · exact ⟨_, (br_data F hα bc').1, (br_data F hα bc').2, rfl⟩
  have hcS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨δ, d1, v1, rfl⟩ := hSd x hx
    obtain ⟨δ', d2, v2, rfl⟩ := hSd y hy
    exact z_comm_two h v1 v2 d1 d2
  have hiS : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨δ, -, v, rfl⟩ := hSd x hx
    exact L.z_mul_self v
  obtain ⟨hfin, hcard⟩ := card_closure_le S hcS hiS
  have hu : L.z α ∈ Subgroup.closure (S : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.2 (by simp [S]))
  have hA : L.z la ∈ Subgroup.closure (S : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.2 (by simp [S]))
  have hA' : L.z (L.z x4 • la) ∈ Subgroup.closure (S : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.2 (by simp [S]))
  have hC : L.z lc ∈ Subgroup.closure (S : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.2 (by simp [S]))
  have hC' : L.z (L.z x4 • lc) ∈ Subgroup.closure (S : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.2 (by simp [S]))
  have hX : L.z x2 ∈ Subgroup.closure (S : Set G) := by
    rw [← hkey]
    exact mul_mem (mul_mem (mul_mem hA hA') hC) hC'
  have alt : ∀ {l δ : V}, (L.z δ = L.z l ∨ L.z δ = L.z l * L.z α) →
      L.z l ∈ Subgroup.closure (S : Set G) → L.z δ ∈ Subgroup.closure (S : Set G) := by
    intro l δ hh hl
    rcases hh with e | e
    · rw [e]
      exact hl
    · rw [e]
      exact mul_mem hl hu
  have hle : L.zGroup 2 α ≤ Subgroup.closure (S : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨δ, hd, hv, rfl⟩
    have hd' : Γ.dist α δ = 0 ∨ Γ.dist α δ = 1 ∨ Γ.dist α δ = 2 := by omega
    rcases hd' with h0 | h1 | h2
    · have : α = δ := ((F.isTree.connected.preconnected α δ).dist_eq_zero_iff).1 h0
      rw [← this]
      exact hu
    · have := valence_adj_three F hα (dist_eq_one_iff_adj.mp h1)
      omega
    · obtain ⟨ν, b⟩ := br_of_dist_two F.isTree h2
      rcases hall ν b.a1 with e | e | e | e | e
      · rw [e] at b
        exact alt (branch_alt hlab hα bx b) hX
      · rw [e] at b
        exact alt (branch_alt hlab hα ba b) hA
      · rw [e] at b
        exact alt (branch_alt hlab hα ba' b) hA'
      · rw [e] at b
        exact alt (branch_alt hlab hα bc b) hC
      · rw [e] at b
        exact alt (branch_alt hlab hα bc' b) hC'
  have := hfin
  refine ⟨Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), ?_⟩
  calc Nat.card ↥(L.zGroup 2 α) ≤ Nat.card ↥(Subgroup.closure (S : Set G)) :=
        Subgroup.card_le_of_le hle
    _ ≤ 2 ^ S.card := hcard
    _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) Finset.card_le_five

end P72

end CFSG.Quasithin.Fan86

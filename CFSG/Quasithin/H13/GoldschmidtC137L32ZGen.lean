module

public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

structure ZFacts (L N W : Subgroup G) (u z : G) : Prop where
  hLN : L ≤ normalizer (N : Set G)
  hperf : Group.IsPerfect ↥L
  hzN : z ∈ N
  hzC : ∀ n ∈ N, n * z = z * n
  hWN : W ≤ N
  hNW : ∀ n ∈ N, ∀ w ∈ W, n * w = w * n
  hWL : ⁅W, L⁆ = W
  huW : u ∈ W

theorem centerOf_comm_gc (X : Subgroup G) : ∀ a ∈ centerOf X, ∀ b ∈ centerOf X, a * b = b * a :=
  fun a ha _ hb => Subgroup.mem_centralizer_iff.1 hb.2 a ha.1

theorem mem_normalizer_inf_gc {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  exact ⟨fun ⟨ha, hb⟩ => ⟨(hA h).1 ha, (hB h).1 hb⟩, fun ⟨ha, hb⟩ => ⟨(hA h).2 ha, (hB h).2 hb⟩⟩

namespace ZFacts

variable {L N W : Subgroup G} {u z : G} (F : ZFacts L N W u z)
include F

theorem hQN : ⁅N, L⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp F.hLN

theorem hLQ : L ≤ normalizer ((⁅N, L⁆ : Subgroup G) : Set G) := fun _ hg =>
  SBd5.mem_normalizer_commutator_of (F.hLN hg) (Subgroup.le_normalizer hg)

theorem hWQ : W ≤ ⁅N, L⁆ := by
  have := Subgroup.commutator_mono F.hWN (le_refl L)
  rwa [F.hWL] at this

theorem hWZ : W ≤ centerOf ⁅N, L⁆ := fun w hw =>
  ⟨F.hWQ hw, Subgroup.mem_centralizer_iff.2 fun q hq => F.hNW q (F.hQN hq) w hw⟩

theorem hWU : W ≤ ⁅centerOf ⁅N, L⁆, L⁆ := by
  have := Subgroup.commutator_mono F.hWZ (le_refl L)
  rwa [F.hWL] at this

theorem hcQ : ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ ⁅N, L⁆ := by
  intro k hk
  have h1 : ⁅k, z⁆ ∈ ⁅L, N⁆ := Subgroup.commutator_mem_commutator hk F.hzN
  rw [Subgroup.commutator_comm] at h1
  simpa [commutatorElement_def] using h1

theorem hcC : ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ centralizer ((⁅N, L⁆ : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqN : q ∈ N := F.hQN hq
  have hq' : k⁻¹ * q * k ∈ ⁅N, L⁆ :=
    (Subgroup.mem_normalizer_iff''.1 (F.hLQ hk) q).1 hq
  have h1 : z⁻¹ * q = q * z⁻¹ := by
    have := F.hzC q hqN
    calc z⁻¹ * q = z⁻¹ * (q * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * q) * z⁻¹ := by rw [this]
      _ = q * z⁻¹ := by group
  have h2 := F.hzC _ (F.hQN hq')
  calc q * (k * z * k⁻¹ * z⁻¹) = k * ((k⁻¹ * q * k) * z) * k⁻¹ * z⁻¹ := by group
    _ = k * (z * (k⁻¹ * q * k)) * k⁻¹ * z⁻¹ := by rw [h2]
    _ = k * z * k⁻¹ * (q * z⁻¹) := by group
    _ = k * z * k⁻¹ * (z⁻¹ * q) := by rw [h1]
    _ = k * z * k⁻¹ * z⁻¹ * q := by group

theorem hcZ : ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ centerOf ⁅N, L⁆ := fun k hk => ⟨F.hcQ k hk, F.hcC k hk⟩

theorem hLZ : L ≤ normalizer ((centerOf ⁅N, L⁆ : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_inf_gc (F.hLQ hg) (Subgroup.mem_normalizer_iff.2 fun c => by
    constructor
    · intro hc
      exact C124.conj_mem_centralizer_of_le F.hLQ hg hc
    · intro hc
      have := C124.conj_mem_centralizer_of_le F.hLQ (L.inv_mem hg) hc
      simpa [mul_assoc] using this)

end ZFacts

end CFSG.Quasithin.H13.U3.GC137

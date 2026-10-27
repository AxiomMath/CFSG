module

public import CFSG.Timmesfeld.ARS.Sec13Restrict
public import CFSG.Timmesfeld.ARS.SimplyLacedConfig

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Sec13Restrict

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

omit hS in
theorem isConfig_restrict {r : ℕ} {adj : Fin r → Fin r → Prop} {P Q : Fin r → Subgroup G}
    (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀) :
    IsConfig (restrict R (levi R A A₀)) adj (fun k => (P k).subgroupOf (levi R A A₀))
      (fun k => (Q k).subgroupOf (levi R A A₀)) := by
  set V := levi R A A₀
  have hP : ∀ k, P k ≤ V := fun k => le_levi (hPQ k).1
  have hQ : ∀ k, Q k ≤ V := fun k => le_levi (hPQ k).2
  have hcomm : ∀ {X Y : Subgroup G}, X ≤ V → Y ≤ V → Commuting X Y →
      Commuting (X.subgroupOf V) (Y.subgroupOf V) := fun hX hY h =>
    (commuting_subgroupOf_iff' hX hY).2 h
  have hcomEq : ∀ {X Y Z : Subgroup G}, X ≤ V → Y ≤ V → ⁅X, Y⁆ = Z →
      ⁅X.subgroupOf V, Y.subgroupOf V⁆ = Z.subgroupOf V := fun hX hY h => by
    rw [Restrict.commutator_subgroupOf hX hY, h]
  refine ⟨fun k => (subgroupOf_mem_restrict_iff (hP k)).2 (hX.memA k),
    fun k => (subgroupOf_mem_restrict_iff (hQ k)).2 (hX.memB k),
    fun k => (opposite_subgroupOf_iff (hP k) (hQ k)).2 (hX.opp k), fun i j hij => ?_,
    fun i j hij h1 h2 => ?_⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hX.edge i j hij
    have hPij : ⁅P i, P j⁆ ≤ V := QD.commutator_le_of_le (hP i) (hP j)
    refine ⟨(special_subgroupOf_iff (hP i) (hP j)).2 e1, hcomm (hQ i) (hP j) e2, ?_,
      hcomm (hP i) (hQ j) e4, ?_, (special_subgroupOf_iff (hQ i) (hQ j)).2 e6⟩
    · rw [hcomEq (hP i) (hP j) rfl, hcomEq (hQ i) hPij e3]
    · rw [hcomEq (hP i) (hP j) rfl, hcomEq hPij (hQ j) e5]
  · obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    exact ⟨hcomm (hP i) (hP j) c1, hcomm (hP i) (hQ j) c2, hcomm (hQ i) (hP j) c3,
      hcomm (hQ i) (hQ j) c4⟩

omit hS in
theorem iSup_subgroupOf_eq_top {r : ℕ} {P Q : Fin r → Subgroup G}
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) :
    ⨆ k, ((P k).subgroupOf (levi R A A₀) ⊔ (Q k).subgroupOf (levi R A A₀)) = ⊤ := by
  set V := levi R A A₀
  have hle : ∀ k, P k ⊔ Q k ≤ V := fun k => hgen ▸ le_iSup (fun k => P k ⊔ Q k) k
  apply Subgroup.map_injective V.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hk : ∀ k, ((P k).subgroupOf V ⊔ (Q k).subgroupOf V).map V.subtype = P k ⊔ Q k :=
    fun k => by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left.trans (hle k)),
        Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans (hle k))]
  rw [iSup_congr hk]
  exact hgen

end Sec13

end CFSG.Timmesfeld.ARS

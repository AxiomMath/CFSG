module

public import CFSG.Quasithin.Background.ONanE68LieBar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem subgroupOf_normalizer_eq {L S : Subgroup G} (hSL : S ≤ L) :
    (L ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L =
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, h⟩ y
    have := h (y : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact this
  · intro h
    refine ⟨g.2, fun y => ?_⟩
    constructor
    · intro hy
      have := (h ⟨y, hSL hy⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact hy)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · intro hy
      have hyL : y ∈ L := by
        have h1 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem g.2) (hSL hy)) g.2
        simpa [mul_assoc] using h1
      have := (h ⟨y, hyL⟩).2 (by rw [Subgroup.mem_subgroupOf]; exact hy)
      rw [Subgroup.mem_subgroupOf] at this
      exact this

variable [Finite G]

theorem relIndex_normalizer_of_lin2 {L S : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n)
    (hS : IsSylowTwoOf S L) :
    (L ⊓ Subgroup.normalizer (S : Set G)).relIndex L = 2 ^ n + 1 := by
  classical
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := hlin
  have hchar : CharP F 2 := CFSG.QuasithinUnique.Setup.Lift.charP_two_of_card_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup ↥L := S.subgroupOf L with hS'def
  have hS'top : IsSylowTwoOf S' ⊤ := isSylowTwoOf_subgroupOf_top_of hS
  have hkerS : α.ker ≤ S' := by
    rw [hker]
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hx
    exact Subgroup.mem_subgroupOf.2 (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS h1)
  set Q' : Subgroup SL(2, F) := S'.map α with hQ'
  have hQ'2 : IsPGroup 2 Q' := hS'top.2.1.map α
  have hidxQ : Q'.index = S'.index := Subgroup.index_map_eq S' hα hkerS
  have hodd : ¬ 2 ∣ Q'.index := by
    rw [hidxQ]
    have h := hS'top.2.2
    rwa [show (S'.subgroupOf (⊤ : Subgroup ↥L)).index = S'.index from
      Subgroup.relIndex_top_right S'] at h
  let P : Sylow 2 SL(2, F) := hQ'2.toSylow hodd
  obtain ⟨-, -, -, -, -, -, -, hP⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.sl2_defining_characteristic_Sylow_normalizer_maximal_Borel
      (F := F) (p := 2)
  obtain ⟨g, -, -, -, -, hNidx⟩ := hP P
  have hPQ : (P : Subgroup SL(2, F)) = Q' := rfl
  rw [hPQ] at hNidx
  set N' : Subgroup ↥L := Subgroup.normalizer (S' : Set ↥L) with hN'
  have hcomap : ∀ t : ↥L, α t ∈ Q' ↔ t ∈ S' := by
    intro t
    rw [← Subgroup.mem_comap, hQ', Subgroup.comap_map_eq_self hkerS]
  have hiff : ∀ y : ↥L, α y ∈ Subgroup.normalizer (Q' : Set SL(2, F)) ↔ y ∈ N' := by
    intro y
    rw [Subgroup.mem_normalizer_iff, hN', Subgroup.mem_normalizer_iff]
    constructor
    · intro h t
      have := h (α t)
      rw [hcomap, ← map_inv, ← map_mul, ← map_mul, hcomap] at this
      exact this
    · intro h w
      obtain ⟨t, rfl⟩ := hα w
      rw [hcomap, ← map_inv, ← map_mul, ← map_mul, hcomap]
      exact h t
  have hmapN : N'.map α = Subgroup.normalizer (Q' : Set SL(2, F)) := by
    ext w
    obtain ⟨y, rfl⟩ := hα w
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← hzy]
      exact (hiff z).2 hz
    · intro hy
      exact ⟨y, (hiff y).1 hy, rfl⟩
  have hker_le : α.ker ≤ N' := hkerS.trans Subgroup.le_normalizer
  have hidxN : N'.index = Fintype.card F + 1 := by
    rw [← Subgroup.index_map_eq N' hα hker_le, hmapN]
    exact hNidx
  rw [Subgroup.relIndex, subgroupOf_normalizer_eq hS.1, ← hN', hidxN, hF]

end CFSG.Quasithin.RonanE611

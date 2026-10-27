module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem pCoreOf_le_self (X : Subgroup G) : pCoreOf 2 X ≤ X := CFSG.openPCoreOf_le 2 X

theorem mem_pCoreOf_iff {X : Subgroup G} {x : G} :
    x ∈ pCoreOf 2 X ↔ ∃ y ∈ CFSG.Open.pCore 2 ↥X, (y : G) = x := by
  simp [pCoreOf, Subgroup.mem_map]

theorem isPGroup_pCoreOf (X : Subgroup G) : IsPGroup 2 (pCoreOf 2 X) := by
  have h := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  exact h.map X.subtype

theorem normalizes_pCoreOf (X : Subgroup G) {a n : G} (ha : a ∈ X) (hn : n ∈ pCoreOf 2 X) :
    a * n * a⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨y, hy, rfl⟩ := mem_pCoreOf_iff.1 hn
  have := (CFSG.pCore_normal (p := 2) (G := ↥X))
  exact mem_pCoreOf_iff.2 ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, this.conj_mem y hy ⟨a, ha⟩, rfl⟩

theorem le_sylow_of_normalizes [Finite G] {P T N : Subgroup G} (hT : IsSylowTwoOf T P)
    (hN2 : IsPGroup 2 N) (hNP : N ≤ P) (hnorm : ∀ a ∈ P, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    N ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N' : Subgroup ↥P := N.subgroupOf P
  have hN'n : N'.Normal := ⟨fun n hn g => by
    simp only [N', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hN'2 : IsPGroup 2 N' := A4.isPGroup_subgroupOf_of_le hNP hN2
  have := IsPGroup.le_sylow_of_normal hN'2 (A4.toSylow hT)
  intro n hn
  have hn' : (⟨n, hNP hn⟩ : ↥P) ∈ N' := hn
  exact this hn'

theorem pCoreOf_le_sylow [Finite G] {X T : Subgroup G} (hT : IsSylowTwoOf T X) :
    pCoreOf 2 X ≤ T :=
  le_sylow_of_normalizes hT (isPGroup_pCoreOf X) (pCoreOf_le_self X)
    (fun _ ha _ hn => normalizes_pCoreOf X ha hn)

end CFSG.Quasithin.H13.I51

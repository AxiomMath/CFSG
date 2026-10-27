module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24EOut
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.QuasithinUnique CFSG.Sporadic.Th CFSG.Sporadic.Fi24
  CFSG.QuasithinUnique.Ch1.SporLat.M24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def fi24EP : Subgroup (Equiv.Perm (Fin 24)) :=
  (Subgroup.closure {x | x ∈ m24Sg}).map
    ((MulAut.conj fi24EC).toMonoidHom.comp NativeSporadic.M24.subtype)

theorem card_fi24EP : Nat.card fi24EP = 2 ^ 10 := by
  rw [fi24EP, card_map_of_injective ((MulAut.conj fi24EC).injective.comp (subtype_injective _)),
    m24_sGens.2]

section T


@[expose] noncomputable def fi24T : Subgroup CFSG.Sporadic.Fi24.J :=
  (fi24EP.comap fi24Pi).map (normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)).subtype

theorem mem_fi24T_iff {g : CFSG.Sporadic.Fi24.J} :
    g ∈ fi24T ↔ ∃ h : g ∈ normalizer (fi24E : Set CFSG.Sporadic.Fi24.J), fi24Pi ⟨g, h⟩ ∈ fi24EP := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem fi24T_le_normalizer : fi24T ≤ normalizer (fi24E : Set CFSG.Sporadic.Fi24.J) := map_subtype_le _


theorem fi24E_le_fi24T : fi24E ≤ fi24T := fun e he =>
  mem_fi24T_iff.2 ⟨le_normalizer he, by
    rw [(fi24Pi_eq_one_iff (n := ⟨e, le_normalizer he⟩)).2 he]
    exact one_mem _⟩


theorem fi24EP_le_range : fi24EP ≤ fi24Pi.range := by
  rw [range_fi24Pi]
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, x.2, rfl⟩

theorem exists_fi24T_of_mem {x : NativeSporadic.M24} (hx : x ∈ m24Sg) :
    ∃ n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J), (n : CFSG.Sporadic.Fi24.J) ∈ fi24T ∧
      fi24Pi n = fi24EC * (x : Equiv.Perm (Fin 24)) * fi24EC⁻¹ := by
  have hP : fi24EC * (x : Equiv.Perm (Fin 24)) * fi24EC⁻¹ ∈ fi24EP :=
    ⟨x, subset_closure hx, rfl⟩
  obtain ⟨n, hn⟩ := fi24EP_le_range hP
  have h : fi24Pi n ∈ fi24EP := hn ▸ hP
  exact ⟨n, mem_fi24T_iff.2 ⟨n.2, h⟩, hn⟩


theorem card_comap_fi24EP : Nat.card (fi24EP.comap fi24Pi) = 2 ^ 21 := by
  have h := card_ker_mul_card_range (fi24Pi.domRestrict (fi24EP.comap fi24Pi))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, map_comap_eq,
    inf_of_le_right fi24EP_le_range, card_fi24EP,
    Nat.card_congr (subgroupOfEquivOfLe (MonoidHom.ker_le_comap _ _)).toEquiv, ker_fi24Pi,
    Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, card_fi24E] at h
  rw [← h]
  norm_num

theorem card_fi24T : Nat.card fi24T = 2 ^ 21 := by
  rw [fi24T, card_map_of_injective (subtype_injective _), card_comap_fi24EP]

theorem isSylowTwoOf_fi24T : IsSylowTwoOf fi24T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card card_fi24T, ?_⟩
  change ¬ 2 ∣ fi24T.relIndex ⊤
  rw [relIndex_top_right]
  rintro ⟨k, hk⟩
  have h := card_mul_index fi24T
  rw [card_fi24T, card_J, hk, show (2 : ℕ) ^ 21 = 2097152 by norm_num] at h
  omega

end T

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

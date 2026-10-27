module

public import CFSG.Quasithin.AppendixH.H9.H92.S6Rank

public section

namespace CFSG.ASVolI.ChH

theorem card_le_eight_of_le_of_mulEquiv_perm_six {G : Type*} [Group G] {X B : Subgroup G}
    (hBX : B ≤ X) (hB : IsElemAb2 B) (θ : X ≃* Equiv.Perm (Fin 6)) : Nat.card B ≤ 8 := by
  let E : Subgroup (Equiv.Perm (Fin 6)) := (B.subgroupOf X).map θ.toMonoidHom
  have hE : IsElemAb2 E := by
    constructor
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      have hxy : x * y = y * x := Subtype.ext (hB.1 _ hx _ hy)
      show θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul, hxy]
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      have hx2 : x ^ 2 = 1 := Subtype.ext (hB.2 _ hx)
      show θ x ^ 2 = 1
      rw [← map_pow, hx2, map_one]
  have hcard : Nat.card E = Nat.card B := by
    rw [Subgroup.card_map_of_injective θ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [← hcard]
  exact card_le_eight_of_isElemAb2 E hE

theorem card_le_two_mul_card_inf_of_relIndex_eq_two {G : Type*} [Group G] {L M A : Subgroup G}
    (hAM : A ≤ M) (hLM : L.relIndex M = 2) : Nat.card A ≤ 2 * Nat.card ↥(L ⊓ A) := by
  have h1 : L.relIndex A ≤ L.relIndex M :=
    Subgroup.relIndex_le_of_le_right hAM (by rw [hLM]; norm_num)
  have h2 : L.relIndex A * Nat.card ↥(L ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card L A
  calc Nat.card A = L.relIndex A * Nat.card ↥(L ⊓ A) := h2.symm
    _ ≤ 2 * Nat.card ↥(L ⊓ A) := Nat.mul_le_mul_right _ (hLM ▸ h1)

theorem false_of_isElemAb2_of_symSix_centralizer {G : Type*} [Group G] {L M A : Subgroup G}
    (hAM : A ≤ M) (hLM : L.relIndex M = 2) (hA : IsElemAb2 A) (hcard : 32 ≤ Nat.card A)
    {t : G} (htA : t ∈ A)
    (θ : ↥(L ⊓ Subgroup.centralizer ({t} : Set G)) ≃* Equiv.Perm (Fin 6)) : False := by
  have hBX : L ⊓ A ≤ L ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hA.1 _ htA b (Subgroup.mem_inf.mp hb).2
  have hBab : IsElemAb2 (L ⊓ A) :=
    ⟨fun x hx y hy => hA.1 x (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).2,
      fun x hx => hA.2 x (Subgroup.mem_inf.mp hx).2⟩
  have h8 := card_le_eight_of_le_of_mulEquiv_perm_six hBX hBab θ
  have h2 := card_le_two_mul_card_inf_of_relIndex_eq_two hAM hLM
  omega

end CFSG.ASVolI.ChH

module

public import CFSG.Sporadic.Recognition.LyonsAmalgamStage3
public import CFSG.Sporadic.Recognition.LyonsLocalA3Cert

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Count

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.card_ker_trLines (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card (D.trLines S).ker = 3888 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (D.trLines_surjective S)
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hTr : Nat.card ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) = 23328 :=
    D.card_normalizer_A3_of_certificate S
  rw [h6, hTr] at h
  omega

theorem LyData.card_KN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(KN (x₁ : G) (x₂ : G) (x₃ : G)) = 3888 := by
  have hker : (D.trLines S).ker =
      (KN (x₁ : G) (x₂ : G) (x₃ : G)).subgroupOf (TrN (x₁ : G) (x₂ : G) (x₃ : G)) := by
    ext n
    rw [MonoidHom.mem_ker, D.trLines_eq_one_iff S n, Subgroup.mem_subgroupOf]
  have h := D.card_ker_trLines S
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (KN_le_TrN _ _ _)).toEquiv] at h
  exact h

theorem LyData.card_TxN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) = 7776 := by
  let f := D.trLines S
  let S0 : Subgroup (Perm (Fin 3)) := MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)
  have hcomap : (TxN (x₁ : G) (x₂ : G) (x₃ : G)).subgroupOf (TrN (x₁ : G) (x₂ : G) (x₃ : G)) =
      S0.comap f := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    constructor
    · intro hn
      have hq : (n : G) ∈ normalizer (zpowers (x₁ : G) : Set G) := hn.2
      have hx1 : (x₁ : G) ≠ 1 := fun h => by
        have := LyData.orderOf_x₁ S (G := G); rw [h, orderOf_one] at this; omega
      have hne : (n : G) * (x₁ : G) * (n : G)⁻¹ ≠ 1 := fun h => hx1 (by
        calc (x₁ : G) = (n : G)⁻¹ * ((n : G) * (x₁ : G) * (n : G)⁻¹) * (n : G) := by group
          _ = 1 := by rw [h]; group)
      have h := D.trLines_spec S n 0
      have h' : (n : G) * (![(x₁ : G), (x₂ : G), (x₃ : G)] 0) * (n : G)⁻¹ ∈
          zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] 0) :=
        conj_mem_zpowers_of_mem_normalizer hq
      exact (lineData_x S).eq_of_mem hne h h'
    · intro hn
      refine ⟨n.2, mem_normalizer_zpowers_of_conj ?_⟩
      have h := D.trLines_spec S n 0
      have h0 : D.trLines S n 0 = 0 := hn
      rw [h0] at h
      exact h
  have hS0 : S0.index = 3 := by
    have := MulAction.index_stabilizer_of_transitive (Perm (Fin 3)) (0 : Fin 3)
    simpa using this
  have hidx : (S0.comap f).index = 3 := by
    rw [Subgroup.index_comap_of_surjective S0 (D.trLines_surjective S), hS0]
  have hmul := Subgroup.card_mul_index (S0.comap f)
  have hTr : Nat.card ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) = 23328 :=
    D.card_normalizer_A3_of_certificate S
  rw [hidx, hTr] at hmul
  have hle : TxN (x₁ : G) (x₂ : G) (x₃ : G) ≤ TrN (x₁ : G) (x₂ : G) (x₃ : G) :=
    fun _ hg => hg.1
  rw [← hcomap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
  omega

end Count

end CFSG.Sporadic.Recognition.LyonsSims

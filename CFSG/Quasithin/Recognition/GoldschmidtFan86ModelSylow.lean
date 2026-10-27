module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G] [Finite G]

theorem pCore_index_three {S : Subgroup G} (hS : IsPGroup 2 S) (hidx : S.index = 3)
    (hnorm : Subgroup.normalizer (S : Set G) ≤ S) :
    2 * Nat.card (Open.pCore 2 G) = Nat.card S ∧
      Nonempty (oTwoQuot G ≃* Equiv.Perm (Fin 3)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ S.index := by rw [hidx]; decide
  let P : Sylow 2 G := hS.toSylow hodd
  have hPS : (P : Subgroup G) = S := IsPGroup.toSylow_coe hS hodd
  let φ : G →* Equiv.Perm (G ⧸ S) := MulAction.toPermHom G (G ⧸ S)
  have hn : (Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcoreS : Open.pCore 2 G ≤ S :=
    hPS ▸ (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal P
  have hpc : Open.pCore 2 G = S.normalCore := by
    refine le_antisymm (Subgroup.normal_le_normalCore.2 hcoreS) ?_
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance (hS.to_le S.normalCore_le)
  have hker : φ.ker = Open.pCore 2 G := by
    rw [hpc, Subgroup.normalCore_eq_ker]
  have hGS : Nat.card (G ⧸ S) = 3 := by rw [← Subgroup.index_eq_card, hidx]
  have hperm : Nat.card (Equiv.Perm (G ⧸ S)) = 6 := by
    rw [Nat.card_perm, hGS]
    rfl
  let e1 : oTwoQuot G ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hQ6 : Nat.card (oTwoQuot G) ∣ 6 := by
    rw [Nat.card_congr e1.toEquiv, ← hperm]
    exact Subgroup.card_subgroup_dvd_card _
  have hGcard : Nat.card S * 3 = Nat.card G := by
    rw [← hidx]
    exact Subgroup.card_mul_index S
  have hQc := card_oTwoQuot_mul G
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hcoreS
  have hcpos : 0 < Nat.card (Open.pCore 2 G) := Nat.card_pos
  have hQ3 : Nat.card (oTwoQuot G) = 3 * m := by
    have : Nat.card (oTwoQuot G) * Nat.card (Open.pCore 2 G) =
        3 * m * Nat.card (Open.pCore 2 G) := by
      rw [hQc, ← hGcard, hm]
      ring
    exact Nat.eq_of_mul_eq_mul_right hcpos this
  have hm12 : m = 1 ∨ m = 2 := by
    have h1 : 3 * m ∣ 6 := hQ3 ▸ hQ6
    have h2' : 3 * m ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have h3 : m ≠ 0 := by
      rintro rfl
      simp at hm
      exact absurd hm (Nat.card_pos (α := S)).ne'
    omega
  have hm2 : m = 2 := by
    rcases hm12 with h | h
    · exfalso
      have hcS : Open.pCore 2 G = S := by
        refine Subgroup.eq_of_le_of_card_ge hcoreS ?_
        rw [hm, h, mul_one]
      have hSn : S.Normal := hcS ▸ hn
      have : (⊤ : Subgroup G) ≤ S := by
        rw [← Subgroup.normalizer_eq_top_iff.2 hSn]
        exact hnorm
      have h1 : S = ⊤ := top_le_iff.1 this
      rw [h1, Subgroup.index_top] at hidx
      exact absurd hidx (by norm_num)
    · exact h
  refine ⟨?_, ?_⟩
  · rw [hm, hm2, mul_comm]
  · have hQ6' : Nat.card φ.range = 6 := by
      rw [← Nat.card_congr e1.toEquiv, hQ3, hm2]
    have hrange : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hQ6', hperm])
    let e2 : φ.range ≃* Equiv.Perm (G ⧸ S) :=
      (MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv
    let e3 : G ⧸ S ≃ Fin 3 := (Finite.equivFin (G ⧸ S)).trans (finCongr hGS)
    exact ⟨(e1.trans e2).trans e3.permCongrHom⟩

end CFSG.Quasithin.Fan86.Model

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.Cited.SuzukiHyp
public import CFSG.Assembly.Defs
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {X : Type} [Group X] [Finite X]

theorem not_eight_dvd_card_of_isKleinFour_sylow
    (hX : ∀ S : Sylow 2 X, IsKleinFour (S : Subgroup X)) : ¬ 8 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h8
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have h4 := (hX S).card_four
  have hdvd : 2 ^ 3 ∣ Nat.card (S : Subgroup X) :=
    S.pow_dvd_card_of_pow_dvd_card (by norm_num; exact h8)
  rw [h4] at hdvd
  norm_num at hdvd

omit [Finite X] in
theorem card_quotient_pPrimeCore_dvd : Nat.card (X ⧸ pPrimeCore 2 X) ∣ Nat.card X :=
  Subgroup.card_quotient_dvd_card _

theorem exists_psl2_of_isKleinFour_sylow
    (hX : ∀ S : Sylow 2 X, IsKleinFour (S : Subgroup X))
    (hns : ¬ Group.IsSolvable X) {P : Prop}
    (hP : ∀ (K : Type) [Field K] [Finite K], IsOddPrimePower (Nat.card K) →
      ∀ L : Subgroup (X ⧸ pPrimeCore 2 X), L.Normal → Odd L.index →
        Nonempty (L ≃* PSL(2, K)) → P) : P := by
  have h8 := not_eight_dvd_card_of_isKleinFour_sylow hX
  have h8Q : ¬ 8 ∣ Nat.card (X ⧸ pPrimeCore 2 X) := fun h =>
    h8 (h.trans card_quotient_pPrimeCore_dvd)
  have hD : HasDihedralSylowTwo X := by
    intro S
    have := hX S
    exact ⟨1, le_rfl, by rw [pow_one]; exact IsKleinFour.nonempty_mulEquiv⟩
  have hOsolv : Group.IsSolvable (pPrimeCore 2 X) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ Suzuki.odd_card_pPrimeCore
  rcases gorensteinWalter X hD with ⟨-, h2⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, K, hK, L, hLn, hLi, hLmodel⟩
  ·
    exfalso
    apply hns
    have : Group.IsSolvable (X ⧸ pPrimeCore 2 X) := by
      have := h2.isNilpotent
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient (pPrimeCore 2 X)
  · exfalso
    apply h8Q
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · rcases hLmodel with he | he
    · exact hP K hK L hLn hLi he
    · obtain ⟨e⟩ := he
      exfalso
      apply h8Q
      have hodd : Odd (Nat.card K) := by
        obtain ⟨p, n, -, hp, -, hq⟩ := hK
        rw [hq]
        exact hp.pow
      have h8L : 8 ∣ Nat.card L := by
        rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
        exact Dvd.dvd.mul_left (Suzuki.eight_dvd_sq_sub_one hodd) _
      exact h8L.trans (Subgroup.card_subgroup_dvd_card L)

end CFSG.Walter.JT

module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecCoord
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecQuot
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecBil

import CFSG.GroupTheory.PermSylowTwo.Sym
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

structure NatPre (P L E K : Subgroup G) (n : ℕ) : Prop where
  le : L ≤ P
  norm_L : P ≤ Subgroup.normalizer (L : Set G)
  norm_E : P ≤ Subgroup.normalizer (E : Set G)
  norm_K : P ≤ Subgroup.normalizer (K : Set G)
  sec : IsElemSec K E
  card : K.relIndex E = 2 ^ (2 * n)
  core : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K
  quot : IsL2Quot n (oTwoQuot ↥L)
  nontriv : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K

private theorem pCoreOf_le_pCoreOf_of_le_normalizer {P L : Subgroup G} (hLP : L ≤ P)
    (hN : P ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 P :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L).trans hLP)
    (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L)

theorem NatPre.isNatSecOf {P L E K T : Subgroup G} [Finite ↥P] {F : Type} [Field F]
    [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L) (h : NatPre P L E K n) (hEP : E ≤ P)
    (hT : IsSylowTwoOf T L) (hC : 2 ^ n ≤ K.relIndex (relCent E K T)) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf L E K α := by
  classical
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)
  haveI : Finite ↥E :=
    Finite.of_injective (Subgroup.inclusion hEP) (Subgroup.inclusion_injective hEP)
  have hcoreLP := pCoreOf_le_pCoreOf_of_le_normalizer h.le h.norm_L
  refine isNatSecOf_of_two_pow_le_of_nontrivial (L := L) (E := E) (Z := K) (T := T)
    hn hF hα hker h.sec ?_ ?_ h.card h.nontriv h.quot hT hC
  · exact le_inf (h.le.trans h.norm_E) (h.le.trans h.norm_K)
  · intro x hx e he
    exact h.core x (hcoreLP hx) e he

theorem natQuot_of_two_pow_le {P L E Z T : Subgroup G} [Finite ↥P] {n : ℕ} (hn : 2 ≤ n)
    (h : NatPre P L E Z n) (hEL : E ≤ L) (hT : IsSylowTwoOf T L)
    (hC : 2 ^ n ≤ Z.relIndex (relCent E Z T)) : NatQuot L E Z n := by
  classical
  have hEP : E ≤ P := hEL.trans h.le
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)
  haveI : Finite ↥E :=
    Finite.of_injective (Subgroup.inclusion hEP) (Subgroup.inclusion_injective hEP)
  have hcoreLP := pCoreOf_le_pCoreOf_of_le_normalizer h.le h.norm_L
  have hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
    le_inf (h.le.trans h.norm_E) (h.le.trans h.norm_K)
  obtain ⟨α, hα, hker, hnat⟩ :=
    exists_isNatSecOf_of_two_pow_le (L := L) (E := E) (Z := Z) (T := T) hn h.quot h.sec
      hL (fun x hx e he => h.core x (hcoreLP hx) e he) h.card h.nontriv hT hC
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  exact natQuot_of_isNatSecOf hF hα hker h.sec.1 hEL hL hnat

theorem comm_le_of_natPre {P L E V Z : Subgroup G} [Finite ↥P] {n : ℕ} (hn : 2 ≤ n)
    (hE : NatPre P L E V n) (hV : NatPre P L V Z n)
    (hEV : NatQuot L E V n) (hVZ : NatQuot L V Z n) (hcomm : ⁅E, E⁆ ≤ V)
    (hcent : ⁅E, V⁆ ≤ Z) : ⁅E, E⁆ ≤ Z := by
  classical
  have hEP : E ≤ P := hEV.E_le.trans hE.le
  have hVP : V ≤ P := hVZ.E_le.trans hV.le
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion hE.le) (Subgroup.inclusion_injective hE.le)
  haveI : Finite ↥E :=
    Finite.of_injective (Subgroup.inclusion hEP) (Subgroup.inclusion_injective hEP)
  obtain ⟨R, hR⟩ := CFSG.GroupTheory.PermSylowTwo.exists_isSylowTwoOf_top ↥L
  let T : Subgroup G := R.map L.subtype
  have hT : IsSylowTwoOf T L := by
    have h := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_of_injective
      (Subgroup.subtype_injective L) hR
    simpa [T, Subgroup.map_top, Subgroup.range_subtype] using h
  have hcoreE := pCoreOf_le_pCoreOf_of_le_normalizer hE.le hE.norm_L
  have hLE : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf (hE.le.trans hE.norm_E) (hE.le.trans hE.norm_K)
  obtain ⟨α, hα, hker, hEVnat⟩ :=
    exists_isNatSecOf_of_two_pow_le (L := L) (E := E) (Z := V) (T := T) hn hE.quot hE.sec
      hLE (fun x hx e he => hE.core x (hcoreE hx) e he) hE.card hE.nontriv hT
      (by rw [hEV.line T hT])
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  have hVnat : CFSG.Quasithin.F112R.St84.IsNatSecOf L V Z α :=
    NatPre.isNatSecOf hn hF hα hker hV hVP hT (by rw [hVZ.line T hT])
  have hF4 : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine comm_le_of_isNatSecOf hF4 hα hVZ.Z_le (fun x hx => (hEV.normal hx).1)
    (fun x hx => (hEV.normal hx).2) hEVnat hVnat hcomm hcent

end CFSG.Quasithin.St84

end

module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBUQ2
public import CFSG.GroupTheory.NormalizerInfCentralizer
public import CFSG.Quasithin.Vol2.Q8D8Extraspecial
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.EmptyFaithful.S1422Center
public import CFSG.Quasithin.Recognition.St84.TransferSetup

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

structure S3A5U42Hyp (L1 L2 S : Subgroup H) : Prop where
  elem_right : IsElemAbelian 2 (pCoreOf 2 (f112saP2' L1 L2 S))
  card_right : Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) = 2 ^ 4
  special_left : IsSpecialPow 2 2 2 ↥(pCoreOf 2 (f112saP1' L1 L2 S))
  nat_left : NatSec (oTwoPrime (f112saP1' L1 L2 S)) (centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
    (pCoreOf 2 (f112saP1' L1 L2 S))

structure S3A5J2Hyp (L1 L2 S : Subgroup H) : Prop where
  q8d8_right : IsQ8D8 ↥(pCoreOf 2 (f112saP2' L1 L2 S))
  nat_left : NatSec (oTwoPrime (f112saP1' L1 L2 S)) ⊥ (pCoreOf 2 (f112saP1' L1 L2 S))

structure S3A5ModuleFacts (L1 L2 S : Subgroup H) : Prop where
  ker_right : ∀ c ∈ S, (∀ l ∈ f112saP2' L1 L2 S, ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) →
    c ∈ pCoreOf 2 (f112saP2' L1 L2 S)
  indec_right : ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoRes L2⁆ =
    pCoreOf 2 (f112saP2' L1 L2 S)
  fix_left : ∀ d ∈ oTwoPrime (f112saP1' L1 L2 S), orderOf d = 3 →
    ∀ e ∈ pCoreOf 2 (f112saP1' L1 L2 S), e * d = d * e →
    e ∈ ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ⊓
      Subgroup.centralizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H)

structure S3A5VertexId (L1 L2 S : Subgroup H) : Prop where
  T_eq : S ⊓ L2 = S ⊓ f112saK L1 L2 S
  L2_eq : L2 = f112saP2' L1 L2 S
  L1_eq : L1 = oTwoPrime (f112saP1' L1 L2 S)
  S_inf_L1 : S ⊓ L1 = S ⊓ f112saK L1 L2 S
  QA_eq : pCoreOf 2 L2 = pCoreOf 2 (f112saP2' L1 L2 S)
  QS_eq : pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S)
  oTwo_right : pCoreOf 2 L2 = dsQ L2 L1 S
  oTwo_left : pCoreOf 2 L1 = dsQ L1 L2 S
  sup_eq : dsQ L2 L1 S ⊔ dsQ L1 L2 S = S ⊓ L2
  charTwo_right : CharTwo L2
  plain : S ≤ L2 → bigB L2 L1 S ≤ L2

structure S3A5TwistBasis (L1 L2 S : Subgroup H) : Prop where
  line_d : ∀ d ∈ L1, d ^ 3 = 1 →
    L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((Subgroup.zpowers d ⊔ pCoreOf 2 L1 : Subgroup H) : Set H)
  line_k : ∀ k ∈ f112saK L1 L2 S, k ^ 3 = 1 →
    L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((Subgroup.zpowers k ⊔ pCoreOf 2 L1 : Subgroup H) : Set H)
  diag : ∃ u ∈ S, u ∉ L2 ∧ u ^ 2 ∈ pCoreOf 2 L1 ∧
    (∀ d ∈ L1, ⁅u, d⁆ ∈ pCoreOf 2 L1) ∧
    ∀ k ∈ f112saK L1 L2 S, k ^ 3 = 1 → u * k * u⁻¹ * k ∈ pCoreOf 2 L1

structure S3A5ParabolicId (L1 L2 S : Subgroup H) : Prop extends S3A5VertexId L1 L2 S where
  ext : ¬ S ≤ L2 → (S ⊓ L2).relIndex S = 2 ∧
    Nonempty (oTwoQuot ↥(L2 ⊔ bigB L2 L1 S) ≃* Equiv.Perm (Fin 5)) ∧
    Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  twist : ¬ S ≤ L2 → S3A5TwistBasis L1 L2 S

theorem f112sa_QA_le_T {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    pCoreOf 2 (f112saP2' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S :=
  F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P2' hF.toW)

theorem f112sa_QS_le_T {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    pCoreOf 2 (f112saP1' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S :=
  F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P1' hF.toW)

theorem f112sa_P2_le_normalizer_QA {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112P2 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
  (f112sa_P2_le_normalizer_P2' hF.toW).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem f112sa_P1_le_normalizer_QS {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112P1 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
  (f112sa_P1_le_normalizer_P1' hF.toW).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem commute_of_mem_centerOf_of_card_two {E Q : Subgroup H}
    (hEQ : E ≤ Subgroup.normalizer (Q : Set H)) (hZ : Nat.card ↥(centerOf Q) = 2)
    {z : H} (hz : z ∈ centerOf Q) : ∀ x ∈ E, z * x = x * z := by
  have hN : E ≤ Subgroup.normalizer (centerOf Q : Set H) := fun x hx =>
    CFSG.GroupTheory.mem_normalizer_inf_centralizer (hEQ hx) (hEQ hx)
  exact fun x hx => (DSBUQ2.mem_center_of_card_two hZ hN hz hx).symm

theorem isQ8D8_extraspecial_facts {Q : Subgroup H} (h : IsQ8D8 ↥Q) :
    CFSG.IsExtraspecialPGroup 2 ↥Q ∧ Nat.card ↥(centerOf Q) = 2 ∧
      IsElemSec (centerOf Q) Q ∧ (centerOf Q).relIndex Q = 16 := by
  obtain ⟨z, hzc, hz1, -, hcen, hsq⟩ := H13.isQ8D8_central_facts h
  have hsqc : ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q := fun x => by
    rw [pow_two]
    rcases hsq x with hx | hx
    · rw [hx]; exact Subgroup.one_mem _
    · rw [hx]; exact hzc
  have hZ : Nat.card ↥(Subgroup.center ↥Q) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥Q))]
    refine ⟨⟨z, hzc⟩, fun h1 => hz1 (congrArg Subtype.val h1), fun y hy => ?_⟩
    rcases hcen y y.2 with h1 | h1
    · exact absurd (Subtype.ext h1) hy
    · exact Subtype.ext h1
  have hQ32 : Nat.card ↥Q = 32 := h.1
  have hE : CFSG.IsExtraspecialPGroup 2 ↥Q := h.isExtraspecialPGroup
  have hcZ : Nat.card ↥(centerOf Q) = 2 := (card_centerOf_eq_card_center Q).trans hZ
  refine ⟨hE, hcZ, ⟨inf_le_left, ?_, fun e he => ?_⟩, ?_⟩
  · rw [← Subgroup.map_subtype_commutator, A1c.centerOf_eq_map_center]
    exact Subgroup.map_mono hE.2.1.le
  · rw [A1c.centerOf_eq_map_center]
    exact ⟨⟨e, he⟩ ^ 2, hsqc _, rfl⟩
  · have hle : centerOf Q ≤ Q := inf_le_left
    have := Subgroup.relIndex_mul_card (centerOf Q) Q
    rw [inf_eq_left.mpr hle, hcZ, hQ32] at this
    omega

end CFSG.Quasithin.F112R.St84

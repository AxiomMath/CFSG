module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev u3Lhat (L1 L2 S : Subgroup G) : Subgroup G := L1 ⊔ Q1 L1 L2 S

abbrev u3K1 (L1 L2 S : Subgroup G) : Subgroup G :=
  Q1 L1 L2 S ⊓ Subgroup.centralizer (u3X1 L1 L2 S : Set G)

abbrev u3M (L1 L2 S : Subgroup G) : Type :=
  ↥(u3X1 L1 L2 S) ⧸ (Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)

@[expose] noncomputable def u3MAct (L1 L2 S : Subgroup G)
    [((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal]
    (hX : u3Lhat L1 L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G))
    (hZ : u3Lhat L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)) :
    ↥(u3Lhat L1 L2 S) →* MulAut (u3M L1 L2 S) :=
  CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hX hZ

theorem u3M_normal (L1 L2 S : Subgroup G) :
    ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal := by
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  exact (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans
    (Subgroup.le_normalizer.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf
      (Q1 L1 L2 S)))

@[expose, instance_reducible] noncomputable def u3MCommGroup {L1 L2 S : Subgroup G}
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S) :
    CommGroup (u3M L1 L2 S) := by
  letI : ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal := u3M_normal L1 L2 S
  exact CommGroup.mk (fun a b => by
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hc : ⁅((y : G)⁻¹), ((x : G)⁻¹)⁆ ∈
            ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ :=
          Subgroup.commutator_mem_commutator ((u3X1 L1 L2 S).inv_mem y.2)
            ((u3X1 L1 L2 S).inv_mem x.2)
        rw [hX1'] at hc
        have he : (((x * y)⁻¹ * (y * x) : ↥(u3X1 L1 L2 S)) : G) =
            ⁅((y : G)⁻¹), ((x : G)⁻¹)⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        exact (Subgroup.mem_subgroupOf (H := Z1 L1 L2 S)
          (K := u3X1 L1 L2 S)).mpr (by rw [he]; exact hc))

theorem u3K1_le_q1 (L1 L2 S : Subgroup G) : u3K1 L1 L2 S ≤ Q1 L1 L2 S := inf_le_left

theorem u3Z1_le_u3K1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≤ u3K1 L1 L2 S := by
  refine le_inf (omegaOneCenterOf_le (Q1 L1 L2 S)) ?_
  rw [Subgroup.le_centralizer_iff]
  have hQ1core : pCoreOf 2 (Q1 L1 L2 S) = Q1 L1 L2 S :=
    le_antisymm (pCoreOf_le 2 (Q1 L1 L2 S))
      (CFSG.LieType.BorelTits.le_pCoreOf 2 (N := Q1 L1 L2 S) (H := Q1 L1 L2 S)
        le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
        (pCoreOf_isPGroup 2 (P1 L1 L2 S)))
  refine (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans ?_
  have hcent := SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (Q1 L1 L2 S)
  simpa [Z1, hQ1core] using hcent

theorem u3K1_normal_in_P1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    P1 L1 L2 S ≤ Subgroup.normalizer (u3K1 L1 L2 S : Set G) := by
  have hP1X : P1 L1 L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    sup_le (le_normalizer_u3X1_left (L1 := L1) (L2 := L2) (S := S))
      (bigB_le_normalizer_u3X1 (L1 := L1) (L2 := L2) (S := S) hF.1)
  have hP1Q : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hP1C : P1 L1 L2 S ≤
      Subgroup.normalizer (Subgroup.centralizer (u3X1 L1 L2 S : Set G) : Set G) :=
    hP1X.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (u3X1 L1 L2 S))
  exact (le_inf hP1Q hP1C).trans Subgroup.inf_normalizer_le_normalizer_inf

@[expose] def Str86X1Natural {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (k : ℕ)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S) : Prop :=
  letI : CommGroup (u3M L1 L2 S) := u3MCommGroup hX1'
  letI : ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal := u3M_normal L1 L2 S
  let act : ↥(u3Lhat L1 L2 S) →* @MulAut (u3M L1 L2 S) (u3MCommGroup hX1').toMul :=
    u3MAct (hX := sup_le (le_normalizer_u3X1_left (L1 := L1) (L2 := L2) (S := S))
      ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
        (f112_isSylowTwoOf_P1 hF.toW)).trans
        (le_normalizer_u3X1_sylow (L1 := L1) (L2 := L2) (S := S) hF)))
      (hZ := by
        refine (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S) ?_).trans ?_
        · exact (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
            (f112_isSylowTwoOf_P1 hF.toW)).trans
            (((le_sup_right : S ≤ bigB L1 L2 S)).trans
              (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S))
        · exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
            (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  Nat.card (u3M L1 L2 S) = (2 ^ k) ^ 6 ∧
    BinaryNaturalSU3 act.range ⊤ ⊥ k

@[expose] def Str86X1K1 (L1 L2 S : Subgroup G) : Prop :=
  Q1 L1 L2 S = u3X1 L1 L2 S ⊔ u3K1 L1 L2 S ∧
    Subgroup.center ↥(u3K1 L1 L2 S) =
      (Z1 L1 L2 S).subgroupOf (u3K1 L1 L2 S)

@[expose] def Str86X1Module {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (k : ℕ)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S) : Prop :=
  Str86X1Natural hF k hX1' ∧ Str86X1K1 L1 L2 S

theorem u3Z1_le_u3X1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≤ u3X1 L1 L2 S := by
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
  have hZ1Y : Z1 L1 L2 S ≤ u3Y L1 L2 S :=
    le_inf hZ1Z2 (omegaOneCenterOf_le (Q1 L1 L2 S))
  exact hZ1Y.trans (u3Y_le_u3X1 (L1 := L1) (L2 := L2) (S := S))

theorem card_u3X1_eq_card_z1_mul_card_u3M {L1 L2 S : Subgroup G}
    (hZ1X : Z1 L1 L2 S ≤ u3X1 L1 L2 S) :
    Nat.card (u3X1 L1 L2 S) =
      Nat.card (Z1 L1 L2 S) * Nat.card (u3M L1 L2 S) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S))
  rw [mul_comm]
  rw [h]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1X).toEquiv

theorem card_u3X1_of_card_u3M {L1 L2 S : Subgroup G} {k : ℕ}
    (hZ1X : Z1 L1 L2 S ≤ u3X1 L1 L2 S) (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hM : Nat.card (u3M L1 L2 S) = (2 ^ k) ^ 6) :
    Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7 := by
  rw [card_u3X1_eq_card_z1_mul_card_u3M hZ1X, hZ1, hM]
  ring

theorem str86_X1_structure_of_parts
    {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hMod : Str86X1Module hF k hX1') :
    Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7 ∧
      Q1 L1 L2 S = u3X1 L1 L2 S ⊔
        (Q1 L1 L2 S ⊓ Subgroup.centralizer (u3X1 L1 L2 S : Set G)) ∧
      Subgroup.center ↥(Q1 L1 L2 S ⊓
        Subgroup.centralizer (u3X1 L1 L2 S : Set G)) =
        (Z1 L1 L2 S).subgroupOf (Q1 L1 L2 S ⊓
          Subgroup.centralizer (u3X1 L1 L2 S : Set G)) := by
  obtain ⟨⟨hMcard, -⟩, hQ1, hCenter⟩ := hMod
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hZ1X : Z1 L1 L2 S ≤ u3X1 L1 L2 S :=
    u3Z1_le_u3X1 hF hSB h1 hB2 h2 hZI
  exact ⟨card_u3X1_of_card_u3M hZ1X hZ1 hMcard, hQ1, hCenter⟩

end CFSG.Quasithin.Stroth

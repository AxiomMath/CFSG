module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseI
public import CFSG.Quasithin.Recognition.Stroth.Str86QOneShape
public import CFSG.Quasithin.Recognition.Stroth.Str86NFUnitary
public import CFSG.Quasithin.Recognition.Stroth.Str86CardQTwo
public import CFSG.Quasithin.Recognition.Stroth.Str86QTwoShape
public import CFSG.Quasithin.Recognition.Stroth.Str86NFLinear
public import CFSG.Quasithin.Recognition.Stroth.Str86Meets
public import CFSG.Quasithin.Recognition.Stroth.Str86BPrime
public import CFSG.Quasithin.Recognition.Stroth.Str86PathFix2
public import CFSG.Quasithin.Recognition.Stroth.IdOfLeaves
public import CFSG.Quasithin.Recognition.Stroth.Str86LocTransParts
public import CFSG.Quasithin.Recognition.Stroth.Str86NormalForm

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_shape
    (hZ : Str86ZNotLe) {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2) :
    Str86Shape L1 L2 S k := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    str86CaseI_holds G L1 L2 S hF hSB h1 hB2 h2
  have hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S := hZ G L1 L2 S hF hSB h1 hB2 h2 hZI
  obtain ⟨hL2, hZ2, hZ1, hY, hX1', hX1Q1⟩ :=
    str86_l2_eq_and_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ
  obtain ⟨hQ1, hQ1card, -, -, hNat1⟩ :=
    str86_q1_shape hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hX1Q1
  obtain ⟨hQ2card, hScard⟩ := str86_card_q2_and_card_s hF hSB hk hFc hU3 hL2 hQ1card
  have hQ1Q2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf hF.toW hSB (Or.inr h1) (by omega) hL2
  have hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7 := by
    rw [← hQ1]
    exact hQ1card
  have hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
    rw [← hQ1]
    exact hQ1Q2
  have hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2 := by
    rw [str86_relIndex_q2_s hF.toW hSB (by omega) hL2, ← pow_mul, mul_comm]
  obtain ⟨hQ2', -, -, -, hQ2irr, hZ2irr, hV⟩ :=
    str86_q2_shape hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4 hX1Q2 hSQ2
      hQ2card
  exact
    { l2 := hL2
      card_q1 := hQ1card
      card_q2 := hQ2card
      card_s := hScard
      q1q2 := hQ1Q2
      nf1 := str86NF_unitary hF hk hQ1 hX1' hNat1
      nf2 := str86NF_linear hk hZ2 hQ2' hQ2irr hZ2irr
      bprime := str86_conj_q1_inf_q2_inf_q1_inf_conj_q2_eq_bot hV
        (str86_z2_inf_q1_inf_conj_q2_le_z1 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2)
        (str86_z1_inf_conj_q1_eq_bot hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hY) }

theorem str86Orders_of_zNotLe
    (hZ : Str86ZNotLe) :
    Str86Orders := by
  intro G _ _ L1 L2 S k F _ _ hF hk hFc hU3 hB2 h2
  have hF' : F112Hyp L1 L2 (str86S' L1 L2 S) := f112Hyp_sup_inf hF
  have hSB' : bigB L1 L2 (str86S' L1 L2 S) ≤
      Subgroup.normalizer (str86S' L1 L2 S : Set G) :=
    bigB_le_normalizer_of_sup_inf_eq hF'.1 (sup_inf_str86S' L1 L2 S)
  have hsh' : Str86Shape L1 L2 (str86S' L1 L2 S) k :=
    str86_shape hZ hF' hSB' hk hFc hU3 hB2 h2
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    str86_bigB_le_normalizer_of_nf hF h1 ⟨2 * k, by omega, hsh'.l2⟩ hsh'.nf1 hsh'.nf2
  have hsh : Str86Shape L1 L2 S k := str86_shape hZ hF hSB hk hFc hU3 hB2 h2
  exact ⟨hsh.l2, hsh.card_q1, hsh.card_q2, hsh.card_s⟩

theorem str86PathFix_of_zNotLe
    (hZ : Str86ZNotLe) :
    Str86PathFix := by
  intro G _ _ L1 L2 S hF h1 hB2 h2
  obtain ⟨k, hk, F, _, _, hFc, hU3⟩ := h1
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨-, hSB⟩ := str86_bigB_le_normalizer (str86Orders_of_zNotLe hZ) hF h1 hB2 h2
  exact str86_pathFix_of_shape hF hSB h1 hB2 h2 (str86_shape hZ hF hSB hk hFc hU3 hB2 h2)

theorem str86LocTrans5_of_zNotLe
    (hZ : Str86ZNotLe) :
    Str86LocTrans5 :=
  str86LocTrans5_of_pathFix (str86Orders_of_zNotLe hZ) (str86PathFix_of_zNotLe hZ)

theorem idU3L2_of_zNotLe
    (hZ : Str86ZNotLe)
    (hW : Weiss80UnitaryQuadrangle) : IdU3L2 :=
  idU3L2_of_leaves (str86LocTrans5_of_zNotLe hZ) (str86Orders_of_zNotLe hZ) hW

end CFSG.Quasithin.Stroth

end

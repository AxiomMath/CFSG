module

public import CFSG.Quasithin.Recognition.Stroth.Str86Q1Eq
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EStep

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str86_q2_chiefStep
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    (hQ2card : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8) :
    IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (Z2 L1 L2 S) (Q2 L1 L2 S) := by
  classical
  let H := u3H L1 L2 S
  let Q := Q2 L1 L2 S
  let Z := Z2 L1 L2 S
  have hZQle : Z ≤ Q := A4.omegaOneCenterOf_le Q
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := str86_z2_normal_u3H L1 L2 S
  have hQn : IsNormalIn H Q Q :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHQ hg) x).mp hx⟩
  have hZn : IsNormalIn H Q Z :=
    ⟨hZQle, fun g hg z hz => (Subgroup.mem_normalizer_iff.mp (hHZ hg) z).mp hz⟩
  have hq1 : 1 < 2 ^ k := Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 2)
  have hZltQ : Z < Q := by
    refine lt_of_le_of_ne hZQle ?_
    intro heq
    have hc : (2 ^ k) ^ 4 = (2 ^ k) ^ 8 := by
      calc (2 ^ k) ^ 4 = Nat.card Z := hZ2.symm
        _ = Nat.card Q := by rw [heq]
        _ = (2 ^ k) ^ 8 := hQ2card
    have hlt : (2 ^ k) ^ 4 < (2 ^ k) ^ 8 :=
      Nat.pow_lt_pow_right hq1 (by norm_num : 4 < 8)
    exact (ne_of_lt hlt) hc
  obtain ⟨J, hstepJ, hJQ⟩ :=
    CFSG.Quasithin.F53B3.NoE.exists_chiefStep_of_lt hZn hQn hZltQ
  have hncJ : ¬ IsCentralStep H Z J := by
    intro hc
    have hJleZ : J ≤ Z := by
      intro x hx
      exact str86_q2_fixed_mem_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
        hI4 hX1Q2 hSQ2 x (hJQ hx) (fun g hg => hc g hg x hx)
    exact (ne_of_lt hstepJ.2.2.1) (le_antisymm hstepJ.2.2.1.le hJleZ)
  have hcardJ : Z.relIndex J = (2 ^ k) ^ 4 :=
    (str86_q2_chiefFactor_natural_card hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hX1' hY hI4
      hX1Q2 hSQ2 le_rfl hstepJ hncJ).1
  have hJcard : Nat.card J = (2 ^ k) ^ 8 := by
    have hmul := Subgroup.relIndex_mul_card Z J
    rw [inf_eq_left.mpr hstepJ.2.2.1.le, hcardJ, hZ2] at hmul
    calc Nat.card J = (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := hmul.symm
      _ = (2 ^ k) ^ 8 := by rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add]
  have hJeq : J = Q := Subgroup.eq_of_le_of_card_ge hJQ (by rw [hJcard, hQ2card])
  rw [hJeq] at hstepJ
  exact hstepJ

private theorem str86_q2_z2_irreducible
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4) :
    ∀ N : Subgroup G, ⊥ < N → N ≤ Z2 L1 L2 S →
      L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S := by
  classical
  intro N hNpos hNZ hL2N
  have hstep := (str86_z2_isChiefStep_u3H hF hSB hk hFc hU3 hB2 h2 hZI hL2 hZ2).1
  have hQN : Q2 L1 L2 S ≤ Subgroup.normalizer (N : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxZ : x ∈ Z2 L1 L2 S := hNZ hx
      have hcomm : x * q = q * x :=
        Subgroup.mem_centralizer_iff.mp
          (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) x hxZ
      have heq : q * x * q⁻¹ = x := by rw [← hcomm]; group
      rw [heq]
      exact hx
    · intro hx
      have hxZ : q * x * q⁻¹ ∈ Z2 L1 L2 S := hNZ hx
      have hcomm : (q * x * q⁻¹) * q = q * (q * x * q⁻¹) :=
        Subgroup.mem_centralizer_iff.mp
          (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq)
          (q * x * q⁻¹) hxZ
      have hxeq : x = q⁻¹ * (q * x * q⁻¹) * q := by group
      have heq : q⁻¹ * (q * x * q⁻¹) * q = q * x * q⁻¹ := by
        calc q⁻¹ * (q * x * q⁻¹) * q = q⁻¹ * ((q * x * q⁻¹) * q) := by group
          _ = q⁻¹ * (q * (q * x * q⁻¹)) := by rw [hcomm]
          _ = q * x * q⁻¹ := by group
      rw [hxeq, heq]
      exact hx
  have hNH : u3H L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hL2N hQN
  have hNnormal : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) N :=
    ⟨hNZ.trans (A4.omegaOneCenterOf_le _),
      fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hNH hg) x).mp hx⟩
  rcases hstep.2.2.2 N hNnormal (bot_le) hNZ with hbot | htop
  · exact absurd hbot (ne_of_gt hNpos)
  · exact htop

private theorem str86_q2_quot_irreducible
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    (hQ2card : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8) :
    ∀ N : Subgroup G, Z2 L1 L2 S ≤ N → N ≤ Q2 L1 L2 S →
      L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S ∨ N = Q2 L1 L2 S := by
  classical
  intro N hZN hNQ hL2N
  have hstep := str86_q2_chiefStep hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
    hI4 hX1Q2 hSQ2 hQ2card
  have hab := (str86_q2_quot_elemAbelian hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY
    hX1' hI4 hX1Q2 hSQ2).1
  have hQN : Q2 L1 L2 S ≤ Subgroup.normalizer (N : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : q * x * q⁻¹ * x⁻¹ ∈ Z2 L1 L2 S := hab q hq x (hNQ hx)
      have heq : q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
      rw [heq]
      exact N.mul_mem (hZN h1) hx
    · intro hx
      have hxQ : q * x * q⁻¹ ∈ Q2 L1 L2 S := hNQ hx
      have h1 : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ * (q * x * q⁻¹)⁻¹ ∈ Z2 L1 L2 S :=
        hab q⁻¹ ((Q2 L1 L2 S).inv_mem hq) (q * x * q⁻¹) hxQ
      have heq : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ =
          (q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ * (q * x * q⁻¹)⁻¹) * (q * x * q⁻¹) := by
        group
      have hmem : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ ∈ N := by
        rw [heq]
        exact N.mul_mem (hZN h1) hx
      have hxeq : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x := by group
      rwa [hxeq] at hmem

  have hNH : u3H L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hL2N hQN
  have hNnormal : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) N :=
    ⟨hNQ, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hNH hg) x).mp hx⟩
  exact hstep.2.2.2 N hNnormal hZN hNQ

private theorem str86_commutator_sq_eq_sq {x s : G}
    (hx : (x * s * x⁻¹ * s⁻¹) * x = x * (x * s * x⁻¹ * s⁻¹)) :
    (x * x) * s * (x * x)⁻¹ * s⁻¹ =
      (x * s * x⁻¹ * s⁻¹) * (x * s * x⁻¹ * s⁻¹) := by
  let z : G := x * s * x⁻¹ * s⁻¹
  have hxs : x * s * x⁻¹ = z * s := by dsimp [z]; group
  calc (x * x) * s * (x * x)⁻¹ * s⁻¹
      = x * (x * s * x⁻¹) * x⁻¹ * s⁻¹ := by group
    _ = x * (z * s) * x⁻¹ * s⁻¹ := by rw [hxs]
    _ = x * z * s * x⁻¹ * s⁻¹ := by group
    _ = z * x * s * x⁻¹ * s⁻¹ := by rw [hx]
    _ = z * (x * s * x⁻¹ * s⁻¹) := by group
    _ = z * z := by rfl

private theorem str86_q2_center_eq
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    (hQ2card : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8) :
    centerOf (Q2 L1 L2 S) = Z2 L1 L2 S := by
  classical
  let H := u3H L1 L2 S
  let Q := Q2 L1 L2 S
  let Z := Z2 L1 L2 S
  have hZQle : Z ≤ Q := A4.omegaOneCenterOf_le Q
  have hZleC : Z ≤ centerOf Q := A4.omegaOneCenterOf_le_centerOf Q
  have hCQ : centerOf Q ≤ Q := A4.centerOf_le Q
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hSH : S ≤ H := str86_s_le_u3H hF.toW hSB (by omega) hL2
  have hP2Z : P2 L1 L2 S ≤ Subgroup.normalizer (Z : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)
  have hQZ : Q ≤ Subgroup.normalizer (Z : Set G) := (pCoreOf_le 2 (P2 L1 L2 S)).trans hP2Z
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hstep : IsChiefStep H Q Z Q :=
    str86_q2_chiefStep hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4 hX1Q2 hSQ2
      hQ2card
  have hHC : H ≤ Subgroup.normalizer (centerOf Q : Set G) :=
    hHQ.trans (A4.normalizer_le_normalizer_centerOf Q)
  refine le_antisymm ?_ hZleC
  intro x hxC
  by_contra hxZ
  have hCnormal : IsNormalIn H Q (centerOf Q) :=
    ⟨hCQ, fun g hg y hy => (Subgroup.mem_normalizer_iff.mp (hHC hg) y).mp hy⟩
  rcases hstep.2.2.2 (centerOf Q) hCnormal hZleC hCQ with hCZ | hCQeq
  · have hxZ' : x ∈ Z := by rw [hCZ] at hxC; exact hxC
    exact hxZ hxZ'
  ·
    have hQcomm : IsMulCommutative ↥Q := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : (a : G) ∈ Subgroup.centralizer (Q : Set G) := by
        have haz : (a : G) ∈ centerOf Q := by rw [hCQeq]; exact a.2
        exact (Subgroup.mem_inf.mp haz).2
      exact (Subgroup.mem_centralizer_iff.mp ha (b : G) b.2).symm
    letI : CommGroup ↥Q := IsMulCommutative.instCommGroup
    obtain ⟨-, hsq, -⟩ :=
      str86_q2_quot_elemAbelian hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4
        hX1Q2 hSQ2
    have hZea : IsElemAbelian 2 Z := SmithC27.isElemAbelian_omegaOneCenterOf Q
    let sq : ↥Q →* ↥Z :=
      { toFun := fun q => ⟨(q : G) * (q : G), hsq (q : G) q.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          change ((a * b : ↥Q) : G) * ((a * b : ↥Q) : G) =
            (a : G) * (a : G) * ((b : G) * (b : G))
          rw [Subgroup.coe_mul]
          have hcomm : (b : G) * (a : G) = (a : G) * (b : G) := by
            exact congrArg Subtype.val (mul_comm (b : ↥Q) (a : ↥Q))
          calc (a : G) * (b : G) * ((a : G) * (b : G))
              = (a : G) * ((b : G) * (a : G)) * (b : G) := by group
            _ = (a : G) * ((a : G) * (b : G)) * (b : G) := by rw [hcomm]
            _ = (a : G) * (a : G) * ((b : G) * (b : G)) := by group }
    have hker : sq.ker = Z.subgroupOf Q := by
      ext q
      rw [MonoidHom.mem_ker]
      constructor
      · intro hq
        have hq1 : (q : G) * (q : G) = 1 := by
          have := congrArg Subtype.val hq
          simpa [sq] using this
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ?_)
        refine ⟨?_, by simpa [pow_two] using hq1⟩
        rw [hCQeq]
        exact q.2
      · intro hq
        have hqZ : (q : G) ∈ Z := Subgroup.mem_subgroupOf.mp hq
        have hq1 : (q : G) * (q : G) = 1 := by
          have := hZea.2 (q : G) hqZ
          simpa [pow_two] using this
        apply Subtype.ext
        simpa [sq] using hq1
    have hkerCard : Nat.card ↥sq.ker = Nat.card ↥Z := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQle).toEquiv
    have hq4 : 0 < (2 ^ k) ^ 4 :=
      pow_pos (show (0 : ℕ) < 2 ^ k by exact Nat.pow_pos (by norm_num)) 4
    have hrangeTop : sq.range = ⊤ := by
      have hmul := Subgroup.card_ker_mul_card_range sq
      rw [hkerCard, hQ2card, hZ2] at hmul
      have hq8 : (2 ^ k) ^ 8 = (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := by
        rw [show 8 = 4 + 4 by norm_num, pow_add]
      rw [hq8] at hmul
      have hcardRange : Nat.card ↥sq.range = (2 ^ k) ^ 4 :=
        Nat.eq_of_mul_eq_mul_left hq4 hmul
      apply Subgroup.eq_of_le_of_card_ge (le_top : sq.range ≤ ⊤)
      rw [show Nat.card ↥(⊤ : Subgroup ↥Z) = Nat.card ↥Z from
        Nat.card_congr Subgroup.topEquiv.toEquiv, hZ2, hcardRange]
    have hsurj : Function.Surjective sq := by
      intro z
      have hz : z ∈ sq.range := by rw [hrangeTop]; exact Subgroup.mem_top z
      rwa [MonoidHom.mem_range] at hz
    let C : Subgroup G := Z ⊓ Subgroup.centralizer (S : Set G)
    have hCeq : C = Z1 L1 L2 S :=
      (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.2.2.2
    let D : Subgroup G := centralizerMod Z Q S
    have hDQ : D ≤ Q := centralizerMod_le_left Z Q S
    let sqD : ↥D →* ↥Z := sq.comp (Subgroup.inclusion hDQ)
    have hSZ : S ≤ Subgroup.normalizer (Z : Set G) :=
      (f112_isSylowTwoOf_P2 hF.toW).1.trans
        (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
    have hZD : Z ≤ D := by
      intro z hz
      refine mem_centralizerMod.mpr
        ⟨hZQle hz, (Subgroup.le_normalizer : Z ≤ Subgroup.normalizer (Z : Set G)) hz, ?_⟩
      intro s hs
      have hsz : s * z * s⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hSZ hs) z).mp hz
      have heq : z * s * z⁻¹ * s⁻¹ = z * (s * z * s⁻¹)⁻¹ := by group
      rw [heq]
      exact Z.mul_mem hz (Z.inv_mem hsz)
    have hrangeD : sqD.range = C.subgroupOf Z := by
      ext z
      constructor
      · intro hz
        rw [MonoidHom.mem_range] at hz
        obtain ⟨d, hd⟩ := hz
        obtain ⟨hdQ, -, hdfix⟩ := mem_centralizerMod.mp d.2
        refine Subgroup.mem_subgroupOf.mpr ⟨z.2, ?_⟩
        change (z : G) ∈ Subgroup.centralizer (S : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hdz : (z : G) = (d : G) * (d : G) := by
          have := congrArg Subtype.val hd
          simpa [sqD, sq] using this.symm
        rw [hdz]
        have hcomm : (d : G) * s * (d : G)⁻¹ * s⁻¹ ∈ Z := hdfix s hs
        have hz2 : ((d : G) * s * (d : G)⁻¹ * s⁻¹) *
            ((d : G) * s * (d : G)⁻¹ * s⁻¹) = 1 := by
          have := hZea.2 ((d : G) * s * (d : G)⁻¹ * s⁻¹) hcomm
          simpa [pow_two] using this
        have hwQ : ((d : G) * s * (d : G)⁻¹ * s⁻¹) ∈ Q := by
          have hsH : s ∈ H := hSH hs
          have hsd : s * (d : G)⁻¹ * s⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp (hHQ hsH) (d : G)⁻¹).mp (Q.inv_mem hdQ)
          have hmem : (d : G) * (s * (d : G)⁻¹ * s⁻¹) ∈ Q := Q.mul_mem hdQ hsd
          convert hmem using 1
          group
        have hdx : ((d : G) * s * (d : G)⁻¹ * s⁻¹) * (d : G) =
            (d : G) * ((d : G) * s * (d : G)⁻¹ * s⁻¹) := by
          exact congrArg Subtype.val
            (mul_comm (⟨_, hwQ⟩ : ↥Q) (⟨(d : G), hdQ⟩ : ↥Q))
        have hsx : s * ((d : G) * (d : G)) = ((d : G) * (d : G)) * s := by
          have h := str86_commutator_sq_eq_sq hdx
          rw [hz2] at h
          have h' : ((d : G) * (d : G)) * s = s * ((d : G) * (d : G)) := by
            calc ((d : G) * (d : G)) * s
                = (((d : G) * (d : G)) * s * ((d : G) * (d : G))⁻¹ * s⁻¹) *
                    (s * ((d : G) * (d : G))) := by group
              _ = 1 * (s * ((d : G) * (d : G))) := by rw [h]
              _ = s * ((d : G) * (d : G)) := by rw [one_mul]
          exact h'.symm
        exact hsx
      · intro hz
        rw [MonoidHom.mem_range]
        obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)
        obtain ⟨x, hx⟩ := hsurj ⟨(z : G), hzZ⟩
        have hx2 : (x : G) * (x : G) = (z : G) := by
          have := congrArg Subtype.val hx
          simpa [sq] using this
        have hxQ : (x : G) ∈ Q := x.2
        have hwZ : ∀ s ∈ S, (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ Z := by
          intro s hs
          have hwQ : (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ Q := by
            have hsH : s ∈ H := hSH hs
            have hxs : s * (x : G)⁻¹ * s⁻¹ ∈ Q :=
              (Subgroup.mem_normalizer_iff.mp (hHQ hsH) (x : G)⁻¹).mp (Q.inv_mem hxQ)
            have hmem : (x : G) * (s * (x : G)⁻¹ * s⁻¹) ∈ Q := Q.mul_mem hxQ hxs
            convert hmem using 1
            group
          have hwx : ((x : G) * s * (x : G)⁻¹ * s⁻¹) * (x : G) =
              (x : G) * ((x : G) * s * (x : G)⁻¹ * s⁻¹) :=
            congrArg Subtype.val
              (mul_comm (⟨_, hwQ⟩ : ↥Q) (⟨(x : G), hxQ⟩ : ↥Q))
          have hzS : s * (z : G) = (z : G) * s :=
            Subgroup.mem_centralizer_iff.mp hzC s hs
          have hfix : s * ((x : G) * (x : G)) * s⁻¹ = (x : G) * (x : G) := by
            calc s * ((x : G) * (x : G)) * s⁻¹ = s * (z : G) * s⁻¹ := by rw [hx2]
              _ = (z : G) * s * s⁻¹ := by rw [hzS]
              _ = (z : G) := by group
              _ = (x : G) * (x : G) := hx2.symm
          have hone : ((x : G) * (x : G)) * s * ((x : G) * (x : G))⁻¹ * s⁻¹ = 1 := by
            rw [show ((x : G) * (x : G)) * s * ((x : G) * (x : G))⁻¹ * s⁻¹ =
                ((x : G) * (x : G)) * (s * ((x : G) * (x : G)) * s⁻¹)⁻¹ by group]
            rw [hfix]
            group
          have hww : ((x : G) * s * (x : G)⁻¹ * s⁻¹) *
              ((x : G) * s * (x : G)⁻¹ * s⁻¹) = 1 := by
            have h := str86_commutator_sq_eq_sq hwx
            rw [hone] at h
            exact h.symm
          exact Subgroup.subset_closure ⟨by rw [hCQeq]; exact hwQ, by simpa [pow_two] using hww⟩
        refine ⟨⟨x, ?_⟩, ?_⟩
        · refine mem_centralizerMod.mpr ⟨x.2, hQZ x.2, hwZ⟩
        · apply Subtype.ext
          have := congrArg Subtype.val hx
          simpa [sqD, sq] using this
    have hkerD : sqD.ker = Z.subgroupOf D := by
      ext d
      rw [MonoidHom.mem_ker]
      constructor
      · intro hd
        have hd' : Subgroup.inclusion hDQ d ∈ sq.ker := by
          rw [MonoidHom.mem_ker]
          simpa [sqD] using hd
        rw [hker] at hd'
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hd')
      · intro hd
        have hd' : Subgroup.inclusion hDQ d ∈ Z.subgroupOf Q := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_subgroupOf.mp hd
        have hd'' : Subgroup.inclusion hDQ d ∈ sq.ker := by
          rwa [hker]
        rw [MonoidHom.mem_ker] at hd''
        simpa [sqD] using hd''
    have hcardD : Nat.card ↥D = Nat.card ↥Z * Nat.card ↥C := by
      have hmul := Subgroup.card_ker_mul_card_range sqD
      rw [hkerD, hrangeD] at hmul
      rw [← hmul]
      congr 1
      · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv
      · exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ Z)).toEquiv
    have hrelD : Z.relIndex D = Nat.card ↥C := by
      have hmul := Subgroup.relIndex_mul_card Z D
      rw [inf_eq_left.mpr hZD, hcardD] at hmul
      have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
      have hmul' : Nat.card ↥Z * Z.relIndex D = Nat.card ↥Z * Nat.card ↥C := by
        rw [mul_comm]
        exact hmul
      exact Nat.eq_of_mul_eq_mul_left hZpos hmul'
    have hCcard : Nat.card ↥C = 2 ^ k := by rw [hCeq, hZ1]
    have hnc : ¬ IsCentralStep H Z Q := by
      intro hc
      have hQZle : Q ≤ Z := fun y hy =>
        str86_q2_fixed_mem_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
          hI4 hX1Q2 hSQ2 y hy (fun g hg => hc g hg y hy)
      exact (ne_of_lt hstep.2.2.1) (le_antisymm hstep.2.2.1.le hQZle)
    have hnat : Z.relIndex D = (2 ^ k) ^ 2 :=
      (str86_q2_chiefFactor_natural_card hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hX1' hY hI4
        hX1Q2 hSQ2 le_rfl hstep hnc).2
    have hqeq : (2 ^ k) ^ 2 = 2 ^ k := by rw [← hnat, hrelD, hCcard]
    have hq1 : 1 < 2 ^ k := Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 2)
    have hlt : 2 ^ k < (2 ^ k) ^ 2 := by
      calc 2 ^ k = (2 ^ k) ^ 1 := (pow_one _).symm
        _ < (2 ^ k) ^ 2 := Nat.pow_lt_pow_right hq1 (by norm_num : 1 < 2)
    exact (ne_of_lt hlt) hqeq.symm

private def str86FixMod (H Z : Subgroup G) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (x : G) : Subgroup G where
  carrier := {h | h ∈ H ∧ h * x * h⁻¹ * x⁻¹ ∈ Z}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  mul_mem' := by
    rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
    refine ⟨H.mul_mem haH hbH, ?_⟩
    have hconj : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hHZ haH) _).mp hb
    have h := Z.mul_mem hconj ha
    convert h using 1
    group
  inv_mem' := by
    rintro a ⟨haH, ha⟩
    refine ⟨H.inv_mem haH, ?_⟩
    have hconj : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHZ haH)) _).mp (Z.inv_mem ha)
    convert hconj using 1
    group

private theorem mem_str86FixMod {H Z : Subgroup G} (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (x h : G) : h ∈ str86FixMod H Z hHZ x ↔ h ∈ H ∧ h * x * h⁻¹ * x⁻¹ ∈ Z :=
  Iff.rfl

private theorem str86_q2_conj_inf_eq
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2) :
    ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
      (((Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S) ⊓
        ((MulAut.conj g • Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S)) =
          Z2 L1 L2 S := by
  classical
  intro g hg hgB
  let H := u3H L1 L2 S
  let Q := Q2 L1 L2 S
  let Z := Z2 L1 L2 S
  let Q1 := Q1 L1 L2 S
  let P2 := P2 L1 L2 S
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hZQle : Z ≤ Q := A4.omegaOneCenterOf_le Q
  have hZ1Z2 : Z1 L1 L2 S ≤ Z :=
    (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
  obtain ⟨-, -, -, -, -, hX1Q1⟩ :=
    str86_l2_eq_and_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ
  have hab := (str86_q2_quot_elemAbelian hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY
    hX1' hI4 hX1Q2 hSQ2).1
  have hQQ : Q1 ⊓ Q ≤ centralizerMod Z Q S :=
    str86_q1_inf_q2_le_centralizerMod hX1Q2 hX1Q1 hZ1Z2 hab
  have hn : 2 ≤ 2 * k := by omega
  have hSH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hP2Z : P2 ≤ Subgroup.normalizer (Z : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf P2
  have hQZ : Q ≤ Subgroup.normalizer (Z : Set G) :=
    (pCoreOf_le 2 P2).trans hP2Z
  have hSZ : S ≤ Subgroup.normalizer (Z : Set G) :=
    (f112_isSylowTwoOf_P2 hF.toW).1.trans hP2Z
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := (u3H_le_p2 L1 L2 S).trans hP2Z
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hbigL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (F1.bigB_le_normalizer_left hR).2
  have hgbig : g ∈ bigB L1 L2 S ⊔ L2 := by rwa [sup_comm] at hg
  obtain ⟨b, hb, l, hl, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hbigL2).mp hgbig
  have hbL2 : b ∈ Subgroup.normalizer (L2 : Set G) := hbigL2 hb
  have hbS : b ∈ Subgroup.normalizer (S : Set G) := hSB hb
  have hbP2 : b ∈ P2 := (le_sup_right : bigB L1 L2 S ≤ P2) hb
  have hlP2 : l ∈ P2 := (le_sup_left : L2 ≤ P2) hl
  have hgP2 : b * l ∈ P2 := P2.mul_mem hbP2 hlP2
  have hgZ : b * l ∈ Subgroup.normalizer (Z : Set G) := hP2Z hgP2
  have hgL2 : b * l ∈ Subgroup.normalizer (L2 : Set G) :=
    (Subgroup.normalizer (L2 : Set G)).mul_mem hbL2 (Subgroup.le_normalizer hl)
  have hgQ : b * l ∈ Subgroup.normalizer (Q : Set G) :=
    (le_normalizer_pCoreOf 2 P2) hgP2
  have hlN : l ∉ Subgroup.normalizer (S : Set G) := by
    intro hlS
    have hlB2 : l ∈ borelOf L2 S := by
      refine ⟨hl, ?_⟩
      change l ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyS, hyL2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hlS y).mp hyS,
          L2.mul_mem (L2.mul_mem hl hyL2) (L2.inv_mem hl)⟩
      · rintro ⟨hyS, hyL2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hlS y).mpr hyS, ?_⟩
        have hyL2' : l⁻¹ * (l * y * l⁻¹) * l ∈ L2 :=
          L2.mul_mem (L2.mul_mem (L2.inv_mem hl) hyL2) hl
        have heq : l⁻¹ * (l * y * l⁻¹) * l = y := by group
        rwa [heq] at hyL2'
    have hlBig : l ∈ bigB L1 L2 S :=
      (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S) hlB2
    exact hgB ((bigB L1 L2 S).mul_mem hb hlBig)
  have hL2le : L2 ≤ S ⊔ MulAut.conj l • S ⊔ Q :=
    str86_rankOne_sup_conj_S hF hSB hl hlN
  have hbL2eq : MulAut.conj b • L2 = L2 := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hbL2
  have hbSeq : MulAut.conj b • S = S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hbS
  have hbQeq : MulAut.conj b • Q = Q := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self ((le_normalizer_pCoreOf 2 P2) hbP2)
  have hL2le' : L2 ≤ S ⊔ MulAut.conj (b * l) • S ⊔ Q := by
    calc L2 = MulAut.conj b • L2 := hbL2eq.symm
      _ ≤ MulAut.conj b • (S ⊔ MulAut.conj l • S ⊔ Q) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hL2le
      _ = MulAut.conj b • S ⊔ MulAut.conj b • (MulAut.conj l • S) ⊔
            MulAut.conj b • Q := by rw [Subgroup.smul_sup, Subgroup.smul_sup]
      _ = S ⊔ MulAut.conj (b * l) • S ⊔ Q := by
          rw [hbSeq, hbQeq, smul_smul, ← map_mul]
  have hQleA : Q ≤ S ⊔ MulAut.conj (b * l) • S := by
    refine (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)).trans ?_
    exact le_sup_left
  have hHle : H ≤ S ⊔ MulAut.conj (b * l) • S := by
    calc H = L2 ⊔ Q := rfl
      _ ≤ S ⊔ MulAut.conj (b * l) • S ⊔ Q := sup_le hL2le' le_sup_right
      _ = S ⊔ MulAut.conj (b * l) • S := sup_eq_left.mpr hQleA
  have hZD : Z ≤ centralizerMod Z Q S := by
    intro z hz
    refine mem_centralizerMod.mpr
      ⟨hZQle hz, (Subgroup.le_normalizer : Z ≤ Subgroup.normalizer (Z : Set G)) hz, ?_⟩
    intro s hs
    have hsz : s * z * s⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hSZ hs) z).mp hz
    have heq : z * s * z⁻¹ * s⁻¹ = z * (s * z * s⁻¹)⁻¹ := by group
    rw [heq]
    exact Z.mul_mem hz (Z.inv_mem hsz)
  have hAD : (Q1 ⊓ Q) ⊔ Z ≤ centralizerMod Z Q S := sup_le hQQ hZD
  have hS'Z : MulAut.conj (b * l) • S ≤ Subgroup.normalizer (Z : Set G) := by
    intro s' hs'
    have hsS : (MulAut.conj (b * l))⁻¹ • s' ∈ S := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hs'
    have hs'eq : s' = (b * l) * ((MulAut.conj (b * l))⁻¹ • s') * (b * l)⁻¹ := by
      simp [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [hs'eq]
    exact (Subgroup.normalizer (Z : Set G)).mul_mem
      ((Subgroup.normalizer (Z : Set G)).mul_mem hgZ (hSZ hsS))
      ((Subgroup.normalizer (Z : Set G)).inv_mem hgZ)
  have hZD' : Z ≤ centralizerMod Z Q (MulAut.conj (b * l) • S) := by
    intro z hz
    refine mem_centralizerMod.mpr
      ⟨hZQle hz, (Subgroup.le_normalizer : Z ≤ Subgroup.normalizer (Z : Set G)) hz, ?_⟩
    intro s' hs'
    have hs'z : s' * z * s'⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hS'Z hs') z).mp hz
    have heq : z * s' * z⁻¹ * s'⁻¹ = z * (s' * z * s'⁻¹)⁻¹ := by group
    rw [heq]
    exact Z.mul_mem hz (Z.inv_mem hs'z)
  have hBQ : (MulAut.conj (b * l) • Q1 ⊓ Q) ≤
      centralizerMod Z Q (MulAut.conj (b * l) • S) := by
    intro y hy
    obtain ⟨hygQ1, hyQ⟩ := Subgroup.mem_inf.mp hy
    have hq1 : (MulAut.conj (b * l))⁻¹ • y ∈ Q1 := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hygQ1
    let q : G := (b * l)⁻¹ * y * (b * l)
    have hqeq : (MulAut.conj (b * l))⁻¹ • y = q := by
      rw [← map_inv]
      simp [q, MulAut.conj_apply]
      group
    have hqQ1 : q ∈ Q1 := by
      rwa [hqeq] at hq1
    have hqQ : q ∈ Q := by
      have hgQinv : (b * l)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hgQ
      have h := (Subgroup.mem_normalizer_iff.mp hgQinv y).mp hyQ
      simpa [q] using h
    have hqD : q ∈ centralizerMod Z Q S := hQQ ⟨hqQ1, hqQ⟩
    refine mem_centralizerMod.mpr ⟨hyQ, hQZ hyQ, ?_⟩
    intro s' hs'
    have hsS : (MulAut.conj (b * l))⁻¹ • s' ∈ S := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hs'
    let s : G := (b * l)⁻¹ * s' * (b * l)
    have hseq0 : (MulAut.conj (b * l))⁻¹ • s' = s := by
      rw [← map_inv]
      simp [s, MulAut.conj_apply]
      group
    have hsS' : s ∈ S := by
      rwa [hseq0] at hsS
    have hqs : q * s * q⁻¹ * s⁻¹ ∈ Z := (mem_centralizerMod.mp hqD).2.2 s hsS'
    have hyeq : y = (b * l) * q * (b * l)⁻¹ := by
      simp [q]
      group
    have hseq : s' = (b * l) * s * (b * l)⁻¹ := by
      simp [s]
      group
    have hconjZ : (b * l) * (q * s * q⁻¹ * s⁻¹) * (b * l)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hgZ _).mp hqs
    rw [hyeq, hseq]
    convert hconjZ using 1
    group
  have hBD : (MulAut.conj (b * l) • Q1 ⊓ Q) ⊔ Z ≤
      centralizerMod Z Q (MulAut.conj (b * l) • S) := sup_le hBQ hZD'
  have hS'leH : MulAut.conj (b * l) • S ≤ H := by
    have hgL2eq : MulAut.conj (b * l) • L2 = L2 := by
      rw [mulAut_conj_smul_eq_conjAct]
      exact Subgroup.conjAct_pointwise_smul_eq_self hgL2
    have hgQeq : MulAut.conj (b * l) • Q = Q := by
      rw [mulAut_conj_smul_eq_conjAct]
      exact Subgroup.conjAct_pointwise_smul_eq_self hgQ
    have hHsmul : MulAut.conj (b * l) • H = H := by
      rw [show H = L2 ⊔ Q from rfl, Subgroup.smul_sup, hgL2eq, hgQeq]
    calc MulAut.conj (b * l) • S ≤ MulAut.conj (b * l) • H :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSH
      _ = H := hHsmul
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxA : x ∈ (Q1 ⊓ Q) ⊔ Z := (Subgroup.mem_inf.mp hx).1
    have hxB : x ∈ (MulAut.conj (b * l) • Q1 ⊓ Q) ⊔ Z := (Subgroup.mem_inf.mp hx).2
    have hxQ : x ∈ Q := (sup_le inf_le_right hZQle) hxA
    let C := str86FixMod H Z hHZ x
    have hSC : S ≤ C := by
      intro s hs
      rw [mem_str86FixMod]
      refine ⟨hSH hs, ?_⟩
      have hxs := (mem_centralizerMod.mp (hAD hxA)).2.2 s hs
      have heq : s * x * s⁻¹ * x⁻¹ = (x * s * x⁻¹ * s⁻¹)⁻¹ := by group
      rw [heq]
      exact Z.inv_mem hxs
    have hS'C : MulAut.conj (b * l) • S ≤ C := by
      intro s' hs'
      rw [mem_str86FixMod]
      refine ⟨hS'leH hs', ?_⟩
      have hxs := (mem_centralizerMod.mp (hBD hxB)).2.2 s' hs'
      have heq : s' * x * s'⁻¹ * x⁻¹ = (x * s' * x⁻¹ * s'⁻¹)⁻¹ := by group
      rw [heq]
      exact Z.inv_mem hxs
    have hHC : H ≤ C := hHle.trans (sup_le hSC hS'C)
    exact str86_q2_fixed_mem_z2 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
      hI4 hX1Q2 hSQ2 x hxQ (fun h hh => by
        have hcomm := (mem_str86FixMod hHZ x h).mp (hHC hh)
        exact hcomm.2)
  · intro z hz
    exact Subgroup.mem_inf.mpr
      ⟨(le_sup_right : Z ≤ (Q1 ⊓ Q) ⊔ Z) hz,
        (le_sup_right : Z ≤ (MulAut.conj (b * l) • Q1 ⊓ Q) ⊔ Z) hz⟩

theorem str86_q2_shape
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hI4 : Nat.card (u3X1 L1 L2 S) = (2 ^ k) ^ 7)
    (hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hSQ2 : (Q2 L1 L2 S).relIndex S = (2 ^ k) ^ 2)
    (hQ2card : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8) :
    ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ Z2 L1 L2 S ∧
      (∀ x ∈ Q2 L1 L2 S, x * x ∈ Z2 L1 L2 S) ∧
      (Z2 L1 L2 S).relIndex (Q2 L1 L2 S) = (2 ^ k) ^ 4 ∧
      centerOf (Q2 L1 L2 S) = Z2 L1 L2 S ∧
      (∀ N : Subgroup G, Z2 L1 L2 S ≤ N → N ≤ Q2 L1 L2 S →
        L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S ∨ N = Q2 L1 L2 S) ∧
      (∀ N : Subgroup G, ⊥ < N → N ≤ Z2 L1 L2 S →
        L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S) ∧
      (∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
        (((Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S) ⊓
          ((MulAut.conj g • Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S)) =
            Z2 L1 L2 S) := by
  classical
  obtain ⟨hQ2', hsq, -⟩ := str86_q2_quot_elemAbelian hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2
    hZ1 hY hX1' hI4 hX1Q2 hSQ2
  have hQ2sub : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ Z2 L1 L2 S := by
    rw [Subgroup.commutator_le]
    exact hQ2'
  have hZrel : (Z2 L1 L2 S).relIndex (Q2 L1 L2 S) = (2 ^ k) ^ 4 := by
    have hZQ : Z2 L1 L2 S ≤ Q2 L1 L2 S := A4.omegaOneCenterOf_le _
    have hmul := Subgroup.relIndex_mul_card (Z2 L1 L2 S) (Q2 L1 L2 S)
    rw [inf_eq_left.mpr hZQ, hZ2, hQ2card] at hmul
    have hq4 : 0 < (2 ^ k) ^ 4 := pow_pos (show (0:ℕ) < 2 ^ k by exact Nat.pow_pos (by norm_num)) 4
    have hq8 : (2 ^ k) ^ 8 = (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := by
      rw [show 8 = 4 + 4 by norm_num, pow_add]
    rw [hq8] at hmul
    have hmul' : (2 ^ k) ^ 4 * (Z2 L1 L2 S).relIndex (Q2 L1 L2 S) =
        (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := by
      rw [mul_comm]
      exact hmul
    exact Nat.eq_of_mul_eq_mul_left hq4 hmul'
  exact ⟨hQ2sub, hsq, hZrel,
    str86_q2_center_eq hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4 hX1Q2 hSQ2
      hQ2card,
    str86_q2_quot_irreducible hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4
      hX1Q2 hSQ2 hQ2card,
    str86_q2_z2_irreducible hF hSB hk hFc hU3 hB2 h2 hZI hL2 hZ2,
    str86_q2_conj_inf_eq hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1' hI4 hX1Q2
      hSQ2⟩

end CFSG.Quasithin.Stroth

end

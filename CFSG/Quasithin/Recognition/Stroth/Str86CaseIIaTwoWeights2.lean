module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoWeights
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoChars

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem str86_caseIIa_two_weights
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hNZ : N ≤ Z1 L1 L2 S) (hNne : N ≠ ⊥)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G))
    (hNS : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S)
    (hNat : @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k)
    (hflag : Nat.card ↥(N ⊓ Subgroup.centralizer (S : Set G)) = (2 ^ k) ^ 2 ∧
      Nat.card ↥⁅N, S⁆ = (2 ^ k) ^ 4 ∧
      ⁅⁅N, S⁆, S⁆ = N ⊓ Subgroup.centralizer (S : Set G) ∧
      N ⊓ Subgroup.centralizer (S : Set G) ≤ ⁅N, S⁆)
    {p : Subgroup G} (hp : p = N ⊓ Subgroup.centralizer (S : Set G))
    {Kb : Subgroup G}
    (hKb : Kb ≤ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G))
    (hKbB : Kb ≤ bigB L1 L2 S)
    (hKbcyc : IsCyclic ↥Kb)
    (hKbcard : Nat.card ↥Kb = 2 ^ m - 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ χ₂ χ₃ : ↥Kb →* Kˣ,
        (∀ d : ↥Kb, (χ₃ d : K) = (χ₂ d : K) ^ (2 ^ k + 1)) ∧
        (∀ d : ↥Kb, (χ₃ d : K) ^ (2 ^ k) = (χ₃ d : K)) ∧
        (∀ d : ↥Kb,
          ((∀ y ∈ str86U2 p p L2 S ⊔ ⁅N, S⁆,
              ((d : G) * y * (d : G)⁻¹) * y⁻¹ ∈ str86U2 p p L2 S) ↔
            (χ₂ d : K) = 1)) ∧
        (∀ d : ↥Kb,
          ((∀ y ∈ str86U2 p p L2 S ⊔ ⁅N, S⁆,
              ((d : G) * y * (d : G)⁻¹) * y⁻¹ ∈ str86U2 p p L2 S →
              y ∈ str86U2 p p L2 S) ↔
            (χ₂ d : K) ≠ 1)) ∧
        (∀ d : ↥Kb,
          ((∀ y ∈ N ⊔ str86U1 ⁅N, S⁆ L2 S,
              ((d : G) * y * (d : G)⁻¹) * y⁻¹ ∈ str86U1 ⁅N, S⁆ L2 S) ↔
            (χ₃ d : K) = 1)) ∧
        (∀ d : ↥Kb,
          ((∀ y ∈ N ⊔ str86U1 ⁅N, S⁆ L2 S,
              ((d : G) * y * (d : G)⁻¹) * y⁻¹ ∈ str86U1 ⁅N, S⁆ L2 S →
              y ∈ str86U1 ⁅N, S⁆ L2 S) ↔
            (χ₃ d : K) ≠ 1)) ∧
        (N ⊓ Subgroup.centralizer (S : Set G)).relIndex ⁅N, S⁆ = (2 ^ k) ^ 2 := by
  classical
  let H : Subgroup G := L2 ⊔ S
  let P : Subgroup G := ⁅N, S⁆
  let U₁ : Subgroup G := str86U1 P L2 S
  let U₂ : Subgroup G := str86U2 p p L2 S
  let U : Subgroup G := str86U L1 L2 S
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, Φ, χ₂, χ₃, hSact, hSsurj, hχrel, hχpow,
    hact⟩ :=
    str86_caseIIa_two_chars hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hN hNZ hNne hNP1 hNS
      hNat hKb hKbB
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hm2 : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hSleP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSleP1.trans hNP1
  obtain ⟨hcent, hPleN, hPmem, -, -⟩ :=
    str86_flag_coords_of_ujSub hN hSN hk hKcard Φ hSact hSsurj
  have hPN : P ≤ N := hPleN
  have hpP : p ≤ P := by rw [hp]; simpa [P] using hflag.2.2.2
  have hpU₂ : p ≤ U₂ := le_conjClosure p H
  have hPleU₁ : P ≤ U₁ := le_conjClosure P H
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hSB hm2 hm
  have hQ2H : H ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm2, hm⟩))
  have hU2leZ2 : U₂ ≤ Z2 L1 L2 S :=
    str86U2_le_z2 hN hNZ hp hQ2S hQ2H hZ
  have hZ2C : Z2 L1 L2 S ≤ Subgroup.centralizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hSle : S ≤ L2 ⊔ Q2 L1 L2 S :=
      (le_of_eq hS2).trans (sup_le ((inf_le_right : S ⊓ L2 ≤ L2).trans le_sup_left) le_sup_right)
    exact (Subgroup.mem_centralizer_iff.mp (hIIa (hSle hs)) z hz).symm
  have hU₂C : U₂ ≤ Subgroup.centralizer (S : Set G) := hU2leZ2.trans hZ2C
  have hinf : P ⊓ U₂ = p := inf_str86U2_eq_p hPN hpP hpU₂ hU₂C hp
  have hNnotU₁ : ¬ N ≤ U₁ := by
    simpa [U₁, P] using
      (str86_caseIIa_two_u1_not_le (L1 := L1) (L2 := L2) (S := S) hF hSB hk hFc hU3
        hB2 hm hZ hNne hNZ hNP1)
  have hKbN : Kb ≤ Subgroup.normalizer (N : Set G) :=
    hKbB.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hNP1)
  have hKbS : Kb ≤ Subgroup.normalizer (S : Set G) := hKb.trans inf_le_right
  have hKbP : Kb ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hKbN hKbS
  have hHnormU₁ : H ≤ Subgroup.normalizer (U₁ : Set G) :=
    str86U1_normalizes (P := P) (L2 := L2) (S := S)
  have hHnormU₂ : H ≤ Subgroup.normalizer (U₂ : Set G) :=
    str86U2_normalizes (p := p) (N := p) (L2 := L2) (S := S)
  have hKbU₁ : Kb ≤ Subgroup.normalizer (U₁ : Set G) :=
    (hKb.trans inf_le_left).trans hHnormU₁
  have hKbU₂ : Kb ≤ Subgroup.normalizer (U₂ : Set G) :=
    (hKb.trans inf_le_left).trans hHnormU₂
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hUe : IsElemAbelian 2 U :=
    isElemAbelian_str86U_of_caseII hF hSB hq hm2 hm hII hZ
  have hZ1U : Z1 L1 L2 S ≤ U := le_conjClosure (Z1 L1 L2 S) H
  have hNU : N ≤ U := hNZ.trans hZ1U
  have hPZ1 : P ≤ Z1 L1 L2 S := hPN.trans hNZ
  have hPU : P ≤ U := hPZ1.trans hZ1U
  have hpN : p ≤ N := by rw [hp]; exact inf_le_left
  have hpZ1 : p ≤ Z1 L1 L2 S := hpN.trans hNZ
  have hU₁U : U₁ ≤ U := str86U1_le_str86U hPZ1
  have hU₂U : U₂ ≤ U := str86U2_le_str86U hpZ1
  have hrelP : p.relIndex P = (2 ^ k) ^ 2 := by
    have hmul := Subgroup.relIndex_mul_card p P
    have hinfpP : p ⊓ P = p := inf_eq_left.mpr hpP
    rw [hinfpP] at hmul
    have hmul' : (N ⊓ Subgroup.centralizer (S : Set G)).relIndex ⁅N, S⁆ *
        Nat.card ↥(N ⊓ Subgroup.centralizer (S : Set G)) =
          Nat.card ↥⁅N, S⁆ := by
      simpa [P, hp] using hmul
    rw [hflag.1, hflag.2.1] at hmul'
    have hq4 : (2 ^ k) ^ 4 = (2 ^ k) ^ 2 * (2 ^ k) ^ 2 := by ring
    rw [hq4] at hmul'
    have hres := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ k) ^ 2) hmul'
    simpa [P, hp] using hres
  have hmain := str86_two_weights_section (S := S) (N := N) (p := p) (P := P)
    (U₁ := U₁) (U₂ := U₂) (U := U) (Kb := Kb) (Φ := Φ) (χ₂ := χ₂) (χ₃ := χ₃)
    hk hKcard hN hPN hpP hpU₂ hPleU₁ hp hcent hPmem hinf hUe hNU hPU hU₁U hU₂U
    hKbN hKbP hKbU₁ hKbU₂ hact hNnotU₁ hrelP
  refine ⟨K, hKfield, hKfin, hKcard, χ₂, χ₃, hχrel, hχpow, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    simpa [commutatorElement_def, U₂, P] using hmain.1 d
  · intro d
    simpa [commutatorElement_def, U₂, P] using hmain.2.1 d
  · intro d
    simpa [commutatorElement_def, U₁] using hmain.2.2.1 d
  · intro d
    simpa [commutatorElement_def, U₁] using hmain.2.2.2.1 d
  · have := hmain.2.2.2.2
    simpa [P, hp] using this

end CFSG.Quasithin.Stroth

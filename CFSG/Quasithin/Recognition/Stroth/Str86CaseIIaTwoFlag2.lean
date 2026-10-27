module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoModel
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoCoords

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_two_flag
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
    (hNat : @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k) :
    Nat.card ↥(N ⊓ Subgroup.centralizer (S : Set G)) = (2 ^ k) ^ 2 ∧
      Nat.card ↥⁅N, S⁆ = (2 ^ k) ^ 4 ∧
      ⁅⁅N, S⁆, S⁆ = N ⊓ Subgroup.centralizer (S : Set G) ∧
      N ⊓ Subgroup.centralizer (S : Set G) ≤ ⁅N, S⁆ := by
  classical
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, hΦ⟩ :=
    str86_caseIIa_two_model hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hN hNZ hNne hNP1 hNS hNat
  obtain ⟨Φ, hconj⟩ := hΦ
  obtain ⟨hL1, hL1', h3, h4⟩ := hconj
  have hSbigB : S ≤ bigB L1 L2 S := le_sup_right
  have hSP1 : S ≤ P1 L1 L2 S := hSbigB.trans le_sup_right
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSP1.trans hNP1
  obtain ⟨hC, hNSle, hNSmem, hNNle, hNNmem⟩ :=
    str86_flag_coords_of_ujSub hN hSN hk hKcard Φ h3 h4
  let eA : ↥(N ⊓ Subgroup.centralizer (S : Set G)) ≃
      {v : Fin 3 → K // v 1 = 0 ∧ v 2 = 0} :=
  { toFun x :=
      let hx := Subgroup.mem_inf.mp x.2
      ⟨Φ (Additive.ofMul ⟨x.1, hx.1⟩), (hC ⟨x.1, hx.1⟩).1 hx.2⟩
    invFun v :=
      let z : Additive ↥N := Φ.symm v.1
      have hzval : Φ (Additive.ofMul z.toMul) = v.1 := by
        rw [ofMul_toMul]
        exact Φ.apply_symm_apply v.1
      have hc : (z.toMul : G) ∈ Subgroup.centralizer (S : Set G) := by
        rw [hC z.toMul, hzval]
        exact v.2
      ⟨z.toMul.1, Subgroup.mem_inf.mpr ⟨z.toMul.2, hc⟩⟩
    left_inv x := by
      apply Subtype.ext
      change (Φ.symm (Φ (Additive.ofMul ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩))).toMul.1 = x.1
      rw [Φ.symm_apply_apply, toMul_ofMul]
    right_inv v := by
      apply Subtype.ext
      change Φ (Additive.ofMul (Additive.toMul (Φ.symm v.1))) = v.1
      rw [ofMul_toMul]
      exact Φ.apply_symm_apply v.1 }
  let e0 : {v : Fin 3 → K // v 1 = 0 ∧ v 2 = 0} ≃ K :=
  { toFun v := v.1 0
    invFun c := ⟨![c, 0, 0], by simp⟩
    left_inv v := by
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [v.2.1, v.2.2]
    right_inv c := by simp }
  have hcardA : Nat.card ↥(N ⊓ Subgroup.centralizer (S : Set G)) = (2 ^ k) ^ 2 := by
    rw [Nat.card_congr eA, Nat.card_congr e0, hKcard]
  let eB : ↥⁅N, S⁆ ≃ {v : Fin 3 → K // v 2 = 0} :=
  { toFun x :=
      let n : ↥N := ⟨x.1, hNSle x.2⟩
      ⟨Φ (Additive.ofMul n), (hNSmem n).1 x.2⟩
    invFun v :=
      let z : Additive ↥N := Φ.symm v.1
      have hzval : Φ (Additive.ofMul z.toMul) = v.1 := by
        rw [ofMul_toMul]
        exact Φ.apply_symm_apply v.1
      have hz : (z.toMul : G) ∈ ⁅N, S⁆ := by
        rw [hNSmem z.toMul, hzval]
        exact v.2
      ⟨z.toMul.1, hz⟩
    left_inv x := by
      apply Subtype.ext
      change (Φ.symm (Φ (Additive.ofMul ⟨x.1, hNSle x.2⟩))).toMul.1 = x.1
      rw [Φ.symm_apply_apply, toMul_ofMul]
    right_inv v := by
      apply Subtype.ext
      change Φ (Additive.ofMul (Additive.toMul (Φ.symm v.1))) = v.1
      rw [ofMul_toMul]
      exact Φ.apply_symm_apply v.1 }
  let e2 : {v : Fin 3 → K // v 2 = 0} ≃ K × K :=
  { toFun v := (v.1 0, v.1 1)
    invFun p := ⟨![p.1, p.2, 0], by simp⟩
    left_inv v := by
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [v.2]
    right_inv p := by
      ext <;> simp }
  have hcardB : Nat.card ↥⁅N, S⁆ = (2 ^ k) ^ 4 := by
    rw [Nat.card_congr eB, Nat.card_congr e2, Nat.card_prod, hKcard]
    ring
  have hdouble : ⁅⁅N, S⁆, S⁆ = N ⊓ Subgroup.centralizer (S : Set G) := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ N := hNNle hx
      have hxmem : Φ (Additive.ofMul ⟨x, hxN⟩) 1 = 0 ∧
          Φ (Additive.ofMul ⟨x, hxN⟩) 2 = 0 := (hNNmem ⟨x, hxN⟩).1 hx
      exact Subgroup.mem_inf.mpr ⟨hxN, (hC ⟨x, hxN⟩).2 hxmem⟩
    · intro x hx
      obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
      exact (hNNmem ⟨x, hxN⟩).2 ((hC ⟨x, hxN⟩).1 hxC)
  have hinf_le : N ⊓ Subgroup.centralizer (S : Set G) ≤ ⁅N, S⁆ := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    exact (hNSmem ⟨x, hxN⟩).2 ((hC ⟨x, hxN⟩).1 hxC).2
  exact ⟨hcardA, hcardB, hdouble, hinf_le⟩

end CFSG.Quasithin.Stroth

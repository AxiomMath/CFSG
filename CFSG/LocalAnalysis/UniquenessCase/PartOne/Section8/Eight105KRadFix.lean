module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadLine
import CFSG.RankThree.PartOne.KF.R9Plane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

omit [Finite K] [CharP K 2] in
private def fixSub {n q : ℕ} (W : Submodule K (Fin n → K)) (Q : Subgroup (StatedSU n q K)) :
    Submodule K (Fin n → K) where
  carrier := {v | v ∈ W ∧ ∀ y ∈ Q, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := fun ha hc => ⟨W.add_mem ha.1 hc.1, fun y hy => by
    rw [Matrix.mulVec_add, ha.2 y hy, hc.2 y hy]⟩
  zero_mem' := ⟨W.zero_mem, fun _ _ => Matrix.mulVec_zero _⟩
  smul_mem' := fun c _ hv => ⟨W.smul_mem c hv.1, fun y hy => by
    rw [Matrix.mulVec_smul, hv.2 y hy]⟩

omit [Finite K] [CharP K 2] in
private theorem mem_fixSub {n q : ℕ} {W : Submodule K (Fin n → K)}
    {Q : Subgroup (StatedSU n q K)} {v : Fin n → K} :
    v ∈ fixSub W Q ↔ v ∈ W ∧ ∀ y ∈ Q, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  Iff.rfl

omit [Finite K] [CharP K 2] in
private theorem mulVec_mem_fixSub {n q : ℕ} {W : Submodule K (Fin n → K)}
    {Q : Subgroup (StatedSU n q K)} {k : StatedSU n q K} (hkW : k ∈ stabSU q W)
    (hkQ : ∀ y ∈ Q, k⁻¹ * y * k ∈ Q) {v : Fin n → K} (hv : v ∈ fixSub W Q) :
    ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ fixSub W Q := by
  obtain ⟨hvW, hvQ⟩ := mem_fixSub.mp hv
  refine mem_fixSub.mpr ⟨mem_stabSU.mp hkW v hvW, fun y hy => ?_⟩
  have h := hvQ _ (hkQ y hy)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec] at h
  have hinv : ∀ u : Fin n → K, ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((((k⁻¹ : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u :=
    fun u => by rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, Matrix.one_mulVec]
  rw [← hinv (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
    (((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)), h]

private theorem fixSub_eq_of_moves_line {n q : ℕ} {W : Submodule K (Fin n → K)}
    {Q : Subgroup (StatedSU n q K)} (hQ : IsPGroup 2 Q) (hQW : Q ≤ stabSU q W)
    (hW : Module.finrank K W = 2) {K₀ : Subgroup (StatedSU n q K)} (hK₀W : K₀ ≤ stabSU q W)
    (hK₀Q : ∀ k ∈ K₀, ∀ y ∈ Q, k⁻¹ * y * k ∈ Q)
    (hmove : ∀ L : Submodule K (Fin n → K), L ≤ W → Module.finrank K L = 1 →
      ∃ k ∈ K₀, ∃ v ∈ L, ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∉ L) :
    fixSub W Q = W := by
  have hW0 : W ≠ ⊥ := fun hbot => by
    rw [hbot] at hW
    simp at hW
  obtain ⟨x, hx, hx0, hfix⟩ := CFSG.RankThree.PartOne.KFU.exists_nonzero_fixed
    (Q.map (StatedSU n q K).subtype) (hQ.map _) W hW0 (by
      rintro _ ⟨y, hy, rfl⟩ v hv
      exact mem_stabSU.mp (hQW hy) v hv)
  have hxC : x ∈ fixSub W Q := mem_fixSub.mpr ⟨hx, fun y hy => hfix _ (mem_map_of_mem _ hy)⟩
  have hle : fixSub W Q ≤ W := fun v hv => (mem_fixSub.mp hv).1
  by_contra hne
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have h0 : Module.finrank K (fixSub W Q) ≠ 0 := fun h0 =>
    hx0 ((Submodule.eq_bot_iff _).mp (Submodule.finrank_eq_zero.mp h0) x hxC)
  rw [hW] at hlt
  obtain ⟨k, hk, v, hv, hkv⟩ := hmove _ hle (by omega)
  exact hkv (mulVec_mem_fixSub (hK₀W hk) (hK₀Q k hk) hv)

theorem RadSetup.pCoreOf_fix (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) {y : StatedSU (2 * 2 + ε) (2 ^ f) K}
    (hy : y ∈ pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω))) {w : Fin (2 * 2 + ε) → K}
    (hw : w ∈ eigSU b ω) :
    ((y : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := fixSub_eq_of_moves_line (W := eigSU b ω)
    (Q := pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (map_subtype_le _) hS.finrank_eig
    (kOf_le_stabSU_eigSU b ω) (fun k hk y hy => by
      have hkN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (inv_mem (kOf_le_stabSU_eigSU b ω hk))
      have hk' := (mem_normalizer_iff.mp hkN y).mp hy
      rwa [inv_inv] at hk')
    (fun L hLW hL => hS.kOf_moves_line h hK₀ hLW hL)
  have hwC : w ∈ fixSub (eigSU b ω) (pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω))) := by
    rw [hC]
    exact hw
  exact (mem_fixSub.mp hwC).2 y hy

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

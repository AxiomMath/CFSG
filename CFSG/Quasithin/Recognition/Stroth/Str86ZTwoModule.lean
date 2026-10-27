module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mulAut_conj_smul_eq_conjAct (g : G) (H : Subgroup G) :
    MulAut.conj g • H = ConjAct.toConjAct g • H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul]
  simp [MulAut.conj_apply]

theorem bigB_le_normalizer_u3Y {L1 L2 S : Subgroup G} :
    bigB L1 L2 S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) := by
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := by
    rw [P2, bigB_comm]
    exact le_sup_right
  have hBQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hBP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (hBP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  exact (le_inf hBZ hBQ).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem str86_u3Y_normalizer_left
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    L1 ⊓ Subgroup.normalizer (u3Y L1 L2 S : Set G) = borelOf L1 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hmax := F1.isUniqueMax_borelOf (Li := L1) (S := S) hR.r1
  have hB1big : borelOf L1 S ≤ bigB L1 L2 S :=
    (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S)
  have hBN : borelOf L1 S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
    hB1big.trans (bigB_le_normalizer_u3Y (L1 := L1) (L2 := L2) (S := S))
  have hS1N : S ⊓ L1 ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
    inf_le_left.trans (le_normalizer_u3Y_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hlt : L1 ⊓ Subgroup.normalizer (u3Y L1 L2 S : Set G) < L1 := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro htop
    apply str86_u3Y_not_normal hF hSB hk hFc hU3 hn hL2 hZQ hser
    refine sup_le ?_ (le_normalizer_u3Y_of_sylow (L1 := L1) (L2 := L2) (S := S))
    exact (le_of_eq htop.symm).trans inf_le_right
  have hle := hmax.2.2 (L1 ⊓ Subgroup.normalizer (u3Y L1 L2 S : Set G))
    (le_inf inf_le_right hS1N) hlt
  exact le_antisymm hle (le_inf (F1.borelOf_le L1 S) hBN)

theorem str86_u3Y_normalizer
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    Subgroup.normalizer (u3Y L1 L2 S : Set G) ⊓ (L1 ⊔ S) =
      bigB L1 L2 S ⊓ (L1 ⊔ S) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB
      (Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hQ1Lhat : Q1 L1 L2 S ≤ L1 ⊔ S := by
    rw [hLhatQ]
    exact le_sup_right
  have hL1Q1 : L1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
    fun q hq => le_normalizer_u3Y_of_sylow (L1 := L1) (L2 := L2) (S := S) (hQ1S hq)
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgN, hgL⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨l, hl, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hL1Q1).mp (hLhatQ ▸ hgL)
    have hqN : q ∈ Subgroup.normalizer (u3Y L1 L2 S : Set G) := hQ1N hq
    let NY : Subgroup G := Subgroup.normalizer (u3Y L1 L2 S : Set G)
    have hlN : l ∈ NY := by
      have hmul : (l * q) * q⁻¹ ∈ NY := NY.mul_mem hgN (NY.inv_mem hqN)
      simpa [NY, mul_assoc] using hmul
    have hlB : l ∈ borelOf L1 S := by
      have hlL1N : l ∈ L1 ⊓ NY := Subgroup.mem_inf.mpr ⟨hl, hlN⟩
      rwa [str86_u3Y_normalizer_left hF hSB hk hFc hU3 hn hL2 hZQ hser] at hlL1N
    have hqB : q ∈ bigB L1 L2 S :=
      (le_sup_right : S ≤ bigB L1 L2 S) (hQ1S hq)
    have hB1big : borelOf L1 S ≤ bigB L1 L2 S :=
      (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S)
    have hgB : l * q ∈ bigB L1 L2 S := (bigB L1 L2 S).mul_mem (hB1big hlB) hqB
    exact Subgroup.mem_inf.mpr ⟨hgB, hLhatQ ▸ (show l * q ∈ L1 ⊔ Q1 L1 L2 S from
      (L1 ⊔ Q1 L1 L2 S).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hq))⟩
  · intro g hg
    exact Subgroup.mem_inf.mpr ⟨bigB_le_normalizer_u3Y (L1 := L1) (L2 := L2) (S := S)
      (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩


theorem str86_u3Y_conj_le_q1 {L1 L2 S : Subgroup G} {g : G} (hg : g ∈ L1 ⊔ S) :
    MulAut.conj g • u3Y L1 L2 S ≤ Q1 L1 L2 S := by
  have hgP1 : g ∈ P1 L1 L2 S :=
    (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) hg
  have hgN : g ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hgP1
  have hYQ : u3Y L1 L2 S ≤ Q1 L1 L2 S := by
    rw [u3Y]
    exact inf_le_right
  have hle : MulAut.conj g • u3Y L1 L2 S ≤ MulAut.conj g • Q1 L1 L2 S :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ
  simp only [mulAut_conj_smul_eq_conjAct] at hle
  rwa [Subgroup.conjAct_pointwise_smul_eq_self hgN] at hle

theorem str86_u3Y_conj_eq_iff
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c)
    {g : G} (hg : g ∈ L1 ⊔ S) :
    MulAut.conj g • u3Y L1 L2 S = u3Y L1 L2 S ↔ g ∈ bigB L1 L2 S ⊓ (L1 ⊔ S) := by
  constructor
  · intro hconj
    have hN : g ∈ Subgroup.normalizer (u3Y L1 L2 S : Set G) := by
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      rwa [← mulAut_conj_smul_eq_conjAct]
    have hmem : g ∈ Subgroup.normalizer (u3Y L1 L2 S : Set G) ⊓ (L1 ⊔ S) :=
      Subgroup.mem_inf.mpr ⟨hN, hg⟩
    rwa [str86_u3Y_normalizer hF hSB hk hFc hU3 hn hL2 hZQ hser] at hmem
  · intro hgB
    have hN : g ∈ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
      (Subgroup.mem_inf.mp hgB).1 |> fun h =>
        bigB_le_normalizer_u3Y (L1 := L1) (L2 := L2) (S := S) h
    have hca := Subgroup.conjAct_pointwise_smul_eq_self hN
    rwa [mulAut_conj_smul_eq_conjAct]

end CFSG.Quasithin.Stroth

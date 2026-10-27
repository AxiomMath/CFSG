module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42bf_relIndex {K L : Subgroup G} (hKL : K ≤ L)
    (hK : Nat.card ↥K = 768) (hL : Nat.card ↥L = 3840) : K.relIndex L = 5 := by
  have h := Subgroup.relIndex_mul_card (H := K) (K := L)
  rw [inf_eq_left.mpr hKL] at h
  have h' : K.relIndex L * 768 = 3840 := by rw [← hK, ← hL]; exact h
  omega

private theorem he42bf_side {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G}
    {a : G} (hD : Data40 A A' u w m N T a) (hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G))
    {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3) :
    Nat.card ↥(normalizer (A : Set G) ⊓
        centralizer ((((A ⊓ A') ⊓ centralizer ({x} : Set G)) : Subgroup G) : Set G)) = 3840 ∧
      Nat.card ↥(N ⊓ centralizer ((((A ⊓ A') ⊓ centralizer ({x} : Set G)) : Subgroup G) : Set G)) =
        768 ∧
      A ⊔ A' ≤ N ⊓ centralizer ((((A ⊓ A') ⊓ centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨b, hb, hbm⟩ := hD.exists_b hxN hxa hx3
  obtain ⟨hb1, hba, hL, hK, -⟩ := hD.alt5 hN hxN hxa hx3 hb hbm
  have hc := hD.centralizer_B hxN hxa hx3 hb hb1 hba
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, ← inf_assoc]
    exact hL
  · rw [hc, ← inf_assoc]
    exact hK
  · rw [hc, ← inf_assoc]
    exact hD.J_le_Kg hxN hxa hx3 hb hbm

theorem HeSetup.baseFacts (S : HeSetup G) : S.BaseFacts := by
  have hN' : S.N = normalizer ((S.A' ⊔ S.A : Subgroup G) : Set G) := by
    rw [S.hN, sup_comm]
  obtain ⟨hL1, hK, hJ⟩ := he42bf_side S.hD S.hN S.hxN S.hxa S.hx3
  obtain ⟨hL2, -, -⟩ := he42bf_side S.hD' hN' S.hxN S.hxa S.hx3
  have hB : ((S.A' ⊓ S.A) ⊓ centralizer ({S.x} : Set G) : Subgroup G) = S.B := by
    show ((S.A' ⊓ S.A) ⊓ centralizer ({S.x} : Set G) : Subgroup G) =
      (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G)
    rw [inf_comm S.A' S.A]
  rw [hB] at hL2
  have hKL1 : S.K ≤ S.L1 := by
    show S.N ⊓ centralizer (S.B : Set G) ≤ normalizer (S.A : Set G) ⊓ centralizer (S.B : Set G)
    exact inf_le_inf_right _ S.hD.N_le_M
  have hKL2 : S.K ≤ S.L2 := by
    show S.N ⊓ centralizer (S.B : Set G) ≤ normalizer (S.A' : Set G) ⊓ centralizer (S.B : Set G)
    exact inf_le_inf_right _ S.hD'.N_le_M
  have hL12 : S.L1 ⊓ S.L2 = S.K := by
    apply le_antisymm
    · intro g hg
      obtain ⟨⟨hgA, hgB⟩, ⟨hgA', -⟩⟩ := hg
      have hgJ : g ∈ normalizer ((S.A ⊔ S.A' : Subgroup G) : Set G) := by
        apply Subgroup.mem_normalizer_fintype
        intro n hn
        refine CFSG.Quasithin.A94.HeJ.sup_induction (A := S.A) (A' := S.A')
          (P := fun y => g * y * g⁻¹ ∈ S.A ⊔ S.A') (x := n) ?_ ?_ ?_ ?_ ?_ hn
        · intro y hy
          exact (le_sup_left : S.A ≤ S.A ⊔ S.A') ((Subgroup.mem_normalizer_iff.1 hgA y).1 hy)
        · intro y hy
          exact (le_sup_right : S.A' ≤ S.A ⊔ S.A') ((Subgroup.mem_normalizer_iff.1 hgA' y).1 hy)
        · show g * 1 * g⁻¹ ∈ S.A ⊔ S.A'
          rw [mul_one, mul_inv_cancel]
          exact (S.A ⊔ S.A').one_mem
        · intro x y _ _ hx hy
          show g * (x * y) * g⁻¹ ∈ S.A ⊔ S.A'
          have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          rw [e]
          exact (S.A ⊔ S.A').mul_mem hx hy
        · intro x _ hx
          show g * x⁻¹ * g⁻¹ ∈ S.A ⊔ S.A'
          have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
          rw [e]
          exact (S.A ⊔ S.A').inv_mem hx
      have hgN : g ∈ S.N := by
        rw [S.hN]
        exact hgJ
      exact Subgroup.mem_inf.2 ⟨hgN, hgB⟩
    · exact le_inf hKL1 hKL2
  refine
    { card_A := S.hD.card_A
      card_A' := S.hD'.card_A
      card_Z := S.hD.card_Z
      card_J := S.hD.cardJ
      card_N := S.hD.cardN
      card_B := S.hD.card_B S.hxN S.hxa S.hx3
      card_L1 := hL1
      card_L2 := hL2
      card_K := hK
      A_le_J := le_sup_left
      A'_le_J := le_sup_right
      Z_le_A := inf_le_left
      Z_le_A' := inf_le_right
      B_le_Z := inf_le_left
      J_le_K := hJ
      K_le_N := inf_le_left
      K_le_L1 := hKL1
      K_le_L2 := hKL2
      L1_inf_L2 := hL12
      relIndex_K_L1 := he42bf_relIndex hKL1 hK hL1
      relIndex_K_L2 := he42bf_relIndex hKL2 hK hL2
      L1_le_normalizer := inf_le_left
      L2_le_normalizer := inf_le_left
      L1_le_centralizer := inf_le_right
      L2_le_centralizer := inf_le_right
      A_comm := S.hD.hK.Aab
      A'_comm := S.hD.hK.A'ab
      A_sq := S.hD.hK.Asq
      A'_sq := S.hD'.hK.Asq }

end CFSG.Quasithin.A94.He42

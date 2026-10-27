module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOneChiefStep
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_X1_isChiefStep_z1
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
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    IsChiefStep (L1 ⊔ S) (u3X1 L1 L2 S) (Z1 L1 L2 S) (u3X1 L1 L2 S) := by
  classical
  obtain ⟨L, N, hstep, hLeq, hXeq⟩ :=
    str86_exists_chiefStep_X1_z1 hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
      hX1Q1
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSeq : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hSH : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hSeq
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hcent : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (sup_le le_sup_left hSH).trans hZI
  have hZH : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hZcentral : ∀ h ∈ (L1 ⊔ S : Subgroup G), ∀ z ∈ Z1 L1 L2 S, h * z = z * h := by
    intro h hh z hz
    exact (Subgroup.mem_centralizer_iff.mp (hcent hh) z hz).symm
  have hZX : Z1 L1 L2 S ≤ u3X1 L1 L2 S := u3Z1_le_u3X1 hF hSB h1 hB2 h2 hZI
  have hXH : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans (hQ1S.trans le_sup_right)
  have hNH : N ≤ L1 ⊔ S := hstep.1.1.trans hXH
  have hcommNZ : ∀ n ∈ N, ∀ z ∈ Z1 L1 L2 S, n * z = z * n := fun n hn z hz =>
    hZcentral n (hNH hn) z hz
  have hX1norm : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF hg) x).mp hx⟩
  have hZ1norm : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (Z1 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer hZX hZH
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ1
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hZ1neX : Z1 L1 L2 S ≠ u3X1 L1 L2 S := by
    intro hZXeq
    have hX1C : u3X1 L1 L2 S ≤ Subgroup.centralizer (u3X1 L1 L2 S : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hZXeq] at hx hy
      have hx' : x ∈ omegaOneCenterOf (Q1 L1 L2 S) := hx
      have hy' : y ∈ omegaOneCenterOf (Q1 L1 L2 S) := hy
      exact CFSG.Quasithin.A4.mul_comm_of_mem_omegaOneCenterOf hy' hx'
    have hcomm : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hX1C
    rw [hX1'] at hcomm
    exact hZ1ne hcomm
  have hZ1lt : Z1 L1 L2 S < u3X1 L1 L2 S := lt_of_le_of_ne hZX hZ1neX
  refine ⟨hX1norm, hZ1norm, hZ1lt, ?_⟩
  intro K hKnorm hZ1K hKX1
  have hKN : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (K ⊓ N) :=
    F112W.isNormalIn_inf hKnorm hstep.1
  have hLKN : L ≤ K ⊓ N := by
    rw [← hLeq]
    exact le_inf (inf_le_right.trans hZ1K) inf_le_left
  rcases hstep.2.2.2 (K ⊓ N) hKN hLKN (inf_le_right : K ⊓ N ≤ N) with hKN_eq | hKN_eq
  ·
    left
    have hKZ1 : K ≤ Z1 L1 L2 S := by
      intro k hk
      have hkX : k ∈ u3X1 L1 L2 S := hKX1 hk
      have hkNZ : k ∈ N ⊔ Z1 L1 L2 S := hXeq ▸ hkX
      obtain ⟨n, hn, z, hz, hnz⟩ :=
        CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommNZ hkNZ
      have hzK : z ∈ K := hZ1K hz
      have hnK : n ∈ K := by
        have hn_eq : n = k * z⁻¹ := by
          rw [← hnz]
          group
        rw [hn_eq]
        exact K.mul_mem hk (K.inv_mem hzK)
      have hnKN : n ∈ K ⊓ N := ⟨hnK, hn⟩
      rw [hKN_eq] at hnKN
      have hnZ : n ∈ Z1 L1 L2 S := by
        rw [← hLeq] at hnKN
        exact hnKN.2
      rw [← hnz]
      exact (Z1 L1 L2 S).mul_mem hnZ hz
    exact le_antisymm hKZ1 hZ1K
  ·
    right
    have hNK : N ≤ K := by
      rw [← hKN_eq]
      exact inf_le_left
    have hX1K : u3X1 L1 L2 S ≤ K := by
      rw [← hXeq]
      exact sup_le hNK hZ1K
    exact le_antisymm hKX1 hX1K

theorem str86X1K1_of_q1_eq {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hQ1 : Q1 L1 L2 S = u3X1 L1 L2 S)
    (hchief : IsChiefStep (L1 ⊔ S) (u3X1 L1 L2 S) (Z1 L1 L2 S) (u3X1 L1 L2 S))
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S) (hZ1ne : Z1 L1 L2 S ≠ ⊥) :
    Str86X1K1 L1 L2 S := by
  classical
  have hK1X : u3K1 L1 L2 S ≤ u3X1 L1 L2 S := by
    rw [← hQ1]
    exact u3K1_le_q1 L1 L2 S
  have hsup : u3X1 L1 L2 S ⊔ u3K1 L1 L2 S = u3X1 L1 L2 S :=
    sup_eq_left.mpr hK1X
  refine ⟨?_, ?_⟩
  · rw [hQ1, hsup]
  · have hP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    have hKnorm : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (u3K1 L1 L2 S) :=
      F112W.isNormalIn_of_le_normalizer hK1X (hP1.trans (u3K1_normal_in_P1 hF))
    have hZ1K : Z1 L1 L2 S ≤ u3K1 L1 L2 S :=
      u3Z1_le_u3K1 hF hSB h1 hB2 h2 hZI
    rcases hchief.2.2.2 (u3K1 L1 L2 S) hKnorm hZ1K hK1X with hK1 | hK1
    · rw [hK1, Subgroup.subgroupOf_self]
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact CFSG.Quasithin.A4.mul_comm_of_mem_omegaOneCenterOf y.2 x.2
    · exfalso
      apply hZ1ne
      have hK1C : u3K1 L1 L2 S ≤
          Subgroup.centralizer (u3X1 L1 L2 S : Set G) := inf_le_right
      have hX1C : u3X1 L1 L2 S ≤ Subgroup.centralizer (u3X1 L1 L2 S : Set G) := by
        rwa [hK1] at hK1C
      have hcomm : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hX1C
      rw [hX1'] at hcomm
      exact hcomm

end CFSG.Quasithin.Stroth

end

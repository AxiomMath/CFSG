module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qBound
public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qSpecial
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecSum

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

namespace U4qBase

private theorem Q1_le_L0 : X.Q 1 ≤ X.L 0 :=
  (X.Q_le_edgeSylow 0).trans (X.edgeSylow_le_L 0)

private theorem Qm1_le_L0 : X.Q (-1) ≤ X.L 0 := by
  refine (X.Q_le_edgeSylow_left (-1)).trans ?_
  exact le_oTwoPrime_of_isPGroup (X.isPGroup_edgeSylow (-1)) (fun x hx =>
    ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right) hx)

private theorem relCent_S_generates (B : X.U4qBase) :
    ∀ Y : Subgroup G, X.Z 0 ≤ Y → Y ≤ X.Q 0 →
      X.L 0 ≤ Subgroup.normalizer (Y : Set G) →
      relCent (X.Q 0) (X.Z 0) X.S ≤ Y → Y = X.Q 0 := by
  intro Y _ hYE hLY hrelY
  have hA : X.Q 0 ⊓ X.Q 1 ≤ Y := by
    rw [← B.relCent_S]
    exact hrelY
  obtain ⟨t, ht, htv, -⟩ := X.exists_reflection_oTwoRes B.gen.hyp 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have ht0 : t • X.vert 0 = X.vert 0 := by simpa using htv 0
  have ht1 : t • X.vert 1 = X.vert (-1) := by simpa using htv 1
  have hQ0 : X.Q 0 = conjSub t (X.Q 0) := Setup.Q_smul X X ht0
  have hQm1 : X.Q (-1) = conjSub t (X.Q 1) := Setup.Q_smul X X ht1
  have hconj : conjSub t (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q (-1) := by
    rw [conjSub_inf, ← hQ0, ← hQm1]
  have hBY : conjSub t Y = Y := mem_normalizer_iff_conjSub.mp (hLY htL)
  have hC : X.Q 0 ⊓ X.Q (-1) ≤ Y := by
    rw [← hconj]
    exact (conjSub_mono t hA).trans (le_of_eq hBY)
  refine le_antisymm hYE ?_
  rw [B.Q0_eq_sup]
  exact sup_le hA hC

private theorem exists_nat_mul_eq (B : X.U4qBase) : ∃ k : ℕ, X.n 1 = X.n 0 * k := by
  classical
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  have hQ : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hLQ : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
    refine (X.L_le_Gi 0).trans ?_
    simpa [Setup.Q] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
  have hLZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    rw [B.Z0_eq]
    exact le_normalizer_centerOf_self (X.L 0)
  have hcore : ∀ x ∈ pCoreOf 2 (X.L 0), ∀ e ∈ X.Q 0, ⁅x, e⁆ ∈ X.Z 0 := by
    intro x hx e he
    rw [hQ] at hx
    exact B.isElemSec_Q0.2.1 (Subgroup.commutator_mem_commutator hx he)
  have hT : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hquad : ∀ t ∈ X.S, ∀ t' ∈ X.S, ∀ e ∈ X.Q 0, ⁅t, ⁅t', e⁆⁆ ∈ X.Z 0 := by
    intro t ht t' ht' e he
    have hmem : ⁅t', e⁆ ∈ ⁅X.Q 0, X.S⁆ := by
      have h := Subgroup.commutator_mem_commutator he ht'
      rw [← commutatorElement_inv]
      exact (⁅X.Q 0, X.S⁆).inv_mem h
    have h1 : ⁅⁅t', e⁆, t⁆ ∈ X.Z 0 :=
      (Subgroup.commutator_le.mp B.quad) ⁅t', e⁆ hmem t ht
    rw [← commutatorElement_inv]
    exact (X.Z 0).inv_mem h1
  obtain ⟨k, hkE, -, -⟩ :=
    exists_relIndex_eq_two_pow_mul_of_quadratic (G := G) (L := X.L 0) (E := X.Q 0)
      (Z := X.Z 0) (T := X.S) (n := X.n 0)
      (by have := B.gen.hyp.two_le_n 0; omega) ((X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot)
      B.isElemSec_Q0 (le_inf hLQ hLZ) hcore B.relCent_L0 hT hquad
      (relCent_S_generates B)
  have hrel : (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 1) := by
    have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
    rw [inf_eq_left.mpr (X.Z_le_Q 0), B.card_Z0, B.card_Q0] at h
    have hpow : 2 ^ (X.n 0 + 2 * X.n 1) = 2 ^ (2 * X.n 1) * 2 ^ X.n 0 := by
      rw [pow_add, mul_comm]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) (X.n 0)) h
  have hmul : X.n 0 * k = X.n 1 := by
    have h2 : 2 * (X.n 0 * k) = 2 * X.n 1 := by
      calc 2 * (X.n 0 * k) = 2 * X.n 0 * k := by ring
        _ = 2 * X.n 1 := Nat.pow_right_injective (le_refl 2) (hkE.symm.trans hrel)
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  exact ⟨k, hmul.symm⟩

theorem n1_eq_two_mul (B : X.U4qBase) : X.n 1 = 2 * X.n 0 := by
  obtain ⟨k, hn1⟩ := exists_nat_mul_eq B
  have hk0 : k ≠ 0 := by
    intro hk
    have h0 : X.n 1 = 0 := by rw [hn1, hk, mul_zero]
    have := B.gen.hyp.two_le_n 1
    omega
  have hk1 : k ≠ 1 := by
    intro hk
    exact B.n1_ne_n0 (by rw [hn1, hk, mul_one])
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k
      · exact (hk0 rfl).elim
      · exact (hk1 rfl).elim
    · exact hge
  have hk_le : k ≤ 2 := by
    have hn0 : 0 < X.n 0 := by have := B.gen.hyp.two_le_n 0; omega
    have h' : X.n 0 * k ≤ X.n 0 * 2 := by
      calc X.n 0 * k = X.n 1 := hn1.symm
        _ ≤ 2 * X.n 0 := B.n1_le_two_mul
        _ = X.n 0 * 2 := by ring
    exact Nat.le_of_mul_le_mul_left h' hn0
  have hk : k = 2 := le_antisymm hk_le hk2
  calc X.n 1 = X.n 0 * k := hn1
    _ = X.n 0 * 2 := by rw [hk]
    _ = 2 * X.n 0 := by ring

theorem blockU_L0 (B : X.U4qBase) : CFSG.QuasithinUnique.blockU (X.L 0) = X.Q 0 := by
  have hQ : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  rw [CFSG.QuasithinUnique.blockU, CFSG.QuasithinUnique.blockQ, hQ]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_comm]
    refine Subgroup.le_normalizer_iff_commutator_le_right.mp ?_
    refine (X.L_le_Gi 0).trans ?_
    simpa [Setup.Q] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
  · have hZ : X.Z 0 ≤ ⁅X.Q 0, X.L 0⁆ := by
      rw [← B.commutator_Q0_eq]
      exact Subgroup.commutator_mono le_rfl (X.Q_le_L 0)
    have hA : X.Q 0 ⊓ X.Q 1 ≤ ⁅X.Q 0, X.L 0⁆ := by
      rw [← B.comm_Q1_sup]
      exact sup_le (Subgroup.commutator_mono le_rfl Q1_le_L0) hZ
    have hC : X.Q 0 ⊓ X.Q (-1) ≤ ⁅X.Q 0, X.L 0⁆ := by
      rw [← B.comm_Qm1_sup]
      exact sup_le (Subgroup.commutator_mono le_rfl Qm1_le_L0) hZ
    calc X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := B.Q0_eq_sup
      _ ≤ ⁅X.Q 0, X.L 0⁆ := sup_le hA hC

theorem blockZ_L0 (B : X.U4qBase) : CFSG.QuasithinUnique.blockZ (X.L 0) = X.Z 0 := by
  rw [CFSG.QuasithinUnique.blockZ, blockU_L0 B]
  refine le_antisymm ?_ ?_
  · intro x hx
    exact B.Z0_eq.symm ▸ Subgroup.mem_inf.mpr ⟨X.Q_le_L 0 hx.1, hx.2⟩
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨X.Z_le_Q 0 hx, ?_⟩
    exact (Subgroup.mem_inf.mp (B.Z0_eq.symm ▸ hx)).2

theorem not_quadratic_Q1 (B : X.U4qBase) :
    ∃ t ∈ X.S, ∃ t' ∈ X.S, ∃ u ∈ X.Q 1, ⁅t, ⁅t', u⁆⁆ ≠ 1 := by
  classical
  have hne : ⁅X.Q 0 ⊓ X.Q 1, X.Q 0⁆ ≠ ⊥ := B.commutator_inf_Q0_ne_bot
  have hnotall : ¬ ∀ a ∈ X.Q 0 ⊓ X.Q 1, ∀ b ∈ X.Q 0, ⁅a, b⁆ ∈ (⊥ : Subgroup G) := by
    intro hall
    apply hne
    rw [← le_bot_iff, Subgroup.commutator_le]
    exact hall
  push Not at hnotall
  obtain ⟨a, ha, b, hb, hab⟩ := hnotall
  have hab1 : ⁅a, b⁆ ≠ 1 := fun h1 => hab (Subgroup.mem_bot.mpr h1)
  have haC : a ∉ Subgroup.centralizer ({b} : Set G) := by
    intro haC
    have hcomm : b * a = a * b := Subgroup.mem_centralizer_iff.mp haC b (by simp)
    exact hab1 (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm)
  have hZ0C : X.Z 0 ≤ Subgroup.centralizer ({b} : Set G) := by
    intro z hz
    have hz' : z ∈ centerOf (X.L 0) := B.Z0_eq ▸ hz
    have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hz').2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyb : y = b := by simpa using hy
    rw [hyb]
    exact Subgroup.mem_centralizer_iff.mp hzC b (X.Q_le_L 0 hb)
  have hnotQ : ¬ ⁅X.Q 0, X.Q 1⁆ ≤ Subgroup.centralizer ({b} : Set G) := by
    intro hle
    apply haC
    have hle' : ⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0 ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le hle hZ0C
    have ha' : a ∈ ⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0 := by
      rw [B.comm_Q1_sup]
      exact ha
    exact hle' ha'
  have hnotall2 : ¬ ∀ x ∈ X.Q 0, ∀ y ∈ X.Q 1,
      ⁅x, y⁆ ∈ Subgroup.centralizer ({b} : Set G) := by
    intro hall
    exact hnotQ (Subgroup.commutator_le.mpr hall)
  push Not at hnotall2
  obtain ⟨x, hx, y, hy, hxy⟩ := hnotall2
  refine ⟨b, ?_, x, ?_, y, hy, ?_⟩
  · simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow_left 0 hb
  · simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow_left 0 hx
  · intro h1
    apply hxy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzb : z = b := by simpa using hz
    rw [hzb]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem u4qLocalData_of_types (B : X.U4qBase)
    (h0 : CFSG.Quasithin.F112R.St84.IsTwoNatType (X.L 0) (X.n 0))
    (h1 : CFSG.Quasithin.IsOmega4MinusType (X.L 1) (X.n 0)) :
    CFSG.Quasithin.F112R.St84.U4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) := by
  have hn : X.n 1 = 2 * X.n 0 := n1_eq_two_mul B
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  refine {
    card_S := ?_
    special_left := B.isSpecialPow_Q0 hn
    center_left := B.L0_le_centralizer
    twoNat_left := h0
    card_right := ?_
    omega_right := h1
    card_inf := ?_ }
  · left
    rw [B.card_S]
    congr 1
    omega
  · rw [hQ1, B.card_Q1]
    congr 1
    omega
  · rw [hQ0, hQ1, B.card_Q0_inf_Q1]
    congr 1
    omega

end U4qBase

end Setup

end CFSG.Quasithin.St84

end

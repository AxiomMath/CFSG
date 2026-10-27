module

import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C1GNBlocks

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Setting (H T M V Y : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  min : MinParabolic H T M
  charTwo : CharTwo H
  sqtk : IsSQTKTC H
  red : IsTwoReducedIn H V
  hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  hVZ : V = VZ T H
  Y_le : Y ≤ H
  Y_res : twoResidual Y = Y
  Y_C : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H
  Y_card : Nat.card (autI hV Y) = 3
  Q_norm : pCoreOf 2 H ≤ Subgroup.normalizer (Y : Set G)
  S_norm : baum T ≤ Subgroup.normalizer (Y : Set G)
  gen : Y ⊔ T = H

theorem charTwo_of_pCore_le {X U : Subgroup G} (hF : CharTwo X) (hQU : pCoreOf 2 X ≤ U)
    (hUX : U ≤ X) : CharTwo U := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hF hUX hQU

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hB
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem twoResidual_mono {A B : Subgroup G} (h : A ≤ B) : twoResidual A ≤ twoResidual B := by
  have hBn : A ≤ Subgroup.normalizer (twoResidual B : Set G) :=
    h.trans (le_normalizer_twoResidual B)
  have hn : A ≤ Subgroup.normalizer ((A ⊓ twoResidual B : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hBn hg⟩
  have h2 : ∀ y ∈ A, ∃ k : ℕ, y ^ 2 ^ k ∈ A ⊓ twoResidual B := fun y hy => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient B y (h hy)
    exact ⟨k, A.pow_mem hy _, hk⟩
  exact (twoResidual_le_of_isTwoQuotient inf_le_left hn h2).trans inf_le_right

@[expose] def R₁ (H T : Subgroup G) : Subgroup G := pCoreOf 2 H ⊔ baum T

namespace Setting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setting H T M V Y hV)

include s

theorem hT : IsSylowTwoOf T H := s.min.isSylow

theorem H_le_N : H ≤ Subgroup.normalizer (V : Set G) := s.red.2.1

theorem not_H_le_C : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
  s.hJ ((thompsonJ_le T).trans (s.hT.1.trans h))

theorem Q_le_T : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf s.hT

theorem Q_le_C : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
  MinParabolic.pCoreOf_le_centralizer s.red

theorem T_inf_C : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H :=
  s.min.inf_centralizer_eq_pCoreOf s.red s.not_H_le_C

theorem S_le_T : baum T ≤ T := inf_le_left

theorem R_le_T : R₁ H T ≤ T := sup_le s.Q_le_T s.S_le_T

theorem R_pGroup : IsPGroup 2 (R₁ H T) := s.hT.2.1.to_le s.R_le_T

theorem Q_le_R : pCoreOf 2 H ≤ R₁ H T := le_sup_left

theorem S_le_R : baum T ≤ R₁ H T := le_sup_right

theorem thompsonJ_R : thompsonJ (R₁ H T) = thompsonJ T :=
  B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum T).trans s.S_le_R) s.R_le_T

theorem baum_R : baum (R₁ H T) = baum T := by
  ext x
  unfold baum
  rw [s.thompsonJ_R]
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨s.R_le_T h.1, h.2⟩, fun h => ⟨s.S_le_R (by
    simpa [baum] using h), h.2⟩⟩

theorem Y_inf_T : Y ⊓ T ≤ pCoreOf 2 H := by
  intro t ht
  have htN : t ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (s.Y_le ht.1)
  set φ := convI hV ⟨t, htN⟩ with hφ
  have h3 : orderOf φ ∣ 3 := by
    have hmem : φ ∈ autI hV Y := convI_mem_autI hV ht.1 htN
    have := Subgroup.orderOf_dvd_natCard (autI hV Y) hmem
    rwa [s.Y_card] at this
  obtain ⟨k, hk⟩ := s.hT.2.1 ⟨t, ht.2⟩
  have ht1 : t ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hpow : φ ^ (2 ^ k) = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨t, htN⟩ : Subgroup.normalizer (V : Set G)) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using ht1)
    rw [this, map_one]
  have h2 : orderOf φ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf φ = 1 := by
    have := Nat.dvd_gcd h3 h2
    have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hg] at this
    exact Nat.dvd_one.1 this
  have hφ1 : φ = 1 := orderOf_eq_one_iff.1 h1
  have hc : t ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV ⟨t, htN⟩).1 hφ1
  rw [← s.T_inf_C]
  exact ⟨ht.2, hc⟩

theorem Y_inf_R : Y ⊓ R₁ H T = Y ⊓ pCoreOf 2 H :=
  le_antisymm (le_inf inf_le_left ((inf_le_inf_left Y s.R_le_T).trans s.Y_inf_T))
    (inf_le_inf_left Y s.Q_le_R)

theorem Y_inf_C : Y ⊓ Subgroup.centralizer (V : Set G) = Y ⊓ pCoreOf 2 H :=
  le_antisymm (le_inf inf_le_left (s.Y_C))
    (inf_le_inf_left Y s.Q_le_C)

theorem relIndex_Y : (Y ⊓ pCoreOf 2 H).relIndex Y = 3 := by
  have h1 := card_autI_mul_card_inf hV (A := Y) (s.Y_le.trans s.H_le_N)
  rw [s.Y_card, s.Y_inf_C] at h1
  have h2 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y)] at h2
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 H) := Nat.card_pos
  have : (Y ⊓ pCoreOf 2 H).relIndex Y * Nat.card ↥(Y ⊓ pCoreOf 2 H) =
      3 * Nat.card ↥(Y ⊓ pCoreOf 2 H) := by rw [h2, ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem sandwich_Y {K : Subgroup G} (h1 : Y ⊓ pCoreOf 2 H ≤ K) (h2 : K ≤ Y) :
    K = Y ⊓ pCoreOf 2 H ∨ K = Y := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [s.relIndex_Y] at h
  have hdvd : (K.relIndex Y) ∣ 3 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3'
  · right
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.1 h1')
  · left
    rw [h3'] at h
    have : (Y ⊓ pCoreOf 2 H).relIndex K = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) h1

theorem exists_order_three : ∃ x ∈ Y, orderOf x = 3 := by
  have hdvd : 3 ∣ Nat.card Y := by
    have h2 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
    rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y), s.relIndex_Y] at h2
    exact Dvd.intro _ h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Setting

end CFSG.Quasithin.C126.A5

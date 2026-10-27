module


import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
import CFSG.Quasithin.Recognition.St84.Gen.Sec6Cover
import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qStep10
public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.Quasithin.Recognition.St84.Sec7Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem s46a5h_Gi_le_normalizer (X : Setup Γ G) :
    X.Gi 0 ≤ Subgroup.normalizer ((⁅X.Q 0, oTwoRes (X.L 0)⁆ : Subgroup G) : Set G) := by
  intro g hg
  have hQ : g ∈ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hg
  have hL : conjSub g (X.L 0) = X.L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_oTwoPrime (X.Gi 0) hg)
  have hR : g ∈ Subgroup.normalizer (oTwoRes (X.L 0) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := conjSub_oTwoRes g (X.L 0)
    rw [hL] at h
    exact h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hQ, Subgroup.mem_normalizer_iff_map_conj_eq.mp hR]

theorem caseA_indec_Q0 (X : Setup Γ G) (hn : 1 ≤ X.n 0)
    (hA1 : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1)
    (hDK : ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Ki 0⁆ =
      X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G))
    (hD : ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Q 1⁆ = X.Z 1)
    (h5d : X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G))) :
    ⁅X.Q 0, oTwoRes (X.L 0)⁆ = X.Q 0 := by
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  set M := ⁅X.Q 0, oTwoRes (X.L 0)⁆ with hM
  have hN := s46a5h_Gi_le_normalizer X
  have hMQ : M ≤ X.Q 0 := by
    rw [hM, Subgroup.commutator_le]
    intro q hq l hl
    have h1 : l * q⁻¹ * l⁻¹ ∈ X.Q 0 :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
        (X.L_le_Gi 0 (oTwoRes_le _ hl))) q⁻¹).mp (inv_mem hq)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hq (by rw [← mul_assoc]; exact h1)
  have hDQ : D ≤ X.Q 0 := by
    have h : D ≤ X.Q 0 ⊓ X.Q 2 := hA1 ▸ le_sup_left
    exact h.trans inf_le_left
  have hDM : D ≤ M := by
    rw [← hDK]
    exact Subgroup.commutator_mono hDQ
      (le_oTwoRes_of_odd_card inf_le_right (X.odd_card_Ki 0 hn))
  have hZM : X.Z 1 ≤ M := by
    rw [← hD, Subgroup.commutator_le]
    intro d hd x hx
    have hxG : x ∈ X.Gi 0 := ((X.Q_le_Gi_adj 1).trans inf_le_left) hx
    have h1 : x * d⁻¹ * x⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hN hxG) d⁻¹).mp (inv_mem (hDM hd))
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem (hDM hd) (by rw [← mul_assoc]; exact h1)
  have hVM : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ M := by
    refine iSup₂_le fun g hg x hx => ?_
    have h := (Subgroup.mem_normalizer_iff.mp (hN hg) (g⁻¹ * x * g)).mp
      (hZM (mem_conjSub.mp hx))
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h
  refine le_antisymm hMQ ?_
  rw [h5d]
  exact sup_le hVM hDM

theorem caseA_perfect_L0 (X : Setup Γ G) (hn : 2 ≤ X.n 0)
    (hindec : ⁅X.Q 0, oTwoRes (X.L 0)⁆ = X.Q 0) : ⁅X.L 0, X.L 0⁆ = X.L 0 := by
  have hLQ : X.L 0 = ⁅X.L 0, X.L 0⁆ ⊔ X.Q 0 :=
    X.L_eq_commutator_sup_Q 0 hn (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hQ : X.Q 0 ≤ ⁅X.L 0, X.L 0⁆ := by
    rw [← hindec]
    exact Subgroup.commutator_mono (X.Q_le_L 0) (oTwoRes_le _)
  have hL : X.L 0 = ⁅X.L 0, X.L 0⁆ := by
    conv_lhs => rw [hLQ]
    rw [sup_eq_left.mpr hQ]
  exact hL.symm

theorem caseA_gen_Q0 (X : Setup Γ G) (hn : 1 ≤ X.n 0) (hsec : IsElemSec (X.Z 0) (X.Q 0))
    (hZ : X.Z 0 ≤ X.Z 1)
    (hA1 : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1)
    (hcardD : Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 2 ^ X.n 0)
    (h5d : X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)))
    (hindec : ⁅X.Q 0, oTwoRes (X.L 0)⁆ = X.Q 0) :
    ∀ N : Subgroup G, X.Z 1 ≤ N → N ≤ X.Q 0 → X.L 0 ≤ Subgroup.normalizer (N : Set G) →
      N = X.Q 0 := by
  intro N hZN hNQ hLN
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  haveI : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNQ)
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDQ : D ≤ X.Q 0 := by
    have h : D ≤ X.Q 0 ⊓ X.Q 2 := hA1 ▸ le_sup_left
    exact h.trans inf_le_left
  haveI : Finite ↥(D ⊓ N) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hNQ))
  have hKN : X.K ≤ Subgroup.normalizer (X.L 0 : Set G) :=
    (X.K_le_Gi 0).trans (le_normalizer_oTwoPrime (X.Gi 0))
  have hset : ((X.L 0 ⊔ X.K : Subgroup G) : Set G) = (X.L 0 : Set G) * (X.K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (X.L 0) X.K hKN
  have hVN : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ N := by
    refine iSup₂_le fun g hg x hx => ?_
    have hg' : g ∈ (X.L 0 : Set G) * (X.K : Set G) := by
      rw [← hset, ← X.Gi_eq_L_sup_K 0]
      exact hg
    obtain ⟨l, hl, k, hk, rfl⟩ := Set.mem_mul.mp hg'
    have hkZ : k ∈ Subgroup.normalizer (X.Z 1 : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 k (X.K_le_Gi 1 hk))
    have h1 := (Subgroup.mem_normalizer_iff.mp hkZ _).mp (mem_conjSub.mp hx)
    have e1 : k * ((l * k)⁻¹ * x * (l * k)) * k⁻¹ = l⁻¹ * x * l := by group
    rw [e1] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp (hLN hl) (l⁻¹ * x * l)).mp (hZN h1)
    have e2 : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
    rwa [e2] at h2
  have hDNQ : D ⊔ N = X.Q 0 := by
    refine le_antisymm (sup_le hDQ hNQ) ?_
    rw [sup_comm]
    conv_lhs => rw [h5d]
    exact sup_le_sup_right hVN D
  have hcard := card_sup_mul_card_inf_of_le_finite (P := X.Q 0) hDQ hNQ
    (hDQ.trans ((X.Q_le_L 0).trans hLN))
  rw [hDNQ] at hcard
  have hrel := Subgroup.relIndex_mul_card (H := N) (K := X.Q 0)
  rw [inf_eq_left.mpr hNQ] at hrel
  have hidx : N.relIndex (X.Q 0) * Nat.card ↥(D ⊓ N) = 2 ^ X.n 0 := by
    rw [← hcardD]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥N)) ?_
    rw [← hcard, ← hrel]
    ring
  have hpos : 0 < Nat.card ↥(D ⊓ N) := Nat.card_pos
  have hle : N.relIndex (X.Q 0) ≤ 2 ^ X.n 0 := by
    rw [← hidx]
    exact Nat.le_mul_of_pos_right _ hpos
  have h0 : N.relIndex (X.Q 0) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hidx
    exact absurd hidx.symm (by positivity)
  have hlt : N.relIndex (X.Q 0) < 2 ^ (2 * X.n 0) :=
    hle.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hcore : ⁅X.Q 0, pCoreOf 2 (X.L 0)⁆ ≤ N := by
    rw [(X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq]
    exact hsec.2.1.trans (hZ.trans hZN)
  have hcomm := comm_le_of_relIndex_lt_two_pow (L := X.L 0) (E := X.Q 0) (N := N) hn
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot hNQ ((X.Q_le_L 0).trans hLN)
    (fun g hg => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (X.L_le_Gi 0 hg))
    hLN (pCoreOf_isPGroup' (X.Gi 0)) hcore h0 hlt
  refine le_antisymm hNQ ?_
  rw [← hindec]
  exact (Subgroup.commutator_mono le_rfl (oTwoRes_le _)).trans hcomm

end Setup

end CFSG.Quasithin.St84

end

module

public import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.Assembly.LowTwoRankDefs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.C5 CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem L3qLocalData.one_le (hD : L3qLocalData L1 L2 S f) : 1 ≤ f := by
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hD.lin_left
  letI := hField
  letI := hFintype
  have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hFcard
  omega

private theorem L3qLocalData.twoPart_left (hD : L3qLocalData L1 L2 S f) :
    twoPart L1 = 2 ^ (3 * f) := by
  have h := twoPart_of_isLin2Type (k := 2 * f) hD.lin_left hD.card_left
  rwa [show 2 * f + f = 3 * f by omega] at h

theorem L3qLocalData.le_left (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    S ≤ L1 := by
  refine hH.le_left_of_twoPart ?_
  rw [hD.twoPart_left, hD.card_S]

theorem L3qLocalData.pCoreOf_ne (hD : L3qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ≠ pCoreOf 2 L2 := by
  intro heq
  have hinf : pCoreOf 2 L1 ⊓ pCoreOf 2 L2 = pCoreOf 2 L1 := by rw [heq, inf_idem]
  have hEq : 2 ^ (2 * f) = 2 ^ f := by
    have h := hD.card_inf
    rwa [hinf, hD.card_left] at h
  have hf : 1 ≤ f := hD.one_le
  have hlt : 2 ^ f < 2 ^ (2 * f) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact (ne_of_lt hlt) hEq.symm

theorem L3qLocalData.blockU_left (hD : L3qLocalData L1 L2 S f) :
    blockU L1 = pCoreOf 2 L1 := by
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, β, hβsurj, hβker, hβact⟩ :=
    hD.lin_left
  letI := hField
  letI := hFintype
  have hle : blockU L1 ≤ pCoreOf 2 L1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L1)
  have hcardrange : Nat.card β.range = 2 ^ (2 * f) := by
    rw [MonoidHom.range_eq_top.mpr hβsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_eq_fintype_card, hFcard, ← pow_mul, Nat.mul_comm]
  have hcardU : Nat.card (blockU L1) = Nat.card β.ker * Nat.card β.range :=
    (Subgroup.card_ker_mul_card_range β).symm
  have hcardle : Nat.card (blockU L1) ≤ 2 ^ (2 * f) := by
    calc
      Nat.card (blockU L1) ≤ Nat.card (pCoreOf 2 L1) := Subgroup.card_le_of_le hle
      _ = 2 ^ (2 * f) := hD.card_left
  have hker_one : Nat.card β.ker = 1 := by
    have hmul : Nat.card β.ker * Nat.card β.range ≤ 1 * 2 ^ (2 * f) := by
      rw [← hcardU, one_mul]
      exact hcardle
    rw [hcardrange] at hmul
    have hle1 : Nat.card β.ker ≤ 1 :=
      Nat.le_of_mul_le_mul_right hmul (by positivity : 0 < 2 ^ (2 * f))
    have hpos : 1 ≤ Nat.card β.ker := Nat.succ_le_of_lt Nat.card_pos
    omega
  have hcardU' : Nat.card (blockU L1) = 2 ^ (2 * f) := by
    rw [hcardU, hker_one, one_mul, hcardrange]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardU', hD.card_left])

theorem L3qLocalData.blockZ_left (hD : L3qLocalData L1 L2 S f) : blockZ L1 = ⊥ := by
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, β, hβsurj, hβker, hβact⟩ :=
    hD.lin_left
  letI := hField
  letI := hFintype
  have hle : blockU L1 ≤ pCoreOf 2 L1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L1)
  have hcardrange : Nat.card β.range = 2 ^ (2 * f) := by
    rw [MonoidHom.range_eq_top.mpr hβsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_eq_fintype_card, hFcard, ← pow_mul, Nat.mul_comm]
  have hcardU : Nat.card (blockU L1) = Nat.card β.ker * Nat.card β.range :=
    (Subgroup.card_ker_mul_card_range β).symm
  have hcardle : Nat.card (blockU L1) ≤ 2 ^ (2 * f) := by
    calc
      Nat.card (blockU L1) ≤ Nat.card (pCoreOf 2 L1) := Subgroup.card_le_of_le hle
      _ = 2 ^ (2 * f) := hD.card_left
  have hker_one : Nat.card β.ker = 1 := by
    have hmul : Nat.card β.ker * Nat.card β.range ≤ 1 * 2 ^ (2 * f) := by
      rw [← hcardU, one_mul]
      exact hcardle
    rw [hcardrange] at hmul
    have hle1 : Nat.card β.ker ≤ 1 :=
      Nat.le_of_mul_le_mul_right hmul (by positivity : 0 < 2 ^ (2 * f))
    have hpos : 1 ≤ Nat.card β.ker := Nat.succ_le_of_lt Nat.card_pos
    omega
  have hsub : (blockZ L1).subgroupOf (blockU L1) = ⊥ := by
    rw [← hβker]
    exact Subgroup.card_eq_one.mp hker_one
  have hcardZ : Nat.card ((blockZ L1).subgroupOf (blockU L1)) = Nat.card (blockZ L1) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L1 ≤ blockU L1)).toEquiv
  exact Subgroup.card_eq_one.mp (by rw [← hcardZ, hsub, Subgroup.card_bot])

theorem L3qLocalData.isElemAbelian_left (hD : L3qLocalData L1 L2 S f) :
    IsElemAbelian 2 (pCoreOf 2 L1) := by
  rw [← hD.blockU_left]
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, β, hβsurj, hβker, hβact⟩ :=
    hD.lin_left
  letI := hField
  letI := hFintype
  have hker : β.ker = ⊥ := by
    rw [hβker, hD.blockZ_left]
    simp
  have hβinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hker
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hcomm : ∀ a b : ↥(blockU L1), a * b = b * a := by
    intro a b
    exact hβinj (by rw [map_mul, map_mul, mul_comm])
  have hsq : ∀ a : ↥(blockU L1), a ^ 2 = 1 := by
    intro a
    apply hβinj
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    simpa using CharTwo.two_nsmul (Multiplicative.toAdd (β a))
  refine ⟨IsMulCommutative.of_comm hcomm, ?_⟩
  intro x hx
  simpa using congrArg Subtype.val (hsq ⟨x, hx⟩)

theorem L3qLocalData.sup_bigB_left (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    L1 ⊔ bigB L1 L2 S = L1 ⊔ borelOf L2 S :=
  sup_bigB_left_of_le (hD.le_left hH)

theorem L3qLocalData.isSylowTwoOf_sup_bigB_left (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) :=
  isSylowTwoOf_sup_bigB_left_of_le hH (hD.le_left hH)
    (L3qLocalData.le_left hH.symm hD.symm)

theorem L3qLocalData.isLinSemidirect_left (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) {F : Type*} [Field F]
    {Γ : Subgroup (GL (Fin 2) F)}
    (hact : LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ) :
    IsLinSemidirect (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ := by
  have hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2) := by
    rw [hD.card_S, hD.card_inf, hD.card_left, hD.card_right, ← pow_add, ← pow_add]
    congr 1
    omega
  exact isLinSemidirect_left_of_le hH (hD.le_left hH)
    (L3qLocalData.le_left hH.symm hD.symm)
    hD.isElemAbelian_left (L3qLocalData.isElemAbelian_left hD.symm) hcard hact

theorem L3qLocalData.le_right (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    S ≤ L2 :=
  L3qLocalData.le_left hH.symm hD.symm

theorem L3qLocalData.blockU_right (hD : L3qLocalData L1 L2 S f) :
    blockU L2 = pCoreOf 2 L2 :=
  L3qLocalData.blockU_left hD.symm

theorem L3qLocalData.blockZ_right (hD : L3qLocalData L1 L2 S f) : blockZ L2 = ⊥ :=
  L3qLocalData.blockZ_left hD.symm

theorem L3qLocalData.isElemAbelian_right (hD : L3qLocalData L1 L2 S f) :
    IsElemAbelian 2 (pCoreOf 2 L2) :=
  L3qLocalData.isElemAbelian_left hD.symm

theorem L3qLocalData.isSylowTwoOf_sup_bigB_right (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) :=
  isSylowTwoOf_sup_bigB_right_of_le hH (hD.le_left hH) (hD.le_right hH)

theorem L3qLocalData.isLinSemidirect_right (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) {F : Type*} [Field F]
    {Γ : Subgroup (GL (Fin 2) F)}
    (hact : LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ) :
    IsLinSemidirect (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ := by
  have hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2) := by
    rw [hD.card_S, hD.card_inf, hD.card_left, hD.card_right, ← pow_add, ← pow_add]
    congr 1
    omega
  exact isLinSemidirect_right_of_le hH (hD.le_left hH) (hD.le_right hH)
    hD.isElemAbelian_left hD.isElemAbelian_right hcard hact

end CFSG.Quasithin.F112R.St84

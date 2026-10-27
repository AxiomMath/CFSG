module

public import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem Sp4qLocalData.one_le (hD : Sp4qLocalData L1 L2 S f) : 1 ≤ f := by
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hD.lin_left
  letI := hField
  letI := hFintype
  have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hFcard
  omega

theorem Sp4qLocalData.le_left (hH : Hyp111 L1 L2 S) (hD : Sp4qLocalData L1 L2 S f) :
    S ≤ L1 := by
  refine hH.le_left_of_twoPart ?_
  have h := twoPart_of_isLin2Type (k := 3 * f) hD.lin_left hD.card_left
  rw [show 3 * f + f = 4 * f by omega] at h
  rw [h, hD.card_S]

theorem Sp4qLocalData.le_right (hH : Hyp111 L1 L2 S) (hD : Sp4qLocalData L1 L2 S f) :
    S ≤ L2 :=
  hD.symm.le_left hH.symm

theorem Sp4qLocalData.isSylowTwoOf_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : IsSylowTwoOf S L1 := by
  have h := twoPart_of_isLin2Type (k := 3 * f) hD.lin_left hD.card_left
  rw [show 3 * f + f = 4 * f by omega] at h
  exact isSylowTwoOf_of_card_eq (hD.le_left hH) hH.h1.pgroup (by rw [hD.card_S, h])

theorem Sp4qLocalData.isSylowTwoOf_right (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : IsSylowTwoOf S L2 :=
  hD.symm.isSylowTwoOf_left hH.symm

theorem Sp4qLocalData.blockU_left (hD : Sp4qLocalData L1 L2 S f) :
    blockU L1 = pCoreOf 2 L1 := by
  simpa [blockU, blockQ] using hD.indec_left

theorem Sp4qLocalData.blockU_right (hD : Sp4qLocalData L1 L2 S f) :
    blockU L2 = pCoreOf 2 L2 :=
  hD.symm.blockU_left

theorem Sp4qLocalData.card_blockZ_left (hD : Sp4qLocalData L1 L2 S f) :
    Nat.card (blockZ L1) = 2 ^ f := by
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, β, hβsurj, hβker, hβact⟩ :=
    hD.lin_left
  letI := hField
  letI := hFintype
  have hcardrange : Nat.card β.range = 2 ^ (2 * f) := by
    rw [MonoidHom.range_eq_top.mpr hβsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_eq_fintype_card, hFcard, ← pow_mul, Nat.mul_comm]
  have hkerZ : Nat.card β.ker = Nat.card (blockZ L1) := by
    rw [hβker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L1 ≤ blockU L1)).toEquiv
  have hcardU : Nat.card (blockU L1) = Nat.card β.ker * Nat.card β.range :=
    (Subgroup.card_ker_mul_card_range β).symm
  have hcardU' : Nat.card (blockU L1) = Nat.card (blockZ L1) * 2 ^ (2 * f) := by
    rw [hcardU, hkerZ, hcardrange]
  have h : 2 ^ (3 * f) = Nat.card (blockZ L1) * 2 ^ (2 * f) := by
    rw [← hD.card_left, ← hD.blockU_left]
    exact hcardU'
  have h3 : 2 ^ (3 * f) = 2 ^ f * 2 ^ (2 * f) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h3] at h
  exact (Nat.mul_right_cancel (by positivity : 0 < 2 ^ (2 * f)) h).symm

theorem Sp4qLocalData.card_blockZ_right (hD : Sp4qLocalData L1 L2 S f) :
    Nat.card (blockZ L2) = 2 ^ f :=
  hD.symm.card_blockZ_left

theorem Sp4qLocalData.pCoreOf_ne (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ≠ pCoreOf 2 L2 := by
  intro heq
  have hinf : pCoreOf 2 L1 ⊓ pCoreOf 2 L2 = pCoreOf 2 L1 := by rw [heq, inf_idem]
  have hEq : 2 ^ (3 * f) = 2 ^ (2 * f) := by
    have h := hD.card_inf
    rwa [hinf, hD.card_left] at h
  have hf := hD.one_le
  have hlt : 2 ^ (2 * f) < 2 ^ (3 * f) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact (ne_of_lt hlt) hEq.symm

theorem Sp4qLocalData.sup_pCoreOf (hH : Hyp111 L1 L2 S) (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ⊔ pCoreOf 2 L2 = S := by
  have hS1 : S ≤ L1 := hD.le_left hH
  have hN : pCoreOf 2 L2 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (hH.pCoreOf_le_right.trans hS1).trans (le_normalizer_pCoreOf 2 L1)
  have h := card_sup_mul_card_inf_of_le_normalizer (A := pCoreOf 2 L2)
    (B := pCoreOf 2 L1) hN
  rw [inf_comm (pCoreOf 2 L2) (pCoreOf 2 L1), hD.card_inf, hD.card_right, hD.card_left] at h
  have h6 : 2 ^ (3 * f) * 2 ^ (3 * f) = 2 ^ (4 * f) * 2 ^ (2 * f) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [h6] at h
  have hcard : Nat.card ↥(pCoreOf 2 L1 ⊔ pCoreOf 2 L2) = 2 ^ (4 * f) := by
    rw [sup_comm (pCoreOf 2 L2) (pCoreOf 2 L1)] at h
    exact Nat.mul_right_cancel (by positivity : 0 < 2 ^ (2 * f)) h
  refine Subgroup.eq_of_le_of_card_ge (sup_le hH.pCoreOf_le_left hH.pCoreOf_le_right) ?_
  rw [hcard, hD.card_S]

theorem Sp4qLocalData.inf_le_centralizer (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ≤ Subgroup.centralizer (S : Set G) :=
  inf_le_centralizer_of_sup_eq (hD.sup_pCoreOf hH) hD.elem_left hD.elem_right

theorem Sp4qLocalData.inf_centralizer_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ⊓ Subgroup.centralizer (S : Set G) = pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
  refine le_antisymm ?_ (le_inf inf_le_left (hD.inf_le_centralizer hH))
  intro x hx
  exact ⟨hx.1, pCoreOf_inf_centralizer_le_right hH (hD.le_right hH) hx⟩

theorem Sp4qLocalData.inf_centralizer_right (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L2 ⊓ Subgroup.centralizer (S : Set G) = pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
  refine le_antisymm ?_ (le_inf inf_le_right (hD.inf_le_centralizer hH))
  intro x hx
  exact ⟨pCoreOf_inf_centralizer_le_left hH (hD.le_left hH) hx, hx.1⟩

theorem Sp4qLocalData.card_inf_centralizer_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    Nat.card ↥(pCoreOf 2 L1 ⊓ Subgroup.centralizer (S : Set G)) = 2 ^ (2 * f) := by
  rw [hD.inf_centralizer_left hH, hD.card_inf]

theorem Sp4qLocalData.card_inf_centralizer_right (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    Nat.card ↥(pCoreOf 2 L2 ⊓ Subgroup.centralizer (S : Set G)) = 2 ^ (2 * f) := by
  rw [hD.inf_centralizer_right hH, hD.card_inf]

theorem Sp4qLocalData.blockZ_left_le (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : blockZ L1 ≤ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
  intro z hz
  have hzQ1 : z ∈ pCoreOf 2 L1 := by
    have hzU : z ∈ blockU L1 := hz.1
    rwa [hD.blockU_left] at hzU
  have hzC : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le (fun s hs => hD.le_left hH hs) hz.2
  rw [← hD.inf_centralizer_left hH]
  exact ⟨hzQ1, hzC⟩

theorem Sp4qLocalData.blockZ_right_le (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : blockZ L2 ≤ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
  have h := hD.symm.blockZ_left_le hH.symm
  rwa [inf_comm (pCoreOf 2 L2) (pCoreOf 2 L1)] at h

theorem Sp4qLocalData.hyp111R (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : Hyp111R L1 L2 S :=
  hyp111R_of_isLin2Type hf hf hH hD.lin_left hD.lin_right

theorem Sp4qLocalData.blockZ_inf_blockZ (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : blockZ L1 ⊓ blockZ L2 = ⊥ :=
  (hD.hyp111R hf hH).blockZ_inf_blockZ

theorem Sp4qLocalData.isSylowTwoOf_sup_bigB_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) :=
  isSylowTwoOf_sup_bigB_left_of_le hH (hD.le_left hH) (hD.le_right hH)

theorem Sp4qLocalData.isSylowTwoOf_sup_bigB_right (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) :=
  isSylowTwoOf_sup_bigB_right_of_le hH (hD.le_left hH) (hD.le_right hH)

theorem Sp4qLocalData.isLinSemidirect_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) {F : Type*} [Field F]
    {Γ : Subgroup (GL (Fin 3) F)}
    (hact : LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ) :
    IsLinSemidirect (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) Γ := by
  have hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2) := by
    rw [hD.card_S, hD.card_inf, hD.card_left, hD.card_right, ← pow_add, ← pow_add]
    congr 1
    omega
  exact isLinSemidirect_left_of_le hH (hD.le_left hH) (hD.le_right hH)
    hD.elem_left hD.elem_right hcard hact

theorem Sp4qLocalData.isLinSemidirect_right (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) {F : Type*} [Field F]
    {Γ : Subgroup (GL (Fin 3) F)}
    (hact : LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ) :
    IsLinSemidirect (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) Γ := by
  have hcard : Nat.card S * Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card (pCoreOf 2 L1) * Nat.card (pCoreOf 2 L2) := by
    rw [hD.card_S, hD.card_inf, hD.card_left, hD.card_right, ← pow_add, ← pow_add]
    congr 1
    omega
  exact isLinSemidirect_right_of_le hH (hD.le_left hH) (hD.le_right hH)
    hD.elem_left hD.elem_right hcard hact

end CFSG.Quasithin.F112R.St84

end

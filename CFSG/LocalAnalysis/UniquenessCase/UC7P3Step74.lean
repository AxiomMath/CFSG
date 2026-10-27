module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.LieType.BorelTits.Basic
import CFSG.SignalizerFunctorTheorem.Inheritance.Pullback

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

theorem card_pCoreOf_inf_le_two {M H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hodd : Odd (Nat.card ↥(CFSG.pPrimeCore p ↥H)))
    (h1 : Nat.card ↥(CFSG.pPrimeCore p
      ↥(((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))) ≤ 2) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ H) ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  let R : Subgroup G := Q ⊓ H
  let K : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  haveI : K.Normal := CFSG.pPrimeCore_normal
  let q : ↥H →* ↥H ⧸ K := QuotientGroup.mk' K
  let B : Subgroup ↥H := (H ⊓ M).subgroupOf H
  let A : Subgroup ↥H := R.subgroupOf H
  let Nbar : Subgroup (↥H ⧸ K) := B.map q
  let Rbar : Subgroup (↥H ⧸ K) := A.map q
  have hRleM : R ≤ M := by
    intro x hx
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 M hx.1
  have hRleH : R ≤ H := inf_le_right
  have hRleB : R ≤ H ⊓ M := le_inf hRleH hRleM
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hR2 : IsPGroup 2 R := hQ2.to_le inf_le_left
  have hB0N : H ⊓ M ≤ Subgroup.normalizer (R : Set G) := by
    have hHn : H ≤ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer
    have hQn : M ≤ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    have hle : H ⊓ M ≤
        Subgroup.normalizer (Q : Set G) ⊓ Subgroup.normalizer (H : Set G) :=
      le_inf (inf_le_right.trans hQn) (inf_le_left.trans hHn)
    simpa [R] using hle.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := Q) (K := H))
  have hAB : A ≤ B := Subgroup.subgroupOf_mono H hRleB
  have hAnorm : (A.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAB]
    intro h b hh hk
    have hhR : (h : G) ∈ R := Subgroup.mem_subgroupOf.mp hh
    have hkB : (b : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hk
    have hmem : (b : G) * (h : G) * (b : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hB0N hkB) (h : G)).mp hhR
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
  have hRbar_le_Nbar : Rbar ≤ Nbar := Subgroup.map_mono hAB
  haveI : (A.subgroupOf B).Normal := hAnorm
  have hRbarSubNorm : (Rbar.subgroupOf Nbar).Normal :=
    CFSG.SignalizerFunctorTheorem.normal_map_subgroupOf q hAB
  have hR2sub : IsPGroup 2 ↥(R.subgroupOf H) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRleH).symm
  have hRbar2 : IsPGroup 2 Rbar := hR2sub.map q
  obtain ⟨n, hn⟩ := hRbar2.exists_card_eq
  have hcopRbar : Nat.Coprime p (Nat.card Rbar) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcardSub : Nat.card (Rbar.subgroupOf Nbar) = Nat.card Rbar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRbar_le_Nbar).toEquiv
  have hcop : Nat.Coprime p (Nat.card (Rbar.subgroupOf Nbar)) := hcardSub ▸ hcopRbar
  have hle : Rbar.subgroupOf Nbar ≤ CFSG.pPrimeCore p ↥Nbar :=
    CFSG.le_pPrimeCore_of_normal_coprime hRbarSubNorm hcop
  have hRbar_card : Nat.card Rbar ≤ 2 :=
    calc Nat.card Rbar = Nat.card (Rbar.subgroupOf Nbar) := hcardSub.symm
      _ ≤ Nat.card (CFSG.pPrimeCore p ↥Nbar) := Subgroup.card_le_of_le hle
      _ ≤ 2 := h1
  have hAK : A ⊓ K = ⊥ := by
    have hAKp : IsPGroup 2 ↥(A ⊓ K) := hR2sub.to_inf_left
    rcases hAKp.card_eq_or_dvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have hdvd : 2 ∣ Nat.card K := h.trans (Subgroup.card_dvd_of_le inf_le_right)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hinj : Function.Injective
      (fun a : A => (⟨q a, Subgroup.mem_map_of_mem q a.2⟩ : Rbar)) := by
    intro a b hab
    have hqab : q (a : ↥H) = q (b : ↥H) := congrArg Subtype.val hab
    have hker : (a : ↥H)⁻¹ * (b : ↥H) ∈ K := by
      have h : (a : ↥H)⁻¹ * (b : ↥H) ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqab, inv_mul_cancel]
      rwa [QuotientGroup.ker_mk'] at h
    have hmemA : (a : ↥H)⁻¹ * (b : ↥H) ∈ A := A.mul_mem (A.inv_mem a.2) b.2
    have hmem : (a : ↥H)⁻¹ * (b : ↥H) ∈ A ⊓ K := ⟨hmemA, hker⟩
    rw [hAK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hA_le : Nat.card A ≤ Nat.card Rbar := Nat.card_le_card_of_injective _ hinj
  have hR_eq : Nat.card R = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH).toEquiv.symm
  show Nat.card R ≤ 2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

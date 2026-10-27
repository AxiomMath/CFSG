module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115CentralizerP
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Core

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the final torus action

This file proves the source-independent action step used at the end of part
(e): a prime-order subgroup of prime at least seven centralizes every cyclic
`3`- or `5`-group that it normalizes.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A prime-cardinality subgroup cannot act nontrivially on a cyclic
`3`- or `5`-group when its prime is at least seven. -/
public theorem lemma115_prime_card_subgroup_centralizes_cyclic_small_group
    {X : Type u} [Group X] [Finite X]
    {P T : Subgroup X} {p f : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hPcard : Nat.card P = p)
    (hf : f = 3 ∨ f = 5)
    (hTf : IsPGroup f T)
    (hTcyc : IsCyclic T)
    (hPnormT : P ≤ Subgroup.normalizer (T : Set X)) :
    P ≤ Subgroup.centralizer (T : Set X) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic T := hTcyc
  letI : Subgroup.Normalizes P T := ⟨hPnormT⟩
  let phi : P →* MulAut T := MulDistribMulAction.toMulAut P T
  have hRangeP : Nat.card phi.range ∣ Nat.card P :=
    Subgroup.card_range_dvd phi
  have hRangeAut : Nat.card phi.range ∣ Nat.card (MulAut T) :=
    Subgroup.card_subgroup_dvd_card phi.range
  have hfprime : f.Prime := by
    rcases hf with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  letI : Fact f.Prime := ⟨hfprime⟩
  have hAutNotP : ¬ p ∣ Nat.card (MulAut T) := by
    obtain ⟨n, hn⟩ := hTf.exists_card_eq
    rw [IsCyclic.card_mulAut, hn]
    exact lemma115_large_prime_not_dvd_totient_small_prime_power hp hp7 hf
  have hRangeOne : Nat.card phi.range = 1 := by
    have hRangeDvdP : Nat.card phi.range ∣ p := by
      simpa [hPcard] using hRangeP
    rcases hp.eq_one_or_self_of_dvd _ hRangeDvdP with hOne | hSelf
    · exact hOne
    · exfalso
      apply hAutNotP
      exact hSelf ▸ hRangeAut
  have hRangeBot : phi.range = ⊥ :=
    (Subgroup.card_eq_one (H := phi.range)).1 hRangeOne
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hphiA : phi ⟨a, ha⟩ = 1 := by
    have hmem : phi ⟨a, ha⟩ ∈ phi.range := ⟨⟨a, ha⟩, rfl⟩
    have hbot : phi ⟨a, ha⟩ ∈ (⊥ : Subgroup (MulAut T)) := by
      simpa [hRangeBot] using hmem
    simpa using hbot
  have hsmul : (⟨a, ha⟩ : P) • (⟨x, hx⟩ : T) = ⟨x, hx⟩ := by
    have h := congrArg (fun g : MulAut T => g ⟨x, hx⟩) hphiA
    simpa [phi, MulDistribMulAction.toMulAut_apply] using h
  have hconj : a * x * a⁻¹ = x := by
    have h := congrArg Subtype.val hsmul
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
  calc
    x * a = (a * x * a⁻¹) * a := by rw [hconj]
    _ = a * x := by group

/-- A cyclic torus with the recognized-model fixed intersection cannot be an
`f`-group.  Otherwise the prime-order subgroup centralizes it, reducing the
torus to `⟨a⟩`, whose small order contradicts the model lower bound. -/
public theorem lemma115_torus_not_isPGroup_of_fixed_intersection
    {X : Type u} [Group X] [Finite X]
    {P T : Subgroup X} {p f : ℕ} {a : X}
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hPcard : Nat.card P = p)
    (hf : f = 3 ∨ f = 5)
    (hTcyc : IsCyclic T)
    (hPnormT : P ≤ Subgroup.normalizer (T : Set X))
    (hfixed : T ⊓ Subgroup.centralizer (P : Set X) =
      Subgroup.zpowers a)
    (haorder : orderOf a = f)
    (hlower : 2 ^ (p - 1) ≤ Nat.card T) :
    ¬ IsPGroup f T := by
  intro hTf
  have hPcentT : P ≤ Subgroup.centralizer (T : Set X) :=
    lemma115_prime_card_subgroup_centralizes_cyclic_small_group
      hp hp7 hPcard hf hTf hTcyc hPnormT
  have hTleCP : T ≤ Subgroup.centralizer (P : Set X) := by
    intro x hxT
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    exact (Subgroup.mem_centralizer_iff.mp (hPcentT hyP) x hxT).symm
  have hTeq : T = Subgroup.zpowers a := by
    calc
      T = T ⊓ Subgroup.centralizer (P : Set X) :=
        (inf_eq_left.mpr hTleCP).symm
      _ = Subgroup.zpowers a := hfixed
  have hcardT : Nat.card T = f := by
    rw [hTeq, Nat.card_zpowers, haorder]
  have h64 : 64 ≤ 2 ^ (p - 1) := by
    have hexp : 6 ≤ p - 1 := by omega
    calc
      64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) hexp
  rcases hf with rfl | rfl <;> omega

end CFSG.BenderSuzuki

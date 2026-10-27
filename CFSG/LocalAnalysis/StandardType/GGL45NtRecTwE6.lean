module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LocalAnalysis.StandardType.GGL45E67Center
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtRecOn_twE6 :
    GGL45NtRecOn GGL45NtFamExTwE6 := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hfam, htag⟩ := hS
  subst htag
  have hp3 : p ≠ 3 := hfam.1
  have hn : 1 ≤ n := hlab.1
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, hKf, hKfin, hKcard, hQ⟩ := hQ
  refine ⟨K, hKf, hKfin, hKcard, hQ, ?_⟩
  dsimp only [GGL45NtRec]
  intro _ _
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
  · intro u hu hpu
    have h3 : u ^ 3 ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range :=
      TwE6Delta.pow_three_mem_inn hn hKcard hu
    obtain ⟨k, hk⟩ := hpu
    have hmem : u ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [pow_zero, pow_one] at hk
        rw [hk]
        exact Subgroup.one_mem _
      · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
          (((Nat.coprime_primes hp Nat.prime_three).2 hp3).pow_left k).symm
          (Nat.one_lt_pow (Nat.ne_of_gt hkpos) hp.one_lt)
        have he : u ^ (3 * m) = u := TableBExc.pow_mul_eq_self_of_mod hm hk
        rw [← he, pow_mul]
        exact Subgroup.pow_mem _ h3 m
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hmem
    exact ⟨r, hr.symm⟩
  · exact TwE6Delta.ggCenterPrime_twE6 hn hKcard hp hp2 hp3

namespace TableB.TwE6

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section RootSetOne

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ) (K : Type)
  [Field K]

@[expose] def DiagOneOn (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a = markDiag S K a * h) →
    ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K a

variable {A ρ n K}

theorem DiagOneOn.of_eq {S S' : (Fin r → ℤ) → Prop} (hS : S = S')
    (h : DiagOneOn A ρ n K S) : DiagOneOn A ρ n K S' :=
  hS ▸ h

theorem diagHom_mem_of_diagOneOn (h : DiagOneOn A ρ n K (LargeEvenIsRoot A))
    {a : Fin r → Kˣ} (ha : ∀ x ∈ LargeEvenTwistedH A K ρ n,
      diagHom A K a * x * (diagHom A K a)⁻¹ ∈ LargeEvenTwistedH A K ρ n) :
    diagHom A K a ∈ LargeEvenTwistedH A K ρ n := by
  rw [largeEvenTwistedH_eq] at ha ⊢
  obtain ⟨g, hg, hgd⟩ := h a fun x hx => ⟨_, ha x hx, by
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (diag_rel_iff a x _).2 rfl⟩
  have hge : g = diagHom A K a := Units.ext (by
    rw [hgd, coe_diagHom, largeEvenDiagMap_eq_markDiag])
  rw [← hge]
  exact hg

end RootSetOne

theorem diagOneOn_isRoot_of_even
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    DiagOneOn TwistTag.E6.tag.cartan TwistTag.E6.perm n K (IsRoot TwistTag.E6.tag) := by
  have h3 : ¬ 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, hk⟩ := heven
    have hmod : 2 ^ n % 3 = 1 := by
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a * g *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [markDiag_isRoot] at e
    rw [← eq_conj_of_mul_rootDiag e]
    exact hh'
  have hT : ∀ c ∈ torus₀ σ,
      rootDiagUnit TwistTag.E6.tag c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨s, hs, rfl⟩
    exact rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  exact ⟨_, hT _ (TwE6Toral.mem_torus₀_of_not_dvd hq hK hσ h3
      fun i => compat_of_forall_conj_mem hconj i), (markDiag_isRoot _).symm⟩

theorem diagHom_mem_twE6_of_even
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {a : Fin 6 → Kˣ}
    (ha : ∀ x ∈ LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n,
      diagHom (LargeEvenCartanE 6) K a * x * (diagHom (LargeEvenCartanE 6) K a)⁻¹ ∈
        LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) :
    diagHom (LargeEvenCartanE 6) K a ∈
      LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n :=
  diagHom_mem_of_diagOneOn
    ((diagOneOn_isRoot_of_even hn heven hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm)
    ha

end TableB.TwE6

namespace TwE6Delta

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem mem_inn_of_even
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n) (heven : Even n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {φ : MulAut (RecipeR K n)} (hφ : φ ∈ RecipeI K n) :
    φ ∈ (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)).range := by
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeR K n) ∪
      LargeEvenChevDiagImage (LargeEvenCartanE 6) K (RecipeH K n)) ≤
      (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)).range := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · exact ⟨x, rfl⟩
    · obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hψ
      rw [TableB.isDiagOf_eq_conj ha (TableB.TwE6.diagHom_mem_twE6_of_even hn heven hK ha.1)]
      exact ⟨_, rfl⟩
  exact hle hφ

end TwE6Delta

theorem ggL45NtRecOn_twE6_even :
    GGL45NtRecOn fun _ lab => lab.tag = .twE6 ∧ Even lab.n := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨htw, heven⟩ := hS
  dsimp only at htw heven
  subst htw
  have hn : 1 ≤ n := hlab.1
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, hKf, hKfin, hKcard, hQ⟩ := hQ
  have h3 : ¬ 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, hk⟩ := heven
    have hmod : 2 ^ n % 3 = 1 := by
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  have hgcd : Nat.Coprime p (Nat.gcd 3 (2 ^ n + 1)) := by
    have h1 : Nat.gcd 3 (2 ^ n + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [h1]
    exact Nat.coprime_one_right p
  refine ⟨K, hKf, hKfin, hKcard, hQ, ?_⟩
  dsimp only [GGL45NtRec]
  intro _ _
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
  · intro u hu _
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 (TwE6Delta.mem_inn_of_even hn heven hKcard hu)
    exact ⟨r, hr.symm⟩
  · exact ggCenterPrime_twE6_of_coprime hn hKcard hp hp2 hgcd

end CFSG.StandardType

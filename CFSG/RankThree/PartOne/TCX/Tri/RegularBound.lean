module

public import CFSG.RankThree.PartOne.TCX.Tri.TorusData
public import CFSG.RankThree.PartOne.TCX.Tri.E36Layer
public import CFSG.RankThree.PartOne.TCX.Tri.TorusBound

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Shape

variable {C : Type} [Group C]

@[expose] def RegularShape (Q : ℕ) (x : C) : Prop :=
  (∀ a ∈ Subgroup.centralizer ({x} : Set C), ∀ b ∈ Subgroup.centralizer ({x} : Set C),
      a * b = b * a) ∧
    ∀ y ∈ Subgroup.centralizer ({x} : Set C), y ^ (Q - 1) = 1 → y ^ 36 = 1

end Shape

section Embedding

variable {C : Type} [Group C] {L : Type} [Field L]

theorem regularShape_of_torus_embedding {x : C} {Q : ℕ}
    (ψ : Subgroup.centralizer ({x} : Set C) →* ModGL TwistTag.D4.tag L)
    (hinj : Function.Injective ψ) (ht : ∀ y, ψ y ∈ torusGroup TwistTag.D4.tag L)
    (hexp : ∀ y, ψ y ^ (Q - 1) = 1 → ψ y ^ 36 = 1) : RegularShape Q x := by
  refine ⟨fun a ha b hb => ?_, fun y hy hyQ => ?_⟩
  · have key : ψ (⟨a, ha⟩ * ⟨b, hb⟩) = ψ (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact torusGroup_comm (ht ⟨a, ha⟩) (ht ⟨b, hb⟩)
    exact congrArg Subtype.val (hinj key)
  · have h1 : ψ (⟨y, hy⟩ ^ (Q - 1)) = 1 := by
      have : (⟨y, hy⟩ : Subgroup.centralizer ({x} : Set C)) ^ (Q - 1) = 1 :=
        Subtype.ext (by simpa using hyQ)
      rw [this, map_one]
    rw [map_pow] at h1
    have h2 : ψ (⟨y, hy⟩ ^ 36) = 1 := by rw [map_pow]; exact hexp _ h1
    have h3 : (⟨y, hy⟩ : Subgroup.centralizer ({x} : Set C)) ^ 36 = 1 :=
      hinj (h2.trans (map_one ψ).symm)
    simpa using congrArg Subtype.val h3

end Embedding

section Exponent

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem tri_regular_exponent {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (w : WeylGroup TwistTag.D4.tag)
    {U X : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ} {d : ℕ}
    (hU : ∀ v, permLattice TwistTag.D4.perm.symm (w⁻¹ • v) = U *ᵥ v) (hU6 : U ^ 6 = 1)
    (hX : (U - 1) * X = (d : ℤ) • 1) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hT : rootDiagUnit TwistTag.D4.tag a ∈ twistedTorusOf
      (nseq (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) (triF0 L f₀) p) (triPhi L p f₀))
    (hord : rootDiagUnit TwistTag.D4.tag a ^ (2 ^ (p * f₀) - 1) = 1) :
    ∀ i, a i ^ d = 1 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  obtain ⟨X', hX'⟩ := exists_rightInverse_pow_sub_one hU6 hX hp6
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
  have hnrat : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n = n :=
    canonicalRep_frobenius_fixed f₀ w
  obtain ⟨-, hNP⟩ := nseq_triF0 f₀ n hnrat p
  have hfix : (n * triP L) ^ p * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))
      (rootDiagUnit TwistTag.D4.tag a) * ((n * triP L) ^ p)⁻¹ =
        rootDiagUnit TwistTag.D4.tag a := by
    have h := (mem_twistedTorusOf.1 hT).2
    rw [triPhi_apply] at h
    rw [← hNP]
    have e : (nseq n (triF0 L f₀) p * triP L ^ p) *
        Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) (rootDiagUnit TwistTag.D4.tag a) *
          (nseq n (triF0 L f₀) p * triP L ^ p)⁻¹ =
        nseq n (triF0 L f₀) p * (triP L ^ p *
          Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) (rootDiagUnit TwistTag.D4.tag a) *
            (triP L ^ p)⁻¹) * (nseq n (triF0 L f₀) p)⁻¹ := by group
    rw [e]
    exact h
  have hFr : ∀ c, iterateFrobenius L 2 (f₀ * p) c = c ^ (2 ^ (p * f₀)) := fun c => by
    rw [mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hQ1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  have haQ1 : ∀ i, a i ^ (2 ^ (p * f₀) - 1) = 1 := by
    have h1 : rootDiagUnit TwistTag.D4.tag (a ^ (2 ^ (p * f₀) - 1)) = 1 := by
      rw [← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)]
      have := map_pow (rootDiagUnitHom TwistTag.D4.tag L) a (2 ^ (p * f₀) - 1)
      change rootDiagUnit TwistTag.D4.tag (a ^ (2 ^ (p * f₀) - 1)) =
        rootDiagUnit TwistTag.D4.tag a ^ (2 ^ (p * f₀) - 1) at this
      rw [this, hord, rootDiagUnit_one]
    have h2 := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
      (h1.trans (rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)).symm)
    exact fun i => congrFun h2 i
  have haQ : ∀ i, a i ^ (2 ^ (p * f₀)) = a i := fun i => by
    rw [← Nat.sub_add_cancel hQ1, pow_succ, haQ1 i, one_mul]
  exact tri_torus_exponent (conjTuple_of_weyl w hU) hFr hfix haQ hX'

theorem tri_regular_exponent_e2 {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hT : rootDiagUnit TwistTag.D4.tag a ∈ twistedTorusOf
      (nseq (triNeg L) (triF0 L f₀) p) (triPhi L p f₀))
    (hord : rootDiagUnit TwistTag.D4.tag a ^ (2 ^ (p * f₀) - 1) = 1) :
    rootDiagUnit TwistTag.D4.tag a ^ 36 = 1 := by
  have h := tri_regular_exponent (L := L) (f₀ := f₀) hp hp5 trialityOppositionWeyl
    (fun v => triU2_hU v) triU2_pow triU2_adj hT hord
  rw [show (36 : ℕ) = 4 * 9 by norm_num, pow_mul]
  have : rootDiagUnit TwistTag.D4.tag a ^ 4 = 1 := by
    rw [← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)]
    have := map_pow (rootDiagUnitHom TwistTag.D4.tag L) a 4
    change rootDiagUnit TwistTag.D4.tag (a ^ 4) = rootDiagUnit TwistTag.D4.tag a ^ 4 at this
    rw [← this]
    congr 1
    funext i
    simpa using h i
  rw [this, one_pow]

theorem tri_regular_exponent_e36 {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {w : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hT : rootDiagUnit TwistTag.D4.tag a ∈ twistedTorusOf
      (nseq (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) (triF0 L f₀) p) (triPhi L p f₀))
    (hord : rootDiagUnit TwistTag.D4.tag a ^ (2 ^ (p * f₀) - 1) = 1) :
    rootDiagUnit TwistTag.D4.tag a ^ 36 = 1 := by
  have key : ∀ d : ℕ, d ∣ 36 → (∀ i, a i ^ d = 1) →
      rootDiagUnit TwistTag.D4.tag a ^ 36 = 1 := by
    intro d hd h
    obtain ⟨e, he⟩ := hd
    have h1 : rootDiagUnit TwistTag.D4.tag a ^ d = 1 := by
      rw [← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)]
      have := map_pow (rootDiagUnitHom TwistTag.D4.tag L) a d
      change rootDiagUnit TwistTag.D4.tag (a ^ d) = rootDiagUnit TwistTag.D4.tag a ^ d at this
      rw [← this]
      congr 1
      funext i
      simpa using h i
    rw [he, pow_mul, h1, one_pow]
  rcases hε with rfl | rfl
  · exact key 9 (by norm_num) (tri_regular_exponent (L := L) (f₀ := f₀) hp hp5 w
      (fun v => triU36_hU (Or.inl rfl) hw v) (triU36_pow (Or.inl rfl)) triU3_adj hT hord)
  · exact key 1 (by norm_num) (tri_regular_exponent (L := L) (f₀ := f₀) hp hp5 w
      (fun v => triU36_hU (Or.inr rfl) hw v) (triU36_pow (Or.inr rfl)) triU6_adj hT hord)

end Exponent

end CFSG.RankThree.PartOne.TCX.Tri

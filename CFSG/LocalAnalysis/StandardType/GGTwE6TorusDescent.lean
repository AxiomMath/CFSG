module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  Polynomial

theorem exists_gf4_algClosure {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra K L) (σ : K ≃+* K),
      Nat.card K = (2 ^ 1) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ 1)) ∧ IsAlgClosure K L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra (ZMod 2) L := ZMod.algebra L 2
  haveI : ExpChar L 2 := expChar_prime L 2
  haveI : Algebra.IsAlgebraic (ZMod 2) L := by
    refine ⟨fun c => ?_⟩
    obtain ⟨n, hn, hc⟩ := halg c
    by_cases h0 : c = 0
    · subst h0
      exact isAlgebraic_zero
    · have hpow : c ^ (2 ^ n - 1) = 1 := by
        have h2 : 2 ^ n = 2 ^ n - 1 + 1 := by
          have : 0 < 2 ^ n := pow_pos (by norm_num) n
          omega
        rw [h2, pow_succ] at hc
        exact mul_right_cancel₀ h0 (by rw [hc, one_mul])
      have hpos : 0 < 2 ^ n - 1 := by
        have h1 : 1 < 2 ^ n :=
          one_lt_pow' (by norm_num : (1 : ℕ) < 2) (Nat.pos_iff_ne_zero.mp hn)
        omega
      exact IsAlgebraic.of_pow (r := c) (n := 2 ^ n - 1) hpos
        (by rw [hpow]; simpa using isAlgebraic_natCast (R := ZMod 2) (A := L) 1)
  let K : Subfield L := TauCeti.frobeniusFixedSubfield L 2 2
  haveI : Finite ↥K := by
    change Finite ↥(TauCeti.frobeniusFixedSubfield L 2 2)
    exact TauCeti.finite_frobeniusFixedSubfield L 2 2 (by norm_num : (2 : ℕ) ≠ 0)
  haveI : CharP ↥K 2 := Subfield.charP K 2
  haveI : ExpChar ↥K 2 := expChar_prime ↥K 2
  haveI : PerfectField ↥K := PerfectField.ofFinite
  haveI : PerfectRing ↥K 2 := PerfectField.toPerfectRing 2
  haveI : Algebra.IsAlgebraic ↥K L := by
    refine ⟨fun y => ?_⟩
    obtain ⟨n, hn, hy⟩ := TauCeti.exists_mem_frobeniusFixedSubfield L 2 y
    refine ⟨X ^ 2 ^ n - X, ?_, ?_⟩
    · change (X ^ 2 ^ n - X : (↥K)[X]) ≠ 0
      exact FiniteField.X_pow_card_pow_sub_X_ne_zero (↥K) hn (by norm_num : 1 < 2)
    · rw [map_sub, map_pow, aeval_X, TauCeti.mem_frobeniusFixedSubfield.1 hy, sub_self]
  refine ⟨↥K, inferInstance, inferInstance, frobeniusEquiv ↥K 2, ?_, ?_, ?_⟩
  · change Nat.card ↥(TauCeti.frobeniusFixedSubfield L 2 2) = (2 ^ 1) ^ 2
    rw [TauCeti.card_frobeniusFixedSubfield L 2 2 (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num
  · intro c
    rw [frobeniusEquiv_def]
    norm_num
  · exact ⟨inferInstance, inferInstance⟩

theorem twE6_descent_packet
    {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {g₀ : ModGL Tag.E6 L} (hg₀ : g₀ ∈ adjointGroup Tag.E6 L)
    (u₀ : Fin Tag.E6.rank → Lˣ) :
    ∃ (k : Subfield L) (_ : Finite k) (ι : K →+* k) (g₃ : ModGL Tag.E6 k)
      (u₃ : Fin Tag.E6.rank → kˣ), k.subtype.comp ι = algebraMap K L ∧
        g₃ ∈ adjointGroup Tag.E6 k ∧ baseChangeGL k.subtype g₃ = g₀ ∧
          (fun j => Units.map k.subtype.toMonoidHom (u₃ j)) = u₀ := by
  classical
  obtain ⟨Sg, hSg⟩ := exists_finset_descent hg₀
  let Su : Finset L := Finset.univ.image fun j => (u₀ j : L)
  obtain ⟨E, hEfin, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (Sg ∪ Su)
  have hSgE : (Sg : Set L) ⊆ E := fun x hx =>
    hSE (by rw [Finset.coe_union]; exact Or.inl hx)
  have huE : ∀ j, (u₀ j : L) ∈ E := fun j =>
    hSE (by
      rw [Finset.coe_union]
      exact Or.inr (Finset.mem_coe.2 (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩)))
  obtain ⟨g₃, hg₃, hg₃eq⟩ := hSg E hSgE
  let u₃ : Fin Tag.E6.rank → Eˣ := fun j =>
    Units.mk0 ⟨(u₀ j : L), huE j⟩ fun h =>
      (u₀ j).ne_zero (by simpa using Subtype.ext_iff.mp h)
  refine ⟨E, hEfin, (algebraMap K L).codRestrict E fun a => hKE ⟨a, rfl⟩, g₃, u₃, ?_, hg₃,
    hg₃eq, ?_⟩
  · ext a
    rfl
  · funext j
    exact Units.ext rfl

end CFSG.StandardType.TwE6Tori

end

module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

open scoped Matrix

section SL2Tools


theorem eq_one_of_mul_self_eq_one_charTwo {L : Type} [Field L] [CharP L 2] {ε : L}
    (h : ε * ε = 1) : ε = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have : (ε - 1) ^ 2 = 0 := by linear_combination h + (1 - ε) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem canonicalRep_conj_rootSL2_of_fixed {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (w : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hw : w • β = β) (A : SL2 L) :
    canonicalRep (coxeterSystem τ) L w * rootSL2 τ L β A *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L β A := by
  obtain ⟨ε, hε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hβ
  obtain ⟨ε', hε', hX'⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (IsRoot.neg hβ)
  have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_charTwo hε
  have hε1' : ε' = 1 := eq_one_of_mul_self_eq_one_charTwo hε'
  obtain ⟨e, -, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  have h : (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp
      (rootSL2 τ L β) = rootSL2 τ L β :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        change canonicalRep (coxeterSystem τ) L w * rootSL2 τ L β (uSL c) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L β (uSL c)
        rw [rootSL2_uSL_eq, hX, hw, hε1, one_mul]
      · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        change canonicalRep (coxeterSystem τ) L w * rootSL2 τ L β (vSL c) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L β (vSL c)
        rw [hv, hX', smul_neg, hw, hε1', one_mul]
  exact DFunLike.congr_fun h A

theorem rootChar_eq_one_of_mem_fixedCharTuples {τ : Tag} {L : Type} [Field L]
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L} {q p : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1)
    {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr) (hap : ∀ i, a i ^ p = 1)
    {β : Fin τ.rank → ℤ} (hMβ : M *ᵥ β = β) : rootChar a β = 1 := by
  set z : Lˣ := rootChar a β with hz
  have h1 : z ^ q = z := by
    have := mem_fixedCharTuples_iff.1 ha β
    rw [hMβ, CTTorus.map_units_eq_pow hFr] at this
    exact this.symm
  have hzp : z ^ p = 1 := CTTorus.rootChar_pow_eq_one hap β
  have h2 : z ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hzp, one_pow]
  have h3 : z ^ 2 = 1 := by
    calc z ^ 2 = z ^ (q + 1) := by rw [pow_succ z q, h1, sq]
      _ = 1 := h2
  have hp0 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have := pow_gcd_eq_one.2 ⟨hzp, h3⟩
  rwa [hp0, pow_one] at this

end SL2Tools

end ExcFramesHalf

end CFSG.StandardType

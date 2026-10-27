module

public import CFSG.RankThree.PartTwo.Sec17.Ronan1724BFTStatement
import CFSG.RankThree.PartTwo.Sec17.Ronan1724BFTLin
import CFSG.RankThree.PartTwo.Sec17.Ronan1724BFTLift
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec17

open scoped commutatorElement

theorem j2NotSectionOfGLFourPrimeToThree_holds :
    J2NotSectionOfGLFourPrimeToThree := by
  intro q hq hq5 V _ _ hexp hcard H _ _ φ N _ hN hker
  refine ⟨fun e => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CFSG.IsElementaryAbelian q V :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  let π : H →* CFSG.Blueprint.NativeSporadic.J2 := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext h
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  obtain ⟨a, b, c, ha, -, hab, hca, hcb, hcard27, -, -, hc⟩ :=
    CFSG.SectionRank.J2_sylow3_cubic_witness
  obtain ⟨x, y, g, hx, hzx, hzy, hz1, hg⟩ :=
    Ronan1724BFT.exists_lift_heisenberg_inverting π hπ (by rw [hπker]; exact hN)
      (IsPGroup.of_card hcard27) ha hab hca hcb hc
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod q) (Additive V) :=
    (CFSG.Semidihedral.ElementaryActionTransport.autEquivGL (p := q) (R := V)).toMonoidHom.comp φ
  have hρN : ∀ h : H, ρ h = 1 → h ∈ N := by
    intro h hh
    apply hker
    rw [MonoidHom.mem_ker]
    exact (MulEquiv.map_eq_one_iff
      (CFSG.Semidihedral.ElementaryActionTransport.autEquivGL (p := q) (R := V))).mp hh
  have h3 : (3 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod q) q] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  haveI : FiniteDimensional (ZMod q) (Additive V) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod q) (Additive V) ≤ 5 := by
    have hc' := Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive V)
    rw [Nat.card_zmod] at hc'
    have hcV : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
    have hle : q ^ Module.finrank (ZMod q) (Additive V) ≤ q ^ 4 := by
      rw [← hc', hcV]
      exact hcard
    have := (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hle
    omega
  refine Ronan1724BFT.false_of_gl_heisenberg h3 hdim (x := ρ x) (y := ρ y) (g := ρ g)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_commutatorElement]; exact hzx.map ρ)
    (by rw [← map_commutatorElement]; exact hzy.map ρ) ?_ ?_
  · rw [← map_commutatorElement]
    intro h
    apply hz1
    have hmem := hρN _ h
    rw [← hπker] at hmem
    exact hmem
  · have h := congrArg ρ hg
    simpa only [map_mul, map_inv, map_commutatorElement] using h

theorem j2NotSectionOfGLFourTwo_of_primeToThree (h : J2NotSectionOfGLFourPrimeToThree) :
    J2NotSectionOfGLFourTwo := by
  intro q hq hq5 V _ _ hexp hcard H _ _ φ N _ hN2 hker
  refine h q hq hq5 V hexp hcard H φ N ?_ hker
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem j2NotSectionOfGLFourTwo_holds : J2NotSectionOfGLFourTwo :=
  j2NotSectionOfGLFourTwo_of_primeToThree j2NotSectionOfGLFourPrimeToThree_holds

end CFSG.RankThree.PartTwo.Sec17

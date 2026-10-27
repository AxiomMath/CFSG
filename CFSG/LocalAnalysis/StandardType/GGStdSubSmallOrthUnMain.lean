module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnSpecial
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddBT
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p n : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
  {Y : Submodule K V}

theorem bigConcl_of_isotropic (S : OrbitData Q p n A Y) (hpq : p ∣ Nat.card K + 1) (h5 : 5 ≤ n)
    {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a) :
    BigConcl p A D := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd S.prime S.odd
  have haA : a ∈ A := hE.a_mem
  have hap : a ^ p = 1 := S.elem.2 a haA
  have hx : OddOrderIsometry Q p a :=
    ⟨orthDerived_le_orthogonalGroup (S.le_omega haA), hap, hpK, fun v hv =>
      S.regular.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨i, hi, hDi⟩ := exists_block_of_endData hx hRep hE.D_le hE.D_cent hE.D_norm hE.D_qs
  by_cases h1 : i = X - 1
  · subst h1
    exact bigConcl_of_fixed S h5 hE (hRep.1 hi) hDi
  · exact bigConcl_of_special S hpq h5 hE (hRep.1 hi) h1 hDi

theorem bigConcl_of_normalizes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hpq : p ∣ Nat.card K + 1)
    (hn : finrank K V = 2 * n) (h5 : 5 ≤ n) {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V}
    (hE : EndData p (orthDerived Q) A D a) (hcard : p ^ (n - 1) ≤ Nat.card A)
    (hU : NormalizesTwoGroup (orthDerived Q) A) : BigConcl p A D := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have hIso : IsoGroup (QuadraticMap.polarBilin Q) p A :=
    isoGroup_of_le hQ hE.A_le hE.A_elem
  obtain ⟨U, hUΩ, hU1, hU2, hAU⟩ := hU
  obtain ⟨Y, hY0, hYinv, hYQ⟩ := OrthBstarOdd.exists_singular_of_two hQ hK1 (S := U) (N := A)
    hU2 hU1
    (fun s hs v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hUΩ hs)) v)
    (fun s hs => (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (hUΩ hs))).2)
    (fun g hg v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hE.A_le hg)) v)
    (fun g hg => hE.A_elem.2 g hg)
    (fun g hg s hs => (Subgroup.mem_normalizer_iff.mp (hAU hg) s).mp hs)
  have hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polarBilin Q y y' = 0 := fun y hy y' hy' => by
    have h1 := hYQ (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h1, hYQ y hy, hYQ y' hy']
    simp
  have hle : Nat.card A ≤ p ^ (n - 1) := by
    have := card_le_of_isotropic hp hpK hK1 (2 * n) V hn (QuadraticMap.polarBilin Q) A hIso Y
      hY0 hYinv hYiso
    rwa [show 2 * n / 2 = n by omega] at this
  exact bigConcl_of_isotropic ⟨hQ, hp, hp2, hK1, hn, hE.A_le, hE.A_elem, le_antisymm hle hcard,
    hY0, hYinv, hYQ⟩ hpq h5 hE

end Main

end SmallOrthUn

end CFSG.StandardType

end

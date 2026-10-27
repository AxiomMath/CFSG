module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmComp
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthFixedSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniGen
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentExcl
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open Module Multiplicative Polynomial QuadraticMap
open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
  {x : V ≃ₗ[K] V}

omit [Finite K] [FiniteDimensional K V] in
theorem ggResX2FixAux_tauOmega_injective [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hA : A ≤ orthDerived Q) : Function.Injective (Δ.τΩ hA) := by
  intro f g hfg
  have h : Δ.τ f = Δ.τ g := congrArg Subtype.val hfg
  exact Δ.τ_inj h



omit [Finite K] [FiniteDimensional K V] in
theorem ggResX2FixAux_normalizes_A_of_conj (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {n : ↥(orthDerived Q)}
    {g : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p))}
    (hconj : ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (g f)) :
    ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
  intro a ha
  have ha' : a ∈ Δ.τ.range := by rwa [Δ.τ_range]
  rcases ha' with ⟨f, rfl⟩
  have h : (n : V ≃ₗ[K] V) * (Δ.τ f) * (n : V ≃ₗ[K] V)⁻¹ = Δ.τ (g f) := by
    change (n : V ≃ₗ[K] V) * (Δ.τΩ hA f : V ≃ₗ[K] V) * (n : V ≃ₗ[K] V)⁻¹ =
      (Δ.τΩ hA (g f) : V ≃ₗ[K] V)
    exact congrArg Subtype.val (hconj f)
  have hmem : Δ.τ (g f) ∈ A := by
    have h' : Δ.τ (g f) ∈ Δ.τ.range := ⟨g f, rfl⟩
    rwa [Δ.τ_range] at h'
  change (↑n * Δ.τ f * (↑n)⁻¹) ∈ A
  rw [h]
  exact hmem


theorem ggResExactTwoOrthFixOmega_scalar [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ f : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1)
    (hcomm : ∀ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
      (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * Δ.τΩ hA f = Δ.τΩ hA f * n) :
    ∃ m : ZMod p, ∀ i, toAdd (f₀ i) ≠ 0 → Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h →
      toAdd (f i) = m * toAdd (f₀ i) := by
  classical
  obtain ⟨a, ha, hval, hswap', hmixed', -⟩ := Δ.blockG_orthDerived_pieces hp2 hQ hA f₀ hh hX
  let P : Fin r → Prop := fun i =>
    toAdd (f₀ i) ≠ 0 ∧ Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h
  have hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a := fun i hi => hval i hi.1 hi.2
  have hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
        ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f) :=
    fun i k hik hi hk he => hswap' i k hik hi.1 hi.2 hk.1 hk.2 he
  have hmixed : ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
        ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) (dinv i k f)) :=
    fun i k hi hk hia hka => hmixed' i k hi.1 hi.2 hk.1 hk.2 hia hka
  suffices hscalar : ∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i) by
    obtain ⟨m, hm⟩ := hscalar
    exact ⟨m, fun i hi hU => hm i ⟨hi, hU⟩⟩
  by_cases hPne : ∃ i, P i
  · obtain ⟨i₀, hP₀⟩ := hPne
    have hi₀_ne : toAdd (f₀ i₀) ≠ 0 := by
      rcases hP i₀ hP₀ with h | h
      · rw [h]; exact ha
      · rw [h]; exact neg_ne_zero.mpr ha
    refine ⟨toAdd (f i₀) * (toAdd (f₀ i₀))⁻¹, ?_⟩
    intro i hPi
    by_cases hii : i = i₀
    · subst hii
      rw [mul_assoc, inv_mul_cancel₀ hi₀_ne, mul_one]
    · rcases hP i hPi with hia | hia
      · rcases hP i₀ hP₀ with hi₀a | hi₀a
        · obtain ⟨n, hn, hconj⟩ := hswap i i₀ hii hPi hP₀ (by rw [hia, hi₀a])
          have hnA : ∀ a' ∈ A, n * a' * n⁻¹ ∈ A :=
            ggResX2FixAux_normalizes_A_of_conj Δ hA
              (g := fun f' => permAut (Equiv.swap i i₀) f') (by
                intro f'; exact hconj f')
          have hcomm_n := hcomm n hn hnA
          have h1 : n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA f := by
            rw [hcomm_n]
            group
          have h2 : Δ.τΩ hA (permAut (Equiv.swap i i₀) f) = Δ.τΩ hA f := by
            rw [← hconj f, h1]
          have h3 : permAut (Equiv.swap i i₀) f = f :=
            ggResX2FixAux_tauOmega_injective Δ hA h2
          have hfi : toAdd (f i) = toAdd (f i₀) := by
            have := congrArg (fun g => toAdd (g i)) h3.symm
            simpa [permAut_apply, Equiv.swap_apply_left] using this
          rw [hfi, hia, hi₀a]
          rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
        · obtain ⟨n, hn, hconj⟩ := hmixed i i₀ hPi hP₀ hia hi₀a
          have hnA : ∀ a' ∈ A, n * a' * n⁻¹ ∈ A :=
            ggResX2FixAux_normalizes_A_of_conj Δ hA
              (g := fun f' => permAut (Equiv.swap i i₀) (dinv i i₀ f')) (by
                intro f'; exact hconj f')
          have hcomm_n := hcomm n hn hnA
          have h1 : n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA f := by
            rw [hcomm_n]
            group
          have h2 : Δ.τΩ hA (permAut (Equiv.swap i i₀) (dinv i i₀ f)) = Δ.τΩ hA f := by
            rw [← hconj f, h1]
          have h3 : permAut (Equiv.swap i i₀) (dinv i i₀ f) = f :=
            ggResX2FixAux_tauOmega_injective Δ hA h2
          have hfi : toAdd (f i) = - toAdd (f i₀) := by
            have := congrArg (fun g => toAdd (g i)) h3.symm
            simpa [permAut_apply, Equiv.swap_apply_left, dinv, Function.update_apply, hii,
              Ne.symm hii] using this
          rw [hfi, hia, hi₀a]
          field_simp
      · rcases hP i₀ hP₀ with hi₀a | hi₀a
        · obtain ⟨n, hn, hconj⟩ := hmixed i₀ i hP₀ hPi hi₀a hia
          have hnA : ∀ a' ∈ A, n * a' * n⁻¹ ∈ A :=
            ggResX2FixAux_normalizes_A_of_conj Δ hA
              (g := fun f' => permAut (Equiv.swap i₀ i) (dinv i₀ i f')) (by
                intro f'; exact hconj f')
          have hcomm_n := hcomm n hn hnA
          have h1 : n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA f := by
            rw [hcomm_n]
            group
          have h2 : Δ.τΩ hA (permAut (Equiv.swap i₀ i) (dinv i₀ i f)) = Δ.τΩ hA f := by
            rw [← hconj f, h1]
          have h3 : permAut (Equiv.swap i₀ i) (dinv i₀ i f) = f :=
            ggResX2FixAux_tauOmega_injective Δ hA h2
          have hfi : toAdd (f i) = - toAdd (f i₀) := by
            have h : toAdd (f i₀) = - toAdd (f i) := by
              have := congrArg (fun g => toAdd (g i₀)) h3.symm
              simpa [permAut_apply, Equiv.swap_apply_right, dinv, Function.update_apply,
                Ne.symm hii, hii] using this
            calc toAdd (f i) = - (- toAdd (f i)) := (neg_neg _).symm
              _ = - toAdd (f i₀) := by rw [h]
          rw [hfi, hia, hi₀a]
          field_simp
        · obtain ⟨n, hn, hconj⟩ := hswap i i₀ hii hPi hP₀ (by rw [hia, hi₀a])
          have hnA : ∀ a' ∈ A, n * a' * n⁻¹ ∈ A :=
            ggResX2FixAux_normalizes_A_of_conj Δ hA
              (g := fun f' => permAut (Equiv.swap i i₀) f') (by
                intro f'; exact hconj f')
          have hcomm_n := hcomm n hn hnA
          have h1 : n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA f := by
            rw [hcomm_n]
            group
          have h2 : Δ.τΩ hA (permAut (Equiv.swap i i₀) f) = Δ.τΩ hA f := by
            rw [← hconj f, h1]
          have h3 : permAut (Equiv.swap i i₀) f = f :=
            ggResX2FixAux_tauOmega_injective Δ hA h2
          have hfi : toAdd (f i) = toAdd (f i₀) := by
            have := congrArg (fun g => toAdd (g i)) h3.symm
            simpa [permAut_apply, Equiv.swap_apply_left] using this
          rw [hfi, hia, hi₀a]
          rw [mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr ha), mul_one]
  · refine ⟨1, ?_⟩
    intro i hPi
    exact absurd ⟨i, hPi⟩ hPne

theorem ggResExactTwoOrthFixOmega_special [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ f : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1)
    (e : ↥(orthDerived Q)) (he : e = Δ.τΩ hA f)
    (hcomm : ∀ n ∈ (specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q),
      (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * e = e * n) :
    e ∈ Subgroup.centralizer
      ((specialBlock Q (Δ.τ f₀) h).subgroupOf (orthDerived Q) : Set ↥(orthDerived Q)) := by
  subst he
  obtain ⟨-, -, -, -, -, hcent⟩ := Δ.blockG_orthDerived_pieces hp2 hQ hA f₀ hh hX
  intro j hj
  exact (hcent f (ggResExactTwoOrthFixOmega_scalar hp2 Δ hQ hA f₀ f hh hX hcomm) j hj).symm

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem ggResX2FixAux_card_of_injective_range {n : ℕ}
    {f : (Fin n → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    (hinj : Function.Injective f) (hrange : f.range = A) :
    Nat.card A = p ^ n := by
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective f⟩
  have h1 : Nat.card (Fin n → Multiplicative (ZMod p)) = Nat.card A := by
    rw [← hrange, Nat.card_congr (Equiv.ofBijective f.rangeRestrict hbij)]
  rw [← h1]
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  rw [Nat.card_pi]
  simp only [hcard]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem ggResX2FixAux_eq_one_of_sq [Fact p.Prime] (hp2 : p ≠ 2)
    {a : Multiplicative (ZMod p)} (h : a ^ 2 = 1) : a = 1 := by
  have ht : toAdd (a ^ 2) = 0 := by rw [h, toAdd_one]
  rw [toAdd_pow] at ht
  have hmul : (2 : ZMod p) * toAdd a = 0 := by
    rw [two_mul]
    exact (two_nsmul (toAdd a)).symm.trans ht
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two Fact.out]
    exact hp2.symm
  have hunit : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).mpr hcop
  have hzero : toAdd a = 0 := by
    have h' : toAdd a * (2 : ZMod p) = 0 := by rw [mul_comm]; exact hmul
    exact (IsUnit.mul_left_eq_zero hunit).mp h'
  exact toAdd.injective (by rw [hzero, toAdd_one])

private theorem ggResX2FixAux_dinv_apply_self {n : ℕ} {i k : Fin n} (hik : i ≠ k)
    (f : Fin n → Multiplicative (ZMod p)) : (dinv i k f) i = (f i)⁻¹ := by
  rw [dinv]
  simp [Function.update_of_ne hik]

private theorem ggResX2FixAux_sgnAut_apply_self {n : ℕ} (i : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) : (sgnAut i f) i = (f i)⁻¹ := by
  rw [sgnAut_apply, Function.update_self]

private theorem ggResX2FixAux_finrank_fixedSpace (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hps : IsPlaneSystem Q Δ.F.U)
    (f₀ : Fin r → Multiplicative (ZMod p)) :
    finrank K (fixedSpace (Δ.τ f₀)) =
      finrank K V - 2 * (Finset.univ.filter (fun j => toAdd (f₀ j) ≠ 0)).card := by
  classical
  rw [Δ.fixedSpace_eq_polarPerp f₀, finrank_polarPerp hQ]
  exact congrArg (fun n => finrank K V - n) (hps.finrank_biSup _)

private theorem ggResX2FixAux_a_facts [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1)
    (Δ : TBJOmData Q p A r) (hps : IsPlaneSystem Q Δ.F.U) :
    finrank K V = 2 * r + finrank K (polarPerp Q (⨆ j, Δ.F.U j)) ∧
      finrank K (polarPerp Q (⨆ j, Δ.F.U j)) ≤ 2 ∧
      (finrank K (polarPerp Q (⨆ j, Δ.F.U j)) = 0 ∨
        finrank K (polarPerp Q (⨆ j, Δ.F.U j)) = 2) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨r', τ', F', hτ'F', hpiece', hdimV', hperm', hdinv'⟩ :=
    exists_torus_frame (p := p) hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  have hcardΔ : Nat.card A = p ^ r := ggResX2FixAux_card_of_injective_range Δ.τ_inj Δ.τ_range
  have hcardF : Nat.card A = p ^ r' := ggResX2FixAux_card_of_injective_range F'.inj F'.range
  have hr : r = r' := Nat.pow_right_injective (a := p) (Fact.out : p.Prime).two_le
    (hcardΔ.symm.trans hcardF)
  have hsup : finrank K (⨆ j, Δ.F.U j : Submodule K V) = 2 * r :=
    CFSG.LocalAnalysis.GLTheoremA.T173U.finrank_iSup_eq_of_isPlaneSystem
      (k := r) (U := fun j => Δ.F.U j) hps
  have hpolar := finrank_polarPerp hQ (⨆ j, Δ.F.U j : Submodule K V)
  rw [hsup] at hpolar
  have hle : 2 * r ≤ finrank K V := by
    rw [← hsup]
    simpa using Submodule.finrank_mono (le_top : (⨆ j, Δ.F.U j : Submodule K V) ≤ ⊤)
  have hdimVle : finrank K V ≤ 2 * r + 2 := by
    rw [← hr] at hdimV'
    exact hdimV'
  have hVdim : finrank K V = 2 * r + finrank K (polarPerp Q (⨆ j, Δ.F.U j)) := by omega
  have ha2 : finrank K (polarPerp Q (⨆ j, Δ.F.U j)) ≤ 2 := by omega
  have heven : Even (finrank K (polarPerp Q (⨆ j, Δ.F.U j))) := by
    obtain ⟨m, hm⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
    exact ⟨m - r, by omega⟩
  refine ⟨hVdim, ha2, ?_⟩
  obtain ⟨k, hk⟩ := heven
  omega

private theorem ggResX2FixAux_finrank_fixedSpace_eq [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1)
    (Δ : TBJOmData Q p A r) (hps : IsPlaneSystem Q Δ.F.U)
    (f₀ : Fin r → Multiplicative (ZMod p)) :
    finrank K (fixedSpace (Δ.τ f₀)) =
      2 * Fintype.card {i : Fin r // toAdd (f₀ i) = 0} +
        finrank K (polarPerp Q (⨆ j, Δ.F.U j)) := by
  classical
  have hVdim := (ggResX2FixAux_a_facts hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne Δ hps).1
  have hW := ggResX2FixAux_finrank_fixedSpace Δ hQ hps f₀
  have hc : (Finset.univ.filter (fun j => toAdd (f₀ j) ≠ 0)).card =
      r - Fintype.card {i : Fin r // toAdd (f₀ i) = 0} := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (p := fun j => toAdd (f₀ j) ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h2 : (Finset.univ.filter (fun j => ¬ toAdd (f₀ j) ≠ 0)).card =
        Fintype.card {i : Fin r // toAdd (f₀ i) = 0} := by
      rw [Fintype.card_subtype]
      congr 1
      ext j
      simp
    omega
  have hZr : Fintype.card {i : Fin r // toAdd (f₀ i) = 0} ≤ r := by
    simpa using Fintype.card_subtype_le (p := fun i : Fin r => toAdd (f₀ i) = 0)
  omega


private theorem ggResX2FixAux_eq_supportedFixedDerived_of_nonsplit
    (hx : OddOrderIsometry Q p x)
    (h4 : finrank K (fixedSpace x) = 4)
    (hnonsplit : ∀ S' : Submodule K (fixedSpace x), finrank K S' = 2 →
      ∃ u ∈ S', (Q.comp (fixedSpace x).subtype) u ≠ 0)
    {F' : Subgroup (V ≃ₗ[K] V)} (hF'q : CFSG.IsQuasisimple ↥F')
    (hF'le : F' ≤ supportedFixedDerived Q x)
    (hF'norm : (F'.subgroupOf (supportedFixedDerived Q x)).Normal) :
    F' = supportedFixedDerived Q x := by
  have hRnd : (polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hnonsplit' : ∀ U : Submodule K (fixedSpace x),
      finrank K U = finrank K (fixedSpace x) / 2 →
        ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    exact hnonsplit U (by omega)
  obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived
    (Q.comp (fixedSpace x).subtype) hRnd (Or.inl h4) hnonsplit'
  have hSq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hq
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hSq hF'norm with htop | hcenter
  · exact le_antisymm hF'le (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have hcomm : ∀ a b : ↥F', a * b = b * a := by
      intro a b
      have ha : Subgroup.inclusion hF'le a ∈
          Subgroup.center ↥(supportedFixedDerived Q x) :=
        hcenter (Subgroup.mem_subgroupOf.mpr a.2)
      have h := Subgroup.mem_center_iff.mp ha (Subgroup.inclusion hF'le b)
      exact Subtype.ext (congrArg Subtype.val h).symm
    have hqcomm : ∀ a b : ↥F' ⧸ Subgroup.center ↥F', a * b = b * a := by
      intro a b
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a' b']
    obtain ⟨a, b, hab⟩ := hF'q.2.2
    exact hab (hqcomm a b)

theorem ggResX2FixAux_dinv_eq_one [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    {f₀ f : Fin r → Multiplicative (ZMod p)} {i k : Fin r} (hik : i ≠ k)
    (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0)
    (h5 : 5 ≤ finrank K (fixedSpace (Δ.τ f₀)))
    {F' : Subgroup (V ≃ₗ[K] V)}
    (hF'eq : F' = supportedFixedDerived Q (Δ.τ f₀))
    (hcomm : ∀ n ∈ (F'.subgroupOf (orthDerived Q)),
      (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * Δ.τΩ hA f = Δ.τΩ hA f * n) :
    f i = 1 := by
  obtain ⟨n, hnS, hnconj⟩ := Δ.blockZ_dinv hp2 hQ hA f₀ h5 hik hi hk
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hnΩ : n ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hnS
  let nΩ : ↥(orthDerived Q) := ⟨n, hnΩ⟩
  have hnC : nΩ ∈ F'.subgroupOf (orthDerived Q) :=
    Subgroup.mem_subgroupOf.mpr (by rw [hF'eq]; exact hnS)
  have hconjΩ : ∀ f', nΩ * Δ.τΩ hA f' * nΩ⁻¹ = Δ.τΩ hA (dinv i k f') := by
    intro f'
    apply Subtype.ext
    change n * Δ.τ f' * n⁻¹ = Δ.τ (dinv i k f')
    exact hnconj f'
  have hnA : ∀ a ∈ A, nΩ * a * nΩ⁻¹ ∈ A :=
    ggResX2FixAux_normalizes_A_of_conj Δ hA (g := fun f' => dinv i k f') hconjΩ
  have h1 : nΩ * Δ.τΩ hA f * nΩ⁻¹ = Δ.τΩ hA f := by
    rw [hcomm nΩ hnC hnA]
    group
  have h2 : Δ.τΩ hA (dinv i k f) = Δ.τΩ hA f := by
    rw [← hconjΩ f, h1]
  have h3 : dinv i k f = f := ggResX2FixAux_tauOmega_injective Δ hA h2
  have hfi : (dinv i k f) i = f i := by rw [h3]
  rw [ggResX2FixAux_dinv_apply_self hik f] at hfi
  have hsq : f i ^ 2 = 1 := by
    rw [pow_two]
    have h := congrArg (fun x => x * f i) hfi
    simpa using h.symm
  exact ggResX2FixAux_eq_one_of_sq hp2 hsq

private theorem ggResX2FixAux_sign_eq_one [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    {f₀ f : Fin r → Multiplicative (ZMod p)} {i : Fin r}
    (hi : toAdd (f₀ i) = 0)
    (h4 : finrank K (fixedSpace (Δ.τ f₀)) = 4)
    (hfix : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    (hnonsplit : ∀ S' : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S' = 2 →
      ∃ u ∈ S', (Q.comp (fixedSpace (Δ.τ f₀)).subtype) u ≠ 0)
    {F' : Subgroup (V ≃ₗ[K] V)}
    (hF'eq : F' = supportedFixedDerived Q (Δ.τ f₀))
    (hcomm : ∀ n ∈ (F'.subgroupOf (orthDerived Q)),
      (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * Δ.τΩ hA f = Δ.τΩ hA f * n) :
    f i = 1 := by
  obtain ⟨n, hnS, hnconj⟩ := Δ.blockZ_sign hp2 hQ hA f₀ h4 hfix hnonsplit hi
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hnΩ : n ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hnS
  let nΩ : ↥(orthDerived Q) := ⟨n, hnΩ⟩
  have hnC : nΩ ∈ F'.subgroupOf (orthDerived Q) :=
    Subgroup.mem_subgroupOf.mpr (by rw [hF'eq]; exact hnS)
  have hconjΩ : ∀ f', nΩ * Δ.τΩ hA f' * nΩ⁻¹ = Δ.τΩ hA (sgnAut i f') := by
    intro f'
    apply Subtype.ext
    change n * Δ.τ f' * n⁻¹ = Δ.τ (sgnAut i f')
    exact hnconj f'
  have hnA : ∀ a ∈ A, nΩ * a * nΩ⁻¹ ∈ A :=
    ggResX2FixAux_normalizes_A_of_conj Δ hA (g := fun f' => sgnAut i f') hconjΩ
  have h1 : nΩ * Δ.τΩ hA f * nΩ⁻¹ = Δ.τΩ hA f := by
    rw [hcomm nΩ hnC hnA]
    group
  have h2 : Δ.τΩ hA (sgnAut i f) = Δ.τΩ hA f := by
    rw [← hconjΩ f, h1]
  have h3 : sgnAut i f = f := ggResX2FixAux_tauOmega_injective Δ hA h2
  have hfi : (sgnAut i f) i = f i := by rw [h3]
  rw [ggResX2FixAux_sgnAut_apply_self i f] at hfi
  have hsq : f i ^ 2 = 1 := by
    rw [pow_two]
    have h := congrArg (fun x => x * f i) hfi
    simpa using h.symm
  exact ggResX2FixAux_eq_one_of_sq hp2 hsq

private theorem ggResX2FixAux_fixed_factor [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1)
    (hps : IsPlaneSystem Q Δ.F.U) (hK : Nat.card K = 2)
    {f₀ f : Fin r → Multiplicative (ZMod p)}
    {F' : Subgroup (V ≃ₗ[K] V)} (hF'q : CFSG.IsQuasisimple ↥F')
    (hF'S : F' ≤ supportedFixedDerived Q (Δ.τ f₀))
    (hF'norm : (F'.subgroupOf (supportedFixedDerived Q (Δ.τ f₀))).Normal)
    (hFix : finrank K (fixedSpace (Δ.τ f₀)) ≤ 4 ∨
      F' = supportedFixedDerived Q (Δ.τ f₀))
    (hcomm : ∀ n ∈ (F'.subgroupOf (orthDerived Q)),
      (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * Δ.τΩ hA f = Δ.τΩ hA f * n) :
    ∀ i, toAdd (f₀ i) = 0 → f i = 1 := by
  classical
  obtain ⟨hVdim, ha2, ha02⟩ :=
    ggResX2FixAux_a_facts hp2 hpq hQ hT hA hApow hAcomm hmax hne Δ hps
  have hWdim := ggResX2FixAux_finrank_fixedSpace_eq hp2 hpq hQ hT hA hApow hAcomm hmax hne Δ hps f₀
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hpiece_fix : ∀ j, toAdd (f₀ j) = 0 → Δ.F.U j ≤ fixedSpace (Δ.τ f₀) := by
    intro j hj u hu
    rw [Δ.mem_fixedSpace_iff f₀]
    intro j' hj' u' hu'
    exact Δ.F.orth j' j (fun h => hj' (h ▸ hj)) u' hu' u hu
  intro i hi
  have hZpos : 1 ≤ Fintype.card {j : Fin r // toAdd (f₀ j) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  by_cases hZ2 : 2 ≤ Fintype.card {j : Fin r // toAdd (f₀ j) = 0}
  · by_cases hW5 : 5 ≤ finrank K (fixedSpace (Δ.τ f₀))
    · obtain ⟨k, hkne, hk0⟩ : ∃ k : Fin r, k ≠ i ∧ toAdd (f₀ k) = 0 := by
        obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card
          (α := {j : Fin r // toAdd (f₀ j) = 0}) (by omega) ⟨i, hi⟩
        exact ⟨k.1, fun h => hk (Subtype.ext h), k.2⟩
      have hF'eq : F' = supportedFixedDerived Q (Δ.τ f₀) := by
        rcases hFix with h | h
        · omega
        · exact h
      exact ggResX2FixAux_dinv_eq_one hp2 Δ hQ hA (Ne.symm hkne) hi hk0 hW5 hF'eq hcomm
    · have hWle : finrank K (fixedSpace (Δ.τ f₀)) ≤ 4 := by omega
      have hZc : Fintype.card {j : Fin r // toAdd (f₀ j) = 0} = 2 := by omega
      have ha0 : finrank K (polarPerp Q (⨆ j, Δ.F.U j)) = 0 := by omega
      obtain ⟨k, hkne, hk0⟩ : ∃ k : Fin r, k ≠ i ∧ toAdd (f₀ k) = 0 := by
        obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card
          (α := {j : Fin r // toAdd (f₀ j) = 0}) (by omega) ⟨i, hi⟩
        exact ⟨k.1, fun h => hk (Subtype.ext h), k.2⟩
      have hW4 : finrank K (fixedSpace (Δ.τ f₀)) = 4 := by omega
      set s : Finset (Fin r) := {i, k} with hs
      have hcard_s : s.card = 2 := by
        rw [hs]; exact Finset.card_pair (Ne.symm hkne)
      have hUik : finrank K (⨆ j ∈ s, Δ.F.U j : Submodule K V) = 4 := by
        have h := hps.finrank_biSup s
        rw [hcard_s] at h
        exact h
      have hUik_eq : (⨆ j ∈ s, Δ.F.U j : Submodule K V) = (Δ.F.U i ⊔ Δ.F.U k : Submodule K V) := by
        rw [hs]
        simp only [Finset.iSup_insert, Finset.iSup_singleton]
      have hUik2 : finrank K (Δ.F.U i ⊔ Δ.F.U k : Submodule K V) = 4 := by
        rw [← hUik_eq]; exact hUik
      have hsub : (Δ.F.U i ⊔ Δ.F.U k : Submodule K V) ≤ fixedSpace (Δ.τ f₀) :=
        sup_le (hpiece_fix i hi) (hpiece_fix k hk0)
      have hWeq : fixedSpace (Δ.τ f₀) = (Δ.F.U i ⊔ Δ.F.U k : Submodule K V) :=
        (Submodule.eq_of_le_of_finrank_eq hsub (by omega)).symm
      have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.comp (fixedSpace (Δ.τ f₀)).subtype) := by
        rw [hWeq, ← hUik_eq]
        refine (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem.isPlusType_biSup_iff
          hps s).mpr ?_
        rw [hcard_s]
        exact ⟨1, by norm_num⟩
      exact absurd hF'q (ggResX2_not_isQuasisimple_of_fixedSpace_small hK hx
        (Or.inr ⟨hW4, hplus⟩) hF'S)
  · have hZ1 : Fintype.card {j : Fin r // toAdd (f₀ j) = 0} = 1 := by omega
    by_cases ha0 : finrank K (polarPerp Q (⨆ j, Δ.F.U j)) = 0
    · have hW2 : finrank K (fixedSpace (Δ.τ f₀)) ≤ 2 := by omega
      exact absurd hF'q (ggResX2_not_isQuasisimple_of_fixedSpace_small hK hx
        (Or.inl hW2) hF'S)
    · have ha2' : finrank K (polarPerp Q (⨆ j, Δ.F.U j)) = 2 := by
        rcases ha02 with h | h
        · exact absurd h ha0
        · exact h
      have hW4 : finrank K (fixedSpace (Δ.τ f₀)) = 4 := by omega
      by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.comp (fixedSpace (Δ.τ f₀)).subtype)
      · exact absurd hF'q (ggResX2_not_isQuasisimple_of_fixedSpace_small hK hx
          (Or.inr ⟨hW4, hplus⟩) hF'S)
      · have hfix : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v := by
          have hpos : 0 < finrank K (polarPerp Q (⨆ j, Δ.F.U j)) := by omega
          obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
          exact ⟨v, fun h0 => hv0 (Subtype.ext h0), Δ.polarPerp_iSup_le_commonFixed hv⟩
        have hnonsplit : ∀ S' : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S' = 2 →
            ∃ u ∈ S', (Q.comp (fixedSpace (Δ.τ f₀)).subtype) u ≠ 0 := by
          intro S' hS'
          by_contra h
          push Not at h
          exact hplus ⟨S', by omega, h⟩
        have hF'eq : F' = supportedFixedDerived Q (Δ.τ f₀) :=
          ggResX2FixAux_eq_supportedFixedDerived_of_nonsplit hx hW4 hnonsplit hF'q hF'S hF'norm
        exact ggResX2FixAux_sign_eq_one hp2 Δ hQ hA hi hW4 hfix hnonsplit hF'eq hcomm

theorem ggResX2FixAux_isPlaneSystem [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hpq : p ∣ Nat.card K + 1) :
    IsPlaneSystem Q Δ.F.U := by
  refine ⟨Δ.finrank_piece, ?_, ?_, Δ.F.orth⟩
  · intro j
    exact CFSG.ComponentClassification.UnbalancedCatalog.nondegenerate_polarBilin_comp_subtype
      (S := Δ.F.U j) fun u hu hperp => Δ.F.nondeg j u hu fun v hv => by
        rw [polar_comm]; exact hperp v hv
  · intro j hplus
    exact (CFSG.RankThree.PartOne.K159.not_dvd_card_sub_one (Fact.out : p.Prime) hp2 hpq)
      ((Δ.isPlusType_piece_iff_dvd_card_sub_one hp2 hA j).mp hplus)
end OrthTorus

theorem ggResExactTwoOrthFixOmega_holds : GGResExactTwoOrthFixOmega := by
  intro F _ _ _ hF2 V _ _ _ Q hQ hdim E hEab hEsc t htE ht1 C hC e he hcomm
  let A : Subgroup (V ≃ₗ[F] V) := E.map (orthDerived Q).subtype
  have hAΩ : A ≤ orthDerived Q := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    exact e.2
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    have h : e ^ 3 = 1 := hEab.2 e he
    exact Subtype.ext_iff.mp h
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rcases Subgroup.mem_map.mp ha with ⟨e₁, he₁, rfl⟩
    rcases Subgroup.mem_map.mp hb with ⟨e₂, he₂, rfl⟩
    have h := hEab.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    have h' : (e₁ : ↥(orthDerived Q)) * e₂ = e₂ * e₁ := Subtype.ext_iff.mp h
    exact congrArg Subtype.val h'
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hgΩ hg3 hgc
    let g' : ↥(orthDerived Q) := ⟨g, hgΩ⟩
    have hg'3 : g' ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hg3
    have hg'c : ∀ e ∈ E, g' * e = e * g' := by
      intro e he
      have heA : (e : V ≃ₗ[F] V) ∈ A := Subgroup.mem_map_of_mem _ he
      have h := hgc (e : V ≃ₗ[F] V) heA
      apply Subtype.ext
      exact h
    have hg'E : g' ∈ E := hEsc g' hg'c hg'3
    exact Subgroup.mem_map_of_mem _ hg'E
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine ⟨(t : V ≃ₗ[F] V), Subgroup.mem_map_of_mem _ htE, ?_⟩
    intro h
    apply ht1
    apply Subtype.ext
    exact h
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hm4 : 4 ≤ m := by omega
  have hm' : Module.finrank F V = 2 * m := by omega
  have hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hm4 hm'
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpq : 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
    right
    rw [hF2]
  obtain ⟨r, τ, F_data, D, i₁, i₂, i₃, c, θ, hτF, hinj, hrange, hdim_D, hcp, hfix, htwist,
    hroots, hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (p := 3) hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  let Δ : OrthTorus.TBJOmData Q 3 A r :=
    { τ := τ, F := F_data, D := D, c := c, θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdim_D, c_pow := hcp, c_fix := hfix, c_twist := htwist, c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsign, noFixed := hnoFix,
      exFixed := hexFix }
  have htA : (t : V ≃ₗ[F] V) ∈ A := Subgroup.mem_map_of_mem _ htE
  obtain ⟨f₀, hf₀⟩ := Δ.τ_range.symm.le htA
  have hf₀' : t = Δ.τΩ hAΩ f₀ := by
    apply Subtype.ext
    exact hf₀.symm
  have heA : (e : V ≃ₗ[F] V) ∈ A := Subgroup.mem_map_of_mem _ he
  obtain ⟨f, hf⟩ := Δ.τ_range.symm.le heA
  have hf' : e = Δ.τΩ hAΩ f := by
    apply Subtype.ext
    exact hf.symm
  have hx : OddOrderIsometry Q 3 (t : V ≃ₗ[F] V) := by
    rw [hf₀']
    exact Δ.oddOrderIsometry hp2 hQ hAΩ f₀
  have htx : (t : V ≃ₗ[F] V) = Δ.τ f₀ :=
    congrArg (fun g : ↥(orthDerived Q) => (g : V ≃ₗ[F] V)) hf₀'
  have hpq3 : 3 ∣ Nat.card F + 1 := by
    rw [hF2]
  have hcommA : ∀ n ∈ C, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * e = e * n := by
    intro n hn hnA
    refine hcomm n hn ?_
    intro a ha
    have haA : (a : V ≃ₗ[F] V) ∈ A := Subgroup.mem_map_of_mem _ ha
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp (hnA a haA)
    rw [show n * a * n⁻¹ = b from Subtype.ext hbeq.symm]
    exact hb
  rcases OrthTorus.component_cases (p := 3) hQ (Fact.out : Nat.Prime 3) hp2 (x := t) hx hC with
      ⟨h, hh, hhX, hCeq⟩ | ⟨F', hF'q, hF'S, hF'norm, hFix, hCeq⟩
  · rw [htx] at hh hCeq
    rw [hCeq] at hcommA ⊢
    exact OrthTorus.ggResExactTwoOrthFixOmega_special hp2 Δ hQ hAΩ f₀ f hh hhX e hf' hcommA
  · rw [htx] at hF'S hF'norm hFix
    rw [hCeq] at hcommA ⊢
    rw [hf'] at hcommA
    have hps : IsPlaneSystem Q Δ.F.U :=
      OrthTorus.ggResX2FixAux_isPlaneSystem hp2 Δ hQ hAΩ hpq3
    have hf1 : ∀ i, toAdd (f₀ i) = 0 → f i = 1 :=
      OrthTorus.ggResX2FixAux_fixed_factor (f₀ := f₀) (f := f) hp2 Δ hQ hAΩ hpq hT hApow
        hAcomm hmax hne hps hF2 hF'q hF'S hF'norm hFix hcommA
    have hcommS := Δ.blockZ_comm hp2 hQ hAΩ f₀ f hf1
    intro c hc
    apply Subtype.ext
    show (c : V ≃ₗ[F] V) * (e : V ≃ₗ[F] V) = (e : V ≃ₗ[F] V) * (c : V ≃ₗ[F] V)
    rw [hf']
    exact (hcommS c.1 (hF'S (Subgroup.mem_subgroupOf.mp hc))).symm
end CFSG.StandardType

end

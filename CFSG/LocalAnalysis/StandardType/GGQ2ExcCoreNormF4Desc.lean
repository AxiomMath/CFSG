module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormLe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawF4Norm
import CFSG.LocalAnalysis.StandardType.GGFamF4Tame
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedRange
import CFSG.LieType.Universal.Symplectic
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes


section Squeeze

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {m : Fin 6}
  (γ : ExcRaw.Root m → Fin τ.rank → ℤ)

theorem codeComponent_mono {c c' : Finset (ExcRaw.Root m)} (h : c ⊆ c') :
    codeComponent S γ c ≤ codeComponent S γ c' := by
  have hΨ : codeRoots γ c ⊆ codeRoots γ c' := fun δ ⟨i, hi, hδ⟩ => ⟨i, h hi, hδ⟩
  have hX := inf_le_inf_right S.Γ (rootSpan_mono (τ := τ) (R := L) hΨ)
  exact Subgroup.commutator_mono hX hX

theorem codeComponent_eq_commutator {c : Finset (ExcRaw.Root m)}
    (hperf : ⁅⁅rootSpan τ L (codeRoots γ c) ⊓ S.D.model, rootSpan τ L (codeRoots γ c) ⊓ S.D.model⁆,
        ⁅rootSpan τ L (codeRoots γ c) ⊓ S.D.model, rootSpan τ L (codeRoots γ c) ⊓ S.D.model⁆⁆ =
      ⁅rootSpan τ L (codeRoots γ c) ⊓ S.D.model, rootSpan τ L (codeRoots γ c) ⊓ S.D.model⁆) :
    codeComponent S γ c =
      ⁅rootSpan τ L (codeRoots γ c) ⊓ S.D.model, rootSpan τ L (codeRoots γ c) ⊓ S.D.model⁆ := by
  set H := rootSpan τ L (codeRoots γ c) ⊓ S.D.model with hH
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  have hYH : rootSpan τ L (codeRoots γ c) ⊓ S.Γ ≤ H := inf_le_inf_left _ hΓM
  have hKH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_self H
  have hKΓ : ⁅H, H⁆ ≤ S.Γ :=
    calc ⁅H, H⁆ = ⁅⁅H, H⁆, ⁅H, H⁆⁆ := hperf.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ :=
        Subgroup.commutator_mono (hKH.trans inf_le_right) (hKH.trans inf_le_right)
  have hKY : ⁅H, H⁆ ≤ rootSpan τ L (codeRoots γ c) ⊓ S.Γ := le_inf (hKH.trans inf_le_left) hKΓ
  refine le_antisymm (Subgroup.commutator_mono hYH hYH) ?_
  calc ⁅H, H⁆ = ⁅⁅H, H⁆, ⁅H, H⁆⁆ := hperf.symm
    _ ≤ codeComponent S γ c := Subgroup.commutator_mono hKY hKY

theorem codeComponent_eq_of_perfect {c : Finset (ExcRaw.Root m)}
    (hperf : ⁅rootSpan τ L (codeRoots γ c) ⊓ S.D.model, rootSpan τ L (codeRoots γ c) ⊓ S.D.model⁆ =
      rootSpan τ L (codeRoots γ c) ⊓ S.D.model) :
    codeComponent S γ c = rootSpan τ L (codeRoots γ c) ⊓ S.D.model := by
  rw [codeComponent_eq_commutator S γ (by rw [hperf, hperf]), hperf]

theorem image_rho_codeRoots (hρ : ∀ δ, IsRoot τ δ → S.ρ δ = -δ) (hγ : ∀ i, IsRoot τ (γ i))
    (c : Finset (ExcRaw.Root m)) : (fun δ => S.ρ δ) '' codeRoots γ c = codeRoots γ c := by
  have hroot : ∀ δ ∈ codeRoots γ c, IsRoot τ δ := by
    rintro δ ⟨i, -, rfl | rfl⟩
    exacts [hγ i, CFSG.LieType.Chevalley.IsRoot.neg (hγ i)]
  have hneg : ∀ δ ∈ codeRoots γ c, -δ ∈ codeRoots γ c := by
    rintro δ ⟨i, hi, rfl | rfl⟩
    exacts [⟨i, hi, Or.inr rfl⟩, ⟨i, hi, Or.inl (neg_neg _)⟩]
  ext δ
  constructor
  · rintro ⟨δ', hδ', rfl⟩
    show S.ρ δ' ∈ codeRoots γ c
    rw [hρ δ' (hroot δ' hδ')]
    exact hneg δ' hδ'
  · intro hδ
    refine ⟨-δ, hneg δ hδ, ?_⟩
    show S.ρ (-δ) = δ
    rw [hρ (-δ) (hroot _ (hneg δ hδ)), neg_neg]

end Squeeze

section Neg

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}

theorem NegLangTwo.charP (hS : NegLangTwo S) : CharP L 2 := by
  have hchar : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rwa [hS.1] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by simpa using hchar)

theorem NegLangTwo.isAlgebraic (hS : NegLangTwo S) [Algebra (ZMod 2) L] :
    Algebra.IsAlgebraic (ZMod 2) L := by
  refine ⟨fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := hS.2.1 x
  rw [hS.1] at hx
  refine ⟨Polynomial.X ^ 2 ^ n - Polynomial.X,
    FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod 2) hn.ne' one_lt_two, ?_⟩
  simp [hx]

end Neg

namespace ExcCoordDatum

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .F4 L p}
  {T₀ : Subgroup (ModGL .F4 L)} (d : ExcCoordDatum S T₀ 0)
include d

theorem exists_famShape (hS : NegLangTwo S) {U : Submodule (ZMod 3) (ExcRaw.V 0)}
    {c : Finset (ExcRaw.Root 0)} (hU : ExcRaw.occurs 0 U c) (hU0 : U ≠ ⊥) :
    ∃ (A : Subgroup (ModGL .F4 L)) (a : ↥A → Fin Tag.F4.rank → Lˣ)
      (j : KernelComponent (famCharHom a)),
      (∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) ∧
        componentRoots (famCharHom a) j = codeRoots d.γ c ∧
        (FamF4PairShape (codeRoots d.γ c) ∨ FamF4LongA2Shape (codeRoots d.γ c) ∨
          FamF4ShortA2Shape (codeRoots d.γ c) ∨ FamF4B2Shape (codeRoots d.γ c) ∨
          FamF4B3Shape (codeRoots d.γ c) ∨ FamF4C3Shape (codeRoots d.γ c)) := by
  classical
  have : CharP L 2 := hS.charP
  obtain ⟨A, hA, hAU⟩ := d.exists_le_ggLinImage_eq U
  obtain ⟨a, ha, hT, h3⟩ := exists_excFamily d hA
  obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha (hAU.symm ▸ hU)
  have h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hU0 ((Submodule.eq_bot_iff _).2 fun v hv => ?_)
    rw [← hAU, mem_ggLinImage] at hv
    have h1 : Additive.toMul (d.coord.symm v) = 1 := by
      refine Subtype.ext ?_
      rw [← ha ⟨_, hv⟩]
      exact hcon _
    have h0 : d.coord.symm v = 0 := by
      rw [← ofMul_toMul (d.coord.symm v), h1, ofMul_one]
    simpa using congrArg d.coord h0
  refine ⟨A, a, j, hT, hj, ?_⟩
  rw [← hj]
  exact famF4_shape S Nat.prime_three (by decide) hT h3 h1 j

theorem card_of_occurs (hS : NegLangTwo S) {U : Submodule (ZMod 3) (ExcRaw.V 0)}
    {c : Finset (ExcRaw.Root 0)} (hU : ExcRaw.occurs 0 U c) (hU0 : U ≠ ⊥) :
    c.card = 1 ∨ c.card = 3 ∨ c.card = 4 ∨ c.card = 9 := by
  obtain ⟨A, a, j, hT, hj, hsh⟩ := d.exists_famShape hS hU hU0
  have hn := d.ncard_codeRoots c
  rcases hsh with h | h | h | h | h | h
  · have := (famF4_pairShape_rankCard h).2
    omega
  · have := (famF4_longA2Shape_rankCard h).2
    omega
  · have := (famF4_shortA2Shape_rankCard h).2
    omega
  · have := (famF4_b2Shape_rankCard h).2
    omega
  · have := (famF4_b3Shape_rankCard h).2
    omega
  · have := (famF4_c3Shape_rankCard h).2
    omega


theorem nonempty_rationalPoints_equiv_perm (hS : NegLangTwo S) {c : Finset (ExcRaw.Root 0)}
    (hc : ∃ U, ExcRaw.occurs 0 U c) (h4 : c.card = 4) :
    Nonempty (↥(rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model) ≃* Equiv.Perm (Fin 6)) := by
  classical
  obtain ⟨U, hU⟩ := hc
  obtain ⟨A, a, j, hT, hj, hsh⟩ :=
    d.exists_famShape hS hU (ExcRaw.ne_bot_of_occurs_zero hU (by omega))
  have hn := d.ncard_codeRoots c
  have hB2 : FamF4B2Shape (codeRoots d.γ c) := by
    rcases hsh with h | h | h | h | h | h
    · have := (famF4_pairShape_rankCard h).2
      omega
    · have := (famF4_longA2Shape_rankCard h).2
      omega
    · have := (famF4_shortA2Shape_rankCard h).2
      omega
    · exact h
    · have := (famF4_b3Shape_rankCard h).2
      omega
    · have := (famF4_c3Shape_rankCard h).2
      omega
  have : CharP L 2 := hS.charP
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) L := hS.isAlgebraic
  have hstable : (fun γ => S.ρ γ) '' componentRoots (famCharHom a) j =
      componentRoots (famCharHom a) j := by
    rw [hj]
    exact image_rho_codeRoots S d.γ hS.2.2 d.isRoot c
  obtain ⟨κ, hκinj, hκrange⟩ := CFSG.StandardType.F4ExplicitPos.FixedRange.b2_fixedRange L
    (K := ZMod 2) S.D 1 le_rfl (by rw [hS.1, pow_one]) (by simp) S.ρ S.frob j
    (fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ) hstable (hj ▸ hB2)
  rw [hj] at hκrange
  obtain ⟨e⟩ :=
    CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := ZMod 2) (by simp)
  exact ⟨((MonoidHom.ofInjective hκinj).trans (MulEquiv.subgroupCongr hκrange)).symm.trans e⟩

theorem commutator_rationalPoints_eq (hS : NegLangTwo S) {c : Finset (ExcRaw.Root 0)}
    (hc : ∃ U, ExcRaw.occurs 0 U c) (h9 : c.card = 9) :
    ⁅rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model,
        rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model⁆ =
      rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model := by
  classical
  obtain ⟨U, hU⟩ := hc
  obtain ⟨A, a, j, hT, hj, hsh⟩ :=
    d.exists_famShape hS hU (ExcRaw.ne_bot_of_occurs_zero hU (by omega))
  have hn := d.ncard_codeRoots c
  have h3 : FamF4B3Shape (codeRoots d.γ c) ∨ FamF4C3Shape (codeRoots d.γ c) := by
    rcases hsh with h | h | h | h | h | h
    · have := (famF4_pairShape_rankCard h).2
      omega
    · have := (famF4_longA2Shape_rankCard h).2
      omega
    · have := (famF4_shortA2Shape_rankCard h).2
      omega
    · have := (famF4_b2Shape_rankCard h).2
      omega
    · exact Or.inl h
    · exact Or.inr h
  have : CharP L 2 := hS.charP
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) L := hS.isAlgebraic
  have hstable : (fun γ => S.ρ γ) '' componentRoots (famCharHom a) j =
      componentRoots (famCharHom a) j := by
    rw [hj]
    exact image_rho_codeRoots S d.γ hS.2.2 d.isRoot c
  obtain ⟨Φ, -, hΦrange⟩ := CFSG.StandardType.F4ExplicitPos.FixedRange.rankThree_fixedRange L
    (K := ZMod 2) S.D 1 le_rfl (by rw [hS.1, pow_one]) (by simp) S.ρ S.frob j
    (fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ) hstable (hj ▸ h3)
  rw [hj] at hΦrange
  have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple 3 (ZMod 2) (by norm_num)
    (Or.inr (Or.inr ⟨by simp, le_rfl⟩))
  have hperf : commutator ↥(CFSG.Open.StatedSp 3 (ZMod 2)) = ⊤ := Group.isPerfect_def.mp hqs.1
  rw [← hΦrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

end ExcCoordDatum

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end

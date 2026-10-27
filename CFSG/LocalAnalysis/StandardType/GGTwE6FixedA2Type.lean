module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedComponent
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneTypes
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.HardMathSupport.Foote.Proving.RootStringOne
public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.LieType.AlgebraicGroups.RootSL2Centralizer

public noncomputable section

namespace CFSG.StandardType.TwE6FixedA2Type

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.LieType.Steinberg.Adjoint

local instance tableBE6FixA2NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def gamma1 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 0, 0]

@[expose] def gamma2 : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 1, 1, 0]

@[expose] def gamma3 : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 2, 1, 0]

@[expose] def orthRoots : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1], ![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0]]

theorem gamma3_eq : gamma3 = gamma1 + gamma2 := by decide +kernel

theorem fixedA2E6_eq_list :
    fixedA2E6 = [gamma1, gamma2, gamma3, -gamma1, -gamma2, -gamma3] := by decide +kernel

theorem mem_fixedA2E6 {α : Fin Tag.E6.rank → ℤ} : α ∈ fixedA2E6 ↔
    α = gamma1 ∨ α = gamma2 ∨ α = gamma3 ∨ α = -gamma1 ∨ α = -gamma2 ∨ α = -gamma3 := by
  rw [fixedA2E6_eq_list]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

section Roots


theorem isRoot_gamma1 : IsRoot .E6 gamma1 := mem_rootFinset.mp (by decide +kernel)
theorem isRoot_gamma2 : IsRoot .E6 gamma2 := mem_rootFinset.mp (by decide +kernel)
theorem isRoot_gamma3 : IsRoot .E6 gamma3 := mem_rootFinset.mp (by decide +kernel)

theorem isRoot_orthRoots : ∀ α ∈ orthRoots, IsRoot .E6 α := fun α hα =>
  mem_rootFinset.mp (by revert α; decide +kernel)

theorem isRoot_of_mem_fixedA2E6 {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ fixedA2E6) : IsRoot .E6 α :=
  mem_rootFinset.mp (by revert α; decide +kernel)

end Roots

theorem iform_fixedA2E6_orthRoots : ∀ γ ∈ fixedA2E6, ∀ β ∈ orthRoots,
    CFSG.LieType.Steinberg.Adjoint.iform γ β = 0 := by
  decide +kernel

theorem exists_corootPair_gamma1 :
    ∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * corootPair gamma1 (Pi.single i 1) = 1 := by
  decide +kernel

theorem exists_corootPair_gamma2 :
    ∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * corootPair gamma2 (Pi.single i 1) = 1 := by
  decide +kernel

theorem exists_corootPair_gamma3 :
    ∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * corootPair gamma3 (Pi.single i 1) = 1 := by
  decide +kernel

theorem rootChar_zetaVec_eq_one_iff_dotZ3 {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (v : Fin Tag.E6.rank → ZMod 3) (α : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec ζ hζ v) α = 1 ↔ dotZ3 α v = 0 := by
  rw [NoOffE8Five.rootChar_zetaVec]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
    simpa [dotZ3] using congrArg Multiplicative.toAdd h1
  · intro h
    rw [show (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 0 by simpa [dotZ3] using h, ofAdd_zero,
      map_one]

theorem rootChar_zetaVec_plane_iff {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (k : Fin 3 → ZMod 3) (α : Fin Tag.E6.rank → ℤ) :
    (∀ v ∈ {v | ∃ x : Fin 3 → ZMod 3, ∑ i, k i * x i = 0 ∧ v = combC x},
      rootChar (zetaVec ζ hζ v) α = 1) ↔ sigmaTest k α := by
  constructor
  · intro h x hx
    exact (rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ _ α).mp (h _ ⟨x, hx, rfl⟩)
  · intro h v hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact (rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ _ α).mpr (h x hx)

theorem pow_three_eq_one_of_rootChar {L : Type} [Field L] (b : Fin Tag.E6.rank → Lˣ)
    (h1 : rootChar b gamma1 = 1) (h2 : rootChar b gamma2 = 1)
    (horth : ∀ α ∈ orthRoots, rootChar b α = 1) : b ^ 3 = 1 := by
  let r0 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 1]
  let r1 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 1, 1]
  let r2 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 1, 0]
  let r3 : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 1, 0, 0]
  let cf : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
    ![
      ![-1, 1, 2, 1, -1, -2],
      ![-1, 1, -1, 1, -1, 1],
      ![2, -2, -1, 1, -1, 1],
      ![0, 0, 0, 0, 3, 0],
      ![-1, 1, 2, -2, -1, 1],
      ![2, 1, -1, 1, -1, -2]
    ]
  have hr0 : rootChar b r0 = 1 := by
    change rootChar b ![0, 0, 1, 1, 1, 1] = 1
    refine horth _ ?_
    change ![0, 0, 1, 1, 1, 1] ∈
      ![0, 0, 1, 1, 1, 1] :: ![0, 1, 0, 1, 1, 1] :: ![1, 0, 1, 1, 1, 0] ::
        ![1, 1, 1, 1, 0, 0] :: []
    exact List.mem_cons_self
  have hr1 : rootChar b r1 = 1 := by
    change rootChar b ![0, 1, 0, 1, 1, 1] = 1
    refine horth _ ?_
    change ![0, 1, 0, 1, 1, 1] ∈
      ![0, 0, 1, 1, 1, 1] :: ![0, 1, 0, 1, 1, 1] :: ![1, 0, 1, 1, 1, 0] ::
        ![1, 1, 1, 1, 0, 0] :: []
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hr2 : rootChar b r2 = 1 := by
    change rootChar b ![1, 0, 1, 1, 1, 0] = 1
    refine horth _ ?_
    change ![1, 0, 1, 1, 1, 0] ∈
      ![0, 0, 1, 1, 1, 1] :: ![0, 1, 0, 1, 1, 1] :: ![1, 0, 1, 1, 1, 0] ::
        ![1, 1, 1, 1, 0, 0] :: []
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr3 : rootChar b r3 = 1 := by
    change rootChar b ![1, 1, 1, 1, 0, 0] = 1
    refine horth _ ?_
    change ![1, 1, 1, 1, 0, 0] ∈
      ![0, 0, 1, 1, 1, 1] :: ![0, 1, 0, 1, 1, 1] :: ![1, 0, 1, 1, 1, 0] ::
        ![1, 1, 1, 1, 0, 0] :: []
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  have hcombo : ∀ a0 a1 a2 a3 a4 a5 : ℤ,
      rootChar b (a0 • r0 + a1 • r1 + a2 • r2 + a3 • r3 + a4 • gamma1 +
        a5 • gamma2) = 1 := by
    intro a0 a1 a2 a3 a4 a5
    simp only [rootChar_add, rootChar_zsmul]
    simp [hr0, hr1, hr2, hr3, h1, h2]
  have key : ∀ i : Fin Tag.E6.rank, b i ^ 3 = 1 := by
    intro i
    have hv : (3 : ℤ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
        cf i 0 • r0 + cf i 1 • r1 + cf i 2 • r2 + cf i 3 • r3 +
          cf i 4 • gamma1 + cf i 5 • gamma2 := by
      fin_cases i <;> decide +kernel
    have hz3 : rootChar b ((3 : ℤ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = b i ^ 3 := by
      have h3 : (3 : ℤ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
          (3 : ℕ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
        change ((3 : ℕ) : ℤ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
          (3 : ℕ) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
        rw [natCast_zsmul]
      rw [h3]
      exact rootChar_nsmul_single b i 3
    rw [← hz3, hv]
    exact hcombo (cf i 0) (cf i 1) (cf i 2) (cf i 3) (cf i 4) (cf i 5)
  funext i
  simpa using key i

section Twists


theorem twist_mul_of_conj {L : Type} [Field L] {y : ModGL .E6 L} {s₁ s₂ s₃ : Lˣ}
    (h₁ : ∀ A, y * rootSL2 .E6 L gamma1 A * y⁻¹ = rootSL2 .E6 L gamma1
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₂ : ∀ A, y * rootSL2 .E6 L gamma2 A * y⁻¹ = rootSL2 .E6 L gamma2
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₂) A))
    (h₃ : ∀ A, y * rootSL2 .E6 L gamma3 A * y⁻¹ = rootSL2 .E6 L gamma3
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₃) A)) :
    s₃ = s₁ * s₂ := by
  have conj_pinnedX : ∀ (γ : Fin Tag.E6.rank → ℤ) (s : Lˣ),
      (∀ A, y * rootSL2 .E6 L γ A * y⁻¹ = rootSL2 .E6 L γ
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) A)) →
      ∀ c : L, y * pinnedX .E6 L γ c * y⁻¹ = pinnedX .E6 L γ ((s : L) * c) := by
    intro γ s hs c
    have hu : ∀ z : L,
        y * pinnedX .E6 L γ ((pinnedData .E6 γ).2.2 • z) * y⁻¹ =
          pinnedX .E6 L γ ((pinnedData .E6 γ).2.2 • ((s : L) * z)) := by
      intro z
      have h := hs (uSL z)
      rwa [rootSL2_uSL_eq, CFSG.RankThree.PartOne.KLAY.conjSL_diagUnitOne_uSL,
        rootSL2_uSL_eq] at h
    rcases pinnedSign_eq .E6 γ with hε | hε
    · simpa [hε] using hu c
    · simpa [hε] using hu (-c)
  have hX1 := conj_pinnedX gamma1 s₁ h₁
  have hX2 := conj_pinnedX gamma2 s₂ h₂
  have hX3 := conj_pinnedX gamma3 s₃ h₃
  have hne : gamma1 ≠ gamma2 := by decide
  have hne' : gamma1 ≠ -gamma2 := by decide
  have hsum : IsRoot .E6 (gamma1 + gamma2) := by
    rw [← gamma3_eq]
    exact isRoot_gamma3
  have hnoFinset : ∀ p ∈ commCandidates, p ≠ (1, 1) →
      p.1 • gamma1 + p.2 • gamma2 ∉ rootFinset .E6 := by
    decide +kernel
  have hno : ∀ p ∈ commCandidates, p ≠ (1, 1) →
      ¬ IsRoot .E6 (p.1 • gamma1 + p.2 • gamma2) := by
    intro p hp hne1 hr
    exact hnoFinset p hp hne1 (mem_rootFinset.mpr hr)
  obtain ⟨C, hC, hF⟩ :=
    CFSG.HardMathSupport.Foote.Proving.commutator_pinnedX_string_one
      (τ := Tag.E6) (α := gamma1) (β := gamma2) isRoot_gamma1 isRoot_gamma2 hne hne'
        hsum hno
  have hC1 : 1 ≤ |C| := hC.1
  have hC2 : |C| ≤ 1 := by
    simpa [RootOps.commConstBound] using hC.2
  have hCabs : |C| = 1 := le_antisymm hC2 hC1
  have hCpm : C = 1 ∨ C = -1 := (abs_eq (zero_le_one' ℤ)).1 hCabs
  have hCne : (C : L) ≠ 0 := by
    rcases hCpm with h | h <;> rw [h] <;> norm_num
  have hmul : ∀ a b : ModGL .E6 L,
      y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by
    intro a b
    group
  have hcomm := hF L 1 1
  rw [← gamma3_eq] at hcomm
  have hconj := congrArg (fun z : ModGL .E6 L => y * z * y⁻¹) hcomm
  rw [hmul, hmul, hmul] at hconj
  rw [hX1, hX1, hX2, hX2, hX3] at hconj
  simp only [mul_neg, mul_one] at hconj
  have hB := hF L (s₁ : L) (s₂ : L)
  rw [← gamma3_eq] at hB
  have hEq : (C : L) * (s₁ : L) * (s₂ : L) = (s₃ : L) * (C : L) :=
    pinnedX_injective .E6 L gamma3 (hB.symm.trans hconj)
  have hfield : (s₁ : L) * (s₂ : L) = (s₃ : L) := by
    refine mul_left_cancel₀ hCne ?_
    calc (C : L) * ((s₁ : L) * (s₂ : L))
        = (C : L) * (s₁ : L) * (s₂ : L) := by ring
      _ = (s₃ : L) * (C : L) := hEq
      _ = (C : L) * (s₃ : L) := by ring
  apply Units.ext
  simpa [Units.val_mul] using hfield.symm

theorem rootSpan_fixedA2_le_centralizer {L : Type} [Field L] {y : ModGL .E6 L}
    (h₁ : ∀ A, y * rootSL2 .E6 L gamma1 A = rootSL2 .E6 L gamma1 A * y)
    (h₂ : ∀ A, y * rootSL2 .E6 L gamma2 A = rootSL2 .E6 L gamma2 A * y)
    (h₃ : ∀ A, y * rootSL2 .E6 L gamma3 A = rootSL2 .E6 L gamma3 A * y) :
    rootSpan .E6 L {α | α ∈ fixedA2E6} ≤ Subgroup.centralizer {y} := by
  have hcent (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ)
      (h : ∀ A, y * rootSL2 .E6 L γ A = rootSL2 .E6 L γ A * y) :
      rootSubgroup .E6 L γ ≤ Subgroup.centralizer ({y} : Set (ModGL .E6 L)) ∧
        rootSubgroup .E6 L (-γ) ≤
          Subgroup.centralizer ({y} : Set (ModGL .E6 L)) := by
    have hL := (exceptional_Lang_root_rank_one_torus_transport .E6 L hγ).1
    constructor
    · intro g hg
      have hg' : g ∈ rootRankOneGroup .E6 L γ := by
        rw [hL]
        exact Subgroup.mem_sup_left hg
      change g ∈ (rootSL2 .E6 L γ).range at hg'
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hg'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h A).symm
    · intro g hg
      have hg' : g ∈ rootRankOneGroup .E6 L γ := by
        rw [hL]
        exact Subgroup.mem_sup_right hg
      change g ∈ (rootSL2 .E6 L γ).range at hg'
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hg'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h A).symm
  have hc1 := hcent gamma1 isRoot_gamma1 h₁
  have hc2 := hcent gamma2 isRoot_gamma2 h₂
  have hc3 := hcent gamma3 isRoot_gamma3 h₃
  simp only [rootSpan]
  refine iSup₂_le ?_
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  rw [mem_fixedA2E6] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hc1.1, hc2.1, hc3.1, hc1.2, hc2.2, hc3.2]

end Twists

section RankOne

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.E6Descent CFSG.ComponentClassification.CatalogueBPrimeJoin

variable
  {Ω : Type} [Field Ω]

theorem rootSL2_mem_closedIdentityComponent [IsAlgClosed Ω] {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) {Hh : Subgroup (ModGL Tag.E6 Ω)}
    (hcomm : ∀ h ∈ Hh, ∀ A, h * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * h) (A : SL2 Ω) :
    rootSL2 .E6 Ω γ A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
  exact CFSG.LieType.AlgebraicGroups.rootSL2_mem_closedIdentityComponent_of_commute
    hγ hcomm A

open CFSG.RankThree.PartOne.KE in
theorem isQuasisimple_jgeom_of_rootPair {Fr : Ω →+* Ω} {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) {ℓ₁ : Label Tag.E6}
    (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * corootPair γ (Pi.single i 1) = 1)
    (hγH : ∀ h ∈ Hh.map (MulAut.conj y₀).toMonoidHom, ∀ A,
      h * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * h)
    (hfam : ∀ z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer
      ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))),
      z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {γ, -γ})
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) {be : Fin Tag.E6.rank → Ωˣ}
    (heT : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 be) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hιK : ∀ A, rootSL2 .E6 Ω γ A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
        Set (ModGL Tag.E6 Ω))) :=
    rootSL2_mem_closedIdentityComponent hγ hγH
  have hspan : rootSpan Tag.E6 Ω {γ, -γ} = rootRankOneGroup Tag.E6 Ω γ := by
    rw [rootSpan, iSup_insert, iSup_singleton,
      (exceptional_Lang_root_rank_one_torus_transport Tag.E6 Ω hγ).1]
  have hKT : ∀ z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer
      ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))),
      ∃ b : Fin Tag.E6.rank → Ωˣ, ∃ c : Ωˣ,
        (∀ A, rootDiagUnit Tag.E6 b * rootSL2 .E6 Ω γ A * (rootDiagUnit Tag.E6 b)⁻¹ =
          rootSL2 .E6 Ω γ
            (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) A)) ∧
        ∃ A, z = rootDiagUnit Tag.E6 b * rootSL2 .E6 Ω γ A := by
    intro z hz
    have h := hfam z hz
    rw [hspan, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootRankOneGroup hγ)] at h
    obtain ⟨t', ht', r, ⟨A, rfl⟩, rfl⟩ := h
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'
    exact ⟨b, rootChar b γ, fun A' => CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b hγ A',
      A, rfl⟩
  exact TwE6FixedComponent.isQuasisimple_jgeom_of_torusFrame hn hk hFr hHF hy₀
    (rootSL2 .E6 Ω γ) (CFSG.RankThree.Chevalley.rootSL2_injective_of_field γ) hιK
    (fun i => corootPair γ (Pi.single i 1)) (rootSL2_HSL_eq hγ) hℓ₁ hKT heK heF he1 he3 hgK hgF
    hg2 hinv heT (fun A => CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 be hγ A)

theorem rootDiagUnit_commute_rootSL2_iff {L : Type} [Field L] (b : Fin Tag.E6.rank → Lˣ)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) :
    rootDiagUnit .E6 b * rootSL2 .E6 L α (uSL 1) = rootSL2 .E6 L α (uSL 1) * rootDiagUnit .E6 b ↔
      rootChar b α = 1 := by
  have hc := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 (K := L) b hα (uSL 1)
  rw [CFSG.RankThree.PartOne.KLAY.conjSL_diagUnitOne_uSL, mul_one] at hc
  constructor
  · intro h
    have h' : rootSL2 .E6 L α (uSL ((rootChar b α : Lˣ) : L)) = rootSL2 .E6 L α (uSL 1) := by
      rw [← hc, h, mul_inv_cancel_right]
    have h2 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 1)
      (CFSG.RankThree.Chevalley.rootSL2_injective_of_field α h')
    simp only [uSL] at h2
    exact Units.val_eq_one.mp (by simpa using h2)
  · intro h
    rw [h, Units.val_one] at hc
    calc rootDiagUnit .E6 b * rootSL2 .E6 L α (uSL 1) =
        (rootDiagUnit .E6 b * rootSL2 .E6 L α (uSL 1) * (rootDiagUnit .E6 b)⁻¹) *
          rootDiagUnit .E6 b := by group
      _ = rootSL2 .E6 L α (uSL 1) * rootDiagUnit .E6 b := by rw [hc]

theorem commute_twist_of_mem_closedIdentityComponent [IsAlgClosed Ω]
    {H' : Subgroup (ModGL Tag.E6 Ω)} {x : ModGL Tag.E6 Ω} (hxM : x ∈ monomialSubgroup Tag.E6 Ω)
    (hxc : weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ = cE6) (hxH : x ∈ H')
    (hKS : ∀ z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))),
      z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6})
    {b : Fin Tag.E6.rank → Ωˣ}
    (hx'S : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤
      Subgroup.centralizer {(rootDiagUnit Tag.E6 b)⁻¹ * x})
    {z : ModGL Tag.E6 Ω} (hz : z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω)))) :
    z * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * z := by
  classical
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  set U := rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} with hU
  set τ := rootDiagUnit Tag.E6 b with hτ
  set x' := τ⁻¹ * x with hx'
  set w := weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ with hw
  have hTc : ∀ a a' : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 a' =
        rootDiagUnit Tag.E6 a' * rootDiagUnit Tag.E6 a := fun a a' => by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      mul_comm]
  have hTU : torusGroup Tag.E6 Ω ≤ Subgroup.normalizer (U : Set (ModGL Tag.E6 Ω)) :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
      (fun α hα => isRoot_of_mem_fixedA2E6 hα)
  have hxz : ∀ z ∈ K', x * z = z * x := fun z hz =>
    Subgroup.mem_centralizer_iff.1 (closedIdentityComponent_le _ hz).2 x hxH
  have hwS : ∀ γ ∈ fixedA2E6, w⁻¹ • γ = γ := fun γ hγ => by
    rw [inv_smul_eq_iff]
    show γ = w • γ
    rw [hxc, cE6_smul, cAct_fixedA2E6 γ hγ]
  have hUorth : ∀ δ ∈ orthRoots, U ≤ Subgroup.centralizer {rootSL2 .E6 Ω δ (uSL 1)} := by
    intro δ hδ
    have hδr := isRoot_orthRoots δ hδ
    have hc : ∀ γ (hγ : γ ∈ fixedA2E6) A, rootSL2 .E6 Ω δ (uSL 1) * rootSL2 .E6 Ω γ A =
        rootSL2 .E6 Ω γ A * rootSL2 .E6 Ω δ (uSL 1) := fun γ hγ A =>
      (commute_rootSL2_of_iform_eq_zero (Or.inr (Or.inl rfl)) hδr (isRoot_of_mem_fixedA2E6 hγ)
        ((iform_comm _ _).trans (iform_fixedA2E6_orthRoots γ hγ δ hδ)) (uSL 1) A).eq
    exact rootSpan_fixedA2_le_centralizer (hc _ (mem_fixedA2E6.2 (Or.inl rfl)))
      (hc _ (mem_fixedA2E6.2 (Or.inr (Or.inl rfl))))
      (hc _ (mem_fixedA2E6.2 (Or.inr (Or.inr (Or.inl rfl)))))
  have hφ : ∀ z ∈ K', ∃ β : Fin Tag.E6.rank → Ωˣ, β ^ 3 = 1 ∧
      x' * z * x'⁻¹ * z⁻¹ = rootDiagUnit Tag.E6 β := by
    intro z hz
    have hzx := hxz z hz
    have hzU := hKS z hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTU] at hzU
    obtain ⟨t', ht', u, hu, rfl⟩ := hzU
    obtain ⟨bt, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'
    have hux : u * x' = x' * u := Subgroup.mem_centralizer_singleton_iff.1 (hx'S hu)
    have hconj : x * rootDiagUnit Tag.E6 bt * x⁻¹ = rootDiagUnit Tag.E6 (weylTuple w bt) := by
      have h := conj_rootDiagUnit_of_mem_monoHat (x := ⟨x, monomial_le_monoHat hxM⟩) bt
      rw [psiHat_of_mem_monomial hxM] at h
      exact h
    have hx't : x' * rootDiagUnit Tag.E6 bt * x'⁻¹ = rootDiagUnit Tag.E6 (weylTuple w bt) := by
      calc x' * rootDiagUnit Tag.E6 bt * x'⁻¹ =
          τ⁻¹ * (x * rootDiagUnit Tag.E6 bt * x⁻¹) * τ := by rw [hx']; group
        _ = τ⁻¹ * (rootDiagUnit Tag.E6 (weylTuple w bt) * τ) := by rw [hconj, mul_assoc]
        _ = rootDiagUnit Tag.E6 (weylTuple w bt) := by
          rw [hτ, hTc, inv_mul_cancel_left]
    set β := weylTuple w bt * bt⁻¹ with hβ
    have hφT : x' * (rootDiagUnit Tag.E6 bt * u) * x'⁻¹ * (rootDiagUnit Tag.E6 bt * u)⁻¹ =
        rootDiagUnit Tag.E6 β := by
      have hu' : x' * u * x'⁻¹ = u := by rw [← hux, mul_inv_cancel_right]
      calc x' * (rootDiagUnit Tag.E6 bt * u) * x'⁻¹ * (rootDiagUnit Tag.E6 bt * u)⁻¹ =
          (x' * rootDiagUnit Tag.E6 bt * x'⁻¹) * (x' * u * x'⁻¹) * u⁻¹ *
            (rootDiagUnit Tag.E6 bt)⁻¹ := by group
        _ = rootDiagUnit Tag.E6 (weylTuple w bt) * (rootDiagUnit Tag.E6 bt)⁻¹ := by
          rw [hx't, hu', mul_inv_cancel_right]
        _ = rootDiagUnit Tag.E6 β := by
          rw [hβ, CFSG.LieType.Chevalley.rootDiagUnit_mul,
            CFSG.LieType.Chevalley.rootDiagUnit_inv]
    have hφU : rootDiagUnit Tag.E6 β ∈ U := by
      rw [← hφT]
      have hzx' : x' * (rootDiagUnit Tag.E6 bt * u) * x'⁻¹ = τ⁻¹ * (rootDiagUnit Tag.E6 bt * u) * τ := by
        calc x' * (rootDiagUnit Tag.E6 bt * u) * x'⁻¹ =
            τ⁻¹ * (x * (rootDiagUnit Tag.E6 bt * u)) * x⁻¹ * τ := by rw [hx']; group
          _ = τ⁻¹ * ((rootDiagUnit Tag.E6 bt * u) * x) * x⁻¹ * τ := by rw [hzx]
          _ = τ⁻¹ * (rootDiagUnit Tag.E6 bt * u) * τ := by group
      have hτt : τ⁻¹ * rootDiagUnit Tag.E6 bt = rootDiagUnit Tag.E6 bt * τ⁻¹ := by
        rw [hτ, CFSG.LieType.Chevalley.rootDiagUnit_inv, hTc]
      have e : τ⁻¹ * (rootDiagUnit Tag.E6 bt * u) * τ * (rootDiagUnit Tag.E6 bt * u)⁻¹ =
          rootDiagUnit Tag.E6 bt * ((τ⁻¹ * u * τ⁻¹⁻¹) * u⁻¹) * (rootDiagUnit Tag.E6 bt)⁻¹ := by
        calc τ⁻¹ * (rootDiagUnit Tag.E6 bt * u) * τ * (rootDiagUnit Tag.E6 bt * u)⁻¹ =
            (τ⁻¹ * rootDiagUnit Tag.E6 bt) * u * τ * u⁻¹ * (rootDiagUnit Tag.E6 bt)⁻¹ := by
              group
          _ = (rootDiagUnit Tag.E6 bt * τ⁻¹) * u * τ * u⁻¹ * (rootDiagUnit Tag.E6 bt)⁻¹ := by
              rw [hτt]
          _ = _ := by group
      rw [hzx', e]
      have hτU : τ⁻¹ * u * τ⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1
        (hTU (inv_mem (rootDiagUnit_mem_torusGroup b))) u).1 hu
      exact (Subgroup.mem_normalizer_iff.1 (hTU (rootDiagUnit_mem_torusGroup bt)) _).1
        (mul_mem hτU (inv_mem hu))
    refine ⟨β, pow_three_eq_one_of_rootChar β ?_ ?_ ?_, hφT⟩
    · have h := rootChar_weylTuple w bt gamma1
      rw [hwS _ (mem_fixedA2E6.2 (Or.inl rfl))] at h
      simp only [hβ, rootChar, Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow,
        Finset.prod_mul_distrib, Finset.prod_inv_distrib] at h ⊢
      rw [h, mul_inv_cancel]
    · have h := rootChar_weylTuple w bt gamma2
      rw [hwS _ (mem_fixedA2E6.2 (Or.inr (Or.inl rfl)))] at h
      simp only [hβ, rootChar, Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow,
        Finset.prod_mul_distrib, Finset.prod_inv_distrib] at h ⊢
      rw [h, mul_inv_cancel]
    · intro δ hδ
      exact (rootDiagUnit_commute_rootSL2_iff β (isRoot_orthRoots δ hδ)).1
        (Subgroup.mem_centralizer_singleton_iff.1 (hUorth δ hδ hφU))
  choose! β hβ3 hβeq using hφ
  set M := Subgroup.centralizer ({x'} : Set (ModGL Tag.E6 Ω)) with hM
  have hcube : ∀ y : K', ∀ i, β y i ^ 3 = 1 := fun y i => by
    simpa using congrFun (hβ3 y y.2) i
  have key : ∀ z₁ z₂ : K', β z₁ = β z₂ →
      (QuotientGroup.mk z₁ : K' ⧸ M.subgroupOf K') = QuotientGroup.mk z₂ := by
    intro z₁ z₂ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have e : x' * (z₁ : ModGL Tag.E6 Ω) * x'⁻¹ * (z₁ : ModGL Tag.E6 Ω)⁻¹ =
        x' * z₂ * x'⁻¹ * (z₂ : ModGL Tag.E6 Ω)⁻¹ := by
      rw [hβeq z₁ z₁.2, hβeq z₂ z₂.2, h]
    have e' : x'⁻¹ * ((z₁ : ModGL Tag.E6 Ω)⁻¹ * z₂) = ((z₁ : ModGL Tag.E6 Ω)⁻¹ * z₂) * x'⁻¹ := by
      calc x'⁻¹ * ((z₁ : ModGL Tag.E6 Ω)⁻¹ * z₂) =
          (z₁ : ModGL Tag.E6 Ω)⁻¹ * x'⁻¹ * (x' * z₁ * x'⁻¹ * (z₁ : ModGL Tag.E6 Ω)⁻¹) * z₂ := by
            group
        _ = (z₁ : ModGL Tag.E6 Ω)⁻¹ * x'⁻¹ * (x' * z₂ * x'⁻¹ * (z₂ : ModGL Tag.E6 Ω)⁻¹) * z₂ := by
            rw [e]
        _ = ((z₁ : ModGL Tag.E6 Ω)⁻¹ * z₂) * x'⁻¹ := by group
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Commute.inv_left (e' : Commute x'⁻¹ _)).eq.symm
  let f : (Fin Tag.E6.rank → rootsOfUnity 3 Ω) → K' ⧸ M.subgroupOf K' := fun p =>
    if hp : ∃ y : K', ∀ i, β y i = (p i : Ωˣ) then QuotientGroup.mk (Classical.choose hp)
    else QuotientGroup.mk 1
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    let p : Fin Tag.E6.rank → rootsOfUnity 3 Ω := fun i =>
      ⟨β y i, (mem_rootsOfUnity _ _).2 (hcube y i)⟩
    have hp : ∃ y' : K', ∀ i, β y' i = (p i : Ωˣ) := ⟨y, fun i => rfl⟩
    refine ⟨p, ?_⟩
    change (if hp : ∃ y' : K', ∀ i, β y' i = (p i : Ωˣ) then
      QuotientGroup.mk (Classical.choose hp) else QuotientGroup.mk 1) = _
    rw [dif_pos hp]
    exact key _ _ (funext (Classical.choose_spec hp))
  have : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective f hf
  have : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hKM : closedIdentityComponent K' ≤ M :=
    closedIdentityComponent_le_of_isPointClosed_finiteIndex (isPointClosed_centralizer _)
  rw [closedIdentityComponent_eq_self (isPointIrreducible_closedIdentityComponent _)] at hKM
  have h1 : z * x' = x' * z := Subgroup.mem_centralizer_singleton_iff.1 (hKM hz)
  have h2 : x * z = z * x := hxz z hz
  have hτx : τ = x * x'⁻¹ := by rw [hx']; group
  rw [hτx]
  calc z * (x * x'⁻¹) = (z * x) * x'⁻¹ := by group
    _ = (x * z) * x'⁻¹ := by rw [h2]
    _ = x * x'⁻¹ * (x' * z) * x'⁻¹ := by group
    _ = x * x'⁻¹ * (z * x') * x'⁻¹ := by rw [h1]
    _ = x * x'⁻¹ * z := by group

end RankOne

section FixedType

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.E6Descent CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.HardMathSupport.Timmesfeld.Torality

variable
  {Ω : Type} [Field Ω]

theorem mem_torus_sup_plane_of_mem_closedIdentityComponent [IsAlgClosed Ω] {ζ : Ωˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (k : Fin 3 → ZMod 3)
    {H' : Subgroup (ModGL Tag.E6 Ω)}
    (ha : ∀ v ∈ {v | ∃ x : Fin 3 → ZMod 3, ∑ i, k i * x i = 0 ∧ v = combC x},
      rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ H')
    {z : ModGL Tag.E6 Ω} (hz : z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω)))) :
    z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | IsRoot .E6 α ∧ sigmaTest k α} := by
  let Hs : Set (Fin Tag.E6.rank → ZMod 3) :=
    {v | ∃ x : Fin 3 → ZMod 3, ∑ i, k i * x i = 0 ∧ v = combC x}
  let a : Hs → Fin Tag.E6.rank → Ωˣ := fun v => zetaVec ζ hζ v.1
  have hkerA : familyKernel a = {α | IsRoot .E6 α ∧ sigmaTest k α} := by
    ext α
    change (IsRoot .E6 α ∧ ∀ v : Hs, rootChar (a v) α = 1) ↔
      (IsRoot .E6 α ∧ sigmaTest k α)
    rw [← rootChar_zetaVec_plane_iff hζo hζ k α]
    exact and_congr_right fun _ =>
      ⟨fun h v hv => h ⟨v, hv⟩, fun h v => h v v.2⟩
  have h := closedIdentityComponent_le_familyGroup_inf_centralizer a (fun v => ha v.1 v.2) hz
  have h1 : z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (familyKernel a) := h.1
  rwa [hkerA] at h1

theorem exists_planeKey_and_connected_centralizer_le_rank_three [IsAlgClosed Ω] {ζ : Ωˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {E : Subgroup (ModGL .E6 Ω)}
    (hEM : E ≤ monomialSubgroup .E6 Ω) [Finite E] (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hEA : ∀ w, w ∈ Subgroup.zpowers cE6 ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 Ω ⟨e, hEM he⟩ = w) :
    ∃ k : Fin 3 → ZMod 3, k ≠ 0 ∧
      (∀ v, v ∈ expE ζ hζ E ↔ ∃ x : Fin 3 → ZMod 3,
        ∑ i, k i * x i = 0 ∧ v = combC x) ∧
      closedIdentityComponent (adjointGroup .E6 Ω ⊓
        Subgroup.centralizer (E : Set (ModGL .E6 Ω))) ≤
        torusGroup .E6 Ω ⊔ rootSpan .E6 Ω {α | IsRoot .E6 α ∧ sigmaTest k α} := by
  obtain ⟨k, hk0, hk⟩ := exists_planeKey_of_zpowers_c_rank_three hζo hζ hEM hE hcard hEA
  refine ⟨k, hk0, hk, fun z hz => ?_⟩
  refine mem_torus_sup_plane_of_mem_closedIdentityComponent hζo hζ k (fun v hv => ?_) hz
  exact mem_expE.mp ((hk v).mpr hv)

theorem connected_centralizer_rank_three_cases [IsAlgClosed Ω] {ζ : Ωˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {E : Subgroup (ModGL .E6 Ω)}
    (hEM : E ≤ monomialSubgroup .E6 Ω) [Finite E] (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hEA : ∀ w, w ∈ Subgroup.zpowers cE6 ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 Ω ⟨e, hEM he⟩ = w) :
    let C := closedIdentityComponent (adjointGroup .E6 Ω ⊓
      Subgroup.centralizer (E : Set (ModGL .E6 Ω)))
    C ≤ torusGroup .E6 Ω ∨
    (∃ β ∈ rootFinset .E6,
      iform β (cAct β) = 0 ∧ iform β (cAct (cAct β)) = 0 ∧
      iform (cAct β) (cAct (cAct β)) = 0 ∧
      C ≤ torusGroup .E6 Ω ⊔ rootSpan .E6 Ω
        {α | α ∈ [β, -β, cAct β, -cAct β, cAct (cAct β), -cAct (cAct β)]}) ∨
    C ≤ torusGroup .E6 Ω ⊔ rootSpan .E6 Ω {α | α ∈ fixedA2E6} ∨
    C ≤ torusGroup .E6 Ω ⊔ rootSpan .E6 Ω
      {α | IsRoot .E6 α ∧ α + cAct α + cAct (cAct α) = 0} := by
  obtain ⟨k, hk0, _, hC⟩ :=
    exists_planeKey_and_connected_centralizer_le_rank_three hζo hζ hEM hE hcard hEA
  rcases planeTypes_c_all k hk0 with h | ⟨β, hβ, hroots, h1, h2, h3, _⟩ | h | ⟨_, h⟩
  · left
    have hempty : {α | IsRoot .E6 α ∧ sigmaTest k α} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hα => h α (mem_rootFinset.mpr hα)
    simpa [hempty, rootSpan] using hC
  · refine Or.inr (Or.inl ⟨β, (Finset.mem_filter.mp hβ).1, h1, h2, h3, ?_⟩)
    apply hC.trans
    apply sup_le_sup_left
    apply rootSpan_mono
    intro α hα
    simpa only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] using
      (hroots α (mem_rootFinset.mpr hα.1)).mp hα.2
  · refine Or.inr (Or.inr (Or.inl (hC.trans (sup_le_sup_left (rootSpan_mono ?_) _))))
    intro α hα
    rcases h with rfl | rfl
    · exact (sigmaTest_fixed α (mem_rootFinset.mpr hα.1)).1.mp hα.2
    · exact (sigmaTest_fixed α (mem_rootFinset.mpr hα.1)).2.mp hα.2
  · refine Or.inr (Or.inr (Or.inr (hC.trans (sup_le_sup_left (rootSpan_mono ?_) _))))
    intro α hα
    exact ⟨hα.1, (h α (mem_rootFinset.mpr hα.1)).mp hα.2⟩

theorem isRoot_and_rootChar_zetaVec_iff {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (α : Fin Tag.E6.rank → ℤ) :
    (IsRoot .E6 α ∧ ∀ v ∈ {v | ∃ x' : Fin 3 → ZMod 3, x' 0 = 0 ∧ v = combC x'},
      rootChar (zetaVec ζ hζ v) α = 1) ↔ α ∈ fixedA2E6 := by
  constructor
  · rintro ⟨hα, h⟩
    refine ((sigmaTest_fixed α (mem_rootFinset.mpr hα)).1).1 fun x' hx' => ?_
    have hx0 : x' 0 = 0 := by simpa [Fin.sum_univ_three] using hx'
    exact (rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ _ α).1 (h _ ⟨x', hx0, rfl⟩)
  · intro hα
    refine ⟨isRoot_of_mem_fixedA2E6 hα, ?_⟩
    rintro v ⟨x', hx0, rfl⟩
    have hs := ((sigmaTest_fixed α (mem_rootFinset.mpr (isRoot_of_mem_fixedA2E6 hα))).1).2 hα
    exact (rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ _ α).2
      (hs x' (by simp [Fin.sum_univ_three, hx0]))

theorem mem_torus_sup_fixedA2_of_mem_closedIdentityComponent [IsAlgClosed Ω] {ζ : Ωˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {H' : Subgroup (ModGL Tag.E6 Ω)}
    (ha : ∀ v ∈ {v | ∃ x' : Fin 3 → ZMod 3, x' 0 = 0 ∧ v = combC x'},
      rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ H')
    {z : ModGL Tag.E6 Ω} (hz : z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω)))) :
    z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} := by
  have h := mem_torus_sup_plane_of_mem_closedIdentityComponent hζo hζ ![1, 0, 0]
    (fun v hv => ha v (by simpa [Fin.sum_univ_three] using hv)) hz
  have hkerA : {α | IsRoot .E6 α ∧ sigmaTest ![1, 0, 0] α} = {α | α ∈ fixedA2E6} := by
    ext α
    exact ⟨fun h => (sigmaTest_fixed α (mem_rootFinset.mpr h.1)).1.mp h.2,
      fun h => ⟨isRoot_of_mem_fixedA2E6 h,
        (sigmaTest_fixed α (mem_rootFinset.mpr (isRoot_of_mem_fixedA2E6 h))).1.mpr h⟩⟩
  rwa [hkerA] at h

theorem isQuasisimple_jgeom_or_centralizes_fixedA2 {Fr : Ω →+* Ω}
    {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω) {x : ModGL Tag.E6 Ω}
    (hxM : x ∈ monomialSubgroup Tag.E6 Ω) (hxc : weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ = cE6)
    {ζ : Ωˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (hHgen : Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
      ((fun v => rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) ''
        {v | ∃ x', x' 0 = 0 ∧ v = combC x'} ∪ {x}))
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) {be : Fin Tag.E6.rank → Ωˣ}
    (heT : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 be) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) ∨
    rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ Subgroup.centralizer {x} := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  set Hs : Set (Fin Tag.E6.rank → ZMod 3) := {v | ∃ x', x' 0 = 0 ∧ v = combC x'} with hHs
  have ha : ∀ v ∈ Hs, rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ H' := fun v hv => by
    rw [hHgen]
    exact Subgroup.subset_closure (Set.mem_union_left _ ⟨v, hv, rfl⟩)
  have hxH : x ∈ H' := by
    rw [hHgen]
    exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hSig : ∀ α, (IsRoot .E6 α ∧ ∀ v ∈ Hs, rootChar (zetaVec ζ hζ v) α = 1) ↔
      α ∈ fixedA2E6 := isRoot_and_rootChar_zetaVec_iff hζo hζ
  have hKS : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} :=
    fun z hz => mem_torus_sup_fixedA2_of_mem_closedIdentityComponent hζo hζ ha hz
  have hmaps := mapsRootLines_weylQuotientHom (R := Ω) ⟨x, hxM⟩
  have hfix : ∀ γ ∈ fixedA2E6, weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • γ = γ := fun γ hγ => by
    rw [hxc, cE6_smul]
    exact cAct_fixedA2E6 γ hγ
  have hm1 : gamma1 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inl rfl)
  have hm2 : gamma2 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inr (Or.inl rfl))
  have hm3 : gamma3 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨s₁, hs₁⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma1
    (hfix gamma1 hm1)
  obtain ⟨s₂, hs₂⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma2
    (hfix gamma2 hm2)
  obtain ⟨s₃, hs₃⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma3
    (hfix gamma3 hm3)
  have hs₁₂ : s₃ = s₁ * s₂ := twist_mul_of_conj hs₁ hs₂ hs₃
  have hcx : ∀ γ, (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne 1) A)) →
      ∀ A, x * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * x := by
    intro γ h A
    have h' := h A
    rw [CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one] at h'
    calc x * rootSL2 .E6 Ω γ A = (x * rootSL2 .E6 Ω γ A * x⁻¹) * x := by group
      _ = rootSL2 .E6 Ω γ A * x := by rw [h']
  by_cases hs : s₁ = 1 ∧ s₂ = 1
  ·
    right
    obtain ⟨rfl, rfl⟩ := hs
    rw [one_mul] at hs₁₂
    subst hs₁₂
    exact rootSpan_fixedA2_le_centralizer (hcx _ hs₁) (hcx _ hs₂) (hcx _ hs₃)
  left
  set bτ : Fin Tag.E6.rank → Ωˣ := ![1, s₂ * s₁⁻¹, 1, s₁, 1, 1] with hbτ
  have hb1 : rootChar bτ gamma1 = s₁ := by
    change ∏ i : Fin 6, bτ i ^ gamma1 i = s₁
    simp [hbτ, gamma1, Fin.prod_univ_succ]
  have hb2 : rootChar bτ gamma2 = s₂ := by
    change ∏ i : Fin 6, bτ i ^ gamma2 i = s₂
    simp [hbτ, gamma2, Fin.prod_univ_succ]
  have hb3 : rootChar bτ gamma3 = s₃ := by
    rw [gamma3_eq, rootChar_add, hb1, hb2, hs₁₂]
  have hx'c : ∀ γ, IsRoot .E6 γ → ∀ s : Ωˣ, rootChar bτ γ = s →
      (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) A)) →
      ∀ A, (rootDiagUnit Tag.E6 bτ)⁻¹ * x * rootSL2 .E6 Ω γ A =
        rootSL2 .E6 Ω γ A * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by
    intro γ hγ s hbs hxs A
    have h2 := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 bτ hγ A
    rw [hbs] at h2
    calc (rootDiagUnit Tag.E6 bτ)⁻¹ * x * rootSL2 .E6 Ω γ A =
        (rootDiagUnit Tag.E6 bτ)⁻¹ * (x * rootSL2 .E6 Ω γ A * x⁻¹) * rootDiagUnit Tag.E6 bτ *
          ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by group
      _ = (rootDiagUnit Tag.E6 bτ)⁻¹ *
          (rootDiagUnit Tag.E6 bτ * rootSL2 .E6 Ω γ A * (rootDiagUnit Tag.E6 bτ)⁻¹) *
            rootDiagUnit Tag.E6 bτ * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by rw [hxs A, h2]
      _ = rootSL2 .E6 Ω γ A * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by group
  have hUx' : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤
      Subgroup.centralizer {(rootDiagUnit Tag.E6 bτ)⁻¹ * x} :=
    rootSpan_fixedA2_le_centralizer (hx'c _ isRoot_gamma1 s₁ hb1 hs₁)
      (hx'c _ isRoot_gamma2 s₂ hb2 hs₂) (hx'c _ isRoot_gamma3 s₃ hb3 hs₃)
  have hKτ : K' ≤ Subgroup.centralizer ({rootDiagUnit Tag.E6 bτ} : Set (ModGL Tag.E6 Ω)) :=
    fun z hz => Subgroup.mem_centralizer_singleton_iff.2
      (commute_twist_of_mem_closedIdentityComponent hxM hxc hxH hKS hUx' hz)
  set H'' := Subgroup.closure ((H' : Set (ModGL Tag.E6 Ω)) ∪ {rootDiagUnit Tag.E6 bτ}) with hH''
  have hC'' : adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (H'' : Set (ModGL Tag.E6 Ω)) =
      (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E6 bτ} : Set (ModGL Tag.E6 Ω)) := by
    rw [hH'', Subgroup.centralizer_closure, inf_assoc]
    congr 1
    ext z
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
      Set.mem_singleton_iff, or_imp, forall_and, forall_eq, SetLike.mem_coe]
  have hK'' : closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H'' : Set (ModGL Tag.E6 Ω))) = K' := by
    rw [hC'', closedIdentityComponent_inf_eq_of_le _ _ hKτ]
  let a'' : Option Hs → Fin Tag.E6.rank → Ωˣ := fun o =>
    Option.elim o bτ fun v => zetaVec ζ hζ (v : Fin Tag.E6.rank → ZMod 3)
  have ha'' : ∀ o, rootDiagUnit Tag.E6 (a'' o) ∈ H'' := by
    rintro (_ | v)
    · exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
    · exact Subgroup.subset_closure (Set.mem_union_left _ (ha v.1 v.2))
  have hfam'' : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (familyKernel a'') := by
    intro z hz
    rw [← hK''] at hz
    exact (closedIdentityComponent_le_familyGroup_inf_centralizer a'' ha'' hz).1
  have hFK : ∀ α ∈ familyKernel a'', α ∈ fixedA2E6 ∧ rootChar bτ α = 1 := by
    rintro α ⟨hα, hall⟩
    exact ⟨(hSig α).1 ⟨hα, fun v hv => hall (some ⟨v, hv⟩)⟩, hall none⟩
  have hrank1 : ∀ γ, IsRoot .E6 γ → γ ∈ fixedA2E6 →
      (∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * corootPair γ (Pi.single i 1) = 1) →
      (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne 1) A)) →
      (∀ α ∈ familyKernel a'', α = γ ∨ α = -γ) →
      CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
          (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
            Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓
              TwistedDiag.Rgrp Ω Fr).subtype) := by
    rintro γ hγ hγS ⟨ℓ, hℓ, hℓ1⟩ hxγ hsub
    have hγH : ∀ h ∈ H', ∀ A, h * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * h := by
      intro h hh A
      rw [hHgen] at hh
      induction hh using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with ⟨v, hv, rfl⟩ | hy
        · have hc := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 (zetaVec ζ hζ v) hγ A
          rw [((hSig γ).2 hγS).2 v hv, CFSG.RankThree.Chevalley.diagUnitOne_one,
            CFSG.RankThree.Classical.conjSL_one] at hc
          calc rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A =
              (rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A *
                (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹) * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
                group
            _ = rootSL2 .E6 Ω γ A * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [hc]
        · rw [Set.mem_singleton_iff.1 hy]
          exact hcx γ hxγ A
      | one => rw [one_mul, mul_one]
      | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
      | inv y _ hy => exact (Commute.inv_left (hy : Commute y (rootSL2 .E6 Ω γ A))).eq
    have hmono : rootSpan Tag.E6 Ω (familyKernel a'') ≤ rootSpan Tag.E6 Ω {γ, -γ} :=
      biSup_mono fun α hα => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hsub α hα
    exact isQuasisimple_jgeom_of_rootPair hn hk hFr hHF hy₀ hγ
      (ℓ₁ := Sum.inr ⟨ℓ, mem_rootFinset.mp hℓ⟩) hℓ1 hγH
      (fun z hz => sup_le_sup_left hmono _ (hfam'' z hz)) heK heF he1 he3 hgK hgF hg2 hinv heT
  have hneg : ∀ γ, rootChar bτ (-γ) = 1 → rootChar bτ γ = 1 := fun γ h => by
    rwa [CFSG.RankThree.Chevalley.rootChar_neg', inv_eq_one] at h
  by_cases h1 : s₁ = 1
  ·
    have h2 : s₂ ≠ 1 := fun h2 => hs ⟨h1, h2⟩
    refine hrank1 gamma1 isRoot_gamma1 hm1 exists_corootPair_gamma1 (h1 ▸ hs₁) fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd (hb2 ▸ hαb) h2
    · exact absurd (by rw [hb3, hs₁₂, h1, one_mul] at hαb; exact hαb) h2
    · exact Or.inr rfl
    · exact absurd (hb2 ▸ hneg _ hαb) h2
    · exact absurd (by have h' := hneg _ hαb; rw [hb3, hs₁₂, h1, one_mul] at h'; exact h') h2
  by_cases h2 : s₂ = 1
  ·
    refine hrank1 gamma2 isRoot_gamma2 hm2 exists_corootPair_gamma2 (h2 ▸ hs₂) fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hb1 ▸ hαb) h1
    · exact Or.inl rfl
    · exact absurd (by rw [hb3, hs₁₂, h2, mul_one] at hαb; exact hαb) h1
    · exact absurd (hb1 ▸ hneg _ hαb) h1
    · exact Or.inr rfl
    · exact absurd (by have h' := hneg _ hαb; rw [hb3, hs₁₂, h2, mul_one] at h'; exact h') h1
  by_cases h3 : s₁ * s₂ = 1
  ·
    refine hrank1 gamma3 isRoot_gamma3 hm3 exists_corootPair_gamma3 ((hs₁₂.trans h3) ▸ hs₃)
      fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hb1 ▸ hαb) h1
    · exact absurd (hb2 ▸ hαb) h2
    · exact Or.inl rfl
    · exact absurd (hb1 ▸ hneg _ hαb) h1
    · exact absurd (hb2 ▸ hneg _ hαb) h2
    · exact Or.inr rfl
  exfalso
  have hFKe : familyKernel a'' = ∅ := by
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hα
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 (hb1 ▸ hαb)
    · exact h2 (hb2 ▸ hαb)
    · exact h3 (by rw [hb3, hs₁₂] at hαb; exact hαb)
    · exact h1 (hb1 ▸ hneg _ hαb)
    · exact h2 (hb2 ▸ hneg _ hαb)
    · exact h3 (by have h' := hneg _ hαb; rw [hb3, hs₁₂] at h'; exact h')
  have hbot : rootSpan Tag.E6 Ω (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
    simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot]
  have hKT : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω := by
    intro z hz
    have h := hfam'' z hz
    rwa [hFKe, hbot, sup_bot_eq] at h
  have hgT := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ g).2 hgK)
  have heT' := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ e).2 heK)
  obtain ⟨bg, hbg⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
  obtain ⟨be', hbe⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT'
  have hcomm : (y₀ * g * y₀⁻¹) * (y₀ * e * y₀⁻¹) = (y₀ * e * y₀⁻¹) * (y₀ * g * y₀⁻¹) := by
    rw [hbg, hbe, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
  have hge : g * e = e * g := by
    have h := congrArg (fun v => y₀⁻¹ * v * y₀) hcomm
    rw [show y₀⁻¹ * (y₀ * g * y₀⁻¹ * (y₀ * e * y₀⁻¹)) * y₀ = g * e by group,
      show y₀⁻¹ * (y₀ * e * y₀⁻¹ * (y₀ * g * y₀⁻¹)) * y₀ = e * g by group] at h
    exact h
  have hee : e = e⁻¹ := by rw [← hinv, hge, mul_inv_cancel_right]
  apply he1
  have h2e : e ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hee]
    exact mul_inv_cancel e
  calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
    _ = 1 := by rw [he3, h2e]; group

end FixedType

end CFSG.StandardType.TwE6FixedA2Type

end

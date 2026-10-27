module

public import CFSG.RankThree.PartOne.KE.E8EightClasses
public import CFSG.RankThree.PartOne.KE.E8D4SwapFamily
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KE.E8TwelveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise MatrixGroups

section Facts

theorem e8T8_weylImage (u : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd e8T8WW • u = e8T8V *ᵥ u := by
  rw [wordProd_smul_eq_wordMat_mulVec, e8T8WW, wordMat_append, wordMat_append, e8T8V, pow_succ,
    pow_two]
  rfl

end Facts

section PerX

theorem e8_eight_perx (hD4 : D4TranspositionLayer Tag.E8) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : 7 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T8WW)
    (g0 : ModGL .E8 L) (hg0C : g0 ∈ adjointGroup .E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e8T8V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L))
    {x : adjointGroup .E8 K} (hx : orderOf x = p) (c : adjointGroup .E8 K)
    (hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
      ∀ b : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
        (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
          Group.IsSolvable V → ∀ v ∈ V,
            ψ v ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
              (rootCharKernel b)) ∧
        (toVec Tag.E8.rank e8T8Alpha0 ∈ rootCharKernel b →
          ∃ Pt : Subgroup (ModGL .E8 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
            ∃ h₀ : ModGL .E8 L, ∀ Y : SL2 K, h₀ * simpleRootSL2 .E8 L (e8Index 3)
              (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T8V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T8_weylImage u
  set ι : adjointGroup .E8 K →* ModGL .E8 L := adjEmb .E8 K L with hιdef
  set h : ModGL .E8 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E8 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hkd := e8T8_kernel_structure Fr hFr hp hp3 hΦ hb hap hb1
  rcases hkd with hA | ⟨cc, hcc, hker', hgood⟩ | ⟨cc, hcc, hker', hgood⟩
  ·
    have hspan : rootSpan .E8 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    have hfam : IsSigmaFamily n Fr (rootCharKernel b) (fun e : Empty => (e.elim : Subgroup _)) := by
      refine ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
        fun e => e.elim, fun y hy hyR _ => ?_⟩
      rw [hspan, sup_bot_eq] at hy
      refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [hspan] at hg
      have : g = 1 := hg
      rw [this, one_mul, mul_one]
    obtain ⟨ψ, hψinj, hψ, -, -, -, -, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW hx c
      hbh' hh rfl (fun α hα => hα.1)
      (fun α hα => ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩) hfam
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v hv => ?_, fun hα => ?_⟩⟩
    · rw [hker b' hb']
      exact hψV V hVn hVs v hv
    · exfalso
      rw [hker b' hb', hA] at hα
      exact Set.notMem_empty _ hα
  ·
    obtain ⟨hS1, u, hu, hcertw⟩ := D4SwapCert.sound hgood
    obtain ⟨-, -, -, hab, ha, hbl, -⟩ := hgood
    set v : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w with hv
    have hSeq : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8) :=
      hker'.trans hS1
    have hcert : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
        ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
          (v⁻¹ * weylQuotientHom .E8 L ⟨n, hnm⟩ * v) • α =
            u • permLattice (Equiv.swap cc.a cc.b) α := by
      rw [hnW]
      exact ⟨u, hu, hcertw⟩
    obtain ⟨P, hfam, hP1, h₀, hh₀⟩ := e8_d4_swap_family hD4 hf hK v n hnm hnC cc.a cc.b hab
      (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
      hcert
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp
      hordW hx c hbh' hh hSeq (d4Set_isRoot v) (d4Set_neg v) hfam
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v' hv' => ?_, fun _ => ?_⟩⟩
    · rw [hker b' hb', hSeq]
      exact hψV V hVn hVs v' hv'
    · exact ⟨P (), hfam.2.1 (), e8_perx_commutator Fr n (d4Set_isRoot v) ψ hψHQ hψR hP1
        (hPψ ()) (hfam.2.1 ()), h₀, hh₀⟩
  ·
    obtain ⟨r₁, r₂, r₃, r₄, hr₁, hr₂, hr₃, hr₄, m12, m23, m34, m41, o12, o13, o14, o23, o24, o34,
      hset⟩ := FourA1Cert.sound (M := e8T8V) e8T8V_eq hgood
    obtain ⟨P, hfam⟩ := e8_four_A1_family (ℓ := ℓ) hf hnm hr₁ hr₂ hr₃ hr₄
      (by rw [hnWv]; exact m12) (by rw [hnWv]; exact m23) (by rw [hnWv]; exact m34)
      (by rw [hnWv]; exact m41) o12 o13 o14 o23 o24 o34
    have hSeq : rootCharKernel b = fourRootSet r₁ r₂ r₃ r₄ := hker'.trans hset
    obtain ⟨ψ, hψinj, hψ, -, -, -, -, hψV⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW hx c
      hbh' hh hSeq (fourRootSet_isRoot hr₁ hr₂ hr₃ hr₄) fourRootSet_neg hfam
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v' hv' => ?_, fun hα => ?_⟩⟩
    · rw [hker b' hb', hSeq]
      exact hψV V hVn hVs v' hv'
    · exfalso
      have hα' : toVec Tag.E8.rank e8T8Alpha0 ∈ classSetL e8T8Rows cc.cls := by
        rw [← hker', ← hker b' hb']
        exact hα
      obtain ⟨l, hl, hl'⟩ := hα'
      exact e8T8Alpha0_not_fourA1 cc hcc l hl hl'.symm

end PerX

end CFSG.RankThree.PartOne.KE

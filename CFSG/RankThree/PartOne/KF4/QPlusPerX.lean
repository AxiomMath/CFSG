module

public import CFSG.RankThree.PartOne.KF4.QPlusAll
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise commutatorElement


section PerX

variable (K : Type) [Field K] [Finite K] {f : ℕ} {p : ℕ}
  (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem qp_core (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (g0 : ModGL Tag.F4 L) (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * qpRep L)
    (hperf : ∀ P : Subgroup (ModGL Tag.F4 L), Finite P → P ≤ adjointGroup Tag.F4 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L 2 f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.F4 K L).range)
    {x : adjointGroup Tag.F4 K} (hx : orderOf x = p) (c : adjointGroup Tag.F4 K)
    (hh : g0⁻¹ * adjEmb Tag.F4 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))))
    (b : Fin Tag.F4.rank → Lˣ)
    (hb : rootDiagUnit Tag.F4 b = g0⁻¹ * adjEmb Tag.F4 K L (c * x * c⁻¹) * g0)
    (S : Set (Fin Tag.F4.rank → ℤ)) (hSeq : rootCharKernel b = S)
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} (P : ι' → Subgroup (ModGL Tag.F4 L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan Tag.F4 L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints (qpRep L)
      (Units.map (entrywiseHom (iterateFrobenius L 2 f))))
    (hPadj : ∀ i, P i ≤ adjointGroup Tag.F4 L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S,
      y ∈ twistedFixedPoints (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) →
        ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S,
      y ∈ twistedFixedPoints (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) →
        (∀ i, ∀ u ∈ P i, y * u = u * y) →
          y ∈ subtorusSigma (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) S) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.F4 K)) →* ModGL Tag.F4 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb Tag.F4 K L (c * (y : adjointGroup Tag.F4 K) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S) ∧
      (∀ y, qpRep L * Units.map (entrywiseHom (iterateFrobenius L 2 f)) (ψ y) *
        (qpRep L)⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup Tag.F4 L) ∧ (∀ i, P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.F4 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ subtorusSigma (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  set Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.F4) := not_dvd_card_weylGroup_F4 hp hp3
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.F4 L) := rootDiagUnit_injective
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 L := adjEmb Tag.F4 K L with hιdef
  set h : ModGL Tag.F4 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hker : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hb.symm)
    rw [this]
  have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
  have hle := rootSpan_le_centralizer (K := L) b hsub
  have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma (qpRep L) Φ S) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hb] at h1
    exact h1
  have hkerZ : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a = h →
      rootCharKernel a ⊆ S := fun a ha => by rw [hker a ha, hSeq]
  exact sigma_embedding_data ι adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) (qpRep L)
    g0 hg0C hg0 hperf hp hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ

theorem f4_qplus_perx (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ 2 ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (g0 : ModGL Tag.F4 L) (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * qpRep L)
    (hperf : ∀ P : Subgroup (ModGL Tag.F4 L), Finite P → P ≤ adjointGroup Tag.F4 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L 2 f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.F4 K L).range)
    {x : adjointGroup Tag.F4 K} (hx : orderOf x = p) (c : adjointGroup Tag.F4 K)
    (hh : g0⁻¹ * adjEmb Tag.F4 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))))
    {J : Finset (Fin Tag.F4.rank)} (hJu : J ≠ Finset.univ) (b : Fin Tag.F4.rank → Lˣ)
    (hb : rootDiagUnit Tag.F4 b = g0⁻¹ * adjEmb Tag.F4 K L (c * x * c⁻¹) * g0)
    (hJ : rootCharKernel b = parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.F4 K)) →* ModGL Tag.F4 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb Tag.F4 K L (c * (y : adjointGroup Tag.F4 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.F4 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) ∧
      (J.Nonempty → ∃ Pt : Subgroup (ModGL Tag.F4 L), ⁅ψ.range, ψ.range⁆ = Pt ∧
        CFSG.layer ↥Pt = ⊤ ∧ ∃ i : Fin Tag.F4.rank, ∃ h₀ : ModGL Tag.F4 L,
          h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL2 K, h₀ * simpleRootSL2 Tag.F4 L i
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  by_cases hJe : J = ∅
  ·
    subst hJe
    have hempty : rootCharKernel b = ∅ := by
      rw [hJ]
      ext α
      simp only [Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      intro hα
      exact IsRoot.ne_zero hα.1 (funext fun i => hα.2 i (Set.notMem_empty i))
    have hspan : rootSpan Tag.F4 L (rootCharKernel b) = ⊥ := by
      rw [hempty]
      simp [rootSpan]
    have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
      ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, -, hψV⟩ := qp_core K L hK hp hp3 g0 hg0C hg0 hperf
      hx c hh b hb (rootCharKernel b) rfl (fun α hα => hα.1) hrootneg (ι' := Empty)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v hv), fun hne => ?_⟩
    exact absurd rfl (Finset.nonempty_iff_ne_empty.1 hne)
  · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.2 hJe
    obtain ⟨i₀, ι', P, hfam, hP1, hlayer, h₀, hh₀C, hh₀⟩ :=
      qp_family_exists (L := L) (K := K) f hf hK hq J hJe hJu
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := qp_core K L hK hp hp3 g0 hg0C hg0 hperf
      hx c hh b hb _ hJ (fun α hα => hα.1) (fun α hα => neg_mem_parabolicRoots hα) P hPfin hPq
      hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v hv), fun _ => ⟨⨆ i, P i, ?_, hlayer, i₀, h₀, hh₀C, hh₀⟩⟩
    refine commutator_range_eq_of_family ψ (H := torusGroup Tag.F4 L)
      (Q := rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))))
      (R := twistedFixedPoints (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))))
      ?_ ?_ hψHQ (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (iSup_le hPψ) ?_
    · exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1)
    · intro a ha a' ha'
      obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
    · refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (iSup_le fun i => ?_)
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      · calc P i = ⁅P i, P i⁆ := (Subgroup.isPerfect_iff.1 (hPq i).1).symm
          _ ≤ ⁅⨆ i, P i, ⨆ i, P i⁆ := Subgroup.commutator_mono (le_iSup P i) (le_iSup P i)

end PerX

end CFSG.RankThree.PartOne.KF4

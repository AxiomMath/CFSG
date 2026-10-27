module

public import CFSG.RankThree.PartOne.KF4.F4ThreeKernel
public import CFSG.RankThree.PartOne.KF4.F4ThreeFamily
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise


theorem neg_mem_sigmaSetLong (v : WeylGroup Tag.F4) :
    ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j}, -r ∈
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j} := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact ⟨j, i, hij.symm, by rw [f4chainLong_neg i j, smul_neg]⟩

theorem neg_mem_sigmaSetShort (v : WeylGroup Tag.F4) :
    ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j}, -r ∈
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j} := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact ⟨j, i, hij.symm, by rw [f4ShortSigma_neg i j, smul_neg]⟩

theorem isRoot_sigmaSetLong (v : WeylGroup Tag.F4) :
    ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j}, IsRoot Tag.F4 r := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact IsRoot.smul (f4chainLong_mem_parabolicRoots hij).1 v

theorem isRoot_sigmaSetShort (v : WeylGroup Tag.F4) :
    ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j}, IsRoot Tag.F4 r := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact IsRoot.smul (f4ShortSigma_mem_parabolicRoots hij).1 v

theorem f4_three_perx (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hq3 : δ = -1 → 2 < ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (δ • weylMatrix f4W3) *ᵥ u)
    (g0 : ModGL .F4 L) (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .F4 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (f4ThreeM δ) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .F4 L))
    {x : adjointGroup .F4 K} (hx : orderOf x = p) (c : adjointGroup .F4 K)
    (hh : g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ b : Fin Tag.F4.rank → Lˣ,
        rootDiagUnit .F4 b = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 →
        (rootCharKernel b).Nonempty →
        ∃ Pt : Subgroup (ModGL .F4 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
          ∃ i : Fin Tag.F4.rank,
            ((i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3)) ∧
            ∃ h₀ : ModGL .F4 L, h₀ ∈ adjointGroup .F4 L ∧ ∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
              (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓ : ℓ.Prime := Fact.out
  have hordW : ¬ p ∣ Nat.card (WeylGroup .F4) := not_dvd_card_weylGroup_F4 hp hp3
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  set ι : adjointGroup .F4 K →* ModGL .F4 L := adjEmb .F4 K L with hιdef
  set h : ModGL .F4 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .F4 b = h := hbh
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
  have hbp : orderOf (rootDiagUnit .F4 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have core : ∀ (S : Set (Fin Tag.F4.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .F4 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .F4 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .F4 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .F4 L) →
        (∀ i, ∀ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L,
          Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .F4 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .F4 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
            Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) b hsub
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data ι adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0
      hg0C hg0 hperf hp hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
  have hkd := f4Three_kernel_of_fixed δ hδ Fr hFr hp hp3 hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hlong | hshort⟩
  ·
    have hspan : rootSpan .F4 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, -, hψV⟩ := core (rootCharKernel b) rfl
      (fun α hα => hα.1) hrootneg (ι' := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v hv), fun b' hb' hne => ?_⟩
    exfalso
    rw [hker b' hb', hA] at hne
    exact Set.not_nonempty_empty hne
  ·
    obtain ⟨hSeq, hπ⟩ := hlong
    obtain ⟨P, hP, hP1, h₀, hh₀C, hh₀⟩ := f4Three_family_long hℓ hf (k := K) hK δ hδ hq3 Fr hFr'
      n hnm hnW v hπ
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core _ hSeq (isRoot_sigmaSetLong v)
      (neg_mem_sigmaSetLong v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' _ _ => ⟨P (), hPq (), ?_, f4Index 0, Or.inl (Or.inl rfl), h₀,
        hh₀C, hh₀⟩⟩
    refine commutator_range_eq_of_family ψ (H := torusGroup .F4 L)
      (Q := rootSpan .F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j})
      (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
      (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
    · exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (isRoot_sigmaSetLong v)
    · intro a ha a' ha'
      obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
    · exact Subgroup.isPerfect_iff.1 (hPq ()).1
  ·
    obtain ⟨hSeq, hπ⟩ := hshort
    obtain ⟨P, hP, hP1, h₀, hh₀C, hh₀⟩ := f4Three_family_short hℓ hf (k := K) hK δ hδ hq3 Fr hFr'
      n hnm hnW v hπ
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core _ hSeq (isRoot_sigmaSetShort v)
      (neg_mem_sigmaSetShort v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' _ _ => ⟨P (), hPq (), ?_, f4Index 2, Or.inr (Or.inl rfl), h₀,
        hh₀C, hh₀⟩⟩
    refine commutator_range_eq_of_family ψ (H := torusGroup .F4 L)
      (Q := rootSpan .F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j})
      (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
      (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
    · exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (isRoot_sigmaSetShort v)
    · intro a ha a' ha'
      obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
    · exact Subgroup.isPerfect_iff.1 (hPq ()).1

end CFSG.RankThree.PartOne.KF4

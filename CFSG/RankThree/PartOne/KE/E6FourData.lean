module

public import CFSG.RankThree.PartOne.KE.E6FourFamily
public import CFSG.RankThree.PartOne.KE.E6FourArith
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.E6FourKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Matrix MatrixGroups

section PerX

theorem e6_four_perx (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E6 K L (c * (y : adjointGroup .E6 K) * c⁻¹) * g0) ∧
      ∀ b : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 →
        (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), V.Normal →
          Group.IsSolvable V → ∀ v ∈ V,
            ψ v ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
              (rootCharKernel b)) ∧
        ((rootCharKernel b).Nonempty →
          ∃ Pt : Subgroup (ModGL .E6 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
            (∃ h₀ : ModGL .E6 L, ∀ Y : SL2 K, h₀ * simpleRootSL2 .E6 L (e6Index 0)
              (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) ∧
            ∃ v : WeylGroup .E6, rootCharKernel b = sigmaSetE6A3 v ∧
              ∃ H : SL(4, L), ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
                Matrix.SpecialLinearGroup.toGL Z =
                  Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
                rhoSigmaE6A3 L v Z ∈ Pt) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓ : ℓ.Prime := Fact.out
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
  set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E6 b = h := hbh
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
  have hbp : orderOf (rootDiagUnit .E6 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hstab : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit .E6 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup .E6)) := by
    intro a hap' ha1 haT
    rw [hT] at haT
    obtain ⟨a', ha', haa⟩ := haT
    have : a' = a := hinj0 haa
    subst this
    exact e6Four_stab_of_fixed Fr hFr hp hp3 hord hΦ ha' hap' ha1
  have core : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .E6 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .E6 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .E6 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .E6 L) →
        (∀ i, ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L,
          Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .E6 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .E6 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), V.Normal →
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
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data_of_stab ι adjEmb_injective adjEmb_mem Φ
      (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj
      hPnorm hPcent hx c hcS hkerZ
  have hkd := e6Four_kernel_of_fixed Fr hFr hp hp3 hΦ hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hunit⟩
  ·
    have hspan : rootSpan .E6 L (rootCharKernel b) = ⊥ := by
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
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v hv => ?_, fun hne => ?_⟩⟩
    · rw [hker b' hb']
      exact hψV V hVn hVs v hv
    · exfalso
      rw [hker b' hb', hA] at hne
      exact Set.not_nonempty_empty hne
  ·
    obtain ⟨P, hP, hP1, ⟨h₀, hh₀⟩, ⟨H, hH⟩⟩ :=
      e6_four_family hℓ hf (k := K) hK Fr hFr' n hnm hnW v hunit
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core (sigmaSetE6A3 v) hSeq
      (sigmaSetE6A3_isRoot v) (sigmaSetE6A3_neg v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v' hv' => ?_, fun _ => ?_⟩⟩
    · rw [hker b' hb', hSeq]
      exact hψV V hVn hVs v' hv'
    · refine ⟨P (), hPq (), ?_, ⟨h₀, hh₀⟩, v, by rw [hker b' hb', hSeq], H, hH⟩
      refine commutator_range_eq_of_family ψ (H := torusGroup .E6 L)
        (Q := rootSpan .E6 L (sigmaSetE6A3 v)) (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
        (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
      · exact torusGroup_le_normalizer_rootSpan (sigmaSetE6A3_isRoot v)
      · intro a ha a' ha'
        obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
        exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
      · exact Subgroup.isPerfect_iff.1 (hPq ()).1

end PerX

section Frame

theorem e6_four_abelian_two_torsion {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {V : Type*} [Group V] (ψ : V →* ModGL .E6 L)
    (hψ : Function.Injective ψ)
    (hV : ∀ v : V, ψ v ∈ (fixedCharTuples e6FourM Fr).map (rootDiagUnitHom .E6 L)) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  choose a ha hav using fun v : V => hV v
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  have hmul : ∀ v w : V, a (v * w) = a v * a w := fun v w => by
    apply hinj0
    rw [hav, map_mul, map_mul, hav, hav]
  refine ⟨fun v w => ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, ← hav v, ← hav w, ← map_mul, ← map_mul, mul_comm]
  · set Γ : Subgroup (Fin Tag.E6.rank → Lˣ) :=
      (fixedCharTuples e6FourM Fr) ⊓ ψ.range.comap (rootDiagUnitHom .E6 L) with hΓ
    have hΓle : Γ ≤ fixedCharTuples e6FourM Fr := inf_le_left
    let φ : {v : V // v ^ 2 = 1} → {g : Γ // g ^ 2 = 1} := fun v =>
      ⟨⟨a v.1, Subgroup.mem_inf.2 ⟨ha v.1, ⟨v.1, (hav v.1).symm⟩⟩⟩, by
        apply Subtype.ext
        apply hinj0
        change rootDiagUnitHom .E6 L (a v.1 ^ 2) = rootDiagUnitHom .E6 L 1
        rw [map_pow, hav, ← map_pow, v.2, map_one, map_one]⟩
    have hφ : Function.Injective φ := fun v w h => by
      apply Subtype.ext
      apply hψ
      rw [← hav v.1, ← hav w.1]
      have := congrArg (fun g : {g : Γ // g ^ 2 = 1} => ((g.1 : Γ) : Fin Tag.E6.rank → Lˣ)) h
      simp only [φ] at this
      rw [this]
    obtain ⟨hfin, hcard⟩ := e6Four_card_two_torsion_le_four Fr hFr hΓle
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

theorem e6_four_frame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u) :
    ∃ g0 : ModGL .E6 L, g0 ∈ adjointGroup .E6 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .E6 K L).range) ∧
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
        (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L) ∧
      ∀ Q : Subgroup (adjointGroup .E6 K), IsPGroup p Q → ∃ c : adjointGroup .E6 K, ∀ q ∈ Q,
        g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∈
          twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E6 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples e6FourM Fr).map (rootDiagUnitHom .E6 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e6FourM = weylMatrix e6F4U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G3 := fixedBlockTuples e6FourM Fr
    (e6FourCols 3 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) with hG3
  set G0 := fixedBlockTuples e6FourM Fr
    (e6FourCols 0 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 3 - (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) - 1).natAbs) ^ 2
    with hNdef
  set Z0 : Subgroup (ModGL .E6 L) := (G3 ⊔ G0).map (rootDiagUnitHom .E6 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e6Four_card_sup Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := pow_ne_zero 2 (e6Four_card_ne_zero hq2)
  have hord : p ^ (Nat.card (adjointGroup .E6 K)).factorization p = p ^ N.factorization p :=
    e6Four_ordProj K hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E6 3
    (Or.inl ⟨rfl, rfl⟩) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨g0, hg0C, hg0, hperf, hT, fun Q hQ => ?_⟩
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun q hq => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q hq))⟩

end Frame

section Solvable

theorem e6_four_solvable (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u) :
    ∀ x : adjointGroup .E6 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L n hnm hnW
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψ⟩ := e6_four_perx K hf hK hp hp3 hordq hΦ L n hnm hnW g0 hg0C hg0 hperf hT
    hx c hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  obtain ⟨hψV, -⟩ := hψ b hb.symm
  have hVT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) ∈
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L) := fun v => by
    rw [← hT]
    exact subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  obtain ⟨hab, h2⟩ := e6_four_abelian_two_torsion (iterateFrobenius L ℓ f) hFr
    (ψ.comp V.subtype) (hψinj.comp V.subtype_injective) hVT
  refine ⟨fun v hv w hw => ?_, h2⟩
  have := hab ⟨v, hv⟩ ⟨w, hw⟩
  exact congrArg Subtype.val this

end Solvable

end CFSG.RankThree.PartOne.KE

module

public import CFSG.RankThree.PartOne.KE.E8FiveFamily
public import CFSG.RankThree.PartOne.KE.E8FiveArith
public import CFSG.RankThree.PartOne.KE.E8Rigid
public import CFSG.RankThree.PartOne.KE.PlaneOdd
public import CFSG.RankThree.PartOne.KE.A1E6Five
public import CFSG.RankThree.PartOne.KE.A1TwE6Ten
public import CFSG.RankThree.PartOne.KE.E8FiveKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise

section Arith

theorem e8Five_odd (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (q : ℕ) :
    Odd (((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs) := by
  rw [Int.natAbs_odd]
  have hδo : Odd δ := by rcases hδ with rfl | rfl <;> decide
  rcases Int.even_or_odd (q : ℤ) with he | ho
  · obtain ⟨k, hk⟩ := he
    exact ⟨8 * k ^ 4 + 4 * δ * k ^ 3 + 2 * k ^ 2 + δ * k, by rw [hk]; ring⟩
  · have h1 : Odd ((q : ℤ) ^ 4) := ho.pow
    have h2 : Odd (δ * (q : ℤ) ^ 3) := hδo.mul ho.pow
    have h3 : Odd ((q : ℤ) ^ 2) := ho.pow
    have h4 : Odd (δ * (q : ℤ)) := hδo.mul ho
    exact ((((h1.add_odd h2).add_odd h3).add_odd h4).add_one)

theorem e8Five_hΦ_one {p : ℕ} (q : ℕ)
    (h : (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0) :
    (((1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 4 + (((1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 3 +
      (((1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 2 + (((1 : ℤ) : ZMod p) * (q : ZMod p)) + 1 = 0 := by
  simpa using h

theorem e8Five_hΦ_neg {p : ℕ} (q : ℕ)
    (h : (-(q : ZMod p)) ^ 4 + (-(q : ZMod p)) ^ 3 + (-(q : ZMod p)) ^ 2 + (-(q : ZMod p)) + 1 =
      0) :
    (((-1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 4 + (((-1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 3 +
      (((-1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 2 + (((-1 : ℤ) : ZMod p) * (q : ZMod p)) + 1 = 0 := by
  simpa using h

theorem exists_ne_one_ker_of_card_sq {A : Type*} [Group A] [Finite A] {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ 2) (χ : A →* Lˣ) (hχ : ∀ a, χ a ^ p = 1) :
    ∃ a : A, a ≠ 1 ∧ χ a = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective χ := (injective_iff_map_eq_one χ).2 fun a ha => by
    by_contra hne
    exact hcon a hne ha
  have hle : Nat.card A ≤ Nat.card (rootsOfUnity p L) :=
    Nat.card_le_card_of_injective (fun a => (⟨χ a, (mem_rootsOfUnity p (χ a)).2 (hχ a)⟩ :
      rootsOfUnity p L)) fun a b hab => hinj (congrArg Subtype.val hab)
  have h2 := card_rootsOfUnity L p
  have hp2 := hp.two_le
  rw [hA] at hle
  nlinarith

end Arith


section PerX

theorem e8_five_perx (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hp7 : 7 < p)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • weylMatrix e8F5U) *ᵥ u)
    (g0 : ModGL .E8 L) (hg0C : g0 ∈ adjointGroup .E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (e8FiveM δ) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L))
    {x : adjointGroup .E8 K} (hx : orderOf x = p) (c : adjointGroup .E8 K)
    (hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ b : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
        (rootCharKernel b).Nonempty →
        ∃ Pt : Subgroup (ModGL .E8 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
          ∃ h₀ : ModGL .E8 L, ∀ Y : SL2 K, h₀ * simpleRootSL2 .E8 L (e8Index 0)
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
  have hℓ : ℓ.Prime := Fact.out
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
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
  have core : ∀ (S : Set (Fin Tag.E8.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .E8 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .E8 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .E8 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .E8 L) →
        (∀ i, ∀ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
          Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .E8 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
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
    have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data ι adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0
      hg0C hg0 hperf hp hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
  have hkd := e8Five_kernel_of_fixed δ hδ Fr hFr hp hp5 hΦ hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hs, hu⟩
  ·
    have hspan : rootSpan .E8 L (rootCharKernel b) = ⊥ := by
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
    obtain ⟨P, hP, hP1, h₀, hh₀⟩ := e8_five_family hℓ hf (k := K) hK Fr hFr' δ hδ n hnm hnW v
      hs hu
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core (sigmaSetE8A4 v) hSeq
      (sigmaSetE8A4_isRoot v) (sigmaSetE8A4_neg v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' _ _ => ⟨P (), hPq (), ?_, h₀, hh₀⟩⟩
    refine commutator_range_eq_of_family ψ (H := torusGroup .E8 L)
      (Q := rootSpan .E8 L (sigmaSetE8A4 v)) (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
      (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
    · exact torusGroup_le_normalizer_rootSpan (sigmaSetE8A4_isRoot v)
    · intro a ha a' ha'
      obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
    · exact Subgroup.isPerfect_iff.1 (hPq ()).1

end PerX


section Main

theorem e8_five_main (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hp7 : 7 < p) {m : ℕ} (hm : m = 5 ∨ m = 10)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • weylMatrix e8F5U) *ᵥ u) :
    (∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E8 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E8 K))))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ = (fixedCharTuples (e8FiveM δ) Fr).map (rootDiagUnitHom .E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM δ = δ • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM δ) Fr
    (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 4 + δ * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
    δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup δ hδ Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero δ hδ hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K δ hδ hp hp5 hm hordq hpq hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  have hodd : Odd (((Nat.card K : ℤ) ^ 4 + δ * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
      δ * (Nat.card K : ℤ) + 1).natAbs) := e8Five_odd δ hδ _
  have hsolv : ∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hxc : c * x * c⁻¹ ∈ subtorusImage (adjEmb .E8 K L) g0 Z0 :=
      hc x (Subgroup.mem_zpowers x)
    have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
      hZ0le ((mem_subtorusImage_iff _ _ _ _).1 hxc)
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := e8_five_perx K hf hK δ hδ hp hp5 hp7 hΦ L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    by_contra hnodd
    have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hv2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) = 2 := by
      rw [orderOf_injective ψ hψinj, Subgroup.orderOf_coe, hv]
    have hmem := hψV V hVn hVs v v.2
    rw [hT] at hmem
    obtain ⟨b', hb', hb'v⟩ := hmem
    have hdvd : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) ∣
        (((Nat.card K : ℤ) ^ 4 + δ * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
          δ * (Nat.card K : ℤ) + 1).natAbs) := by
      rw [← hb'v]
      exact (orderOf_map_dvd (rootDiagUnitHom .E8 L) b').trans
        (e8Five_orderOf_dvd δ hδ Fr hFr hb')
    rw [hv2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  refine ⟨hsolv, ?_⟩
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E8 K) :=
    A.comap (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .E8 K L (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q q.2))
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit .E8 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.E8.rank → ℤ := Pi.single 0 1 with hα₀def
  have hα₀ : IsRoot .E8 α₀ := IsRoot.basis 0
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))
        ((q : adjointGroup .E8 K) ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    have h2 : (q : adjointGroup .E8 K) ^ p = 1 := hIntinj (h1.trans (map_one _).symm)
    have h3 : q ^ p = 1 := Subtype.ext h2
    rw [h3, map_one]
  obtain ⟨q, hq1, hqχ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
  set x : adjointGroup .E8 K := (q : adjointGroup .E8 K) with hxdef
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) (x ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    exact hIntinj (h1.trans (map_one _).symm)
  have hx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxA : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) x ∈ A := q.2
  have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ q]
    exact hφT q
  obtain ⟨ψ, hψinj, hψ, -, hψK⟩ := e8_five_perx K hf hK δ hδ hp hp5 hp7 hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  have hb : rootDiagUnit .E8 (β q) = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hne : (rootCharKernel (β q)).Nonempty := ⟨α₀, hα₀, hqχ⟩
  obtain ⟨Pt, hPq, hcomm, h₀, hh₀⟩ := hψK (β q) hb hne
  have hle := e8_core_le_range_conj_of_embedding K L hp hB c g0 ψ hψinj hψ hPq hcomm
    (e8Index 0) h₀ hh₀
  refine ⟨MulAut.conj x, hxA, fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  have hsx := odd_card_inf_range_of_solvable (B := B) hp hC hB (hsolv x hx)
  rwa [inf_eq_left.2 hle] at hsx

end Main


section Final

theorem planeLocalCoreOdd_E8_five (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 10).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .E8 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E8 (Or.inr (Or.inr rfl)) K).1
  have hcore := localCoreTrivialOn_noninner_E .E8 (Or.inr (Or.inr rfl)) K hp (by omega)
  rcases hpf with h5 | h10
  ·
    have h5' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
        (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using h5
    obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Five_data hp hp5 h5'
    have hΦ5 : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
        ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 +
        (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 h5'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L e8F5U
    have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8F5U, hcm⟩ = e8F5U :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep e8F5U)
    have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8F5U, hcm⟩ • u =
        ((1 : ℤ) • weylMatrix e8F5U) *ᵥ u := fun u => by
      rw [hπ, one_smul, weylMatrix_mulVec]
    have h := e8_five_main K hf hK 1 (Or.inl rfl) hp hp5 hp7 (m := 5) (Or.inl rfl) hord hpq
      (e8Five_hΦ_one _ hΦ5) L _ hcm hnW
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2
  ·
    have h10' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 -
        (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using h10
    obtain ⟨hp7, hpq, hord, hΦ10⟩ := CTE6.twE6Ten_data hp hp5 h10'
    have hcm := canonicalRep_mem_monomialSubgroup L (e8F5C ^ 21)
    have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L (e8F5C ^ 21), hcm⟩ =
        e8F5C ^ 21 := weylQuotientHom_eq (mapsRootLines_canonicalRep (e8F5C ^ 21))
    have hnW : ∀ u, weylQuotientHom .E8 L
        ⟨canonicalRep (coxeterSystem .E8) L (e8F5C ^ 21), hcm⟩ • u =
          ((-1 : ℤ) • weylMatrix e8F5U) *ᵥ u := fun u => by
      rw [hπ, ← weylMatrix_mulVec, weylMatrix_e8F5C_21, neg_one_smul]
    have h := e8_five_main K hf hK (-1) (Or.inr rfl) hp hp5 hp7 (m := 10) (Or.inr rfl) hord hpq
      (e8Five_hΦ_neg _ hΦ10) L _ hcm hnW
    exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2

theorem oddEndpoint_E8_phi5Phi10 :
    OddEndpoint .E8 fun p ℓ f =>
      5 < p ∧ ((p : ℤ) ∣ cycloVal 5 ℓ f ∨ (p : ℤ) ∣ cycloVal 10 ℓ f) := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E8_five K hℓ hf hK hp hc.1 (by simpa [cycloVal, hK] using hc.2)

end Final

end CFSG.RankThree.PartOne.KE

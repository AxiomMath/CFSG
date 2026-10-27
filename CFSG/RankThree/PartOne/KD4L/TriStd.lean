module

public import CFSG.RankThree.PartOne.KD4L.TriNu
public import CFSG.RankThree.Chevalley.SteinbergBIE6D4Layers
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.RankThree.PartOne.KD4L.TriDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups commutatorElement

section Simple

theorem isQuasisimple_of_isSimpleGroup {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnc : ∃ x y : G, x * y ≠ y * x) : CFSG.IsQuasisimple G := by
  have hperf : Group.IsPerfect G := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  have hs' : IsSimpleGroup (G ⧸ (⊥ : Subgroup G)) := by
    have : Nontrivial (G ⧸ (⊥ : Subgroup G)) := QuotientGroup.quotientBot.symm.injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective (QuotientGroup.mk' (⊥ : Subgroup G))
      (QuotientGroup.mk'_surjective _)
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (⊥ : Subgroup G) bot_le
    hperf hs' ?_
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨x, y, fun h => hxy ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_bot,
    inv_mul_eq_one] at h
  exact h

theorem isQuasisimple_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple H :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e hG

end Simple


section Std

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]

structure StdTwist (n₁ : ModGL τ L) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ) : Prop where
  he : e = 1 ∨ e = 2
  hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k)
  hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ
  hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ
  hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
    n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c

variable {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}

omit [IsAlgClosed L] in
theorem StdTwist.normalizes (h : StdTwist n₁ π e) :
    n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
  mem_normalizer_subsystemGroup_of_conj h.hπ h.hπ' h.hgen

omit hτ [IsAlgClosed L] in
@[expose] def stdLayer (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (n₁ : ModGL τ L) :
    Subgroup (ModGL τ L) :=
  subsystemGroup τ L (d4Set τ) ⊓
    twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

omit hτ [IsAlgClosed L] in
theorem mem_stdLayer {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {g : ModGL τ L} :
    g ∈ stdLayer ℓ f n₁ ↔ g ∈ subsystemGroup τ L (d4Set τ) ∧
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g :=
  Iff.rfl

variable {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem StdTwist.stdLayer_eq_map (h : StdTwist n₁ π e) :
    stdLayer ℓ f n₁ = ((d4ThetaFixed L (iterateFrobenius L ℓ f) e).map
      (nuEquiv τ L).symm.toMonoidHom).map (subsystemGroup τ L (d4Set τ)).subtype := by
  ext g
  constructor
  · rintro ⟨hgQ, hgfix⟩
    have h1 := (fixed_iff_nuE_mem (f := f) h.normalizes h.hgen h.he h.hπe ⟨g, hgQ⟩).1 hgfix
    exact ⟨(nuEquiv τ L).symm (nuE τ L ⟨g, hgQ⟩), ⟨nuE τ L ⟨g, hgQ⟩, h1, rfl⟩,
      congrArg Subtype.val ((nuEquiv τ L).symm_apply_apply ⟨g, hgQ⟩)⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨((nuEquiv τ L).symm z).2, ?_⟩
    refine (fixed_iff_nuE_mem (f := f) h.normalizes h.hgen h.he h.hπe ((nuEquiv τ L).symm z)).2 ?_
    have : nuE τ L ((nuEquiv τ L).symm z) = z := (nuEquiv τ L).apply_symm_apply z
    rw [this]
    exact hz

@[expose] def StdTwist.layerEquiv (h : StdTwist n₁ π e) :
    stdLayer ℓ f n₁ ≃* d4ThetaFixed L (iterateFrobenius L ℓ f) e :=
  (MulEquiv.subgroupCongr h.stdLayer_eq_map).trans
    (((((d4ThetaFixed L (iterateFrobenius L ℓ f) e).map
      (nuEquiv τ L).symm.toMonoidHom).equivMapOfInjective
        (subsystemGroup τ L (d4Set τ)).subtype (Subgroup.subtype_injective _)).symm).trans
      ((d4ThetaFixed L (iterateFrobenius L ℓ f) e).equivMapOfInjective
        (nuEquiv τ L).symm.toMonoidHom (nuEquiv τ L).symm.injective).symm)

theorem StdTwist.finite_quasisimple (h : StdTwist n₁ π e) (hf : 1 ≤ f) :
    Finite (stdLayer ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer ℓ f n₁) := by
  have hℓ : ℓ.Prime := Fact.out
  set K := frobeniusFixedField L ℓ (3 * f) with hKdef
  have hKc : Nat.card K = (ℓ ^ f) ^ 3 := by
    rw [card_frobeniusFixedField (by omega), ← pow_mul, mul_comm]
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKc]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  let σ : K →+* K := iterateFrobenius K ℓ (f * e)
  have hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ e) := fun c => by
    rw [iterateFrobenius_def, ← pow_mul]
  obtain ⟨φ, -⟩ := exists_d4ThetaFixed_equiv' (K := K) (Ω := L) (σ := σ)
    (Fr := iterateFrobenius L ℓ f) hℓ hf hKc h.he hσ (fun c => iterateFrobenius_def ℓ f c)
  obtain ⟨hsimple, hnc⟩ := isSimple_graphFixedRootGroup_triality hℓ hf hKc e h.he σ hσ
  have hfinC : Finite (graphFixedRootGroup TwistTag.D4 K σ) := by
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    exact Subtype.finite
  have hψ : stdLayer ℓ f n₁ ≃* graphFixedRootGroup TwistTag.D4 K σ := h.layerEquiv.trans φ
  exact ⟨Finite.of_equiv _ hψ.symm.toEquiv,
    isQuasisimple_of_mulEquiv' hψ.symm (isQuasisimple_of_isSimpleGroup hsimple hnc)⟩

omit [IsAlgClosed L] in
theorem middle_SL2_mem_stdLayer
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    (hπ2 : π (d4Id (τ := τ) 2) = d4Id 2) {k : Type} [Field k] [Algebra k L]
    (hk : Nat.card k = ℓ ^ f) (Y : SL(2, k)) :
    simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈
      stdLayer ℓ f n₁ := by
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have : Fintype k := Fintype.ofFinite k
  have hι : ∀ b : k, algebraMap k L b ^ ℓ ^ f = algebraMap k L b := fun b => by
    rw [← map_pow]
    congr 1
    have := FiniteField.pow_card b
    rwa [← Nat.card_eq_fintype_card, hk] at this
  have hfix : ∀ c : L, c ^ ℓ ^ f = c → xUnit τ L (d4Id 2) c ∈ stdLayer ℓ f n₁ ∧
      yUnit τ L (d4Id 2) c ∈ stdLayer ℓ f n₁ := fun c hc => by
    refine ⟨⟨xUnit_mem_subsystemGroup (d4Id_mem 2) c, ?_⟩, ⟨yUnit_mem_subsystemGroup (d4Id_mem 2) c, ?_⟩⟩
    · change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (xUnit τ L (d4Id 2) c) * n₁⁻¹ = _
      rw [entrywise_xUnit, hc, (hgen _ (d4Id_mem 2) c).1, hπ2]
      rfl
    · change n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (yUnit τ L (d4Id 2) c) * n₁⁻¹ = _
      rw [entrywise_yUnit, hc, (hgen _ (d4Id_mem 2) c).2, hπ2]
      rfl
  have hT : (stdLayer ℓ f n₁).comap ((simpleRootSL2 τ L (d4Id 2)).comp
      (Matrix.SpecialLinearGroup.map (algebraMap k L))) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower :
      Subgroup.closure (Set.range (uSL (K := k)) ∪ Set.range vSL) = ⊤), Subgroup.closure_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · change simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) (uSL b)) ∈
        stdLayer ℓ f n₁
      rw [map_uSL, simpleRootSL2_uSL]
      exact (hfix _ (hι b)).1
    · change simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) (vSL b)) ∈
        stdLayer ℓ f n₁
      rw [map_vSL, simpleRootSL2_vSL]
      exact (hfix _ (hι b)).2
  have hA : Y ∈ (stdLayer ℓ f n₁).comap ((simpleRootSL2 τ L (d4Id 2)).comp
      (Matrix.SpecialLinearGroup.map (algebraMap k L))) := hT ▸ Subgroup.mem_top Y
  exact hA

omit [IsAlgClosed L] in
theorem StdTwist.middle_SL2 (h : StdTwist n₁ π e) {k : Type} [Field k] [Algebra k L]
    (hk : Nat.card k = ℓ ^ f) (Y : SL(2, k)) :
    simpleRootSL2 τ L (d4Id 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈
      stdLayer ℓ f n₁ :=
  middle_SL2_mem_stdLayer h.hgen (by
    rw [h.hπe 2]
    rcases h.he with rfl | rfl <;> simp [rhoE, d4Rho_values.2.2.1]) hk Y

theorem StdTwist.commute_of_commute (h : StdTwist n₁ π e) (hf : 1 ≤ f) {q' : ModGL τ L}
    (hq' : q' ∈ subsystemGroup τ L (d4Set τ)) (hc : ∀ u ∈ stdLayer ℓ f n₁, q' * u = u * q') :
    ∀ g ∈ subsystemGroup τ L (d4Set τ), q' * g = g * q' := by
  have hℓ : ℓ.Prime := Fact.out
  have hX : ((nuQ τ L ⟨q', hq'⟩ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) ∈
      e6Commutant ((d4Layer (iterateFrobenius L ℓ f) e : Subgroup (ModGL Tag.E6 L)) :
        Set (ModGL Tag.E6 L)) := by
    rintro _ ⟨z, hz, rfl⟩
    have hg' : (((nuEquiv τ L).symm z : subsystemGroup τ L (d4Set τ)) : ModGL τ L) ∈
        stdLayer ℓ f n₁ := by
      refine ⟨((nuEquiv τ L).symm z).2, ?_⟩
      refine (fixed_iff_nuE_mem (f := f) h.normalizes h.hgen h.he h.hπe ((nuEquiv τ L).symm z)).2 ?_
      have : nuE τ L ((nuEquiv τ L).symm z) = z := (nuEquiv τ L).apply_symm_apply z
      rw [this]
      exact hz
    have hcomm := hc _ hg'
    have hnu : nuQ τ L ((nuEquiv τ L).symm z) = ((z : subsystemGroup Tag.E6 L d4Support) :
        ModGL Tag.E6 L) := congrArg Subtype.val ((nuEquiv τ L).apply_symm_apply z)
    have h2 : nuQ τ L ⟨q', hq'⟩ * nuQ τ L ((nuEquiv τ L).symm z) =
        nuQ τ L ((nuEquiv τ L).symm z) * nuQ τ L ⟨q', hq'⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (nuQ τ L) (Subtype.ext hcomm)
    rw [hnu] at h2
    exact Commute.units_val h2
  rw [e6Commutant_d4Layer (Ω := L) hℓ hf (fun c => iterateFrobenius_def ℓ f c) h.he] at hX
  intro g hg
  have h1 := hX _ (nuQ_mem ⟨g, hg⟩)
  have h1' : Commute (nuQ τ L ⟨q', hq'⟩) (nuQ τ L ⟨g, hg⟩) := by simpa using h1
  have h3 : (⟨q', hq'⟩ * ⟨g, hg⟩ : subsystemGroup τ L (d4Set τ)) =
      ⟨g, hg⟩ * ⟨q', hq'⟩ := nuQ_injective (by rw [map_mul, map_mul]; exact h1'.eq)
  exact congrArg Subtype.val h3

end Std

end CFSG.RankThree.PartOne.KD4L

module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i)

section Fix

variable {K : Type} [Field K]

variable (K) in
@[expose] def fixGL (β : K ≃+* K) :
    Subgroup (ModGL F4.tag K) :=
  (Units.map (entrywiseHom (τ := F4.tag) β.toRingHom)).eqLocus (MonoidHom.id _)

theorem mem_fixGL {β : K ≃+* K}
    {x : ModGL F4.tag K} :
    x ∈ fixGL K β ↔ Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) x = x :=
  Iff.rfl

theorem canonicalRep_mem_fixGL (β : K ≃+* K)
    (w : WeylGroup F4.tag) : canonicalRep (coxeterSystem F4.tag) K w ∈ fixGL K β :=
  entrywise_canonicalRep β w

theorem entrywise_pinnedX_units
    (β : K ≃+* K) (α : Fin F4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (pinnedX F4.tag K α c) =
      pinnedX F4.tag K α (β c) := by
  rw [Units.ext_iff, Units.coe_map]
  show entrywise β.toRingHom _ = _
  rw [entrywise_pinnedX]
  rfl

theorem map_largeReeSigma (β : K ≃+* K) (m : ℕ) (c : K) :
    β (largeReeSigma m c) = largeReeSigma m (β c) := by
  simp [largeReeSigma, map_pow]

end Fix

section Sub

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (K) in
@[expose] def Rf (a : ℕ) (β : K ≃+* K) : Subgroup (ModGL F4.tag K) :=
  F4.reeGamma K a ⊓ fixGL K β

theorem map_fixedSubgroup_eq_Rf {a : ℕ} (β : K ≃+* K) :
    (CFSG.RankThree.PartOne.CTP.fixedSubgroup (F4.reeGammaFieldAut K a β)).map
      (F4.reeGamma K a).subtype = Rf K a β := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hfix, rfl⟩

theorem mem_fixedSubgroup_iff {a : ℕ} {β : K ≃+* K} (g : F4.reeGamma K a) :
    g ∈ CFSG.RankThree.PartOne.CTP.fixedSubgroup (F4.reeGammaFieldAut K a β) ↔
      (g : ModGL F4.tag K) ∈ Rf K a β := by
  rw [← map_fixedSubgroup_eq_Rf]
  constructor
  · intro h
    exact ⟨g, h, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    rwa [Subtype.ext hyg] at hy

end Sub

section Rational

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem entrywise_sylowVec (β : K ≃+* K) (x : Fin 12 → K) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (sylowVec a K x) =
      sylowVec a K (fun i => β (x i)) := by
  simp only [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
    sylowX, map_mul, entrywise_pinnedX_units, map_add, map_mul, map_pow, map_largeReeSigma]

theorem sylowVec_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (x : Fin 12 → K) :
    sylowVec a K x ∈ Rf K a β ↔ ∀ i, β (x i) = x i := by
  have hmem : sylowVec a K x ∈ F4.reeFixedPosUnipotent K a := (bijOn_sylowVec hK).1 (Set.mem_univ x)
  constructor
  · rintro ⟨-, hfix⟩
    change Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (sylowVec a K x) = sylowVec a K x
      at hfix
    rw [entrywise_sylowVec] at hfix
    have := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ x) hfix
    exact fun i => congrFun this i
  · intro h
    refine ⟨reeFixedPosUnipotent_le_reeGamma hmem, ?_⟩
    change Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (sylowVec a K x) = sylowVec a K x
    rw [entrywise_sylowVec]
    congr 1
    funext i
    exact h i

theorem weylOne_mem_Rf (β : K ≃+* K) : weylOne K ∈ Rf K a β :=
  ⟨weylOne_mem, canonicalRep_mem_fixGL β _⟩

theorem weylTwo_mem_Rf (β : K ≃+* K) : weylTwo K ∈ Rf K a β :=
  ⟨weylTwo_mem, canonicalRep_mem_fixGL β _⟩

end Rational

section Levi

variable {K : Type} [Field K]

theorem leviImage_mul_mem {R V H : Subgroup (ModGL F4.tag K)}
    (hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))) {r r' : ModGL F4.tag K}
    (hr : r ∈ R) (h : ∃ v ∈ V, v * r ∈ H) (h' : ∃ v ∈ V, v * r' ∈ H) :
    ∃ v ∈ V, v * (r * r') ∈ H := by
  obtain ⟨v, hv, hvr⟩ := h
  obtain ⟨v', hv', hvr'⟩ := h'
  refine ⟨v * (r * v' * r⁻¹), V.mul_mem hv ((Subgroup.mem_normalizer_iff.1 (hRV hr) v').1 hv'), ?_⟩
  have e : v * (r * v' * r⁻¹) * (r * r') = (v * r) * (v' * r') := by group
  rw [e]
  exact H.mul_mem hvr hvr'

theorem leviImage_inv_mem {R V H : Subgroup (ModGL F4.tag K)}
    (hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))) {r : ModGL F4.tag K}
    (hr : r ∈ R) (h : ∃ v ∈ V, v * r ∈ H) : ∃ v ∈ V, v * r⁻¹ ∈ H := by
  obtain ⟨v, hv, hvr⟩ := h
  refine ⟨r⁻¹ * v⁻¹ * r, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 (hRV (R.inv_mem hr)) v⁻¹).1 (V.inv_mem hv)
    simpa using this
  · have e : r⁻¹ * v⁻¹ * r * r⁻¹ = (v * r)⁻¹ := by group
    rw [e]
    exact H.inv_mem hvr

@[expose] def leviImage (R V H : Subgroup (ModGL F4.tag K))
    (hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))) : Subgroup (ModGL F4.tag K) where
  carrier := {r | r ∈ R ∧ ∃ v ∈ V, v * r ∈ H}
  mul_mem' := fun {r r'} hr hr' => ⟨R.mul_mem hr.1 hr'.1, leviImage_mul_mem hRV hr.1 hr.2 hr'.2⟩
  one_mem' := ⟨R.one_mem, 1, V.one_mem, by rw [one_mul]; exact H.one_mem⟩
  inv_mem' := fun {r} hr => ⟨R.inv_mem hr.1, leviImage_inv_mem hRV hr.1 hr.2⟩

theorem inf_le_leviImage {R V H : Subgroup (ModGL F4.tag K)}
    {hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))} : R ⊓ H ≤ leviImage R V H hRV :=
  fun r hr => ⟨hr.1, 1, V.one_mem, by rw [one_mul]; exact hr.2⟩

theorem leviImage_le {R V H : Subgroup (ModGL F4.tag K)}
    {hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))} : leviImage R V H hRV ≤ R :=
  fun _ hr => hr.1

variable [Finite K] [CharP K F4.prime] {a : ℕ}

variable (K a) in
theorem rankOneGroupOne_le_normalizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) :=
  rankOneGroupOne_le_normalizer_complement hK

variable (K a) in
theorem rankOneGroupTwo_le_normalizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) :=
  rankOneGroupTwo_le_normalizer_complement hK

variable (K a) in
@[expose] def Y1 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (H : Subgroup (ModGL F4.tag K)) : Subgroup (ModGL F4.tag K) :=
  leviImage (rankOneGroupOne K a) (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) H
    (rankOneGroupOne_le_normalizer K a hK)

variable (K a) in
@[expose] def Y2 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (H : Subgroup (ModGL F4.tag K)) : Subgroup (ModGL F4.tag K) :=
  leviImage (rankOneGroupTwo K a) (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) H
    (rankOneGroupTwo_le_normalizer K a hK)

end Levi

end CFSG.RankThree.PartOne.SEITZRF

module

public import CFSG.Quasithin.H13.NQCatBNG2
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.Bruhat
public import CFSG.LieType.Steinberg.TwistedD4.Generation
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Sporadic.J4Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.NQCat.BN

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.QuasithinUnique

variable {K : Type} [Field K]

theorem not_isSolvable_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : ∃ s : Finset F, s.card = 4) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro hs
  have := Vol2Native.A312L.sl2_isSimple hF4
  obtain ⟨a, b, hab⟩ := Vol2Native.A312L.sl2_nonabelian hF4
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem not_isSolvable_of_range_le {G L : Type*} [Group G] [Group L] {M : Subgroup G}
    (φ : L →* G) (hφ : Function.Injective φ) (hle : φ.range ≤ M)
    (hL : ¬ Group.IsSolvable L) : ¬ Group.IsSolvable M := by
  intro hM
  have hrs : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact hL (Group.isSolvable_of_isSolvable_injective (f := φ.rangeRestrict)
    (MonoidHom.rangeRestrict_injective_iff.mpr hφ))

theorem rankOne_not_solvable_d4
    [Finite K] [CharP K 2]
    {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (hK4 : ∃ s : Finset K, s.card = 4)
    (hF4 : ∃ s : Finset (fixedField σ), s.card = 4) (i : Fin (Tag.rank .G2)) :
    ¬ Group.IsSolvable (rankOne (twistedDatum σ).rootGroup i) := by
  fin_cases i
  · refine not_isSolvable_of_range_le (slLong σ hσ) (slLong_injective hσ) ?_
      (not_isSolvable_sl2 hF4)
    rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · refine mem_sup_left ((mem_twistedRootGroup σ).2 ?_)
      change (slLong σ hσ (sl2Upper c) : adjointGroup d4 K) ∈ _
      rw [slLong_val, slLongE_upper]
      exact xPar_single_two_mem_twisted hσ c.2
    · refine mem_sup_right ((mem_twistedRootGroup σ).2 ?_)
      change (slLong σ hσ (sl2Lower c) : adjointGroup d4 K) ∈ _
      rw [slLong_val, slLongE_lower]
      exact xPar_neg_single_two_mem_twisted hσ c.2
  · refine not_isSolvable_of_range_le (slShort σ hσ) (slShort_injective hσ) ?_
      (not_isSolvable_sl2 hK4)
    rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · refine mem_sup_left ((mem_twistedRootGroup σ).2 ?_)
      change (slShort σ hσ (sl2Upper c) : adjointGroup d4 K) ∈ _
      rw [slShort_upper]
      have h := xOuter_mem σ (s := 1) (Or.inl rfl) (hσ c)
      rwa [one_smul] at h
    · refine mem_sup_right ((mem_twistedRootGroup σ).2 ?_)
      change (slShort σ hσ (sl2Lower c) : adjointGroup d4 K) ∈ _
      rw [slShort_lower]
      have h := xOuter_mem σ (s := -1) (Or.inr rfl) (hσ c)
      rwa [neg_one_smul] at h

theorem posUnipotent_twisted_eq
    (σ : K →+* K) :
    CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ) =
      (⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ 0 < ht β},
        twistedRootSubgroupD4 σ β).subgroupOf (twistedGroup σ) := by
  rw [CFSG.LieType.Steinberg.posUnipotent, twisted_setOf_pos_eq]
  exact iSup_twistedRootGroup_eq_subgroupOf σ fun β hβ => hβ.1

theorem exists_sylow_posUnipotent_d4
    [Finite K] [CharP K 2]
    {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (hK4 : ∃ s : Finset K, s.card = 4)
    (hF4 : ∃ s : Finset (fixedField σ), s.card = 4) :
    ∃ S : Sylow 2 (twistedGroup σ), (S : Subgroup (twistedGroup σ)) =
      CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUU : CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ) ≤
      (nativeData d4 K).U.comap (twistedGroup σ).subtype := by
    intro x hx
    rw [CFSG.LieType.Steinberg.posUnipotent, twisted_setOf_pos_eq] at hx
    have h := iSup_twistedRootGroup_le σ (fun h => 0 < h) hx
    rw [mem_comap, ← posUnipotent_adjDatum d4]
    change _ ∈ ⨆ γ ∈ {γ | γ ∈ (adjDatum (rootOperatorFamily d4) K).roots ∧ 0 < ht γ},
      rootGroup (rootOperatorFamily d4) K γ
    rw [adjDatum_roots]
    exact h
  have hU : IsPGroup 2 (CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ)) :=
    (((nativeRootSubgroups d4 K).isPGroup_U 2).comap_of_injective _
      Subtype.val_injective).to_le hUU
  refine CFSG.LieType.BorelTits.Weighted.exists_sylow_eq_of_normalizer 2 hU
    fun t htN ⟨k, hk⟩ => ?_
  have hz : IsPGroup 2 (zpowers t) := by
    rintro ⟨x, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (t ^ m) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hA := hz.to_sup_of_normal_right' hU ((zpowers_le (G := twistedGroup σ)).2 htN)
  have : Group.IsNilpotent
      ↥(zpowers t ⊔ CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ)) := hA.isNilpotent
  have hB := le_borel_of_isSolvable (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ) (rankOne_not_solvable_d4 hσ hK4 hF4)
    (A := zpowers t ⊔ CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ)) le_sup_right
    inferInstance
  have htB := borel_twisted_le σ (hB (mem_sup_left (mem_zpowers t)))
  rw [mem_comap] at htB
  have htU := (nativeRootSubgroups d4 K).mem_U_of_pow_eq_one 2 (borel_adjDatum_le d4 htB)
    (k := k) (by simpa using congrArg Subtype.val hk)
  have h62 := iSup_rootGroup_inf_twistFixed_le σ (f := htHom)
    (fun v => by rw [htHom_apply, htHom_apply, ht_rho])
    (Ψ := {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ}) (fun α hα => hα)
    (fun α hα β hβ hr => ⟨hr, by rw [ht_add]; linarith [hα.2, hβ.2]⟩)
    (fun α hα => ⟨isRoot_rho hα.1, by rw [ht_rho]; exact hα.2⟩)
    (mem_inf.2 ⟨nativeU_le htU, twistedGroup_le_twistFixed σ t.2⟩)
  rw [posUnipotent_twisted_eq, mem_subgroupOf]
  refine (iSup₂_le fun β hβ => ?_ : ⨆ β ∈ proj '' {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
    0 < ht γ}, twistedRootSubgroupD4 σ β ≤ _) h62
  obtain ⟨α, hα, rfl⟩ := hβ
  exact le_iSup₂_of_le (f := fun (β : Fin (Tag.rank .G2) → ℤ)
    (_ : β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ 0 < ht β}) =>
      twistedRootSubgroupD4 σ β) (proj α) ⟨isRoot_proj hα.1, by rw [ht_proj]; exact hα.2⟩
    le_rfl

theorem solvOver_of_is3D4
    {S : Type} [Group S] [Finite S]
    {k : ℕ} (hk : 2 ≤ k) (h : CFSG.Quasithin.Is3D4 2 k S) {P : Subgroup S}
    (hP : IsSylowTwoOf P ⊤) : SolvOver S P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, σ, hσc, ⟨e⟩⟩ := h
  have hK3 : Nat.card K = (2 ^ k) ^ 3 := hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := k * 3) (by omega) (by rw [hK3, ← pow_mul])
  have hq : 2 ≤ 2 ^ k :=
    (Nat.le_self_pow (by omega) 2).trans' le_rfl
  have hσ := sigma_three_of_card hK3 hσc
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    Vol2Native.A312L.exists_finset_card_four (hK3 ▸ four_le_pow_three hq)
  have hFcard : Nat.card (fixedField σ) = 2 ^ k := by
    have h1 := card_orbitField_D4_orientation (K := K) Nat.prime_two (f := k) (by omega) hK3
      (r := 1) (Or.inl rfl) (σ := σ) (fun c => by rw [pow_one]; exact hσc c) ⟨1, by decide⟩
    have h2 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
    rw [h2, pow_one] at h1
    have e2 : orbitField TwistTag.D4 K σ ⟨1, by decide⟩ = fixedField σ := by
      ext c
      rw [mem_orbitField, h2, pow_one, RingHom.mem_eqLocusField, RingHom.id_apply]
    rw [← e2]
    exact h1
  have hF4 : ∃ s : Finset (fixedField σ), s.card = 4 :=
    exists_finset_card_four_of_card hk hFcard
  set e₁ := twistedGroupEquivDerived σ hq hK3 hσc
  set π : twistedGroup σ →* DerivedCentralQuotient (twistedFixedGroup .D4 K σ) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp e₁.surjective
  have hker : π.ker ≤ center (twistedGroup σ) := by
    intro x hx
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [mem_center_iff]
    intro y
    apply e₁.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hx (e₁ y)
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hsol : SolvOver (DerivedCentralQuotient (twistedFixedGroup .D4 K σ))
      ((CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ)).map π) :=
    solvOver_map_of_ker_le_center π hπs hker (borel_le_normalizer_posUnipotent hct)
      fun _ hUA hA => le_borel_of_isSolvable hct (twistedDatum_steinbergExtras σ hσ)
        (rankOne_not_solvable_d4 hσ hK4 hF4) hUA hA
  obtain ⟨Q, hQ⟩ := exists_sylow_posUnipotent_d4 hσ hK4 hF4
  have hU₀ := isSylowTwoOf_map π hπs (hQ ▸ isSylowTwoOf_top_of_sylow Q)
  exact solvOver_of_sylow hsol hU₀ e.symm hP

end CFSG.Quasithin.H13.NQCat.BN

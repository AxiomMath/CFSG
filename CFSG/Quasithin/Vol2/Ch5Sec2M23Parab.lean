module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Blueprint
  CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open Module

theorem map_mem_maximalParabolics {A B : Type*} [Group A] [Group B] [Finite A] (φ : A ≃* B)
    {p : ℕ} [Fact p.Prime] {X : Subgroup A} (hX : X ∈ LinearFlag.maximalParabolics A p) :
    X.map φ.toMonoidHom ∈ LinearFlag.maximalParabolics B p := by
  obtain ⟨hco, B₀, ⟨P, hP⟩, hle⟩ := hX
  have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  refine ⟨(OrderIso.isCoatom_iff φ.mapSubgroup X).mpr hco,
    (Subgroup.normalizer ((P : Subgroup A) : Set A)).map φ.toMonoidHom,
    ⟨P.mapSurjective hsurj, ?_⟩, ?_⟩
  · rw [Sylow.coe_mapSurjective, Subgroup.map_equiv_normalizer_eq]
  · rw [hP]
    exact Subgroup.map_mono hle

theorem mem_maximalParabolics_of_map_eq {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A ≃* B) {p : ℕ} [Fact p.Prime] {X : Subgroup A} {Y : Subgroup B}
    (h : X.map φ.toMonoidHom = Y) (hY : Y ∈ LinearFlag.maximalParabolics B p) :
    X ∈ LinearFlag.maximalParabolics A p := by
  have : Finite B := Finite.of_equiv A φ.toEquiv
  have h1 := map_mem_maximalParabolics φ.symm hY
  rw [← h, Subgroup.map_map] at h1
  have h2 : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  rwa [h2, Subgroup.map_id] at h1

theorem sylowNormalizer_le_parOne_parTwo :
    ∃ B₀ ∈ LinearFlag.sylowNormalizers ↥(stabilizer M22 (0 : Fin 22)) 2,
      B₀ ≤ parOne ∧ B₀ ≤ parTwo := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T0, hT0B, hT0c⟩ := exists_sylow_borelBar
  have hT0i : ¬ 2 ∣ T0.index := by
    have h := Subgroup.card_mul_index T0
    rw [hT0c, card_m22Stab0] at h
    omega
  exact ⟨_, ⟨(IsPGroup.of_card (n := 6) (by rw [hT0c]; norm_num) : IsPGroup 2 T0).toSylow hT0i,
    rfl⟩, normalizer_le_parOne hT0B hT0c, normalizer_le_parTwo hT0B hT0c⟩

theorem parOne_mem_maximalParabolics :
    parOne ∈ LinearFlag.maximalParabolics ↥(stabilizer M22 (0 : Fin 22)) 2 := by
  obtain ⟨B₀, hB₀, h1, -⟩ := sylowNormalizer_le_parOne_parTwo
  refine ⟨⟨parOne_ne_top, fun X hX => ?_⟩, B₀, hB₀, h1⟩
  rcases eq_or_eq_top_of_card_eq_960 card_m22Stab0 card_parOne hX.le with h | h
  · exact absurd h hX.ne'
  · exact h

theorem parTwo_mem_maximalParabolics :
    parTwo ∈ LinearFlag.maximalParabolics ↥(stabilizer M22 (0 : Fin 22)) 2 := by
  obtain ⟨B₀, hB₀, -, h2⟩ := sylowNormalizer_le_parOne_parTwo
  refine ⟨⟨parTwo_ne_top, fun X hX => ?_⟩, B₀, hB₀, h2⟩
  rcases eq_or_eq_top_of_card_eq_960 card_m22Stab0 card_parTwo hX.le with h | h
  · exact absurd h hX.ne'
  · exact h

section Amalgam

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_of_isos
    {A1 A2 : Subgroup G} (φ₁ : ↥m22TwoStab ≃* ↥A1)
    (φ₂ : ↥m22PtHexStab ≃* ↥A2)
    (hB : ∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
      ((φ₁ ⟨b, hb₁⟩ : ↥A1) : G) = ((φ₂ ⟨b, hb₂⟩ : ↥A2) : G))
    (hB' : ∀ p : ↥m22TwoStab, ((φ₁ p : ↥A1) : G) ∈ A2 ↔ (p : M22) ∈ m22PtHexStab)
    {s t : G} (hs1 : s ∈ A1) (hs2 : s ∉ A2) (ht2 : t ∈ A2) (ht1 : t ∉ A1)
    (hss : s * s = 1) (htt : t * t = 1) (hst : orderOf (s * t) ≤ 3) :
    ∃ Φ : ↥(A1 ⊔ A2) ≃* ↥(stabilizer M22 (0 : Fin 22)),
      (A1.subgroupOf (A1 ⊔ A2)).map Φ.toMonoidHom = parOne ∧
        (A2.subgroupOf (A1 ⊔ A2)).map Φ.toMonoidHom = parTwo := by
  set A0 := A1 ⊔ A2 with hA0
  have hA1 : A1 ≤ A0 := le_sup_left
  have hA2 : A2 ≤ A0 := le_sup_right
  have hgen : A1.subgroupOf A0 ⊔ A2.subgroupOf A0 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA1 hA2, Subgroup.subgroupOf_self]
  let ψ₁ : ↥m22TwoStab ≃* ↥(A1.subgroupOf A0) := φ₁.trans (Subgroup.subgroupOfEquivOfLe hA1).symm
  let ψ₂ : ↥m22PtHexStab ≃* ↥(A2.subgroupOf A0) :=
    φ₂.trans (Subgroup.subgroupOfEquivOfLe hA2).symm
  have hψ₁ : ∀ p, ((ψ₁ p : ↥A0) : G) = ((φ₁ p : ↥A1) : G) := fun p => rfl
  have hψ₂ : ∀ p, ((ψ₂ p : ↥A0) : G) = ((φ₂ p : ↥A2) : G) := fun p => rfl
  have hB₀ : ∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
      (ψ₁ ⟨b, hb₁⟩ : ↥A0) = ψ₂ ⟨b, hb₂⟩ := fun b hb₁ hb₂ => by
    apply Subtype.ext
    rw [hψ₁, hψ₂]
    exact hB b hb₁ hb₂
  have hB₀' : ∀ p : ↥m22TwoStab, (ψ₁ p : ↥A0) ∈ A2.subgroupOf A0 ↔ (p : M22) ∈ m22PtHexStab :=
    fun p => by rw [Subgroup.mem_subgroupOf, hψ₁]; exact hB' p
  have ht₁ : (⟨s, hA1 hs1⟩ : ↥A0) ∈ A1.subgroupOf A0 := Subgroup.mem_subgroupOf.mpr hs1
  have ht₁' : (⟨s, hA1 hs1⟩ : ↥A0) ∉ A2.subgroupOf A0 := fun h =>
    hs2 (Subgroup.mem_subgroupOf.mp h)
  have ht₂ : (⟨t, hA2 ht2⟩ : ↥A0) ∈ A2.subgroupOf A0 := Subgroup.mem_subgroupOf.mpr ht2
  have ht₂' : (⟨t, hA2 ht2⟩ : ↥A0) ∉ A1.subgroupOf A0 := fun h =>
    ht1 (Subgroup.mem_subgroupOf.mp h)
  have hss' : (⟨s, hA1 hs1⟩ : ↥A0) * ⟨s, hA1 hs1⟩ = 1 := Subtype.ext hss
  have htt' : (⟨t, hA2 ht2⟩ : ↥A0) * ⟨t, hA2 ht2⟩ = 1 := Subtype.ext htt
  have hst' : orderOf ((⟨s, hA1 hs1⟩ : ↥A0) * ⟨t, hA2 ht2⟩) ≤ 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hst
  obtain ⟨Φ, hΦ1, hΦ2⟩ := CFSG.Quasithin.L34Amalgam.nonempty_mulEquiv_m22Stab_of_amalgam hgen ψ₁
    ψ₂ hB₀ hB₀' ht₁ ht₁' ht₂ ht₂' hss' htt' hst'
  refine ⟨Φ, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxp : ((ψ₁ (ψ₁.symm ⟨x, hx⟩) : ↥(A1.subgroupOf A0)) : ↥A0) = x := by simp
      rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, ← hxp, hΦ1]
      exact (ψ₁.symm ⟨x, hx⟩).2
    · intro hy
      have hy' : ((y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab :=
        Subgroup.mem_subgroupOf.mp hy
      refine ⟨(ψ₁ ⟨_, hy'⟩ : ↥A0), (ψ₁ ⟨_, hy'⟩).2, ?_⟩
      apply Subtype.ext
      exact hΦ1 ⟨_, hy'⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxp : ((ψ₂ (ψ₂.symm ⟨x, hx⟩) : ↥(A2.subgroupOf A0)) : ↥A0) = x := by simp
      rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, ← hxp, hΦ2]
      exact (ψ₂.symm ⟨x, hx⟩).2
    · intro hy
      have hy' : ((y : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab :=
        Subgroup.mem_subgroupOf.mp hy
      refine ⟨(ψ₂ ⟨_, hy'⟩ : ↥A0), (ψ₂ ⟨_, hy'⟩).2, ?_⟩
      apply Subtype.ext
      exact hΦ2 ⟨_, hy'⟩

theorem mem_maximalParabolics_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2))
    {s t : G} (hs1 : s ∈ G1) (hs2 : s ∉ G2) (ht2 : t ∈ G2) (ht1 : t ∉ G1)
    (hss : s * s = 1) (htt : t * t = 1) (hst : orderOf (s * t) ≤ 3) :
    G1.subgroupOf (G1 ⊔ G2) ∈ LinearFlag.maximalParabolics ↥(G1 ⊔ G2) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with ⟨φ₁, φ₂, hB, hB'⟩ | ⟨φ₁, φ₂, hB, hB'⟩
  · obtain ⟨Φ, h1, -⟩ := exists_mulEquiv_of_isos φ₁ φ₂ hB hB' hs1 hs2 ht2 ht1 hss htt hst
    exact mem_maximalParabolics_of_map_eq Φ h1 parOne_mem_maximalParabolics
  · obtain ⟨Φ, -, h2⟩ := exists_mulEquiv_of_isos φ₁ φ₂ hB hB' ht2 ht1 hs1 hs2 htt hss
      (by rwa [orderOf_mul_comm'])
    have h := mem_maximalParabolics_of_map_eq Φ h2 parTwo_mem_maximalParabolics
    rwa [sup_comm G2 G1] at h

omit [Finite G] in
theorem card_eq_960_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2)) :
    Nat.card G1 = 960 := by
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with ⟨φ₁, -, -, -⟩ | ⟨-, φ₂, -, -⟩
  · rw [← Nat.card_congr φ₁.toEquiv, card_m22TwoStab]
  · rw [← Nat.card_congr φ₂.toEquiv, M22Witt.card_m22PtHexStab]

end Amalgam

section Aut

variable {F : Type*} [Field F] [Finite F]

theorem exists_conjAut_mul_fieldAut_of_map_eq [CharP F 2]
    {P : Subgroup (LinearFlag.projectiveSL 3 F)}
    (hP : P ∈ LinearFlag.maximalParabolics (LinearFlag.projectiveSL 3 F) 2)
    (α : MulAut (LinearFlag.projectiveSL 3 F)) (hα : P.map α.toMonoidHom = P) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F),
      α = LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM, -, -⟩ := LinearFlag.maximal_parabolics (K := F) 2 (by norm_num : 1 ≤ 3)
  obtain ⟨-, -, -, -, -, -, haut⟩ := LinearFlag.incidence_graph (K := F) 2 (le_refl 3)
  obtain ⟨hE, hdisj, -, -, -⟩ := LinearFlag.intrinsic_extremal_parabolics (K := F) 2 (le_refl 3)
  rw [hM] at hP
  obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hP
  obtain ⟨hk1, hk3⟩ := LinearFlag.one_le_finrank_and_lt h0 htop
  have hW : finrank F W = 1 ∨ finrank F W = 3 - 1 := by omega
  have hPE : LinearFlag.projStabilizer W ∈
      LinearFlag.extremalParabolics (LinearFlag.projectiveSL 3 F) 2 := by
    rw [hE]
    rcases hW with h | h
    · exact Or.inl ⟨W, h, rfl⟩
    · exact Or.inr ⟨W, h, rfl⟩
  obtain ⟨Φ, hΦ, hpres⟩ := haut α
  have hfix : (Φ ⟨_, hPE⟩ : Subgroup (LinearFlag.projectiveSL 3 F)) =
      LinearFlag.projStabilizer W := (hΦ _).trans hα
  apply LinearFlag.type_preserving_automorphisms (le_refl 3) α
  intro L hL
  have hLE : LinearFlag.projStabilizer L ∈
      LinearFlag.extremalParabolics (LinearFlag.projectiveSL 3 F) 2 := by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  rcases hpres with ⟨hpp, -⟩ | ⟨hph, hhp⟩
  · obtain ⟨L', hL', hL'eq⟩ := hpp ⟨_, hLE⟩ ⟨L, hL, rfl⟩
    exact ⟨L', hL', (hΦ _).symm.trans hL'eq⟩
  · exfalso
    rcases hW with h | h
    · obtain ⟨H', hH', hH'eq⟩ := hph ⟨_, hPE⟩ ⟨W, h, rfl⟩
      rw [hfix] at hH'eq
      exact Set.disjoint_left.mp hdisj ⟨W, h, rfl⟩ ⟨H', hH', hH'eq.symm⟩
    · obtain ⟨L', hL', hL'eq⟩ := hhp ⟨_, hPE⟩ ⟨W, h, rfl⟩
      rw [hfix] at hL'eq
      exact Set.disjoint_left.mp hdisj ⟨L', hL', hL'eq.symm⟩ ⟨W, h, rfl⟩

theorem exists_conj_of_conjAut_pow_eq_one (hF : Nat.card F = 4) (A : GL (Fin 3) F) {k : ℕ}
    (h : LinearFlag.conjAut 3 F A ^ (2 ^ k) = 1) :
    ∃ y : LinearFlag.projectiveSL 3 F, LinearFlag.conjAut 3 F A = MulAut.conj y := by
  rw [← map_pow] at h
  obtain ⟨c, hc⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff (le_refl 3) _).mp h
  have hU : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hc3 : c ^ 3 = 1 := by rw [← hU]; exact pow_card_eq_one'
  have hd : Matrix.GeneralLinearGroup.det A ^ (2 ^ k) = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hc3] at h1
    exact h1.symm
  have hd3 : Matrix.GeneralLinearGroup.det A ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := Matrix.GeneralLinearGroup.det A)
    rwa [hU] at h1
  have hd1 : Matrix.GeneralLinearGroup.det A = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hd, hd3⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)),
      pow_one] at h1
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 := congrArg (fun u : Fˣ => (u : F)) hd1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1
  set g : Matrix.SpecialLinearGroup (Fin 3) F := ⟨A, hdet⟩
  have hgA : Matrix.SpecialLinearGroup.toGL g = A := Units.ext rfl
  exact ⟨LinearFlag.proj 3 F g, by rw [← hgA, LinearFlag.conjAut_toGL]⟩

end Aut

end CFSG.Quasithin.H13

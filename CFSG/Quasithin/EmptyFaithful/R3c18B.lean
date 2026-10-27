module

public import CFSG.Quasithin.EmptyFaithful.R3c18A
public import CFSG.Quasithin.EmptyFaithful.R3c18Fam
public import CFSG.Quasithin.EmptyFaithful.R3c18G
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.Quasithin

namespace R3c18

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartTwo.KFacts CFSG.Open CFSG.QuasithinUnique.Fin257
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

@[expose] def g2B : Fin Tag.G2.rank → ℤ := ![0, 1]

@[expose] def g2C : Fin Tag.G2.rank → ℤ := ![2, 3]

@[expose] def g2Roots : List (List ℤ) :=
  [[1, 0], [0, 1], [-1, 0], [1, 3], [1, 1], [0, -1], [-1, -3], [2, 3], [1, 2], [-1, -1], [-2, -3],
    [-1, -2]]

theorem g2_rootList : ∀ k < Tag.G2.rootCertificate.roots.length,
    List.ofFn (Tag.G2.rootCertificate.root k) ∈ g2Roots := by
  unfold g2Roots
  decide +kernel

theorem g2_rootList' : ∀ v ∈ g2Roots, ∃ k < Tag.G2.rootCertificate.roots.length,
    List.ofFn (Tag.G2.rootCertificate.root k) = v := by
  unfold g2Roots
  decide +kernel

section Roots


theorem g2_isRoot_iff_mem (v : Fin Tag.G2.rank → ℤ) : IsRoot Tag.G2 v ↔ List.ofFn v ∈ g2Roots := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check _)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact g2_rootList k hk
  · intro h
    obtain ⟨k, hk, hkv⟩ := g2_rootList' _ h
    exact ⟨k, hk, List.ofFn_injective hkv⟩

theorem g2B_isRoot : IsRoot Tag.G2 g2B := by
  rw [g2_isRoot_iff_mem]
  unfold g2B g2Roots
  decide +kernel

theorem g2C_isRoot : IsRoot Tag.G2 g2C := by
  rw [g2_isRoot_iff_mem]
  unfold g2C g2Roots
  decide +kernel

theorem g2_not_isRoot_add : ¬ IsRoot Tag.G2 (g2B + g2C) := by
  rw [g2_isRoot_iff_mem]
  unfold g2B g2C g2Roots
  decide +kernel

theorem g2_not_isRoot_sub : ¬ IsRoot Tag.G2 (g2B - g2C) := by
  rw [g2_isRoot_iff_mem]
  unfold g2B g2C g2Roots
  decide +kernel

end Roots

theorem g2_iform : CFSG.LieType.Steinberg.Adjoint.iform g2B g2C = 0 := by
  unfold g2B g2C
  decide +kernel

@[expose] def G2PRankShape : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] {p m : ℕ}, p.Prime → 5 ≤ p → Nat.card K = 2 ^ m →
    1 ≤ m → p ∣ Nat.card (adjointGroup Tag.G2 K) → ¬ p ∣ Nat.card K ^ 2 - 1 →
    CFSG.pRank p (adjointGroup Tag.G2 K) ≤ 1

section Construction

set_option linter.unusedSectionVars false


theorem g2_orth_commute {K : Type} [Field K] (A B : SL2 K) :
    Commute (rootSL2 Tag.G2 K g2B A) (rootSL2 Tag.G2 K g2C B) :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.G2 K g2B_isRoot g2C_isRoot
    g2_iform g2_not_isRoot_add g2_not_isRoot_sub _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

theorem exists_sq_g2 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) {a : SL2 K} (ha : orderOf a = p)
    (hfix : Matrix.SpecialLinearGroup.map σ.toRingHom a = a) :
    ∃ E : Subgroup (adjointGroup Tag.G2 K), Nat.card E = p ^ 2 ∧ IsElemAbelian p E ∧
      ∀ y ∈ E, g2FieldHom K σ y = y := by
  classical
  obtain ⟨hinjβ, -, -, -, -, -, -, -, hnatβ, -⟩ :=
    even_Chevalley_pinned_root_SL2_maps Tag.G2 K g2B_isRoot
  obtain ⟨hinjγ, -, -, -, -, -, -, -, hnatγ, -⟩ :=
    even_Chevalley_pinned_root_SL2_maps Tag.G2 K g2C_isRoot
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  set H : Subgroup (adjointGroup Tag.G2 K) :=
    (g2FieldHom K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hH
  have hu₁ : (⟨rootSL2 Tag.G2 K g2B a, rootSL2_mem_adjointGroup _ _⟩ : adjointGroup Tag.G2 K) ∈ H := by
    change g2FieldHom K σ _ = _
    apply Subtype.ext
    rw [coe_g2FieldHom]
    change Units.map (entrywiseHom σ.toRingHom) (rootSL2 Tag.G2 K g2B a) = rootSL2 Tag.G2 K g2B a
    rw [hnatβ σ.toRingHom a, hfix]
  have hu₂ : (⟨rootSL2 Tag.G2 K g2C a, rootSL2_mem_adjointGroup _ _⟩ : adjointGroup Tag.G2 K) ∈ H := by
    change g2FieldHom K σ _ = _
    apply Subtype.ext
    rw [coe_g2FieldHom]
    change Units.map (entrywiseHom σ.toRingHom) (rootSL2 Tag.G2 K g2C a) = rootSL2 Tag.G2 K g2C a
    rw [hnatγ σ.toRingHom a, hfix]
  set v₁ : H := ⟨_, hu₁⟩ with hv₁
  set v₂ : H := ⟨_, hu₂⟩ with hv₂
  have hc : v₁ * v₂ = v₂ * v₁ := Subtype.ext (Subtype.ext (g2_orth_commute a a))
  have hv₁p : v₁ ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (rootSL2 Tag.G2 K g2B a) ^ p = 1
    rw [← map_pow, hap, map_one]
  have hv₂p : v₂ ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (rootSL2 Tag.G2 K g2C a) ^ p = 1
    rw [← map_pow, hap, map_one]
  have hind : ∀ i j : ℕ, v₁ ^ i * v₂ ^ j = 1 → p ∣ i ∧ p ∣ j := by
    intro i j h
    have h0 := congrArg (fun w : H => ((w : adjointGroup Tag.G2 K) : ModGL Tag.G2 K)) h
    have h1 : rootSL2 Tag.G2 K g2B (a ^ i) * rootSL2 Tag.G2 K g2C (a ^ j) = 1 := by
      change (rootSL2 Tag.G2 K g2B a) ^ i * (rootSL2 Tag.G2 K g2C a) ^ j = 1 at h0
      rwa [← map_pow, ← map_pow] at h0
    have hβγ : rootSL2 Tag.G2 K g2B (a ^ i) = (rootSL2 Tag.G2 K g2C (a ^ j))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have hγβ : rootSL2 Tag.G2 K g2C (a ^ j) = (rootSL2 Tag.G2 K g2B (a ^ i))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    have hai : a ^ i = 1 := by
      refine eq_one_of_forall_commute_sl2 fun A => hinjβ ?_
      rw [map_mul, map_mul, hβγ]
      exact ((g2_orth_commute A (a ^ j)).inv_right).symm.eq
    have haj : a ^ j = 1 := by
      refine eq_one_of_forall_commute_sl2 fun B => hinjγ ?_
      rw [map_mul, map_mul, hγβ]
      exact ((g2_orth_commute (a ^ i) B).inv_left).eq
    rw [← ha]
    exact ⟨orderOf_dvd_of_pow_eq_one hai, orderOf_dvd_of_pow_eq_one haj⟩
  obtain ⟨P₀, hel, hcard, -, -⟩ := exists_elemAbelian_pair hp hc hv₁p hv₂p hind
  refine ⟨P₀.map H.subtype, ?_, CFSG.SectionRank.isElemAbelian_map hel H.subtype, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
  · rintro _ ⟨w, -, rfl⟩
    exact w.2

end Construction

section Frame

set_option linter.unusedSectionVars false


@[expose] noncomputable def pFrameG2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hshape : G2PRankShape)
    (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    PFrame p ↥(adjointGroup Tag.G2 K) (K ≃+* K) where
  fld := g2FieldHom K
  fld_inter := fun c hc =>
    (g2_automorphism_normal_form (by rw [ringChar.eq K 2]; norm_num) (by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)).2 c hc
  conj_mem := fun α _ _ => by
    obtain ⟨g, σ, h⟩ := (g2_automorphism_normal_form (K := K) (by rw [ringChar.eq K 2]; norm_num) (by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)).1 α
    exact ⟨1, MulAut.conj g, ⟨g, rfl⟩, σ, by rw [h]; simp⟩
  sq := fun h2 c hc => by
    have hdvdG : p ∣ Nat.card (adjointGroup Tag.G2 K) := dvd_card_of_two_le_pRank hp h2
    have hf1 : 1 ≤ f := by omega
    have hd : p ∣ Nat.card K ^ 2 - 1 := by
      by_contra hnd
      have := hshape K hp hp5 hK hf1 hdvdG hnd
      omega
    obtain ⟨hpf, k, hk, hkcard⟩ := exists_fixed_subfield hf1 hK c hc
    have hKk : Nat.card K = Nat.card k ^ p := by
      rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hq0 : 0 < Nat.card k := by
      rw [hkcard]
      exact pow_pos (by norm_num) _
    have hd' : p ∣ Nat.card k ^ 2 - 1 := by
      rw [hKk] at hd
      exact (dvd_pow_sub_one_iff_of_pow hp hq0 2).1 hd
    obtain ⟨a, ha, hfix⟩ := exists_fixed_sl2_elem c hk hp hd'
    exact exists_sq_g2 c hp ha hfix

theorem qLiePRankFam_g2 (hshape : G2PRankShape) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) := by
  classical
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hf, hS⟩ hS2 hX
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hS
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card]; exact hKcard)
  let ψ : ↥S ≃* ↥(adjointGroup Tag.G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)
  have : Fact p.Prime := ⟨hp⟩
  exact pframe_core hC ((pFrameG2 hp hp5 hshape K hKcard hf).ofMulEquiv hp.one_lt ψ) hS2 hX

end Frame

end R3c18

end CFSG.Quasithin

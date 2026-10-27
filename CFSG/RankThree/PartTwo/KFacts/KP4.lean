module

public import CFSG.RankThree.PartTwo.KFacts.KP4Gen
public import CFSG.RankThree.PartTwo.KFacts.KP4Aut
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import Certificates.Certificate13951

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.WittDesign
open CFSG.RankThree.Asc83Table (Automizer automizerCongr automizerOfEq)
open CFSG.RankThree.Asc83Table.M22 (x y X Y E GI)
open CFSG.RankThree.PartTwo (invariantPiSubgroups maxInvariantPiSubgroups piCompl piOf)
open CFSG.RankThree.PartTwo.Sec4.Sporadic (map_symm_map map_map_symm image_maxInvariantPiSubgroups
  map_mem_invariantPiSubgroups_iff)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

section Transport

variable {G G' : Type*} [Group G] [Group G'] (ψ : G ≃* G')

theorem map_centralizer_singleton (a : G) :
    (centralizer ({a} : Set G)).map ψ.toMonoidHom = centralizer ({ψ a} : Set G') := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg ψ h
    simpa using this
  · intro h
    apply ψ.injective
    simpa using h

theorem map_theta [Finite G] (X : Subgroup G) :
    (inSubgroup (aschbacherSolvableCore 3) X).map ψ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (X.map ψ.toMonoidHom) :=
  CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv
    Nat.prime_three ψ X

theorem map_pCore_two (X : Subgroup G) :
    (inSubgroup (CFSG.pCore 2) X).map ψ.toMonoidHom =
      inSubgroup (CFSG.pCore 2) (X.map ψ.toMonoidHom) :=
  CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore 2 ψ X

theorem map_pPrimeCoreOf (X : Subgroup G) :
    (CFSG.GH74.GLS.pPrimeCoreOf 3 X).map ψ.toMonoidHom =
      CFSG.GH74.GLS.pPrimeCoreOf 3 (X.map ψ.toMonoidHom) :=
  CFSG.RankThree.PartTwo.Sec14.map_pPrimeCoreOf 3 ψ X

theorem map_top_equiv : (⊤ : Subgroup G).map ψ.toMonoidHom = ⊤ :=
  Subgroup.map_top_of_surjective _ ψ.surjective

theorem map_sSup_equiv (F : Set (Subgroup G)) :
    (sSup F).map ψ.toMonoidHom = sSup ((fun Q : Subgroup G => Q.map ψ.toMonoidHom) '' F) := by
  refine le_antisymm ?_ (sSup_le ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Q hQ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨Q, hQ, rfl⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    exact Subgroup.map_mono (le_sSup hQ)

end Transport

variable {L : Type*} [Group L]

theorem finite_of_nonempty (hL : Nonempty (L ≃* NativeSporadic.M22)) : Finite L := by
  obtain ⟨e⟩ := hL
  exact Finite.of_equiv _ e.symm.toEquiv

theorem exists_equiv_P0 (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) : ∃ ψ : G22 ≃* L, P0.map ψ.toMonoidHom = B := by
  obtain ⟨e⟩ := hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card P0 = 3 ^ (Nat.card G22).factorization 3 := by
    rw [card_P0, CFSG.RankThree.Asc83Table.M22.factorization_card]
    norm_num
  set B' := B.map e.toMonoidHom
  have hB' : Nat.card B' = 9 := by rw [Subgroup.card_map_of_injective e.injective, hB]
  have hp : IsPGroup 3 B' := IsPGroup.of_card (n := 2) (by rw [hB']; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP hp
  have heq : B'.map (MulAut.conj g).toMonoidHom = P0 :=
    Subgroup.eq_of_le_of_card_ge hg
      (by rw [card_P0, CFSG.RankThree.Asc83Table.card_map_conj, hB'])
  set φ : L ≃* G22 := e.trans (MulAut.conj g)
  have hBφ : B.map φ.toMonoidHom = P0 := by
    rw [← heq, Subgroup.map_map]
    rfl
  refine ⟨φ.symm, ?_⟩
  rw [← hBφ]
  exact map_symm_map φ B

theorem mem_map_P0 {ψ : G22 ≃* L} {B : Subgroup L} (hψ : P0.map ψ.toMonoidHom = B) {a : L}
    (ha : a ∈ B) : ∃ a' ∈ P0, ψ a' = a := by
  rw [← hψ] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  exact ⟨a', ha', rfl⟩

theorem m22_isElementaryAbelian (hL : Nonempty (L ≃* NativeSporadic.M22))
    {B : Subgroup L} (hB : Nat.card B = 9) : IsElementaryAbelian 3 B := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [← hψ]
  exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ E.isElementaryAbelian

theorem m22_nonempty_automizer_equiv (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) : Nonempty (Automizer B ≃* QuaternionGroup 2) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.M22.automizer_P0
  exact ⟨((automizerCongr ψ P0).trans (automizerOfEq hψ)).symm.trans q⟩

theorem m22_centralizer_eq (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) : centralizer (B : Set L) = B := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [← hψ, ← CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq, centralizer_P0]

theorem m22_card_normalizer (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) : Nat.card (normalizer (B : Set L)) = 72 := by
  have : Finite L := finite_of_nonempty hL
  obtain ⟨q⟩ := m22_nonempty_automizer_equiv hL hB
  have h8 : Nat.card (Automizer B) = 8 := by
    rw [Nat.card_congr q.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hle := Subgroup.centralizer_le_normalizer (B : Set L)
  have h9 : Nat.card ((centralizer (B : Set L)).subgroupOf (normalizer (B : Set L))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, m22_centralizer_eq hL hB, hB]
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((centralizer (B : Set L)).subgroupOf (normalizer (B : Set L)))
  rw [this, h9]
  change Nat.card (Automizer B) * 9 = 72
  rw [h8]

theorem GI_mem_normalizer : GI ∈ normalizer (P0 : Set G22) := by
  have h := E.mem_normalizer_of_conj 0 2 1 0 CFSG.RankThree.Asc83Table.M22.GI_X
    CFSG.RankThree.Asc83Table.M22.GI_Y
  rwa [E.closure_range] at h

theorem m22_centralizer_facts (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {a : L} (ha : a ∈ B) (ha1 : a ≠ 1) :
    Nat.card (centralizer ({a} : Set L)) = 36 ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      CFSG.GH74.GLS.pPrimeCoreOf 3 (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      Nat.card (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L))) = 4 ∧
      IsElementaryAbelian 2 (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L))) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  obtain ⟨a', ha', rfl⟩ := mem_map_P0 hψ ha
  have ha1' : a' ≠ 1 := fun h => ha1 (by rw [h, map_one])
  obtain ⟨i, hi⟩ := exists_centralizer_eq ha' ha1'
  have hC : centralizer ({ψ a'} : Set L) =
      (centralizer ({lineE i} : Set G22)).map ψ.toMonoidHom := by
    rw [← hi, map_centralizer_singleton]
  rw [hC, ← map_theta, ← map_pCore_two, ← map_pPrimeCoreOf, theta_centralizer_line,
    pCore_centralizer_line, pPrimeCoreOf_centralizer_line]
  refine ⟨?_, rfl, rfl, ?_, CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _
    (isElementaryAbelian_V i)⟩
  · rw [Subgroup.card_map_of_injective ψ.injective, card_centralizer_line]
  · rw [Subgroup.card_map_of_injective ψ.injective, card_V]

theorem m22_centralizer_facts_of_orderOf (hL : Nonempty (L ≃* NativeSporadic.M22)) {a : L}
    (ha : orderOf a = 3) :
    Nat.card (centralizer ({a} : Set L)) = 36 ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      CFSG.GH74.GLS.pPrimeCoreOf 3 (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      Nat.card (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L))) = 4 ∧
      IsElementaryAbelian 2 (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L))) := by
  have : Finite L := finite_of_nonempty hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hL
  have hp : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; rfl)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hcard : Nat.card (P : Subgroup L) = 9 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      CFSG.RankThree.Asc83Table.M22.factorization_card]
    norm_num
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  exact m22_centralizer_facts ⟨e⟩ hcard (hP (mem_zpowers a)) ha1

theorem conj_x_facts : ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ k l : Fin 4,
    (GI : Perm (Fin 22)) ^ (k : ℕ) * (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ) *
        (X : Perm (Fin 22)) *
      ((GI : Perm (Fin 22)) ^ (k : ℕ) *
        (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ))⁻¹ =
      (X : Perm (Fin 22)) ^ (a : ℕ) * (Y : Perm (Fin 22)) ^ (b : ℕ) :=
  Certificates.certificate13951.2

theorem isConj_X_of_mem_P0 {c : G22} (hc : c ∈ P0) (hc1 : c ≠ 1) : IsConj X c := by
  obtain ⟨a, b, ha, hb, rfl⟩ := E.exists_pow_mul_pow hc
  have hab : ((⟨a, ha⟩ : Fin 3), (⟨b, hb⟩ : Fin 3)) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_zero] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc1 (by simp)
  obtain ⟨k, l, hkl⟩ := conj_x_facts ⟨a, ha⟩ ⟨b, hb⟩ hab
  refine isConj_iff.2 ⟨GI ^ (k : ℕ) * CFSG.RankThree.Asc83Table.M22.GJ ^ (l : ℕ), ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact hkl

theorem isConj_X_of_orderOf {c : G22} (hc : orderOf c = 3) : IsConj X c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card P0 = 3 ^ (Nat.card G22).factorization 3 := by
    rw [card_P0, CFSG.RankThree.Asc83Table.M22.factorization_card]
    norm_num
  have hp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc]; rfl)
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP hp
  have hgc : g * c * g⁻¹ ∈ P0 := hg ⟨c, mem_zpowers c, rfl⟩
  have hgc1 : g * c * g⁻¹ ≠ 1 := by
    intro h
    have : c = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hc
    norm_num at hc
  exact (isConj_X_of_mem_P0 hgc hgc1).trans (isConj_iff.2 ⟨g, rfl⟩).symm

theorem m22_isConj_of_orderOf (hL : Nonempty (L ≃* NativeSporadic.M22)) {a b : L}
    (ha : orderOf a = 3) (hb : orderOf b = 3) : IsConj a b := by
  obtain ⟨e⟩ := hL
  have ha' : orderOf (e a) = 3 := by rw [MulEquiv.orderOf_eq]; exact ha
  have hb' : orderOf (e b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
  have h := e.symm.toMonoidHom.map_isConj
    ((isConj_X_of_orderOf ha').symm.trans (isConj_X_of_orderOf hb'))
  simpa using h

theorem maxInvariant_threePrime_map {ψ : G22 ≃* L} {B : Subgroup L}
    (hψ : P0.map ψ.toMonoidHom = B) :
    maxInvariantPiSubgroups ⊤ B (piCompl 3) =
      {(R 0).map ψ.toMonoidHom, (R 1).map ψ.toMonoidHom} := by
  rw [← hψ, ← map_top_equiv ψ, ← image_maxInvariantPiSubgroups, maxInvariant_threePrime,
    Set.image_pair]

theorem maxInvariant_two_map {ψ : G22 ≃* L} {B : Subgroup L} (hψ : P0.map ψ.toMonoidHom = B) :
    maxInvariantPiSubgroups ⊤ B (piOf 2) = {(R 0).map ψ.toMonoidHom, (R 1).map ψ.toMonoidHom} := by
  rw [← hψ, ← map_top_equiv ψ, ← image_maxInvariantPiSubgroups, maxInvariant_two,
    Set.image_pair]

theorem m22_maxInvariant_threePrime_eq_two (hL : Nonempty (L ≃* NativeSporadic.M22))
    {B : Subgroup L} (hB : Nat.card B = 9) :
    maxInvariantPiSubgroups ⊤ B (piCompl 3) = maxInvariantPiSubgroups ⊤ B (piOf 2) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [maxInvariant_threePrime_map hψ, maxInvariant_two_map hψ]

theorem m22_isPGroup_of_mem_invariant (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {Q : Subgroup L} (hQ : Q ∈ invariantPiSubgroups ⊤ B (piCompl 3)) :
    IsPGroup 2 Q := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  subst hψ
  have hQ' : Q.map ψ.symm.toMonoidHom ∈ invariantPiSubgroups ⊤ P0 (piCompl 3) := by
    have := (map_mem_invariantPiSubgroups_iff ψ.symm (H := ⊤) (A := P0.map ψ.toMonoidHom)
      (X := Q) (π := piCompl 3)).2 hQ
    rwa [map_top_equiv, map_symm_map] at this
  exact (isPGroup_of_mem_invariant hQ').of_equiv (ψ.symm.subgroupMap Q).symm

theorem m22_maxInvariant_structure (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {R' : Subgroup L} (hR : R' ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3)) :
    IsElementaryAbelian 2 R' ∧ Nat.card R' = 16 ∧ ∃ a b : L, a ∈ B ∧ b ∈ B ∧
      closure ({a, b} : Set L) = B ∧
      R' ⊓ centralizer ({a} : Set L) = inSubgroup (aschbacherSolvableCore 3)
        (centralizer ({a} : Set L)) ∧
      R' ⊓ centralizer ({b} : Set L) = inSubgroup (aschbacherSolvableCore 3)
        (centralizer ({b} : Set L)) ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊓
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) = ⊥ ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊔
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) = R' ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({b} : Set L)) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [maxInvariant_threePrime_map hψ] at hR
  have key : ∀ j : Fin 2, R' = (R j).map ψ.toMonoidHom → IsElementaryAbelian 2 R' ∧
      Nat.card R' = 16 ∧ ∃ a b : L, a ∈ B ∧ b ∈ B ∧ closure ({a, b} : Set L) = B ∧
      R' ⊓ centralizer ({a} : Set L) = inSubgroup (aschbacherSolvableCore 3)
        (centralizer ({a} : Set L)) ∧
      R' ⊓ centralizer ({b} : Set L) = inSubgroup (aschbacherSolvableCore 3)
        (centralizer ({b} : Set L)) ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊓
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) = ⊥ ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊔
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) = R' ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set L)) ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) =
        inSubgroup (CFSG.pCore 2) (centralizer ({b} : Set L)) := by
    rintro j rfl
    have hθa : inSubgroup (aschbacherSolvableCore 3) (centralizer ({ψ (lineE (hexFst j))} :
        Set L)) = (V (hexFst j)).map ψ.toMonoidHom := by
      rw [← map_centralizer_singleton, ← map_theta, theta_centralizer_line]
    have hθb : inSubgroup (aschbacherSolvableCore 3) (centralizer ({ψ (lineE (hexSnd j))} :
        Set L)) = (V (hexSnd j)).map ψ.toMonoidHom := by
      rw [← map_centralizer_singleton, ← map_theta, theta_centralizer_line]
    have hOa : inSubgroup (CFSG.pCore 2) (centralizer ({ψ (lineE (hexFst j))} : Set L)) =
        (V (hexFst j)).map ψ.toMonoidHom := by
      rw [← map_centralizer_singleton, ← map_pCore_two, pCore_centralizer_line]
    have hOb : inSubgroup (CFSG.pCore 2) (centralizer ({ψ (lineE (hexSnd j))} : Set L)) =
        (V (hexSnd j)).map ψ.toMonoidHom := by
      rw [← map_centralizer_singleton, ← map_pCore_two, pCore_centralizer_line]
    refine ⟨CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ (isElementaryAbelian_R j),
      by rw [Subgroup.card_map_of_injective ψ.injective, card_R],
      ψ (lineE (hexFst j)), ψ (lineE (hexSnd j)), hψ ▸ mem_map_of_mem _ (lineE_mem_P0 _),
      hψ ▸ mem_map_of_mem _ (lineE_mem_P0 _), ?_, ?_, ?_, ?_, ?_, by rw [hθa, hOa],
      by rw [hθb, hOb]⟩
    · rw [← hψ, ← closure_hex_eq j, MonoidHom.map_closure, Set.image_pair]
      rfl
    · rw [hθa, ← map_centralizer_singleton, ← Subgroup.map_inf _ _ _ ψ.injective,
        R_inf_centralizer_fst]
    · rw [hθb, ← map_centralizer_singleton, ← Subgroup.map_inf _ _ _ ψ.injective,
        R_inf_centralizer_snd]
    · rw [hθa, hθb, ← Subgroup.map_inf _ _ _ ψ.injective, V_inf_V, Subgroup.map_bot]
    · rw [hθa, hθb, ← Subgroup.map_sup]
      rfl
  rcases hR with h | h
  · exact key 0 h
  · exact key 1 h

theorem m22_maxInvariant_eq_pair (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) : ∃ a b : L, a ∈ B ∧ b ∈ B ∧ closure ({a, b} : Set L) = B ∧
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊔
          inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)) ≠
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({a * b} : Set L)) ⊔
          inSubgroup (aschbacherSolvableCore 3) (centralizer ({a * b ^ 2} : Set L)) ∧
      maxInvariantPiSubgroups ⊤ B (piCompl 3) =
        {inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set L)) ⊔
            inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set L)),
          inSubgroup (aschbacherSolvableCore 3) (centralizer ({a * b} : Set L)) ⊔
            inSubgroup (aschbacherSolvableCore 3) (centralizer ({a * b ^ 2} : Set L))} := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  have hθ : ∀ i : Fin 4, inSubgroup (aschbacherSolvableCore 3) (centralizer
      ({ψ (lineE i)} : Set L)) = (V i).map ψ.toMonoidHom := fun i => by
    rw [← map_centralizer_singleton, ← map_theta, theta_centralizer_line]
  have h0 : ψ X = ψ (lineE 0) := by rw [lineE_eq]; simp [lineA, lineB]
  have h1 : ψ Y = ψ (lineE 1) := by rw [lineE_eq]; simp [lineA, lineB]
  have h2 : ψ X * ψ Y = ψ (lineE 2) := by rw [lineE_eq, ← map_mul]; simp [lineA, lineB]
  have h3 : ψ X * ψ Y ^ 2 = ψ (lineE 3) := by
    rw [lineE_eq, ← map_pow, ← map_mul]; simp [lineA, lineB]
  have hR0 : (R 0).map ψ.toMonoidHom = (V 0).map ψ.toMonoidHom ⊔ (V 1).map ψ.toMonoidHom :=
    Subgroup.map_sup _ _ _
  have hR1 : (R 1).map ψ.toMonoidHom = (V 2).map ψ.toMonoidHom ⊔ (V 3).map ψ.toMonoidHom :=
    Subgroup.map_sup _ _ _
  refine ⟨ψ X, ψ Y, hψ ▸ mem_map_of_mem _ X_mem_P0, hψ ▸ mem_map_of_mem _ Y_mem_P0, ?_, ?_, ?_⟩
  · rw [← hψ, MonoidHom.map_closure, Set.image_pair]
    rfl
  · rw [h2, h3, h0, h1, hθ, hθ, hθ, hθ, ← hR0, ← hR1]
    exact fun h => R_ne (Subgroup.map_injective ψ.injective h)
  · rw [maxInvariant_threePrime_map hψ, h2, h3, h0, h1, hθ, hθ, hθ, hθ, hR0, hR1]

theorem m22_normalizer_quotient (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {R' : Subgroup L} (hR : R' ∈ maxInvariantPiSubgroups ⊤ B (piOf 2)) :
    Nat.card (normalizer (R' : Set L)) = 5760 ∧
      Nonempty (normalizer (R' : Set L) ⧸ R'.subgroupOf (normalizer (R' : Set L)) ≃*
        alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [maxInvariant_two_map hψ] at hR
  have key : ∀ j : Fin 2, R' = (R j).map ψ.toMonoidHom →
      Nat.card (normalizer (R' : Set L)) = 5760 ∧
      Nonempty (normalizer (R' : Set L) ⧸ R'.subgroupOf (normalizer (R' : Set L)) ≃*
        alternatingGroup (Fin 6)) := by
    rintro j rfl
    have hN : (normalizer (R j : Set G22)).map ψ.toMonoidHom =
        normalizer (((R j).map ψ.toMonoidHom : Subgroup L) : Set L) :=
      Subgroup.map_equiv_normalizer_eq _ _
    refine ⟨by rw [← hN, Subgroup.card_map_of_injective ψ.injective, card_normalizer_R], ?_⟩
    obtain ⟨q⟩ := nonempty_normalizer_quotient_equiv j
    let e : normalizer (R j : Set G22) ≃*
        normalizer (((R j).map ψ.toMonoidHom : Subgroup L) : Set L) :=
      (ψ.subgroupMap _).trans (MulEquiv.subgroupCongr hN)
    have he : ((R j).subgroupOf (normalizer (R j : Set G22))).map e.toMonoidHom =
        ((R j).map ψ.toMonoidHom).subgroupOf
          (normalizer (((R j).map ψ.toMonoidHom : Subgroup L) : Set L)) := by
      ext g
      simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact mem_map_of_mem ψ.toMonoidHom hh
      · intro hg
        refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
        obtain ⟨r, hr, hrg⟩ := hg
        have : ((e.symm g : normalizer (R j : Set G22)) : G22) = r := by
          apply ψ.injective
          have h1 : ψ ((e.symm g : normalizer (R j : Set G22)) : G22) =
              ((e (e.symm g) : normalizer _) : L) := rfl
          rw [h1, e.apply_symm_apply]
          exact hrg.symm
        rw [this]
        exact hr
    exact ⟨(QuotientGroup.congr _ _ e he).symm.trans q⟩
  rcases hR with h | h
  · exact key 0 h
  · exact key 1 h

theorem m22_sup_eq_top_of_seven (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {R' : Subgroup L} (hR : R' ∈ maxInvariantPiSubgroups ⊤ B (piOf 2))
    {X' : Subgroup L} (hX : B ≤ normalizer (X' : Set L)) (h7 : 7 ∣ Nat.card X') :
    R' ⊔ X' = ⊤ := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  rw [maxInvariant_two_map hψ] at hR
  set X := X'.map ψ.symm.toMonoidHom
  have hXP : P0 ≤ normalizer (X : Set G22) := by
    have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hX
    rwa [← hψ, map_symm_map, Subgroup.map_equiv_normalizer_eq] at this
  have hX7 : 7 ∣ Nat.card X := by rwa [Subgroup.card_map_of_injective ψ.symm.injective]
  have hXX : X' = X.map ψ.toMonoidHom := (map_map_symm ψ X').symm
  have key : ∀ j : Fin 2, R' = (R j).map ψ.toMonoidHom → R' ⊔ X' = ⊤ := by
    rintro j rfl
    rw [hXX, ← Subgroup.map_sup, sup_eq_top_of_seven j hXP hX7, map_top_equiv]
  rcases hR with h | h
  · exact key 0 h
  · exact key 1 h

theorem m22_sSup_cases (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) (F : Set (Subgroup L))
    (hF : F ⊆ invariantPiSubgroups ⊤ B (piCompl 3)) :
    IsPGroup 2 (sSup F : Subgroup L) ∨ (B ≤ sSup F ∧
      Nonempty ((sSup F : Subgroup L) ≃* alternatingGroup (Fin 7))) ∨ sSup F = ⊤ := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  subst hψ
  set F' := (fun Q : Subgroup L => Q.map ψ.symm.toMonoidHom) '' F
  have hF' : F' ⊆ invariantPiSubgroups ⊤ P0 (piCompl 3) := by
    rintro _ ⟨Q, hQ, rfl⟩
    have := (map_mem_invariantPiSubgroups_iff ψ.symm (H := ⊤) (A := P0.map ψ.toMonoidHom)
      (X := Q) (π := piCompl 3)).2 (hF hQ)
    rwa [map_top_equiv, map_symm_map] at this
  have hsup : sSup F' = (sSup F).map ψ.symm.toMonoidHom := (map_sSup_equiv ψ.symm F).symm
  have hback : sSup F = (sSup F').map ψ.toMonoidHom := by
    rw [hsup, map_map_symm]
  rcases sSup_cases F' hF' with h | ⟨hP, ⟨q⟩⟩ | h
  · left
    rw [hsup] at h
    exact h.of_equiv (ψ.symm.subgroupMap (sSup F)).symm
  · right; left
    refine ⟨?_, ⟨?_⟩⟩
    · rw [hback]
      exact Subgroup.map_mono hP
    · rw [hback]
      exact (ψ.subgroupMap (sSup F')).symm.trans q
  · right; right
    rw [hback, h, map_top_equiv]

theorem congr_symm_apply (ψ : G22 ≃* L) (α : MulAut L) (g : G22) :
    ((MulAut.congr ψ).symm α) g = ψ.symm (α (ψ g)) := rfl

theorem map_congr_symm {ψ : G22 ≃* L} (α : MulAut L) (H : Subgroup L) :
    (H.map ψ.symm.toMonoidHom).map ((MulAut.congr ψ).symm α).toMonoidHom =
      (H.map α.toMonoidHom).map ψ.symm.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp

theorem m22_aut_pow_eight (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {α : MulAut L} (hα : B.map α.toMonoidHom = B) {b : L} (hb : b ∈ B) :
    (α ^ 8) b = b := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  set β := (MulAut.congr ψ).symm α
  have hβ : P0.map β.toMonoidHom = P0 := by
    have : P0 = B.map ψ.symm.toMonoidHom := by rw [← hψ, map_symm_map]
    rw [this, map_congr_symm, hα]
  obtain ⟨b', hb', rfl⟩ := mem_map_P0 hψ hb
  have h := aut_pow_eight hβ hb'
  have hαβ : α = MulAut.congr ψ β := ((MulAut.congr ψ).apply_symm_apply α).symm
  have hpow : (α ^ 8) (ψ b') = ψ ((β ^ 8) b') := by
    rw [hαβ, ← map_pow, MulAut.congr_apply]
    simp
  rw [hpow, h]

theorem m22_aut_fix_eq_conj (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {α : MulAut L} (hα : ∀ b ∈ B, α b = b) :
    ∃ c ∈ B, α = MulAut.conj c := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  set β := (MulAut.congr ψ).symm α
  have hβ : ∀ b ∈ P0, β b = b := by
    intro b hb
    rw [congr_symm_apply, hα _ (hψ ▸ mem_map_of_mem _ hb), MulEquiv.symm_apply_apply]
  obtain ⟨c, hc, hβc⟩ := aut_fix_eq_conj hβ
  refine ⟨ψ c, hψ ▸ mem_map_of_mem _ hc, ?_⟩
  have : α = MulAut.congr ψ β := ((MulAut.congr ψ).apply_symm_apply α).symm
  rw [this, hβc, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

theorem m22_aut_threePrime_le_range (hL : Nonempty (L ≃* NativeSporadic.M22)) {B : Subgroup L}
    (hB : Nat.card B = 9) {Q : Subgroup (MulAut L)} (h3 : ¬ 3 ∣ Nat.card Q)
    (hQ : B.map (MulAut.conj : L →* MulAut L) ≤ normalizer (Q : Set (MulAut L))) :
    Q ≤ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hL hB
  set c := MulAut.congr ψ
  set Q' := Q.map c.symm.toMonoidHom
  have hQ3 : ¬ 3 ∣ Nat.card Q' := by rwa [Subgroup.card_map_of_injective c.symm.injective]
  have hP : P0.map (MulAut.conj : G22 →* MulAut G22) ≤ normalizer (Q' : Set (MulAut G22)) := by
    have h1 : (P0.map (MulAut.conj : G22 →* MulAut G22)).map c.toMonoidHom =
        B.map (MulAut.conj : L →* MulAut L) := by
      rw [← hψ, CFSG.RankThree.PartTwo.Sec4.Sporadic.map_map_conj]
    have := Subgroup.map_mono (f := c.symm.toMonoidHom) hQ
    rwa [← h1, map_symm_map, Subgroup.map_equiv_normalizer_eq] at this
  have hle := aut_threePrime_le_inner hP hQ3
  have hQQ : Q = Q'.map c.toMonoidHom := (map_map_symm c Q).symm
  rw [hQQ]
  have := Subgroup.map_mono (f := c.toMonoidHom) hle
  rwa [show (MulAut.conj : G22 →* MulAut G22).range.map c.toMonoidHom =
    (MulAut.conj : L →* MulAut L).range from
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ] at this

end CFSG.RankThree.PartTwo.KFacts.KP4

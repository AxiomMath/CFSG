module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieE27
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieType
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieField
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterUni
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossUnit

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.GH74.GLS.IVK (fixedField)

theorem false_of_e9_of_isCyclic_sylow {X : Type*} [Group X] [Finite X]
    (hcyc : ∀ Q : Sylow 3 X, IsCyclic Q) {E : Subgroup X} (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE9 : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  haveI := hcyc Q
  haveI : IsCyclic (E.subgroupOf (Q : Subgroup X)) := Subgroup.isCyclic _
  have heq : E.subgroupOf (Q : Subgroup X) ≃* E := Subgroup.subgroupOfEquivOfLe hQ
  haveI : IsCyclic E := isCyclic_of_surjective heq.toMonoidHom heq.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hord : orderOf g = 9 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hE9]
  have h3 : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 _ g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hord] at this
  norm_num at this

section Rows


variable {S : Type} [Group S] [Finite S]

theorem fix_of_le {σ : MulAut S} {C K : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hKC : K ≤ C) :
    ∀ k ∈ K, σ k = k := fun k hk => (hC k).mp (hKC hk)

theorem exists_ne_one_pow_three {E : Subgroup S} (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ k ∈ E, k ≠ 1 ∧ k ^ 3 = 1 := by
  haveI : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE9]
    norm_num
  obtain ⟨k, hk⟩ := exists_ne (1 : E)
  exact ⟨k, k.2, fun h => hk (Subtype.ext h), hE3 k k.2⟩

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem rowLie_SL3 (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n)
    (eS : S ≃* projSL 3 (GaloisField 2 n)) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {C K : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hKC : K ≤ C) [Group.IsPerfect K]
    (hsub : (K.subgroupOf C).IsSubnormal)
    (htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.J2)) :
    CFSG.pCore 2 C = ⊥ ∧ ∃ m : ℕ, 1 ≤ m ∧ n = 3 * m ∧ IsoLThreePi K 2 m ∧ IsoLThreePi S 2 n ∧
      ∃ τ : S ≃* projectiveSL 3 (GaloisField 2 n),
        (stdPinnedPSL 3 (GaloisField 2 n)).IsField (MulAut.congr τ σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 htype
  have hfix := fix_of_le hC hKC
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have h3 : ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEK hk₀E, hk₀1, hk₀3⟩
  have hnt : K ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hEK hk₀E))
  rcases two_pow_mod_three n with hmod | hmod
  swap
  ·
    exact (false_of_e9_of_isCyclic_sylow
      (isCyclic_sylow_three_of_mulEquiv_projSL (by rw [hFcard]; exact hmod) eS) hE3 hE9).elim
  obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 F
  set τ : S ≃* projectiveSL 3 F := eS.trans φ₀ with hτ
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hD : α ∈ linearAutGroup 3 F
  ·
    exfalso
    obtain ⟨p, f, hPi, hq⟩ := RonanK432.L3Outer.exists_piField_true (K := F) (by rw [hFcard]; exact hmod)
    refine false_of_fix_e9_of_mulEquiv τ (linearAutGroup 3 F) ?_ ?_ ?_ hD hσ3 hσ1 hEK hEc hE3
      hE9 hfix hEZ
    · intro B hB h3 hc
      refine card_le_nine_of_le_range hPi hq (conjAut 3 F) (MonoidHom.id (GL (Fin 3) F))
        (fun g => RonanK432.L3Outer.conjAut_eq_one_iff g) (fun g => mem_glPi_true _ g) ?_ h3 hc
      rw [← linearAutGroup_eq_range]
      exact hB
    · intro x
      obtain ⟨g, rfl⟩ := proj_surjective 3 F x
      rw [conj_proj_eq_conjAut]
      exact conjAut_mem_linearAutGroup _
    · intro s hs'
      have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := F) (n := 3)
        le_rfl
      have hsZ : s ∈ Subgroup.center (projectiveSL 3 F) :=
        Subgroup.mem_center_iff.mpr fun t => (hs' t).symm
      rw [hZ] at hsZ
      exact (Subgroup.mem_bot).mp hsZ
  ·
    obtain ⟨φ, hφ, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
    have hστ' : MulAut.congr (τ.trans (conjAut 3 F H)⁻¹) σ = fieldAut 3 F φ := by
      rw [congr_trans_mulAut, ← hα, hαH]
      group
    obtain ⟨⟨eK⟩, hO2⟩ := fieldCase_linear (τ.trans (conjAut 3 F H)⁻¹) hστ' hC hKC hnt hsub h3
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hFcard hφ
    obtain ⟨m, rfl⟩ := h3n
    have hm : 1 ≤ m := by omega
    have hcube : Nat.card F = (2 ^ m) ^ 3 := by rw [hFcard, ← pow_mul, mul_comm]
    have hK₀ : Nat.card (fixedField φ) = 2 ^ m := card_fixedField_of_orderOf_eq_three hφ hcube
    have hmod' : 2 ^ m % 3 = 1 := by
      rw [← pow_three_mod_three, ← pow_mul, mul_comm, hmod]
    have := Fintype.ofFinite (fixedField φ)
    have ψ : fixedField φ ≃+* GaloisField 2 m :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 m (by omega) hK₀
    obtain ⟨φ₁⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 m)
    refine ⟨hO2, m, hm, rfl, Or.inl ⟨hmod', ⟨(eK.trans
      (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr ψ)).trans φ₁.symm⟩⟩,
      Or.inl ⟨hmod, ⟨eS⟩⟩, τ, isField_of_pow_three_eq_one le_rfl hα3 hD⟩

theorem rowLie_SU3 (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n)
    (eS : S ≃* projSU 3 2 n) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {C K : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hKC : K ≤ C) [Group.IsPerfect K]
    (hsub : (K.subgroupOf C).IsSubnormal)
    (htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.J2)) :
    CFSG.pCore 2 C = ⊥ ∧ ∃ m : ℕ, 1 ≤ m ∧ n = 3 * m ∧ IsoLThreePi K 2 m ∧ IsoLThreePi S 2 n ∧
      ∃ (h : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) (τ : S ≃* unitaryPSU h 3),
        (stdPinnedPSU3 h).IsField (MulAut.congr τ σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 (2 * n) with hF
  have hFcard : Nat.card F = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have h : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn, hFcard⟩
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 htype
  have hfix := fix_of_le hC hKC
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have h3 : ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEK hk₀E, hk₀1, hk₀3⟩
  have hnt : K ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hEK hk₀E))
  rcases two_pow_mod_three n with hmod | hmod
  ·
    exact (false_of_e9_of_isCyclic_sylow
      (isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hmod eS) hE3 hE9).elim
  have hq2 : 2 < 2 ^ n := by
    by_contra hle
    have hn1 : n = 1 := by
      by_contra hne
      have h2 : 2 ≤ n := by omega
      have h4 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
      norm_num at h4
      omega
    subst hn1
    have hsolv : Group.IsSolvable (projSU 3 2 1) := CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom) eS.symm.surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr ‹_› a b)
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  set τ : S ≃* unitaryPSU h 3 := eS.trans φ₀.symm with hτ
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hD : α ∈ (psuConj h).range
  ·
    exfalso
    have hPi : Sec4.PiField false 2 n F :=
      ⟨Nat.prime_two, hn, by rw [hFcard, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
    refine false_of_fix_e9_of_mulEquiv τ (psuConj h).range ?_ ?_ ?_ hD hσ3 hσ1 hEK hEc hE3
      hE9 hfix hEZ
    · intro B hB h3 hc
      exact card_le_nine_of_le_range hPi (show Sec4.ModThree false (2 ^ n) from hmod)
        (psuConj h) (unitaryIsom3 h).subtype (fun g => RonanK432.L3Outer.psuConj_eq_one_iff g)
        (fun g => (Sec4.mem_glPi_false h).mpr (mem_unitaryIsom3.mp g.2)) hB h3 hc
    · intro x
      obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
      exact ⟨_, (conj_mk_eq_psuConj g).symm⟩
    · intro s hs'
      have hZ := center_unitaryPSU_three_eq_bot h hq2
      have hsZ : s ∈ Subgroup.center (unitaryPSU h 3) :=
        Subgroup.mem_center_iff.mpr fun t => (hs' t).symm
      rw [hZ] at hsZ
      exact (Subgroup.mem_bot).mp hsZ
  ·
    obtain ⟨φ, hφ, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
    have hστ' : MulAut.congr (τ.trans (psuConj h H)⁻¹) σ = psuField h φ := by
      rw [congr_trans_mulAut, ← hα, hαH]
      group
    obtain ⟨m, hnm, hm, hK₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hφ
    have h₀ : UnitaryFieldData 2 m (fixedField φ) := ⟨Nat.prime_two, hm, hK₀⟩
    have hbar := bar_coe_fixedField h hnm h₀
    have hmod' : 2 ^ m % 3 = 2 := by
      rw [← pow_three_mod_three, ← pow_mul, mul_comm, ← hnm, hmod]
    by_cases hm1 : 2 ^ m = 2
    · exact (false_of_uniFix_two h₀ hbar (τ.trans (psuConj h H)⁻¹) hστ' hm1 hC hKC hnt).elim
    have hq₀ : 2 < 2 ^ m := by
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
      omega
    obtain ⟨⟨eK⟩, hO2⟩ := fieldCase_unitary h₀ hbar (τ.trans (psuConj h H)⁻¹) hστ' hq₀ hC hKC
      hnt hsub h3
    have hG₀ : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) := GaloisField.card 2 (2 * m) (by omega)
    have h₁ : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) := ⟨Nat.prime_two, hm, hG₀⟩
    have := Fintype.ofFinite (fixedField φ)
    have ψ : fixedField φ ≃+* GaloisField 2 (2 * m) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 (2 * m) (by omega) hK₀
    obtain ⟨φ₁⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₁
    refine ⟨hO2, m, hm, hnm, Or.inr ⟨hmod', ⟨(eK.trans
      (CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.psuEquiv ψ h₁ h₀ hq₀)).trans
        φ₁⟩⟩, Or.inr ⟨hmod, ⟨eS⟩⟩, h, τ, isField_psu3_of_pow_three_eq_one hq2 hα3 hD⟩

end Rows

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

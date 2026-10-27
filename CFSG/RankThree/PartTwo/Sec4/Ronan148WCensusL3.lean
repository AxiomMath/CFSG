module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieL3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeQuasisimpleSL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverPSL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverPSU

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148W

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.GH74.GLS.IVK (fixedField)

section Cover

variable {X : Type} [Group X] [Finite X]

theorem two_pow_mod_three_cases (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem exists_ne_one_pow_three_of_card {E : Subgroup X} (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ k ∈ E, k ≠ 1 ∧ k ^ 3 = 1 := by
  haveI : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE9]
    norm_num
  obtain ⟨k, hk⟩ := exists_ne (1 : E)
  exact ⟨k, k.2, fun h => hk (Subtype.ext h), hE3 k k.2⟩

theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_e9_of_cover {Y : Subgroup X} {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) :
    ∃ E : Subgroup X, E ≤ Y ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧
      Nat.card E = 9 ∧ (∀ z ∈ E, (∀ k ∈ Y, z * k = k * z) → z = 1) ∧
      ∀ (z : Y), (z : X) ∈ E → π z = 1 → z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3 := two_pow_mod_three_of_odd hmo
  have hq2 : 2 < 2 ^ m := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  obtain ⟨-, hZU⟩ := Sec13.isPerfect_center_projSU 2 m (by omega) hq3 hq2
  obtain ⟨E₀, hE₀, h9₀⟩ := Sec15.exists_e9_of_isLThreePi (X := projSU 3 2 m)
    ⟨2, m, ⟨Nat.prime_two⟩, by omega, Or.inr ⟨hq3, ⟨MulEquiv.refl _⟩⟩⟩
  set eq := QuotientGroup.quotientKerEquivOfSurjective π hπ with heq
  set E' : Subgroup (Y ⧸ π.ker) := E₀.map eq.symm.toMonoidHom with hE'
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := hE₀.map _
  have h9' : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective eq.symm.injective, h9₀]
  have hN : ¬ 3 ∣ Nat.card π.ker := fun h3 => by
    have := Nat.Coprime.eq_one_of_dvd hker.symm h3
    omega
  obtain ⟨P, hPmap, hP9, hPN, hP⟩ := exists_e9_lift π.ker hN hE'e h9'
  refine ⟨P.map Y.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val)
  · rintro _ ⟨a, ha, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hP.2 a ha, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hP9]
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have hxc : π x ∈ Subgroup.center (projSU 3 2 m) := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨k, rfl⟩ := hπ u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm k k.2).symm
    rw [hZU, Subgroup.mem_bot] at hxc
    have hx1 : x ∈ P ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hx, hxc⟩
    rw [hPN, Subgroup.mem_bot] at hx1
    simp [hx1]
  · rintro z ⟨x, hx, hxz⟩ hz1
    have hxz' : x = z := Subtype.ext hxz
    subst hxz'
    have hx1 : x ∈ P ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hx, hz1⟩
    rw [hPN, Subgroup.mem_bot] at hx1
    exact hx1

end Cover

section NotInndiag

variable {S : Type} [Group S] [Finite S]

theorem not_mem_linearAutGroup_of_e9 {F : Type} [Field F] [Finite F] (hmod : Nat.card F % 3 = 1)
    (τ : S ≃* projectiveSL 3 F) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {K E : Subgroup S} (hEK : E ≤ K) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : Nat.card E = 9) (hfix : ∀ k ∈ K, σ k = k)
    (hEZ : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) :
    MulAut.congr τ σ ∉ linearAutGroup 3 F := by
  intro hD
  obtain ⟨p, f, hPi, hq⟩ := RonanK432.L3Outer.exists_piField_true (K := F) hmod
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

theorem not_mem_psuConj_range_of_e9 {n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 n F)
    (hmod : 2 ^ n % 3 = 2) (hq2 : 2 < 2 ^ n) (τ : S ≃* unitaryPSU h 3) {σ : MulAut S}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {K E : Subgroup S} (hEK : E ≤ K)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hfix : ∀ k ∈ K, σ k = k) (hEZ : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) :
    MulAut.congr τ σ ∉ (psuConj h).range := by
  intro hD
  have := h.finite
  have hPi : Sec4.PiField false 2 n F :=
    ⟨Nat.prime_two, h.one_le, by rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
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

end NotInndiag

section Simple

variable {X : Type} [Group X] [Finite X]

theorem false_rowU3_L3 {n : ℕ} (hn : 1 ≤ n) (eS : X ≃* projSL 3 (GaloisField 2 n))
    {α : MulAut X} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {Y : Subgroup X} (hYC : Y ≤ Sec4.autFix α)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix α)).IsSubnormal)
    {m : ℕ} (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ, -⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, α k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three_of_card hE3 hE9
  have h3 : ∃ k ∈ Y, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEY hk₀E, hk₀1, hk₀3⟩
  have hnt : Y ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hEY hk₀E))
  rcases two_pow_mod_three_cases n with hmod | hmod
  swap
  · exact false_of_e9_of_isCyclic_sylow
      (isCyclic_sylow_three_of_mulEquiv_projSL (by rw [hFcard]; exact hmod) eS) hE3 hE9
  obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 F
  set τ : X ≃* projectiveSL 3 F := eS.trans φ₀ with hτ
  set α' := MulAut.congr τ α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hD := not_mem_linearAutGroup_of_e9 (by rw [hFcard]; exact hmod) τ hα3 hα1 hEY hEc hE3
    hE9 hfix hEZ
  obtain ⟨φ, hφ, H, hαH⟩ := linear_order_three_field_descent le_rfl α' hα'3 hD
  have hστ' : MulAut.congr (τ.trans (conjAut 3 F H)⁻¹) α = fieldAut 3 F φ := by
    rw [congr_trans_mulAut, ← hα', hαH]
    group
  obtain ⟨⟨eY⟩, -⟩ := fieldCase_linear (τ.trans (conjAut 3 F H)⁻¹) hστ'
    (fun x => Sec4.mem_autFix) hYC hnt hsub h3
  obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hFcard hφ
  obtain ⟨n₀, rfl⟩ := h3n
  have hn₀ : 1 ≤ n₀ := by omega
  have hcube : Nat.card F = (2 ^ n₀) ^ 3 := by rw [hFcard, ← pow_mul, mul_comm]
  have hK₀ : Nat.card (fixedField φ) = 2 ^ n₀ := card_fixedField_of_orderOf_eq_three hφ hcube
  have hmod₀ : 2 ^ n₀ % 3 = 1 := by
    rw [← pow_three_mod_three, ← pow_mul, mul_comm, hmod]
  have := Fintype.ofFinite (fixedField φ)
  have ψ : fixedField φ ≃+* GaloisField 2 n₀ :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 n₀ (by omega) hK₀
  obtain ⟨φ₁⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 n₀)
  set eY' : Y ≃* projSL 3 (GaloisField 2 n₀) :=
    (eY.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr ψ)).trans φ₁.symm with heY'
  have hYs : IsSimpleGroup Y := by
    haveI := CFSG.ComponentClassification.OutcomeLocal.isSimpleGroup_projectiveSL
      (k := fixedField φ) (n := 3) le_rfl
    exact eY.isSimpleGroup
  have hq3 := two_pow_mod_three_of_odd hmo
  have hq2 : 2 < 2 ^ m := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hkbot : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨-, hZU⟩ := Sec13.isPerfect_center_projSU 2 m (by omega) hq3 hq2
      have hnt' : Nontrivial (projSU 3 2 m) := by
        obtain ⟨u, hu⟩ := Sec15.exists_e9_of_isLThreePi (X := projSU 3 2 m)
          ⟨2, m, ⟨Nat.prime_two⟩, by omega, Or.inr ⟨hq3, ⟨MulEquiv.refl _⟩⟩⟩
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        have : Nat.card u ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
        omega
      obtain ⟨u, hu⟩ := exists_ne (1 : projSU 3 2 m)
      obtain ⟨y, rfl⟩ := hπ u
      exact hu ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top y))
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkbot
  set eU : Y ≃* projSU 3 2 m := MulEquiv.ofBijective π ⟨hπinj, hπ⟩ with heU
  have hY₀ : IsoLThreePi Y 2 n₀ := Or.inl ⟨hmod₀, ⟨eY'⟩⟩
  have hYm : IsoLThreePi Y 2 m := Or.inr ⟨hq3, ⟨eU⟩⟩
  obtain ⟨-, rfl⟩ := Sec14.Ronan148A.isoLThreePi_unique hn₀ (by omega) hY₀ hYm
  omega

theorem rowU3_U3 {n : ℕ} (hn : 1 ≤ n) (hq : IsQuasisimple X) (eS : X ≃* projSU 3 2 n)
    {α : MulAut X} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {Y : Subgroup X} (hYC : Y ≤ Sec4.autFix α)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix α)).IsSubnormal)
    {m : ℕ} (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * m) K) (e : X ≃* unitaryPSU h 3),
      (stdPinnedPSU3 h).HasKind (MulAut.congr e α) .field := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 (2 * n) with hF
  have hFcard : Nat.card F = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have h : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn, hFcard⟩
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ, -⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, α k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three_of_card hE3 hE9
  have h3 : ∃ k ∈ Y, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEY hk₀E, hk₀1, hk₀3⟩
  have hnt : Y ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hEY hk₀E))
  rcases two_pow_mod_three_cases n with hmod | hmod
  · exact (false_of_e9_of_isCyclic_sylow
      (isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hmod eS) hE3 hE9).elim
  have hq2 : 2 < 2 ^ n :=
    Sec13.Item138Proof.two_lt_of_mulEquiv hq (Sec13.piField_galoisField_two 2 n hn) hmod
      (eS.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage 2 n)))
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  set τ : X ≃* unitaryPSU h 3 := eS.trans φ₀.symm with hτ
  set α' := MulAut.congr τ α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hD := not_mem_psuConj_range_of_e9 h hmod hq2 τ hα3 hα1 hEY hEc hE3 hE9 hfix hEZ
  obtain ⟨φ, hφ, H, hαH⟩ := unitary_order_three_field_descent hq2 α' hα'3 hD
  have hστ' : MulAut.congr (τ.trans (psuConj h H)⁻¹) α = psuField h φ := by
    rw [congr_trans_mulAut, ← hα', hαH]
    group
  obtain ⟨n₀, hnm, hn₀, hK₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hφ
  have h₀ : UnitaryFieldData 2 n₀ (fixedField φ) := ⟨Nat.prime_two, hn₀, hK₀⟩
  have hbar := bar_coe_fixedField h hnm h₀
  have hmod₀ : 2 ^ n₀ % 3 = 2 := by
    rw [← pow_three_mod_three, ← pow_mul, mul_comm, ← hnm, hmod]
  by_cases hn₁ : 2 ^ n₀ = 2
  · exact (false_of_uniFix_two h₀ hbar (τ.trans (psuConj h H)⁻¹) hστ' hn₁
      (fun x => Sec4.mem_autFix) hYC hnt).elim
  have hq₀ : 2 < 2 ^ n₀ := by
    have : 2 ≤ 2 ^ n₀ := Nat.le_self_pow (by omega) 2
    omega
  obtain ⟨⟨eY⟩, -⟩ := fieldCase_unitary h₀ hbar (τ.trans (psuConj h H)⁻¹) hστ' hq₀
    (fun x => Sec4.mem_autFix) hYC hnt hsub h3
  have hG₀ : Nat.card (GaloisField 2 (2 * n₀)) = 2 ^ (2 * n₀) :=
    GaloisField.card 2 (2 * n₀) (by omega)
  have h₁ : UnitaryFieldData 2 n₀ (GaloisField 2 (2 * n₀)) := ⟨Nat.prime_two, hn₀, hG₀⟩
  have := Fintype.ofFinite (fixedField φ)
  have ψ : fixedField φ ≃+* GaloisField 2 (2 * n₀) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 (2 * n₀) (by omega) hK₀
  obtain ⟨φ₁⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₁
  set eY' : Y ≃* projSU 3 2 n₀ := (eY.trans
    (CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.psuEquiv ψ h₁ h₀ hq₀)).trans φ₁
    with heY'
  have hYs : IsSimpleGroup Y := by
    haveI := CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.isSimpleGroup_unitaryPSU_three
      (h := h₀) hq₀
    exact eY.isSimpleGroup
  have hq3 := two_pow_mod_three_of_odd hmo
  have hq2m : 2 < 2 ^ m := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hkbot : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h' | h'
    · exact h'
    · exfalso
      have hnt' : Nontrivial (projSU 3 2 m) := by
        obtain ⟨u, hu⟩ := Sec15.exists_e9_of_isLThreePi (X := projSU 3 2 m)
          ⟨2, m, ⟨Nat.prime_two⟩, by omega, Or.inr ⟨hq3, ⟨MulEquiv.refl _⟩⟩⟩
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        have : Nat.card u ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
        omega
      obtain ⟨u, hu⟩ := exists_ne (1 : projSU 3 2 m)
      obtain ⟨y, rfl⟩ := hπ u
      exact hu ((MonoidHom.mem_ker).mp (h' ▸ Subgroup.mem_top y))
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkbot
  set eU : Y ≃* projSU 3 2 m := MulEquiv.ofBijective π ⟨hπinj, hπ⟩ with heU
  have hY₀ : IsoLThreePi Y 2 n₀ := Or.inr ⟨hmod₀, ⟨eY'⟩⟩
  have hYm : IsoLThreePi Y 2 m := Or.inr ⟨hq3, ⟨eU⟩⟩
  obtain ⟨-, rfl⟩ := Sec14.Ronan148A.isoLThreePi_unique hn₀ (by omega) hY₀ hYm
  subst hnm
  exact ⟨F, inferInstance, h, τ, isField_psu3_of_pow_three_eq_one hq2 hα'3 hD⟩

end Simple

section Cover3

variable {L : Type} [Group L] [Finite L] {π : Bool} {p f f₀ : ℕ} {F : Type} [Field F]

theorem autFix_eq_of_frob_perfect (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    (hf : f = 3 * f₀) {φ : F ≃+* F} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {g : GL (Fin 3) F} (hg : g ∈ glPi π 3 (p ^ f) F)
    (e : L ≃* slPi π 3 (p ^ f) F) {α : MulAut L} (hα3 : α ^ 3 = 1)
    (hform : ∀ l, (e (α l) : GL (Fin 3) F) = g * frobGL φ (e l) * g⁻¹)
    {K : Subgroup L} (hKfix : K ≤ autFix α) (hKp : Group.IsPerfect K) (hKnt : Nontrivial K)
    (hKsn : (K.subgroupOf (autFix α)).IsSubnormal) : K = autFix α := by
  set σ : GL (Fin 3) F →* GL (Fin 3) F := (MulAut.conj g).toMonoidHom.comp (frobGL φ) with hσdef
  have hσapp : ∀ A, σ A = g * frobGL φ A * g⁻¹ := fun A => rfl
  have hσ : ∀ A : GL (Fin 3) F, (σ A : Matrix (Fin 3) (Fin 3) F) =
      g * (A : Matrix (Fin 3) (Fin 3) F).map (· ^ piCard π (p ^ f₀)) * (g⁻¹ : GL (Fin 3) F) := by
    intro A
    rw [hσapp, Units.val_mul, Units.val_mul, coe_frobGL]
    congr 2
    ext i k
    exact hφ _
  have hσe : ∀ l, σ (e l) = e (α l) := fun l => (hform l).symm
  have hα3' : ∀ l, α (α (α l)) = l := by
    intro l
    have h := congrArg (fun β : MulAut L => β l) hα3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  have hσ3 : ∀ A ∈ slPi π 3 (p ^ f) F, σ (σ (σ A)) = A := by
    intro A hA
    obtain ⟨l, hl⟩ := e.surjective ⟨A, hA⟩
    have hA' : A = (e l : GL (Fin 3) F) := by rw [hl]
    rw [hA', hσe, hσe, hσe, hα3']
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  obtain ⟨S₀, -, hS₀card⟩ := exists_fixedField hK hf hφ3
  have hK₀ : PiField π p f₀ S₀ := ⟨hK.prime, hf₀, hS₀card⟩
  obtain ⟨-, -, ⟨eX⟩⟩ := rank3II_4_10_four hK hq hf hg σ hσ hσ3 S₀ hK₀
  have hmap : (autFix α).map ((slPi π 3 (p ^ f) F).subtype.comp e.toMonoidHom) =
      fixedIn (slPi π 3 (p ^ f) F) σ := by
    ext A
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨(e l).2, ?_⟩
      change σ (e l) = (e l : GL (Fin 3) F)
      have hl' : α l = l := hl
      rw [hσe, hl']
    · rintro ⟨hA, hσA⟩
      change σ A = A at hσA
      obtain ⟨l, hl⟩ := e.surjective ⟨A, hA⟩
      refine ⟨l, ?_, by simp [hl]⟩
      change α l = l
      apply e.injective
      apply Subtype.ext
      rw [← hσe, hl]
      exact hσA
  have hinj : Function.Injective ((slPi π 3 (p ^ f) F).subtype.comp e.toMonoidHom) :=
    (Subgroup.subtype_injective _).comp e.injective
  have eF : autFix α ≃* slPi π 3 (p ^ f₀) S₀ :=
    ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hmap)).trans eX
  by_cases h2 : 2 < p ^ f₀
  · have hq0 : IsQuasisimple (slPi π 3 (p ^ f₀) S₀) :=
      Item462AltProof.KSLThree.isQuasisimple_slPi hK₀ h2
    have hqfix : IsQuasisimple (autFix α) := LocalCores.isQuasisimple_of_mulEquiv eF.symm hq0
    exact Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKfix hqfix hKp hKnt hKsn
  · exfalso
    have hp := hK.prime
    have hq₀2 : p ^ f₀ = 2 := by
      have : p ≤ p ^ f₀ := Nat.le_self_pow (by omega) p
      have := hp.two_le
      omega
    obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq₀2
    subst hf
    cases π
    · have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 S₀ := hK₀.unitary
      have hcard : Nat.card (autFix α) = 216 := by
        rw [Nat.card_congr eF.toEquiv]
        exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      have := Fintype.ofFinite (autFix α)
      have hsolv : Group.IsSolvable (autFix α) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      have hsolK : Group.IsSolvable K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKfix)
          (Subgroup.inclusion_injective hKfix)
      exact Group.IsPerfect.not_isSolvable K hsolK
    · norm_num [ModThree] at hq

theorem autFix_eq_of_frobPow_perfect (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    (hf : f = 3 * f₀) {φ : F ≃+* F} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ρ : F ≃+* F} (hρ : ρ = φ ∨ ρ = φ ^ 2)
    {g : GL (Fin 3) F} (hg : g ∈ glPi π 3 (p ^ f) F) (e : L ≃* slPi π 3 (p ^ f) F)
    {α : MulAut L} (hα3 : α ^ 3 = 1)
    (hform : ∀ l, (e (α l) : GL (Fin 3) F) = g * frobGL ρ (e l) * g⁻¹)
    {K : Subgroup L} (hKfix : K ≤ autFix α) (hKp : Group.IsPerfect K) (hKnt : Nontrivial K)
    (hKsn : (K.subgroupOf (autFix α)).IsSubnormal) : K = autFix α := by
  rcases hρ with rfl | rfl
  · exact autFix_eq_of_frob_perfect hK hq hf hφ hφ3 hg e hα3 hform hKfix hKp hKnt hKsn
  · have hα3' : ∀ l, α (α (α l)) = l := by
      intro l
      have h := congrArg (fun β : MulAut L => β l) hα3
      simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
    have hsq : ∀ l, (α ^ 2) l = α (α l) := fun l => by rw [pow_two, MulAut.mul_apply]
    have hfix2 : autFix (α ^ 2) = autFix α := by
      ext l
      rw [mem_autFix, mem_autFix, hsq]
      constructor
      · intro h
        calc α l = α (α (α l)) := by rw [h]
          _ = l := hα3' l
      · intro h
        rw [h, h]
    have hα23 : (α ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hα3, one_pow]
    have hg₂ : g * frobGL (φ ^ 2) g ∈ glPi π 3 (p ^ f) F :=
      mul_mem hg (frobGL_mem_glPi hK _ hg)
    have hφ4 : ∀ A, frobGL (φ ^ 2) (frobGL (φ ^ 2) A) = frobGL φ A := by
      intro A
      rw [frobGL_pow_two, frobGL_pow_two, frobGL_three hφ3]
    have hform2 : ∀ l, (e ((α ^ 2) l) : GL (Fin 3) F) =
        (g * frobGL (φ ^ 2) g) * frobGL φ (e l) * (g * frobGL (φ ^ 2) g)⁻¹ := by
      intro l
      rw [hsq, hform, hform, map_mul, map_mul, map_inv, hφ4]
      group
    rw [← hfix2] at hKfix hKsn ⊢
    exact autFix_eq_of_frob_perfect hK hq hf hφ hφ3 hg₂ e hα23 hform2 hKfix hKp hKnt hKsn

end Cover3

section CoverRow


variable {X : Type} [Group X] [Finite X]

theorem false_rowU3_SL3 {n : ℕ} (hn : 1 ≤ n) (hq : IsQuasisimple X)
    (hXat : IsSLThreePiAt X (2 ^ n)) {α : MulAut X} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {Y : Subgroup X} (hYC : Y ≤ Sec4.autFix α) [hYp : Group.IsPerfect Y]
    (hsub : (Y.subgroupOf (Sec4.autFix α)).IsSubnormal)
    {m : ℕ} (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect X := hq.1
  have hZ3 : Nat.card (Subgroup.center X) = 3 := card_center_of_isSLThreePiAt_two_pow hn hXat
  have hZodd : Odd (Nat.card (Subgroup.center X)) := by rw [hZ3]; decide
  have hZ : Subgroup.center X ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ, hEπ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hq3 := two_pow_mod_three_of_odd hmo
  have hq2m : 2 < 2 ^ m := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  obtain ⟨-, hZU⟩ := Sec13.isPerfect_center_projSU 2 m (by omega) hq3 hq2m
  have hcen : ∀ (c : Y), (c : X) ∈ Subgroup.center X → π c = 1 := by
    intro c hc
    have h1 : π c ∈ Subgroup.center (projSU 3 2 m) := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨k, rfl⟩ := hπ u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hc (k : X))
    rw [hZU, Subgroup.mem_bot] at h1
    exact h1
  set N := Subgroup.center X with hN
  set σ := centerDescend X α with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hα3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hα1
    refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
    have h2 := congrArg (fun φ : MulAut (X ⧸ N) => φ (s : X ⧸ N)) h1
    simp only [hσdef, centerDescend_mk, MulAut.one_apply] at h2
    exact QuotientGroup.eq.mp h2.symm
  set Kb : Subgroup (X ⧸ N) := Y.map (QuotientGroup.mk' N) with hKb
  set Eb : Subgroup (X ⧸ N) := E.map (QuotientGroup.mk' N) with hEb
  have hfixb : ∀ k ∈ Kb, σ k = k := by
    rintro _ ⟨y, hy, rfl⟩
    change centerDescend X α (y : X ⧸ N) = (y : X ⧸ N)
    rw [centerDescend_mk, Sec4.mem_autFix.mp (hYC hy)]
  have hEbK : Eb ≤ Kb := Subgroup.map_mono hEY
  have hEbc : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hEb3 : ∀ a ∈ Eb, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE3 a ha, map_one]
  have hinjE : ∀ a ∈ E, ∀ b ∈ E, QuotientGroup.mk' N a = QuotientGroup.mk' N b → a = b := by
    intro a ha b hb hab
    have hm : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have hmE : a⁻¹ * b ∈ E := mul_mem (inv_mem ha) hb
    have h1 : π ⟨a⁻¹ * b, hEY hmE⟩ = 1 := hcen ⟨a⁻¹ * b, hEY hmE⟩ hm
    have h2 := hEπ ⟨a⁻¹ * b, hEY hmE⟩ hmE h1
    have h3 : a⁻¹ * b = 1 := congrArg Subtype.val h2
    exact (inv_mul_eq_one.mp h3)
  have hEb9 : Nat.card Eb = 9 := by
    have hinj' : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
      intro a b hab
      exact Subtype.ext (hinjE a a.2 b b.2 hab)
    have hrange : ((QuotientGroup.mk' N).comp E.subtype).range = Eb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm, hE9]
  have hEbZ : ∀ z ∈ Eb, (∀ k ∈ Kb, z * k = k * z) → z = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hcomm
    have hπz : π ⟨z, hEY hz⟩ = 1 := by
      have hc : π ⟨z, hEY hz⟩ ∈ Subgroup.center (projSU 3 2 m) := by
        rw [Subgroup.mem_center_iff]
        intro u
        obtain ⟨k, rfl⟩ := hπ u
        have h1 := hcomm (QuotientGroup.mk' N (k : X)) ⟨k, k.2, rfl⟩
        rw [← map_mul, ← map_mul] at h1
        have h2 : (k : X)⁻¹ * z⁻¹ * ((k : X) * z) ∈ N := by
          have := QuotientGroup.eq.mp h1
          simpa [mul_assoc] using this
        have hk : (k : X)⁻¹ * z⁻¹ * ((k : X) * z) ∈ Y :=
          mul_mem (mul_mem (inv_mem k.2) (inv_mem (hEY hz))) (mul_mem k.2 (hEY hz))
        have h3 := hcen ⟨_, hk⟩ h2
        have h4 : (⟨(k : X)⁻¹ * z⁻¹ * ((k : X) * z), hk⟩ : Y) =
            k⁻¹ * (⟨z, hEY hz⟩ : Y)⁻¹ * (k * ⟨z, hEY hz⟩) := rfl
        rw [h4, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
        have h5 : π k * π ⟨z, hEY hz⟩ = π ⟨z, hEY hz⟩ * π k := by
          have := h3
          calc π k * π ⟨z, hEY hz⟩ = π ⟨z, hEY hz⟩ * π k *
                ((π k)⁻¹ * (π ⟨z, hEY hz⟩)⁻¹ * (π k * π ⟨z, hEY hz⟩)) := by group
            _ = π ⟨z, hEY hz⟩ * π k := by rw [this, mul_one]
        exact h5
      rw [hZU, Subgroup.mem_bot] at hc
      exact hc
    have h1 := hEπ ⟨z, hEY hz⟩ hz hπz
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, map_one]
  have hiso : IsoLThreePi (X ⧸ N) 2 n :=
    Item462AltProof.isoLThreePi_quotient_center_of_isSLThreePiAt hn hXat
  have hYnt : Nontrivial Y := by
    obtain ⟨k₀, hk₀E, hk₀1, -⟩ := exists_ne_one_pow_three_of_card hE3 hE9
    exact ⟨⟨⟨k₀, hEY hk₀E⟩, 1, fun h => hk₀1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨-, hCNF⟩ : Nat.card (Subgroup.center X) = 3 ∧ CoverNormalForm X α := by
    rcases hiso with ⟨hmod, ⟨eS⟩⟩ | ⟨hmod, ⟨eS⟩⟩
    · set F' := GaloisField 2 n
      have hFcard : Nat.card F' = 2 ^ n := GaloisField.card 2 n (by omega)
      obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 F'
      set τ : X ⧸ N ≃* projectiveSL 3 F' := eS.trans φ₀ with hτ
      have hD := not_mem_linearAutGroup_of_e9 (by rw [hFcard]; exact hmod) τ hσ3 hσ1 hEbK hEbc
        hEb3 hEb9 hfixb hEbZ
      have hτ3 : MulAut.congr τ σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
      exact coverNormalForm_of_psl hZodd hZ hα3 τ (isField_of_pow_three_eq_one le_rfl hτ3 hD)
    · have hq2 : 2 < 2 ^ n := by
        by_contra hle
        have hn1 : 2 ^ n = 2 := by
          have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
          omega
        have hn1' : n = 1 := by
          rcases Nat.lt_or_ge n 2 with h | h
          · omega
          · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
            omega
        subst hn1'
        haveI := Sec13.isSolvable_projSU_two
        have hsol : Group.IsSolvable (X ⧸ N) :=
          Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
        have hsolX : Group.IsSolvable X := by
          haveI := hsol
          haveI : Group.IsSolvable N := inferInstance
          exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
            rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
        have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
        exact Group.IsPerfect.not_isSolvable X hsolX
      set F' := GaloisField 2 (2 * n)
      have hF'card : Nat.card F' = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
      have h : UnitaryFieldData 2 n F' := ⟨Nat.prime_two, hn, hF'card⟩
      obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
      set τ : X ⧸ N ≃* unitaryPSU h 3 := eS.trans φ₀.symm with hτ
      have hD := not_mem_psuConj_range_of_e9 h hmod hq2 τ hσ3 hσ1 hEbK hEbc hEb3 hEb9 hfixb
        hEbZ
      have hτ3 : MulAut.congr τ σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
      exact coverNormalForm_of_psu hZodd hZ hα3 h hq2 τ
        (isField_psu3_of_pow_three_eq_one hq2 hτ3 hD)
  obtain ⟨π', p', f', F', _, hK', hq', f₀, hf, ρ, hρ, g, hg, e, hform⟩ := hCNF
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK' hf
  have hYeq : Y = autFix α :=
    autFix_eq_of_frobPow_perfect hK' hq' hf hφ hφ3 (eq_or_eq_sq_of_pow hφ hρ) hg e hα3 hform
      hYC hYp hYnt hsub
  have hZY : N ≤ Y := hYeq ▸ center_le_autFix_of_card_three hZ3 hα3
  obtain ⟨z, hzN, hz1⟩ : ∃ z ∈ N, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hZ ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have hzker : (⟨z, hZY hzN⟩ : Y) ∈ π.ker := hcen _ hzN
  have hzo : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := hZ3 ▸ Subgroup.orderOf_dvd_natCard N hzN
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  have h3 : 3 ∣ Nat.card π.ker := by
    have h1 := Subgroup.orderOf_dvd_natCard π.ker hzker
    rwa [Subgroup.orderOf_mk, hzo] at h1
  have := Nat.Coprime.eq_one_of_dvd hker.symm h3
  omega

theorem rowU3_L3eps (hq : IsQuasisimple X) (_hZ : IsPGroup 3 (Subgroup.center X)) {n : ℕ}
    (hn : 1 ≤ n)
    (hX : IsSLThreeEpsAt X (2 ^ n) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n))
    {α : MulAut X} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {Y : Subgroup X} (hYC : Y ≤ Sec4.autFix α)
    (hYp : Group.IsPerfect Y) (hsub : (Y.subgroupOf (Sec4.autFix α)).IsSubnormal)
    {m : ℕ} (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * m) K) (e : X ≃* unitaryPSU h 3),
      (stdPinnedPSU3 h).HasKind (MulAut.congr e α) .field := by
  haveI := hYp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with hSL | ⟨⟨eS⟩⟩ | ⟨⟨eS⟩⟩
  · by_cases hat : IsSLThreePiAt X (2 ^ n)
    · exact (false_rowU3_SL3 hn hq hat hα3 hα1 hYC hsub hmo hm1 π hπ hker).elim
    · obtain ⟨E, -, -, hE3, hE9, -, -⟩ := exists_e9_of_cover hmo hm1 π hπ hker
      exact (false_of_e9_of_isCyclic_sylow
        (isCyclic_sylow_of_isSLThreeEpsAt (by norm_num) hSL hat) hE3 hE9).elim
  · exact (false_rowU3_L3 hn eS hα3 hα1 hYC hsub hmo hm1 π hπ hker).elim
  · exact rowU3_U3 hn hq eS hα3 hα1 hYC hsub hmo hm1 π hπ hker

end CoverRow

end CFSG.RankThree.PartTwo.Sec4.Ronan148W

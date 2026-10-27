module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies
import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def Census228U3Rank : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 → q % 3 = 1 →
    CFSG.pRank 3 (StatedSU 3 q K ⧸ Subgroup.center (StatedSU 3 q K)) ≤ 1

namespace Item228CensusProof

theorem eq_one_of_finrank_eq_one {K : Type*} [Field K] {S : Type*} [AddCommGroup S] [Module K S]
    (hS : Module.finrank K S = 1) {p : ℕ} (hroot : ∀ t : K, t ^ p = 1 → t = 1)
    {f : S ≃ₗ[K] S} (hf : f ^ p = 1) : f = 1 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hS
  obtain ⟨c, hc⟩ := hv (f v)
  have hfw : ∀ w : S, f w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hfp : ∀ (k : ℕ) (w : S), (f ^ k) w = c ^ k • w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, LinearEquiv.mul_apply, hfw, ih, smul_smul, ← pow_succ]
  have hcp : c ^ p = 1 := by
    have h1 := hfp p v
    rw [hf] at h1
    have h1' : v = c ^ p • v := h1
    have h2 : (c ^ p - 1) • v = 0 := by rw [sub_smul, ← h1', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  have hc1 := hroot c hcp
  ext w
  rw [hfw, hc1, one_smul]
  rfl

theorem card_le_of_faithful_module_noRoots {K : Type*} [Field K] {A : Type*} [CommGroup A]
    [Finite A] (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (MonoidAlgebra K A) V] [IsScalarTower K (MonoidAlgebra K A) V] {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hexp : ∀ a : A, a ^ p = 1)
    (hroot : ∀ t : K, t ^ p = 1 → t = 1) (hdim : Module.finrank K V ≤ 3)
    (hinjective : Function.Injective
      (CFSG.LargeEvenClassification.Helpers.groupAlgebraModuleAction (ScalarField := K)
        (Acting := A) V)) :
    Nat.card A ≤ p := by
  classical
  obtain ⟨r, hr⟩ := Census.exists_card_eq_pow_of_exponent hp hexp
  have : NeZero (Nat.card A : K) := ⟨by rw [hr, Nat.cast_pow]; exact pow_ne_zero r hpK⟩
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    Census.maschke_decomposition (K := K) (A := A) V
  have : ∀ i, IsSimpleModule (MonoidAlgebra K A) (summands i) := hsimple
  let actions := fun i =>
    CFSG.LargeEvenClassification.Helpers.groupAlgebraModuleAction (ScalarField := K)
      (Acting := A) (summands i)
  have : ∀ i, Finite (actions i).range := fun i =>
    Finite.of_surjective (actions i).rangeRestrict (actions i).rangeRestrict_surjective
  have hfin : ∀ i, Module.Finite K (summands i) := fun i =>
    Module.Finite.of_injective (((summands i).subtype).restrictScalars K) Subtype.val_injective
  have hrank : ∀ i, 1 ≤ Module.finrank K (summands i) := by
    intro i
    have : Nontrivial (summands i) := IsSimpleModule.nontrivial (MonoidAlgebra K A) _
    exact Module.finrank_pos
  set T : Finset (Fin count) := Finset.univ.filter fun i => 2 ≤ Module.finrank K (summands i)
    with hTdef
  have hbound : ∀ i, Nat.card (actions i).range ≤ p ^ (if i ∈ T then 1 else 0) := by
    intro i
    by_cases hi : i ∈ T
    · rw [ite_eq_left_iff.mpr (fun h => absurd hi h), pow_one]
      have : IsCyclic (actions i).range :=
        CFSG.LargeEvenClassification.Helpers.simple_groupAlgebra_action_cyclic (summands i)
      exact Nat.le_of_dvd hp.pos
        (CFSG.LargeEvenClassification.Helpers.cyclic_action_card_dvd_exponent (actions i) hexp)
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hi), pow_zero]
      have hd1 : Module.finrank K (summands i) = 1 := by
        have := hrank i
        rw [hTdef, Finset.mem_filter] at hi
        push Not at hi
        exact le_antisymm (by have := hi (Finset.mem_univ i); omega) this
      have htriv : (actions i).range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨a, rfl⟩
        rw [Subgroup.mem_bot]
        exact eq_one_of_finrank_eq_one hd1 hroot (by rw [← map_pow, hexp, map_one])
      rw [htriv, Subgroup.card_bot]
  have hT : T.card ≤ 1 := by
    have h1 : ∑ i ∈ T, Module.finrank K (summands i) ≤ ∑ i, Module.finrank K (summands i) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    have h2 : ∑ i ∈ T, 2 ≤ ∑ i ∈ T, Module.finrank K (summands i) :=
      Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    rw [Finset.sum_const, smul_eq_mul] at h2
    omega
  let embedding := MonoidHom.pi (fun i => (actions i).rangeRestrict)
  have hembedding : Function.Injective embedding := by
    intro first second heq
    apply hinjective
    ext x
    change (MonoidAlgebra.of K A) first • x = (MonoidAlgebra.of K A) second • x
    apply equivalence.injective
    rw [equivalence.map_smul, equivalence.map_smul]
    apply DFinsupp.ext
    intro i
    have hcomponent : actions i first = actions i second :=
      congrArg (fun tuple => (tuple i : summands i ≃ₗ[K] summands i)) heq
    exact congrArg (fun automorphism : summands i ≃ₗ[K] summands i =>
      automorphism (equivalence x i)) hcomponent
  calc Nat.card A ≤ Nat.card (∀ i, (actions i).range) :=
        Nat.card_le_card_of_injective embedding hembedding
    _ = ∏ i, Nat.card (actions i).range := Nat.card_pi
    _ ≤ ∏ i, p ^ (if i ∈ T then 1 else 0) := Finset.prod_le_prod fun i _ => hbound i
    _ = p ^ T.card := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hT
    _ = p := pow_one p

theorem card_le_three_of_isElemAbelian_GL3 {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (hroot : ∀ t : K, t ^ 3 = 1 → t = 1) {E : Subgroup (GL (Fin 3) K)} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.1.is_comm.comm }
  let ρ : E →* ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp E.subtype)
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)).injective.comp
      (Matrix.GeneralLinearGroup.toLin.injective.comp E.subtype_injective)
  have hexp : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (hE.2 a a.2)
  let representation := CFSG.LargeEvenClassification.Helpers.linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  have hmoduleInjective : Function.Injective
      (CFSG.LargeEvenClassification.Helpers.groupAlgebraModuleAction (ScalarField := K)
        (Acting := E) representation.asModule) := by
    intro first second heq
    apply hρ
    refine LinearEquiv.ext fun x => ?_
    have hfixed := congrArg (fun automorphism : representation.asModule ≃ₗ[K]
        representation.asModule => representation.asModuleEquiv
          (automorphism (representation.asModuleEquiv.symm x))) heq
    change representation.asModuleEquiv ((MonoidAlgebra.of K E) first •
        representation.asModuleEquiv.symm x) =
      representation.asModuleEquiv ((MonoidAlgebra.of K E) second •
        representation.asModuleEquiv.symm x) at hfixed
    rw [representation.asModuleEquiv_map_smul, representation.asModuleEquiv_map_smul,
      representation.asAlgebraHom_of, representation.asAlgebraHom_of,
      representation.asModuleEquiv.apply_symm_apply] at hfixed
    exact hfixed
  have hdim : Module.finrank K representation.asModule ≤ 3 := by
    rw [representation.asModuleEquiv.finrank_eq, Module.finrank_fin_fun]
  exact card_le_of_faithful_module_noRoots representation.asModule Nat.prime_three
    (by exact_mod_cast h3) hexp hroot hdim hmoduleInjective

theorem card_le_three_of_isElemAbelian_SL3 {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 2) {E : Subgroup (GL (Fin 3) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have h3' : ¬ 3 ∣ Nat.card K - 1 := by
    have : 2 ≤ Nat.card K := by omega
    omega
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have : Fintype K := Fintype.ofFinite K
    have hc := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, ← Nat.div_add_mod (Nat.card K) 3, hq] at hc
    push_cast at hc
    rw [h, zero_mul, zero_add] at hc
    have h1 : (1 : K) = 0 := by linear_combination h - hc
    exact one_ne_zero h1
  exact card_le_three_of_isElemAbelian_GL3 h3
    (fun t ht => Sec4.eq_one_of_pow_three_eq_one h3' ht) hE

theorem pRank_three_statedSL_le_one {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2) :
    CFSG.pRank 3 (StatedSL 3 K) ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hE : CFSG.Open.IsElemAbelian 3 (B.map (StatedSL 3 K).subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : GL (Fin 3) K) * y = y * x
      rw [← hxe, ← hye, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨x', hx'⟩
        ⟨y', hy'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
      have h' : x ^ 3 = 1 := by simpa using congrArg Subtype.val h
      rw [← map_pow, h', map_one]
  have h3 := card_le_three_of_isElemAbelian_SL3 hq hE
  rw [Subgroup.card_map_of_injective (StatedSL 3 K).subtype_injective, hr] at h3
  by_contra hr1
  have : 3 ^ 2 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem center_statedSL_eq_bot {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2) :
    Subgroup.center (StatedSL 3 K) = ⊥ := by
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by
    have : 2 ≤ Nat.card K := by omega
    omega
  have hZ := Sec4.center_specialLinearGroup_eq_bot (n := 3) (K := K)
    fun r hr => Sec4.eq_one_of_pow_three_eq_one h3 hr
  rw [← Sec4.map_center_mulEquiv (Sec4.statedSLEquiv 3 K).symm, hZ, Subgroup.map_bot]

theorem pRank_quot_center_le_of_mulEquiv {Y S : Type} [Group Y] [Group S] [Finite Y] [Finite S]
    (e : Y ≃* S) (h : CFSG.pRank 3 (S ⧸ Subgroup.center S) ≤ 1) :
    CFSG.pRank 3 (Y ⧸ Subgroup.center Y) ≤ 1 :=
  (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num)
    (Sec4.quotientCenterCongr e).toMonoidHom (Sec4.quotientCenterCongr e).injective).trans h

theorem pRank_quot_center_le_of_center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hZ : Subgroup.center Y = ⊥) {r : ℕ} (h : CFSG.pRank 3 Y ≤ r) :
    CFSG.pRank 3 (Y ⧸ Subgroup.center Y) ≤ r :=
  (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num)
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toMonoidHom
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).injective).trans h

theorem eq_one_of_scalar_mem_statedSU {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ p ^ e + 1) {l : (GaloisField p (2 * e))ˣ}
    (hl : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈ StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :
    l = 1 := by
  have hU := Sec4.unitaryFieldData_galoisField p e he
  have hmem := (mem_unitarySU_iff hU).mp hl
  obtain ⟨hdet, hunit⟩ := hmem
  have hl3 : (l : GaloisField p (2 * e)) ^ 3 = 1 := by
    have : (Matrix.scalar (Fin 3) (l : GaloisField p (2 * e))).det = 1 := by simpa using hdet
    simpa [Matrix.det_smul] using this
  have hlq : (l : GaloisField p (2 * e)) ^ (p ^ e + 1) = 1 := by
    have h00 := congrFun (congrFun hunit 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
    rw [pow_succ]
    exact h00
  have hmod : (p ^ e + 1) % 3 = 1 ∨ (p ^ e + 1) % 3 = 2 := by omega
  apply Units.ext
  rw [Units.val_one]
  have hpow : ∀ k : ℕ, (l : GaloisField p (2 * e)) ^ k = (l : GaloisField p (2 * e)) ^ (k % 3) :=
    fun k => by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hl3, one_pow, one_mul]
  rw [hpow] at hlq
  rcases hmod with h | h
  · rw [h, pow_one] at hlq
    exact hlq
  · rw [h] at hlq
    have h32 : (l : GaloisField p (2 * e)) ^ 3 = (l : GaloisField p (2 * e)) ^ 2 * l := by ring
    rw [hl3, hlq, one_mul] at h32
    exact h32.symm

noncomputable def statedSUEquivProjSU {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ p ^ e + 1) :
    StatedSU 3 (p ^ e) (GaloisField p (2 * e)) ≃* projSU 3 p e :=
  (MonoidHom.ofInjective (f := (Matrix.ProjGenLinGroup.mk :
      GL (Fin 3) (GaloisField p (2 * e)) →* Matrix.ProjGenLinGroup (Fin 3)
        (GaloisField p (2 * e))).comp (StatedSU 3 (p ^ e) (GaloisField p (2 * e))).subtype) (by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hc : (A : GL (Fin 3) (GaloisField p (2 * e))) ∈
        Subgroup.center (GL (Fin 3) (GaloisField p (2 * e))) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hA
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hlmem : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈
        StatedSU 3 (p ^ e) (GaloisField p (2 * e)) := hl ▸ A.2
    have hl1 := eq_one_of_scalar_mem_statedSU he h3 hlmem
    apply Subtype.ext
    rw [← hl, hl1, map_one]
    rfl)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 p e))

theorem pow_mod_three_ne_zero {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : p ^ e % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  exact hp3 this.symm

theorem pRank_le_one_of_L3 (hU : Census228U3Rank) {Y : Type} [Group Y] [Finite Y] {p e : ℕ}
    [hp : Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e) (hT : ¬ IsL3Type228 Y)
    (h : Sec4.IsSLThreeEpsAt Y (p ^ e) ∨ Nonempty (Y ≃* projSL 3 (GaloisField p e)) ∨
      Nonempty (Y ≃* projSU 3 p e)) :
    CFSG.pRank 3 (Y ⧸ Subgroup.center Y) ≤ 1 := by
  have hq0 := pow_mod_three_ne_zero (e := e) hp.out hp3
  have hq2 : 2 ≤ p ^ e := (Nat.le_self_pow (by omega) p).trans' hp.out.two_le
  have hSL : ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ e →
      Nonempty (Y ≃* StatedSL 3 K) → CFSG.pRank 3 (Y ⧸ Subgroup.center Y) ≤ 1 := by
    intro K _ _ hK ⟨eY⟩
    by_cases h1 : 3 ∣ Nat.card K - 1
    · exact absurd (Or.inl ⟨K, inferInstance, inferInstance, h1,
        Or.inr ⟨eY.trans (Sec4.statedSLEquiv 3 K)⟩⟩) hT
    · have hq : Nat.card K % 3 = 2 := by
        rw [hK] at h1 ⊢
        omega
      exact pRank_quot_center_le_of_mulEquiv eY
        (pRank_quot_center_le_of_center_eq_bot (center_statedSL_eq_bot hq)
          (pRank_three_statedSL_le_one hq))
  have hSU : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ e) ^ 2 →
      Nonempty (Y ≃* StatedSU 3 (p ^ e) K) → CFSG.pRank 3 (Y ⧸ Subgroup.center Y) ≤ 1 := by
    intro K _ _ hK ⟨eY⟩
    by_cases h1 : 3 ∣ p ^ e + 1
    · have hUK : UnitaryFieldData p e K := ⟨hp.out, he, by rw [hK, ← pow_mul, mul_comm]⟩
      exact absurd (Or.inr ⟨p, e, K, inferInstance, hUK, h1, Or.inr ⟨eY⟩⟩) hT
    · have hq : p ^ e % 3 = 1 := by omega
      exact pRank_quot_center_le_of_mulEquiv eY (hU (p ^ e) K hK hq)
  rcases h with ⟨K, _, _, ⟨hK, hY⟩ | ⟨hK, hY⟩⟩ | hL | hU'
  · exact hSL K hK hY
  · exact hSU K hK hY
  · obtain ⟨eY⟩ := hL
    have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    by_cases h1 : 3 ∣ p ^ e - 1
    · exact absurd (Or.inl ⟨GaloisField p e, inferInstance, inferInstance, hK ▸ h1,
        Or.inl ⟨eY.trans (Sec4.projSLEquivProjectiveSL 3 _)⟩⟩) hT
    · obtain ⟨e₂⟩ := Sec4.nonempty_statedSL_mulEquiv_projSL (K := GaloisField p e) he hK h1
      exact hSL (GaloisField p e) hK ⟨eY.trans e₂.symm⟩
  · obtain ⟨eY⟩ := hU'
    by_cases h1 : 3 ∣ p ^ e + 1
    · exact absurd (Or.inr ⟨p, e, GaloisField p (2 * e), inferInstance,
        Sec4.unitaryFieldData_galoisField p e he, h1,
        Or.inl ⟨eY.trans (Sec4.projSUEquivUnitaryPSU p e _)⟩⟩) hT
    · have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
        rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
      exact hSU (GaloisField p (2 * e)) hK ⟨eY.trans (statedSUEquivProjSU he h1).symm⟩

end Item228CensusProof

open Item228CensusProof

theorem census228L3Rest_of (hU : Census228U3Rank) : Census228L3Rest := by
  intro Y _ _ hT h
  rcases h with ⟨p, e, hpf, hp3, he1, -, h⟩ | ⟨n, hn, h⟩
  · exact pRank_le_one_of_L3 hU (by omega) he1 hT h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine pRank_le_one_of_L3 (p := 2) (e := n) hU (by norm_num) hn hT ?_
    rcases h with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
    · exact Or.inl h3

end CFSG.RankThree.PartTwo.Sec21

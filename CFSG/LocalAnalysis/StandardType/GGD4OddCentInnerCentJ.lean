module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerUnitaryOm8
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaNorm
public import CFSG.GH74.GLS.LU.Local.L3InvUni
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.LU.Local.L3Facts
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (sc scal mem_sc_iff scal_mem_sc
  coe_scal sc_mem_center scal_pow scal_one)

namespace D4Inner

section Abstract

variable {G R U : Type*} [Group G] [Group R] [Group U] {C : Subgroup G}

theorem natCard_eq_mul_of_mulEquiv (Ψ : ↥C ≃* R × U) {S : Set G} (hSC : S ⊆ C) {P : R → Prop}
    {P' : U → Prop} (hS : ∀ y : C, (y : G) ∈ S ↔ P (Ψ y).1 ∧ P' (Ψ y).2) :
    Nat.card S = Nat.card {r // P r} * Nat.card {u // P' u} := by
  have e1 : S ≃ {y : C // P (Ψ y).1 ∧ P' (Ψ y).2} :=
    { toFun := fun z => ⟨⟨z.1, hSC z.2⟩, (hS _).mp z.2⟩
      invFun := fun y => ⟨y.1.1, (hS y.1).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {y : C // P (Ψ y).1 ∧ P' (Ψ y).2} ≃ {p : R × U // P p.1 ∧ P' p.2} :=
    Ψ.toEquiv.subtypeEquiv fun _ => Iff.rfl
  rw [Nat.card_congr (e1.trans (e2.trans Equiv.subtypeProdEquivProd)), Nat.card_prod]

theorem mem_centralizer_iff_of_mulEquiv (Ψ : ↥C ≃* R × U) {J : Set G} (hJC : J ⊆ C)
    {T : U → Prop} (hJ : ∀ y : C, (y : G) ∈ J ↔ (Ψ y).1 = 1 ∧ T (Ψ y).2) (y : C) :
    (y : G) ∈ Subgroup.centralizer J ↔ ∀ u : U, T u → u * (Ψ y).2 = (Ψ y).2 * u := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    set j : C := Ψ.symm (1, u) with hj
    have hΨj : Ψ j = (1, u) := by rw [hj, MulEquiv.apply_symm_apply]
    have hjJ : (j : G) ∈ J := (hJ j).mpr (by rw [hΨj]; exact ⟨rfl, hu⟩)
    have h1 : j * y = y * j := Subtype.ext (h j hjJ)
    have h2 := congrArg (fun z => (Ψ z).2) h1
    simp only [map_mul, Prod.snd_mul, hΨj] at h2
    exact h2
  · intro h j hj
    obtain ⟨h1, h2⟩ := (hJ ⟨j, hJC hj⟩).mp hj
    have : (⟨j, hJC hj⟩ : C) * y = y * ⟨j, hJC hj⟩ := by
      apply Ψ.injective
      rw [map_mul, map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, Prod.fst_mul, h1, one_mul, mul_one]
      · rw [Prod.snd_mul, Prod.snd_mul]
        exact h _ h2
    exact congrArg Subtype.val this

end Abstract

section Scalars

variable {n : ℕ} {E : Type} [Field E] (hU : UnitaryFieldData 2 n E)

omit [Field E] in
theorem scal_injective {E : Type} [Field E] : Function.Injective (scal : Eˣ → GL (Fin 3) E) := by
  intro c c' h
  have := congrArg (fun g : GL (Fin 3) E => (g : Matrix (Fin 3) (Fin 3) E) 0 0) h
  simp only [coe_scal, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem scal_mem_unitaryIsom3_iff (c : Eˣ) :
    scal c ∈ unitaryIsom3 hU ↔ (c : E) ^ (2 ^ n + 1) = 1 := by
  rw [mem_unitaryIsom3, coe_scal, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_injective.eq_iff, funext_iff]
  simp only [UnitaryFieldData.bar_apply, pow_succ]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem card_scal_mem_unitaryIsom3 [Finite E] (hq : 2 ≤ 2 ^ n) (hE : Nat.card E = (2 ^ n) ^ 2) :
    Nat.card {u : unitaryIsom3 hU // (u : GL (Fin 3) E) ∈ sc E} = 2 ^ n + 1 := by
  have hpow : ∀ c : rootsOfUnity (2 ^ n + 1) E, ((c : Eˣ) : E) ^ (2 ^ n + 1) = 1 := fun c => by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp c.2, Units.val_one]
  refine (Nat.card_eq_of_bijective (fun c => ⟨⟨scal (c : Eˣ),
    (scal_mem_unitaryIsom3_iff hU _).mpr (hpow c)⟩, scal_mem_sc _⟩)
      ⟨fun c c' h => ?_, ?_⟩).symm.trans
    (CFSG.GH74.GLS.LU.Local.L3InvUni.card_rootsOfUnity_succ hq hE)
  · exact Subtype.ext (scal_injective (congrArg (fun u => ((u.1 : unitaryIsom3 hU) :
      GL (Fin 3) E)) h))
  · rintro ⟨⟨g, hgU⟩, hgsc⟩
    obtain ⟨c, rfl⟩ := mem_sc_iff.mp hgsc
    have hc := (scal_mem_unitaryIsom3_iff hU c).mp hgU
    refine ⟨⟨c, (mem_rootsOfUnity _ _).mpr (Units.ext (by rw [Units.val_pow_eq_pow_val, hc,
      Units.val_one]))⟩, rfl⟩

theorem card_scal_mem_unitaryIsom3_pow_three (h3 : 3 ∣ 2 ^ n + 1) {ω : Eˣ}
    (hω : IsPrimitiveRoot (ω : E) 3) :
    Nat.card {u : unitaryIsom3 hU // (u : GL (Fin 3) E) ∈ sc E ∧ u ^ 3 = 1} = 3 := by
  obtain ⟨k, hk⟩ := h3
  have hpow : ∀ c : rootsOfUnity 3 E, ((c : Eˣ) : E) ^ (2 ^ n + 1) = 1 := fun c => by
    rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp c.2, Units.val_one,
      one_pow]
  have hpow3 : ∀ c : rootsOfUnity 3 E, (⟨scal (c : Eˣ), (scal_mem_unitaryIsom3_iff hU _).mpr
      (hpow c)⟩ : unitaryIsom3 hU) ^ 3 = 1 := fun c => Subtype.ext (by
    rw [SubgroupClass.coe_pow, ← scal_pow, (mem_rootsOfUnity _ _).mp c.2, scal_one]
    rfl)
  refine (Nat.card_eq_of_bijective (fun c => ⟨⟨scal (c : Eˣ),
    (scal_mem_unitaryIsom3_iff hU _).mpr (hpow c)⟩, scal_mem_sc _, hpow3 c⟩)
    ⟨fun c c' h => ?_, ?_⟩).symm.trans
    (IsPrimitiveRoot.coe_units_iff.mp hω).card_rootsOfUnity'
  · exact Subtype.ext (scal_injective (congrArg (fun u => ((u.1 : unitaryIsom3 hU) :
      GL (Fin 3) E)) h))
  · rintro ⟨⟨g, hgU⟩, hgsc, hg3⟩
    obtain ⟨c, rfl⟩ := mem_sc_iff.mp hgsc
    have hc3 : c ^ 3 = 1 := by
      apply scal_injective
      rw [scal_pow, scal_one]
      exact congrArg Subtype.val hg3
    exact ⟨⟨c, (mem_rootsOfUnity _ _).mpr hc3⟩, rfl⟩

theorem mem_sc_of_commute_det_one (hq : 2 < 2 ^ n) {M : GL (Fin 3) E}
    (hM : ∀ u : unitaryIsom3 hU, ((u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1 →
      (u : GL (Fin 3) E) * M = M * u) : M ∈ sc E := by
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_scalar_of_commute_unitarySU hU
    hq (S := (M : Matrix (Fin 3) (Fin 3) E)) fun g hg => by
      obtain ⟨hdet, hunit⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU).mp hg
      have h1 := congrArg Units.val (hM ⟨g, mem_unitaryIsom3.mpr hunit⟩ hdet)
      rw [Units.val_mul, Units.val_mul] at h1
      exact h1.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact M.ne_zero hc
  refine mem_sc_iff.mpr ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [hc, coe_scal, Units.val_mk0, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Scalars

section CentJ

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem centDer_le_centralizer (s : Om8 K) :
    centDer s ≤ Subgroup.centralizer ({s} : Set (Om8 K)) :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem centralizer_centDer_le_centralizer {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    Subgroup.centralizer (centDer s : Set (Om8 K)) ≤ Subgroup.centralizer ({s} : Set (Om8 K)) :=
  fun _ hy => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hy s (mem_centDer_self hK hn hn3 hs3 hd)).symm

omit [Finite K] [CharP K 2] in
theorem mem_centralizer_centDer_iff_of_model {n : ℕ} (hn3 : 3 ≤ n) {s : Om8 K} {E : Type}
    [Field E] {hU : UnitaryFieldData 2 n E} {R : Type} [Group R]
    (Ψ : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) ≃* R × ↥(unitaryIsom3 hU))
    (hJ : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))), (y : Om8 K) ∈ centDer s ↔
      (Ψ y).1 = 1 ∧ (((Ψ y).2 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1)
    (y : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) :
    (y : Om8 K) ∈ Subgroup.centralizer (centDer s : Set (Om8 K)) ↔
      ((Ψ y).2 : GL (Fin 3) E) ∈ sc E := by
  have hq : 2 < 2 ^ n := by
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  rw [mem_centralizer_iff_of_mulEquiv Ψ (J := (centDer s : Set (Om8 K)))
    (T := fun u => (((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1)
    (fun _ hz => centDer_le_centralizer s hz) (fun z => by rw [SetLike.mem_coe]; exact hJ z) y]
  constructor
  · intro h
    exact mem_sc_of_commute_det_one hU hq fun u hu => congrArg Subtype.val (h u hu)
  · intro h u _
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp (sc_mem_center h) _)

theorem centralizer_centDer_facts {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    (∀ x ∈ Subgroup.centralizer (centDer s : Set (Om8 K)),
      ∀ y ∈ Subgroup.centralizer (centDer s : Set (Om8 K)), x * y = y * x) ∧
    Nat.card (Subgroup.centralizer (centDer s : Set (Om8 K))) = (2 ^ n + 1) ^ 2 ∧
    Nat.card {x : Om8 K // x ∈ Subgroup.centralizer (centDer s : Set (Om8 K)) ∧ x ^ 3 = 1} =
      3 ^ 2 := by
  obtain ⟨E, _, hU, R, _, Ψ, ω, hRc, hRcard, hR3, hω, hJ, -, -⟩ :=
    exists_d2Model hK hn hn3 hs3 hd
  have := hU.finite
  have hle := centralizer_centDer_le_centralizer hK hn hn3 hs3 hd
  have hchar := mem_centralizer_centDer_iff_of_model hn3 Ψ hJ
  have h3 : 3 ∣ 2 ^ n + 1 := hK ▸ three_dvd_card_add_one hK hn
  have hE : Nat.card E = (2 ^ n) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  refine ⟨fun a ha b hb => ?_, ?_, ?_⟩
  · have hsa := (hchar ⟨a, hle ha⟩).mp ha
    have : (⟨a, hle ha⟩ : ↥(Subgroup.centralizer ({s} : Set (Om8 K)))) * ⟨b, hle hb⟩ =
        ⟨b, hle hb⟩ * ⟨a, hle ha⟩ := by
      apply Ψ.injective
      rw [map_mul, map_mul]
      refine Prod.ext (hRc _ _) (Subtype.ext ?_)
      rw [Prod.snd_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact (Subgroup.mem_center_iff.mp (sc_mem_center hsa) _).symm
    exact congrArg Subtype.val this
  · have hc := natCard_eq_mul_of_mulEquiv Ψ (S := (Subgroup.centralizer (centDer s : Set (Om8 K)) :
      Set (Om8 K))) hle (P := fun _ => True)
      (P' := fun u => ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) ∈ sc E)
      fun y => by rw [SetLike.mem_coe, hchar y, true_and]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), hRcard,
      card_scal_mem_unitaryIsom3 hU (by have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega) hE] at hc
    rw [show Nat.card ↥(Subgroup.centralizer (centDer s : Set (Om8 K))) =
      Nat.card ((Subgroup.centralizer (centDer s : Set (Om8 K)) : Set (Om8 K))) from rfl, hc, sq]
  · have hc := natCard_eq_mul_of_mulEquiv Ψ
      (S := {x : Om8 K | x ∈ Subgroup.centralizer (centDer s : Set (Om8 K)) ∧ x ^ 3 = 1})
      (fun x hx => hle hx.1) (P := fun r => r ^ 3 = 1)
      (P' := fun u => ((u : ↥(unitaryIsom3 hU)) : GL (Fin 3) E) ∈ sc E ∧ u ^ 3 = 1)
      fun y => by
        have hpow : (y : Om8 K) ^ 3 = 1 ↔ (Ψ y).1 ^ 3 = 1 ∧ (Ψ y).2 ^ 3 = 1 := by
          rw [← SubgroupClass.coe_pow, OneMemClass.coe_eq_one, ← Ψ.injective.eq_iff, map_pow,
            map_one, Prod.ext_iff, Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one]
        rw [Set.mem_setOf_eq, hchar y, hpow]
        tauto
    rw [hR3, card_scal_mem_unitaryIsom3_pow_three hU h3 hω] at hc
    exact hc

end CentJ

end D4Inner

end CFSG.StandardType

end

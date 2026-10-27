module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62OneControl
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Gamma614Application
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import CFSG.GH74.KGroups.PSLN
import CFSG.CGT.PushingUpLit.T2KSW.Prop28
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
import CFSG.LieType.Simplicity.ExceptionalConverse
import CFSG.RankThree.PartOne.Mult.Exceptional

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (omegaOne)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC conjSetOf IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (uc22br4_M_ne_top uc22p20d_inCatalog_bar2 uc22p20p_odd_center_bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

@[expose] def R857List {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → List857 (Bar2 L)

@[expose] def R857Moreover {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → List857Clause1 (Bar2 L) →
    omegaOne 3 Q ≤ (Subgroup.center ↥(P ⊓ normalizer (L : Set G))).map
      (P ⊓ normalizer (L : Set G)).subtype

@[expose] def R857Cover {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → List857Clause2 (Bar2 L) → IsExtraspecialExpP 3 1 ↥Q

theorem r857_of_parts {G : Type} [Group G] [Finite G] {D : Data G}
    (hList : R857List D) (hMoreover : R857Moreover D) (hCover : R857Cover D) : R857 D :=
  fun L Q P h => ⟨hList L Q P h, hMoreover L Q P h, hCover L Q P h⟩

private theorem res_mem_uniqueSet_of_inU {G : Type} [Group G] {M X : Subgroup G}
    (h : UC6.InU M X) : X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  refine ⟨h.1, ?_⟩
  intro k hk
  have hk' : X ≤ CFSG.Open.uniqueFourConj k⁻¹ M := by
    simpa [CFSG.Open.uniqueFourConj] using hk
  have hconj := h.2 k⁻¹ hk'
  simpa [CFSG.Open.uniqueFourConj] using hconj

theorem r862_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (h63 : UC6.R6_3 D) (h859 : R859 D) (h861 : R861 D) : R862 D := by
  intro L Q P hcex
  have hLM : L ≤ D.M := hcex.mem.1.le
  have hLrank : 2 ≤ CFSG.Open.pRank 3 L := hcex.rank.ge
  have hPL : P ≤ normalizer (L : Set G) := h859 L Q P hcex
  have h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (centralizer (X : Set G) ⊓ L) :=
    fun X hXP hXc hXQ => (h861 L Q P hcex X hXP hXc hXQ).1
  refine ⟨fun X hX g hg => ?_, fun X hXP hN => ?_⟩
  · exact exists_mem_conj_forall_of_centralizer_transport h63 hLM hcex.sylowQ hcex.le
      hcex.sylowP hLrank hcex.gamma hPL h61 hX hg
  · exact res_mem_uniqueSet_of_inU
      (inU_of_normalizer_le_of_centralizer_transport h63 hLM hcex.sylowQ hcex.le hcex.sylowP
        hLrank hcex.gamma hPL h61 hXP hN)

private theorem res_le_omegaOne_of_isElemAbelian {G : Type} [Group G] {E Q : Subgroup G}
    (hEQ : E ≤ Q) (hE : CFSG.Open.IsElemAbelian 3 E) : E ≤ omegaOne 3 Q := by
  intro e he
  exact Subgroup.subset_closure ⟨hEQ he, hE.2 e he⟩

theorem Cex856.false_of_omegaOne_le_center {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (hcex : Cex856 D L Q P) (hOmega : omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype) :
    False := by
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hcex.mem
  have hsub : D.sig ⊆ D.sig1 := UC6S846.sig_subset_sig1 hSg hns
  have h3 : 3 ∉ D.sig := fun h => hcex.notStrong (UC6S846.sp_of_mem_sig hSg hns h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hEel, hEcard⟩ := CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq (p := 3)
    (by norm_num) hcex.sylowQ.isPGroup hcex.not_isCyclic_sylowQ
  have hEΩ : E ≤ omegaOne 3 Q := res_le_omegaOne_of_isElemAbelian hEQ hEel
  exact hcex.notStrong
    (h614 hsub 3 Nat.prime_three (by norm_num) h3 P hcex.sylowP E
      (e9_le_center_sylow_of_omega hcex.le hOmega hEΩ) hEel hEcard
      (gamma_le_of_gammaQ_of_le hEQ hcex.gamma))

theorem r860_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h859 : R859 D)
    (hMoreover : R857Moreover D) : R860 D := by
  intro L Q P hcex hcl
  have hOmega := hMoreover L Q P hcex hcl
  rw [inf_eq_left.mpr (h859 L Q P hcex)] at hOmega
  exact hcex.false_of_omegaOne_le_center hSg h614 hOmega

theorem r857Moreover_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (hNC : Eight60FieldNoThreeCover) (hSmall : Eight60FieldSmallInput) : R857Moreover D := by
  intro L Q P hcex hcl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLN : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  have hQS : Q ≤ P ⊓ normalizer (L : Set G) := le_inf hcex.le (hcex.sylowQ.le.trans hLN)
  have hSM : P ⊓ normalizer (L : Set G) ≤ D.M ⊓ normalizer (L : Set G) :=
    inf_le_inf_right _ hcex.sylowP.le
  obtain ⟨P', hP', hSP'⟩ : ∃ P' : Subgroup G,
      IsSylowOf 3 P' (D.M ⊓ normalizer (L : Set G)) ∧ P ⊓ normalizer (L : Set G) ≤ P' := by
    obtain ⟨S, hS⟩ := ((hcex.sylowP.isPGroup.to_inf_left (K := normalizer (L : Set G))).comap_subtype
      (K := D.M ⊓ normalizer (L : Set G))).exists_le_sylow
    exact ⟨S.map (D.M ⊓ normalizer (L : Set G)).subtype, ⟨S, rfl⟩,
      fun x hx => ⟨⟨x, hSM hx⟩, hS hx, rfl⟩⟩
  have hΩ := omegaOne_le_center_of_list857Clause1 hNC hSmall inf_le_right hcl hcex.rank
    hcex.sylowQ hP' (hQS.trans hSP')
  intro x hx
  have hxQ : x ∈ Q := (Subgroup.closure_le Q).2 (fun _ hy => hy.1) hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp (hΩ hx)
  refine Subgroup.mem_map.mpr ⟨⟨(z : G), hQS hxQ⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y.1, hSP' y.2⟩)
  exact Subtype.ext (by simpa using h2)

open scoped IsMulCommutative in
theorem sylow_three_noncomm_of_perfect_of_center {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (hZ : 3 ∣ Nat.card (Subgroup.center X)) (S : Sylow 3 X) :
    ∃ x ∈ (S : Subgroup X), ∃ y ∈ (S : Subgroup X), x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsMulCommutative (S : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 hZ
  have hVone : ∀ g : X, MonoidHom.transfer (MonoidHom.id (S : Subgroup X)) g = 1 := by
    intro g
    have h1 : commutator X ≤ (MonoidHom.transfer (MonoidHom.id (S : Subgroup X))).ker :=
      Abelianization.commutator_subset_ker _
    rw [Group.isPerfect_def.mp hperf] at h1
    exact h1 (Subgroup.mem_top g)
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * (z : X) ^ k * g₀ ∈ (S : Subgroup X) →
      g₀⁻¹ * (z : X) ^ k * g₀ = (z : X) ^ k := by
    intro k g₀ _
    have hc : (z : X) ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ z.2 k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hc g₀, inv_mul_cancel_left]
  have hS := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup X)) (z : X) hkey
  rw [hVone] at hS
  have hpow : (z : X) ^ (S : Subgroup X).index = 1 := congrArg Subtype.val hS.symm
  have hdvd : orderOf (z : X) ∣ (S : Subgroup X).index := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hz] at hdvd
  exact S.not_dvd_index hdvd

@[expose] def SylowThreeLinesMoved (A : Type) [Group A] : Prop :=
  ∀ S : Sylow 3 A, Nat.card ↥(S : Subgroup A) = 9 ∧ (∀ x ∈ (S : Subgroup A), x ^ 3 = 1) ∧
    ∀ E : Subgroup A, E ≤ (S : Subgroup A) → Nat.card ↥E = 3 →
      ∃ n ∈ normalizer ((S : Subgroup A) : Set A), ∃ e ∈ E, n * e * n⁻¹ ∉ E

private theorem res_no_sqrt_neg_one : ∀ r : ZMod 3, r * r + 1 ≠ 0 := by decide

open CFSG.RankThree.Asc83Table in
theorem sylowThreeLinesMoved_of_witness {A : Type} [Group A] [Finite A] (a b t : A)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) (hta : t * a * t⁻¹ = b) (htb : t * b * t⁻¹ = a⁻¹)
    (hcard : (Nat.card A).factorization 3 = 2) : SylowThreeLinesMoved A := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEa, hEb⟩ : ∃ E : E9Basis A, E.a = a ∧ E.b = b :=
    ⟨⟨a, b, ha, hb, hab, card_closure_pair_eq_nine ha hb hab ha1 hba⟩, rfl, rfl⟩
  have hs_a : t * t * a * (t * t)⁻¹ = a⁻¹ := by
    calc t * t * a * (t * t)⁻¹ = t * (t * a * t⁻¹) * t⁻¹ := by group
      _ = a⁻¹ := by rw [hta, htb]
  have hs_b : t * t * b * (t * t)⁻¹ = b⁻¹ := by
    calc t * t * b * (t * t)⁻¹ = t * (t * b * t⁻¹) * t⁻¹ := by group
      _ = b⁻¹ := by rw [htb, ← hta]; group
  have ha2 : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha)
  have hinv : ∀ y ∈ E.sub, t * t * y * (t * t)⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨i, j, -, -, rfl⟩ := E.exists_pow_mul_pow hy
    rw [hEa, hEb]
    have e1 : (t * t) * a ^ i * (t * t)⁻¹ = (a ^ i)⁻¹ := by rw [← conj_pow, hs_a, inv_pow]
    have e2 : (t * t) * b ^ j * (t * t)⁻¹ = (b ^ j)⁻¹ := by rw [← conj_pow, hs_b, inv_pow]
    calc t * t * (a ^ i * b ^ j) * (t * t)⁻¹
        = ((t * t) * a ^ i * (t * t)⁻¹) * ((t * t) * b ^ j * (t * t)⁻¹) := by group
      _ = (a ^ i)⁻¹ * (b ^ j)⁻¹ := by rw [e1, e2]
      _ = (a ^ i * b ^ j)⁻¹ := by
        rw [mul_inv_rev]
        exact ((hab.pow_pow i j).inv_inv).eq
  have htN : t ∈ Subgroup.normalizer (E.sub : Set A) := by
    have h := E.mem_normalizer_of_conj (g := t) 0 2 1 0
      (by rw [hEa, hEb, hta]; simp) (by rw [hEa, hEb, htb, pow_zero, mul_one]; exact ha2)
    rwa [E.closure_range] at h
  intro S
  obtain ⟨hEA, hS9⟩ := e9_sylow E hcard S
  obtain ⟨-, hcube⟩ := isElementaryAbelian_iff.mp hEA
  refine ⟨hS9, hcube, ?_⟩
  obtain ⟨g, hg⟩ := exists_sylow_eq_map (e9_card_sylow E hcard) S
  intro E' hE'S hE'3
  have hnN : g * t * g⁻¹ ∈ Subgroup.normalizer ((S : Subgroup A) : Set A) := by
    rw [hg]
    have := Subgroup.le_normalizer_map (H := E.sub) (MulAut.conj g).toMonoidHom
      (Subgroup.mem_map_of_mem _ htN)
    simpa using this
  have hninv : ∀ x ∈ (S : Subgroup A),
      (g * t * g⁻¹) * (g * t * g⁻¹) * x * ((g * t * g⁻¹) * (g * t * g⁻¹))⁻¹ = x⁻¹ := by
    intro x hx
    rw [hg] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 := hinv y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc _ = g * (t * t * y * (t * t)⁻¹) * g⁻¹ := by group
      _ = _ := by rw [h1]; group
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E', e ≠ 1 := by
    by_contra h
    push Not at h
    have : E' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hE'3
    omega
  refine ⟨g * t * g⁻¹, hnN, e, he, ?_⟩
  intro hne
  have heS : e ∈ (S : Subgroup A) := hE'S he
  have he3 : e ^ 3 = 1 := hcube e heS
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hz3 : Nat.card (Subgroup.zpowers e) = 3 := by rw [Nat.card_zpowers, hord]
  have hzle : Subgroup.zpowers e ≤ E' := (Subgroup.zpowers_le).mpr he
  have hzeq : Subgroup.zpowers e = E' :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hz3, hE'3])
  rw [← hzeq] at hne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hne
  have hsq := hninv e heS
  have h2 : (g * t * g⁻¹) * (g * t * g⁻¹) * e * ((g * t * g⁻¹) * (g * t * g⁻¹))⁻¹ =
      e ^ (k * k) := by
    calc _ = (g * t * g⁻¹) * ((g * t * g⁻¹) * e * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹ := by group
      _ = (g * t * g⁻¹) * e ^ k * (g * t * g⁻¹)⁻¹ := by rw [← hk]
      _ = ((g * t * g⁻¹) * e * (g * t * g⁻¹)⁻¹) ^ k := (conj_zpow).symm
      _ = e ^ (k * k) := by rw [← hk, ← zpow_mul]
  have h3 : e ^ (k * k + 1) = 1 := by
    rw [zpow_add_one, ← h2, hsq, inv_mul_cancel]
  have hdvd : (3 : ℤ) ∣ k * k + 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rwa [hord] at this
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k + 1) 3).mpr hdvd
  push_cast at hz
  exact res_no_sqrt_neg_one _ hz

private theorem res_linesMoved_of_equiv {A B : Type} [Group A] [Finite A] [Group B] (e : A ≃* B)
    (a b t : B) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) (hta : t * a * t⁻¹ = b) (htb : t * b * t⁻¹ = a⁻¹)
    (hcard : (Nat.card B).factorization 3 = 2) : SylowThreeLinesMoved A := by
  refine sylowThreeLinesMoved_of_witness (e.symm a) (e.symm b) (e.symm t) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · exact hab.map e.symm
  · intro h
    exact ha1 (e.symm.injective (by rw [h, map_one]))
  · intro h
    apply hba
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.symm.injective ?_⟩
    rw [map_zpow, hk]
  · simpa using congrArg e.symm hta
  · simpa using congrArg e.symm htb
  · rw [Nat.card_congr e.toEquiv]
    exact hcard

private def resA6a : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def resA6b : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [3, 4, 5], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def resA6t : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 3, 1, 4] * List.formPerm [2, 5],
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private theorem resA6_a3 : resA6a ^ 3 = 1 := by decide +kernel
private theorem resA6_b3 : resA6b ^ 3 = 1 := by decide +kernel
private theorem resA6_ab : resA6a * resA6b = resA6b * resA6a := by decide +kernel
private theorem resA6_a1 : resA6a ≠ 1 := by decide +kernel
private theorem resA6_b0 : resA6b ≠ 1 := by decide +kernel
private theorem resA6_ba : resA6b ≠ resA6a := by decide +kernel
private theorem resA6_ba2 : resA6b ≠ resA6a ^ 2 := by decide +kernel
private theorem resA6_ta : resA6t * resA6a * resA6t⁻¹ = resA6b := by decide +kernel
private theorem resA6_tb : resA6t * resA6b * resA6t⁻¹ = resA6a⁻¹ := by decide +kernel

private def resA7a : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def resA7b : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [3, 4, 5], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def resA7t : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 3, 1, 4] * List.formPerm [2, 5],
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private theorem resA7_a3 : resA7a ^ 3 = 1 := by decide +kernel
private theorem resA7_b3 : resA7b ^ 3 = 1 := by decide +kernel
private theorem resA7_ab : resA7a * resA7b = resA7b * resA7a := by decide +kernel
private theorem resA7_a1 : resA7a ≠ 1 := by decide +kernel
private theorem resA7_b0 : resA7b ≠ 1 := by decide +kernel
private theorem resA7_ba : resA7b ≠ resA7a := by decide +kernel
private theorem resA7_ba2 : resA7b ≠ resA7a ^ 2 := by decide +kernel
private theorem resA7_ta : resA7t * resA7a * resA7t⁻¹ = resA7b := by decide +kernel
private theorem resA7_tb : resA7t * resA7b * resA7t⁻¹ = resA7a⁻¹ := by decide +kernel

theorem threeCoverSylowQuot_alt :
    ∀ (A : Type) [Group A] [Finite A], (IsAlt A 6 ∨ IsAlt A 7) → SylowThreeLinesMoved A := by
  intro A _ _ h
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine res_linesMoved_of_equiv e resA6a resA6b resA6t resA6_a3 resA6_b3 resA6_ab resA6_a1
      (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne resA6_a3 resA6_b0 resA6_ba resA6_ba2)
      resA6_ta resA6_tb ?_
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (by decide : Nat.factorial 6 / 2 = 3 ^ 2 * 40) (by norm_num)
  · refine res_linesMoved_of_equiv e resA7a resA7b resA7t resA7_a3 resA7_b3 resA7_ab resA7_a1
      (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne resA7_a3 resA7_b0 resA7_ba resA7_ba2)
      resA7_ta resA7_tb ?_
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (by decide : Nat.factorial 7 / 2 = 3 ^ 2 * 280) (by norm_num)

private def resM22t : ↥CFSG.Blueprint.NativeSporadic.M22 := CFSG.Sporadic.Mathieu.m22b

private def resM22a : ↥CFSG.Blueprint.NativeSporadic.M22 :=
  CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22b *
    CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22a *
    CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22b⁻¹ *
    CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22b⁻¹ * CFSG.Sporadic.Mathieu.m22a *
    CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22a *
    CFSG.Sporadic.Mathieu.m22b * CFSG.Sporadic.Mathieu.m22b

private def resM22b : ↥CFSG.Blueprint.NativeSporadic.M22 := resM22t * resM22a * resM22t⁻¹

private theorem resM22_a3 : resM22a ^ 3 = 1 := by decide +kernel
private theorem resM22_b3 : resM22b ^ 3 = 1 := by decide +kernel
private theorem resM22_ab : resM22a * resM22b = resM22b * resM22a := by decide +kernel
private theorem resM22_a1 : resM22a ≠ 1 := by decide +kernel
private theorem resM22_b0 : resM22b ≠ 1 := by decide +kernel
private theorem resM22_ba : resM22b ≠ resM22a := by decide +kernel
private theorem resM22_ba2 : resM22b ≠ resM22a ^ 2 := by decide +kernel
private theorem resM22_ta : resM22t * resM22a * resM22t⁻¹ = resM22b := rfl
private theorem resM22_tb : resM22t * resM22b * resM22t⁻¹ = resM22a⁻¹ := by decide +kernel

theorem threeCoverSylowQuot_M22 :
    ∀ (A : Type) [Group A] [Finite A], IsSpor A .M22 → SylowThreeLinesMoved A := by
  intro A _ _ h
  obtain ⟨e⟩ := h
  let e' : A ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  refine res_linesMoved_of_equiv e' resM22a resM22b resM22t resM22_a3 resM22_b3 resM22_ab
    resM22_a1
    (CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne resM22_a3 resM22_b0 resM22_ba resM22_ba2)
    resM22_ta resM22_tb ?_
  rw [CFSG.CGT.PushingUpLit.T2KSW.card_nativeM22_eq]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (by norm_num : 443520 = 3 ^ 2 * 49280) (by norm_num)

private theorem res_exponent_eq_three {P : Type} [Group P] (hexp : ∀ g : P, g ^ 3 = 1)
    (hnt : Nat.card P ≠ 1) : Monoid.exponent P = 3 := by
  have hdvd : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exfalso
    apply hnt
    have h1 : ∀ g : P, g = 1 := fun g => by
      have := Monoid.pow_exponent_eq_one g
      rwa [h, pow_one] at this
    have : Subsingleton P := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
    exact Nat.card_of_subsingleton (1 : P)
  · exact h

private theorem res_cube_eq_one_of_linesMoved {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3)
    (hA : SylowThreeLinesMoved (X ⧸ Subgroup.center X)) (S : Sylow 3 X) :
    ∀ g ∈ (S : Subgroup X), g ^ 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center X with hZdef
  set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZc : π.ker ≤ Subgroup.center X := hker.le
  have hZ3 : Nat.card π.ker = 3 := by rw [hker]; exact hZ
  set Sb : Sylow 3 (X ⧸ Z) := Sylow.mapSurjective hπ S with hSbdef
  have hSb : (Sb : Subgroup (X ⧸ Z)) = (S : Subgroup X).map π := by simp [hSbdef]
  obtain ⟨hc9, hc1, hline⟩ := hA Sb
  have hcomm : IsMulCommutative (Sb : Subgroup (X ⧸ Z)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hc9]; norm_num)
  have hab : ∀ a ∈ (Sb : Subgroup (X ⧸ Z)), ∀ b ∈ (Sb : Subgroup (X ⧸ Z)), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : (Sb : Subgroup (X ⧸ Z))) ⟨b, hb⟩)
  have hE : CFSG.IsElementaryAbelian 3 (Sb : Subgroup (X ⧸ Z)) :=
    (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff).2 ⟨hab, hc1⟩
  let c := CFSG.RankThree.CentralExtension.cubeClassHom hπ hZc (Sb : Subgroup (X ⧸ Z))
  have hcone : c.ker = ⊤ := by
    by_contra hne
    have hidx : c.ker.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    have hrdvd : Nat.card c.range ∣ 3 := by
      have h1 : Nat.card c.range ∣
          Nat.card (π.ker ⧸ CFSG.RankThree.CentralExtension.centralCubes hZc) :=
        Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card (π.ker ⧸ CFSG.RankThree.CentralExtension.centralCubes hZc) ∣
          Nat.card π.ker := Subgroup.card_quotient_dvd_card _
      rw [hZ3] at h2
      exact h1.trans h2
    have hr3 : Nat.card c.range = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hrdvd with h | h
      · exact absurd (by rw [Subgroup.index_ker, h]) hidx
      · exact h
    have hK3 : Nat.card c.ker = 3 := by
      have h := Subgroup.card_mul_index c.ker
      rw [Subgroup.index_ker, hr3, hc9] at h
      omega
    have hE'c : Nat.card (c.ker.map (Sb : Subgroup (X ⧸ Z)).subtype) = 3 := by
      rw [Subgroup.card_map_of_injective (Sb : Subgroup (X ⧸ Z)).subtype_injective, hK3]
    obtain ⟨n, hn, e, he, hne'⟩ := hline _ (Subgroup.map_subtype_le _) hE'c
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp he
    apply hne'
    have hnk : n * (k : X ⧸ Z) * n⁻¹ ∈ (Sb : Subgroup (X ⧸ Z)) :=
      (Subgroup.mem_normalizer_iff.mp hn (k : X ⧸ Z)).mp k.2
    refine Subgroup.mem_map.mpr ⟨⟨_, hnk⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, CFSG.RankThree.CentralExtension.cubeClassHom_apply]
    have hk1 : CFSG.RankThree.CentralExtension.cubeClass hπ hZc (k : X ⧸ Z) = 1 := hk
    change CFSG.RankThree.CentralExtension.cubeClass hπ hZc (n * (k : X ⧸ Z) * n⁻¹) = 1
    rw [CFSG.RankThree.CentralExtension.cubeClass_conj hπ hZc n _ (hc1 _ k.2), hk1]
  intro g hg
  have hmem : π g ∈ (Sb : Subgroup (X ⧸ Z)) := hSb ▸ Subgroup.mem_map_of_mem π hg
  have hg3 : π g ^ 3 = 1 := hc1 _ hmem
  have hx : g ^ 3 ∈ π.ker := CFSG.RankThree.CentralExtension.pow_three_mem_ker hg3
  have h1 : CFSG.RankThree.CentralExtension.cubeClass hπ hZc (π g) = 1 := by
    have := (MonoidHom.mem_ker (f := c)).mp
      (show (⟨π g, hmem⟩ : (Sb : Subgroup (X ⧸ Z))) ∈ c.ker by rw [hcone]; exact Subgroup.mem_top _)
    exact this
  rw [CFSG.RankThree.CentralExtension.cubeClass_apply hπ hZc g hx, QuotientGroup.eq_one_iff] at h1
  obtain ⟨z, hz⟩ := h1
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥π.ker) (x := z)
    rwa [hZ3] at h
  rw [hz3] at hz
  exact congrArg Subtype.val hz.symm

theorem threeCoverSylow_of_quotientData {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (hZ : Nat.card (Subgroup.center X) = 3)
    (hA : SylowThreeLinesMoved (X ⧸ Subgroup.center X)) (S : Sylow 3 X) :
    IsExtraspecialExpP 3 1 ↥(S : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube := res_cube_eq_one_of_linesMoved hZ hA S
  have hcard : Nat.card (S : Subgroup X) = 27 := by
    set Z := Subgroup.center X with hZdef
    have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
    set Sb : Sylow 3 (X ⧸ Z) := Sylow.mapSurjective hπ S with hSbdef
    have hSb : Nat.card (Sb : Subgroup (X ⧸ Z)) = 9 := (hA Sb).1
    have hSbc := Sylow.card_eq_multiplicity Sb
    have hf : (Nat.card (X ⧸ Z)).factorization 3 = 2 := by
      have h9 : (3 : ℕ) ^ (Nat.card (X ⧸ Z)).factorization 3 = 3 ^ 2 := by
        rw [← hSbc, hSb]
        norm_num
      exact Nat.pow_right_injective (by norm_num) h9
    have hXc : Nat.card X = Nat.card (X ⧸ Z) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZ]
    have hXf : (Nat.card X).factorization 3 = 3 := by
      rw [hXc, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply, hf,
        Nat.Prime.factorization_self Nat.prime_three]
    rw [Sylow.card_eq_multiplicity S, hXf]
    norm_num
  have hexp : ∀ g : ↥(S : Subgroup X), g ^ 3 = 1 := fun g => Subtype.ext (hcube g g.2)
  have hnc : ¬ IsMulCommutative (S : Subgroup X) := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      sylow_three_noncomm_of_perfect_of_center hperf (by rw [hZ]) S
    exact hxy (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(S : Subgroup X)) ⟨y, hy⟩))
  have hext := CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three S.isPGroup' hexp
    (by rw [hcard]; norm_num) hnc
  exact isExtraspecialExpP_of_isHeisThree
    ⟨hext, hcard, res_exponent_eq_three hexp (by rw [hcard]; norm_num)⟩

theorem threeCoverSylowExtraspecial_holds :
    ∀ (X : Type) [Group X] [Finite X], (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) →
      ∀ S : Sylow 3 X, IsExtraspecialExpP 3 1 ↥(S : Subgroup X) := by
  intro X _ _ h S
  rcases h with ⟨hq, hZ, hA⟩ | ⟨hq, hZ, hA⟩ | ⟨hq, hZ, hA⟩
  · exact threeCoverSylow_of_quotientData hq.1 hZ
      (threeCoverSylowQuot_alt _ (Or.inl hA)) S
  · exact threeCoverSylow_of_quotientData hq.1 hZ
      (threeCoverSylowQuot_alt _ (Or.inr hA)) S
  · exact threeCoverSylow_of_quotientData hq.1 hZ (threeCoverSylowQuot_M22 _ hA) S

theorem r857Cover_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    : R857Cover D := by
  have hK := threeCoverSylowExtraspecial_holds
  intro L Q P hcex hcl
  exact isExtraspecialExpP_of_isSylowOf_bar hcex.sylowQ (hK (Bar2 L) hcl)

@[expose] def FiveCover (S : ∀ (Y : Type) [Group Y], Prop) (X : Type) [Group X] : Prop :=
  CFSG.Open.IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 5 ∧ S (X ⧸ Subgroup.center X)

@[expose] def Eight57FiveCoverCase (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 2 ∧ FiveCover (fun Y _ => LieModel Y .PSL 5 p f) X) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ FiveCover (fun Y _ => LieModel Y .PSU 5 p f) X)

@[expose] def Eight57OddCentreTable : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X) → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 →
      Odd (Nat.card (Subgroup.center X)) → ¬ IsPGroup 3 (Subgroup.center X) →
        Eight57FiveCoverCase X

@[expose] def ExceptionalCoverSmallPrimes : Prop :=
  ∀ (E J : Type) [Group E] [Group J] [Finite E], CFSG.Open.IsQuasisimple E →
    ((∃ p f : ℕ, LieModel J .G2 0 p f) ∨ (∃ p f : ℕ, LieModel J .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel J .twistedF4 0 2 f) ∨ LieModel J .Tits 0 2 1) →
    ∀ q : E →* J, Function.Surjective q → q.ker ≤ Subgroup.center E →
      ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card q.ker

private theorem rsexc_rep {G : Type} [Group G]
    (hJ : (∃ p f : ℕ, LieModel G .G2 0 p f) ∨ (∃ p f : ℕ, LieModel G .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel G .twistedF4 0 2 f) ∨ LieModel G .Tits 0 2 1) :
    CFSG.Blueprint.ExceptionalRep G := by
  rcases hJ with ⟨p, f, hm⟩ | ⟨p, f, hm⟩ | ⟨f, hm⟩ | hm
  · exact Or.inl ⟨.G2, p, f, by decide, hm.chevalleyExceptionalModel (by decide)⟩
  · exact Or.inl ⟨.trialityD4, p, f, by decide, hm.chevalleyExceptionalModel (by decide)⟩
  · exact Or.inr (Or.inl ⟨.twistedF4, 2, f, by decide, (hm.reeTitsModel (by decide)).2⟩)
  · exact Or.inr (Or.inl ⟨.Tits, 2, 1, by decide, (hm.reeTitsModel (by decide)).2⟩)

private theorem rsexc_transport {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (hJ : (∃ p f : ℕ, LieModel G .G2 0 p f) ∨ (∃ p f : ℕ, LieModel G .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel G .twistedF4 0 2 f) ∨ LieModel G .Tits 0 2 1) :
    (∃ p f : ℕ, LieModel G' .G2 0 p f) ∨ (∃ p f : ℕ, LieModel G' .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel G' .twistedF4 0 2 f) ∨ LieModel G' .Tits 0 2 1 := by
  rcases hJ with ⟨p, f, hm⟩ | ⟨p, f, hm⟩ | ⟨f, hm⟩ | hm
  · exact Or.inl ⟨p, f, hm.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨p, f, hm.of_mulEquiv e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hm.of_mulEquiv e⟩))
  · exact Or.inr (Or.inr (Or.inr (hm.of_mulEquiv e)))

theorem exceptionalCoverSmallPrimes_of_center
    (hECS : CFSG.RankThree.PartOne.ExceptionalCenterSmallPrimes) :
    ExceptionalCoverSmallPrimes := by
  intro E J _ _ _ hqs hJ q hsurj hker p hp hp3
  have hS : IsSimpleGroup J :=
    (CFSG.LieType.Simplicity.fam_exceptional_converse J (rsexc_rep hJ)).2.2
  have hcen : Subgroup.center E ≤ q.ker := by
    have := hS
    have hN : ((Subgroup.center E).map q).Normal := Subgroup.Normal.map inferInstance q hsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center E).map q) with h | h
    · intro z hz
      have hz' : q z ∈ (Subgroup.center E).map q := ⟨z, hz, rfl⟩
      rw [h, Subgroup.mem_bot] at hz'
      exact (MonoidHom.mem_ker).2 hz'
    · exfalso
      have htop : Subgroup.center E = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : q x ∈ (Subgroup.center E).map q := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨z, hz, hzx⟩ := hx
        have hk : z⁻¹ * x ∈ q.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
        rw [← mul_inv_cancel_left z x]
        exact Subgroup.mul_mem _ hz (hker hk)
      have := hqs.2
      have hsub : ∀ x : E ⧸ Subgroup.center E, x = 1 := by
        intro x
        refine QuotientGroup.induction_on x ?_
        intro a
        exact (QuotientGroup.eq_one_iff a).2 (by rw [htop]; exact Subgroup.mem_top a)
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (E ⧸ Subgroup.center E)
      exact hxy ((hsub x).trans (hsub y).symm)
  have hker_eq : q.ker = Subgroup.center E := le_antisymm hker hcen
  let e : E ⧸ Subgroup.center E ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hsurj)
  have hq' : CFSG.IsQuasisimple E := CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hqs
  have hrep : CFSG.Blueprint.ExceptionalRep (E ⧸ Subgroup.center E) :=
    rsexc_rep (rsexc_transport e.symm hJ)
  rw [hker_eq]
  exact hECS E hq' hrep p hp hp3

theorem exceptionalCoverSmallPrimes_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) : ExceptionalCoverSmallPrimes :=
  exceptionalCoverSmallPrimes_of_center
    (CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA)

section Odd

open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (classicalTags)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open GL83.I243.Cover (primeCentre)

private theorem rsodd_false_of_dvd {r m : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hm : m ∣ 12)
    (h : r ∣ m) : False := by
  have h12 : r ∣ 12 := h.trans hm
  have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases r <;> first | omega | exact absurd hr (by norm_num)

private theorem rsodd_false_of_dvd_small {r n : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hn : n ≠ 0)
    (hn4 : n ≤ 4) (h : r ∣ n) : False := by
  have hrle : r ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
  have h4 : r = 4 := by omega
  subst h4
  exact absurd hr (by norm_num)

private theorem rsodd_exists_prime {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X))) (hnot3 : ¬ IsPGroup 3 (Subgroup.center X)) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (Subgroup.center X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  apply hnot3
  have hpos : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card (Subgroup.center X) → d = 3 := by
    intro d hd hdvd
    have h2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
    by_contra h3
    have hd2 := hd.two_le
    exact hcon d hd (by omega) hdvd
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos hall)

private theorem rsodd_dvd_card_primeCentre {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrZ : r ∣ Nat.card (Subgroup.center X)) : r ∣ Nat.card (primeCentre 3 X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) r hrZ
  have hmem : QuotientGroup.mk' (primeCentre 3 X) (g : X) ∈
      Subgroup.center (X ⧸ primeCentre 3 X) := by
    rw [GL83.I243.Cover.center_quotient_eq_map hq]
    exact ⟨g, g.2, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1
    (GL83.I243.Cover.isPGroup_center_quotient (p := 3) hq) ⟨_, hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : 3 ^ k ∣ r := by
    have h1 : orderOf (QuotientGroup.mk' (primeCentre 3 X) (g : X)) ∣ orderOf (g : X) :=
      orderOf_map_dvd _ _
    rw [hk, Subgroup.orderOf_coe, hg] at h1
    exact h1
  have hk0 : k = 0 := by
    by_contra hne
    have h3 : 3 ∣ r := (dvd_pow_self 3 hne).trans hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h3
    omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have hgN : (g : X) ∈ primeCentre 3 X := (QuotientGroup.eq_one_iff _).1 hk
  have h := orderOf_dvd_natCard (⟨(g : X), hgN⟩ : ↥(primeCentre 3 X))
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg] at h

private theorem rsodd_card_dvd_hopf {X J : Type} [Group X] [Finite X] [Group J]
    (hE : Group.IsPerfect X) (M : Subgroup X) [M.Normal] (hM : M ≤ Subgroup.center X)
    (e : X ⧸ M ≃* J) : Nat.card M ∣ Nat.card (hopfMultiplier J) := by
  have hs : Function.Surjective ((e : X ⧸ M →* J).comp (QuotientGroup.mk' M)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective M)
  have hk : ((e : X ⧸ M →* J).comp (QuotientGroup.mk' M)).ker = M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE
    ((e : X ⧸ M →* J).comp (QuotientGroup.mk' M)) hs (by rw [hk]; exact hM)
  rwa [hk] at h

private theorem rsodd_center_eq_bot {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hs : IsSimpleGroup L) : Subgroup.center L = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : L, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center L := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
    have : Group.IsPerfect L := ⟨hq.1⟩
    have : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    have : Group.IsSolvable L := Group.isSolvable_of_comm hc
    exact Group.IsPerfect.not_isSolvable L inferInstance

private theorem rsodd_of_model_center (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (hq : CFSG.Open.IsQuasisimple X) {t : StatedLieTag} {n p f r : ℕ} (hn : n ≠ 0)
    (hm : LieModel (X ⧸ Subgroup.center X) t n p f) (hr : r.Prime) (hr3 : 3 < r)
    (hrZ : r ∣ Nat.card (Subgroup.center X)) :
    (t = .PSL ∨ t = .PSU) ∧ r ∣ n ∧ Nat.card (Subgroup.center X) ∣
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  have hq' : CFSG.IsQuasisimple X := CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq'
    (hm.statedClassicalModel_of_ne_zero hn)
  rcases CFSG.RankThree.PartOne.prime_dvd_table hr hr3 (hrZ.trans hd) with
    ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨Or.inl h1, h2, hd⟩
  · exact ⟨Or.inr h1, h2, hd⟩

private theorem rsodd_classical (hGA : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X)
    (e1 : (X ⧸ primeCentre 3 X) ⧸ Subgroup.center (X ⧸ primeCentre 3 X) ≃*
      X ⧸ Subgroup.center X)
    {t : StatedLieTag} (ht : t ∈ classicalTags) {n p f r : ℕ} (hn : n ≠ 0)
    (hm : LieModel (X ⧸ primeCentre 3 X) t n p f) (hr : r.Prime) (hr3 : 3 < r)
    (hrZ : r ∣ Nat.card (Subgroup.center X)) :
    LieModel (X ⧸ Subgroup.center X) t n p f ∧ (t = .PSL ∨ t = .PSU) ∧ r ∣ n ∧
      Nat.card (Subgroup.center X) ∣
        ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
          ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  have hbot := rsodd_center_eq_bot (GL83.I243.Cover.isQuasisimple_quotient (p := 3) hq)
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht hm)
  have e0 : (X ⧸ primeCentre 3 X) ⧸ Subgroup.center (X ⧸ primeCentre 3 X) ≃*
      X ⧸ primeCentre 3 X :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hm' : LieModel (X ⧸ Subgroup.center X) t n p f :=
    LieModel.of_mulEquiv (e0.symm.trans e1) hm
  exact ⟨hm', rsodd_of_model_center hGA hq hn hm' hr hr3 hrZ⟩

private theorem rsodd_false_classical (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (e1 : (X ⧸ primeCentre 3 X) ⧸ Subgroup.center (X ⧸ primeCentre 3 X) ≃*
      X ⧸ Subgroup.center X)
    {t : StatedLieTag} (ht : t ∈ classicalTags) {n p f r : ℕ} (hn : n ≠ 0) (hn4 : n ≤ 4)
    (hm : LieModel (X ⧸ primeCentre 3 X) t n p f) (hr : r.Prime) (hr3 : 3 < r)
    (hrZ : r ∣ Nat.card (Subgroup.center X)) : False := by
  obtain ⟨-, -, hrn, -⟩ := rsodd_classical hGA hq e1 ht hn hm hr hr3 hrZ
  exact rsodd_false_of_dvd_small hr hr3 hn hn4 hrn

private theorem rsodd_table_dvd_five {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ} :
    ((genericOrders t 5 p f).1 * (genericOrders t 5 p f).2) *
      ((exceptionalOrders t 5 p f).1 * (exceptionalOrders t 5 p f).2) ∣ 5 := by
  rcases ht with rfl | rfl
  · have hg : genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := rfl
    have he : exceptionalOrders .PSL 5 p f = (1, 1) := rfl
    rw [hg, he]
    simpa using Nat.gcd_dvd_left 5 (p ^ f - 1)
  · have hg : genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := rfl
    have he : exceptionalOrders .PSU 5 p f = (1, 1) := rfl
    rw [hg, he]
    simpa using Nat.gcd_dvd_left 5 (p ^ f + 1)

private theorem rsodd_card_five {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {p f r : ℕ} (hr3 : 3 < r)
    (hrZ : r ∣ Nat.card (Subgroup.center X))
    (hd : Nat.card (Subgroup.center X) ∣
      ((genericOrders t 5 p f).1 * (genericOrders t 5 p f).2) *
        ((exceptionalOrders t 5 p f).1 * (exceptionalOrders t 5 p f).2)) :
    Nat.card (Subgroup.center X) = 5 := by
  have h5 : Nat.card (Subgroup.center X) ∣ 5 := hd.trans (rsodd_table_dvd_five ht)
  rcases (Nat.dvd_prime Nat.prime_five).1 h5 with h | h
  · rw [h] at hrZ
    exact absurd (Nat.le_of_dvd one_pos hrZ) (by omega)
  · exact h

private theorem rsodd_false_exceptional (hExc : ExceptionalCoverSmallPrimes) {X : Type}
    [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrN : r ∣ Nat.card (primeCentre 3 X))
    (hJ : (∃ p f : ℕ, LieModel (X ⧸ primeCentre 3 X) .G2 0 p f) ∨
      (∃ p f : ℕ, LieModel (X ⧸ primeCentre 3 X) .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel (X ⧸ primeCentre 3 X) .twistedF4 0 2 f) ∨
      LieModel (X ⧸ primeCentre 3 X) .Tits 0 2 1) : False := by
  have hk : (QuotientGroup.mk' (primeCentre 3 X)).ker = primeCentre 3 X :=
    QuotientGroup.ker_mk' _
  refine hExc X (X ⧸ primeCentre 3 X) hq hJ (QuotientGroup.mk' (primeCentre 3 X))
    (QuotientGroup.mk'_surjective _) (by rw [hk]; exact GL83.I243.Cover.primeCentre_le_center)
    r hr hr3 ?_
  rwa [hk]

theorem eight57OddCentreTable_of_inputs (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* s.Group))
    (hExc : ExceptionalCoverSmallPrimes)
    (h33 : UCK.K33) : Eight57OddCentreTable := by
  intro X _ _ hq hcat hr2 hodd hnot3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr, hr3, hrZ⟩ := rsodd_exists_prime hodd hnot3
  have hrN : r ∣ Nat.card (primeCentre 3 X) := rsodd_dvd_card_primeCentre hq hr hr3 hrZ
  have hNc : primeCentre 3 X ≤ Subgroup.center X := GL83.I243.Cover.primeCentre_le_center
  have hLq : CFSG.Open.IsQuasisimple (X ⧸ primeCentre 3 X) :=
    GL83.I243.Cover.isQuasisimple_quotient (p := 3) hq
  obtain ⟨e1⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
  have hcatL : CFSG.Open.IsCatalogGroup
      ((X ⧸ primeCentre 3 X) ⧸ Subgroup.center (X ⧸ primeCentre 3 X)) := by
    obtain ⟨i, ⟨f⟩⟩ := hcat
    exact ⟨i, ⟨e1.trans f⟩⟩
  have hNn : ¬ 3 ∣ Nat.card (primeCentre 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 GL83.I243.Cover.coprime_card_primeCentre
  have hrkL : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ primeCentre 3 X)) = 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (primeCentre 3 X) hNn]
    exact hr2
  have hq' : CFSG.IsQuasisimple X := CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq
  have hperf : Group.IsPerfect X := ⟨hq.1⟩
  rcases h33 _ hLq hcatL (GL83.I243.Cover.isPGroup_center_quotient (p := 3) hq) hrkL with
    h1 | h2 | h3 | h4 | h5
  ·
    exfalso
    rcases h1 with ⟨-, -, ⟨eA⟩⟩ | ⟨-, -, ⟨eA⟩⟩ | ⟨-, -, ⟨eM⟩⟩ | ⟨p, f, -, -, -, hm⟩ |
      ⟨p, f, -, -, -, hm⟩
    · have h6 := GL83.I243.CoverList.card_center_dvd_alternating hAlt hq' (n := 6)
        (by norm_num) (e1.symm.trans eA)
      exact rsodd_false_of_dvd hr hr3 (h6.trans (by norm_num)) hrZ
    · have h7 := GL83.I243.CoverList.card_center_dvd_alternating hAlt hq' (n := 7)
        (by norm_num) (e1.symm.trans eA)
      exact rsodd_false_of_dvd hr hr3 (h7.trans (by norm_num)) hrZ
    · obtain ⟨b⟩ := hbr .M22
      have h12 := GL83.I243.CoverList.card_center_dvd_sporadic hSpor hq' (s := .M22)
        ((e1.symm.trans eM).trans b)
      exact rsodd_false_of_dvd hr hr3 (h12.trans (by decide)) hrZ
    · obtain ⟨-, hrn, -⟩ := rsodd_of_model_center hGA hq (n := 3) (by norm_num)
        (LieModel.of_mulEquiv e1 hm) hr hr3 hrZ
      exact rsodd_false_of_dvd_small hr hr3 (by norm_num) (by norm_num) hrn
    · obtain ⟨-, hrn, -⟩ := rsodd_of_model_center hGA hq (n := 3) (by norm_num)
        (LieModel.of_mulEquiv e1 hm) hr hr3 hrZ
      exact rsodd_false_of_dvd_small hr hr3 (by norm_num) (by norm_num) hrn
  ·
    exfalso
    rcases h2 with ⟨⟨eA⟩⟩ | ⟨⟨eA⟩⟩
    · have h7 := rsodd_card_dvd_hopf (J := (TauCeti.CFSGIndex.alternating 7 (by norm_num)).Group)
        hperf (primeCentre 3 X) hNc eA
      rw [(hAlt 7 (by norm_num)).2] at h7
      exact rsodd_false_of_dvd hr hr3 (h7.trans (by norm_num)) hrN
    · have h6 := rsodd_card_dvd_hopf (J := (TauCeti.CFSGIndex.alternating 6 (by norm_num)).Group)
        hperf (primeCentre 3 X) hNc eA
      rw [(hAlt 6 (by norm_num)).2] at h6
      exact rsodd_false_of_dvd hr hr3 (h6.trans (by norm_num)) hrN
  ·
    exfalso
    rcases h3 with hm | hm
    · exact rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3 hrZ
    · exact rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3 hrZ
  ·
    rcases h4 with ⟨p, f, -, hm⟩ | ⟨p, f, -, hm⟩ | ⟨p, f, hm⟩ | ⟨p, f, hm⟩ | ⟨p, f, hm⟩ |
      ⟨f, hm⟩ | hm | ⟨p, f, -, hm⟩ | ⟨p, f, -, hm⟩ | ⟨p, f, hc, hm⟩ | ⟨p, f, hc, hm⟩
    · exact (rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3
        hrZ).elim
    · exact (rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3
        hrZ).elim
    · exact (rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3
        hrZ).elim
    · exact (rsodd_false_exceptional hExc hq hr hr3 hrN (Or.inl ⟨p, f, hm⟩)).elim
    · exact (rsodd_false_exceptional hExc hq hr hr3 hrN (Or.inr (Or.inl ⟨p, f, hm⟩))).elim
    · exact (rsodd_false_exceptional hExc hq hr hr3 hrN
        (Or.inr (Or.inr (Or.inl ⟨f, hm⟩)))).elim
    · exact (rsodd_false_exceptional hExc hq hr hr3 hrN (Or.inr (Or.inr (Or.inr hm)))).elim
    · exact (rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3
        hrZ).elim
    · exact (rsodd_false_classical hGA hq e1 (by decide) (by norm_num) (by norm_num) hm hr hr3
        hrZ).elim
    · obtain ⟨hm', hPSLU, -, hd⟩ := rsodd_classical hGA hq e1 (by decide) (by norm_num) hm hr hr3
        hrZ
      exact Or.inl ⟨p, f, hc, hq, rsodd_card_five hPSLU hr3 hrZ hd, hm'⟩
    · obtain ⟨hm', hPSLU, -, hd⟩ := rsodd_classical hGA hq e1 (by decide) (by norm_num) hm hr hr3
        hrZ
      exact Or.inr ⟨p, f, hc, hq, rsodd_card_five hPSLU hr3 hrZ hd, hm'⟩
  ·
    exfalso
    obtain ⟨s, hs, ⟨eS⟩⟩ := h5
    obtain ⟨b⟩ := hbr s
    have hdiv := rsodd_card_dvd_hopf (J := (TauCeti.CFSGIndex.sporadic s).Group) hperf
      (primeCentre 3 X) hNc (eS.trans b)
    rw [hSpor.1 s] at hdiv
    have h12 : CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s ∣ 12 := by
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact rsodd_false_of_dvd hr hr3 h12 (hrN.trans hdiv)

end Odd

theorem list857_or_fiveCover_of_inputs (h33 : UCK.K33) (hT : Eight57OddCentreTable)
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X))
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hnotSL3 : ¬ IsSL3PiType X) : List857 X ∨ Eight57FiveCoverCase X := by
  by_cases hZ : IsPGroup 3 (Subgroup.center X)
  · exact Or.inl (list857_of_K33 h33 hq hcat hZ hr hnotSL3)
  · exact Or.inr (hT X hq hcat hr hodd hZ)

theorem Cex856.isCatalogGroup_bar {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) :
    CFSG.Open.IsCatalogGroup (Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
  have hLM : L ≤ D.M := h.mem.1.le
  have hLtop : L ≠ ⊤ := fun htop => uc22br4_M_ne_top D (top_le_iff.mp (htop ▸ hLM))
  exact uc22p20d_inCatalog_bar2 D.standing.kProper hLtop h.mem.2.2

theorem Cex856.pRank_bar_eq_two {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    intro hdvd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn] at hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)) (by norm_num)
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = CFSG.Open.pRank 3 L :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥L).symm.trans
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 L)
  rw [h1, h2, h.rank]

theorem r857ListCov_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (h33 : UCK.K33) (hT : Eight57OddCentreTable) {L Q P : Subgroup G} (hcex : Cex856 D L Q P) :
    List857 (Bar2 L) ∨ Eight57FiveCoverCase (Bar2 L) :=
  list857_or_fiveCover_of_inputs h33 hT hcex.mem.2.2 hcex.isCatalogGroup_bar
    hcex.pRank_bar_eq_two (uc22p20p_odd_center_bar2 ↥L) hcex.notSL3

theorem omegaOne_le_center_of_fiveCoverCase {G : Type} [Group G] [Finite G]
    {M L Q P : Subgroup G} (hLM : M ≤ normalizer (L : Set G))
    (hcl : Eight57FiveCoverCase (Bar2 L)) (hQ : IsSylowOf 3 Q L) (hP : IsSylowOf 3 P M)
    (hQP : Q ≤ P) : omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  have key : AutOmegaCentral (Bar2 L) ∧ ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rcases hcl with ⟨p, f, hq, hperf, hc5, h⟩ | ⟨p, f, hq, hperf, hc5, h⟩
    · exact ⟨autOmegaCentral_of_perfect_centerQuotient (Group.isPerfect_def.mpr hperf.1)
        (autOmegaCentral_of_lieModel (Or.inl ⟨rfl, Or.inr rfl, hq⟩) h), by rw [hc5]; omega⟩
    · exact ⟨autOmegaCentral_of_perfect_centerQuotient (Group.isPerfect_def.mpr hperf.1)
        (autOmegaCentral_of_lieModel (Or.inr (Or.inl ⟨rfl, Or.inr rfl, hq⟩)) h),
        by rw [hc5]; omega⟩
  exact omegaOne_le_center_of_autOmegaCentral (hP.le.trans hLM) hP.isPGroup hQ.le hQP key.1 key.2

theorem Cex856.false_of_fiveCoverCase {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (hcex : Cex856 D L Q P) (hcl : Eight57FiveCoverCase (Bar2 L)) : False := by
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rcases hcl with ⟨p, f, -, -, hc5, -⟩ | ⟨p, f, -, -, hc5, -⟩ <;> rw [hc5] <;> omega
  have hm3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp hSg
      hcex.notStrong hcex.mem
  have hN : D.M ≤ normalizer (L : Set G) := by
    by_contra hN
    have h2 : 1 < (conjSetOf D.M L).ncard := two_le_ncard_conjSetOf_of_not_le_normalizer hN
    obtain ⟨L1, L2, hL1, hL2, h12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    have h4 := four_le_pRank_three_of_two_conj_of_not_three_dvd_center hcex.mem hL1 hL2 h12
      hcex.rank hZ3
    omega
  exact hcex.false_of_omegaOne_le_center hSg h614
    (omegaOne_le_center_of_fiveCoverCase hN hcl hcex.sylowQ hcex.sylowP hcex.le)

theorem r857List_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h33 : UCK.K33)
    (hT : Eight57OddCentreTable) : R857List D := fun _ _ _ hcex =>
  (r857ListCov_of_inputs h33 hT hcex).resolve_right (hcex.false_of_fiveCoverCase hSg h614)

theorem r857_of_inputs {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h33 : UCK.K33)
    (hT : Eight57OddCentreTable) (hNC : Eight60FieldNoThreeCover)
    (hSmall : Eight60FieldSmallInput) : R857 D :=
  r857_of_parts (r857List_of_inputs hSg h614 h33 hT) (r857Moreover_of_inputs hNC hSmall)
    r857Cover_of_inputs

theorem r857_of_tables {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h33 : UCK.K33)
    (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* s.Group))
    (hExc : ExceptionalCoverSmallPrimes) (hNC : Eight60FieldNoThreeCover)
    (hSmall : Eight60FieldSmallInput) : R857 D :=
  r857_of_inputs hSg h614 h33 (eight57OddCentreTable_of_inputs hGA hAlt hSpor hbr hExc h33) hNC
    hSmall

private theorem res_isExtraspecialExpP_sylow_of_mulEquiv {X N : Type} [Group X] [Group N]
    [Finite X] [Finite N] (e : X ≃* N) (Q₀ : Sylow 3 N)
    (h : IsExtraspecialExpP 3 1 ↥(Q₀ : Subgroup N)) (Q : Sylow 3 X) :
    IsExtraspecialExpP 3 1 ↥(Q : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q' : Sylow 3 N := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup N) = (Q : Subgroup X).map e.toMonoidHom := by simp [Q']
  have h1 : (Q : Subgroup X) ≃* (Q' : Subgroup N) := by
    rw [hQ']
    exact e.subgroupMap (Q : Subgroup X)
  have h2 : (Q' : Subgroup N) ≃* (Q₀ : Subgroup N) := Sylow.equiv Q' Q₀
  exact isExtraspecialExpP_of_mulEquiv (h1.trans h2) h

open scoped commutatorElement in
theorem isExtraspecialExpP_sylow_of_ex27 {N : Type} [Group N] [Finite N] {x y : N}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) (hN : (Nat.card N).factorization 3 = 3) {L : Type} [Group L] [Finite L]
    (e : L ≃* N) (P : Sylow 3 L) : IsExtraspecialExpP 3 1 ↥(P : Subgroup L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P₀ : Subgroup N := Subgroup.closure ({x, y} : Set N) with hP₀
  have hcard : Nat.card P₀ = 27 := CFSG.RankThree.Asc83Table.ex27_card hx hy hzx hzy hz1
  have hP₀p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hexp : ∀ g : P₀, g ^ 3 = 1 := fun g =>
    Subtype.ext (CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy g.2)
  have hnc : ¬ IsMulCommutative P₀ := by
    intro hc
    apply hz1
    rw [commutatorElement_eq_one_iff_mul_comm]
    have := mul_comm' (⟨x, Subgroup.subset_closure (by simp)⟩ : P₀)
      ⟨y, Subgroup.subset_closure (by simp)⟩
    exact congrArg Subtype.val this
  have hext := CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP₀p hexp
    (by rw [hcard]; norm_num) hnc
  have hH : IsExtraspecialExpP 3 1 ↥P₀ :=
    isExtraspecialExpP_of_isHeisThree
      ⟨hext, hcard, res_exponent_eq_three hexp (by rw [hcard]; norm_num)⟩
  have hsyl : Nat.card P₀ = 3 ^ (Nat.card N).factorization 3 := by
    rw [hN, hcard]
    norm_num
  exact res_isExtraspecialExpP_sylow_of_mulEquiv e (Sylow.ofCard P₀ hsyl) hH P

private def resX : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

private def resY : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

private def resZ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

private theorem res_sl3_xy : resX * resY = resZ * (resY * resX) := by decide +kernel

open scoped commutatorElement in
private theorem res_sl3_comm : ⁅resX, resY⁆ = resZ := by
  rw [commutatorElement_def]
  calc resX * resY * resX⁻¹ * resY⁻¹ = resZ * (resY * resX) * resX⁻¹ * resY⁻¹ := by
        rw [res_sl3_xy]
    _ = resZ := by group

private theorem res_center_sl3 :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  have cube_one : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := cube_one r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

private theorem res_card_sl3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem sylow_isExtraspecialExpP_of_l33 :
    ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 3 1 →
      ∀ S : Sylow 3 Y, IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) := by
  intro Y _ _ h S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    (by rw [Nat.card_zmod]; norm_num) h
  have e2 : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq res_center_sl3).trans QuotientGroup.quotientBot
  refine isExtraspecialExpP_sylow_of_ex27 (x := resX) (y := resY) (by decide +kernel)
    (by decide +kernel) ?_ ?_ ?_ ?_ (e1.trans e2) S
  · rw [res_sl3_comm]
    exact (by decide +kernel : resZ * resX = resX * resZ)
  · rw [res_sl3_comm]
    exact (by decide +kernel : resZ * resY = resY * resZ)
  · rw [res_sl3_comm]
    decide +kernel
  · rw [res_card_sl3]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 5616 = 3 ^ 3 * 208 by norm_num) (by norm_num)

theorem sylow_isExtraspecialExpP_of_tits
    : ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .Tits 0 2 1 →
      ∀ S : Sylow 3 Y, IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) := by
  intro Y _ _ h S
  have hree : CFSG.Blueprint.ReeTitsModel Y .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hree
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, hcard, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := K) hK
  have hfin : Finite (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) :=
    Finite.of_equiv Y e.toEquiv
  have hdvd := CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd (K := K) hK
  have h27 : 3 ^ 3 ∣ Nat.card (commutator (CFSG.LieType.Ree.reeFixed
      CFSG.LieType.Ree.ReeTag.F4 K 0)) := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hpos : Nat.card (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) ≠
      0 := Nat.card_pos.ne'
  have hN : (Nat.card (commutator (CFSG.LieType.Ree.reeFixed
      CFSG.LieType.Ree.ReeTag.F4 K 0))).factorization 3 = 3 := by
    refine le_antisymm ?_ ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 h27)
    have hle := (Nat.factorization_le_iff_dvd hpos (by norm_num)).2 hdvd 3
    rwa [CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 35942400 = 3 ^ 3 * 1331200 by norm_num) (by norm_num)] at hle
  exact isExtraspecialExpP_sylow_of_ex27 hx hy hzx hzy hz hN e S

theorem sylowIsExtraspecialOfTypes_holds
    : SylowIsExtraspecialOfTypes := by
  intro Y _ _ h S
  exact h.elim (fun h => sylow_isExtraspecialExpP_of_l33 Y h S)
    (fun h => sylow_isExtraspecialExpP_of_tits Y h S)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

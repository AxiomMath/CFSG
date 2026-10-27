module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType.UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']

theorem diag_norm_one_of_mem_unitarySU {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) {D : ↥(unitarySU 2 n K d)} {w : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w) (i : Fin d) :
    w i ^ (2 ^ n + 1) = 1 := by
  have hunit := (mem_unitarySU_iff hK).mp D.2
  rw [hD] at hunit
  have hmat := hunit.2
  rw [Matrix.diagonal_map (map_zero hK.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hmat
  have hii := congrFun (congrFun hmat i) i
  simp only [Matrix.diagonal_apply_eq] at hii
  rw [hK.bar_apply, ← pow_succ] at hii
  exact hii

theorem diag_pow_norm_eq_of_mem_normalizer {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t : Fin d → K} (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (i j : Fin d) :
    t i ^ (2 ^ n + 1) = t j ^ (2 ^ n + 1) := by
  by_cases hij : i = j
  · rw [hij]
  set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
  set P : ↥(unitarySU 2 n K d) := LineU.permSU hK σ with hP
  set Y : ↥(unitarySU 2 n K d) := LineU.conjN D hD P * P⁻¹ with hY
  have hYeq : (Y : GL (Fin d) K) = D * (P * D⁻¹ * P⁻¹) := by
    rw [hY]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
    group
  have hYmat : ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => t k * (t (σ⁻¹ k))⁻¹) := by
    rw [hYeq]
    simp only [Subgroup.coe_inv, Units.val_mul]
    rw [hDt, hP, LineU.coe_permSU, LineU.coe_permGL_matrix, LineU.coe_inv_diag hDt,
      LineU.coe_permGL_inv_matrix, LineU.permMatrix_conj_diag σ (fun k => (t k)⁻¹),
      diagonal_mul_diagonal]
  have hnorm := diag_norm_one_of_mem_unitarySU hK hYmat i
  rw [hσ, Equiv.swap_inv, Equiv.swap_apply_left] at hnorm
  have htj : t j ≠ 0 := LineU.diag_ne_zero_of_eq hDt j
  have h1 : t i ^ (2 ^ n + 1) * (t j ^ (2 ^ n + 1))⁻¹ = 1 := by
    simpa [mul_pow, inv_pow] using hnorm
  exact (mul_inv_eq_one₀ (pow_ne_zero _ htj)).mp h1

structure Model (φ : ↥(unitarySU 2 n K d) →* L') : Prop where
  field : UnitaryFieldData 2 n K
  surj : Function.Surjective φ
  ker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
    ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c

theorem Model.block {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    (S : Finset (Fin d)) :
    Model ((φ.comp (TableBUE.blockExtSU S hM.field)).rangeRestrict) := by
  classical
  refine ⟨hM.field, (φ.comp (TableBUE.blockExtSU S hM.field)).rangeRestrict_surjective, ?_⟩
  intro g hg
  have hg' : φ (TableBUE.blockExtSU S hM.field g) = 1 := congrArg Subtype.val hg
  obtain ⟨c, hc⟩ := hM.ker _ hg'
  refine ⟨c, ?_⟩
  have hr := congrArg (TableBUE.blockRes S) hc
  rw [TableBUE.coe_blockExtSU, TableBUE.blockRes_blockExt] at hr
  calc
    ((g : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
        TableBUE.blockRes S (diagonal fun _ => c) := hr
    _ = diagonal (fun _ => c) := by
      ext a b
      change (diagonal (fun _ : Fin d => c)) (S.equivFin.symm a) (S.equivFin.symm b) =
        (diagonal (fun _ : Fin S.card => c)) a b
      by_cases hab : a = b
      · subst b
        simp only [diagonal_apply_eq]
      · have hne : ((S.equivFin.symm a : ↥S) : Fin d) ≠ S.equivFin.symm b :=
          fun h => hab (S.equivFin.symm.injective (Subtype.ext h))
        rw [diagonal_apply_ne _ hne, diagonal_apply_ne _ hab]

theorem Model.injective_comp_blockExtSU {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : Model φ) (S : Finset (Fin d)) (hS : ∃ i : Fin d, i ∉ S) :
    Function.Injective (φ.comp (TableBUE.blockExtSU S hM.field)) := by
  classical
  obtain ⟨i, hi⟩ := hS
  intro x y hxy
  have hker : φ (TableBUE.blockExtSU S hM.field (x * y⁻¹)) = 1 := by
    change (φ.comp (TableBUE.blockExtSU S hM.field)) (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hM.ker _ hker
  have hspec := TableBUE.isBlockOn_blockExt (S := S)
    (((x * y⁻¹ : ↥(unitarySU 2 n K S.card)) : GL (Fin S.card) K) :
      Matrix (Fin S.card) (Fin S.card) K) i i (Or.inl hi)
  change (((TableBUE.blockExtSU S hM.field (x * y⁻¹) :
    ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i =
      (1 : Matrix (Fin d) (Fin d) K) i i at hspec
  rw [hc, diagonal_apply_eq, one_apply_eq] at hspec
  have hext : TableBUE.blockExtSU S hM.field (x * y⁻¹) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (((TableBUE.blockExtSU S hM.field (x * y⁻¹) :
      ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1
    simpa only [hspec, Matrix.diagonal_one] using hc
  have hxy' : x * y⁻¹ = 1 := (TableBUE.blockExtSU_injective S hM.field) (by
    simpa only [map_one] using hext)
  exact mul_inv_eq_one.mp hxy'

section Acts

variable {φ : ↥(unitarySU 2 n K d) →* L'}

theorem actsDiagU_mul {a b : MulAut L'} {t u : Fin d → K} (ha : ActsDiagU φ a t)
    (hb : ActsDiagU φ b u) : ActsDiagU φ (a * b) (fun k => t k * u k) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  refine ⟨D * E, Subgroup.mul_mem _ hD hE, ?_, fun s => ?_⟩
  · rw [Units.val_mul, hDt, hEt, diagonal_mul_diagonal]
  · rw [MulAut.mul_apply, hbct s, hact (conjN E hE s)]
    congr 1
    apply Subtype.ext
    simp only [coe_conjN, _root_.mul_inv_rev]
    group

theorem actsDiagU_inv {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) :
    ActsDiagU φ a⁻¹ (fun k => (t k)⁻¹) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have hDi : D⁻¹ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.inv_mem _ hD
  refine ⟨D⁻¹, hDi, coe_inv_diag hDt, fun s => ?_⟩
  have h := hact (conjN D⁻¹ hDi s)
  have e : conjN D hD (conjN D⁻¹ hDi s) = s := by
    apply Subtype.ext
    simp only [coe_conjN]
    group
  rw [e] at h
  rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem actsDiagU_unique (hφs : Function.Surjective φ) {a b : MulAut L'} {t : Fin d → K}
    (ha : ActsDiagU φ a t) (hb : ActsDiagU φ b t) : a = b := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  have hDE : D = E := Units.ext (hDt.trans hEt.symm)
  subst hDE
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  rw [hact, hbct]

theorem actsDiagU_conj {D : ↥(unitarySU 2 n K d)} {t : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ActsDiagU φ (MulAut.conj (φ D)) t := by
  refine ⟨(D : GL (Fin d) K), Subgroup.le_normalizer D.2, hD, fun s => ?_⟩
  have e : conjN (D : GL (Fin d) K) (Subgroup.le_normalizer D.2) s = D * s * D⁻¹ :=
    Subtype.ext (by simp only [coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv])
  rw [e, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem actsDiagU_mul_const {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) {c : K}
    (hc : c ≠ 0) : ActsDiagU φ a (fun k => t k * c) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set z : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc) with hz
  have hzc : z ∈ Subgroup.center (GL (Fin d) K) := TableB.scalar_mem_center _
  have hzN : D * z ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.mul_mem _ hD (Subgroup.center_le_normalizer _ hzc)
  refine ⟨D * z, hzN, ?_, fun s => ?_⟩
  · rw [Units.val_mul, hDt, hz, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_mul_diagonal]
    rfl
  · rw [hact s]
    congr 1
    apply Subtype.ext
    have hs := Subgroup.mem_center_iff.mp hzc (s : GL (Fin d) K)
    simp only [coe_conjN, _root_.mul_inv_rev]
    calc (D : GL (Fin d) K) * s * D⁻¹
        = D * (z * s * z⁻¹) * D⁻¹ := by rw [← hs, mul_inv_cancel_right]
      _ = D * z * s * (z⁻¹ * D⁻¹) := by group

theorem actsDiagU_mul_conj_comm {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    {X : ↥(unitarySU 2 n K d)} {v : Fin d → K}
    (hX : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    a * MulAut.conj (φ X) = MulAut.conj (φ X) * a := by
  have h := ha.fix_of_diagonal X hX
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]

end Acts

private theorem ratio_eq_two {φ : ↥(unitarySU 2 n K 2) →* L'} (hM : Model φ)
    {a : MulAut L'} {t u : Fin 2 → K} (ha : ActsDiagU φ a t) (hb : ActsDiagU φ a u) :
    t 0 * (t 1)⁻¹ = u 0 * (u 1)⁻¹ := by
  let : CharP K 2 := hM.field.charP
  have htne : ∀ k, t k ≠ 0 := fun k => ha.ne_zero k
  have hune : ∀ k, u k ≠ 0 := fun k => hb.ne_zero k
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  set σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1 with hσ
  set X : ↥(unitarySU 2 n K 2) :=
    conjN D hD (permSU hM.field σ) * (conjN E hE (permSU hM.field σ))⁻¹ with hXdef
  have hXφ : φ X = 1 := by
    rw [hXdef, map_mul, map_inv, ← hact (permSU hM.field σ),
      ← hbct (permSU hM.field σ), mul_inv_cancel]
  obtain ⟨c, hc⟩ := hM.ker X hXφ
  have hdet := ((mem_unitarySU_iff hM.field).mp X.2).1
  rw [hc, det_diagonal] at hdet
  have hc2 : c ^ 2 = 1 := by
    simpa [Fin.prod_univ_two, pow_two] using hdet
  have hc1 : c = 1 := CharTwo.sq_inj.mp (by simpa only [one_pow] using hc2)
  set F : GL (Fin 2) K := D⁻¹ * E with hFdef
  have hF : (F : Matrix (Fin 2) (Fin 2) K) = diagonal (fun k => (t k)⁻¹ * u k) := by
    rw [hFdef, Units.val_mul, coe_inv_diag hDt, hEt, diagonal_mul_diagonal]
  have hX' : ((X : ↥(unitarySU 2 n K 2)) : GL (Fin 2) K) =
      D * (CFSG.RankThree.Classical.permGL σ * F *
        (CFSG.RankThree.Classical.permGL σ)⁻¹) * E⁻¹ := by
    rw [hXdef, hFdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN, coe_permSU]
    group
  have hXm : (((X : ↥(unitarySU 2 n K 2)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagonal (fun m => t m * ((t (σ⁻¹ m))⁻¹ * u (σ⁻¹ m)) * (u m)⁻¹) := by
    rw [hX']
    simp only [Units.val_mul]
    rw [hDt, coe_permGL_matrix, hF, coe_permGL_inv_matrix, coe_inv_diag hEt,
      permMatrix_conj_diag σ, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have hf : (fun m => t m * ((t (σ⁻¹ m))⁻¹ * u (σ⁻¹ m)) * (u m)⁻¹) = fun _ => c :=
    Matrix.diagonal_injective (hXm.symm.trans hc)
  have hi := congrFun hf 0
  rw [hσ, Equiv.swap_inv, Equiv.swap_apply_left, hc1] at hi
  field_simp [htne 0, htne 1, hune 0, hune 1] at hi ⊢
  linear_combination hi

private theorem ratio_pow_two {φ : ↥(unitarySU 2 n K 2) →* L'} (hM : Model φ)
    {a : MulAut L'} {t : Fin 2 → K} (ha : ActsDiagU φ a t) (hap : a ^ p = 1) :
    (t 0 * (t 1)⁻¹) ^ p = 1 := by
  have h1 : ActsDiagU φ 1 (fun k => t k ^ p) := by
    rw [← hap]
    exact ha.pow p
  have h2 := ratio_eq_two hM h1 (actsDiagU_one φ)
  simp only [inv_one, mul_one] at h2
  rw [mul_pow, inv_pow]
  exact h2

theorem card_diagonal_two_le [Finite K] {φ : ↥(unitarySU 2 n K 2) →* L'} (hM : Model φ)
    (hp : p.Prime) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin 2 → K, ActsDiagU φ a t) : Nat.card A ≤ p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  choose tA htA using fun a : A => hdiag a a.2
  have hne : ∀ (a : A) k, tA a k ≠ 0 := fun a k => (htA a).ne_zero k
  have hpow : ∀ a : A, (tA a 0 * (tA a 1)⁻¹) ^ p = 1 := fun a =>
    ratio_pow_two hM (htA a) (hAp a a.2)
  let f : A → ↥(rootsOfUnity p K) := fun a =>
    ⟨Units.mk0 (tA a 0 * (tA a 1)⁻¹) (mul_ne_zero (hne a 0) (inv_ne_zero (hne a 1))), by
      rw [mem_rootsOfUnity']
      exact hpow a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hr := congrArg (fun z : ↥(rootsOfUnity p K) => ((z : Kˣ) : K)) hab
    change tA a 0 * (tA a 1)⁻¹ = tA b 0 * (tA b 1)⁻¹ at hr
    have hn : (fun k : Fin 2 => tA a k * (tA a 1)⁻¹) =
        (fun k : Fin 2 => tA b k * (tA b 1)⁻¹) := by
      funext k
      fin_cases k
      · exact hr
      · exact (mul_inv_cancel₀ (hne a 1)).trans (mul_inv_cancel₀ (hne b 1)).symm
    have ha := actsDiagU_mul_const (htA a) (inv_ne_zero (hne a 1))
    have hb := actsDiagU_mul_const (htA b) (inv_ne_zero (hne b 1))
    apply Subtype.ext
    exact actsDiagU_unique hM.surj (hn ▸ ha) hb
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity K p)

theorem card_diagonal_pow_le {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    (hd : 3 ≤ d) (hp : p.Prime) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    Nat.card A ≤ p ^ (d - 1) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite K := hM.field.finite
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  choose tA htA using fun a : A => hdiag a a.2
  have hne : ∀ (a : A) k, tA a k ≠ 0 := fun a k => (htA a).ne_zero k
  have hpow : ∀ (a : A) (i : Fin m),
      (tA a i.castSucc * (tA a (Fin.last m))⁻¹) ^ p = 1 := fun a i =>
    (htA a).ratio_pow hM.field (by omega) hM.ker (hAp a a.2) i.castSucc (Fin.last m)
  let g : A → (Fin m → ↥(rootsOfUnity p K)) := fun a i =>
    ⟨Units.mk0 (tA a i.castSucc * (tA a (Fin.last m))⁻¹)
        (mul_ne_zero (hne a _) (inv_ne_zero (hne a _))),
      by
        rw [mem_rootsOfUnity']
        exact hpow a i⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hcoord : ∀ i : Fin m,
        tA a i.castSucc * (tA a (Fin.last m))⁻¹ =
          tA b i.castSucc * (tA b (Fin.last m))⁻¹ := fun i => by
      have h := congrFun hab i
      exact congrArg (fun z : ↥(rootsOfUnity p K) => ((z : Kˣ) : K)) h
    have hn : (fun k : Fin (m + 1) => tA a k * (tA a (Fin.last m))⁻¹) =
        (fun k : Fin (m + 1) => tA b k * (tA b (Fin.last m))⁻¹) := by
      funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
      · exact hcoord i
      · rw [mul_inv_cancel₀ (hne a _), mul_inv_cancel₀ (hne b _)]
    have ha := actsDiagU_mul_const (htA a) (inv_ne_zero (hne a (Fin.last m)))
    have hb := actsDiagU_mul_const (htA b) (inv_ne_zero (hne b (Fin.last m)))
    apply Subtype.ext
    exact actsDiagU_unique hM.surj (hn ▸ ha) hb
  calc
    Nat.card A ≤ Nat.card (Fin m → ↥(rootsOfUnity p K)) :=
      Nat.card_le_card_of_injective g hg
    _ = Nat.card (↥(rootsOfUnity p K)) ^ m := by rw [Nat.card_fun, Nat.card_fin]
    _ ≤ p ^ m := Nat.pow_le_pow_left (card_rootsOfUnity K p) m
    _ = p ^ (m + 1 - 1) := by rw [Nat.add_sub_cancel]


section Diag

theorem exists_diagSU (hK : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) {u : Fin d → K}
    (hu : ∀ i, u i ^ p = 1) (hprod : ∏ i, u i = 1) :
    ∃ D : ↥(unitarySU 2 n K d), ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact Nat.succ_ne_zero _ (Nat.eq_zero_of_zero_dvd hpq)
  have hu0 : ∀ i, u i ≠ 0 := fun i h0 => by
    have := hu i
    rw [h0, zero_pow hp0] at this
    exact zero_ne_one this
  set t : Fin d → Kˣ := fun i => Units.mk0 (u i) (hu0 i) with ht
  have htp : ∀ i, t i ^ p = 1 := fun i => Units.ext (by
    simp only [ht, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hu i)
  have htq : ∀ k, t k ^ (2 ^ n + 1) = 1 := by
    intro k
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, htp k, one_pow]
  have htprod : ∏ k, t k = 1 := Units.ext (by
    simp only [ht, Units.coe_prod, Units.val_mk0, Units.val_one]
    exact hprod)
  exact ⟨⟨diagHom d t, TableBUE.diagHom_mem_unitarySU hK htq htprod⟩, by
    simp only [coe_diagHom, ht, Units.val_mk0]⟩

theorem projMk_eq_one_iff (hd : 0 < d) {x : ↥(unitarySU 2 n K d)} :
    LargeEvenProjMk (unitarySU 2 n K d) x = 1 ↔
      ∃ c : K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c := by
  have key : LargeEvenProjMk (unitarySU 2 n K d) x = 1 ↔ x ∈ (LargeEvenProjMk
      (unitarySU 2 n K d)).ker := MonoidHom.mem_ker.symm
  rw [key, LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(u : K), ?_⟩
    rw [← hu]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      have := diag_ne_zero_of_eq (t := fun _ => c) hc ⟨0, hd⟩
      exact this
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc, Matrix.scalar_apply]
    rfl

end Diag

section Scalar

variable {φ : ↥(unitarySU 2 n K d) →* L'}

theorem scalar_of_map_conj_eq [Finite K] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 4 ≤ d) {g : ↥(unitarySU 2 n K d)} (h : ∀ y, φ (g * y * g⁻¹) = φ y) :
    ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by omega) hdq
  set q := LargeEvenProjMk (unitarySU 2 n K d) with hq
  have hmem : q g ∈ Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : φ (g * y * g⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_inv, h y, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hM.ker _ h1
    have h2 : q (g * y * g⁻¹ * y⁻¹) = 1 := (projMk_eq_one_iff (by omega)).mpr ⟨c, hc⟩
    have h3 : q (g * y) = q (y * g) := by
      have e : g * y = (g * y * g⁻¹ * y⁻¹) * (y * g) := by group
      rw [e, map_mul, h2, one_mul]
    change q y * q g = q g * q y
    rw [← map_mul, ← map_mul, h3]
  rw [hZ, Subgroup.mem_bot] at hmem
  exact (projMk_eq_one_iff (by omega)).mp hmem

end Scalar

section Perm

variable {φ : ↥(unitarySU 2 n K d) →* L'}

theorem eq_one_of_conj_perm (hM : Model φ) (hd : 3 ≤ d) {b : MulAut L'} {t : Fin d → K}
    (hb : ActsDiagU φ b t)
    (hfix : ∀ σ : Equiv.Perm (Fin d), MulAut.conj (φ (permSU hM.field σ)) * b *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = b) : b = 1 := by
  refine hb.eq_one_of_const hM.surj ⟨0, by omega⟩ fun i j => ?_
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hki, hkj⟩ := exists_not_mem_two hd i j
  have h1 := hb.conj_perm hM.field (Equiv.swap i j)
  rw [hfix] at h1
  have h2 := hb.ratio_eq hM.field hd hM.ker h1 k i
  simp only [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hki hkj, Equiv.swap_apply_left] at h2
  exact inv_inj.mp (mul_left_cancel₀ (hb.ne_zero k) h2)

end Perm

end CFSG.StandardType.UnitTB

end

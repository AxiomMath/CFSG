module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Short
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open ProofKS1623Parab
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem lev_mulVec (A : SpecialLinearGroup (Fin 2) F) (v : Fin 3 → F) (hv : v 2 = 0) :
    (lev F A).val *ᵥ v = ![(A.val *ᵥ ![v 0, v 1]) 0, (A.val *ᵥ ![v 0, v 1]) 1, 0] := by
  ext i
  fin_cases i <;> simp [lev_val, levMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_two, hv]

theorem invariant_subspace_parK {Y : Submodule F (Fin 3 → F)}
    (hY : ∀ g ∈ parK F, ∀ v ∈ Y, g.val *ᵥ v ∈ Y) :
    Y = ⊥ ∨ Y = flagSpace 3 F 2 ∨ Y = ⊤ := by
  by_cases h : ∃ y ∈ Y, y 2 ≠ 0
  · right; right
    obtain ⟨y, hyY, hy2⟩ := h
    have hmv : ∀ w : Fin 2 → F,
        (uVec w).val *ᵥ y = ![y 0 + w 0 * y 2, y 1 + w 1 * y 2, y 2] := by
      intro w
      ext i
      fin_cases i <;> simp [uVec, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hdiff : ∀ w : Fin 2 → F, ![y 2 * w 0, y 2 * w 1, 0] ∈ Y := by
      intro w
      have h1 := Y.sub_mem (hY _ (radU_le_parK (uVec_mem_radU w)) y hyY) hyY
      rw [hmv] at h1
      convert h1 using 1
      ext i
      fin_cases i <;> simp <;> ring
    have he0 : (![1, 0, 0] : Fin 3 → F) ∈ Y := by
      have := Y.smul_mem (y 2)⁻¹ (hdiff ![1, 0])
      convert this using 1
      ext i
      fin_cases i <;> simp [hy2]
    have he1 : (![0, 1, 0] : Fin 3 → F) ∈ Y := by
      have := Y.smul_mem (y 2)⁻¹ (hdiff ![0, 1])
      convert this using 1
      ext i
      fin_cases i <;> simp [hy2]
    have he2 : (![0, 0, 1] : Fin 3 → F) ∈ Y := by
      have := Y.smul_mem (y 2)⁻¹
        (Y.sub_mem (Y.sub_mem hyY (Y.smul_mem (y 0) he0)) (Y.smul_mem (y 1) he1))
      convert this using 1
      ext i
      fin_cases i
      · show (0 : F) = (y 2)⁻¹ * (y 0 - y 0 * 1 - y 1 * 0)
        ring
      · show (0 : F) = (y 2)⁻¹ * (y 1 - y 0 * 0 - y 1 * 1)
        ring
      · show (1 : F) = (y 2)⁻¹ * (y 2 - y 0 * 0 - y 1 * 0)
        rw [mul_zero, mul_zero, sub_zero, sub_zero, inv_mul_cancel₀ hy2]
    rw [eq_top_iff]
    intro v _
    have : v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
      ext i
      fin_cases i <;> simp
    rw [this]
    exact Y.add_mem (Y.add_mem (Y.smul_mem _ he0) (Y.smul_mem _ he1)) (Y.smul_mem _ he2)
  · push Not at h
    have hYW : Y ≤ flagSpace 3 F 2 := fun y hy => mem_flagSpace_two.mpr (h y hy)
    by_cases hbot : Y = ⊥
    · exact Or.inl hbot
    right; left
    apply le_antisymm hYW
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hy2 := h y hyY
    have hy' : (![y 0, y 1] : Fin 2 → F) ≠ 0 := by
      intro h0
      apply hy0
      ext i
      fin_cases i
      · exact congrFun h0 0
      · exact congrFun h0 1
      · exact hy2
    intro w hw
    have hw2 := mem_flagSpace_two.mp hw
    by_cases hw0 : (![w 0, w 1] : Fin 2 → F) = 0
    · have : w = 0 := by
        ext i
        fin_cases i
        · exact congrFun hw0 0
        · exact congrFun hw0 1
        · exact hw2
      rw [this]
      exact Y.zero_mem
    obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq hy' hw0
    have h1 := hY _ (lev_mem_parK A) y hyY
    rw [lev_mulVec A y hy2, hA] at h1
    convert h1 using 1
    ext i
    fin_cases i <;> simp [hw2]

@[expose] def fixVec {n : ℕ} (X : Subgroup (SpecialLinearGroup (Fin n) F)) :
    Submodule F (Fin n → F) where
  carrier := {v | ∀ x ∈ X, x.val *ᵥ v = v}
  add_mem' {a b} ha hb x hx := by rw [mulVec_add, ha x hx, hb x hx]
  zero_mem' x _ := by rw [mulVec_zero]
  smul_mem' c v hv x hx := by rw [mulVec_smul, hv x hx]

theorem smul_vec_eq' {n : ℕ} (x : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    x • v = (x : Matrix (Fin n) (Fin n) F) *ᵥ v :=
  Matrix.smul_eq_mulVec _ _

theorem exists_ne_zero_mem_fixVec [Finite F] [CharP F 2] {n : ℕ} (hn : n ≠ 0)
    {X : Subgroup (SpecialLinearGroup (Fin n) F)} (hX : IsPGroup 2 X) :
    ∃ v ∈ fixVec X, v ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hdvd : 2 ∣ Nat.card (Fin n → F) := by
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk, ← pow_mul]
    exact dvd_pow_self 2 (Nat.mul_ne_zero k.ne_zero hn)
  obtain ⟨b, hb, hne⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Fin n → F) hdvd (a := 0) (fun x => smul_zero (x : SpecialLinearGroup (Fin n) F))
  refine ⟨b, fun x hx => ?_, fun h => hne h.symm⟩
  have := hb ⟨x, hx⟩
  rwa [Subgroup.mk_smul, smul_vec_eq'] at this

theorem mulVec_mem_fixVec {n : ℕ} {X : Subgroup (SpecialLinearGroup (Fin n) F)}
    {g : SpecialLinearGroup (Fin n) F} (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {v : Fin n → F}
    (hv : v ∈ fixVec X) : g.val *ᵥ v ∈ fixVec X := by
  intro x hx
  have h2 : g * (g⁻¹ * x * g) = x * g := by group
  have h3 : x.val *ᵥ (g.val *ᵥ v) = g.val *ᵥ ((g⁻¹ * x * g).val *ᵥ v) := by
    rw [mulVec_mulVec, mulVec_mulVec, show x.val * g.val = (x * g).val from rfl, ← h2]
    rfl
  rw [h3, hv _ (hg x hx)]

theorem mem_radU_of_fix {g : SpecialLinearGroup (Fin 3) F}
    (hg : ∀ w ∈ flagSpace 3 F 2, g.val *ᵥ w = w) : g ∈ radU F (flagSpace 3 F 2) := by
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  have he1 : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  have h0 := hg _ he0
  have h1 := hg _ he1
  have c00 := congrFun h0 0
  have c10 := congrFun h0 1
  have c20 := congrFun h0 2
  have c01 := congrFun h1 0
  have c11 := congrFun h1 1
  have c21 := congrFun h1 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at c00 c10 c20 c01 c11 c21
  have hdet := g.prop
  rw [Matrix.det_fin_three, c00, c10, c20, c01, c11, c21] at hdet
  have c22 : g.val 2 2 = 1 := by linear_combination hdet
  exact mem_radU_two_iff.mpr ⟨c00, c01, c10, c11, c20, c21, c22⟩

theorem eq_one_of_forall_mulVec' {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : ∀ v, M *ᵥ v = v) :
    M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem three_dvd_one_add_two_pow (k : ℕ) : 3 ∣ 1 + 2 ^ (2 * k + 1) := by
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

theorem exists_two_lift {h : SpecialLinearGroup (Fin 3) F} {k : ℕ}
    (hk : proj 3 F h ^ 2 ^ k = 1) :
    ∃ h' : SpecialLinearGroup (Fin 3) F, proj 3 F h' = proj 3 F h ∧ h' ^ 2 ^ k = 1 := by
  rw [← map_pow, proj_eq_one_iff] at hk
  obtain ⟨c, hc3, hcz⟩ := mem_scalars.mp hk
  set ν : Fˣ := c ^ 2 ^ (k + 1) with hν
  have hν3 : ν ^ 3 = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  refine ⟨h * scalarElement ν hν3, ?_, ?_⟩
  · rw [map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars ν hν3), mul_one]
  · have hcomm : Commute h (scalarElement (n := 3) ν hν3) :=
      ((Subgroup.mem_center_iff.mp ((scalars_eq_center 3 F) ▸
        scalarElement_mem_scalars ν hν3)) h)
    rw [hcomm.mul_pow]
    apply Subtype.ext
    rw [show (h ^ 2 ^ k * scalarElement ν hν3 ^ 2 ^ k).val =
        (h ^ 2 ^ k).val * (scalarElement ν hν3).val ^ 2 ^ k from rfl, hcz, coe_scalarElement,
      ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hν, ← pow_mul,
      ← pow_succ']
    obtain ⟨r, hr⟩ := three_dvd_one_add_two_pow k
    rw [show 2 ^ (k + 1) * 2 ^ k + 1 = 1 + 2 ^ (2 * k + 1) by ring, hr, pow_mul, hc3, one_pow,
      Units.val_one, map_one]
    rfl

theorem exists_two_lift_subgroup [Finite F] {R : Subgroup (projectiveSL 3 F)}
    (hR : IsPGroup 2 R) :
    ∃ S : Subgroup (SpecialLinearGroup (Fin 3) F), IsPGroup 2 S ∧ S.map (proj 3 F) = R ∧
      ∀ g, proj 3 F g ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)) →
        ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rh := R.comap (proj 3 F) with hRh
  set f : Rh →* R := (proj 3 F).subgroupComap R with hf
  have hker : f.ker ≤ Subgroup.center Rh := by
    intro x hx
    have hx1 : proj 3 F x.1 = 1 := congrArg Subtype.val hx
    have hxz : x.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) :=
      (scalars_eq_center 3 F) ▸ proj_eq_one_iff.mp hx1
    rw [Subgroup.mem_center_iff] at hxz ⊢
    intro y
    exact Subtype.ext (hxz y.1)
  have : Group.IsNilpotent R := hR.isNilpotent
  have hnil : Group.IsNilpotent Rh := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨S⟩ : Nonempty (Sylow 2 Rh) := inferInstance
  have hSn := hnil.sylow_normal 2 S
  have huniq := Sylow.unique_of_normal S hSn
  set S' := (S : Subgroup Rh).map Rh.subtype with hS'
  have h2el : ∀ h ∈ Rh, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ S' := by
    intro h hh k hk
    have hP : IsPGroup 2 (Subgroup.zpowers (⟨h, hh⟩ : Rh)) := by
      rintro ⟨y, hy⟩
      refine ⟨k, Subtype.ext ?_⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk' : (⟨h, hh⟩ : Rh) ^ 2 ^ k = 1 := Subtype.ext hk
      show ((⟨h, hh⟩ : Rh) ^ n) ^ 2 ^ k = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk',
        _root_.one_zpow]
    obtain ⟨P, hP'⟩ := hP.exists_le_sylow
    have hPS : P = S := Subsingleton.elim P S
    exact ⟨⟨h, hh⟩, hPS ▸ hP' (Subgroup.mem_zpowers _), rfl⟩
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'Rh : S' ≤ Rh := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  refine ⟨S', hS'2, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      exact s.2
    · intro x hx
      obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
      obtain ⟨h, rfl⟩ := proj_surjective 3 F x
      have hk' : proj 3 F h ^ 2 ^ k = 1 := congrArg Subtype.val hk
      obtain ⟨h', hh', hh'k⟩ := exists_two_lift hk'
      have hh'R : h' ∈ Rh := by
        show proj 3 F h' ∈ R
        rw [hh']
        exact hx
      exact ⟨h', h2el h' hh'R k hh'k, hh'⟩
  · intro g hg s hs
    have hgs : g * s * g⁻¹ ∈ Rh := by
      show proj 3 F (g * s * g⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp (hS'Rh hs)
    obtain ⟨k, hk⟩ := hS'2 ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine h2el _ hgs k ?_
    rw [conj_pow, hk', mul_one, mul_inv_cancel]

theorem le_radV_of_isPGroup [Finite F] [CharP F 2] {R : Subgroup (projectiveSL 3 F)}
    (hR : IsPGroup 2 R) (hN : parB F ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F))) :
    R ≤ radV F := by
  obtain ⟨S', hS'2, hS'R, hSK⟩ := exists_two_lift_subgroup hR
  obtain ⟨v, hvC, hv0⟩ := exists_ne_zero_mem_fixVec (by norm_num) hS'2
  have hCinv : ∀ g ∈ parK F, ∀ w ∈ fixVec S', g.val *ᵥ w ∈ fixVec S' := by
    intro g hg w hw
    refine mulVec_mem_fixVec (fun x hx => ?_) hw
    have := hSK g⁻¹ (hN ⟨g⁻¹, inv_mem hg, rfl⟩) x hx
    rwa [inv_inv] at this
  rcases invariant_subspace_parK hCinv with hC0 | hCW | hCtop
  · exfalso
    rw [hC0] at hvC
    exact hv0 ((Submodule.mem_bot F).mp hvC)
  · have hS'U : S' ≤ radU F (flagSpace 3 F 2) := fun s hs =>
      mem_radU_of_fix fun w hw => (hCW ▸ hw : w ∈ fixVec S') s hs
    rw [← hS'R]
    exact Subgroup.map_mono hS'U
  · have hS'1 : S' ≤ ⊥ := by
      intro s hs
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      exact eq_one_of_forall_mulVec' fun w =>
        (show w ∈ fixVec S' by rw [hCtop]; exact Submodule.mem_top) s hs
    rw [← hS'R]
    exact (Subgroup.map_mono hS'1).trans (by rw [Subgroup.map_bot]; exact bot_le)

theorem transvection_mem_radU {i : Fin 3} (hi : i ≠ 2) (c : F) :
    SpecialLinearGroup.transvection hi c ∈ radU F (flagSpace 3 F 2) := by
  rw [mem_radU_two_iff]
  fin_cases i
  · simp [SpecialLinearGroup.transvection_coe]
  · simp [SpecialLinearGroup.transvection_coe]
  · exact absurd rfl hi

theorem transvection_eq_lev {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2) (c : F) :
    ∃ A : SpecialLinearGroup (Fin 2) F, lev F A = SpecialLinearGroup.transvection hij c := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact absurd rfl hi
    | exact absurd rfl hj
    | skip
  · refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c, ?_⟩
    apply Subtype.ext
    rw [lev_val]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [levMat, SpecialLinearGroup.transvection_coe]
  · refine ⟨SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c, ?_⟩
    apply Subtype.ext
    rw [lev_val]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [levMat, SpecialLinearGroup.transvection_coe]

@[expose] def swapTwo (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination -h2⟩

theorem swap_conj_transvection [CharP F 2] (c : F) :
    lev F (swapTwo F) * SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c *
      (lev F (swapTwo F))⁻¹ =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c := by
  have hsq : lev F (swapTwo F) * lev F (swapTwo F) = 1 := by
    rw [← map_mul]
    have : swapTwo F * swapTwo F = 1 := by
      apply Subtype.ext
      show !![(0 : F), 1; 1, 0] * !![0, 1; 1, 0] = 1
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, map_one]
  have hinv : (lev F (swapTwo F))⁻¹ = lev F (swapTwo F) :=
    inv_eq_of_mul_eq_one_right hsq
  rw [hinv]
  apply Subtype.ext
  show (lev F (swapTwo F)).val * (1 + Matrix.single 2 1 c) * (lev F (swapTwo F)).val =
    1 + Matrix.single 2 0 c
  rw [lev_val]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;>
    simp [levMat, swapTwo]

theorem exists_parK_row_zero {a b : F} (c : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ k ∈ parK F, k.val 0 0 = a ∧ k.val 0 1 = b ∧ k.val 0 2 = c := by
  rcases hab with ha | hb
  · refine ⟨⟨!![a, b, c; 0, a⁻¹, 0; 0, 0, 1], ?_⟩, mem_parK.mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp [Matrix.det_fin_three, ha]
  · refine ⟨⟨!![a, b, c; -b⁻¹, 0, 0; 0, 0, 1], ?_⟩, mem_parK.mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp [Matrix.det_fin_three, hb]

theorem transvection_two_zero_mulVec (c : F) {v : Fin 3 → F} (hv : v 0 = 0) :
    (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c).val *ᵥ v = v := by
  ext i
  fin_cases i <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hv]

theorem eq_top_of_parK_le [CharP F 2] {Z : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hKZ : parK F ≤ Z) {h : SpecialLinearGroup (Fin 3) F} (hhZ : h ∈ Z)
    (hh : h ∉ stabilizer (flagSpace 3 F 2)) : Z = ⊤ := by
  have hrow : h.val 2 0 ≠ 0 ∨ h.val 2 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hh
    rw [mem_stabilizer_flagSpace_iff]
    intro i j hi hj
    have hi2 : i = 2 := by
      ext
      have := i.2
      simp only [Fin.val_two]
      omega
    subst hi2
    fin_cases j
    · exact hcon.1
    · exact hcon.2
    · exact absurd hj (by decide)
  obtain ⟨k, hk, hk0, hk1, hk2⟩ := exists_parK_row_zero (h.val 2 2) hrow
  set g := k * h⁻¹ with hg
  have hgZ : g ∈ Z := mul_mem (hKZ hk) (inv_mem hhZ)
  have key : ∀ j, g.val 0 j = (h * h⁻¹).val 2 j := by
    intro j
    show (k.val * (h⁻¹).val) 0 j = (h.val * (h⁻¹).val) 2 j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, hk0, hk1, hk2]
  rw [mul_inv_cancel] at key
  have hg0 : g.val 0 0 = 0 := by rw [key]; rfl
  have hg1 : g.val 0 1 = 0 := by rw [key]; rfl
  have hT20 : ∀ c : F,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ Z := by
    intro c
    set T := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c with hT
    have hu : g⁻¹ * T * g ∈ radU F (flagSpace 3 F 2) := by
      refine mem_radU_of_fix fun w hw => ?_
      have hw2 := mem_flagSpace_two.mp hw
      have hgw : (g.val *ᵥ w) 0 = 0 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hg0, hg1, hw2]
      have h1 : (g⁻¹ * T * g).val = (g⁻¹).val * T.val * g.val := rfl
      have h2 : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
      rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, transvection_two_zero_mulVec c hgw,
        Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have : T = g * (g⁻¹ * T * g) * g⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hgZ (hKZ (radU_le_parK hu))) (inv_mem hgZ)
  have hT21 : ∀ c : F,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ Z := by
    intro c
    have hs := hKZ (lev_mem_parK (swapTwo F))
    have h1 := swap_conj_transvection (F := F) c
    have : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c =
        (lev F (swapTwo F))⁻¹ *
          SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c *
          lev F (swapTwo F) := by
      rw [← h1]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs) (hT20 c)) hs
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  by_cases hj : j = 2
  · subst hj
    exact hKZ (radU_le_parK (transvection_mem_radU (by simpa using hij) c))
  by_cases hi : i = 2
  · subst hi
    fin_cases j
    · exact hT20 c
    · exact hT21 c
    · exact absurd rfl hj
  · obtain ⟨A, hA⟩ := transvection_eq_lev hij hi hj c
    rw [← hA]
    exact hKZ (lev_mem_parK A)

theorem le_stabilizer_of_le [CharP F 2] {Y : Subgroup (projectiveSL 3 F)} (hKY : parB F ≤ Y)
    (hY : Y ≠ ⊤) : Y ≤ (stabilizer (flagSpace 3 F 2)).map (proj 3 F) := by
  intro y hy
  obtain ⟨h, rfl⟩ := proj_surjective 3 F y
  by_contra hcon
  apply hY
  have hh : h ∉ stabilizer (flagSpace 3 F 2) := fun hs => hcon ⟨h, hs, rfl⟩
  have hZ : Y.comap (proj 3 F) = ⊤ :=
    eq_top_of_parK_le (fun k hk => hKY ⟨k, hk, rfl⟩) hy hh
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  have : g ∈ Y.comap (proj 3 F) := hZ ▸ Subgroup.mem_top g
  exact this

theorem perfectResidual_eq_of_le [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {Y : Subgroup (projectiveSL 3 F)} (hKY : parB F ≤ Y) (hY : Y ≠ ⊤) :
    inSubgroup perfectResidual Y = parB F := by
  apply le_antisymm
  · exact (Sec18.inSubgroup_perfectResidual_mono (le_stabilizer_of_le hKY hY)).trans
      (perfectResidual_stabilizer_eq hF4).le
  · exact CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
      hKY (isPerfect_parB hF4)

end ProofKS1624KP1

end CFSG.RankThree.PartTwo.Sec16

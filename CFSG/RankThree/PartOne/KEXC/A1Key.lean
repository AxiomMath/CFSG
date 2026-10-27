module

public import CFSG.RankThree.PartOne.KLR.A1Twist
public import CFSG.RankThree.PartOne.KEXC.BTSL2
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one conjSL_mul)


theorem eq_one_of_commute_uSL_vSL {L : Type*} [Field L] [CharP L 2] {Y : SL2 L}
    (hu : uSL 1 * Y = Y * uSL 1) (hv : vSL 1 * Y = Y * vSL 1) : Y = 1 := by
  have hum := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hu
  have hvm := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hum hvm
  rw [coe_uSL] at hum
  rw [coe_vSL] at hvm
  have hscal := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute (Y : Matrix (Fin 2) (Fin 2) L)
    hum.symm hvm.symm
  have hdet : (Y : Matrix (Fin 2) (Fin 2) L).det = 1 := Y.2
  have h1 : (Y : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    rw [hscal] at hdet
    simp [Matrix.scalar_apply] at hdet
    rcases hdet with h | h
    · exact h
    · rw [h]
      exact CharTwo.neg_eq 1
  refine Subtype.ext ?_
  rw [hscal, h1]
  simp

theorem mem_fixed_swap_iff {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) (φ : G → G)
    (hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, φ (x * y) = φ x * φ y)
    (hφA : ∀ a ∈ A, φ a ∈ B) (hφB : ∀ b ∈ B, φ b ∈ A)
    (X : Subgroup G) (hX : ∀ a, a ∈ X ↔ a ∈ A ∧ φ (φ a) = a)
    (P : Subgroup G) (hP : ∀ g, g ∈ P ↔ g ∈ A ⊔ B ∧ φ g = g) :
    ∀ g, g ∈ P ↔ ∃ x ∈ X, g = x * φ x := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, b * a = a * b := fun a ha b hb => (hAB a ha b hb).symm
  intro g
  rw [hP g]
  constructor
  · rintro ⟨hgAB, hgφ⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hgAB
    have h1 : φ (a * b) = φ a * φ b := hmul _ (hAle ha) _ (hBle hb)
    have hφa : φ a ∈ B := hφA _ ha
    have hφb : φ b ∈ A := hφB _ hb
    rw [h1] at hgφ
    have h2 : a * b = φ b * φ a := by
      rw [← hgφ]
      exact (hAB _ hφb _ hφa).symm
    obtain ⟨hab, hbφ⟩ := mul_inj_of_disjoint hdisj ha hφb hb hφa h2
    have hxX : a ∈ X := (hX a).2 ⟨ha, by rw [← hbφ, hab]⟩
    exact ⟨a, hxX, by rw [hbφ]⟩
  · rintro ⟨x, hxX, rfl⟩
    have hxA : x ∈ A := ((hX x).1 hxX).1
    have hxφ : φ (φ x) = x := ((hX x).1 hxX).2
    have hφx : φ x ∈ B := hφA _ hxA
    refine ⟨(A ⊔ B).mul_mem (hAle hxA) (hBle hφx), ?_⟩
    rw [hmul _ (hAle hxA) _ (hBle hφx), hxφ]
    exact hcomm _ hxA _ hφx

section A1Struct

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

theorem a1_exists_struct (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    ∃ f : SL2 K →* ModGL ReeTag.F4.tag L, Function.Injective f ∧
      (∀ B, f B ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1)) ∧
      (∀ x, (x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ∧
        twistMap D.F n' (twistMap D.F n' x) = x) ↔ x ∈ f.range) ∧
      (∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
          twistedFixed D.F n' ↔ ∃ B : SL2 K, g = f B * twistMap D.F n' (f B)) ∧
      (∀ Y ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1),
        (∀ B, Y * f B = f B * Y) → Y = 1) := by
  classical
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  set A := rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) with hA
  set B := rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) with hB
  have hABle : A ⊔ B ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B,
      twistMap D.F n' (x * y) = twistMap D.F n' x * twistMap D.F n' y :=
    fun x hx y hy => twistMap_mul n' (hABle hx) (hABle hy)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  obtain ⟨P₀, hX⟩ := h.exists_twist D hK hn' hperm hstab
  have hρinj := rootSL2_injective_of_field (K := L) (τ := ReeTag.F4.tag) (Pi.single i 1)
  have hρadj : ∀ B₀ : SL2 L,
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) B₀ ∈ adjointGroup ReeTag.F4.tag L := fun B₀ =>
    (hABle (Subgroup.mem_sup_left ⟨B₀, rfl⟩))
  have hSLinj :
      Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A₀ B₀ hAB₀
    ext i₀ j₀
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
      (X : Matrix (Fin 2) (Fin 2) L) i₀ j₀) hAB₀
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hconjinj : Function.Injective (conjSL P₀) := fun A₀ B₀ hAB₀ => by
    have h1 := congrArg (conjSL P₀⁻¹) hAB₀
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let f : SL2 K →* ModGL ReeTag.F4.tag L :=
    (rootSL2 ReeTag.F4.tag L (Pi.single i 1)).comp
      ((conjSL P₀).comp (Matrix.SpecialLinearGroup.map (algebraMap K L)))
  have hf : ∀ B₀, f B₀ = rootSL2 ReeTag.F4.tag L (Pi.single i 1)
      (conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap K L) B₀)) := fun _ => rfl
  have hfinj : Function.Injective f := hρinj.comp (hconjinj.comp hSLinj)
  have hXmem : ∀ x, (x ∈ A ∧ twistMap D.F n' (twistMap D.F n' x) = x) ↔ x ∈ f.range := by
    intro x
    constructor
    · rintro ⟨⟨B₀, rfl⟩, hfix⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)] at hfix
      have hB₀ := (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).1 hfix
      obtain ⟨B₁, hB₁, rfl⟩ := hB₀
      obtain ⟨B₂, rfl⟩ := hB₁
      exact ⟨B₂, rfl⟩
    · rintro ⟨B₂, rfl⟩
      refine ⟨⟨_, rfl⟩, ?_⟩
      rw [hf, twistMap_twistMap D hn' (hρadj _)]
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX _).2 ⟨_, ⟨B₂, rfl⟩, rfl⟩
  have hPmem : ∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n' ↔ g ∈ A ⊔ B ∧ twistMap D.F n' g = g := by
    intro g
    rw [hspan]
    constructor
    · rintro ⟨hg, -, hfix⟩
      exact ⟨hg, hfix⟩
    · rintro ⟨hg, hfix⟩
      exact ⟨hg, hABle hg, hfix⟩
  have hfixed := mem_fixed_swap_iff hAB hdisj (twistMap D.F n') hmul hφA hφB f.range
    (fun x => (hXmem x).symm) _ (fun g => (hPmem g))
  refine ⟨f, hfinj, fun B₀ => ⟨_, rfl⟩, hXmem, ?_, ?_⟩
  · intro g
    rw [hfixed g]
    constructor
    · rintro ⟨x, ⟨B₀, rfl⟩, hg⟩
      exact ⟨B₀, hg⟩
    · rintro ⟨B₀, hg⟩
      exact ⟨f B₀, ⟨B₀, rfl⟩, hg⟩
  · rintro Y ⟨Y₀, rfl⟩ hY
    set ρ := rootSL2 ReeTag.F4.tag L (Pi.single i 1) with hρ
    have hcomm : ∀ B₀ : SL2 K, Y₀ * conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap K L) B₀) =
        conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap K L) B₀) * Y₀ := fun B₀ =>
      hρinj (by rw [map_mul, map_mul]; exact hY B₀)
    have hZ : ∀ B₀ : SL2 K, conjSL P₀⁻¹ Y₀ * Matrix.SpecialLinearGroup.map (algebraMap K L) B₀ =
        Matrix.SpecialLinearGroup.map (algebraMap K L) B₀ * conjSL P₀⁻¹ Y₀ := by
      intro B₀
      apply hconjinj
      rw [map_mul, map_mul, ← conjSL_mul, mul_inv_cancel, conjSL_one]
      exact hcomm B₀
    have hu := hZ (uSL 1)
    have hv := hZ (vSL 1)
    rw [KLR.map_uSL, map_one] at hu
    rw [KLR.map_vSL, map_one] at hv
    have hZ1 := eq_one_of_commute_uSL_vSL hu.symm hv.symm
    have hY1 : Y₀ = 1 := by
      have := congrArg (conjSL P₀) hZ1
      rwa [← conjSL_mul, mul_inv_cancel, conjSL_one, map_one] at this
    rw [hY1, map_one]


omit [CharP L 2] [Finite K] [Algebra K L] [IsAlgClosed L] in
theorem twistMap_eq_one {n g : ModGL ReeTag.F4.tag L} {F : MulAut (adjointGroup ReeTag.F4.tag L)}
    (hg : g ∈ adjointGroup ReeTag.F4.tag L) (h : twistMap F n g = 1) : g = 1 := by
  have h1 : Fext F g = 1 := by
    have : n⁻¹ * (n * Fext F g * n⁻¹) * n = Fext F g := by group
    rw [← this]
    unfold twistMap at h
    rw [h]
    group
  rw [Fext_of_mem F hg] at h1
  have h2 : F ⟨g, hg⟩ = 1 := Subtype.ext h1
  have h3 : (⟨g, hg⟩ : adjointGroup ReeTag.F4.tag L) = 1 := (map_eq_one_iff F F.injective).1 h2
  exact congrArg Subtype.val h3

theorem conj_prod_of_comm {G : Type*} [Group G] {a b x y : G} (hbx : b * x = x * b)
    (hay : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a) :
    (a * b) * (x * y) * (a * b)⁻¹ = (a * x * a⁻¹) * (b * y * b⁻¹) := by
  calc (a * b) * (x * y) * (a * b)⁻¹ = a * (b * x) * (y * b⁻¹ * a⁻¹) := by group
    _ = a * (x * b) * (y * b⁻¹ * a⁻¹) := by rw [hbx]
    _ = a * x * (b * y * b⁻¹) * a⁻¹ := by group
    _ = a * x * a⁻¹ * (a * (b * y * b⁻¹) * a⁻¹) := by group
    _ = a * x * a⁻¹ * ((b * y * b⁻¹) * a * a⁻¹) := by rw [hay]
    _ = (a * x * a⁻¹) * (b * y * b⁻¹) := by group

theorem a1_centralizer_trivial (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    {y : ModGL ReeTag.F4.tag L}
    (hy : y ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))))
    (hcomm : ∀ g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      twistedFixed D.F n', y * g = g * y) : y = 1 := by
  classical
  obtain ⟨f, hfinj, hfA, hXmem, hPdesc, hCtriv⟩ := a1_exists_struct D h hK hn' hperm hstab
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  rw [hspan] at hy
  obtain ⟨yA, hyA, yB, hyB, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hy
  have hABle : rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hadjA : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1),
      x ∈ adjointGroup ReeTag.F4.tag L := fun x hx => hABle (Subgroup.mem_sup_left hx)
  have hadjB : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1),
      x ∈ adjointGroup ReeTag.F4.tag L := fun x hx => hABle (Subgroup.mem_sup_right hx)
  have key : ∀ B₀ : SL2 K, yA * f B₀ = f B₀ * yA ∧
      yB * twistMap D.F n' (f B₀) = twistMap D.F n' (f B₀) * yB := by
    intro B₀
    have hxA := hfA B₀
    have hφx := hφA _ hxA
    have hgP : f B₀ * twistMap D.F n' (f B₀) ∈ rootSpan ReeTag.F4.tag L (parabolicRoots
        ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
          Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n' :=
      (hPdesc _).2 ⟨B₀, rfl⟩
    have hg := hcomm _ hgP
    have e1 : (yA * f B₀ * yA⁻¹) * (yB * twistMap D.F n' (f B₀) * yB⁻¹) =
        f B₀ * twistMap D.F n' (f B₀) := by
      rw [← conj_prod_of_comm (hAB _ hxA _ hyB).symm
        (hAB _ hyA _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyB hφx) (inv_mem hyB)))]
      rw [mul_inv_eq_iff_eq_mul]
      exact hg
    have hX1 : yA * f B₀ * yA⁻¹ ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyA hxA) (inv_mem hyA)
    have hY1 : yB * twistMap D.F n' (f B₀) * yB⁻¹ ∈
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyB hφx) (inv_mem hyB)
    obtain ⟨h1, h2⟩ := mul_inj_of_disjoint hdisj hX1 hxA hY1 hφx e1
    exact ⟨by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1,
      by rw [mul_inv_eq_iff_eq_mul] at h2; exact h2⟩
  have hyA1 : yA = 1 := hCtriv yA hyA fun B₀ => (key B₀).1
  have hφyB : twistMap D.F n' yB = 1 := by
    have hφyBA : twistMap D.F n' yB ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) :=
      hφB _ hyB
    refine hCtriv _ hφyBA fun B₀ => ?_
    have hxA := hfA B₀
    have hφx := hφA _ hxA
    have hX : twistMap D.F n' (twistMap D.F n' (f B₀)) = f B₀ := ((hXmem _).2 ⟨B₀, rfl⟩).2
    have := congrArg (twistMap D.F n') (key B₀).2
    rw [twistMap_mul n' (hadjB _ hyB) (hadjB _ hφx), twistMap_mul n' (hadjB _ hφx) (hadjB _ hyB),
      hX] at this
    exact this
  have hyB1 : yB = 1 := twistMap_eq_one (hadjB _ hyB) hφyB
  rw [hyA1, hyB1, one_mul]


theorem HSL_mul_HSL {M : Type*} [Field M] (s t : Mˣ) : (HSL s : SL2 M) * HSL t = HSL (s * t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one_eq {M : Type*} [Field M] : (HSL (1 : Mˣ) : SL2 M) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem HSL_pow_eq {M : Type*} [Field M] (t : Mˣ) (n : ℕ) : (HSL t : SL2 M) ^ n = HSL (t ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HSL_one_eq]
  | succ n ih => rw [pow_succ, ih, HSL_mul_HSL, pow_succ]

theorem HSL_conj_uSL' {M : Type*} [Field M] (a : Mˣ) (c : M) :
    (HSL a : SL2 M) * uSL c * (HSL a)⁻¹ = uSL ((a : M) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, uSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_conj_vSL' {M : Type*} [Field M] (a : Mˣ) (c : M) :
    (HSL a : SL2 M) * vSL c * (HSL a)⁻¹ = vSL (((a⁻¹ : Mˣ) : M) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

omit [IsAlgClosed L] in
theorem rootDiagUnit_conj_rankOne (b : Fin ReeTag.F4.tag.rank → Lˣ) (k : Fin ReeTag.F4.tag.rank)
    (t : Lˣ) (ht : t ^ 2 = b k) (B₀ : SL2 L) :
    rootDiagUnit ReeTag.F4.tag b * rootSL2 ReeTag.F4.tag L (Pi.single k 1) B₀ *
        (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
      rootSL2 ReeTag.F4.tag L (Pi.single k 1) (HSL t * B₀ * (HSL t)⁻¹) := by
  have hk : IsRoot ReeTag.F4.tag (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) := isRoot_single _ k
  let f₁ : SL2 L →* ModGL ReeTag.F4.tag L :=
    (MulAut.conj (rootDiagUnit ReeTag.F4.tag b)).toMonoidHom.comp
      (rootSL2 ReeTag.F4.tag L (Pi.single k 1))
  let f₂ : SL2 L →* ModGL ReeTag.F4.tag L :=
    (rootSL2 ReeTag.F4.tag L (Pi.single k 1)).comp (MulAut.conj (HSL t)).toMonoidHom
  have hu : ∀ s, f₁ (uSL s) = f₂ (uSL s) := by
    intro s
    show rootDiagUnit ReeTag.F4.tag b * rootSL2 ReeTag.F4.tag L (Pi.single k 1) (uSL s) *
        (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
      rootSL2 ReeTag.F4.tag L (Pi.single k 1) (HSL t * uSL s * (HSL t)⁻¹)
    rw [rootSL2_uSL_charTwo, HSL_conj_uSL', rootSL2_uSL_charTwo,
      rootDiagUnit_conj_pinnedX b hk, CTTorus.rootChar_single, ← ht]
    simp [sq]
  have hv : ∀ s, f₁ (vSL s) = f₂ (vSL s) := by
    intro s
    show rootDiagUnit ReeTag.F4.tag b * rootSL2 ReeTag.F4.tag L (Pi.single k 1) (vSL s) *
        (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
      rootSL2 ReeTag.F4.tag L (Pi.single k 1) (HSL t * vSL s * (HSL t)⁻¹)
    rw [rootSL2_vSL_charTwo hk, HSL_conj_vSL', rootSL2_vSL_charTwo hk,
      rootDiagUnit_conj_pinnedX b (IsRoot.neg hk)]
    have h1 : rootChar b (-(Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) = (b k)⁻¹ := by
      rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul, CTTorus.rootChar_single]
    rw [h1, ← ht]
    simp [sq]
  exact DFunLike.congr_fun (hom_eq_of_uSL_vSL f₁ f₂ hu hv) B₀


theorem a1_key (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {R : Subgroup (ModGL ReeTag.F4.tag L)} (hR0 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRP : R ≤ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      twistedFixed D.F n')
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hbp : ∀ k, b k ^ p = 1)
    (hbfix : rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n')
    (hbN : rootDiagUnit ReeTag.F4.tag b ∈ Subgroup.normalizer (R : Set (ModGL ReeTag.F4.tag L)))
    (hnt : b i ≠ 1 ∨ b j ≠ 1) : False := by
  classical
  obtain ⟨f, hfinj, hfA, hXmem, hPdesc, hCtriv⟩ := a1_exists_struct D h hK hn' hperm hstab
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  have hABle : rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hmul : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1),
      ∀ y ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1),
      twistMap D.F n' (x * y) = twistMap D.F n' x * twistMap D.F n' y :=
    fun x hx y hy => twistMap_mul n' (hABle hx) (hABle hy)
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hsq : ∀ u : Lˣ, u ^ p = 1 → (u ^ (m + 1)) ^ 2 = u := by
    intro u hu
    rw [← pow_mul, show (m + 1) * 2 = p + 1 by omega, pow_succ, hu, one_mul]
  have hpw : ∀ u : Lˣ, u ^ p = 1 → (u ^ (m + 1)) ^ p = 1 := by
    intro u hu
    rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
  let ρA := rootSL2 ReeTag.F4.tag L (Pi.single i 1)
  let ρB := rootSL2 ReeTag.F4.tag L (Pi.single j 1)
  let δA : ModGL ReeTag.F4.tag L := ρA (HSL (b i ^ (m + 1)))
  let δB : ModGL ReeTag.F4.tag L := ρB (HSL (b j ^ (m + 1)))
  have hδAA : δA ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) := ⟨_, rfl⟩
  have hδBB : δB ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) := ⟨_, rfl⟩
  let δ : ModGL ReeTag.F4.tag L := δA * δB
  have hδmem : δ ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) :=
    mul_mem (Subgroup.mem_sup_left hδAA) (Subgroup.mem_sup_right hδBB)
  let e : ModGL ReeTag.F4.tag L := rootDiagUnit ReeTag.F4.tag b
  have hconjA : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1),
      e * x * e⁻¹ = δ * x * δ⁻¹ := by
    rintro _ ⟨B₀, rfl⟩
    have h1 := rootDiagUnit_conj_rankOne b i (b i ^ (m + 1)) (hsq _ (hbp i)) B₀
    have hc : ρA B₀ * δB = δB * ρA B₀ := hAB _ ⟨B₀, rfl⟩ _ hδBB
    have h2 : δB * ρA B₀ * δB⁻¹ = ρA B₀ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    calc e * ρA B₀ * e⁻¹ = ρA (HSL (b i ^ (m + 1)) * B₀ * (HSL (b i ^ (m + 1)))⁻¹) := h1
      _ = δA * ρA B₀ * δA⁻¹ := by simp only [δA, map_mul, map_inv]
      _ = δA * (δB * ρA B₀ * δB⁻¹) * δA⁻¹ := by rw [h2]
      _ = δ * ρA B₀ * δ⁻¹ := by simp only [δ]; group
  have hconjB : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1),
      e * x * e⁻¹ = δ * x * δ⁻¹ := by
    rintro _ ⟨B₀, rfl⟩
    have h1 := rootDiagUnit_conj_rankOne b j (b j ^ (m + 1)) (hsq _ (hbp j)) B₀
    have hBB : δB * ρB B₀ * δB⁻¹ ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) :=
      mul_mem (mul_mem hδBB ⟨B₀, rfl⟩) (inv_mem hδBB)
    have hc : δA * (δB * ρB B₀ * δB⁻¹) = (δB * ρB B₀ * δB⁻¹) * δA :=
      hAB _ hδAA _ hBB
    have h2 : δA * (δB * ρB B₀ * δB⁻¹) * δA⁻¹ = δB * ρB B₀ * δB⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    calc e * ρB B₀ * e⁻¹ = ρB (HSL (b j ^ (m + 1)) * B₀ * (HSL (b j ^ (m + 1)))⁻¹) := h1
      _ = δB * ρB B₀ * δB⁻¹ := by simp only [δB, map_mul, map_inv]
      _ = δA * (δB * ρB B₀ * δB⁻¹) * δA⁻¹ := h2.symm
      _ = δ * ρB B₀ * δ⁻¹ := by simp only [δ]; group
  have hconj : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1), e * x * e⁻¹ = δ * x * δ⁻¹ := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    have := MonoidHom.eqOn_closure (f := (MulAut.conj e).toMonoidHom)
      (g := (MulAut.conj δ).toMonoidHom)
      (s := ((rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) : Set (ModGL ReeTag.F4.tag L)) ∪
        (rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) : Set (ModGL ReeTag.F4.tag L))))
      (fun y hy => by
        rcases hy with hy | hy
        · exact hconjA y hy
        · exact hconjB y hy) hx
    exact this
  have hnormR : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1), (x ∈ R ↔ δ * x * δ⁻¹ ∈ R) := fun x hx => by
    rw [← hconj x hx]
    exact Subgroup.mem_normalizer_iff.1 hbN x
  have hφe : twistMap D.F n' e = e := hbfix.2
  have headj : e ∈ adjointGroup ReeTag.F4.tag L := hbfix.1
  have hδadj : δ ∈ adjointGroup ReeTag.F4.tag L := hABle hδmem
  have hδφ : twistMap D.F n' δ = δ := by
    have hφδmem : twistMap D.F n' δ ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) := by
      have : twistMap D.F n' δ = twistMap D.F n' δA * twistMap D.F n' δB :=
        twistMap_mul n' (hABle (Subgroup.mem_sup_left hδAA)) (hABle (Subgroup.mem_sup_right hδBB))
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right (hφA _ hδAA)) (Subgroup.mem_sup_left (hφB _ hδBB))
    have hymem : δ⁻¹ * twistMap D.F n' δ ∈ rootSpan ReeTag.F4.tag L (parabolicRoots
        ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
          Set (Fin ReeTag.F4.tag.rank))) := by
      rw [hspan]
      exact mul_mem (inv_mem hδmem) hφδmem
    have hycomm : ∀ g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n', (δ⁻¹ * twistMap D.F n' δ) * g = g * (δ⁻¹ * twistMap D.F n' δ) := by
      intro g hg
      have hgrs := hg.1
      have hgadj : g ∈ adjointGroup ReeTag.F4.tag L := hg.2.1
      have hgφ : twistMap D.F n' g = g := hg.2.2
      have hgAB : g ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
          rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) := by
        rw [← hspan]
        exact hgrs
      have h1 := hconj g hgAB
      have h2 : twistMap D.F n' (δ * g * δ⁻¹) = δ * g * δ⁻¹ := by
        rw [← h1, twistMap_mul n' (mul_mem headj hgadj) (inv_mem headj),
          twistMap_mul n' headj hgadj, twistMap_inv n' headj, hφe, hgφ]
      rw [twistMap_mul n' (mul_mem hδadj hgadj) (inv_mem hδadj), twistMap_mul n' hδadj hgadj,
        twistMap_inv n' hδadj, hgφ] at h2
      calc δ⁻¹ * twistMap D.F n' δ * g
          = δ⁻¹ * (twistMap D.F n' δ * g * (twistMap D.F n' δ)⁻¹) * twistMap D.F n' δ := by
            group
        _ = δ⁻¹ * (δ * g * δ⁻¹) * twistMap D.F n' δ := by rw [h2]
        _ = g * (δ⁻¹ * twistMap D.F n' δ) := by group
    have h1 := a1_centralizer_trivial D h hK hn' hperm hstab hymem hycomm
    exact (inv_mul_eq_one.1 h1).symm
  let Θ : SL2 K →* ModGL ReeTag.F4.tag L :=
    { toFun := fun B₀ => f B₀ * twistMap D.F n' (f B₀)
      map_one' := by
        show f 1 * twistMap D.F n' (f 1) = 1
        rw [map_one, twistMap_one, mul_one]
      map_mul' := fun B₀ B₁ => by
        have h1 : twistMap D.F n' (f B₀ * f B₁) =
            twistMap D.F n' (f B₀) * twistMap D.F n' (f B₁) :=
          hmul _ (Subgroup.mem_sup_left (hfA B₀)) _ (Subgroup.mem_sup_left (hfA B₁))
        have hc : f B₁ * twistMap D.F n' (f B₀) = twistMap D.F n' (f B₀) * f B₁ :=
          hAB _ (hfA B₁) _ (hφA _ (hfA B₀))
        show f (B₀ * B₁) * twistMap D.F n' (f (B₀ * B₁)) =
          (f B₀ * twistMap D.F n' (f B₀)) * (f B₁ * twistMap D.F n' (f B₁))
        rw [map_mul, h1]
        calc f B₀ * f B₁ * (twistMap D.F n' (f B₀) * twistMap D.F n' (f B₁))
            = f B₀ * (f B₁ * twistMap D.F n' (f B₀)) * twistMap D.F n' (f B₁) := by group
          _ = f B₀ * (twistMap D.F n' (f B₀) * f B₁) * twistMap D.F n' (f B₁) := by rw [hc]
          _ = _ := by group }
  have hΘ : ∀ B₀, Θ B₀ = f B₀ * twistMap D.F n' (f B₀) := fun _ => rfl
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro B₀ hB₀
    rw [hΘ] at hB₀
    have := (mul_inj_of_disjoint hdisj (hfA B₀) (Subgroup.one_mem _) (hφA _ (hfA B₀))
      (Subgroup.one_mem _) (by rw [hB₀, mul_one])).1
    exact hfinj (by rw [this, map_one])
  have hΘP : ∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      twistedFixed D.F n' ↔ ∃ B₀ : SL2 K, g = Θ B₀ := hPdesc
  have hδP : δ ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      twistedFixed D.F n' := by
    refine ⟨?_, hδadj, hδφ⟩
    rw [hspan]
    exact hδmem
  obtain ⟨B₁, hB₁⟩ := (hΘP δ).1 hδP
  have hΘmem : ∀ B₀ : SL2 K, Θ B₀ ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) := fun B₀ => by
    have := ((hΘP (Θ B₀)).2 ⟨B₀, rfl⟩).1
    rwa [hspan] at this
  let R₁ : Subgroup (SL2 K) := R.comap Θ
  have hR₁mem : ∀ B₀, B₀ ∈ R₁ ↔ Θ B₀ ∈ R := fun _ => Iff.rfl
  have hR₁ne : R₁ ≠ ⊥ := by
    obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR0
    obtain ⟨B₀, hB₀⟩ := (hΘP r).1 (hRP r.2)
    intro hbot
    have hmem : B₀ ∈ R₁ := by
      rw [hR₁mem, ← hB₀]
      exact r.2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hr1
    exact Subtype.ext (by rw [hB₀, hmem, map_one]; rfl)
  have hR₁2 : IsPGroup 2 R₁ := hR2.comap_of_injective Θ hΘinj
  have hδp : δ ^ p = 1 := by
    have hcAB : Commute δA δB := hAB _ hδAA _ hδBB
    have h1 : δA ^ p = 1 := by
      show (ρA (HSL (b i ^ (m + 1)))) ^ p = 1
      rw [← map_pow, HSL_pow_eq, hpw _ (hbp i), HSL_one_eq, map_one]
    have h2 : δB ^ p = 1 := by
      show (ρB (HSL (b j ^ (m + 1)))) ^ p = 1
      rw [← map_pow, HSL_pow_eq, hpw _ (hbp j), HSL_one_eq, map_one]
    show (δA * δB) ^ p = 1
    rw [hcAB.mul_pow, h1, h2, one_mul]
  have hΘB₁ : Θ B₁ = δ := hB₁.symm
  have hB₁p : B₁ ^ p = 1 := by
    apply hΘinj
    rw [map_pow, hΘB₁, hδp, map_one]
  have hB₁N : B₁ ∈ Subgroup.normalizer (R₁ : Set (SL2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro B₀
    rw [hR₁mem, hR₁mem, map_mul, map_mul, map_inv, hΘB₁]
    exact hnormR (Θ B₀) (hΘmem B₀)
  have hB₁1 : B₁ = 1 := sl2_bt hp hp2 hpq hR₁2 hR₁ne hB₁p hB₁N
  have hδ1 : δ = 1 := by rw [← hΘB₁, hB₁1, map_one]
  rcases hnt with hnt | hnt
  · have hx : pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 ∈
        rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) :=
      Subgroup.mem_sup_left ⟨uSL 1, rootSL2_uSL_charTwo _ _⟩
    have h1 := hconj _ hx
    rw [hδ1, one_mul, inv_one, mul_one] at h1
    have h2 : e * pinnedX ReeTag.F4.tag L (Pi.single i 1) 1 * e⁻¹ =
        pinnedX ReeTag.F4.tag L (Pi.single i 1) (((b i : Lˣ) : L) * 1) := by
      have := rootDiagUnit_conj_pinnedX b hα (1 : L)
      rwa [CTTorus.rootChar_single] at this
    rw [h2] at h1
    have h3 := pinnedX_injective ReeTag.F4.tag L _ h1
    exact hnt (Units.ext (by simpa using h3))
  · have hx : pinnedX ReeTag.F4.tag L (Pi.single j 1) 1 ∈
        rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) :=
      Subgroup.mem_sup_right ⟨uSL 1, rootSL2_uSL_charTwo _ _⟩
    have h1 := hconj _ hx
    rw [hδ1, one_mul, inv_one, mul_one] at h1
    have h2 : e * pinnedX ReeTag.F4.tag L (Pi.single j 1) 1 * e⁻¹ =
        pinnedX ReeTag.F4.tag L (Pi.single j 1) (((b j : Lˣ) : L) * 1) := by
      have := rootDiagUnit_conj_pinnedX b hβ (1 : L)
      rwa [CTTorus.rootChar_single] at this
    rw [h2] at h1
    have h3 := pinnedX_injective ReeTag.F4.tag L _ h1
    exact hnt (Units.ext (by simpa using h3))

end A1Struct

end CFSG.RankThree.PartOne.KEXC

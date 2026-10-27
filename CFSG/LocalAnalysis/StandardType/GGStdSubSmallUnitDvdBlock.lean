module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdDiag
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

@[expose] def ActsU (φ : ↥(unitarySU 2 n K d) →* L') (a : MulAut L') (σ : Fin d → Kˣ) : Prop :=
  ∃ hD : diagHom d σ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
    ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (conjN (diagHom d σ) hD s)

theorem ActsU.of_actsDiagU {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) :
    ∃ σ : Fin d → Kˣ, (∀ k, ((σ k : Kˣ) : K) = t k) ∧ ActsU φ a σ := by
  obtain ⟨σ, hD, hσt, hact⟩ := actsDiagU_exists_units ha
  exact ⟨σ, hσt, hD, hact⟩

theorem ActsU.actsDiagU {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ) :
    ActsDiagU φ a (fun k => ((σ k : Kˣ) : K)) := by
  obtain ⟨hD, hact⟩ := ha
  exact ⟨diagHom d σ, hD, by rw [coe_diagHom], hact⟩

theorem ActsU.fix_of_const {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {S : Finset (Fin d)} (hS : ∀ i ∈ S, ∀ j ∈ S, σ i = σ j) {y : ↥(unitarySU 2 n K d)}
    (hy : y ∈ blockSU S) : a (φ y) = φ y := by
  obtain ⟨hD, hact⟩ := ha
  rw [hact y]
  congr 1
  apply Subtype.ext
  rw [coe_conjN]
  have hc := diagHom_mul_comm_of_isBlockOn hS (X := (y : GL (Fin d) K)) hy
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem ActsU.const_of_fix (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {S : Finset (Fin d)} {k₀ : Fin d} (hk₀ : k₀ ∉ S)
    (hfix : ∀ y ∈ blockSU S, a (φ y) = φ y) : ∀ i ∈ S, ∀ j ∈ S, σ i = σ j := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨hD, hact⟩ := ha
  set P : ↥(unitarySU 2 n K d) := ⟨permGL (Equiv.swap i j), permGL_swap_mem hM.field i j⟩ with hP
  have hPS : P ∈ blockSU S := isBlockOn_permGL_swap hi hj
  have h1 := hfix P hPS
  rw [hact P] at h1
  have h2 : φ (conjN (diagHom d σ) hD P * P⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hM.ker _ h2
  have hX : (((conjN (diagHom d σ) hD P * P⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => ((σ k * (σ (Equiv.swap i j k))⁻¹ : Kˣ) : K)) := by
    have e1 : ((conjN (diagHom d σ) hD P * P⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        diagHom d (σ * (σ⁻¹ ∘ (Equiv.swap i j).symm)) := by
      have e2 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) σ⁻¹
      rw [map_inv] at e2
      rw [Subgroup.coe_mul, coe_conjN, Subgroup.coe_inv, map_mul, ← e2]
      show diagHom d σ * permGL (Equiv.swap i j) * (diagHom d σ)⁻¹ *
          (permGL (Equiv.swap i j))⁻¹ = diagHom d σ * (permGL (Equiv.swap i j) *
            (diagHom d σ)⁻¹ * (permGL (Equiv.swap i j))⁻¹)
      group
    rw [e1, coe_diagHom]
    rfl
  have hf := Matrix.diagonal_injective (hX.symm.trans hc)
  have hk := congrFun hf k₀
  have hki : k₀ ≠ i := fun h => hk₀ (h ▸ hi)
  have hkj : k₀ ≠ j := fun h => hk₀ (h ▸ hj)
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj] at hk
  have hc1 : c = 1 := by
    rw [← hk]
    simp
  have hi' := congrFun hf i
  rw [hc1, Equiv.swap_apply_left] at hi'
  have : σ i * (σ j)⁻¹ = 1 := Units.ext hi'
  exact mul_inv_eq_one.mp this


@[expose] def centSU (n : ℕ) {d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K) :
    Subgroup ↥(unitarySU 2 n K d) :=
  (Subgroup.centralizer ({D} : Set (GL (Fin d) K))).comap (unitarySU 2 n K d).subtype

theorem mem_centSU {D : GL (Fin d) K} {g : ↥(unitarySU 2 n K d)} :
    g ∈ centSU n D ↔ (g : GL (Fin d) K) * D = D * (g : GL (Fin d) K) := by
  unfold centSU
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  rfl

@[expose] def cent0 (φ : ↥(unitarySU 2 n K d) →* L') (D : GL (Fin d) K) : Subgroup L' :=
  (centSU n D).map φ

theorem mem_center_of_ker (hM : Model φ) {x : ↥(unitarySU 2 n K d)} (hx : φ x = 1) :
    (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
  obtain ⟨c, hc⟩ := hM.ker x hx
  rw [Subgroup.mem_center_iff]
  intro M
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hc]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem cent0_le_fix {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ) :
    cent0 φ (diagHom d σ) ≤ ggFix a := by
  obtain ⟨hD, hact⟩ := ha
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_ggFix, hact g]
  congr 1
  apply Subtype.ext
  rw [coe_conjN]
  have hc := mem_centSU.mp hg
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_lift_twist (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {l : L'} (hl : l ∈ ggFix a) :
    ∃ γ : ↥(unitarySU 2 n K d), φ γ = l ∧
      diagHom d σ * (γ : GL (Fin d) K) * (diagHom d σ)⁻¹ * (γ : GL (Fin d) K)⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
  obtain ⟨hD, hact⟩ := ha
  obtain ⟨γ, rfl⟩ := hM.surj l
  refine ⟨γ, rfl, ?_⟩
  have h1 : a (φ γ) = φ γ := mem_ggFix.mp hl
  rw [hact γ] at h1
  have h2 : φ (conjN (diagHom d σ) hD γ * γ⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := mem_center_of_ker hM h2
  rw [Subgroup.coe_mul, coe_conjN, Subgroup.coe_inv] at h3
  exact h3

theorem comm_of_twist {M : Type*} [Group M] {D G g Z : M} (hZ : ∀ x, x * Z = Z * x)
    (hZdef : Z = D * G * D⁻¹ * G⁻¹) (hg : g * D = D * g) :
    (G * g * G⁻¹) * D = D * (G * g * G⁻¹) := by
  have hDG : D * G = Z * G * D := by rw [hZdef]; group
  have h1 : (G * g * G⁻¹ * D) * G = (D * (G * g * G⁻¹)) * G := by
    calc G * g * G⁻¹ * D * G = G * g * G⁻¹ * (D * G) := by group
      _ = G * g * G⁻¹ * (Z * G * D) := by rw [hDG]
      _ = G * g * (G⁻¹ * Z) * G * D := by group
      _ = G * g * (Z * G⁻¹) * G * D := by rw [hZ G⁻¹]
      _ = (G * g) * Z * D := by group
      _ = Z * (G * g) * D := by rw [← hZ (G * g)]
      _ = Z * G * (g * D) := by group
      _ = Z * G * (D * g) := by rw [hg]
      _ = (Z * G * D) * g := by group
      _ = D * G * g := by rw [← hDG]
      _ = (D * (G * g * G⁻¹)) * G := by group
  exact mul_right_cancel h1

theorem cent0_normal (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {l l₀ : L'} (hl : l ∈ ggFix a) (hl₀ : l₀ ∈ cent0 φ (diagHom d σ)) :
    l * l₀ * l⁻¹ ∈ cent0 φ (diagHom d σ) := by
  obtain ⟨γ, rfl, hZ⟩ := exists_lift_twist hM ha hl
  obtain ⟨g, hg, rfl⟩ := hl₀
  refine ⟨γ * g * γ⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  change g ∈ centSU n (diagHom d σ) at hg
  change γ * g * γ⁻¹ ∈ centSU n (diagHom d σ)
  rw [mem_centSU] at hg ⊢
  have hZ' : ∀ x, x * (diagHom d σ * (γ : GL (Fin d) K) * (diagHom d σ)⁻¹ *
      (γ : GL (Fin d) K)⁻¹) = (diagHom d σ * (γ : GL (Fin d) K) * (diagHom d σ)⁻¹ *
        (γ : GL (Fin d) K)⁻¹) * x := fun x => Subgroup.mem_center_iff.mp hZ x
  have := comm_of_twist (D := diagHom d σ) (G := (γ : GL (Fin d) K)) (g := (g : GL (Fin d) K))
    hZ' rfl hg
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this


theorem conj_mem_blockSU_of_cent {σ : Fin d → Kˣ} {g y : ↥(unitarySU 2 n K d)}
    (hg : g ∈ centSU n (diagHom d σ)) {S : Finset (Fin d)}
    (hS : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i) (hy : y ∈ blockSU S) :
    g * y * g⁻¹ ∈ blockSU S := by
  have hc : ∀ g' ∈ centSU n (diagHom d σ),
      (g' : GL (Fin d) K) * diagHom d σ = diagHom d σ * g' := fun g' hg' => mem_centSU.mp hg'
  have hne : ∀ i k, i ∉ S → k ∈ S → σ i ≠ σ k := fun i k hi hk he => hi ((hS k hk i).mpr he)
  have hgi := (centSU n (diagHom d σ)).inv_mem hg
  rw [mem_blockSU]
  have h1 : (((g * y * g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  rw [h1]
  refine StdSubRestU.isBlockOn_conj ?_ hy
    (fun i k hi hk => entry_eq_zero_of_commute (hc g hg) (hne i k hi hk))
    (fun l j hl hj => entry_eq_zero_of_commute (hc _ hgi) (hne j l hj hl).symm)
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem isComponentOf_block (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {S : Finset (Fin d)} (hS : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i)
    (hq : CFSG.Assembly.IsQuasisimple ↥((blockSU S).map φ)) :
    IsComponentOf ((blockSU S).map φ) (ggFix a) := by
  have hSc : ∀ i ∈ S, ∀ j ∈ S, σ i = σ j := fun i hi j hj => ((hS i hi j).mp hj).symm
  have hle1 : (blockSU S).map φ ≤ cent0 φ (diagHom d σ) := by
    refine Subgroup.map_mono (fun y hy => ?_)
    rw [mem_centSU]
    exact (diagHom_mul_comm_of_isBlockOn hSc hy).symm
  have hle2 := cent0_le_fix ha
  refine ⟨hle1.trans hle2, IsSubnormal.step hle1 ?_ (IsSubnormal.step hle2 ?_
    (IsSubnormal.refl _)), hq⟩
  · rw [Subgroup.normal_subgroupOf_iff hle1]
    rintro _ k ⟨y, hy, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨g * y * g⁻¹, conj_mem_blockSU_of_cent hg hS hy, by simp only [map_mul, map_inv]⟩
  · rw [Subgroup.normal_subgroupOf_iff hle2]
    intro h k hh hk
    exact cent0_normal hM ha hk hh

theorem layer_eq_block [Finite L'] (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ}
    (ha : ActsU φ a σ) {S : Finset (Fin d)} (hS : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i)
    (hq : CFSG.Assembly.IsQuasisimple ↥((blockSU S).map φ))
    (hE : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    LargeEvenLayer (ggFix a) = (blockSU S).map φ := by
  have hKc := isComponentOf_block hM ha hS hq
  have hKE : (blockSU S).map φ ≤ LargeEvenLayer (ggFix a) := le_sSup hKc
  exact (eq_of_isComponentOf_le hKc hE hKE).symm

theorem comm_mem_cent0 (hM : Model φ) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    {l₁ l₂ : L'} (h₁ : l₁ ∈ ggFix a) (h₂ : l₂ ∈ ggFix a) :
    ⁅l₁, l₂⁆ ∈ cent0 φ (diagHom d σ) := by
  obtain ⟨γ₁, rfl, hZ₁⟩ := exists_lift_twist hM ha h₁
  obtain ⟨γ₂, rfl, hZ₂⟩ := exists_lift_twist hM ha h₂
  refine ⟨⁅γ₁, γ₂⁆, ?_, by rw [map_commutatorElement]⟩
  change ⁅γ₁, γ₂⁆ ∈ centSU n (diagHom d σ)
  rw [mem_centSU]
  set D := diagHom d σ with hD
  set G₁ := (γ₁ : GL (Fin d) K) with hG₁
  set G₂ := (γ₂ : GL (Fin d) K) with hG₂
  have e1 : D * G₁ * D⁻¹ = (D * G₁ * D⁻¹ * G₁⁻¹) * G₁ := by group
  have e2 : D * G₂ * D⁻¹ = (D * G₂ * D⁻¹ * G₂⁻¹) * G₂ := by group
  have hcomm : D * ⁅G₁, G₂⁆ * D⁻¹ = ⁅G₁, G₂⁆ := by
    have h3 := map_commutatorElement (MulAut.conj D) G₁ G₂
    simp only [MulAut.conj_apply] at h3
    rw [h3, e1, e2]
    exact comm_mul_central hZ₁ hZ₂ G₁ G₂
  have hc : ((⁅γ₁, γ₂⁆ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = ⁅G₁, G₂⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [hc]
  calc ⁅G₁, G₂⁆ * D = D * ⁅G₁, G₂⁆ * D⁻¹ * D := by rw [hcomm]
    _ = D * ⁅G₁, G₂⁆ := by group

theorem centSU_comm_of_injective {σ : Fin d → Kˣ} (hσ : Function.Injective σ)
    {g g' : ↥(unitarySU 2 n K d)} (hg : g ∈ centSU n (diagHom d σ))
    (hg' : g' ∈ centSU n (diagHom d σ)) : g * g' = g' * g := by
  have hdiag : ∀ x ∈ centSU n (diagHom d σ),
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
    intro x hx i j hij
    exact entry_eq_zero_of_commute (mem_centSU.mp hx) (hσ.ne hij)
  have h1 := (Matrix.isDiag_iff_diagonal_diag _).mp (hdiag g hg)
  have h2 := (Matrix.isDiag_iff_diagonal_diag _).mp (hdiag g' hg')
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← h1, ← h2,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem not_isComponentOf_of_injective [Finite L'] (hM : Model φ) {a : MulAut L'}
    {σ : Fin d → Kˣ} (ha : ActsU φ a σ) (hσ : Function.Injective σ)
    (hE : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) : False := by
  set E := LargeEvenLayer (ggFix a) with hEdef
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.mpr hE.2.2.1)
  have hEle : E ≤ ggFix a := hE.1
  have hEc : E ≤ cent0 φ (diagHom d σ) := by
    rw [← hEperf]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    exact comm_mem_cent0 hM ha (hEle hx) (hEle hy)
  have hbot : E = ⊥ := by
    rw [← hEperf, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨g, hg, rfl⟩ := hEc hx
    obtain ⟨g', hg', rfl⟩ := hEc hy
    rw [Subgroup.mem_bot, commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, centSU_comm_of_injective hσ hg hg', mul_inv_cancel_right, mul_inv_cancel,
      map_one]
  have hn : Nontrivial ↥E :=
    CFSG.LocalCores.isQuasisimple_nontrivial ((TableBSymp.isQuasisimple_iff E).mp hE.2.2)
  rw [hbot] at hn
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hn


open scoped Classical in
@[expose] noncomputable def cls (σ : Fin d → Kˣ) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun k => σ k = σ i

open scoped Classical in
theorem mem_cls {σ : Fin d → Kˣ} {i k : Fin d} : k ∈ cls σ i ↔ σ k = σ i := by
  simp [cls]

theorem cls_isCls (σ : Fin d → Kˣ) (i : Fin d) :
    ∀ x ∈ cls σ i, ∀ j, j ∈ cls σ i ↔ σ j = σ x := by
  intro x hx j
  rw [mem_cls] at hx ⊢
  rw [hx]

end CFSG.StandardType.SmallU

end

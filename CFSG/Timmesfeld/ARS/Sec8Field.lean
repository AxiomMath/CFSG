module

public import CFSG.Timmesfeld.ARS.FrameSL3Coord
public import CFSG.Timmesfeld.ARS.Sec8Regular
public import CFSG.Timmesfeld.ARS.Sec5Seven

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec8Field

section Torus

variable {K : Type*} [Field K] {A A₀ : Subgroup G} (φ : ↥(A ⊔ A₀) ≃* SpecialLinearGroup (Fin 2) K)

theorem torPar_one : torPar φ 1 = 1 := by
  simp [torPar, diagElt_one]

theorem torPar_mul (c d : Kˣ) : torPar φ (c * d) = torPar φ c * torPar φ d := by
  simp only [torPar, ← diagElt_mul_diagElt, map_mul, Subgroup.coe_mul]

theorem torPar_inv (c : Kˣ) : (torPar φ c)⁻¹ = torPar φ c⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← torPar_mul, inv_mul_cancel, torPar_one]

theorem torPar_mem_sup (c : Kˣ) : torPar φ c ∈ A ⊔ A₀ :=
  (φ.symm (diagElt c)).2

variable {φ} (hφA : (A.subgroupOf (A ⊔ A₀)).map φ.toMonoidHom = upperUnipotent K)
include hφA

theorem torPar_mem_normalizer (c : Kˣ) : torPar φ c ∈ Subgroup.normalizer (A : Set G) :=
  coe_mem_normalizer hφA le_sup_left (by
    rw [MulEquiv.apply_symm_apply]
    exact diagElt_mem_normalizer_upperUnipotent c)

theorem conjSub_torPar (c : Kˣ) : conjSub A (torPar φ c) = A :=
  conjSub_eq_self_iff.2 (torPar_mem_normalizer hφA c)

end Torus

section Param

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A)
  {K : Type*} [Field K] [Finite K] [CharP K 2] {φ : ↥(A ⊔ A₀) ≃* SpecialLinearGroup (Fin 2) K}
  (hφA : (A.subgroupOf (A ⊔ A₀)).map φ.toMonoidHom = upperUnipotent K)
include h hA hA₀ hφA

theorem exists_param {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) {w : G} (hw : w ∈ D)
    (hw1 : w ≠ 1) :
    ∃ d : K → G, (∀ s t, d (s + t) = d s * d t) ∧ Function.Injective d ∧ d 1 = w ∧
      (∀ s, d s ∈ D) ∧ (∀ x ∈ D, ∃ s, d s = x) ∧
      ∀ (c : Kˣ) (s : K), torPar φ c * d s * (torPar φ c)⁻¹ = d (c * s) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨θ, hθ, hrange, he⟩ :=
    Sec3.exists_isNaturalModule hR hiso hA hA₀.1 hA₀.2 hD.1 hD.2 φ hφA hw hw1
  have hmem : ∀ v, θ v ∈ D ⊔ ⁅A₀, D⁆ := fun v => by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨v, rfl⟩
  refine ⟨fun s => θ ![s, 0], map_vec_add_left hθ, injective_left hθ, he, fun s => ?_,
    fun x hx => ?_, fun c s => ?_⟩
  · refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA hA₀.1 hA₀.2 hD.1 hD.2 (hmem _) ?_
    exact (hθ.forall_commute_upper_iff hφA le_sup_left _).2 (by simp)
  · have hx' : x ∈ Set.range θ := by
      rw [hrange]
      exact Subgroup.mem_sup_left hx
    obtain ⟨v, rfl⟩ := hx'
    have h1 : v 1 = 0 := (hθ.forall_commute_upper_iff hφA le_sup_left v).1
      fun a ha => hD.1.1.2.2 a ha _ hx
    refine ⟨v 0, congrArg θ ?_⟩
    ext i
    fin_cases i <;> simp [h1]
  · simp only
    rw [torPar_conj hθ]
    congr 1
    ext i
    fin_cases i <;> simp

theorem conjSub_torPar_of_mem_lambdaStar {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀)
    (c : Kˣ) : conjSub D (torPar φ c) = D := by
  obtain ⟨w, hw, hw1⟩ := h.root.exists_ne_one hD.1.1.1
  obtain ⟨d, -, -, -, hdD, hDd, hd⟩ := exists_param h hA hA₀ hφA hD hw hw1
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := hDd x hx
    change torPar φ c * d s * (torPar φ c)⁻¹ ∈ D
    rw [hd]
    exact hdD _
  · obtain ⟨s, rfl⟩ := hDd x hx
    rw [mem_conjSub]
    have e := hd c⁻¹ s
    rw [← torPar_inv, inv_inv] at e
    rw [show (torPar φ c)⁻¹ * d s * torPar φ c = d ((c⁻¹ : Kˣ) * s) from e]
    exact hdD _

end Param

instance normal_subgroupOf_M (R : Set (Subgroup G)) (A : Subgroup G) :
    (A.subgroupOf (M R A)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer QD.le_M_self]
  exact sup_le Subgroup.le_normalizer (iSup₂_le fun B hB =>
    (commuting_iff_le_centralizer.1 hB.1.2.2).trans (Subgroup.centralizer_le_normalizer _))

abbrev MQuot (R : Set (Subgroup G)) (A : Subgroup G) : Type _ :=
  ↥(M R A) ⧸ A.subgroupOf (M R A)

abbrev commGroupMQuot (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R) : CommGroup (MQuot R A) where
  __ := (inferInstance : Group (MQuot R A))
  mul_comm x y := by
    refine QuotientGroup.induction_on x fun a => QuotientGroup.induction_on y fun b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc : ⁅(b : G)⁻¹, (a : G)⁻¹⁆ ∈ ⁅M R A, M R A⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem b.2) (inv_mem a.2)
    rw [(Q_eq_M h hA).2.2.1] at hc
    have e : (((a * b)⁻¹ * (b * a) : ↥(M R A)) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hc

section Conj

variable (hR : IsRootClass R) {A : Subgroup G}

section Normalizer

variable {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
include hR hg

theorem conj_mem_M_of_mem_normalizer {m : G} (hm : m ∈ M R A) : g * m * g⁻¹ ∈ M R A := by
  have := conj_mem_conjSub g hm
  rwa [Sec5.conjSub_M hR, conjSub_eq_self_iff.2 hg] at this

@[expose] def conjN : ↥(M R A) →* ↥(M R A) where
  toFun m := ⟨g * m * g⁻¹, conj_mem_M_of_mem_normalizer hR hg m.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' m m' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem le_comap_conjN :
    A.subgroupOf (M R A) ≤ (A.subgroupOf (M R A)).comap (conjN hR hg) := fun m hm => by
  have := conj_mem_conjSub g (Subgroup.mem_subgroupOf.1 hm)
  rw [conjSub_eq_self_iff.2 hg] at this
  exact this

@[expose] def conjNQ : MQuot R A →* MQuot R A :=
  QuotientGroup.map _ _ (conjN hR hg) (le_comap_conjN hR hg)

end Normalizer

variable {K : Type*} [Field K] {A₀ : Subgroup G} {φ : ↥(A ⊔ A₀) ≃* SpecialLinearGroup (Fin 2) K}
  (hφA : (A.subgroupOf (A ⊔ A₀)).map φ.toMonoidHom = upperUnipotent K)

@[expose] def conjM (c : Kˣ) : ↥(M R A) →* ↥(M R A) :=
  conjN hR (torPar_mem_normalizer hφA c)

theorem coe_conjM (c : Kˣ) (m : ↥(M R A)) :
    (conjM hR hφA c m : G) = torPar φ c * m * (torPar φ c)⁻¹ := rfl

@[expose] def conjQ (c : Kˣ) : MQuot R A →* MQuot R A :=
  conjNQ hR (torPar_mem_normalizer hφA c)

theorem conjQ_one (x : MQuot R A) : conjQ hR hφA 1 x = x := by
  refine QuotientGroup.induction_on x fun m => ?_
  change ((conjM hR hφA 1 m : ↥(M R A)) : MQuot R A) = m
  congr 1
  exact Subtype.ext (by rw [coe_conjM, torPar_one]; group)

theorem conjQ_mul (c d : Kˣ) (x : MQuot R A) :
    conjQ hR hφA (c * d) x = conjQ hR hφA c (conjQ hR hφA d x) := by
  refine QuotientGroup.induction_on x fun m => ?_
  change ((conjM hR hφA (c * d) m : ↥(M R A)) : MQuot R A) =
    ((conjM hR hφA c (conjM hR hφA d m) : ↥(M R A)) : MQuot R A)
  congr 1
  refine Subtype.ext ?_
  rw [coe_conjM, coe_conjM, coe_conjM, torPar_mul]
  group

end Conj

@[expose] def Space (_h : Hyp G R) {A A₀ : Subgroup G} (_hA : A ∈ R) (_hA₀ : A₀ ∈ omegaSet R A)
    {K : Type*} [Field K] (φ : ↥(A ⊔ A₀) ≃* SpecialLinearGroup (Fin 2) K)
    (_hφA : (A.subgroupOf (A ⊔ A₀)).map φ.toMonoidHom = upperUnipotent K) : Type _ :=
  Additive (MQuot R A)

section Space

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A) {K : Type*}
  [Field K] (φ : ↥(A ⊔ A₀) ≃* SpecialLinearGroup (Fin 2) K)
  (hφA : (A.subgroupOf (A ⊔ A₀)).map φ.toMonoidHom = upperUnipotent K)

instance : AddCommGroup (Space h hA hA₀ φ hφA) :=
  @Additive.addCommGroup (MQuot R A) (commGroupMQuot h hA)

instance : Finite (Space h hA hA₀ φ hφA) := by
  have := h.finite
  exact Finite.of_equiv (MQuot R A) Additive.ofMul

@[expose] def mk (m : ↥(M R A)) : Space h hA hA₀ φ hφA :=
  Additive.ofMul (QuotientGroup.mk m : MQuot R A)

theorem mk_mul (m m' : ↥(M R A)) :
    mk h hA hA₀ φ hφA (m * m') = mk h hA hA₀ φ hφA m + mk h hA hA₀ φ hφA m' := rfl

theorem mk_one : mk h hA hA₀ φ hφA 1 = 0 := rfl

theorem mk_inv (m : ↥(M R A)) : mk h hA hA₀ φ hφA m⁻¹ = -mk h hA hA₀ φ hφA m := rfl

theorem mk_eq_zero_iff (m : ↥(M R A)) : mk h hA hA₀ φ hφA m = 0 ↔ (m : G) ∈ A := by
  change (QuotientGroup.mk m : MQuot R A) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk_surjective : Function.Surjective (mk h hA hA₀ φ hφA) := fun x =>
  QuotientGroup.mk_surjective (Additive.toMul x : MQuot R A)

open Classical in
noncomputable instance : SMul K (Space h hA hA₀ φ hφA) where
  smul c x := if hc : c = 0 then 0 else
    Additive.ofMul (conjQ h.root hφA (Units.mk0 c hc) (Additive.toMul x : MQuot R A))

variable {h hA hA₀ φ hφA}

theorem zero_smul' (x : Space h hA hA₀ φ hφA) : (0 : K) • x = 0 := dite_eq_left rfl

theorem smul_of_ne {c : K} (hc : c ≠ 0) (x : Space h hA hA₀ φ hφA) :
    c • x = Additive.ofMul (conjQ h.root hφA (Units.mk0 c hc) (Additive.toMul x : MQuot R A)) :=
  dite_eq_right hc

variable (h hA hA₀ φ hφA) in
theorem smul_mk (c : Kˣ) (m : ↥(M R A)) :
    (c : K) • mk h hA hA₀ φ hφA m = mk h hA hA₀ φ hφA (conjM h.root hφA c m) := by
  rw [smul_of_ne c.ne_zero, Units.mk0_val]
  rfl

theorem smul_add' (c : K) (x y : Space h hA hA₀ φ hφA) : c • (x + y) = c • x + c • y := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul', zero_smul', zero_smul', add_zero]
  · rw [smul_of_ne hc, smul_of_ne hc, smul_of_ne hc]
    exact congrArg Additive.ofMul (map_mul _ _ _)

theorem smul_zero' (c : K) : c • (0 : Space h hA hA₀ φ hφA) = 0 := by
  by_cases hc : c = 0
  · subst hc
    exact zero_smul' _
  · rw [smul_of_ne hc]
    exact congrArg Additive.ofMul (map_one _)

theorem smul_neg' (c : K) (x : Space h hA hA₀ φ hφA) : c • (-x) = -(c • x) := by
  rw [eq_neg_iff_add_eq_zero, ← smul_add', neg_add_cancel, smul_zero']

theorem one_smul' (x : Space h hA hA₀ φ hφA) : (1 : K) • x = x := by
  rw [smul_of_ne one_ne_zero, show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext rfl,
    conjQ_one]
  rfl

theorem mul_smul' (c d : K) (x : Space h hA hA₀ φ hφA) : (c * d) • x = c • d • x := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_mul, zero_smul', zero_smul']
  by_cases hd : d = 0
  · subst hd
    rw [mul_zero, zero_smul', smul_zero']
  rw [smul_of_ne (mul_ne_zero hc hd), smul_of_ne hc, smul_of_ne hd,
    show Units.mk0 (c * d) (mul_ne_zero hc hd) = Units.mk0 c hc * Units.mk0 d hd from Units.ext rfl,
    conjQ_mul]
  rfl

theorem smul_mk_param {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) {d : K → G}
    (hdD : ∀ s, d s ∈ D) (hd0 : d 0 = 1)
    (hd : ∀ (c : Kˣ) (s : K), torPar φ c * d s * (torPar φ c)⁻¹ = d (c * s)) (c s : K) :
    c • mk h hA hA₀ φ hφA ⟨d s, QD.le_M hD.1 (hdD s)⟩ =
      mk h hA hA₀ φ hφA ⟨d (c * s), QD.le_M hD.1 (hdD _)⟩ := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul', eq_comm, mk_eq_zero_iff]
    show d (0 * s) ∈ A
    rw [zero_mul, hd0]
    exact A.one_mem
  · rw [show c = ((Units.mk0 c hc : Kˣ) : K) from rfl, smul_mk]
    congr 1
    exact Subtype.ext (by rw [coe_conjM]; exact hd _ s)

variable [Finite K] [CharP K 2]

theorem add_smul' (c₁ c₂ : K) (x : Space h hA hA₀ φ hφA) : (c₁ + c₂) • x = c₁ • x + c₂ • x := by
  obtain ⟨m, rfl⟩ := mk_surjective h hA hA₀ φ hφA x
  let P : Space h hA hA₀ φ hφA → Prop := fun y => (c₁ + c₂) • y = c₁ • y + c₂ • y
  have hP0 : P 0 := by
    simp only [P, smul_zero', add_zero]
  have hPadd : ∀ y z, P y → P z → P (y + z) := by
    intro y z hy hz
    simp only [P, smul_add'] at hy hz ⊢
    rw [hy, hz]
    abel
  have hPneg : ∀ y, P y → P (-y) := by
    intro y hy
    simp only [P, smul_neg'] at hy ⊢
    rw [hy, neg_add]
  let T : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ M R A, P (mk h hA hA₀ φ hφA ⟨g, hg⟩)}
      mul_mem' := by
        rintro g g' ⟨hg, h1⟩ ⟨hg', h2⟩
        exact ⟨(M R A).mul_mem hg hg', hPadd _ _ h1 h2⟩
      one_mem' := ⟨(M R A).one_mem, hP0⟩
      inv_mem' := by
        rintro g ⟨hg, h1⟩
        exact ⟨(M R A).inv_mem hg, hPneg _ h1⟩ }
  have hMT : M R A ≤ T := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    refine gen_le fun D hD g hg => ?_
    obtain ⟨w, hw, hw1⟩ := h.root.exists_ne_one hD.1.1.1
    obtain ⟨d, hadd, -, -, hdD, hDd, hd⟩ := exists_param h hA hA₀ hφA hD hw hw1
    obtain ⟨s, rfl⟩ := hDd g hg
    have hd0 : d 0 = 1 := by
      have e := hadd 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    refine ⟨QD.le_M hD.1 (hdD s), ?_⟩
    simp only [P]
    rw [smul_mk_param hD hdD hd0 hd, smul_mk_param hD hdD hd0 hd, smul_mk_param hD hdD hd0 hd,
      ← mk_mul]
    congr 1
    exact Subtype.ext (show d ((c₁ + c₂) * s) = d (c₁ * s) * d (c₂ * s) by rw [add_mul, hadd])
  exact (hMT m.2).2

noncomputable instance : Module K (Space h hA hA₀ φ hφA) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_zero := smul_zero'
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul := zero_smul'

variable (h hA hA₀ φ hφA)

@[expose] def submodule (H : Subgroup G) (hH : ∀ c : Kˣ, conjSub H (torPar φ c) = H) :
    Submodule K (Space h hA hA₀ φ hφA) where
  carrier := {x | ∃ m : ↥(M R A), (m : G) ∈ H ∧ mk h hA hA₀ φ hφA m = x}
  add_mem' := by
    rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m * m', H.mul_mem hm hm', mk_mul h hA hA₀ φ hφA m m'⟩
  zero_mem' := ⟨1, H.one_mem, mk_one h hA hA₀ φ hφA⟩
  smul_mem' := by
    rintro c _ ⟨m, hm, rfl⟩
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul']
      exact ⟨1, H.one_mem, mk_one h hA hA₀ φ hφA⟩
    · refine ⟨conjM h.root hφA (Units.mk0 c hc) m, ?_, (smul_mk h hA hA₀ φ hφA _ m).symm⟩
      have := conj_mem_conjSub (torPar φ (Units.mk0 c hc)) hm
      rwa [hH] at this

theorem mem_submodule {H : Subgroup G} {hH : ∀ c : Kˣ, conjSub H (torPar φ c) = H}
    {x : Space h hA hA₀ φ hφA} :
    x ∈ submodule h hA hA₀ φ hφA H hH ↔ ∃ m : ↥(M R A), (m : G) ∈ H ∧ mk h hA hA₀ φ hφA m = x :=
  Iff.rfl

end Space

end Sec8Field

end CFSG.Timmesfeld.ARS

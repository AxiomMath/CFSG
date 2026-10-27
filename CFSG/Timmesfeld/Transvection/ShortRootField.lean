module

public import CFSG.Timmesfeld.Transvection.Sp4Root

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

section ModuleOfUnits

variable {K V : Type*} [Field K] [AddCommGroup V] (ρ : Kˣ → V →+ V)

@[expose] noncomputable def smulOfUnits (c : K) (v : V) : V :=
  haveI := Classical.dec (c = 0)
  if h : c = 0 then 0 else ρ (Units.mk0 c h) v

theorem smulOfUnits_zero (v : V) : smulOfUnits ρ 0 v = 0 := by
  simp [smulOfUnits]

theorem smulOfUnits_units (c : Kˣ) (v : V) : smulOfUnits ρ c v = ρ c v := by
  simp only [smulOfUnits, Units.ne_zero, ↓reduceDIte, Units.mk0_val]

theorem smulOfUnits_of_ne {c : K} (hc : c ≠ 0) (v : V) :
    smulOfUnits ρ c v = ρ (Units.mk0 c hc) v := by
  rw [← smulOfUnits_units, Units.val_mk0]

@[reducible, expose] noncomputable def moduleOfUnits (hone : ∀ v, ρ 1 v = v)
    (hmul : ∀ c c' v, ρ (c * c') v = ρ c (ρ c' v))
    (hadd : ∀ (c c' : Kˣ) (h : (c : K) + c' ≠ 0) (v : V), ρ (Units.mk0 _ h) v = ρ c v + ρ c' v)
    (hneg : ∀ (c c' : Kˣ), (c : K) + c' = 0 → ∀ v : V, ρ c v + ρ c' v = 0) : Module K V where
  smul := smulOfUnits ρ
  one_smul v := by
    show smulOfUnits ρ 1 v = v
    rw [← Units.val_one, smulOfUnits_units, hone]
  mul_smul c c' v := by
    show smulOfUnits ρ (c * c') v = smulOfUnits ρ c (smulOfUnits ρ c' v)
    by_cases hc : c = 0
    · simp [hc, smulOfUnits_zero]
    by_cases hc' : c' = 0
    · simp [hc', smulOfUnits_zero, smulOfUnits_of_ne ρ hc]
    rw [smulOfUnits_of_ne ρ (mul_ne_zero hc hc'), smulOfUnits_of_ne ρ hc,
      smulOfUnits_of_ne ρ hc', ← hmul]
    congr 2
    ext
    rfl
  smul_zero c := by
    show smulOfUnits ρ c 0 = 0
    by_cases hc : c = 0
    · simp [hc, smulOfUnits_zero]
    · simp [smulOfUnits_of_ne ρ hc]
  smul_add c v w := by
    show smulOfUnits ρ c (v + w) = smulOfUnits ρ c v + smulOfUnits ρ c w
    by_cases hc : c = 0
    · simp [hc, smulOfUnits_zero]
    · simp [smulOfUnits_of_ne ρ hc]
  add_smul c c' v := by
    show smulOfUnits ρ (c + c') v = smulOfUnits ρ c v + smulOfUnits ρ c' v
    by_cases hc : c = 0
    · simp [hc, smulOfUnits_zero]
    by_cases hc' : c' = 0
    · simp [hc', smulOfUnits_zero]
    rw [smulOfUnits_of_ne ρ hc, smulOfUnits_of_ne ρ hc']
    by_cases hcc : c + c' = 0
    · rw [hcc, smulOfUnits_zero]
      exact (hneg (Units.mk0 c hc) (Units.mk0 c' hc') hcc v).symm
    · rw [smulOfUnits_of_ne ρ hcc]
      exact hadd (Units.mk0 c hc) (Units.mk0 c' hc') hcc v
  zero_smul v := smulOfUnits_zero ρ v

end ModuleOfUnits

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

noncomputable def torusElt (c : (GaloisField 2 k)ˣ) : G := (φ.mat_surj (diagElt c)).choose

theorem torusElt_mem (c : (GaloisField 2 k)ˣ) : φ.torusElt c ∈ A ⊔ E :=
  (φ.mat_surj (diagElt c)).choose_spec.1

theorem mat_torusElt (c : (GaloisField 2 k)ˣ) : φ.mat (φ.torusElt c) = diagElt c :=
  (φ.mat_surj (diagElt c)).choose_spec.2

theorem torusElt_mul (c c' : (GaloisField 2 k)ˣ) :
    φ.torusElt (c * c') = φ.torusElt c * φ.torusElt c' :=
  φ.mat_injOn (φ.torusElt_mem _) (Subgroup.mul_mem _ (φ.torusElt_mem c) (φ.torusElt_mem c')) (by
    rw [φ.mat_mul (φ.torusElt_mem c) (φ.torusElt_mem c'), φ.mat_torusElt, φ.mat_torusElt,
      φ.mat_torusElt, diagElt_mul_diagElt])

theorem torusElt_one : φ.torusElt 1 = 1 :=
  φ.mat_inj (φ.torusElt_mem 1) (by rw [φ.mat_torusElt, diagElt_one])

theorem torusElt_inv (c : (GaloisField 2 k)ˣ) : φ.torusElt c⁻¹ = (φ.torusElt c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← φ.torusElt_mul, inv_mul_cancel, φ.torusElt_one]

end SL2Coords

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

theorem conjSub_torusElt [Finite G] (c : (GaloisField 2 k)ˣ) :
    conjSub A (φ.torusElt c) = A ∧ conjSub E (φ.torusElt c) = E := by
  have hX := φ.torusElt_mem c
  have key : ∀ {P : Subgroup G}, P ≤ A ⊔ E →
      ∀ {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))},
      (∀ {x : G}, x ∈ A ⊔ E → (x ∈ P ↔ φ.mat x ∈ U)) →
      diagElt c ∈ Subgroup.normalizer (U : Set _) → conjSub P (φ.torusElt c) = P := by
    intro P hP U hU hnorm
    have hle : conjSub P (φ.torusElt c) ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      show φ.torusElt c * a * (φ.torusElt c)⁻¹ ∈ P
      have haX : a ∈ A ⊔ E := hP ha
      have hX' : φ.torusElt c * a ∈ A ⊔ E := Subgroup.mul_mem _ hX haX
      rw [hU (Subgroup.mul_mem _ hX' (Subgroup.inv_mem _ hX)), φ.mat_mul hX'
        (Subgroup.inv_mem _ hX), φ.mat_mul hX haX, φ.mat_inv hX, φ.mat_torusElt]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 ((hU haX).1 ha)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj (φ.torusElt c)).injective).ge
  exact ⟨key le_sup_left (fun hx => φ.mem_A_iff hx) (diagElt_mem_normalizer_lowerUnipotent c),
    key le_sup_right (fun hx => φ.mem_E_iff hx) (diagElt_mem_normalizer_upperUnipotent c)⟩

end SL2Coords

@[expose] def SL2Coords.Aligned (Δ : Set (Subgroup G)) {A E D E' : Subgroup G} {k : ℕ}
    (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k) : Prop :=
  ∀ ν : (GaloisField 2 k)ˣ, ∀ x ∈ shortRootGroup Δ E A D E',
    Commute (φ₀.torusElt ν * φ₁.torusElt ν) x

namespace TriangleSetting

variable {A E C : Subgroup G} {t : G} (S : TriangleSetting Δ A E C t) (htY : t ∈ A ⊔ E ⊔ C)
  {k : ℕ} (φ : SL2Coords A E k)

theorem vecOf_torusElt [Finite G] (hq : 4 ≤ Nat.card A) {x : G}
    (hx : x ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G)) (c : (GaloisField 2 k)ˣ) :
    S.vecOf htY hq φ (φ.torusElt c * x * (φ.torusElt c)⁻¹) =
      ![(c : GaloisField 2 k) * S.vecOf htY hq φ x 0, 0] := by
  have hx1 : S.vecOf htY hq φ x 1 = 0 := ((S.vecOf_spec htY hq φ).2.2.2.2.2.1 hx.1).1
    fun e he => (Subgroup.mem_centralizer_iff.1 hx.2 e he).symm
  rw [(S.vecOf_spec htY hq φ).2.2.2.1 (φ.torusElt_mem c) hx.1, φ.mat_torusElt, diagElt_mulVec,
    hx1, mul_zero]

end TriangleSetting

@[expose] def ShortRootFieldHyp (Δ : Set (Subgroup G)) (A E D E' : Subgroup G) : Prop :=
  (∀ x ∈ shortRootGroup Δ E A D E', x ≠ 1 → conjSub A x ∈ lineOf Δ A D ∧
    conjSub A x ≠ A ∧ conjSub A x ≠ D ∧ ∀ t, TriangleSetting Δ A E (conjSub A x) t →
      t ∈ A ⊔ E ⊔ conjSub A x → x ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G)) ∧
  (∀ x ∈ shortRootGroup Δ E A D E', conjSub A x = A → x = 1)

namespace PairFrame

variable {A E D E' : Subgroup G} (F : PairFrame Δ A E D E') {k : ℕ} (φ : SL2Coords A E k)
include F

theorem commute_torusElt (c : (GaloisField 2 k)ˣ) {x : G} (hx : x ∈ D ⊔ E') :
    Commute (φ.torusElt c) x :=
  F.comm _ (φ.torusElt_mem c) x hx

theorem conjSub_shortRootGroup_torusElt [Finite G] (hR : IsRootClass Δ)
    (c : (GaloisField 2 k)ˣ) :
    conjSub (shortRootGroup Δ E A D E') (φ.torusElt c) = shortRootGroup Δ E A D E' := by
  obtain ⟨hA, hE⟩ := φ.conjSub_torusElt c
  have hD : conjSub D (φ.torusElt c) = D :=
    conjSub_of_forall_commute fun d hd => F.commute_torusElt φ c (Subgroup.mem_sup_left hd)
  have hE' : conjSub E' (φ.torusElt c) = E' :=
    conjSub_of_forall_commute fun d hd => F.commute_torusElt φ c (Subgroup.mem_sup_right hd)
  rw [← shortRootGroup_conjSub hR, hA, hE, hD, hE']

theorem conj_torusElt_mem [Finite G] (hR : IsRootClass Δ) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (c : (GaloisField 2 k)ˣ) :
    φ.torusElt c * x * (φ.torusElt c)⁻¹ ∈ shortRootGroup Δ E A D E' := by
  have h := conj_mem_conjSub (φ.torusElt c) hx
  rwa [F.conjSub_shortRootGroup_torusElt φ hR c] at h

omit φ in
theorem commute_of_mem_shortRootGroup (hΔ : IsTransvectionClass Δ) {x y : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hy : y ∈ shortRootGroup Δ E A D E') : Commute x y :=
  commute_of_mem_lineGroup hΔ F.memE F.memD F.commuting_ED hx.1.1 hy.1.1

omit φ in
theorem mul_self_of_mem_shortRootGroup (hΔ : IsTransvectionClass Δ) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') : x * x = 1 :=
  mul_self_of_mem_lineGroup hΔ F.memE F.memD F.commuting_ED hx.1.1

omit φ in
@[reducible, expose] def shortRootAddCommGroup (hΔ : IsTransvectionClass Δ) :
    AddCommGroup (Additive ↥(shortRootGroup Δ E A D E')) :=
  { (inferInstance : AddGroup (Additive ↥(shortRootGroup Δ E A D E'))) with
    add_comm := fun a b => Additive.toMul.injective (Subtype.ext
      (F.commute_of_mem_shortRootGroup hΔ a.toMul.2 b.toMul.2).eq) }

@[expose] noncomputable def torusAct [Finite G] (hR : IsRootClass Δ) (c : (GaloisField 2 k)ˣ) :
    Additive ↥(shortRootGroup Δ E A D E') →+ Additive ↥(shortRootGroup Δ E A D E') where
  toFun v := Additive.ofMul ⟨φ.torusElt c * (v.toMul : G) * (φ.torusElt c)⁻¹,
    F.conj_torusElt_mem φ hR v.toMul.2 c⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show φ.torusElt c * 1 * (φ.torusElt c)⁻¹ = 1
    group
  map_add' v w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show φ.torusElt c * ((v.toMul : G) * w.toMul) * (φ.torusElt c)⁻¹ =
      (φ.torusElt c * v.toMul * (φ.torusElt c)⁻¹) * (φ.torusElt c * w.toMul * (φ.torusElt c)⁻¹)
    group

theorem coe_torusAct [Finite G] (hR : IsRootClass Δ) (c : (GaloisField 2 k)ˣ)
    (v : Additive ↥(shortRootGroup Δ E A D E')) :
    (((F.torusAct φ hR c v).toMul : ↥(shortRootGroup Δ E A D E')) : G) =
      φ.torusElt c * (v.toMul : G) * (φ.torusElt c)⁻¹ := rfl

omit F in
theorem eq_of_vecOf_eq [Finite G] (hq : 4 ≤ Nat.card A) (hX : ShortRootFieldHyp Δ A E D E')
    {C : Subgroup G} {t : G} (S : TriangleSetting Δ A E C t) (htY : t ∈ A ⊔ E ⊔ C) {y y' : G}
    (hy : y ∈ shortRootGroup Δ E A D E') (hy' : y' ∈ shortRootGroup Δ E A D E')
    (hyN : y ∈ corrN A E t) (hy'N : y' ∈ corrN A E t)
    (h : S.vecOf htY hq φ y = S.vecOf htY hq φ y') : y = y' := by
  have hzN : y⁻¹ * y' ∈ corrN A E t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hy'N
  have hzX : y⁻¹ * y' ∈ shortRootGroup Δ E A D E' :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hy'
  have hv : S.vecOf htY hq φ (y⁻¹ * y') = 0 := by
    have h1 := (S.vecOf_spec htY hq φ).1 hyN hzN
    rw [show y * (y⁻¹ * y') = y' by group, ← h] at h1
    exact (add_eq_left.1 h1.symm)
  have hz := ((S.vecOf_spec htY hq φ).2.2.1 hzN).1 hv
  have hzA : conjSub A (y⁻¹ * y') = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 hz a (Subgroup.mem_sup_left ha)).symm
  have h1 := hX.2 _ hzX hzA
  rw [inv_mul_eq_one] at h1
  exact h1

omit φ in
theorem exists_setting [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) (hX : ShortRootFieldHyp Δ A E D E') {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hx1 : x ≠ 1) :
    ∃ t, ∃ _ : TriangleSetting Δ A E (conjSub A x) t, t ∈ A ⊔ E ⊔ conjSub A x ∧
      x ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G) := by
  obtain ⟨hC, hCA, hCD, hN⟩ := hX.1 x hx hx1
  obtain ⟨t, htY, S⟩ :=
    exists_triangleSetting hΔ hiso ((F.toSp4Frame hC hCA hCD).isTriangle hΔ hpts)
  exact ⟨t, S, htY, hN t S htY⟩

theorem torusElt_add_conj [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) (hX : ShortRootFieldHyp Δ A E D E')
    (c c' : (GaloisField 2 k)ˣ) (hcc : (c : GaloisField 2 k) + c' ≠ 0) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') :
    φ.torusElt (Units.mk0 _ hcc) * x * (φ.torusElt (Units.mk0 _ hcc))⁻¹ =
      (φ.torusElt c * x * (φ.torusElt c)⁻¹) * (φ.torusElt c' * x * (φ.torusElt c')⁻¹) := by
  by_cases hx1 : x = 1
  · subst hx1
    group
  obtain ⟨t, S, htY, hxN⟩ := F.exists_setting hΔ hiso hpts hX hx hx1
  have hmemN : ∀ c : (GaloisField 2 k)ˣ, φ.torusElt c * x * (φ.torusElt c)⁻¹ ∈ corrN A E t :=
    fun c => conj_mem_corrN (φ.torusElt_mem c) hxN.1
  have hR := hΔ.root
  refine eq_of_vecOf_eq φ hq hX S htY (F.conj_torusElt_mem φ hR hx _)
    (Subgroup.mul_mem _ (F.conj_torusElt_mem φ hR hx c) (F.conj_torusElt_mem φ hR hx c'))
    (hmemN _) (Subgroup.mul_mem _ (hmemN c) (hmemN c')) ?_
  rw [(S.vecOf_spec htY hq φ).1 (hmemN c) (hmemN c'), S.vecOf_torusElt htY φ hq hxN,
    S.vecOf_torusElt htY φ hq hxN, S.vecOf_torusElt htY φ hq hxN, Units.val_mk0, add_mul]
  ext i
  fin_cases i <;> simp

@[reducible, expose] noncomputable def shortRootModule [Finite G] (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A)
    (hX : ShortRootFieldHyp Δ A E D E') :
    letI := F.shortRootAddCommGroup hΔ
    Module (GaloisField 2 k) (Additive ↥(shortRootGroup Δ E A D E')) :=
  let _ := F.shortRootAddCommGroup hΔ
  moduleOfUnits (F.torusAct φ hΔ.root)
    (fun v => by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [coe_torusAct, φ.torusElt_one]
      group)
    (fun c c' v => by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [coe_torusAct, coe_torusAct, coe_torusAct, φ.torusElt_mul]
      group)
    (fun c c' hcc v => by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact F.torusElt_add_conj φ hΔ hiso hpts hq hX c c' hcc v.toMul.2)
    (fun c c' hcc v => by
      have hc : c' = c := Units.ext (by
        rw [← CharTwo.neg_eq (c : GaloisField 2 k)]
        exact (neg_eq_of_add_eq_zero_right hcc).symm)
      rw [hc]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact F.mul_self_of_mem_shortRootGroup hΔ (F.conj_torusElt_mem φ hΔ.root v.toMul.2 c))


omit φ in
theorem conjSub_shortRootGroup_torusElt' [Finite G] (hR : IsRootClass Δ) (φ₁ : SL2Coords D E' k)
    (μ : (GaloisField 2 k)ˣ) :
    conjSub (shortRootGroup Δ E A D E') (φ₁.torusElt μ) = shortRootGroup Δ E A D E' := by
  obtain ⟨hD, hE'⟩ := φ₁.conjSub_torusElt μ
  have hA : conjSub A (φ₁.torusElt μ) = A := conjSub_of_forall_commute fun a ha =>
    (F.comm a (Subgroup.mem_sup_left ha) _ (φ₁.torusElt_mem μ)).symm
  have hE : conjSub E (φ₁.torusElt μ) = E := conjSub_of_forall_commute fun e he =>
    (F.comm e (Subgroup.mem_sup_right he) _ (φ₁.torusElt_mem μ)).symm
  rw [← shortRootGroup_conjSub hR, hE, hA, hD, hE']

section Module

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
  (hq : 4 ≤ Nat.card A) (hX : ShortRootFieldHyp Δ A E D E')

theorem coe_smul {c : GaloisField 2 k} (hc : c ≠ 0) (v : Additive ↥(shortRootGroup Δ E A D E')) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    (((c • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) =
      φ.torusElt (Units.mk0 c hc) * (v.toMul : G) * (φ.torusElt (Units.mk0 c hc))⁻¹ := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  show (((smulOfUnits (F.torusAct φ hΔ.root) c v).toMul : ↥(shortRootGroup Δ E A D E')) : G) = _
  rw [smulOfUnits_of_ne _ hc]
  rfl

theorem coe_zero_smul (v : Additive ↥(shortRootGroup Δ E A D E')) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    ((((0 : GaloisField 2 k) • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) = 1 := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  rw [zero_smul]
  rfl

theorem vecOf_smul {C : Subgroup G} {t : G} (S : TriangleSetting Δ A E C t)
    (htY : t ∈ A ⊔ E ⊔ C) (v : Additive ↥(shortRootGroup Δ E A D E'))
    (hv : ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) ∈
      corrN A E t ⊓ Subgroup.centralizer (E : Set G)) (c : GaloisField 2 k) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    ((((c • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) ∈
      corrN A E t ⊓ Subgroup.centralizer (E : Set G)) ∧
    S.vecOf htY hq φ ((c • v).toMul : ↥(shortRootGroup Δ E A D E')) =
      ![c * S.vecOf htY hq φ (v.toMul : ↥(shortRootGroup Δ E A D E')) 0, 0] := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  by_cases hc : c = 0
  · subst hc
    rw [F.coe_zero_smul φ hΔ hiso hpts hq hX v, zero_mul]
    refine ⟨Subgroup.one_mem _, ?_⟩
    have h1 := ((S.vecOf_spec htY hq φ).2.2.1 (Subgroup.one_mem (corrN A E t))).2
      (Subgroup.one_mem _)
    rw [h1]
    ext i
    fin_cases i <;> rfl
  · rw [F.coe_smul φ hΔ hiso hpts hq hX hc v]
    refine ⟨Subgroup.mem_inf.2 ⟨conj_mem_corrN (φ.torusElt_mem _) hv.1, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have heE : e ∈ conjSub E (φ.torusElt (Units.mk0 c hc)) := by
        rw [(φ.conjSub_torusElt _).2]
        exact he
      obtain ⟨e', he', rfl⟩ := mem_conjSub_iff.1 heE
      have h1 := Subgroup.mem_centralizer_iff.1 hv.2 e' he'
      calc φ.torusElt (Units.mk0 c hc) * e' * (φ.torusElt (Units.mk0 c hc))⁻¹ *
            (φ.torusElt (Units.mk0 c hc) * ↑(Additive.toMul v) *
              (φ.torusElt (Units.mk0 c hc))⁻¹) =
            φ.torusElt (Units.mk0 c hc) * (e' * ↑(Additive.toMul v)) *
              (φ.torusElt (Units.mk0 c hc))⁻¹ := by group
        _ = φ.torusElt (Units.mk0 c hc) * (↑(Additive.toMul v) * e') *
              (φ.torusElt (Units.mk0 c hc))⁻¹ := by rw [h1]
        _ = φ.torusElt (Units.mk0 c hc) * ↑(Additive.toMul v) *
              (φ.torusElt (Units.mk0 c hc))⁻¹ *
            (φ.torusElt (Units.mk0 c hc) * e' * (φ.torusElt (Units.mk0 c hc))⁻¹) := by group
    · rw [S.vecOf_torusElt htY φ hq hv, Units.val_mk0]

theorem exists_smul_eq {C : Subgroup G} {t : G} (S : TriangleSetting Δ A E C t)
    (htY : t ∈ A ⊔ E ⊔ C) {v w : Additive ↥(shortRootGroup Δ E A D E')}
    (hv : ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) ∈
      corrN A E t ⊓ Subgroup.centralizer (E : Set G)) (hv1 : v ≠ 0)
    (hw : ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G) ∈
      corrN A E t ⊓ Subgroup.centralizer (E : Set G)) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    ∃ c : GaloisField 2 k, w = c • v := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  set x : G := ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) with hx
  set y : G := ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G) with hy
  have hx1 : S.vecOf htY hq φ x 1 = 0 := ((S.vecOf_spec htY hq φ).2.2.2.2.2.1 hv.1).1
    fun e he => (Subgroup.mem_centralizer_iff.1 hv.2 e he).symm
  have hy1 : S.vecOf htY hq φ y 1 = 0 := ((S.vecOf_spec htY hq φ).2.2.2.2.2.1 hw.1).1
    fun e he => (Subgroup.mem_centralizer_iff.1 hw.2 e he).symm
  have hx0 : S.vecOf htY hq φ x 0 ≠ 0 := by
    intro h0
    have hz : S.vecOf htY hq φ x = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact hx1
    have hc := ((S.vecOf_spec htY hq φ).2.2.1 hv.1).1 hz
    have hxA : conjSub A x = A := conjSub_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.1 hc a (Subgroup.mem_sup_left ha)).symm
    apply hv1
    apply Additive.toMul.injective
    exact Subtype.ext (hX.2 x (v.toMul.2) hxA)
  refine ⟨S.vecOf htY hq φ y 0 / S.vecOf htY hq φ x 0, ?_⟩
  obtain ⟨hcN, hcv⟩ := F.vecOf_smul φ hΔ hiso hpts hq hX S htY v hv
    (S.vecOf htY hq φ y 0 / S.vecOf htY hq φ x 0)
  apply Additive.toMul.injective
  apply Subtype.ext
  refine eq_of_vecOf_eq φ hq hX S htY w.toMul.2 (((S.vecOf htY hq φ y 0 /
    S.vecOf htY hq φ x 0) • v).toMul.2) hw.1 hcN.1 ?_
  rw [hcv, div_mul_cancel₀ _ hx0]
  ext i
  fin_cases i
  · rfl
  · exact hy1

theorem card_shortRootGroup :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    Nat.card ↥(shortRootGroup Δ E A D E') =
      (2 ^ k) ^ Module.finrank (GaloisField 2 k) (Additive ↥(shortRootGroup Δ E A D E')) := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  have hk : k ≠ 0 := by
    rintro rfl
    have := φ.card_eq
    rw [pow_zero] at this
    omega
  have : Module.Finite (GaloisField 2 k) (Additive ↥(shortRootGroup Δ E A D E')) :=
    Module.Finite.of_finite
  rw [← GaloisField.card 2 k hk]
  exact Module.natCard_eq_pow_finrank (K := GaloisField 2 k)
    (V := Additive ↥(shortRootGroup Δ E A D E'))

theorem exists_smul_eq_torusElt (φ₁ : SL2Coords D E' k) (μ : (GaloisField 2 k)ˣ) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    ∃ a : GaloisField 2 k, ∀ v : Additive ↥(shortRootGroup Δ E A D E'),
      φ₁.torusElt μ * ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) * (φ₁.torusElt μ)⁻¹ =
        (((a • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  set h₁ := φ₁.torusElt μ with hh₁
  have hmem : ∀ x ∈ shortRootGroup Δ E A D E', h₁ * x * h₁⁻¹ ∈ shortRootGroup Δ E A D E' :=
    fun x hx => by
      have h := conj_mem_conjSub h₁ hx
      rwa [F.conjSub_shortRootGroup_torusElt' hΔ.root φ₁ μ] at h
  let ψ : Additive ↥(shortRootGroup Δ E A D E') →ₗ[GaloisField 2 k]
      Additive ↥(shortRootGroup Δ E A D E') :=
    { toFun := fun v => Additive.ofMul ⟨h₁ * (v.toMul : G) * h₁⁻¹, hmem _ v.toMul.2⟩
      map_add' := fun v w => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show h₁ * ((v.toMul : G) * w.toMul) * h₁⁻¹ =
          (h₁ * v.toMul * h₁⁻¹) * (h₁ * w.toMul * h₁⁻¹)
        group
      map_smul' := fun c v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show h₁ * (((c • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) * h₁⁻¹ =
          (((c • Additive.ofMul (⟨h₁ * (v.toMul : G) * h₁⁻¹, hmem _ v.toMul.2⟩ :
            ↥(shortRootGroup Δ E A D E'))).toMul : ↥(shortRootGroup Δ E A D E')) : G)
        by_cases hc : c = 0
        · subst hc
          rw [F.coe_zero_smul φ hΔ hiso hpts hq hX, F.coe_zero_smul φ hΔ hiso hpts hq hX]
          group
        · rw [F.coe_smul φ hΔ hiso hpts hq hX hc, F.coe_smul φ hΔ hiso hpts hq hX hc]
          have hcomm : Commute (φ.torusElt (Units.mk0 c hc)) h₁ :=
            F.comm _ (φ.torusElt_mem _) _ (φ₁.torusElt_mem μ)
          show h₁ * (φ.torusElt (Units.mk0 c hc) * (v.toMul : G) *
              (φ.torusElt (Units.mk0 c hc))⁻¹) * h₁⁻¹ =
            φ.torusElt (Units.mk0 c hc) * (h₁ * (v.toMul : G) * h₁⁻¹) *
              (φ.torusElt (Units.mk0 c hc))⁻¹
          calc h₁ * (φ.torusElt (Units.mk0 c hc) * (v.toMul : G) *
                (φ.torusElt (Units.mk0 c hc))⁻¹) * h₁⁻¹ =
                (h₁ * φ.torusElt (Units.mk0 c hc)) * (v.toMul : G) *
                  (h₁ * φ.torusElt (Units.mk0 c hc))⁻¹ := by group
            _ = (φ.torusElt (Units.mk0 c hc) * h₁) * (v.toMul : G) *
                  (φ.torusElt (Units.mk0 c hc) * h₁)⁻¹ := by rw [hcomm.eq]
            _ = φ.torusElt (Units.mk0 c hc) * (h₁ * (v.toMul : G) * h₁⁻¹) *
                  (φ.torusElt (Units.mk0 c hc))⁻¹ := by group }
  have key : ∀ v, ¬ LinearIndependent (GaloisField 2 k) ![v, ψ v] := by
    intro v hli
    by_cases hv : v = 0
    · exact hli.ne_zero 0 (by simp [hv])
    have hx1 : ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) ≠ 1 := fun h =>
      hv (Additive.toMul.injective (Subtype.ext h))
    obtain ⟨hC, hCA, hCD, -⟩ := hX.1 _ v.toMul.2 hx1
    obtain ⟨t, S, htY, hxN⟩ := F.exists_setting hΔ hiso hpts hX v.toMul.2 hx1
    have F' := F.toSp4Frame hC hCA hCD
    obtain ⟨t', ht'Y, S'⟩ := exists_triangleSetting hΔ hiso (F'.swap.isTriangle hΔ hpts)
    have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq F.memD F.memA]
    have hN := (F'.torus_spec_swap hpts S htY S' ht'Y hq (S'.coordsOf ht'Y hqD φ₁)
      (φ₁.torusElt_mem μ) (ν := μ) (φ₁.mat_torusElt μ)).2.2.2.2.1
    have hyN : h₁ * ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) * h₁⁻¹ ∈
        corrN A E t ⊓ Subgroup.centralizer (E : Set G) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h := conj_mem_conjSub h₁ hxN.1
        rwa [hN] at h
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        have h1 := Subgroup.mem_centralizer_iff.1 hxN.2 e he
        have h2 : Commute e h₁ := F.comm e (Subgroup.mem_sup_right he) _ (φ₁.torusElt_mem μ)
        set x : G := ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G)
        calc e * (h₁ * x * h₁⁻¹) = (e * h₁) * x * h₁⁻¹ := by group
          _ = (h₁ * e) * x * h₁⁻¹ := by rw [h2.eq]
          _ = h₁ * (e * x) * h₁⁻¹ := by group
          _ = h₁ * (x * e) * h₁⁻¹ := by rw [h1]
          _ = h₁ * x * h₁⁻¹ * (h₁ * e * h₁⁻¹) := by group
          _ = h₁ * x * h₁⁻¹ * e := by
            rw [show h₁ * e * h₁⁻¹ = e by rw [← h2.eq]; group]
    obtain ⟨c, hc⟩ := F.exists_smul_eq φ hΔ hiso hpts hq hX S htY (v := v) (w := ψ v) hxN hv hyN
    exact (LinearIndependent.pair_iff' hv).1 hli c hc.symm
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent key
  refine ⟨a, fun v => ?_⟩
  have h := LinearMap.congr_fun ha v
  exact congrArg (fun w : Additive ↥(shortRootGroup Δ E A D E') =>
    ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G)) h

theorem exists_monoidHom_torusElt (φ₁ : SL2Coords D E' k)
    (hX1 : ∃ x ∈ shortRootGroup Δ E A D E', x ≠ 1) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ hΔ hiso hpts hq hX
    ∃ κ : (GaloisField 2 k)ˣ →* (GaloisField 2 k)ˣ, ∀ (μ : (GaloisField 2 k)ˣ)
      (v : Additive ↥(shortRootGroup Δ E A D E')),
      φ₁.torusElt μ * ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) * (φ₁.torusElt μ)⁻¹ =
        ((((κ μ : GaloisField 2 k) • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) := by
  let _ := F.shortRootAddCommGroup hΔ
  let _ := F.shortRootModule φ hΔ hiso hpts hq hX
  choose a ha using F.exists_smul_eq_torusElt φ hΔ hiso hpts hq hX φ₁
  obtain ⟨x₀, hx₀, hx₀1⟩ := hX1
  set v₀ : Additive ↥(shortRootGroup Δ E A D E') := Additive.ofMul ⟨x₀, hx₀⟩
  have hv₀ : v₀ ≠ 0 := fun h => hx₀1 (congrArg (fun w : Additive ↥(shortRootGroup Δ E A D E') =>
    ((w.toMul : ↥(shortRootGroup Δ E A D E')) : G)) h)
  have hext : ∀ b b' : GaloisField 2 k, (((b • v₀).toMul : ↥(shortRootGroup Δ E A D E')) : G) =
      (((b' • v₀).toMul : ↥(shortRootGroup Δ E A D E')) : G) → b = b' := by
    intro b b' h
    have h1 : b • v₀ = b' • v₀ := Additive.toMul.injective (Subtype.ext h)
    have h2 : (b - b') • v₀ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv₀)
  have hne : ∀ μ, a μ ≠ 0 := by
    intro μ h0
    have h1 := ha μ v₀
    rw [h0, F.coe_zero_smul φ hΔ hiso hpts hq hX] at h1
    apply hx₀1
    have h2 : φ₁.torusElt μ * x₀ = φ₁.torusElt μ := by
      calc φ₁.torusElt μ * x₀ = φ₁.torusElt μ * x₀ * (φ₁.torusElt μ)⁻¹ * φ₁.torusElt μ := by
            group
        _ = φ₁.torusElt μ := by rw [show φ₁.torusElt μ * x₀ * (φ₁.torusElt μ)⁻¹ = 1 from h1,
            one_mul]
    exact mul_eq_left.1 h2
  refine ⟨{ toFun := fun μ => Units.mk0 (a μ) (hne μ), map_one' := ?_, map_mul' := ?_ },
    fun μ v => ?_⟩
  · apply Units.ext
    show a 1 = 1
    apply hext
    rw [← ha, one_smul, φ₁.torusElt_one]
    group
  · intro μ μ'
    apply Units.ext
    show a (μ * μ') = a μ * a μ'
    apply hext
    rw [mul_smul, ← ha, ← ha, ← ha, φ₁.torusElt_mul]
    group
  · exact ha μ v

end Module

end PairFrame

end CFSG.Timmesfeld.Transvection

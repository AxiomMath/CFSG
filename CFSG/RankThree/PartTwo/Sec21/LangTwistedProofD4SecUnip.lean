module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecTheta
public import CFSG.RankThree.Chevalley.SteinbergBID4RootOps
public import CFSG.Blueprint.ChevalleyRootArtifact

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley


@[expose] def secRep : Fin 6 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 1]]

@[expose] def secOrbit (j : Fin 6) : Finset (Fin TwistTag.D4.tag.rank → ℤ) :=
  TwistTag.D4.diagramOrbit (secRep j)

@[expose] def secVec : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]],
    ![![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1]],
    ![![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 0]]]

@[expose] def secTripleIdx : Fin 3 → Fin 6 :=
  ![0, 2, 3]

theorem isRoot_secRep (j : Fin 6) : IsRoot TwistTag.D4.tag (secRep j) := by
  refine (isRoot_iff_mem_artifactRoots).2 ?_
  revert j
  decide +kernel

theorem isRoot_secVec (j i : Fin 3) : IsRoot TwistTag.D4.tag (secVec j i) := by
  refine (isRoot_iff_mem_artifactRoots).2 ?_
  revert j i
  decide +kernel

theorem secOrbit_triple_eq : ∀ j : Fin 3,
    secOrbit (secTripleIdx j) = {secVec j 0, secVec j 1, secVec j 2} := by
  decide +kernel

theorem mem_secOrbit_triple (j : Fin 3) (α : Fin TwistTag.D4.tag.rank → ℤ) :
    α ∈ secOrbit (secTripleIdx j) ↔ α = secVec j 0 ∨ α = secVec j 1 ∨ α = secVec j 2 := by
  rw [secOrbit_triple_eq]
  simp

theorem permLattice_secVec : ∀ j : Fin 3,
    permLattice TwistTag.D4.perm (secVec j 0) = secVec j 1 ∧
      permLattice TwistTag.D4.perm (secVec j 1) = secVec j 2 ∧
        permLattice TwistTag.D4.perm (secVec j 2) = secVec j 0 := by
  decide +kernel

theorem height_secVec : ∀ j i : Fin 3, height (secVec j i) = (j : ℤ) + 1 := by
  decide +kernel

theorem secVec_nodup (j : Fin 3) : [secVec j 0, secVec j 1, secVec j 2].Nodup := by
  revert j
  decide +kernel

theorem secOrbit_single : ∀ j : Fin 6, j ∉ Set.range secTripleIdx →
    secOrbit j = {secRep j} ∧ permLattice TwistTag.D4.perm (secRep j) = secRep j ∧
      (height (secRep j) = 1 ∨ height (secRep j) = 4 ∨ height (secRep j) = 5) := by
  intro j hj
  fin_cases j
  · exact absurd ⟨0, rfl⟩ hj
  · decide +kernel
  · exact absurd ⟨1, rfl⟩ hj
  · exact absurd ⟨2, rfl⟩ hj
  · decide +kernel
  · decide +kernel

theorem disjoint_secOrbit : ∀ i j : Fin 6, i ≠ j → Disjoint (secOrbit i) (secOrbit j) := by
  decide +kernel

@[expose] def secRoot (k : Fin 24) : Fin TwistTag.D4.tag.rank → ℤ :=
  d4RootVec k

theorem secRoot_mem_secOrbit : ∀ k : Fin 24,
    0 < height (secRoot k) → ∃ j : Fin 6, secRoot k ∈ secOrbit j := by
  decide +kernel

theorem pos_iff_mem_secOrbit (α : Fin TwistTag.D4.tag.rank → ℤ) :
    (IsRoot TwistTag.D4.tag α ∧ 0 < height α) ↔ ∃ j, α ∈ secOrbit j := by
  constructor
  · rintro ⟨hα, hpos⟩
    obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
    exact secRoot_mem_secOrbit k hpos
  · rintro ⟨j, hj⟩
    refine ⟨TwistTag.D4.isRoot_of_mem_diagramOrbit (isRoot_secRep j) hj, ?_⟩
    rw [TwistTag.D4.height_of_mem_diagramOrbit hj]
    have h : ∀ j : Fin 6, 0 < height (secRep j) := by decide +kernel
    exact h j

theorem pos_of_mem_secOrbit {j : Fin 6} {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ secOrbit j) : IsRoot TwistTag.D4.tag α ∧ 0 < height α :=
  (pos_iff_mem_secOrbit α).2 ⟨j, hα⟩

theorem not_isRoot_of_mem_secOrbit (j : Fin 6) {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ secOrbit j) (hβ : β ∈ secOrbit j) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot TwistTag.D4.tag (a • α + b • β) :=
  TwistTag.D4.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit (isRoot_secRep j) hα hβ ha hb

variable {L : Type} [Field L]

theorem secElt_conj_mem_rootSpan_secOrbit (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 6)
    {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ))) :
    secElt μ * u * (secElt μ)⁻¹ ∈
      rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  have hle : rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ≤
      (rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ))).comap
        (MulAut.conj (secElt μ)).toMonoidHom := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      secElt_conj_pinnedX h2 μ (pos_of_mem_secOrbit hα).1]
    exact pinnedX_mem_rootSpan (TwistTag.D4.permLattice_mem_diagramOrbit hα) _
  exact hle hu

theorem secElt_conj_triple (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (c₀ c₁ c₂ : L) :
    secElt μ * (pinnedX TwistTag.D4.tag L (secVec j 0) c₀ *
        pinnedX TwistTag.D4.tag L (secVec j 1) c₁ * pinnedX TwistTag.D4.tag L (secVec j 2) c₂) *
        (secElt μ)⁻¹ =
      pinnedX TwistTag.D4.tag L (secVec j 0) (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₂) *
        pinnedX TwistTag.D4.tag L (secVec j 1) (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₀) *
          pinnedX TwistTag.D4.tag L (secVec j 2) (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₁) := by
  obtain ⟨p0, p1, p2⟩ := permLattice_secVec j
  have hc : ∀ (i k : Fin 3) (x y : L),
      Commute (pinnedX TwistTag.D4.tag L (secVec j i) x)
        (pinnedX TwistTag.D4.tag L (secVec j k) y) := by
    intro i k x y
    by_cases hik : i = k
    · subst hik
      change pinnedX TwistTag.D4.tag L (secVec j i) x * pinnedX TwistTag.D4.tag L (secVec j i) y =
        pinnedX TwistTag.D4.tag L (secVec j i) y * pinnedX TwistTag.D4.tag L (secVec j i) x
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · refine commute_pinnedX_of_rootForm_eq_zero L (isRoot_secVec j i) (isRoot_secVec j k) ?_ x y
      revert hik
      revert j i k
      decide +kernel
  have e : ∀ x y z : ModGL TwistTag.D4.tag L,
      secElt μ * (x * y * z) * (secElt μ)⁻¹ =
        (secElt μ * x * (secElt μ)⁻¹) * (secElt μ * y * (secElt μ)⁻¹) *
          (secElt μ * z * (secElt μ)⁻¹) := fun x y z => by group
  rw [e, secElt_conj_pinnedX h2 μ (isRoot_secVec j 0),
    secElt_conj_pinnedX h2 μ (isRoot_secVec j 1), secElt_conj_pinnedX h2 μ (isRoot_secVec j 2),
    p0, p1, p2, height_secVec, height_secVec, height_secVec]
  have hcomm := (hc 1 0 (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₀)
    (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₂)).mul_left
      (hc 2 0 (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₁) (((μ ^ ((j : ℤ) + 1) : Lˣ) : L) * c₂))
  rw [hcomm.eq, ← mul_assoc]

theorem secVec_ne : ∀ j : Fin 3,
    secVec j 1 ≠ secVec j 0 ∧ secVec j 2 ≠ secVec j 0 ∧ secVec j 2 ≠ secVec j 1 := by
  decide +kernel

theorem triple_injective (j : Fin 3) {x₀ x₁ x₂ y₀ y₁ y₂ : L}
    (h : pinnedX TwistTag.D4.tag L (secVec j 0) x₀ * pinnedX TwistTag.D4.tag L (secVec j 1) x₁ *
        pinnedX TwistTag.D4.tag L (secVec j 2) x₂ =
      pinnedX TwistTag.D4.tag L (secVec j 0) y₀ * pinnedX TwistTag.D4.tag L (secVec j 1) y₁ *
        pinnedX TwistTag.D4.tag L (secVec j 2) y₂) :
    x₀ = y₀ ∧ x₁ = y₁ ∧ x₂ = y₂ := by
  classical
  obtain ⟨h10, h20, h21⟩ := secVec_ne j
  set f : (Fin TwistTag.D4.tag.rank → ℤ) → L := fun α =>
    if α = secVec j 0 then x₀ else if α = secVec j 1 then x₁ else x₂ with hf
  set g : (Fin TwistTag.D4.tag.rank → ℤ) → L := fun α =>
    if α = secVec j 0 then y₀ else if α = secVec j 1 then y₁ else y₂ with hg
  have hprod : ∀ F : (Fin TwistTag.D4.tag.rank → ℤ) → L,
      ([secVec j 0, secVec j 1, secVec j 2].map fun α => pinnedX TwistTag.D4.tag L α (F α)).prod =
        pinnedX TwistTag.D4.tag L (secVec j 0) (F (secVec j 0)) *
          pinnedX TwistTag.D4.tag L (secVec j 1) (F (secVec j 1)) *
            pinnedX TwistTag.D4.tag L (secVec j 2) (F (secVec j 2)) := fun F => by
    simp [List.map, List.prod_cons, mul_assoc]
  have hpos : ∀ α ∈ [secVec j 0, secVec j 1, secVec j 2],
      IsRoot TwistTag.D4.tag α ∧ 0 < height α := by
    intro α hα
    refine pos_of_mem_secOrbit (j := secTripleIdx j) ?_
    rw [mem_secOrbit_triple]
    simpa using hα
  have key := pinnedX_list_prod_injective _ (secVec_nodup j) hpos f g (by
    rw [hprod, hprod]
    simp only [hf, hg, h10, h20, h21, ite_true, ite_false]
    simpa using h)
  have k0 := key (secVec j 0) (by simp)
  have k1 := key (secVec j 1) (by simp)
  have k2 := key (secVec j 2) (by simp)
  simp only [hf, hg, h10, h20, h21, ite_true, ite_false] at k0 k1 k2
  exact ⟨k0, k1, k2⟩

theorem exists_triple_eq (j : Fin 3) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L
      (secOrbit (secTripleIdx j) : Set (Fin TwistTag.D4.tag.rank → ℤ))) :
    ∃ c₀ c₁ c₂ : L, u = pinnedX TwistTag.D4.tag L (secVec j 0) c₀ *
      pinnedX TwistTag.D4.tag L (secVec j 1) c₁ * pinnedX TwistTag.D4.tag L (secVec j 2) c₂ := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq L
    (S := (secOrbit (secTripleIdx j) : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (fun α hα => pos_of_mem_secOrbit hα)
    (fun α hα β hβ a b ha hb hr => absurd hr (not_isRoot_of_mem_secOrbit _ hα hβ ha hb))
    (secVec_nodup j) (fun α => by
      rw [Finset.mem_coe, mem_secOrbit_triple]
      simp) hu
  refine ⟨c (secVec j 0), c (secVec j 1), c (secVec j 2), ?_⟩
  rw [← hc]
  simp [List.map, List.prod_cons, mul_assoc]

theorem exists_single_eq {j : Fin 6} (hj : secOrbit j = {secRep j}) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ))) :
    ∃ c : L, u = pinnedX TwistTag.D4.tag L (secRep j) c := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq L
    (S := (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (fun α hα => pos_of_mem_secOrbit hα)
    (fun α hα β hβ a b ha hb hr => absurd hr (not_isRoot_of_mem_secOrbit _ hα hβ ha hb))
    (List.nodup_singleton (secRep j)) (fun α => by
      rw [Finset.mem_coe, hj]
      simp) hu
  exact ⟨c (secRep j), by rw [← hc]; simp⟩

@[expose] def secKappa (μ : Lˣ) (j : Fin 3) : L :=
  ((μ ^ ((j : ℤ) + 1) : Lˣ) : L)

@[expose] def secOrbitX (μ : Lˣ) (j : Fin 3) (a : L) : ModGL TwistTag.D4.tag L :=
  pinnedX TwistTag.D4.tag L (secVec j 0) a *
    pinnedX TwistTag.D4.tag L (secVec j 1) (secKappa μ j * a) *
      pinnedX TwistTag.D4.tag L (secVec j 2) (secKappa μ j ^ 2 * a)

theorem pow_three_of_sq_add {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) : μ ^ 3 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination ((μ : L) - 1) * hμ)

theorem secKappa_pow_three {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3) : secKappa μ j ^ 3 = 1 := by
  rw [secKappa, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hμ3, one_zpow, Units.val_one]

theorem pow_ne_one_of_sq_add (h2 : (2 : L) = 0) {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {n : ℕ} (hn : n = 1 ∨ n = 4 ∨ n = 5) : ((μ ^ n : Lˣ) : L) ≠ 1 := by
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  have hμ1 : (μ : L) ≠ 1 := fun h => by
    rw [h] at hμ
    have : (1 : L) = 0 := by linear_combination hμ - h2
    exact one_ne_zero this
  have hμ2 : (μ : L) ^ 2 ≠ 1 := fun h => by
    apply hμ1
    calc (μ : L) = μ * μ ^ 2 := by rw [h, mul_one]
      _ = μ ^ 3 := by ring
      _ = 1 := h3
  rw [Units.val_pow_eq_pow_val]
  rcases hn with rfl | rfl | rfl
  · rwa [pow_one]
  · rw [show (μ : L) ^ 4 = μ ^ 3 * μ by ring, h3, one_mul]
    exact hμ1
  · rw [show (μ : L) ^ 5 = μ ^ 3 * μ ^ 2 by ring, h3, one_mul]
    exact hμ2

theorem eq_one_of_fixed_single (h2 : (2 : L) = 0) {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {j : Fin 6} (hj : j ∉ Set.range secTripleIdx) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L (secOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hfix : secElt μ * u * (secElt μ)⁻¹ = u) : u = 1 := by
  obtain ⟨hone, hρ, hht⟩ := secOrbit_single j hj
  obtain ⟨c, rfl⟩ := exists_single_eq hone hu
  rw [secElt_conj_pinnedX h2 μ (isRoot_secRep j) c, hρ] at hfix
  have hc := pinnedX_injective TwistTag.D4.tag L (secRep j) hfix
  have key : ∀ n : ℕ, (n = 1 ∨ n = 4 ∨ n = 5) → ((μ ^ (n : ℤ) : Lˣ) : L) ≠ 1 := fun n hn => by
    rw [zpow_natCast]
    exact pow_ne_one_of_sq_add h2 hμ hn
  have hne : ((μ ^ height (secRep j) : Lˣ) : L) ≠ 1 := by
    rcases hht with h | h | h <;> rw [h]
    · exact_mod_cast key 1 (Or.inl rfl)
    · exact_mod_cast key 4 (Or.inr (Or.inl rfl))
    · exact_mod_cast key 5 (Or.inr (Or.inr rfl))
  have hc0 : c = 0 := by
    have h' : (((μ ^ height (secRep j) : Lˣ) : L) - 1) * c = 0 := by linear_combination hc
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  rw [hc0, pinnedX_zero]

theorem eq_secOrbitX_of_fixed (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3)
    {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L
      (secOrbit (secTripleIdx j) : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hfix : secElt μ * u * (secElt μ)⁻¹ = u) : ∃ a : L, u = secOrbitX μ j a := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := exists_triple_eq j hu
  rw [secElt_conj_triple h2 μ j] at hfix
  obtain ⟨e0, e1, e2⟩ := triple_injective j hfix
  refine ⟨c₀, ?_⟩
  have e1' : secKappa μ j * c₀ = c₁ := e1
  have e2' : secKappa μ j ^ 2 * c₀ = c₂ := by
    rw [← e2, ← e1]
    change secKappa μ j ^ 2 * c₀ = secKappa μ j * (secKappa μ j * c₀)
    ring
  rw [secOrbitX, e1', e2']

theorem secElt_conj_list_prod (μ : Lˣ) (l : List (ModGL TwistTag.D4.tag L)) :
    (l.map fun x => secElt μ * x * (secElt μ)⁻¹).prod = secElt μ * l.prod * (secElt μ)⁻¹ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    group

theorem exists_eq_secOrbitX_of_fixed (h2 : (2 : L) = 0) {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ posUnipotent TwistTag.D4.tag L) (hfix : secElt μ * u * (secElt μ)⁻¹ = u) :
    ∃ a₀ a₁ a₂ : L, u = secOrbitX μ 0 a₀ * secOrbitX μ 1 a₁ * secOrbitX μ 2 a₂ := by
  set S := {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α}
    with hSdef
  have hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α ∧ 0 < height α := fun α hα => hα
  have hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.D4.tag (a • α + b • β) → a • α + b • β ∈ S :=
    fun α hα β hβ a b ha hb hr => by
      refine ⟨hr, ?_⟩
      rw [height_nsmul_add_nsmul]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith [hα.2, hβ.2]
  have hSO : ∀ α, α ∈ S ↔ ∃ j, α ∈ secOrbit j := fun α => pos_iff_mem_secOrbit α
  obtain ⟨v, hv, rfl⟩ := exists_prod_rootSpan_eq disjoint_secOrbit hS hclosed hSO hu
  have hθv : (fun j => secElt μ * v j * (secElt μ)⁻¹) = v := by
    refine eq_of_prod_rootSpan_eq disjoint_secOrbit (fun j α hα => pos_of_mem_secOrbit hα)
      (fun j α hα β hβ a b ha hb => not_isRoot_of_mem_secOrbit j hα hβ ha hb)
      (fun j => secElt_conj_mem_rootSpan_secOrbit h2 μ j (hv j)) hv ?_
    change (List.ofFn ((fun x => secElt μ * x * (secElt μ)⁻¹) ∘ v)).prod = _
    rw [← List.map_ofFn, secElt_conj_list_prod, hfix]
  have hfixj : ∀ j, secElt μ * v j * (secElt μ)⁻¹ = v j := fun j => congrFun hθv j
  have h1 : v 1 = 1 := eq_one_of_fixed_single h2 hμ (by decide) (hv 1) (hfixj 1)
  have h4 : v 4 = 1 := eq_one_of_fixed_single h2 hμ (by decide) (hv 4) (hfixj 4)
  have h5 : v 5 = 1 := eq_one_of_fixed_single h2 hμ (by decide) (hv 5) (hfixj 5)
  obtain ⟨a₀, h0⟩ := eq_secOrbitX_of_fixed h2 μ 0 (hv 0) (hfixj 0)
  obtain ⟨a₁, h2'⟩ := eq_secOrbitX_of_fixed h2 μ 1 (hv 2) (hfixj 2)
  obtain ⟨a₂, h3⟩ := eq_secOrbitX_of_fixed h2 μ 2 (hv 3) (hfixj 3)
  refine ⟨a₀, a₁, a₂, ?_⟩
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  change v 0 * (v 1 * (v 2 * (v 3 * (v 4 * (v 5 * 1))))) = _
  rw [h0, h1, h2', h3, h4, h5]
  group

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecUnip

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD

@[expose] def secSE : WeylGroup TwistTag.D4.tag :=
  simple TwistTag.D4.tag 0 * simple TwistTag.D4.tag 1 * simple TwistTag.D4.tag 3

@[expose] def secW : Fin 3 → WeylGroup TwistTag.D4.tag :=
  ![1, simple TwistTag.D4.tag 2, secSE * simple TwistTag.D4.tag 2]

@[expose] def secRefl (j : Fin 3) : WeylGroup TwistTag.D4.tag :=
  secW j * secSE * (secW j)⁻¹

@[expose] def secWA : Fin 6 → WeylGroup TwistTag.D4.tag :=
  ![1, secRefl 0, secRefl 1, secRefl 2, secRefl 0 * secRefl 1, secRefl 1 * secRefl 0]

@[expose] def secWAVec : Fin 6 → Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank → ℤ :=
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
    ![![-1, 0, 0, 0], ![0, -1, 0, 0], ![1, 1, 1, 1], ![0, 0, 0, -1]],
    ![![0, 1, 1, 1], ![1, 0, 1, 1], ![-1, -1, -2, -1], ![1, 1, 1, 0]],
    ![![-1, 0, -1, 0], ![0, -1, -1, 0], ![0, 0, 1, 0], ![0, 0, -1, -1]],
    ![![1, 0, 1, 0], ![0, 1, 1, 0], ![-1, -1, -2, -1], ![0, 0, 1, 1]],
    ![![0, -1, -1, -1], ![-1, 0, -1, -1], ![1, 1, 1, 1], ![-1, -1, -1, 0]]]

theorem simple_inv_D4 (i : Fin TwistTag.D4.tag.rank) :
    (simple TwistTag.D4.tag i)⁻¹ = simple TwistTag.D4.tag i :=
  (coxeterSystem TwistTag.D4.tag).inv_simple i

set_option linter.unusedSimpArgs false in
theorem secWA_smul (k : Fin 6) (i : Fin TwistTag.D4.tag.rank) :
    secWA k • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = secWAVec k i := by
  fin_cases k <;>
    simp only [secWA, secRefl, secW, secSE, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, mul_inv_rev, inv_one, simple_inv_D4, mul_one,
      one_mul, mul_smul, simple_smul, one_smul] <;>
    revert i <;> decide +kernel

set_option linter.unusedSimpArgs false in
theorem secW_smul (j : Fin 3) (i : Fin 3) :
    secW j • (Pi.single (![0, 1, 3] i) 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j i := by
  fin_cases j <;>
    simp only [secW, secSE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_smul, simple_smul, one_smul] <;>
    revert i <;> decide +kernel

variable {L : Type} [Field L]

theorem commute_secVec (j : Fin 3) {i k : Fin 3} (ε δ : Bool) (hik : i ≠ k ∨ ε = δ)
    (x y : L) :
    Commute (pinnedX TwistTag.D4.tag L (if ε then secVec j i else -secVec j i) x)
      (pinnedX TwistTag.D4.tag L (if δ then secVec j k else -secVec j k) y) := by
  by_cases hik' : i = k ∧ ε = δ
  · obtain ⟨rfl, rfl⟩ := hik'
    change pinnedX TwistTag.D4.tag L _ x * pinnedX TwistTag.D4.tag L _ y =
      pinnedX TwistTag.D4.tag L _ y * pinnedX TwistTag.D4.tag L _ x
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hroot : ∀ (v : Fin TwistTag.D4.tag.rank → ℤ) (b : Bool), IsRoot TwistTag.D4.tag v →
        IsRoot TwistTag.D4.tag (if b then v else -v) := fun v b hv => by
      cases b
      · exact IsRoot.neg hv
      · exact hv
    refine commute_pinnedX_of_rootForm_eq_zero L (hroot _ ε (isRoot_secVec j i))
      (hroot _ δ (isRoot_secVec j k)) ?_ x y
    have hne : i ≠ k := fun h => by
      rcases hik with h' | h'
      · exact h' h
      · exact hik' ⟨h, h'⟩
    revert hne
    revert j i k ε δ
    decide +kernel

theorem commute_secVec_pp (j : Fin 3) {i k : Fin 3} (x y : L) :
    Commute (pinnedX TwistTag.D4.tag L (secVec j i) x)
      (pinnedX TwistTag.D4.tag L (secVec j k) y) := by
  simpa using commute_secVec (L := L) j (i := i) (k := k) true true (Or.inr rfl) x y

theorem commute_secVec_nn (j : Fin 3) {i k : Fin 3} (x y : L) :
    Commute (pinnedX TwistTag.D4.tag L (-secVec j i) x)
      (pinnedX TwistTag.D4.tag L (-secVec j k) y) := by
  simpa using commute_secVec (L := L) j (i := i) (k := k) false false (Or.inr rfl) x y

theorem commute_secVec_np (j : Fin 3) {i k : Fin 3} (hik : i ≠ k) (x y : L) :
    Commute (pinnedX TwistTag.D4.tag L (-secVec j i) x)
      (pinnedX TwistTag.D4.tag L (secVec j k) y) := by
  simpa using commute_secVec (L := L) j (i := i) (k := k) false true (Or.inl hik) x y

theorem commute_secVec_pn (j : Fin 3) {i k : Fin 3} (hik : i ≠ k) (x y : L) :
    Commute (pinnedX TwistTag.D4.tag L (secVec j i) x)
      (pinnedX TwistTag.D4.tag L (-secVec j k) y) := by
  simpa using commute_secVec (L := L) j (i := i) (k := k) true false (Or.inl hik) x y

theorem rearrange_three {G : Type*} [Group G] {x₀ x₁ x₂ y₀ y₁ y₂ : G}
    (h01 : Commute x₀ x₁) (h02 : Commute x₀ x₂) (h12 : Commute x₁ x₂)
    (hy0x1 : Commute y₀ x₁) (hy0x2 : Commute y₀ x₂) (hx0y1 : Commute x₀ y₁)
    (hx0y2 : Commute x₀ y₂) (hy1x2 : Commute y₁ x₂) (hx1y2 : Commute x₁ y₂) :
    x₀ * x₁ * x₂ * (y₀ * y₁ * y₂) * (x₀ * x₁ * x₂) =
      (x₀ * y₀ * x₀) * (x₁ * y₁ * x₁) * (x₂ * y₂ * x₂) := by
  have c1 : Commute y₀ (x₁ * x₂) := hy0x1.mul_right hy0x2
  have c2 : Commute x₀ (x₁ * x₂ * (y₁ * y₂)) :=
    (h01.mul_right h02).mul_right (hx0y1.mul_right hx0y2)
  have c4 : Commute x₁ (x₂ * y₂) := h12.mul_right hx1y2
  calc x₀ * x₁ * x₂ * (y₀ * y₁ * y₂) * (x₀ * x₁ * x₂)
      = x₀ * ((x₁ * x₂) * y₀) * (y₁ * y₂) * x₀ * (x₁ * x₂) := by group
    _ = x₀ * (y₀ * (x₁ * x₂)) * (y₁ * y₂) * x₀ * (x₁ * x₂) := by rw [← c1.eq]
    _ = x₀ * y₀ * ((x₁ * x₂ * (y₁ * y₂)) * x₀) * (x₁ * x₂) := by group
    _ = x₀ * y₀ * (x₀ * (x₁ * x₂ * (y₁ * y₂))) * (x₁ * x₂) := by rw [← c2.eq]
    _ = x₀ * y₀ * x₀ * (x₁ * (x₂ * y₁) * y₂ * x₁ * x₂) := by group
    _ = x₀ * y₀ * x₀ * (x₁ * (y₁ * x₂) * y₂ * x₁ * x₂) := by rw [← hy1x2.eq]
    _ = x₀ * y₀ * x₀ * (x₁ * y₁ * ((x₂ * y₂) * x₁) * x₂) := by group
    _ = x₀ * y₀ * x₀ * (x₁ * y₁ * (x₁ * (x₂ * y₂)) * x₂) := by rw [← c4.eq]
    _ = (x₀ * y₀ * x₀) * (x₁ * y₁ * x₁) * (x₂ * y₂ * x₂) := by group

@[expose] def secOrbitY (μ : Lˣ) (j : Fin 3) (a : L) : ModGL TwistTag.D4.tag L :=
  pinnedX TwistTag.D4.tag L (-secVec j 0) a *
    pinnedX TwistTag.D4.tag L (-secVec j 1) (secKappa μ j ^ 2 * a) *
      pinnedX TwistTag.D4.tag L (-secVec j 2) (secKappa μ j * a)

theorem secKappa_inv {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3) :
    ((μ ^ (-((j : ℤ) + 1)) : Lˣ) : L) = secKappa μ j ^ 2 := by
  have h3 := secKappa_pow_three hμ3 j
  have hne : secKappa μ j ≠ 0 := by rw [secKappa]; exact Units.ne_zero _
  rw [zpow_neg, Units.val_inv_eq_inv_val]
  change (secKappa μ j)⁻¹ = _
  exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)).symm

theorem secElt_conj_secOrbitY (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3)
    (a : L) : secElt μ * secOrbitY μ j a * (secElt μ)⁻¹ = secOrbitY μ j a := by
  obtain ⟨p0, p1, p2⟩ := permLattice_secVec j
  have h3 := secKappa_pow_three hμ3 j
  have hneg : ∀ i, height (-secVec j i) = -((j : ℤ) + 1) := fun i => by
    rw [CFSG.LieType.Chevalley.height_neg, height_secVec]
  have e : ∀ x y z : ModGL TwistTag.D4.tag L,
      secElt μ * (x * y * z) * (secElt μ)⁻¹ =
        (secElt μ * x * (secElt μ)⁻¹) * (secElt μ * y * (secElt μ)⁻¹) *
          (secElt μ * z * (secElt μ)⁻¹) := fun x y z => by group
  rw [secOrbitY, e, secElt_conj_pinnedX h2 μ (IsRoot.neg (isRoot_secVec j 0)),
    secElt_conj_pinnedX h2 μ (IsRoot.neg (isRoot_secVec j 1)),
    secElt_conj_pinnedX h2 μ (IsRoot.neg (isRoot_secVec j 2)), permLattice_neg, permLattice_neg,
    permLattice_neg, p0, p1, p2, hneg, hneg, hneg, secKappa_inv hμ3]
  have hc := (commute_secVec (L := L) j (i := 1) (k := 0) false false (Or.inl (by decide))
    (secKappa μ j ^ 2 * a) (secKappa μ j ^ 2 * (secKappa μ j * a))).mul_left
      (commute_secVec (L := L) j (i := 2) (k := 0) false false (Or.inl (by decide))
        (secKappa μ j ^ 2 * (secKappa μ j ^ 2 * a)) (secKappa μ j ^ 2 * (secKappa μ j * a)))
  simp only [Bool.false_eq_true, ite_false] at hc
  rw [hc.eq, ← mul_assoc]
  have e1 : secKappa μ j ^ 2 * (secKappa μ j * a) = a := by
    linear_combination a * h3
  have e2 : secKappa μ j ^ 2 * (secKappa μ j ^ 2 * a) = secKappa μ j * a := by
    linear_combination (secKappa μ j * a) * h3
  rw [e1, e2]

theorem secElt_conj_secOrbitX (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3)
    (a : L) : secElt μ * secOrbitX μ j a * (secElt μ)⁻¹ = secOrbitX μ j a := by
  have h3 := secKappa_pow_three hμ3 j
  rw [secOrbitX, secElt_conj_triple h2 μ j]
  change pinnedX TwistTag.D4.tag L (secVec j 0) (secKappa μ j * (secKappa μ j ^ 2 * a)) *
      pinnedX TwistTag.D4.tag L (secVec j 1) (secKappa μ j * a) *
        pinnedX TwistTag.D4.tag L (secVec j 2) (secKappa μ j * (secKappa μ j * a)) = _
  have e1 : secKappa μ j * (secKappa μ j ^ 2 * a) = a := by linear_combination a * h3
  have e2 : secKappa μ j * (secKappa μ j * a) = secKappa μ j ^ 2 * a := by ring
  rw [e1, e2]

theorem prod_three_mul {G : Type*} [Group G] {a₀ a₁ a₂ b₀ b₁ b₂ : G}
    (h10 : Commute a₁ b₀) (h20 : Commute a₂ b₀) (h21 : Commute a₂ b₁) :
    a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) = (a₀ * b₀) * (a₁ * b₁) * (a₂ * b₂) := by
  have c : Commute (a₁ * a₂) b₀ := h10.mul_left h20
  calc a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) = a₀ * ((a₁ * a₂) * b₀) * b₁ * b₂ := by group
    _ = a₀ * (b₀ * (a₁ * a₂)) * b₁ * b₂ := by rw [c.eq]
    _ = a₀ * b₀ * a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₀ * b₀ * a₁ * (b₁ * a₂) * b₂ := by rw [h21.eq]
    _ = _ := by group

theorem secOrbitX_add (μ : Lˣ) (j : Fin 3) (a a' : L) :
    secOrbitX μ j (a + a') = secOrbitX μ j a * secOrbitX μ j a' := by
  have hc := fun (i k : Fin 3) (hik : i ≠ k) (x y : L) =>
    commute_secVec (L := L) j (i := i) (k := k) true true (Or.inl hik) x y
  simp only [ite_true] at hc
  rw [secOrbitX, secOrbitX, secOrbitX, prod_three_mul (hc 1 0 (by decide) _ _)
    (hc 2 0 (by decide) _ _) (hc 2 1 (by decide) _ _), ← pinnedX_add, ← pinnedX_add,
    ← pinnedX_add, mul_add, mul_add]

theorem secOrbitY_add (μ : Lˣ) (j : Fin 3) (a a' : L) :
    secOrbitY μ j (a + a') = secOrbitY μ j a * secOrbitY μ j a' := by
  have hc := fun (i k : Fin 3) (hik : i ≠ k) (x y : L) =>
    commute_secVec (L := L) j (i := i) (k := k) false false (Or.inl hik) x y
  simp only [Bool.false_eq_true, ite_false] at hc
  rw [secOrbitY, secOrbitY, secOrbitY, prod_three_mul (hc 1 0 (by decide) _ _)
    (hc 2 0 (by decide) _ _) (hc 2 1 (by decide) _ _), ← pinnedX_add, ← pinnedX_add,
    ← pinnedX_add, mul_add, mul_add]

@[expose] def secOrbitXHom (μ : Lˣ) (j : Fin 3) : Multiplicative L →* ModGL TwistTag.D4.tag L where
  toFun a := secOrbitX μ j a.toAdd
  map_one' := by simp [secOrbitX, pinnedX_zero]
  map_mul' a a' := secOrbitX_add μ j a.toAdd a'.toAdd

@[expose] def secOrbitYHom (μ : Lˣ) (j : Fin 3) : Multiplicative L →* ModGL TwistTag.D4.tag L where
  toFun a := secOrbitY μ j a.toAdd
  map_one' := by simp [secOrbitY, pinnedX_zero]
  map_mul' a a' := secOrbitY_add μ j a.toAdd a'.toAdd

@[expose] def secH (μ : Lˣ) : Option (Fin 3 × Bool) → Subgroup (ModGL TwistTag.D4.tag L)
  | none => torusGroup TwistTag.D4.tag L ⊓
      graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L)
  | some (j, true) => (secOrbitXHom μ j).range
  | some (j, false) => (secOrbitYHom μ j).range

@[expose] def secM (μ : Lˣ) : Subgroup (ModGL TwistTag.D4.tag L) :=
  ⨆ o, secH μ o

theorem secOrbitX_mem_secM (μ : Lˣ) (j : Fin 3) (a : L) : secOrbitX μ j a ∈ secM μ :=
  Subgroup.mem_iSup_of_mem (some (j, true)) ⟨Multiplicative.ofAdd a, rfl⟩

theorem secOrbitY_mem_secM (μ : Lˣ) (j : Fin 3) (a : L) : secOrbitY μ j a ∈ secM μ :=
  Subgroup.mem_iSup_of_mem (some (j, false)) ⟨Multiplicative.ofAdd a, rfl⟩

theorem mem_secM_of_mem_torus (μ : Lˣ) {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L)
    (htP : t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L)) : t ∈ secM μ :=
  Subgroup.mem_iSup_of_mem none (Subgroup.mem_inf.2 ⟨ht, htP⟩)

theorem secElt_conj_torus (μ : Lˣ) {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    secElt μ * t * (secElt μ)⁻¹ = diagramMap TwistTag.D4 L * t * (diagramMap TwistTag.D4 L)⁻¹ := by
  rw [secElt_conj_eq, twistHom_id_eq]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (twistHom_mem_torusGroup' (RingHom.id L).surjective ht)
  rw [twistHom_id_eq] at ha
  rw [ha, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm (secTuple μ) a,
    mul_assoc, mul_inv_cancel, mul_one]

theorem secM_le (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) :
    secM μ ≤ graphCentralizer TwistTag.D4.tag L (secElt μ) := by
  have hfix : ∀ g, g ∈ adjointGroup TwistTag.D4.tag L → secElt μ * g * (secElt μ)⁻¹ = g →
      g ∈ graphCentralizer TwistTag.D4.tag L (secElt μ) := fun g hg hfg => by
    refine Subgroup.mem_inf.2 ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * secElt μ = secElt μ * g * (secElt μ)⁻¹ * secElt μ := by rw [hfg]
      _ = secElt μ * g := by group
  refine iSup_le fun o => ?_
  rcases o with _ | ⟨j, _ | _⟩
  · intro t ht
    obtain ⟨htT, htP⟩ := Subgroup.mem_inf.1 ht
    obtain ⟨htG, htc⟩ := Subgroup.mem_inf.1 htP
    rw [Subgroup.mem_centralizer_singleton_iff] at htc
    refine hfix t htG ?_
    rw [secElt_conj_torus μ htT, ← htc, mul_inv_cancel_right]
  · rintro _ ⟨a, rfl⟩
    refine hfix _ ?_ (secElt_conj_secOrbitY h2 hμ3 j a.toAdd)
    exact mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)
  · rintro _ ⟨a, rfl⟩
    refine hfix _ ?_ (secElt_conj_secOrbitX h2 hμ3 j a.toAdd)
    exact mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)

theorem mapsRootLines_weylElt_unit' (i : Fin TwistTag.D4.tag.rank) (t : Lˣ) :
    MapsRootLines (weylElt TwistTag.D4.tag L i t) (simple TwistTag.D4.tag i) := by
  rw [weylElt_eq_torusElt_mul_weylElt_one]
  simpa using (mapsRootLines_of_mem_torusGroup (torusElt_mem_torusGroup i t)).mul
    (mapsRootLines_weylElt (R := L) i)

theorem weylElt_mem_monomialSubgroup' (i : Fin TwistTag.D4.tag.rank) (t : Lˣ) :
    weylElt TwistTag.D4.tag L i t ∈ monomialSubgroup TwistTag.D4.tag L := by
  rw [weylElt_eq_torusElt_mul_weylElt_one]
  exact mul_mem (torusElt_mem_monomialSubgroup i t) (weylElt_mem_monomialSubgroup i)

theorem canonicalRep_conj_weylElt (h2 : (2 : L) = 0) (w : WeylGroup TwistTag.D4.tag)
    (i : Fin TwistTag.D4.tag.rank) (t : Lˣ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L w * weylElt TwistTag.D4.tag L i t *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ =
      pinnedX TwistTag.D4.tag L (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) t *
        pinnedX TwistTag.D4.tag L (-(w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)))
          ((t⁻¹ : Lˣ) : L) *
        pinnedX TwistTag.D4.tag L (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) t := by
  have hneg : -((t⁻¹ : Lˣ) : L) = ((t⁻¹ : Lˣ) : L) := by
    linear_combination (-((t⁻¹ : Lˣ) : L)) * h2
  rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, hneg, ← pinnedX_single, ← pinnedX_neg_single]
  have e : ∀ a b c : ModGL TwistTag.D4.tag L,
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w * (a * b * c) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * a *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * b *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * c *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹) := fun a b c => by group
  rw [e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ i),
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (IsRoot.neg (isRoot_single _ i)), smul_neg]

@[expose] def secLift (μ : Lˣ) (j : Fin 3) : ModGL TwistTag.D4.tag L :=
  secOrbitX μ j 1 * secOrbitY μ j 1 * secOrbitX μ j 1

theorem secLift_mem_secM (μ : Lˣ) (j : Fin 3) : secLift μ j ∈ secM μ :=
  mul_mem (mul_mem (secOrbitX_mem_secM μ j 1) (secOrbitY_mem_secM μ j 1))
    (secOrbitX_mem_secM μ j 1)

theorem secLift_eq (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3) :
    secLift μ j = canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) *
      (weylElt TwistTag.D4.tag L 0 1 * weylElt TwistTag.D4.tag L 1 (μ ^ ((j : ℤ) + 1)) *
        weylElt TwistTag.D4.tag L 3 ((μ ^ ((j : ℤ) + 1)) ^ 2)) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j))⁻¹ := by
  set u : Lˣ := μ ^ ((j : ℤ) + 1) with hu
  have hκ : secKappa μ j = (u : L) := rfl
  have h3 : (u : L) ^ 3 = 1 := by rw [← hκ]; exact secKappa_pow_three hμ3 j
  have hu1 : ((u⁻¹ : Lˣ) : L) = (u : L) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)).symm
  have hu2 : (((u ^ 2)⁻¹ : Lˣ) : L) = (u : L) := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact h3)).symm
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) with hn
  have e : ∀ a b c : ModGL TwistTag.D4.tag L,
      n * (a * b * c) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) * (n * c * n⁻¹) := fun a b c => by
    group
  have hv0 : secW j • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 0 := secW_smul j 0
  have hv1 : secW j • (Pi.single 1 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 1 := secW_smul j 1
  have hv3 : secW j • (Pi.single 3 1 : Fin TwistTag.D4.tag.rank → ℤ) = secVec j 2 := secW_smul j 2
  rw [e, hn, canonicalRep_conj_weylElt h2, canonicalRep_conj_weylElt h2,
    canonicalRep_conj_weylElt h2, hv0, hv1, hv3, hu1, hu2, inv_one, Units.val_one,
    Units.val_pow_eq_pow_val]
  rw [secLift, secOrbitX, secOrbitY, hκ]
  simp only [mul_one]
  rw [rearrange_three (commute_secVec_pp j _ _) (commute_secVec_pp j _ _)
      (commute_secVec_pp j _ _) (commute_secVec_np j (by decide) _ _)
      (commute_secVec_np j (by decide) _ _) (commute_secVec_pn j (by decide) _ _)
      (commute_secVec_pn j (by decide) _ _) (commute_secVec_np j (by decide) _ _)
      (commute_secVec_pn j (by decide) _ _)]

theorem mapsRootLines_secLift (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (j : Fin 3) :
    MapsRootLines (secLift μ j) (secRefl j) := by
  rw [secLift_eq h2 hμ3 j, secRefl, secSE]
  exact ((mapsRootLines_canonicalRep (R := L) (secW j)).mul
    (((mapsRootLines_weylElt_unit' 0 1).mul (mapsRootLines_weylElt_unit' 1 _)).mul
      (mapsRootLines_weylElt_unit' 3 _))).mul (mapsRootLines_canonicalRep (R := L) (secW j)).inv

theorem secLift_mem_monomialSubgroup (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1)
    (j : Fin 3) : secLift μ j ∈ monomialSubgroup TwistTag.D4.tag L := by
  rw [secLift_eq h2 hμ3 j]
  exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L _)
    (mul_mem (mul_mem (weylElt_mem_monomialSubgroup' 0 1) (weylElt_mem_monomialSubgroup' 1 _))
      (weylElt_mem_monomialSubgroup' 3 _))) (inv_mem (canonicalRep_mem_monomialSubgroup L _))

@[expose] def secWALift (μ : Lˣ) : Fin 6 → ModGL TwistTag.D4.tag L :=
  ![1, secLift μ 0, secLift μ 1, secLift μ 2, secLift μ 0 * secLift μ 1,
    secLift μ 1 * secLift μ 0]

theorem secWALift_spec (h2 : (2 : L) = 0) {μ : Lˣ} (hμ3 : μ ^ 3 = 1) (k : Fin 6) :
    secWALift μ k ∈ secM μ ∧ secWALift μ k ∈ monomialSubgroup TwistTag.D4.tag L ∧
      MapsRootLines (secWALift μ k) (secWA k) := by
  have hM := secLift_mem_secM (L := L) μ
  have hN := secLift_mem_monomialSubgroup (L := L) h2 hμ3
  have hR := mapsRootLines_secLift (L := L) h2 hμ3
  fin_cases k
  · exact ⟨one_mem _, one_mem _, mapsRootLines_one⟩
  · exact ⟨hM 0, hN 0, hR 0⟩
  · exact ⟨hM 1, hN 1, hR 1⟩
  · exact ⟨hM 2, hN 2, hR 2⟩
  · exact ⟨mul_mem (hM 0) (hM 1), mul_mem (hN 0) (hN 1), (hR 0).mul (hR 1)⟩
  · exact ⟨mul_mem (hM 1) (hM 0), mul_mem (hN 1) (hN 0), (hR 1).mul (hR 0)⟩

@[expose] def secTabCol (e : ℕ) (i : Fin TwistTag.D4.tag.rank) : Fin TwistTag.D4.tag.rank → ℤ :=
  d4RootVec (d4Dig i (d4TupCode e))

theorem secWA_tab_check : ∀ e ∈ d4WeylTab,
    (∀ i, secTabCol e (TwistTag.D4.perm i) = permLattice TwistTag.D4.perm (secTabCol e i)) →
    (3 : ℤ) ∣ height (secTabCol e 2) - 1 →
    (3 : ℤ) ∣ height (secTabCol e 0) + height (secTabCol e 1) + height (secTabCol e 3) →
    ∃ k : Fin 6, ∀ i, secTabCol e i = secWAVec k i := by
  decide +kernel

theorem three_dvd_of_zpow_eq_one (h2 : (2 : L) = 0) {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {k : ℤ} (hk : μ ^ k = 1) : (3 : ℤ) ∣ k := by
  have hμ3 := pow_three_of_sq_add hμ
  have hμ1 : μ ≠ 1 := fun h => by
    have := pow_ne_one_of_sq_add h2 hμ (n := 1) (Or.inl rfl)
    rw [h, one_pow, Units.val_one] at this
    exact this rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf μ = 3 := orderOf_eq_prime hμ3 hμ1
  have h := orderOf_dvd_iff_zpow_eq_one.2 hk
  rw [hord] at h
  exact_mod_cast h

theorem mem_secM_of_fixed_monomial (h2 : (2 : L) = 0) {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTwist TwistTag.D4 w = w) {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ torusGroup TwistTag.D4.tag L)
    (hfix : secElt μ * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) * (secElt μ)⁻¹ =
      h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) :
    h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈ secM μ := by
  have hμ3 := pow_three_of_sq_add hμ
  obtain ⟨p0, p1, p2, p3⟩ := d4_perm_values
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  set f := secTuple μ * (weylTuple w (secTuple μ))⁻¹ with hf
  have htuple : (fun i => a (TwistTag.D4.perm.symm i)) * f = a := by
    have h1 : secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹ =
        rootDiagUnit TwistTag.D4.tag ((fun i => a (TwistTag.D4.perm.symm i)) * f) * n := by
      calc secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹ =
          (secElt μ * rootDiagUnit TwistTag.D4.tag a * (secElt μ)⁻¹) *
            (secElt μ * n * (secElt μ)⁻¹) := by group
        _ = _ := by
          rw [secElt_conj_rootDiagUnit, hn, secElt_conj_canonicalRep μ hw, ← mul_assoc,
            ← rootDiagUnit_mul]
    rw [h1] at hfix
    exact rootDiagUnit_injective (mul_right_cancel hfix)
  have hfi : ∀ i,
      f i = μ ^ (1 - height (w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ))) := by
    intro i
    simp only [hf, Pi.mul_apply, Pi.inv_apply, weylTuple, rootChar_secTuple]
    rw [zpow_sub, zpow_one]
    rfl
  have hc := fun i => congrFun htuple i
  simp only [Pi.mul_apply] at hc
  have hρs : TwistTag.D4.perm.symm 2 = 2 ∧ TwistTag.D4.perm.symm 0 = 3 ∧
      TwistTag.D4.perm.symm 1 = 0 ∧ TwistTag.D4.perm.symm 3 = 1 := by decide
  obtain ⟨s2, s0, s1, s3⟩ := hρs
  have hf2 : f 2 = 1 := by
    have := hc 2
    rw [s2] at this
    exact mul_eq_left.1 this
  have hf013 : f 0 * f 1 * f 3 = 1 := by
    have e0 := hc 0
    have e1 := hc 1
    have e3 := hc 3
    rw [s0] at e0
    rw [s1] at e1
    rw [s3] at e3
    have : (a 3 * f 0) * (a 0 * f 1) * (a 1 * f 3) = a 0 * a 1 * a 3 := by rw [e0, e1, e3]
    have e : (a 3 * f 0) * (a 0 * f 1) * (a 1 * f 3) = (a 0 * a 1 * a 3) * (f 0 * f 1 * f 3) := by
      simp only [mul_left_comm, mul_assoc]
    rw [e] at this
    exact mul_eq_left.1 this
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab (w⁻¹ : WeylGroup Tag.D4)
  have hwe' : ∀ i, w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = secTabCol e i := hwe
  have hcomm : ∀ i, secTabCol e (TwistTag.D4.perm i) =
      permLattice TwistTag.D4.perm (secTabCol e i) := by
    intro i
    have hwinv : weylTwist TwistTag.D4 w⁻¹ = w⁻¹ := by rw [map_inv, hw]
    rw [← hwe', ← hwe', ← permLattice_single, ← weylTwist_smul_permLattice, hwinv]
  have hcond2 : (3 : ℤ) ∣ height (secTabCol e 2) - 1 := by
    have h := three_dvd_of_zpow_eq_one h2 hμ (k := 1 - height (secTabCol e 2)) (by
      rw [← hwe', ← hfi, hf2])
    rw [show height (secTabCol e 2) - 1 = -(1 - height (secTabCol e 2)) by ring]
    exact dvd_neg.2 h
  have hcond013 : (3 : ℤ) ∣ height (secTabCol e 0) + height (secTabCol e 1) +
      height (secTabCol e 3) := by
    have h := three_dvd_of_zpow_eq_one h2 hμ
      (k := 3 - (height (secTabCol e 0) + height (secTabCol e 1) + height (secTabCol e 3))) (by
        rw [← hwe', ← hwe', ← hwe', show (3 : ℤ) - (height (w⁻¹ • (Pi.single 0 1 :
          Fin TwistTag.D4.tag.rank → ℤ)) + height (w⁻¹ • (Pi.single 1 1 :
            Fin TwistTag.D4.tag.rank → ℤ)) + height (w⁻¹ • (Pi.single 3 1 :
              Fin TwistTag.D4.tag.rank → ℤ))) = (1 - height (w⁻¹ • (Pi.single 0 1 :
          Fin TwistTag.D4.tag.rank → ℤ))) + (1 - height (w⁻¹ • (Pi.single 1 1 :
            Fin TwistTag.D4.tag.rank → ℤ))) + (1 - height (w⁻¹ • (Pi.single 3 1 :
              Fin TwistTag.D4.tag.rank → ℤ))) by ring, zpow_add, zpow_add, ← hfi, ← hfi, ← hfi,
          hf013])
    have h3 : (3 : ℤ) ∣ 3 := dvd_refl 3
    have := dvd_sub h3 h
    simpa using this
  obtain ⟨k, hk⟩ := secWA_tab_check e he hcomm hcond2 hcond013
  have hwk : w⁻¹ = secWA k := ext_single fun i => (hwe' i).trans ((hk i).trans
    (secWA_smul k i).symm)
  obtain ⟨hlM, hlN, hlR⟩ := secWALift_spec h2 hμ3 k (L := L)
  rw [← hwk] at hlR
  set l := secWALift μ k with hl
  set t := rootDiagUnit TwistTag.D4.tag a * n * l with ht
  have htN : t ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (Subgroup.mem_sup_left hh) (canonicalRep_mem_monomialSubgroup L w)) hlN
  have htR : MapsRootLines t 1 := by
    have := ((mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep (R := L) w)).mul
      hlR
    rwa [one_mul, mul_inv_cancel] at this
  have htT : t ∈ torusGroup TwistTag.D4.tag L := by
    obtain ⟨w', k', hk', hgk⟩ := monomialSubgroup_le_torusWeylCosets htN
    have hmaps : MapsRootLines t w' := by
      rw [hgk]
      simpa using (mapsRootLines_of_mem_torusGroup hk').mul (mapsRootLines_canonicalRep w')
    have hw1 : w' = 1 := hmaps.unique htR
    rw [hgk, hw1, canonicalRep_one, mul_one]
    exact hk'
  have hlfix : secElt μ * l * (secElt μ)⁻¹ = l := by
    have hlc := (Subgroup.mem_inf.1 (secM_le h2 hμ3 hlM)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hlc
    rw [← hlc, mul_inv_cancel_right]
  have htfix : secElt μ * t * (secElt μ)⁻¹ = t := by
    calc secElt μ * t * (secElt μ)⁻¹ =
        (secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹) *
          (secElt μ * l * (secElt μ)⁻¹) := by rw [ht]; group
      _ = t := by rw [hfix, hlfix, ht]
  have htP : t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
    have hTG : torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
      (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
    refine Subgroup.mem_inf.2 ⟨hTG htT, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [secElt_conj_torus μ htT] at htfix
    calc t * diagramMap TwistTag.D4 L =
        diagramMap TwistTag.D4 L * t * (diagramMap TwistTag.D4 L)⁻¹ * diagramMap TwistTag.D4 L := by
          rw [htfix]
      _ = diagramMap TwistTag.D4 L * t := by group
  have e : rootDiagUnit TwistTag.D4.tag a * n = t * l⁻¹ := by rw [ht]; group
  rw [e]
  exact mul_mem (mem_secM_of_mem_torus μ htT htP) (inv_mem hlM)

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

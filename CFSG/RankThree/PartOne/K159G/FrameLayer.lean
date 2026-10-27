module

public import CFSG.RankThree.PartOne.K159G.PlaneLayer
public import CFSG.RankThree.PartOne.U5K.Kf.Zeta

public section

namespace CFSG.RankThree.PartOne.K159G

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
  CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.U5K.Kf

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def dUnit (Z : ZetaData h p) (a : Fin 5 → ZMod p) : Fin 5 → Kˣ :=
  fun s => Units.mk0 (zp Z.ζ (a s)) (zp_ne_zero Z.prim _)

theorem dgU_eq_diagU (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    ((Z.dgU a : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) = diagU (dUnit Z a) :=
  Units.ext rfl

theorem dUnit_eq_iff (Z : ZetaData h p) (a : Fin 5 → ZMod p) {k l : Fin 5} :
    dUnit Z a k = dUnit Z a l ↔ a k = a l := by
  rw [← zp_inj Z.prim]
  exact Units.ext_iff

theorem dgU_pow (Z : ZetaData h p) (a : Fin 5 → ZMod p) : Z.dgU a ^ p = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, dgU_eq_diagU Z, diagU_pow]
  have : dUnit Z a ^ p = 1 := by
    funext s
    apply Units.ext
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, dUnit, Units.val_mk0, Pi.one_apply,
      Units.val_one, zp]
    rw [← pow_mul, mul_comm, pow_mul, Z.pow_eq_one, one_pow]
  rw [this, diagU_one]
  rfl

@[expose] noncomputable def planesOf (h : UnitaryFieldData 2 f K) (a : Fin 5 → ZMod p) :
    Subgroup (primeFormP h (idGram K 5)) :=
  ⨆ q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2}, planeP h q.1.1 q.1.2 (ne_of_lt q.2.1)

theorem perfect_le_planesOf (Z : ZetaData h p) (a : Fin 5 → ZMod p)
    {Y : Subgroup (primeFormP h (idGram K 5))}
    (hY : Y ≤ fixedSub (primeFormConjHom h (idGram K 5) (Z.dgU a))) (hYp : ⁅Y, Y⁆ = Y) :
    Y ≤ planesOf h a := by
  refine (perfect_le_planes h (Fact.out : p.Prime) Z.five_le Z.dvd (dgU_eq_diagU Z a) (dgU_pow Z a) hY
    hYp).trans (iSup_le fun q => ?_)
  have hqa : a q.1.1 = a q.1.2 := (dUnit_eq_iff Z a).1 q.2.2
  rcases lt_or_gt_of_ne q.2.1 with hlt | hgt
  · exact le_iSup (fun q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2} =>
      planeP h q.1.1 q.1.2 (ne_of_lt q.2.1)) ⟨q.1, hlt, hqa⟩
  · rw [planeP_swap h q.2.1.symm]
    exact le_iSup (fun q : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2} =>
      planeP h q.1.1 q.1.2 (ne_of_lt q.2.1)) ⟨(q.1.2, q.1.1), hgt, hqa.symm⟩

@[expose] def genVec (p : ℕ) (i j : Fin 5) : Fin 5 → ZMod p :=
  fun k => if k = j then ((i : ℕ) : ZMod p) else ((k : ℕ) : ZMod p)

theorem genVec_eq {i j : Fin 5} (hp5 : 5 ≤ p) (hij : i ≠ j) {k l : Fin 5} (hkl : k ≠ l)
    (h : genVec p i j k = genVec p i j l) : (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  have hinj : ∀ a b : Fin 5, ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) → a = b := by
    intro a b hab
    have h1 := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.2 hp5), ZMod.val_natCast_of_lt (lt_of_lt_of_le b.2 hp5)] at h1
    exact Fin.ext h1
  unfold genVec at h
  by_cases hkj : k = j
  · subst hkj
    have hlj : l ≠ k := fun e => hkl e.symm
    simp only [ite_true, hlj, ite_false] at h
    exact Or.inr ⟨rfl, (hinj _ _ h).symm⟩
  · by_cases hlj : l = j
    · subst hlj
      simp only [hkj, ite_false, ite_true] at h
      exact Or.inl ⟨hinj _ _ h, rfl⟩
    · simp only [hkj, hlj, ite_false] at h
      exact absurd (hinj _ _ h) hkl

omit [Fact p.Prime] in
theorem genVec_self {i j : Fin 5} (hij : i ≠ j) : genVec p i j i = genVec p i j j := by
  simp [genVec, hij]

theorem perfect_le_planeP (Z : ZetaData h p) {i j : Fin 5} (hij : i ≠ j)
    {Y : Subgroup (primeFormP h (idGram K 5))}
    (hY : Y ≤ fixedSub (primeFormConjHom h (idGram K 5) (Z.dgU (genVec p i j)))) (hYp : ⁅Y, Y⁆ = Y) :
    Y ≤ planeP h i j hij := by
  refine (perfect_le_planes h (Fact.out : p.Prime) Z.five_le Z.dvd (dgU_eq_diagU Z (genVec p i j))
    (dgU_pow Z _) hY hYp).trans (iSup_le fun q => ?_)
  have hqa : genVec p i j q.1.1 = genVec p i j q.1.2 := (dUnit_eq_iff Z _).1 q.2.2
  rcases genVec_eq Z.five_le hij q.2.1 hqa with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : q.1 = (i, j) := Prod.ext h1 h2
    obtain ⟨q', hq'⟩ := q
    subst this
    exact le_rfl
  · have : q.1 = (j, i) := Prod.ext h1 h2
    obtain ⟨q', hq'⟩ := q
    subst this
    exact (planeP_swap h hij).le

theorem le_iSup_of_fixed_perfect {H : Type*} [Group H] {Ψ : H →* primeFormP h (idGram K 5)}
    (hker : Ψ.ker ≤ Subgroup.center H) (Z : ZetaData h p) (a : Fin 5 → ZMod p)
    {T : {q : Fin 5 × Fin 5 // q.1 < q.2 ∧ a q.1 = a q.2} → Subgroup H}
    (hT : ∀ q, (T q).map Ψ = planeP h q.1.1 q.1.2 (ne_of_lt q.2.1)) {Q : Subgroup H}
    (hQ : ⁅Q, Q⁆ = Q)
    (hfix : ∀ y ∈ Q, primeFormConjHom h (idGram K 5) (Z.dgU a) (Ψ y) = Ψ y) : Q ≤ ⨆ q, T q := by
  refine S15K.le_iSup_of_isPerfect_of_map_le hker hT hQ ?_
  have hY : Q.map Ψ ≤ fixedSub (primeFormConjHom h (idGram K 5) (Z.dgU a)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfix y hy
  have hYp : ⁅Q.map Ψ, Q.map Ψ⁆ = Q.map Ψ := by rw [← Subgroup.map_commutator, hQ]
  exact perfect_le_planesOf Z a hY hYp

theorem map_eq_planeP {H : Type*} [Group H] {Ψ : H →* primeFormP h (idGram K 5)} (Z : ZetaData h p)
    {i j : Fin 5} (hij : i ≠ j) {T : Subgroup H} (hT : ⁅T, T⁆ = T)
    (hfix : ∀ y ∈ T, primeFormConjHom h (idGram K 5) (Z.dgU (genVec p i j)) (Ψ y) = Ψ y)
    (hinj : ∀ x ∈ T, Ψ x = 1 → x = 1) (hcard : Nat.card T = Nat.card (blk h hij)) :
    T.map Ψ = planeP h i j hij := by
  have hfin := h.finite
  have hle : T.map Ψ ≤ planeP h i j hij := by
    refine perfect_le_planeP Z hij (fun w hw => ?_) (by rw [← Subgroup.map_commutator, hT])
    obtain ⟨y, hy, rfl⟩ := hw
    exact hfix y hy
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hinj' : Function.Injective (Ψ.domRestrict T) := by
    intro x y hxy
    have h1 : Ψ ((x : H)⁻¹ * (y : H)) = 1 := by
      rw [map_mul, map_inv, show Ψ (x : H) = Ψ (y : H) from hxy, inv_mul_cancel]
    have h2 := hinj _ (mul_mem (inv_mem x.2) y.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  rw [card_planeP h hij, ← hcard, ← MonoidHom.domRestrict_range T Ψ]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).le

end CFSG.RankThree.PartOne.K159G

module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDFork
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessD
import all TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import CFSG.RankThree.PartTwo.Census.Spin.Family

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD RootData

variable (d : TypeTwistedDLieIndex)

theorem four_le : 4 ≤ d.1.rank := d.toTypeDDiagramLieIndex.four_le_rank

noncomputable abbrev frob : d.1.Closure →+* d.1.Closure :=
  iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent

theorem frob_apply (u : d.1.Closure) : frob d u = u ^ d.1.fieldOrder := by
  rw [frob, iterateFrobenius_def, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

abbrev perm : Equiv.Perm (Fin d.1.rank) := graphPermD d.1.rank (by have := four_le d; omega)

theorem perm_forkA : perm d (forkA d.1.rank (four_le d)) = forkB d.1.rank (four_le d) := by
  rw [perm, graphPermD]
  exact Equiv.swap_apply_left _ _

theorem perm_forkB : perm d (forkB d.1.rank (four_le d)) = forkA d.1.rank (four_le d) := by
  rw [perm, graphPermD]
  exact Equiv.swap_apply_right _ _

theorem perm_of_lt {j : Fin d.1.rank} (hj : j.val < d.1.rank - 2) : perm d j = j := by
  rw [perm, graphPermD]
  refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
  · have := congrArg Fin.val h
    simp only at this
    omega
  · have := congrArg Fin.val h
    simp only at this
    omega

theorem isTwistedFrobenius :
    (rootData d.1.rank (four_le d) d.1.Closure).IsTwistedFrobenius (frob d) (perm d)
      d.steinberg where
  map_x i u := by
    rw [TypeTwistedDLieIndex.steinberg_def]
    change d.graphAut (TypeDDiagramLieIndex.frobenius _ (rootSubgroupPoints _ _ (.inl i) _ _)) =
      rootSubgroupPoints _ _ (.inl _) _ _
    rw [TypeDDiagramLieIndex.frobenius_def, frobenius_rootSubgroupPoints,
      TypeTwistedDLieIndex.graphAut_def, graphAutPoints_rootSubgroupPoints, graphRootPerm_inl,
      toAdd_ofAdd, iterateFrobenius_def]
  map_y i u := by
    rw [TypeTwistedDLieIndex.steinberg_def]
    change d.graphAut (TypeDDiagramLieIndex.frobenius _ (rootSubgroupPoints _ _ (.inr i) _ _)) =
      rootSubgroupPoints _ _ (.inr _) _ _
    rw [TypeDDiagramLieIndex.frobenius_def, frobenius_rootSubgroupPoints,
      TypeTwistedDLieIndex.graphAut_def, graphAutPoints_rootSubgroupPoints, graphRootPerm_inr,
      toAdd_ofAdd, iterateFrobenius_def]
  map_torus s := by
    rw [TypeTwistedDLieIndex.steinberg_def]
    change d.graphAut (TypeDDiagramLieIndex.frobenius _ (weightTorusPoints _ _ _ s)) =
      weightTorusPoints _ _ _ _
    rw [TypeDDiagramLieIndex.frobenius_def, frobenius_weightTorusPoints,
      TypeTwistedDLieIndex.graphAut_def, graphAutPoints_weightTorusPoints]
    congr 1

theorem mem_fixedField_iff (u : d.1.Closure) :
    u ∈ RootData.fixedField (frob d) ↔ u ∈ d.1.fixedField := by
  rw [RootData.mem_fixedField, frob_apply, ValidLieTypeIndex.mem_fixedField]

theorem card_fixedField_frob :
    Nat.card (RootData.fixedField (frob d)) = d.1.characteristic ^ d.1.fieldExponent := by
  rw [Subfield.ext (mem_fixedField_iff d), d.1.card_fixedField,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

noncomputable abbrev fixedField2 : Subfield d.1.Closure :=
  RootData.fixedField ((frob d).comp (frob d))

theorem fixedField2_eq :
    fixedField2 d = frobeniusFixedSubfield d.1.Closure d.1.characteristic
      (2 * d.1.fieldExponent) := by
  ext u
  rw [RootData.mem_fixedField, mem_frobeniusFixedSubfield, RingHom.comp_apply, frob_apply,
    frob_apply, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, ← pow_mul, ← pow_add,
    two_mul]

theorem card_fixedField2 :
    Nat.card (fixedField2 d) = d.1.characteristic ^ (2 * d.1.fieldExponent) := by
  rw [fixedField2_eq, card_frobeniusFixedSubfield]
  have : 0 < d.1.fieldExponent := d.1.1.fieldExponent_pos
  omega

theorem two_ne_zero_closure (hodd : d.1.characteristic ≠ 2) : (2 : d.1.Closure) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : d.1.Closure) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff d.1.Closure d.1.characteristic] at h'
  exact hodd ((Nat.prime_dvd_prime_iff_eq d.1.characteristic_prime Nat.prime_two).mp h')

theorem exists_fixed_neighbour (i : Fin d.1.rank) (hi : i.val < d.1.rank - 2) :
    ∃ j : Fin d.1.rank, j.val < d.1.rank - 2 ∧ CartanMatrix.D d.1.rank j i = -1 := by
  have h4 := four_le d
  by_cases h0 : i.val = 0
  · refine ⟨⟨1, by omega⟩, by simp; omega, ?_⟩
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · refine ⟨⟨i.val - 1, by omega⟩, by simp; omega, ?_⟩
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem D_fork_neighbour :
    CartanMatrix.D d.1.rank ⟨d.1.rank - 3, by have := four_le d; omega⟩
        (forkA d.1.rank (four_le d)) = -1 ∧
      CartanMatrix.D d.1.rank ⟨d.1.rank - 3, by have := four_le d; omega⟩
        (forkB d.1.rank (four_le d)) = -1 := by
  have h4 := four_le d
  constructor <;>
  · simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem D_forkA_forkB :
    CartanMatrix.D d.1.rank (forkA d.1.rank (four_le d)) (forkB d.1.rank (four_le d)) = 0 := by
  have h4 := four_le d
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

variable {d}

theorem mem_commutator_of_unit {μ : d.1.Closureˣ} (hμF : frob d μ = μ) (hμ1 : μ ≠ 1) :
    (∀ i : Fin d.1.rank, i.val < d.1.rank - 2 → ∀ u, frob d u = u →
      (rootData d.1.rank (four_le d) d.1.Closure).x i u ∈
        ⁅fixedSubgroup d.steinberg, fixedSubgroup d.steinberg⁆ ∧
      (rootData d.1.rank (four_le d) d.1.Closure).y i u ∈
        ⁅fixedSubgroup d.steinberg, fixedSubgroup d.steinberg⁆) ∧
    (∀ u, frob d (frob d u) = u →
      (rootData d.1.rank (four_le d) d.1.Closure).pairX (frob d) (forkA d.1.rank (four_le d))
          (forkB d.1.rank (four_le d)) u ∈
        ⁅fixedSubgroup d.steinberg, fixedSubgroup d.steinberg⁆ ∧
      (rootData d.1.rank (four_le d) d.1.Closure).pairY (frob d) (forkA d.1.rank (four_le d))
          (forkB d.1.rank (four_le d)) u ∈
        ⁅fixedSubgroup d.steinberg, fixedSubgroup d.steinberg⁆) := by
  have hF := isTwistedFrobenius d
  have h4 := four_le d
  have hμk : μ ^ (-1 : ℤ) ≠ 1 := by
    rw [zpow_neg_one]
    exact fun h => hμ1 (inv_eq_one.mp h)
  refine ⟨fun i hi u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨j, hj, hji⟩ := exists_fixed_neighbour d i hi
    have hμc : μ ^ (rootData d.1.rank h4 d.1.Closure).CM j i ≠ 1 := by
      rw [rootData_CM, hji]
      exact hμk
    exact ⟨x_mem_commutator_tw hF (perm_of_lt d hi) (perm_of_lt d hj) hμF hμc hu,
      y_mem_commutator_tw hF (perm_of_lt d hi) (perm_of_lt d hj) hμF hμc hu⟩
  · obtain ⟨hja, hjb⟩ := D_fork_neighbour d
    have hj : perm d ⟨d.1.rank - 3, by omega⟩ = ⟨d.1.rank - 3, by omega⟩ :=
      perm_of_lt d (by simp; omega)
    exact ⟨pairX_mem_commutator hF (perm_forkA d) (perm_forkB d) (D_forkA_forkB d) hj hja hjb
      hμF hμk hu, pairY_mem_commutator hF (perm_forkA d) (perm_forkB d) (D_forkA_forkB d) hj
      hja hjb hμF hμk hu⟩

variable (d)

theorem hasWitness_unipotent (hodd : d.1.characteristic ≠ 2) {κ : Type} [Fintype κ]
    [DecidableEq κ] (J : κ → Fin d.1.rank) (hJ : ∀ a, (J a).val < d.1.rank - 2)
    (horth : ∀ a a', a ≠ a' → CartanMatrix.D d.1.rank (J a) (J a') = 0)
    (hfa : ∀ a, CartanMatrix.D d.1.rank (J a) (forkA d.1.rank (four_le d)) = 0)
    (hfb : ∀ a, CartanMatrix.D d.1.rank (J a) (forkB d.1.rank (four_le d)) = 0)
    (k : Fin d.1.rank) (hk : k.val < d.1.rank - 2)
    (hkJ : ∀ a, Even (CartanMatrix.D d.1.rank k (J a)))
    (hka : Even (CartanMatrix.D d.1.rank k (forkA d.1.rank (four_le d))))
    (hkb : Even (CartanMatrix.D d.1.rank k (forkB d.1.rank (four_le d))))
    (j₀ : Fin d.1.rank) (hj₀ : j₀.val < d.1.rank - 2)
    (hkj₀ : Odd (CartanMatrix.D d.1.rank k j₀)) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * (Fintype.card κ + 2)) := by
  have h4 := four_le d
  have h2 := two_ne_zero_closure d hodd
  set R := rootData d.1.rank h4 d.1.Closure with hR
  have hCM : R.CM = CartanMatrix.D d.1.rank := rfl
  let H : Subgroup R.G := fixedSubgroup d.steinberg
  set σ := frob d
  set fa := forkA d.1.rank h4
  set fb := forkB d.1.rank h4
  have hp : R.IsDisjointPair fa fb := isDisjointPair_fork d.1.rank h4 d.1.Closure
  have hm1F : σ ((-1 : d.1.Closureˣ) : d.1.Closure) = ((-1 : d.1.Closureˣ) : d.1.Closure) := by
    simp
  have hneg : (-1 : d.1.Closure) ≠ 1 := fun h => h2 (by
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h]
    exact neg_add_cancel 1)
  have hm1 : (-1 : d.1.Closureˣ) ≠ 1 := fun h => hneg (by
    have := congrArg (fun v : d.1.Closureˣ => (v : d.1.Closure)) h
    simpa using this)
  obtain ⟨hxy, hXY⟩ := mem_commutator_of_unit hm1F hm1
  have hJinj : Function.Injective J := fun a a' h => by
    by_contra hne
    have := horth a a' hne
    rw [h, CartanMatrix.D_diag] at this
    exact absurd this (by norm_num)
  have hJfa : ∀ a, J a ≠ fa := fun a h => by
    have := hJ a
    rw [h] at this
    simp only [fa] at this
    omega
  have hJfb : ∀ a, J a ≠ fb := fun a h => by
    have := hJ a
    rw [h] at this
    simp only [fb] at this
    omega
  set Fq := RootData.fixedField σ
  set L2 := fixedField2 d
  let L : κ ⊕ Unit → Subfield d.1.Closure := Sum.elim (fun _ => Fq) (fun _ => L2)
  let g : κ ⊕ Unit → d.1.Closure → R.G :=
    Sum.elim (fun a => R.x (J a)) (fun _ => R.pairX σ fa fb)
  have hg : ∀ c u v, g c (u + v) = g c u * g c v := by
    rintro (a | _) u v
    · exact R.x_add _ u v
    · exact pairX_add (D_forkA_forkB d) u v
  have hg0 : ∀ c, g c 0 = 1 := by
    rintro (a | _)
    · exact R.x_zero _
    · change R.x fa 0 * R.x fb (σ 0) = 1
      rw [map_zero, x_zero, x_zero, mul_one]
  let ϕ : ∀ c, Multiplicative (L c) →* R.G := fun c =>
    { toFun := fun u => g c ((Multiplicative.toAdd u : L c) : d.1.Closure)
      map_one' := hg0 c
      map_mul' := fun u v => hg c _ _ }
  have hcomm : Pairwise fun c c' => ∀ u v, Commute (ϕ c u) (ϕ c' v) := by
    rintro (a | _) (a' | _) hne u v
    · exact R.commute_x_x (horth a a' (fun h => hne (congrArg Sum.inl h))) _ _
    · exact (R.commute_x_x (hfa a) _ _).mul_right (R.commute_x_x (hfb a) _ _)
    · exact ((R.commute_x_x (hfa a') _ _).mul_right (R.commute_x_x (hfb a') _ _)).symm
    · exact absurd rfl hne
  have hD : ∀ c u, ϕ c u ∈ ⁅H, H⁆ := by
    rintro (a | _) u
    · exact (hxy (J a) (hJ a) _ (Multiplicative.toAdd u).2).1
    · exact (hXY _ (Multiplicative.toAdd u).2).1
  have hpc : ∀ c (u : L c), d.1.characteristic • u = 0 := fun c u => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl)
  have hcard : Nat.card (∀ c, Multiplicative (L c)) =
      d.1.characteristic ^ (d.1.fieldExponent * (Fintype.card κ + 2)) := by
    have e1 : ∀ c, Nat.card (Multiplicative (L c)) = Nat.card (L c) := fun c =>
      Nat.card_congr Multiplicative.toAdd
    rw [Nat.card_pi, Fintype.prod_sum_type]
    simp only [e1]
    change (∏ _a : κ, Nat.card Fq) * (∏ _u : Unit, Nat.card L2) = _
    rw [card_fixedField_frob, card_fixedField2, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Finset.card_univ, Fintype.card_unit, pow_one, ← pow_mul, ← pow_add]
    congr 1
    ring
  let y : κ ⊕ Unit → R.G := Sum.elim (fun a => R.y (J a) 1) (fun _ => R.pairY σ fa fb 1)
  have hy : ∀ c, y c ∈ ⁅H, H⁆ := by
    rintro (a | _)
    · exact (hxy (J a) (hJ a) 1 (map_one _)).2
    · exact (hXY 1 (by simp)).2
  have hdet : ∀ c u, Commute (ϕ c u) (y c) → u = 1 := by
    rintro (a | _) u h
    · exact Multiplicative.toAdd.injective (Subtype.ext (R.eq_zero_of_commute_x_y h))
    · exact Multiplicative.toAdd.injective (Subtype.ext (eq_zero_of_commute_pairX_pairY hp h))
  have hoff : ∀ c c', c ≠ c' → ∀ u, Commute (ϕ c' u) (y c) := by
    rintro (a | _) (a' | _) hne u
    · exact R.commute_x_y (fun h => hne (congrArg Sum.inl (hJinj h).symm)) _ _
    · exact (R.commute_x_y (Ne.symm (hJfa a)) _ _).mul_left
        (R.commute_x_y (Ne.symm (hJfb a)) _ _)
    · exact (R.commute_x_y (hJfa a') _ _).mul_right (R.commute_x_y (hJfb a') _ _)
    · exact absurd rfl hne
  have htD : R.h k (-1) ∈ ⁅H, H⁆ :=
    h_mem_of_xy (R := R) (fun u hu => (hxy k hk u hu).1) (fun u hu => (hxy k hk u hu).2) hm1F
  have ht2 : R.h k (-1) ^ 2 = 1 := by
    rw [RootData.h, ← map_pow, ← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one, map_one]
  have htz : ∃ g ∈ ⁅H, H⁆, R.h k (-1) * g ≠ g * R.h k (-1) := by
    refine ⟨R.x j₀ 1, (hxy j₀ hj₀ 1 (map_one _)).1, fun hc => ?_⟩
    have h1 := R.h_conj_x k j₀ (-1) 1
    rw [hc, mul_inv_cancel_right, hCM, hkj₀.neg_one_zpow, Units.val_neg, Units.val_one,
      mul_one] at h1
    exact hneg (R.x_injective j₀ h1).symm
  have ht : ∀ c u, Commute (R.h k (-1)) (ϕ c u) := by
    rintro (a | _) u
    · have h1 := R.h_conj_x k (J a) (-1) ((Multiplicative.toAdd u : L (Sum.inl a)) : _)
      rw [hCM, (hkJ a).neg_one_zpow, Units.val_one, one_mul] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · have h1 := R.h_conj_x k fa (-1) ((Multiplicative.toAdd u : L (Sum.inr ())) : _)
      have h1' := R.h_conj_x k fb (-1) (σ ((Multiplicative.toAdd u : L (Sum.inr ())) : _))
      rw [hCM, hka.neg_one_zpow, Units.val_one, one_mul] at h1
      rw [hCM, hkb.neg_one_zpow, Units.val_one, one_mul] at h1'
      have c1 : Commute (R.h k (-1)) (R.x fa _) := mul_inv_eq_iff_eq_mul.mp h1
      have c2 : Commute (R.h k (-1)) (R.x fb _) := mul_inv_eq_iff_eq_mul.mp h1'
      exact c1.mul_right c2
  exact family_witness ϕ hcomm hD hpc hcard y hy hdet hoff _ htD ht2 htz ht

theorem hasWitness_torus (h2 : d.1.characteristic = 2) (hq : 4 ≤ d.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hsq : s ∣ d.1.fieldOrder - 1) {κ : Type} [Fintype κ] [DecidableEq κ]
    (S : κ → Finset (Fin d.1.rank))
    (hS : ∀ b, (∀ i ∈ S b, i.val < d.1.rank - 2) ∨
      S b = {forkA d.1.rank (four_le d), forkB d.1.rank (four_le d)})
    (rw : κ → Fin d.1.rank)
    (hrw : ∀ a, (rw a).val < d.1.rank - 2 ∨ rw a = forkA d.1.rank (four_le d))
    (hdet : (Matrix.of fun a b =>
      ((∑ i ∈ S b, CartanMatrix.D d.1.rank i (rw a) : ℤ) : ZMod s)).det ≠ 0) :
    HasWitness d.Group s (Fintype.card κ) := by
  have h4 := four_le d
  have : NeZero s := ⟨hs.ne_zero⟩
  set R := rootData d.1.rank h4 d.1.Closure with hR
  have hCM : R.CM = CartanMatrix.D d.1.rank := rfl
  let H : Subgroup R.G := fixedSubgroup d.steinberg
  set σ := frob d
  set fa := forkA d.1.rank h4
  set fb := forkB d.1.rank h4
  have hp : R.IsDisjointPair fa fb := isDisjointPair_fork d.1.rank h4 d.1.Closure
  have hfab : fa ≠ fb := Fork.na_ne_nb (by omega : 2 ≤ d.1.rank)
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  have hcard : Nat.card d.1.fixedField = d.1.fieldOrder := d.1.card_fixedField
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one d.1.fixedField (hcard ▸ hq)
  obtain ⟨ζ, hζL, hζ⟩ := exists_unit_orderOf d.1.fixedField (hcard ▸ hsq)
  have hμF : σ μ = μ := (mem_fixedField_iff d _).mpr hμL
  have hζF : (ζ : d.1.Closure) ∈ RootData.fixedField σ := (mem_fixedField_iff d _).mpr hζL
  have hμ1 : μ ≠ 1 := fun h => hμ2 (by rw [h, Units.val_one, one_pow])
  obtain ⟨hxy, hXY⟩ := mem_commutator_of_unit hμF hμ1
  have hhD : ∀ i : Fin d.1.rank, i.val < d.1.rank - 2 → ∀ c : d.1.Closureˣ, σ c = c →
      R.h i c ∈ ⁅H, H⁆ := fun i hi c hc =>
    h_mem_of_xy (R := R) (fun u hu => (hxy i hi u hu).1) (fun u hu => (hxy i hi u hu).2) hc
  have hpairD : ∀ c : d.1.Closureˣ, σ c = c → R.h fa c * R.h fb c ∈ ⁅H, H⁆ := fun c hc =>
    h_mul_h_mem_of_pair (R := R) hfab (D_forkA_forkB d) (fun u hu => (hXY u hu).1)
      (fun u hu => (hXY u hu).2) hc
  set τ := torusSetHom ζ hζ S
  have hτD : ∀ e, R.torus (τ e) ∈ ⁅H, H⁆ := by
    intro e
    rw [torusSetHom_apply]
    refine Finset.prod_induction _ (fun t => R.torus t ∈ ⁅H, H⁆)
      (fun t t' ht ht' => by rw [map_mul]; exact Subgroup.mul_mem _ ht ht')
      (by rw [map_one]; exact Subgroup.one_mem _) fun b _ => ?_
    have hz : σ (zpowHom ζ hζ (e b) : d.1.Closure) = zpowHom ζ hζ (e b) :=
      zpowHom_mem ζ hζ hζF (e b)
    rcases hS b with hfix | hpair
    · refine Finset.prod_induction _ (fun t => R.torus t ∈ ⁅H, H⁆)
        (fun t t' ht ht' => by rw [map_mul]; exact Subgroup.mul_mem _ ht ht')
        (by rw [map_one]; exact Subgroup.one_mem _) fun i hi => ?_
      exact hhD i (hfix i hi) _ hz
    · rw [hpair, Finset.prod_pair hfab, map_mul]
      exact hpairD _ hz
  have hτL : ∀ e j, ((τ e j : d.1.Closureˣ) : d.1.Closure) ∈ RootData.fixedField σ :=
    fun e j => torusSetHom_mem ζ hζ S hζF e j
  have h0 : (⟨0, by omega⟩ : Fin d.1.rank).val < d.1.rank - 2 := by simp; omega
  have hxD : ∀ u ∈ RootData.fixedField σ, R.x ⟨0, by omega⟩ u ∈ ⁅H, H⁆ := fun u hu =>
    (hxy _ h0 u hu).1
  have hnc : ∃ c ∈ ⁅H, H⁆, R.x ⟨0, by omega⟩ 1 * c ≠ c * R.x ⟨0, by omega⟩ 1 := by
    refine ⟨R.h ⟨0, by omega⟩ μ, hhD _ h0 μ hμF, fun hc => hμ2 ?_⟩
    have h1 := R.h_conj_x ⟨0, by omega⟩ ⟨0, by omega⟩ μ 1
    rw [← hc, mul_inv_cancel_right, mul_one, hCM, CartanMatrix.D_diag,
      Units.val_zpow_eq_zpow_val, zpow_ofNat] at h1
    exact (R.x_injective _ h1).symm
  let g : κ → R.G := fun a => if rw a = fa then R.pairX σ fa fb 1 else R.x (rw a) 1
  have hgD : ∀ a, g a ∈ ⁅H, H⁆ := fun a => by
    by_cases ha : rw a = fa
    · simp only [g, ha, ite_true]
      exact (hXY 1 (by simp)).1
    · simp only [g, ha, ite_false]
      exact (hxy _ ((hrw a).resolve_right ha) 1 (map_one _)).1
  have hdetect : ∀ e, (∀ a, Commute (R.torus (τ e)) (g a)) → e = 1 := fun e he =>
    eq_one_of_torusSetHom_char ζ hζ S hs R.CM rw hdet e fun a => by
      by_cases ha : rw a = fa
      · have h1 := he a
        simp only [g, ha, ite_true] at h1
        rw [ha]
        exact char_eq_one_of_commute_pairX hp h1
      · have h1 := he a
        simp only [g, ha, ite_false] at h1
        exact R.char_eq_one_of_commute h1.eq
  obtain ⟨E, P, hW⟩ := R.torus_witness_of (H := H) (RootData.fixedField σ) hchar τ hτD hτL
    ⟨0, by omega⟩ hxD hnc g hgD hdetect
  exact hW.hasWitness

macro "d_entry" : tactic => `(tactic| (split_ifs <;> (try simp only [false_and, and_false,
  true_and, and_true, not_false_eq_true, not_true_eq_false, false_or, or_false] at *) <;> omega))

theorem D_apply (m : ℕ) (i j : Fin m) : CartanMatrix.D m i j =
    if i.val = j.val then 2 else if m ≤ 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < m then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < m then -1
    else if i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m) then -1
    else if j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m) then -1 else 0 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]

theorem hasWitness_unipotent_three (hodd : d.1.characteristic ≠ 2) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 3) := by
  have h4 := four_le d
  have h := hasWitness_unipotent d hodd (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin d.1.rank))
    (fun _ => by simp; omega) (fun a a' h => absurd (Subsingleton.elim a a') h)
    (fun _ => by simp only [D_apply, forkA]; d_entry)
    (fun _ => by simp only [D_apply, forkB]; d_entry)
    ⟨0, by omega⟩ (by simp; omega)
    (fun _ => by rw [Int.even_iff]; simp only [D_apply]; d_entry)
    (by rw [Int.even_iff]; simp only [D_apply, forkA]; d_entry)
    (by rw [Int.even_iff]; simp only [D_apply, forkB]; d_entry)
    ⟨1, by omega⟩ (by simp; omega)
    (by rw [Int.odd_iff]; simp only [D_apply]; d_entry)
  rwa [Fintype.card_fin] at h

theorem hasWitness_unipotent_four (hodd : d.1.characteristic ≠ 2) (h6 : 6 ≤ d.1.rank) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 4) := by
  have h := hasWitness_unipotent d hodd
    (![⟨0, by omega⟩, ⟨2, by omega⟩] : Fin 2 → Fin d.1.rank)
    (fun a => by fin_cases a <;> simp <;> omega)
    (fun a a' h => by
      fin_cases a <;> fin_cases a' <;> simp [D_apply] at h ⊢ <;> omega)
    (fun a => by fin_cases a <;> simp only [D_apply, forkA] <;> simp <;> d_entry)
    (fun a => by fin_cases a <;> simp only [D_apply, forkB] <;> simp <;> d_entry)
    ⟨0, by omega⟩ (by simp; omega)
    (fun a => by
      rw [Int.even_iff]
      fin_cases a
      all_goals simp only [D_apply]
      all_goals simp
      all_goals d_entry)
    (by rw [Int.even_iff]; simp only [D_apply, forkA]; d_entry)
    (by rw [Int.even_iff]; simp only [D_apply, forkB]; d_entry)
    ⟨1, by omega⟩ (by simp; omega)
    (by rw [Int.odd_iff]; simp only [D_apply]; d_entry)
  rwa [Fintype.card_fin] at h

@[expose] def nodeSets5 (m : ℕ) (hm : 4 ≤ m) : Fin 4 → Finset (Fin m) :=
  ![{⟨0, by omega⟩}, {⟨1, by omega⟩}, {⟨2, by omega⟩}, {⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩}]

@[expose] def rows5 (m : ℕ) (hm : 4 ≤ m) : Fin 4 → Fin m :=
  ![⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨m - 2, by omega⟩]

@[expose] def nodeSets4 (m : ℕ) (hm : 4 ≤ m) : Fin 3 → Finset (Fin m) :=
  ![{⟨0, by omega⟩}, {⟨1, by omega⟩}, {⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩}]

@[expose] def rows4 (m : ℕ) (hm : 4 ≤ m) : Fin 3 → Fin m :=
  ![⟨0, by omega⟩, ⟨1, by omega⟩, ⟨m - 2, by omega⟩]

theorem minor5_eq (m : ℕ) (hm4 : 4 ≤ m) (hm : m = 5) :
    (Matrix.of fun a b => (∑ i ∈ nodeSets5 m hm4 b, CartanMatrix.D m i (rows5 m hm4 a) : ℤ)) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -2; 0, 0, -1, 2] := by
  subst hm
  exact (by decide : (Matrix.of fun a b => (∑ i ∈ nodeSets5 5 (by norm_num) b,
    CartanMatrix.D 5 i (rows5 5 (by norm_num) a) : ℤ)) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -2; 0, 0, -1, 2])

theorem minor4_eq (m : ℕ) (hm4 : 4 ≤ m) (hm : m = 4) :
    (Matrix.of fun a b => (∑ i ∈ nodeSets4 m hm4 b, CartanMatrix.D m i (rows4 m hm4 a) : ℤ)) =
      !![2, -1, 0; -1, 2, -2; 0, -1, 2] := by
  subst hm
  exact (by decide : (Matrix.of fun a b => (∑ i ∈ nodeSets4 4 (by norm_num) b,
    CartanMatrix.D 4 i (rows4 4 (by norm_num) a) : ℤ)) = !![2, -1, 0; -1, 2, -2; 0, -1, 2])

theorem minor6_eq (m : ℕ) (h4 : 4 ≤ m) (hm : 6 ≤ m) :
    (Matrix.of fun a b : Fin 4 => (∑ i ∈ ({Fin.castLE h4 b} : Finset (Fin m)),
      CartanMatrix.D m i (Fin.castLE h4 a) : ℤ)) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2] := by
  ext a b
  simp only [Finset.sum_singleton]
  fin_cases a <;> fin_cases b <;> simp [CartanMatrix.D, Matrix.of_apply] <;> omega

theorem det_cast_ne_zero {k : ℕ} {s : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (c : ℤ)
    (hM : M.det = c) (hc : ((c : ℤ) : ZMod s) ≠ 0) :
    (Matrix.of fun a b => ((M a b : ℤ) : ZMod s)).det ≠ 0 := by
  have hmap : (Matrix.of fun a b => ((M a b : ℤ) : ZMod s)) =
      (Int.castRingHom (ZMod s)).mapMatrix M := by
    ext a b
    simp
  rw [hmap, ← RingHom.map_det, hM]
  exact hc

theorem hasWitness_torus_six (h2 : d.1.characteristic = 2) (hq : 4 ≤ d.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hs5 : s ≠ 5) (hsq : s ∣ d.1.fieldOrder - 1) (h6 : 6 ≤ d.1.rank) :
    HasWitness d.Group s 4 := by
  have h4 := four_le d
  have hfix : ∀ b : Fin 4, (Fin.castLE h4 b).val < d.1.rank - 2 := fun b => by
    have := b.isLt
    rw [Fin.val_castLE]
    omega
  have h := hasWitness_torus d h2 hq hs hsq
    (fun b : Fin 4 => ({Fin.castLE h4 b} : Finset (Fin d.1.rank)))
    (fun b => Or.inl fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hfix b)
    (fun a : Fin 4 => Fin.castLE h4 a) (fun a => Or.inl (hfix a)) ?_
  · rwa [Fintype.card_fin] at h
  · refine det_cast_ne_zero (Matrix.of fun a b : Fin 4 =>
      (∑ i ∈ ({Fin.castLE h4 b} : Finset (Fin d.1.rank)),
        CartanMatrix.D d.1.rank i (Fin.castLE h4 a) : ℤ)) 5 ?_ ?_
    · rw [minor6_eq _ h4 h6]
      decide
    · have : Fact s.Prime := ⟨hs⟩
      intro h0
      rw [show ((5 : ℤ) : ZMod s) = ((5 : ℕ) : ZMod s) by norm_num,
        ZMod.natCast_eq_zero_iff] at h0
      exact hs5 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).mp h0)

theorem hasWitness_torus_five (h2 : d.1.characteristic = 2) (hq : 4 ≤ d.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ d.1.fieldOrder - 1) (h5 : d.1.rank = 5) :
    HasWitness d.Group s 4 := by
  have h4 := four_le d
  have h := hasWitness_torus d h2 hq hs hsq (nodeSets5 d.1.rank h4) (fun b => ?_)
    (rows5 d.1.rank h4) (fun a => ?_) ?_
  · rwa [Fintype.card_fin] at h
  · fin_cases b
    · exact Or.inl fun i hi => by simp [nodeSets5] at hi; rw [hi]; simp; omega
    · exact Or.inl fun i hi => by simp [nodeSets5] at hi; rw [hi]; simp; omega
    · exact Or.inl fun i hi => by simp [nodeSets5] at hi; rw [hi]; simp; omega
    · exact Or.inr rfl
  · fin_cases a
    · exact Or.inl (by simp [rows5]; omega)
    · exact Or.inl (by simp [rows5]; omega)
    · exact Or.inl (by simp [rows5]; omega)
    · exact Or.inr rfl
  · refine det_cast_ne_zero (Matrix.of fun a b => (∑ i ∈ nodeSets5 d.1.rank h4 b,
      CartanMatrix.D d.1.rank i (rows5 d.1.rank h4 a) : ℤ)) 2 ?_ (two_ne_zero_zmod hs hs2)
    rw [minor5_eq _ h4 h5]
    decide

theorem hasWitness_torus_four (h2 : d.1.characteristic = 2) (hq : 4 ≤ d.1.fieldOrder) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ d.1.fieldOrder - 1) (hr : d.1.rank = 4) :
    HasWitness d.Group s 3 := by
  have h4 := four_le d
  have h := hasWitness_torus d h2 hq hs hsq (nodeSets4 d.1.rank h4) (fun b => ?_)
    (rows4 d.1.rank h4) (fun a => ?_) ?_
  · rwa [Fintype.card_fin] at h
  · fin_cases b
    · exact Or.inl fun i hi => by simp [nodeSets4] at hi; rw [hi]; simp; omega
    · exact Or.inl fun i hi => by simp [nodeSets4] at hi; rw [hi]; simp; omega
    · exact Or.inr rfl
  · fin_cases a
    · exact Or.inl (by simp [rows4]; omega)
    · exact Or.inl (by simp [rows4]; omega)
    · exact Or.inr rfl
  · refine det_cast_ne_zero (Matrix.of fun a b => (∑ i ∈ nodeSets4 d.1.rank h4 b,
      CartanMatrix.D d.1.rank i (rows4 d.1.rank h4 a) : ℤ)) 2 ?_ (two_ne_zero_zmod hs hs2)
    rw [minor4_eq _ h4 hr]
    decide

end CFSG.RankThree.PartTwo.Census.Spin.CarrierTD

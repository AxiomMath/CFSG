module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)

theorem tor_smul (hζ : ζ ^ 3 = 1) (k : ZMod 3) (f : Fin F.s → ZMod 3) :
    F.tor (k • f) = F.tor f ^ k.val := by
  have h : ∀ m : ℕ, F.tor ((m : ZMod 3) • f) = F.tor f ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, zero_smul, F.tor_zero, pow_zero]
    | succ m ih => rw [Nat.cast_succ, add_smul, one_smul, F.tor_add hζ, ih, pow_succ]
  calc F.tor (k • f) = F.tor ((k.val : ZMod 3) • f) := by rw [ZMod.natCast_zmod_val]
    _ = F.tor f ^ k.val := h k.val

noncomputable def torHom (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin F.s → ZMod 3) →* StatedSp n K where
  toFun f := F.tor (Multiplicative.toAdd f)
  map_one' := F.tor_zero
  map_mul' f g := F.tor_add hζ (Multiplicative.toAdd f) (Multiplicative.toAdd g)

@[expose] noncomputable def torSub (hζ : ζ ^ 3 = 1) (S : AddSubgroup (Fin F.s → ZMod 3)) :
    Subgroup (StatedSp n K) :=
  S.toSubgroup.map (torHom F hζ)

theorem mem_torSub (hζ : ζ ^ 3 = 1) {S : AddSubgroup (Fin F.s → ZMod 3)} {g : StatedSp n K} :
    g ∈ torSub F hζ S ↔ ∃ f ∈ S, F.tor f = g := by
  rw [torSub, Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, hg⟩ => ⟨x.toAdd, hx, hg⟩,
    fun ⟨f, hf, hg⟩ => ⟨Multiplicative.ofAdd f, hf, hg⟩⟩

theorem card_torSub (hζo : IsPrimitiveRoot ζ 3) (S : AddSubgroup (Fin F.s → ZMod 3)) :
    Nat.card (torSub F hζo.pow_eq_one S) = Nat.card S := by
  have hinj : Function.Injective (torHom F hζo.pow_eq_one) := by
    intro x y h
    have h' : F.tor x.toAdd = F.tor y.toAdd := h
    exact Multiplicative.toAdd.injective (F.tor_injective hζo h')
  rw [torSub, Subgroup.card_map_of_injective hinj]
  exact (Nat.card_congr (Equiv.subtypeEquiv (Multiplicative.ofAdd)
    (fun _ => Iff.rfl))).symm

@[expose] def coordSub {s : ℕ} (T : Finset (Fin s)) : AddSubgroup (Fin s → ZMod 3) where
  carrier := {f | ∀ i, i ∉ T → f i = 0}
  add_mem' hf hg i hi := by rw [Pi.add_apply, hf i hi, hg i hi, add_zero]
  zero_mem' _ _ := rfl
  neg_mem' hf i hi := by rw [Pi.neg_apply, hf i hi, neg_zero]

theorem mem_coordSub {s : ℕ} {T : Finset (Fin s)} {f : Fin s → ZMod 3} :
    f ∈ coordSub T ↔ ∀ i, i ∉ T → f i = 0 := Iff.rfl

theorem card_coordSub {s : ℕ} (T : Finset (Fin s)) : Nat.card (coordSub T) = 3 ^ T.card := by
  have e : ↥(coordSub T) ≃ (↥T → ZMod 3) :=
    { toFun := fun f i => (f : Fin s → ZMod 3) i
      invFun := fun g => ⟨fun i => if h : i ∈ T then g ⟨i, h⟩ else 0, by
        intro i hi
        simp [hi]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ T
        · simp [h]
        · simp only [h, dite_false]
          exact (f.2 i h).symm
      right_inv := fun g => by
        funext i
        simp }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem mem_closure_pair_iff (hζ : ζ ^ 3 = 1) {c d : Fin F.s → ZMod 3}
    {g : StatedSp n K} :
    g ∈ Subgroup.closure {F.tor c, F.tor d} ↔ ∃ α β : ZMod 3, g = F.tor (α • c + β • d) := by
  constructor
  · intro hg
    refine Subgroup.closure_induction
      (k := ({F.tor c, F.tor d} : Set (StatedSp n K)))
      (p := fun g _ => ∃ α β : ZMod 3, g = F.tor (α • c + β • d)) ?_ ?_ ?_ ?_ hg
    · intro x hx
      rcases hx with hx | hx
      · subst hx
        exact ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
      · subst hx
        exact ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
    · exact ⟨0, 0, by rw [zero_smul, zero_smul, add_zero, F.tor_zero]⟩
    · rintro x y hx hy ⟨α, β, rfl⟩ ⟨α', β', rfl⟩
      refine ⟨α + α', β + β', ?_⟩
      rw [← F.tor_add hζ, add_smul, add_smul]
      congr 1
      abel
    · rintro x hx ⟨α, β, rfl⟩
      refine ⟨-α, -β, ?_⟩
      have h1 : F.tor ((-α) • c + (-β) • d) * F.tor (α • c + β • d) = 1 := by
        rw [← F.tor_add hζ]
        have h2 : (-α) • c + (-β) • d = -(α • c + β • d) := by
          rw [neg_smul, neg_smul, neg_add]
        rw [h2, neg_add_cancel, F.tor_zero]
      exact (eq_inv_of_mul_eq_one_left h1).symm
  · rintro ⟨α, β, rfl⟩
    rw [F.tor_add hζ, tor_smul F hζ, tor_smul F hζ]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem isElemAbelian_closure_pair (hζ : ζ ^ 3 = 1) (c d : Fin F.s → ZMod 3) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure {F.tor c, F.tor d}) := by
  refine ⟨isMulCommutative_iff.mpr fun x y => ?_, fun x hx => ?_⟩
  · obtain ⟨α, β, hx1⟩ := (mem_closure_pair_iff F hζ).mp x.2
    obtain ⟨α', β', hy1⟩ := (mem_closure_pair_iff F hζ).mp y.2
    exact Subtype.ext (by
      show (x : StatedSp n K) * (y : StatedSp n K) =
        (y : StatedSp n K) * (x : StatedSp n K)
      rw [hx1, hy1]
      exact F.tor_comm hζ _ _)
  · obtain ⟨α, β, hx1⟩ := (mem_closure_pair_iff F hζ).mp hx
    have h3 : (x : StatedSp n K) ^ 3 = 1 := by
      rw [hx1]
      exact F.tor_pow_three hζ (α • c + β • d)
    simpa using h3

theorem isPGroup_closure_pair (hζ : ζ ^ 3 = 1) (c d : Fin F.s → ZMod 3) :
    IsPGroup 3 (Subgroup.closure {F.tor c, F.tor d}) := by
  intro x
  obtain ⟨α, β, hx⟩ := (mem_closure_pair_iff F hζ).mp x.2
  refine ⟨1, ?_⟩
  have h3 : (x : StatedSp n K) ^ 3 = 1 := by
    rw [hx]
    exact F.tor_pow_three hζ (α • c + β • d)
  rw [pow_one]
  exact Subtype.ext h3

theorem card_closure_pair (hζo : IsPrimitiveRoot ζ 3) {c d : Fin F.s → ZMod 3}
    (hind : ∀ α β : ZMod 3, α • c + β • d = 0 → α = 0 ∧ β = 0) :
    Nat.card (Subgroup.closure {F.tor c, F.tor d}) = 9 := by
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hbij : Function.Bijective (fun p : ZMod 3 × ZMod 3 =>
      (⟨F.tor (p.1 • c + p.2 • d), (mem_closure_pair_iff F hζ).mpr ⟨p.1, p.2, rfl⟩⟩ :
        Subgroup.closure {F.tor c, F.tor d})) := by
    constructor
    · rintro ⟨α, β⟩ ⟨α', β'⟩ h
      have h' : F.tor (α • c + β • d) = F.tor (α' • c + β' • d) := congrArg Subtype.val h
      have h'' := F.tor_injective hζo h'
      have hzero : (α - α') • c + (β - β') • d = 0 := by
        have h1 : (α - α') • c + (β - β') • d
            = (α • c + β • d) - (α' • c + β' • d) := by module
        rw [h1, sub_eq_zero.mpr h'']
      obtain ⟨h1, h2⟩ := hind (α - α') (β - β') hzero
      exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
    · rintro ⟨g, hg⟩
      obtain ⟨α, β, hg'⟩ := (mem_closure_pair_iff F hζ).mp hg
      exact ⟨(α, β), Subtype.ext hg'.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_zmod]

theorem not_isCyclic_closure_pair (hζo : IsPrimitiveRoot ζ 3) {c d : Fin F.s → ZMod 3}
    (hind : ∀ α β : ZMod 3, α • c + β • d = 0 → α = 0 ∧ β = 0) :
    ¬ IsCyclic (Subgroup.closure {F.tor c, F.tor d}) := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  have h3 : g ^ 3 = 1 := by
    obtain ⟨α, β, hg'⟩ := (mem_closure_pair_iff F hζo.pow_eq_one).mp g.2
    exact Subtype.ext (by
      show (g : StatedSp n K) ^ 3 = 1
      rw [hg']
      exact F.tor_pow_three hζo.pow_eq_one (α • c + β • d))
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rw [card_closure_pair F hζo hind] at hg
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem eq_closure_pair (hζo : IsPrimitiveRoot ζ 3) {c d : Fin F.s → ZMod 3}
    (hind : ∀ α β : ZMod 3, α • c + β • d = 0 → α = 0 ∧ β = 0) {D : Subgroup (StatedSp n K)}
    (hD : Nat.card D = 9) (hc : F.tor c ∈ D) (hd : F.tor d ∈ D) :
    D = Subgroup.closure {F.tor c, F.tor d} := by
  have hle : Subgroup.closure {F.tor c, F.tor d} ≤ D := by
    refine (Subgroup.closure_le D).mpr ?_
    rintro x (rfl | rfl)
    · exact hc
    · exact hd
  have hcard := card_closure_pair F hζo hind
  haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hD])).symm

theorem spPull_phi3_le_spSupported (f : Fin F.s → ZMod 3) :
    spPull (F.tor f) (ChoiceTwo.phi3 K) ≤ spSupported (F.tor f) {ChoiceTwo.phi3 K} := by
  have h : spPull (F.tor f) (ChoiceTwo.phi3 K) ≤
      spSupported (F.tor f) {ChoiceTwo.phi3 K, reciprocalPolynomial (ChoiceTwo.phi3 K)} := by
    change (specialBlock (spForm n K) (spLin n K (F.tor f)) (ChoiceTwo.phi3 K)).comap
        (spLin n K) ≤
      (supportedUnitary (spForm n K) (spLin n K (F.tor f))
        {ChoiceTwo.phi3 K, reciprocalPolynomial (ChoiceTwo.phi3 K)}).comap (spLin n K)
    rw [← orbitFactor_spForm]
    exact Subgroup.comap_mono specialBlock_le_orbitFactor
  rwa [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton] at h

theorem isQuasisimple_spPull_phi3 [NeZero n] [Module.Finite K L] (hK : Nat.card K = 2)
    (hζo : IsPrimitiveRoot ζ 3) (hL : Module.finrank K L = 2) {f : Fin F.s → ZMod 3}
    (hf : 4 ≤ (F.suppSet f).card) :
    CFSG.IsQuasisimple ↥(spPull (F.tor f) (ChoiceTwo.phi3 K)) := by
  have hf0 : f ≠ 0 := by
    intro h
    rw [h] at hf
    simp [ChoiceTwo.SpFrame.suppSet] at hf
  have blocks := F.blocks_tor hK hζo hf0
  have hmem : ChoiceTwo.phi3 K ∈ primaryFactors (spEnd (F.tor f)) := by
    by_contra hnm
    have hbot := primaryComponent_eq_bot_of_not_mem (ChoiceTwo.phi3_irreducible hK)
      ChoiceTwo.monic_phi3 hnm
    have hm := F.finrank_phi3_tor hζo hL f
    rw [hbot, finrank_bot] at hm
    omega
  have hself : reciprocalPolynomial
        ((⟨ChoiceTwo.phi3 K, hmem⟩ : primaryFactors (spEnd (F.tor f))) : K[X]) =
      (⟨ChoiceTwo.phi3 K, hmem⟩ : primaryFactors (spEnd (F.tor f))) := ChoiceTwo.reciprocal_phi3
  obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
    (blocks.selfDual ⟨ChoiceTwo.phi3 K, hmem⟩ ChoiceTwo.phi3_ne_X_sub_one hself).exists_half
  have hm : primaryMultiplicity (spEnd (F.tor f)) (ChoiceTwo.phi3 K) = (F.suppSet f).card :=
    F.mult_phi3_tor hK hζo hL f
  refine SevSpNs.isQuasisimple_spPull_selfDual (r := n) (x := F.tor f)
    (h := (⟨ChoiceTwo.phi3 K, hmem⟩ : primaryFactors (spEnd (F.tor f))))
    (f := 1) (d := d) hself hE hHf hHfl φ hφ ?_ ⟨?_, ?_⟩
  · rw [hm]
    omega
  · rintro h2
    rw [hm] at h2
    omega
  · rintro h3
    rw [hm] at h3
    omega

private theorem indep_of_coord {h₁ h₂ h₃ : Fin F.s → ZMod 3} {i₁ i₂ : Fin F.s}
    (h1i : h₁ i₁ ≠ 0) (h2i : h₂ i₂ ≠ 0) (h3ne : h₃ ≠ 0) (h2i1 : h₂ i₁ = 0)
    (h3i1 : h₃ i₁ = 0) (h1i2 : h₁ i₂ = 0) (h3i2 : h₃ i₂ = 0) :
    ∀ α β γ : ZMod 3, α • h₁ + β • h₂ + γ • h₃ = 0 → α = 0 ∧ β = 0 ∧ γ = 0 := by
  intro α β γ h
  have hα : α = 0 := by
    have h1 := congrFun h i₁
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, h2i1, h3i1,
      mul_zero, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right h1i
  have hβ : β = 0 := by
    have h2 := congrFun h i₂
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, h1i2, h3i2,
      mul_zero, add_zero, zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_right h2i
  refine ⟨hα, hβ, ?_⟩
  rw [hα, hβ, zero_smul, zero_smul, zero_add, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_right h3ne

theorem false_of_le_spSupported_phi3 [NeZero n] [Module.Finite K L] (hK : Nat.card K = 2)
    (hζo : IsPrimitiveRoot ζ 3) (hL : Module.finrank K L = 2) {f : Fin F.s → ZMod 3}
    {Q : Subgroup (StatedSp n K)}
    (hQ : CFSG.Assembly.IsComponentOf Q (Subgroup.centralizer {F.tor f}))
    (hQs : Q ≤ spSupported (F.tor f) {ChoiceTwo.phi3 K}) (h27 : ¬ 27 ∣ Nat.card Q) : False := by
  classical
  have hQq : CFSG.IsQuasisimple ↥Q :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Q).1 hQ.2.2
  have hperf : ⁅Q, Q⁆ = Q := LayerFacts.ggCommutator_eq_of_isQuasisimple hQq
  by_cases hsmall : (F.suppSet f).card ≤ 3
  · have hQle : Q ≤ spFixedFactor (F.tor f) :=
      F.le_spFixedFactor hK hζo hL hsmall hperf hQ.1
    exact SevSpNs.false_of_le_of_commute hQ.2.2 le_rfl fun g hg g' hg' =>
      ChoiceTwo.commute_of_mem_spFixedFactor hK (F.tor_pow_three hζo.pow_eq_one f)
        (O := {ChoiceTwo.phi3 K})
        (by rw [Set.mem_singleton_iff]; exact fun h => ChoiceTwo.phi3_ne_X_sub_one h.symm)
        (hQle hg) (hQs hg')
  · have hbig : 4 ≤ (F.suppSet f).card := by omega
    have hQeq : Q = spPull (F.tor f) (ChoiceTwo.phi3 K) := by
      have hLO : Q ≤ spSupported (F.tor f)
          {ChoiceTwo.phi3 K, reciprocalPolynomial (ChoiceTwo.phi3 K)} := by
        rwa [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton]
      exact SevSpNs.eq_spPull_of_le hQ hLO (isQuasisimple_spPull_phi3 F hK hζo hL hbig)
    obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hbig
    obtain ⟨e1, e2, e3, e4, h12, h13, h14, h23, h24, h34, hs_eq⟩ :=
      Finset.card_eq_four.mp hsc
    rw [hs_eq] at hs
    have hf1 : f e1 ≠ 0 := F.mem_suppSet.mp (hs (by simp))
    have hf2 : f e2 ≠ 0 := F.mem_suppSet.mp (hs (by simp))
    have hf3 : f e3 ≠ 0 := F.mem_suppSet.mp (hs (by simp))
    have hf4 : f e4 ≠ 0 := F.mem_suppSet.mp (hs (by simp))
    have hpair : ∀ i j : Fin F.s, f i ≠ 0 → f j ≠ 0 → i ≠ j →
        ∃ h : Fin F.s → ZMod 3, h ≠ 0 ∧ F.tor h ∈ spPull (F.tor f) (ChoiceTwo.phi3 K) ∧
          ∀ k, h k ≠ 0 → k = i ∨ k = j := by
      intro i j hi hj hij
      haveI : Fact (Irreducible (ChoiceTwo.phi3 K)) := ⟨ChoiceTwo.phi3_irreducible hK⟩
      have hu : F.tor (Pi.single i (1 : ZMod 3)) ∈ spSupported (F.tor f) {ChoiceTwo.phi3 K} :=
        F.tor_mem_spSupported hK hζo f _
          (fun k hk => by rw [Pi.single_eq_of_ne (by rintro rfl; exact hi hk)])
          (Set.mem_singleton _)
      have hv : F.tor (Pi.single j (1 : ZMod 3)) ∈ spSupported (F.tor f) {ChoiceTwo.phi3 K} :=
        F.tor_mem_spSupported hK hζo f _
          (fun k hk => by rw [Pi.single_eq_of_ne (by rintro rfl; exact hj hk)])
          (Set.mem_singleton _)
      have hu' : F.tor (Pi.single i (1 : ZMod 3)) ∈
          spSupported (F.tor f) {ChoiceTwo.phi3 K, reciprocalPolynomial (ChoiceTwo.phi3 K)} := by
        rwa [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton]
      have hv' : F.tor (Pi.single j (1 : ZMod 3)) ∈
          spSupported (F.tor f) {ChoiceTwo.phi3 K, reciprocalPolynomial (ChoiceTwo.phi3 K)} := by
        rwa [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton]
      obtain ⟨a, b, ha, hb, hab, hmem⟩ := SevSpNs.exists_pow_mul_pow_mem_spPull
        (p := 3) Nat.prime_three hu' hv' (F.tor_pow_three hζo.pow_eq_one _)
        (F.tor_pow_three hζo.pow_eq_one _)
      refine ⟨(a : ZMod 3) • Pi.single i 1 + (b : ZMod 3) • Pi.single j 1, ?_, ?_, ?_⟩
      · rcases hab with ha0 | hb0
        · have hai : (a : ZMod 3) ≠ 0 := by
            intro h
            have h1 : (a : ZMod 3).val = 0 := (ZMod.val_eq_zero _).mpr h
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha] at h1
            exact ha0 h1
          intro h0
          have h1 := congrFun h0 i
          simp [hij] at h1
          exact hai h1
        · have hbi : (b : ZMod 3) ≠ 0 := by
            intro h
            have h1 : (b : ZMod 3).val = 0 := (ZMod.val_eq_zero _).mpr h
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb] at h1
            exact hb0 h1
          intro h0
          have h1 := congrFun h0 j
          simp [hij] at h1
          exact hbi h1
      · have hmem' : F.tor ((a : ZMod 3) • Pi.single i 1 + (b : ZMod 3) • Pi.single j 1) =
            F.tor (Pi.single i 1) ^ a * F.tor (Pi.single j 1) ^ b := by
          rw [F.tor_add hζo.pow_eq_one, tor_smul F hζo.pow_eq_one,
            tor_smul F hζo.pow_eq_one, ZMod.val_natCast, ZMod.val_natCast,
            Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        rw [hmem']
        exact hmem
      · intro k hk
        by_contra hc
        push Not at hc
        obtain ⟨hki, hkj⟩ := hc
        exact hk (by simp [hki, hkj])
    have hex : ∀ {i j : Fin F.s}, f i ≠ 0 → f j ≠ 0 → i ≠ j →
        ∃ (h : Fin F.s → ZMod 3) (i' : Fin F.s), h i' ≠ 0 ∧ (i' = i ∨ i' = j) ∧
          F.tor h ∈ spPull (F.tor f) (ChoiceTwo.phi3 K) ∧
            ∀ k, h k ≠ 0 → k = i ∨ k = j := by
      intro i j hi hj hij
      obtain ⟨h, hne, hmem, hsup⟩ := hpair i j hi hj hij
      by_cases hhi : h i ≠ 0
      · exact ⟨h, i, hhi, Or.inl rfl, hmem, hsup⟩
      · push Not at hhi
        have hhj : h j ≠ 0 := by
          intro h0
          exact hne (funext fun k => by
            by_cases hk : h k = 0
            · exact hk
            · rcases hsup k hk with rfl | rfl
              · exact hhi
              · exact h0)
        exact ⟨h, j, hhj, Or.inr rfl, hmem, hsup⟩
    obtain ⟨h₁, i1, hi1, hi1e, hmem₁, hsup₁⟩ := hex hf1 hf2 h12
    obtain ⟨h₂, i2, hi2, hi2e, hmem₂, hsup₂⟩ := hex hf3 hf4 h34
    let j1 : Fin F.s := if i1 = e1 then e2 else e1
    let j2 : Fin F.s := if i2 = e3 then e4 else e3
    have hj1e : j1 = e1 ∨ j1 = e2 := by
      by_cases h : i1 = e1
      · exact Or.inr (by simp [j1, h])
      · rcases hi1e with h' | h'
        · exact absurd h' h
        · exact Or.inl (by simp [j1, h'])
    have hj2e : j2 = e3 ∨ j2 = e4 := by
      by_cases h : i2 = e3
      · exact Or.inr (by simp [j2, h])
      · rcases hi2e with h' | h'
        · exact absurd h' h
        · exact Or.inl (by simp [j2, h'])
    have hi1j1 : i1 ≠ j1 := by
      by_cases h : i1 = e1
      · have hj : j1 = e2 := by simp [j1, h]
        rw [h, hj]
        exact h12
      · have hj : j1 = e1 := by simp [j1, h]
        rw [hj]
        exact h
    have hi2j2 : i2 ≠ j2 := by
      by_cases h : i2 = e3
      · have hj : j2 = e4 := by simp [j2, h]
        rw [h, hj]
        exact h34
      · have hj : j2 = e3 := by simp [j2, h]
        rw [hj]
        exact h
    have hfj1 : f j1 ≠ 0 := by
      rcases hj1e with h | h
      · rw [h]
        exact hf1
      · rw [h]
        exact hf2
    have hfj2 : f j2 ≠ 0 := by
      rcases hj2e with h | h
      · rw [h]
        exact hf3
      · rw [h]
        exact hf4
    have hj1j2 : j1 ≠ j2 := by
      rcases hj1e with h | h <;> rcases hj2e with h' | h'
      · rw [h, h']
        exact h13
      · rw [h, h']
        exact h14
      · rw [h, h']
        exact h23
      · rw [h, h']
        exact h24
    obtain ⟨h₃, hne₃, hmem₃, hsup₃⟩ := hpair j1 j2 hfj1 hfj2 hj1j2
    have key_ne : ∀ {x y : Fin F.s}, (x = e1 ∨ x = e2) → (y = e3 ∨ y = e4) → x ≠ y := by
      rintro x y (rfl | rfl) (rfl | rfl)
      exacts [h13, h14, h23, h24]
    have key_ne' : ∀ {x y : Fin F.s}, (x = e3 ∨ x = e4) → (y = e1 ∨ y = e2) → x ≠ y := by
      rintro x y (rfl | rfl) (rfl | rfl)
      exacts [Ne.symm h13, Ne.symm h23, Ne.symm h14, Ne.symm h24]
    have key_same : ∀ {x : Fin F.s}, (x = e1 ∨ x = e2) → (x = e3 ∨ x = e4) → False := by
      intro x h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h | h
      · exact h13 h
      · exact h14 h
      · exact h23 h
      · exact h24 h
    have key_same' : ∀ {x : Fin F.s}, (x = e3 ∨ x = e4) → (x = e1 ∨ x = e2) → False := by
      intro x h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h | h
      · exact h13 h.symm
      · exact h23 h.symm
      · exact h14 h.symm
      · exact h24 h.symm
    have h2i1 : h₂ i1 = 0 := by
      by_contra hne
      exact key_same hi1e (hsup₂ i1 hne)
    have h3i1 : h₃ i1 = 0 := by
      by_contra hne
      rcases hsup₃ i1 hne with h | h
      · exact hi1j1 h
      · exact key_ne hi1e hj2e h
    have h1i2 : h₁ i2 = 0 := by
      by_contra hne
      exact key_same' hi2e (hsup₁ i2 hne)
    have h3i2 : h₃ i2 = 0 := by
      by_contra hne
      rcases hsup₃ i2 hne with h | h
      · exact key_ne' hi2e hj1e h
      · exact hi2j2 h
    have hindep := indep_of_coord F hi1 hi2 hne₃ h2i1 h3i1 h1i2 h3i2
    let D : Submodule (ZMod 3) (Fin F.s → ZMod 3) :=
      { carrier := {h | F.tor h ∈ spPull (F.tor f) (ChoiceTwo.phi3 K)}
        add_mem' := by
          intro a b ha hb
          change F.tor (a + b) ∈ spPull (F.tor f) (ChoiceTwo.phi3 K)
          rw [F.tor_add hζo.pow_eq_one]
          exact mul_mem ha hb
        zero_mem' := by
          change F.tor 0 ∈ spPull (F.tor f) (ChoiceTwo.phi3 K)
          rw [F.tor_zero]
          exact one_mem _
        smul_mem' := by
          intro c h hh
          change F.tor (c • h) ∈ spPull (F.tor f) (ChoiceTwo.phi3 K)
          rw [tor_smul F hζo.pow_eq_one]
          exact pow_mem hh _ }
    let W : Submodule (ZMod 3) (Fin F.s → ZMod 3) :=
      Submodule.span (ZMod 3) (Set.range ![h₁, h₂, h₃])
    have hDW : W ≤ D := by
      change Submodule.span (ZMod 3) (Set.range ![h₁, h₂, h₃]) ≤ D
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact hmem₁
      · exact hmem₂
      · exact hmem₃
    have hli : LinearIndependent (ZMod 3) ![h₁, h₂, h₃] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : g 0 • h₁ + g 1 • h₂ + g 2 • h₃ = 0 := by
        simpa [Fin.sum_univ_three] using hg
      obtain ⟨g0, g1, g2⟩ := hindep (g 0) (g 1) (g 2) hg'
      intro i
      fin_cases i
      · exact g0
      · exact g1
      · exact g2
    have hWcard : Nat.card ↥W = 27 := by
      have hfin : Module.finrank (ZMod 3) ↥W = 3 := by
        change Module.finrank (ZMod 3)
          ↥(Submodule.span (ZMod 3) (Set.range ![h₁, h₂, h₃])) = 3
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ↥W), hfin, Nat.card_zmod]
      norm_num
    have hcardS : Nat.card ↥(W.toAddSubgroup) = 27 := hWcard
    have hle : torSub F hζo.pow_eq_one W.toAddSubgroup ≤ Q := by
      rw [hQeq]
      rintro g ⟨h, hh, rfl⟩
      exact hDW (show h ∈ W from hh)
    have hdvd : 27 ∣ Nat.card Q := by
      have h2 : Nat.card (torSub F hζo.pow_eq_one W.toAddSubgroup) ∣ Nat.card Q :=
        Subgroup.card_dvd_of_le hle
      rwa [card_torSub F hζo W.toAddSubgroup, hcardS] at h2
    exact h27 hdvd

end A6InsideSp

end CFSG.StandardType

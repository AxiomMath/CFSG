module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiCount

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open CFSG.ClassicalInvolution.Solomon73

set_option maxRecDepth 100000 in
theorem pact_e45_cases : ∀ π : Perm (Fin 6), InS ⟨pact π (v6 [4, 5]), 1⟩ →
    pact π (v6 [4, 5]) = v6 [0, 1] ∨ pact π (v6 [4, 5]) = v6 [2, 3] ∨
      pact π (v6 [4, 5]) = v6 [4, 5] := by decide +kernel

theorem cSp_sc_vec :
    cSp (sc [0]) = ⟨v6 [0, 1], 1⟩ ∧ cSp (sc [1]) = ⟨v6 [2, 3], 1⟩ ∧
      cSp (sc [2]) = ⟨v6 [4, 5], 1⟩ := by
  decide

theorem actXi_sc : actXi (sc [2]) = sc [0] ∧ actXi (sc [0]) = sc [1] ∧
    actXi (sc [0, 1]) = sc [1, 2] ∧ actXi (sc [1, 2]) = sc [0, 2] := by decide

theorem sc_ne : sc [0] ≠ sc [1] ∧ sc [0] ≠ sc [2] ∧ sc [1] ≠ sc [2] ∧ sc [0, 1] ≠ sc [0, 2] ∧
    sc [0, 1] ≠ sc [1, 2] ∧ sc [0, 2] ≠ sc [1, 2] := by decide

theorem mem_scOrb_facts : sc [0, 1, 2] ∈ scOrb 0 ∧ sc [2] ∈ scOrb 1 ∧ sc [0, 1] ∈ scOrb 3 ∧
    sc [2, 3, 4, 5] ∈ scOrb 8 := by decide

theorem sc012_eq : sc [0, 1, 2] = ((1 : Fin 3 → ZMod 2), (0 : Fin 3 → ZMod 2)) := by decide

theorem perm_cSp_2345 : (cSp (sc [2, 3, 4, 5])).perm ≠ 1 ∧
    (cSp (sc [2, 3, 4, 5])).perm ≠ swap 4 5 := by decide

@[expose] def orbSize : Fin 10 → ℕ := ![1, 3, 6, 3, 12, 12, 6, 12, 4, 4]

set_option maxRecDepth 100000 in
theorem orbit_cases : ∀ I : Finset (Fin 10), 0 ∈ I → 1 ∉ I → 3 ∉ I →
    2 ≤ ∑ i ∈ I, orbSize i → ∑ i ∈ I, orbSize i ≤ 15 →
    I = {0, 2} ∨ I = {0, 6} ∨ ∑ i ∈ I, orbSize i = 11 ∨ ∑ i ∈ I, orbSize i = 13 ∨
      (I ⊆ {0, 8, 9} ∧ 5 ≤ ∑ i ∈ I, orbSize i ∧ (8 ∈ I ∨ 9 ∈ I)) ∨
      (∑ i ∈ I, orbSize i = 15 ∧ 8 ∈ I) := by
  decide +kernel

@[expose] def U4 : Finset SC :=
  ([[], [0], [0, 1], [0, 1, 2], [0, 1, 2, 3, 4, 5], [0, 1, 3, 4, 5], [0, 2], [0, 2, 3, 4, 5],
    [0, 3, 4, 5], [1], [1, 2], [1, 2, 3, 4, 5], [1, 3, 4, 5], [2], [2, 3, 4, 5], [3, 4, 5]].map
    sc).toFinset

theorem U4_add : ∀ x ∈ U4, ∀ y ∈ U4, x + y ∈ U4 := by decide

theorem U4_card : U4.card = 16 := by decide

theorem zero_mem_U4 : (0 : SC) ∈ U4 := by decide

theorem scOrb_sub_U4 : scOrb 0 ⊆ U4 ∧ scOrb 8 ⊆ U4 ∧ scOrb 9 ⊆ U4 := by decide

theorem sc2_decomp : sc [2] = sc [0, 1, 2] + sc [0, 1, 2, 3, 4, 5] + sc [2, 3, 4, 5] ∧
    sc [0, 1, 2, 3, 4, 5] ∈ scOrb 8 ∧ sc [2, 3, 4, 5] ∈ scOrb 8 ∧
    sc [2] = sc [0, 1, 2] + sc [3, 4, 5] + sc [0, 1, 3, 4, 5] ∧ sc [3, 4, 5] ∈ scOrb 9 ∧
    sc [0, 1, 3, 4, 5] ∈ scOrb 9 := by decide

theorem card_SC : Nat.card SC = 64 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem neg_SC (x : SC) : -x = x := neg_eq_of_add_eq_zero_right (SC_add_self x)

theorem card_le_63 {F₁ F₂ F₃ : Finset SC} (h₁ : (0 : SC) ∉ F₁) (h₂ : (0 : SC) ∉ F₂)
    (h₃ : (0 : SC) ∉ F₃) (d₁₂ : Disjoint F₁ F₂) (d₁₃ : Disjoint F₁ F₃) (d₂₃ : Disjoint F₂ F₃) :
    F₁.card + F₂.card + F₃.card ≤ 63 := by
  have hsub : F₁ ∪ F₂ ∪ F₃ ⊆ Finset.univ.erase 0 := by
    intro c hc
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact h₁ hc
      · exact h₂ hc
    · exact h₃ hc
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d₁₃, d₂₃⟩),
    Finset.card_union_of_disjoint d₁₂, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_SC] at hc
  omega

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

abbrev NA : Subgroup G := Subgroup.normalizer (Y.A : Set G)

abbrev XN : Subgroup G := Y.NA ⊓ Subgroup.centralizer ({z} : Set G)

theorem ϑ_conj_vec {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) {w : Fin 6 → ZMod 2}
    (hyw : (Y.ϑ ⟨y, hy⟩ : Wr 6) = ⟨w, 1⟩) :
    (Y.ϑ ⟨x * y * x⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)⟩ :
      Wr 6) = ⟨pact (Y.ϑ ⟨x, hx⟩ : Wr 6).perm w, 1⟩ := by
  have h : (⟨x * y * x⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)⟩ :
      ↥(Subgroup.centralizer ({z} : Set G))) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ := rfl
  rw [h]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyw]
  set W := (Y.ϑ ⟨x, hx⟩ : Wr 6) with hW
  have hW' : W = ⟨W.vec, W.perm⟩ := rfl
  rw [hW', conj_vec_gen]

theorem conj_pi3_mem {x : G} (hx : x ∈ Y.XN) :
    x * Y.π3 * x⁻¹ = Y.σA (sc [0]) ∨ x * Y.π3 * x⁻¹ = Y.σA (sc [1]) ∨
      x * Y.π3 * x⁻¹ = Y.σA (sc [2]) := by
  have hxC := hx.2
  have h1 := Y.ϑ_conj_vec hxC Y.π3_mem_C (w := v6 [4, 5]) (by rw [Y.ϑ_π3]; rfl)
  have hA : x * Y.π3 * x⁻¹ ∈ Y.A :=
    (Subgroup.mem_normalizer_iff.mp hx.1 _).mp (by rw [← Y.σA_pi3]; exact Y.σA_mem_A _)
  obtain ⟨hC', hS⟩ := Y.mem_lift.mp hA
  rw [h1] at hS
  obtain ⟨h0, h1', h2'⟩ := cSp_sc_vec
  have key : ∀ c : SC, cSp c = ⟨pact (Y.ϑ ⟨x, hxC⟩ : Wr 6).perm (v6 [4, 5]), 1⟩ →
      x * Y.π3 * x⁻¹ = Y.σA c := by
    intro c hc
    apply Y.eq_of_ϑ_eq (hx := hC') (hy := Y.σA_mem_C c)
    rw [Y.ϑ_σA, hc]
    exact h1
  rcases pact_e45_cases _ hS with h | h | h
  · exact Or.inl (key _ (by rw [h0, h]))
  · exact Or.inr (Or.inl (key _ (by rw [h1', h])))
  · exact Or.inr (Or.inr (key _ (by rw [h2', h])))

@[expose] noncomputable def ξ : G := Y.ι ⟨wXi, wXi_mem_Wsub⟩

theorem ξ_mem_XN : Y.ξ ∈ Y.XN := ⟨Y.gens_mem_normalizer.2.2.2, Y.ι_mem_C _⟩

theorem conj_ξ (c : SC) : Y.ξ * Y.σA c * Y.ξ⁻¹ = Y.σA (actXi c) :=
  Y.conj_σA_of wXi_mem_Wsub conj_cS_wXi c

theorem conj_ξ2 (c : SC) :
    (Y.ξ * Y.ξ) * Y.σA c * (Y.ξ * Y.ξ)⁻¹ = Y.σA (actXi (actXi c)) := by
  rw [show (Y.ξ * Y.ξ) * Y.σA c * (Y.ξ * Y.ξ)⁻¹ = Y.ξ * (Y.ξ * Y.σA c * Y.ξ⁻¹) * Y.ξ⁻¹ by group,
    Y.conj_ξ, Y.conj_ξ]

theorem conjSet_XN_pi3 :
    conjSet Y.XN Y.π3 = {Y.σA (sc [0]), Y.σA (sc [1]), Y.σA (sc [2])} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Y.conj_pi3_mem hx
  · rintro (rfl | rfl | rfl)
    · exact ⟨Y.ξ, Y.ξ_mem_XN, by rw [← Y.σA_pi3, Y.conj_ξ, actXi_sc.1]⟩
    · exact ⟨Y.ξ * Y.ξ, Y.XN.mul_mem Y.ξ_mem_XN Y.ξ_mem_XN,
        by rw [← Y.σA_pi3, Y.conj_ξ2, actXi_sc.1, actXi_sc.2.1]⟩
    · rw [Y.σA_pi3]
      exact self_mem_conjSet _ _

theorem ncard_conjSet_XN_pi3 : (conjSet Y.XN Y.π3).ncard = 3 := by
  rw [Y.conjSet_XN_pi3]
  obtain ⟨h01, h02, h12, -⟩ := sc_ne
  exact Set.ncard_eq_three.mpr ⟨_, _, _, fun h => h01 (Y.σA_injective h),
    fun h => h02 (Y.σA_injective h), fun h => h12 (Y.σA_injective h), rfl⟩

theorem three_le_ncard_conjSet_pi12 {H : Subgroup G} (hH : Y.XN ≤ H) :
    3 ≤ (conjSet H Y.π12).ncard := by
  have hsub : ({Y.σA (sc [0, 1]), Y.σA (sc [1, 2]), Y.σA (sc [0, 2])} : Set G) ⊆
      conjSet H Y.π12 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [Y.σA_pi12]
      exact self_mem_conjSet _ _
    · exact ⟨Y.ξ, hH Y.ξ_mem_XN, by rw [← Y.σA_pi12, Y.conj_ξ, actXi_sc.2.2.1]⟩
    · exact ⟨Y.ξ * Y.ξ, hH (Y.XN.mul_mem Y.ξ_mem_XN Y.ξ_mem_XN),
        by rw [← Y.σA_pi12, Y.conj_ξ2, actXi_sc.2.2.1, actXi_sc.2.2.2]⟩
  obtain ⟨-, -, -, h1, h2, h3⟩ := sc_ne
  have hcard : ({Y.σA (sc [0, 1]), Y.σA (sc [1, 2]), Y.σA (sc [0, 2])} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, fun h => h2 (Y.σA_injective h),
      fun h => h1 (Y.σA_injective h), fun h => h3 (Y.σA_injective h).symm, rfl⟩
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (conjSet_finite _ _)

theorem ncard_conj_pi3_of_le
    (hC3 : Subgroup.centralizer ({Y.π3} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) :
    (conjSet Y.NA Y.π3).ncard = 3 * (conjSet Y.NA z).ncard := by
  have e1 := ncard_conjSet_mul Y.NA z
  have e2 := ncard_conjSet_mul Y.NA Y.π3
  have e3 := ncard_conjSet_mul Y.XN Y.π3
  rw [Y.ncard_conjSet_XN_pi3] at e3
  have hsub : Y.NA ⊓ Subgroup.centralizer {Y.π3} = Y.XN ⊓ Subgroup.centralizer {Y.π3} := by
    rw [inf_assoc, inf_eq_right.mpr hC3]
  rw [hsub] at e2
  have hpos : 0 < Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π3} : Subgroup G) := Nat.card_pos
  rw [← e3] at e1
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [e2, ← e1]
  ring

theorem π3_mem_A : Y.π3 ∈ Y.A := Y.σA_pi3 ▸ Y.σA_mem_A _

theorem π12_mem_A : Y.π12 ∈ Y.A := Y.σA_pi12 ▸ Y.σA_mem_A _

theorem zero_not_mem_coord_conj {x : G} (hx : x ≠ 1) {H : Subgroup G} :
    (0 : SC) ∉ Y.coord (conjSet H x) := by
  rw [Y.mem_coord, Y.σA_zero]
  intro h
  exact hx (isConj_one_left.mp (isConj_of_mem_conjSet h))

theorem disjoint_coord_conj {x y : G} (hxy : ¬ IsConj x y) {H : Subgroup G} :
    Disjoint (Y.coord (conjSet H x)) (Y.coord (conjSet H y)) := by
  rw [Finset.disjoint_left]
  intro c hcx hcy
  exact hxy ((isConj_of_mem_conjSet (Y.mem_coord.mp hcx)).trans
    (isConj_of_mem_conjSet (Y.mem_coord.mp hcy)).symm)

@[expose] noncomputable def coordOf (a : G) : SC := Classical.epsilon fun c => Y.σA c = a

theorem σA_coordOf {a : G} (h : a ∈ Y.A) : Y.σA (Y.coordOf a) = a :=
  Classical.epsilon_spec (Y.exists_σA h)

theorem coordOf_σA (c : SC) : Y.coordOf (Y.σA c) = c :=
  Y.σA_injective (Y.σA_coordOf (Y.σA_mem_A c))

@[expose] noncomputable def cc (g : G) (c : SC) : SC := Y.coordOf (g * Y.σA c * g⁻¹)

theorem conj_mem_A {g : G} (hg : g ∈ Y.NA) {a : G} (ha : a ∈ Y.A) : g * a * g⁻¹ ∈ Y.A :=
  (Subgroup.mem_normalizer_iff.mp hg a).mp ha

theorem σA_cc {g : G} (hg : g ∈ Y.NA) (c : SC) : Y.σA (Y.cc g c) = g * Y.σA c * g⁻¹ :=
  Y.σA_coordOf (Y.conj_mem_A hg (Y.σA_mem_A c))

theorem cc_add {g : G} (hg : g ∈ Y.NA) (c c' : SC) : Y.cc g (c + c') = Y.cc g c + Y.cc g c' := by
  apply Y.σA_injective
  rw [Y.σA_add, Y.σA_cc hg, Y.σA_cc hg, Y.σA_cc hg, Y.σA_add]
  group

theorem cc_mul {g h : G} (hg : g ∈ Y.NA) (hh : h ∈ Y.NA) (c : SC) :
    Y.cc (g * h) c = Y.cc g (Y.cc h c) := by
  apply Y.σA_injective
  rw [Y.σA_cc (Y.NA.mul_mem hg hh), Y.σA_cc hg, Y.σA_cc hh]
  group

theorem cc_one (c : SC) : Y.cc 1 c = c := by
  apply Y.σA_injective
  rw [Y.σA_cc Y.NA.one_mem]
  group

theorem cc_zero {g : G} (hg : g ∈ Y.NA) : Y.cc g 0 = 0 := by
  apply Y.σA_injective
  rw [Y.σA_cc hg, Y.σA_zero]
  group

theorem not_dvd_card_NA {p : ℕ} (hp : p = 11 ∨ p = 13) : ¬ p ∣ Nat.card Y.NA := by
  classical
  intro hdvd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hg : (x : G) ∈ Y.NA := x.2
  have hgo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  let f : Function.End SC := Y.cc x
  have hpow : ∀ k : ℕ, f ^ k = Y.cc ((x : G) ^ k) := by
    intro k
    induction k with
    | zero =>
      funext c
      simp only [pow_zero]
      exact (Y.cc_one c).symm
    | succ k ih =>
      rw [pow_succ, ih]
      funext c
      show Y.cc ((x : G) ^ k) (Y.cc x c) = Y.cc ((x : G) ^ (k + 1)) c
      rw [pow_succ, Y.cc_mul (Y.NA.pow_mem hg k) hg]
  have hfp : f ^ p ^ 1 = 1 := by
    rw [pow_one, hpow, ← hgo, pow_orderOf_eq_one]
    funext c
    exact Y.cc_one c
  have hmod := Equiv.Perm.card_fixedPoints_modEq hfp
  let Fix : AddSubgroup SC :=
    { carrier := {c | Y.cc x c = c}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Y.cc_add hg, ha, hb]
      zero_mem' := Y.cc_zero hg
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [neg_SC, ha] }
  have hcardFix : Fintype.card (Function.fixedPoints f) = Nat.card Fix := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcardFix, ← Nat.card_eq_fintype_card, card_SC] at hmod
  have hdvd64 : Nat.card Fix ∣ 64 := card_SC ▸ AddSubgroup.card_addSubgroup_dvd_card Fix
  have hle : Nat.card Fix ≤ 64 := Nat.le_of_dvd (by norm_num) hdvd64
  have h64 : Nat.card Fix = 64 := by
    unfold Nat.ModEq at hmod
    rcases hp with rfl | rfl <;> interval_cases h : Nat.card Fix <;> omega
  have htop : Fix = ⊤ := Fix.eq_top_of_card_eq (h64.trans card_SC.symm)
  have hxA : (x : G) ∈ Y.A := by
    apply Y.centralizer_A_le
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨c, rfl⟩ := Y.exists_σA ha
    have hc : Y.cc x c = c := by
      have : c ∈ Fix := htop ▸ AddSubgroup.mem_top c
      exact this
    have h1 := Y.σA_cc hg c
    rw [hc] at h1
    calc Y.σA c * (x : G) = ((x : G) * Y.σA c * (x : G)⁻¹) * x := by rw [← h1]
      _ = (x : G) * Y.σA c := by group
  have hdvd' : p ∣ 64 := by
    rw [← hgo, ← Y.card_A]
    exact Subgroup.orderOf_dvd_natCard _ hxA
  rcases hp with rfl | rfl <;> norm_num at hdvd'

theorem coord_conj_z (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12)
    (h312 : ¬ IsConj Y.π3 Y.π12) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hiso : ∃ a ∈ Y.A, a ≠ z ∧ IsConj z a) :
    Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 2 ∨
      Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6 := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  obtain ⟨Fz, hFz⟩ : ∃ F, F = Y.coord (conjSet Y.NA z) := ⟨_, rfl⟩
  rw [← hFz]
  have hcz : Fz.card = (conjSet Y.NA z).ncard :=
    hFz ▸ Y.card_coord (conjSet_normalizer_subset Y.z_mem_A)
  have hc3 : (Y.coord (conjSet Y.NA Y.π3)).card = (conjSet Y.NA Y.π3).ncard :=
    Y.card_coord (conjSet_normalizer_subset Y.π3_mem_A)
  have hc12 : (Y.coord (conjSet Y.NA Y.π12)).card = (conjSet Y.NA Y.π12).ncard :=
    Y.card_coord (conjSet_normalizer_subset Y.π12_mem_A)
  have h3n := Y.ncard_conj_pi3_of_le (Y.centralizer_pi3_le hchar P hP hz h3 h12)
  have h12n := Y.three_le_ncard_conjSet_pi12 (H := Y.NA) inf_le_left
  have hbound := card_le_63 (Y.zero_not_mem_coord_conj hz1 (H := Y.NA))
    (Y.zero_not_mem_coord_conj Y.π3_ne_one (H := Y.NA))
    (Y.zero_not_mem_coord_conj Y.π12_ne_one (H := Y.NA)) (Y.disjoint_coord_conj h3)
    (Y.disjoint_coord_conj h12) (Y.disjoint_coord_conj h312)
  rw [hc3, hc12, h3n, ← hFz, hcz] at hbound
  have hn15 : Fz.card ≤ 15 := by omega
  have hn2 : 2 ≤ Fz.card := by
    obtain ⟨a, ha, haz, hza⟩ := hiso
    obtain ⟨g, hg⟩ := isConj_iff.mp hza
    obtain ⟨m, hm, hma⟩ := Y.exists_normalizer_conj P hP hE Y.z_mem_A ha hg
    rw [hcz]
    have hsub : ({z, a} : Set G) ⊆ conjSet Y.NA z := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact self_mem_conjSet _ _
      · exact ⟨m, hm, hma⟩
    calc 2 = ({z, a} : Set G).ncard := (Set.ncard_pair (Ne.symm haz)).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (conjSet_finite _ _)
  have hcl : IsClosedSC ↑Fz := hFz ▸ Y.coord_closed fun x hx n hn => conj_mem_conjSet hx hn
  have h0 : (0 : SC) ∉ Fz := hFz ▸ Y.zero_not_mem_coord_conj hz1
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin 10), I = Finset.univ.filter fun i => scOrb i ⊆ Fz :=
    ⟨_, rfl⟩
  have hsum : Fz.card = ∑ i ∈ I, orbSize i := by
    rw [card_eq_sum_of_closed hcl h0, hI]
    exact Finset.sum_congr rfl fun i _ => card_scOrb i
  have hFI : Fz = I.biUnion scOrb := hI ▸ eq_biUnion_of_closed hcl h0
  obtain ⟨m012, m2, m01, m2345⟩ := mem_scOrb_facts
  have hzF : sc [0, 1, 2] ∈ Fz := hFz ▸ Y.mem_coord.mpr (by
    rw [sc012_eq, Y.σA_one_zero]
    exact self_mem_conjSet _ _)
  have hmemFz : ∀ {c : SC}, c ∈ Fz ↔ Y.σA c ∈ conjSet Y.NA z := fun {c} => hFz ▸ Y.mem_coord
  have hmemI : ∀ {i : Fin 10} {c : SC}, c ∈ scOrb i → c ∈ Fz → i ∈ I := fun hci hcF => by
    rw [hI]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.coe_subset.mp
      (scOrb_subset_of_closed hcl hci hcF)⟩
  have hsubI : ∀ {i : Fin 10}, i ∈ I → scOrb i ⊆ Fz := fun {i} hi => by
    rw [hI] at hi
    exact (Finset.mem_filter.mp hi).2
  have hI0 : (0 : Fin 10) ∈ I := hmemI m012 hzF
  have hI1 : (1 : Fin 10) ∉ I := by
    intro h
    have := hmemFz.mp (hsubI h m2)
    rw [Y.σA_pi3] at this
    exact h3 (isConj_of_mem_conjSet this)
  have hI3 : (3 : Fin 10) ∉ I := by
    intro h
    have := hmemFz.mp (hsubI h m01)
    rw [Y.σA_pi12] at this
    exact h12 (isConj_of_mem_conjSet this)
  have hcardNA : (conjSet Y.NA z).ncard ∣ Nat.card Y.NA :=
    ⟨_, (ncard_conjSet_mul Y.NA z).symm⟩
  rcases orbit_cases I hI0 hI1 hI3 (by rw [← hsum]; exact hn2) (by rw [← hsum]; exact hn15) with
    h | h | h | h | ⟨hsub, h5, h89⟩ | ⟨h15, h8⟩
  · left
    rw [hFI, h, Finset.biUnion_insert, Finset.singleton_biUnion]
  · right
    rw [hFI, h, Finset.biUnion_insert, Finset.singleton_biUnion]
  · exfalso
    rw [← hsum, hcz] at h
    exact Y.not_dvd_card_NA (Or.inl rfl) (h ▸ hcardNA)
  · exfalso
    rw [← hsum, hcz] at h
    exact Y.not_dvd_card_NA (Or.inr rfl) (h ▸ hcardNA)
  ·
    exfalso
    have hFU : Fz ⊆ U4 := by
      rw [hFI]
      intro c hc
      obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp hc
      have hi' := hsub hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
      obtain ⟨u0, u8, u9⟩ := scOrb_sub_U4
      rcases hi' with rfl | rfl | rfl
      exacts [u0 hci, u8 hci, u9 hci]
    obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, sc [2] = sc [0, 1, 2] + a + b ∧ a ∈ Fz ∧ b ∈ Fz := by
      obtain ⟨d8, a8, b8, d9, a9, b9⟩ := sc2_decomp
      rcases h89 with h8 | h9
      · exact ⟨_, _, d8, hsubI h8 a8, hsubI h8 b8⟩
      · exact ⟨_, _, d9, hsubI h9 a9, hsubI h9 b9⟩
    have hπ : Y.π3 = Y.σA (sc [0, 1, 2]) * Y.σA a * Y.σA b := by
      rw [← Y.σA_add, ← Y.σA_add, ← hab, Y.σA_pi3]
    have hF3U : Y.coord (conjSet Y.NA Y.π3) ⊆ U4 := by
      intro c hc
      obtain ⟨m, hm, hmc⟩ := Y.mem_coord.mp hc
      have hconj : ∀ e ∈ Fz, ∃ e' ∈ Fz, m * Y.σA e * m⁻¹ = Y.σA e' := by
        intro e he
        have h1 : m * Y.σA e * m⁻¹ ∈ conjSet Y.NA z := conj_mem_conjSet (hmemFz.mp he) hm
        obtain ⟨e', he'⟩ := Y.exists_σA (conjSet_normalizer_subset Y.z_mem_A h1)
        exact ⟨e', hmemFz.mpr (he' ▸ h1), he'.symm⟩
      obtain ⟨e1, he1, h1⟩ := hconj _ hzF
      obtain ⟨e2, he2, h2⟩ := hconj _ ha
      obtain ⟨e3, he3, h3'⟩ := hconj _ hb
      have hce : Y.σA c = Y.σA (e1 + e2 + e3) := by
        rw [Y.σA_add, Y.σA_add, ← h1, ← h2, ← h3', ← hmc, hπ]
        group
      rw [Y.σA_injective hce]
      exact U4_add _ (U4_add _ (hFU he1) _ (hFU he2)) _ (hFU he3)
    have hsub' : Fz ∪ Y.coord (conjSet Y.NA Y.π3) ⊆ U4.erase 0 := by
      intro c hc
      rw [Finset.mem_erase]
      rcases Finset.mem_union.mp hc with hc | hc
      · exact ⟨fun h => h0 (h ▸ hc), hFU hc⟩
      · exact ⟨fun h => Y.zero_not_mem_coord_conj Y.π3_ne_one (h ▸ hc), hF3U hc⟩
    have hc := Finset.card_le_card hsub'
    rw [Finset.card_union_of_disjoint (hFz ▸ Y.disjoint_coord_conj h3),
      Finset.card_erase_of_mem zero_mem_U4, U4_card, hc3, h3n, ← hcz] at hc
    rw [← hsum] at h5
    omega
  ·
    exfalso
    have hn : Fz.card = 15 := hsum.trans h15
    have h12eq : (conjSet Y.NA Y.π12).ncard = 3 := by omega
    set N12 := Y.NA ⊓ Subgroup.centralizer ({Y.π12} : Set G) with hN12
    have e1 := ncard_conjSet_mul Y.NA z
    have e4 := ncard_conjSet_mul Y.NA Y.π12
    have e5 := ncard_conjSet_mul Y.XN Y.π12
    have e6 := ncard_conjSet_mul N12 z
    have hX12 : N12 ⊓ Subgroup.centralizer {z} = Y.XN ⊓ Subgroup.centralizer {Y.π12} :=
      inf_right_comm _ _ _
    rw [hX12] at e6
    have h5 := Y.three_le_ncard_conjSet_pi12 (H := Y.XN) le_rfl
    have hk : 0 < Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π12} : Subgroup G) := Nat.card_pos
    rw [← hcz, hn] at e1
    rw [h12eq] at e4
    have e1' : 15 * Nat.card Y.XN = Nat.card Y.NA := e1
    have e4' : 3 * Nat.card N12 = Nat.card Y.NA := e4
    have hge : 15 ≤ (conjSet N12 z).ncard := by
      have hA : 3 * ((conjSet N12 z).ncard *
          Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π12} : Subgroup G)) =
          15 * ((conjSet Y.XN Y.π12).ncard *
            Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π12} : Subgroup G)) := by
        rw [e6, e5]
        omega
      have hB : 15 * Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π12} : Subgroup G) ≤
          (conjSet N12 z).ncard * Nat.card (Y.XN ⊓ Subgroup.centralizer {Y.π12} : Subgroup G) := by
        nlinarith
      exact Nat.le_of_mul_le_mul_right hB hk
    have heq : conjSet N12 z = conjSet Y.NA z :=
      Set.eq_of_subset_of_ncard_le (conjSet_mono inf_le_left z) (by rw [← hcz, hn]; exact hge)
        (conjSet_finite _ _)
    have hmem : Y.σA (sc [2, 3, 4, 5]) ∈ conjSet N12 z := by
      rw [heq]
      exact hmemFz.mp (hsubI h8 m2345)
    obtain ⟨g, hg, hgz⟩ := hmem
    obtain ⟨hx, hperm⟩ := Y.conj_z_perm hchar P hP hz (Or.inr rfl) hg.2
    have hx' : (⟨g * z * g⁻¹, hx⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨Y.σA (sc [2, 3, 4, 5]), Y.σA_mem_C _⟩ := Subtype.ext hgz
    rw [hx', Y.ϑ_σA] at hperm
    obtain ⟨p1, p2⟩ := perm_cSp_2345
    rcases hperm with h | h
    exacts [p1 h, p2 h]

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A11Group
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.RankThree.PartTwo.Sec4.Ronan148R (a11A0 a11c1 a11c2 a11c3 a11i1 a11s12 a11s13)

theorem vecPerm_mem_alternatingGroup_eleven (v : Fin 3 → ZMod 3) :
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.vecPerm 11 v ∈ alternatingGroup (Fin 11) := by
  show (a11c1 : Equiv.Perm (Fin 11)) ^ (v 0).val * (a11c2 : Equiv.Perm (Fin 11)) ^ (v 1).val *
      (a11c3 : Equiv.Perm (Fin 11)) ^ (v 2).val ∈ alternatingGroup (Fin 11)
  exact (alternatingGroup (Fin 11)).mul_mem ((alternatingGroup (Fin 11)).mul_mem
    ((alternatingGroup (Fin 11)).pow_mem a11c1.2 _) ((alternatingGroup (Fin 11)).pow_mem a11c2.2 _))
    ((alternatingGroup (Fin 11)).pow_mem a11c3.2 _)

@[expose] def a11Coords : Multiplicative (Fin 3 → ZMod 3) →* alternatingGroup (Fin 11) :=
  (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.vecHom
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.wFacts_eleven.toA0Facts).codRestrict
    (alternatingGroup (Fin 11))
    (fun v => vecPerm_mem_alternatingGroup_eleven (Multiplicative.toAdd v))

theorem a11Coords_apply (v : Fin 3 → ZMod 3) :
    a11Coords (Multiplicative.ofAdd v) =
      a11c1 ^ (v 0).val * a11c2 ^ (v 1).val * a11c3 ^ (v 2).val :=
  Subtype.ext rfl

private def a11c : Fin 3 → alternatingGroup (Fin 11) := ![a11c1, a11c2, a11c3]

private theorem a11c_pow_three (j : Fin 3) : a11c j ^ 3 = 1 := by
  fin_cases j <;> decide

private theorem a11c_ne_one (j : Fin 3) : a11c j ≠ 1 := by
  fin_cases j <;> decide

private theorem a11c_commute (i j : Fin 3) : Commute (a11c i) (a11c j) := by
  rw [commute_iff_eq]
  fin_cases i <;> fin_cases j <;> decide

private theorem a11c_support (j : Fin 3) :
    ((a11c j : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3 := by
  fin_cases j <;> decide +kernel

private theorem a11c_mem_a11A0 (j : Fin 3) : a11c j ∈ a11A0 := by
  fin_cases j
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a11c1))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a11c2))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a11c3)

private theorem a11Coords_single (j : Fin 3) (δ : ZMod 3) :
    a11Coords (Multiplicative.ofAdd (fun i => if i = j then δ else 0)) = a11c j ^ δ.val := by
  rw [a11Coords_apply]
  fin_cases j <;> simp [a11c]

private theorem card_support_eq_three_iff_a11Coords (u : Fin 3 → ZMod 3) :
    (((a11Coords (Multiplicative.ofAdd u) : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)).support.card = 3) ↔
      ∃ j : Fin 3, ∃ δ : ZMod 3, δ ≠ 0 ∧ u = fun i => if i = j then δ else 0 := by
  decide +kernel +revert

private theorem a11c_pow_ne (j j' : Fin 3) (m : Fin 3) (h : j ≠ j') :
    a11c j' ≠ a11c j ^ (m : ℕ) := by
  revert j j' m
  decide +kernel

private theorem conj_a11Coords (n : alternatingGroup (Fin 11)) (v : Fin 3 → ZMod 3) :
    n * a11Coords (Multiplicative.ofAdd v) * n⁻¹ =
      (n * a11c 0 * n⁻¹) ^ (v 0).val * (n * a11c 1 * n⁻¹) ^ (v 1).val *
        (n * a11c 2 * n⁻¹) ^ (v 2).val := by
  rw [a11Coords_apply]
  conv_lhs => rw [← MulAut.conj_apply n]
  rw [map_mul, map_mul, map_pow, map_pow, map_pow]
  simp only [MulAut.conj_apply, a11c]
  rfl

private theorem prod_ofFn_three (f : Fin 3 → alternatingGroup (Fin 11)) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 := by
  simp [List.ofFn_succ, mul_assoc]

private lemma action_a11Coords (n : alternatingGroup (Fin 11)) (kf : Fin 3 → Fin 3)
    (hk : Function.Injective kf) (δ : Fin 3 → ZMod 3) (v : Fin 3 → ZMod 3)
    (hconj : ∀ j, n * a11c j * n⁻¹ = a11c (kf j) ^ (δ j).val) :
    n * a11Coords (Multiplicative.ofAdd v) * n⁻¹ =
      a11Coords (Multiplicative.ofAdd fun i =>
        δ ((Equiv.ofBijective kf hk.bijective_of_finite).symm i) *
          v ((Equiv.ofBijective kf hk.bijective_of_finite).symm i)) := by
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective kf hk.bijective_of_finite
  let B : Fin 3 → ℕ := fun i => (δ (e.symm i) * v (e.symm i)).val
  let f : Fin 3 → alternatingGroup (Fin 11) := fun i => a11c i ^ B i
  let g : Fin 3 → alternatingGroup (Fin 11) :=
    fun j => a11c (kf j) ^ ((δ j).val * (v j).val)
  have hL : n * a11Coords (Multiplicative.ofAdd v) * n⁻¹ = (List.ofFn g).prod := by
    rw [conj_a11Coords]
    rw [hconj 0, hconj 1, hconj 2]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    exact (prod_ofFn_three g).symm
  have hR : a11Coords (Multiplicative.ofAdd fun i => δ (e.symm i) * v (e.symm i)) =
      (List.ofFn f).prod := by
    rw [a11Coords_apply]
    exact (prod_ofFn_three f).symm
  rw [hL, hR]
  have hg : g = f ∘ e := by
    funext j
    simp only [g, f, B, Function.comp_apply]
    have hej : e j = kf j := Equiv.ofBijective_apply kf hk.bijective_of_finite j
    have hσ : e.symm (kf j) = j := by
      rw [← hej]
      exact Equiv.symm_apply_apply e j
    rw [hej, hσ, ZMod.val_mul]
    exact pow_eq_pow_mod ((δ j).val * (v j).val) (a11c_pow_three (kf j))
  have hprod : (List.ofFn (f ∘ e)).prod = (List.ofFn f).prod := by
    apply List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm e f)
    rw [List.pairwise_ofFn]
    intro i j _
    exact (a11c_commute (e i) (e j)).pow_pow _ _
  rw [hg]
  exact hprod

private def a11i2 : alternatingGroup (Fin 11) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 9 10, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def a11i3 : alternatingGroup (Fin 11) :=
  ⟨Equiv.swap 6 7 * Equiv.swap 9 10, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def a11i : Fin 3 → alternatingGroup (Fin 11) := ![a11i1, a11i2, a11i3]

private def signBit (x : ZMod 3) : ℕ := if x = 1 then 0 else 1

private def signRep (ε : Fin 3 → ZMod 3) : alternatingGroup (Fin 11) :=
  a11i 0 ^ signBit (ε 0) * a11i 1 ^ signBit (ε 1) * a11i 2 ^ signBit (ε 2)

private theorem signRep_spec (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) (j : Fin 3) :
    signRep ε * a11c j * (signRep ε)⁻¹ = a11c j ^ (ε j).val := by
  revert ε j
  decide +kernel

private def permRep (σ : Equiv.Perm (Fin 3)) : alternatingGroup (Fin 11) :=
  if σ = 1 then 1
  else if σ = Equiv.swap (0 : Fin 3) 1 then a11s12
  else if σ = Equiv.swap (0 : Fin 3) 2 then a11s13
  else if σ = Equiv.swap (1 : Fin 3) 2 then a11s12 * a11s13 * a11s12
  else if σ = Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2 then a11s13 * a11s12
  else a11s12 * a11s13

private theorem permRep_spec (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    permRep σ * a11c j * (permRep σ)⁻¹ = a11c (σ.symm j) := by
  revert σ j
  decide +kernel

private theorem a11Coords_range : a11Coords.range = a11A0 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rw [show u = Multiplicative.ofAdd (Multiplicative.toAdd u) from rfl, a11Coords_apply]
    exact mul_mem (mul_mem (pow_mem (a11c_mem_a11A0 0) _) (pow_mem (a11c_mem_a11A0 1) _))
      (pow_mem (a11c_mem_a11A0 2) _)
  · intro hx
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ :=
      CFSG.RankThree.PartTwo.Sec4.Ronan148R.mem_a11A0 hx
    refine ⟨Multiplicative.ofAdd ![i, j, k], ?_⟩
    rw [a11Coords_apply]
    simp [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hk]

private lemma injective_of_conj_action (n : alternatingGroup (Fin 11)) (kf : Fin 3 → Fin 3)
    (δ : Fin 3 → ZMod 3)
    (hconj : ∀ j, n * a11c j * n⁻¹ = a11c (kf j) ^ (δ j).val) :
    Function.Injective kf := by
  intro j j' hjj
  by_contra hne
  set k := kf j with hk
  have hmem : ∀ (t : Fin 3), kf t = k → a11c t ∈ Subgroup.zpowers (n⁻¹ * a11c k * n) := by
    intro t ht
    have hz : a11c t = (n⁻¹ * a11c k * n) ^ (δ t).val := by
      calc a11c t = n⁻¹ * (n * a11c t * n⁻¹) * n := by group
        _ = n⁻¹ * a11c (kf t) ^ (δ t).val * n := by rw [hconj t]
        _ = n⁻¹ * a11c k ^ (δ t).val * n := by rw [ht]
        _ = (n⁻¹ * a11c k * n) ^ (δ t).val := by
              simpa only [MulAut.conj_apply, inv_inv] using
                (map_pow (MulAut.conj n⁻¹) (a11c k) (δ t).val)
    exact Subgroup.mem_zpowers_iff.mpr ⟨(δ t).val, hz.symm⟩
  have hmemj : a11c j ∈ Subgroup.zpowers (n⁻¹ * a11c k * n) := hmem j rfl
  have hmemj' : a11c j' ∈ Subgroup.zpowers (n⁻¹ * a11c k * n) :=
    hmem j' (by rw [hjj])
  have hz_eq : Subgroup.zpowers (n⁻¹ * a11c k * n) =
      (Subgroup.zpowers (a11c k)).map (MulAut.conj n⁻¹).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hcardz : Nat.card (Subgroup.zpowers (n⁻¹ * a11c k * n)) = 3 := by
    rw [hz_eq, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective,
      Nat.card_zpowers, orderOf_eq_prime (a11c_pow_three k) (a11c_ne_one k)]
  have hcardt : ∀ t : Fin 3, Nat.card (Subgroup.zpowers (a11c t)) = 3 := by
    intro t
    rw [Nat.card_zpowers, orderOf_eq_prime (a11c_pow_three t) (a11c_ne_one t)]
  have heq : Subgroup.zpowers (a11c j) = Subgroup.zpowers (n⁻¹ * a11c k * n) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmemj)
      (by rw [hcardz, hcardt j])
  have heq' : Subgroup.zpowers (a11c j') = Subgroup.zpowers (n⁻¹ * a11c k * n) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmemj')
      (by rw [hcardz, hcardt j'])
  have hmemz : a11c j' ∈ Subgroup.zpowers (a11c j) := by
    rw [heq, ← heq']
    exact Subgroup.mem_zpowers _
  obtain ⟨m, hm3, hm⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148R.exists_pow_of_mem_zpowers
      (a11c_pow_three j) hmemz
  exact a11c_pow_ne j j' ⟨m, hm3⟩ hne hm

private lemma exists_normalizer_action (n : alternatingGroup (Fin 11))
    (hn : n ∈ Subgroup.normalizer (a11A0 : Set (alternatingGroup (Fin 11)))) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ v, n * a11Coords v * n⁻¹ =
        a11Coords (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  have hconjA : ∀ j, n * a11c j * n⁻¹ ∈ a11A0 := fun j =>
    (Subgroup.mem_normalizer_iff.mp hn (a11c j)).mp (a11c_mem_a11A0 j)
  have hex : ∀ j, ∃ u, a11Coords u = n * a11c j * n⁻¹ := by
    intro j
    have h : n * a11c j * n⁻¹ ∈ a11Coords.range := by
      rw [a11Coords_range]
      exact hconjA j
    exact MonoidHom.mem_range.mp h
  choose u hu using hex
  have hu' : ∀ j, a11Coords (Multiplicative.ofAdd (Multiplicative.toAdd (u j))) =
      n * a11c j * n⁻¹ := fun j => by
    simpa using hu j
  have hsupport : ∀ j, (((a11Coords (Multiplicative.ofAdd (Multiplicative.toAdd (u j))) :
      alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card) = 3 := by
    intro j
    rw [hu' j]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Equiv.Perm.card_support_conj]
    exact a11c_support j
  choose kj δj hδj hwj using fun j =>
    (card_support_eq_three_iff_a11Coords (Multiplicative.toAdd (u j))).mp (hsupport j)
  have hconj : ∀ j, n * a11c j * n⁻¹ = a11c (kj j) ^ (δj j).val := by
    intro j
    rw [← hu' j, hwj j, a11Coords_single]
  have hk_inj : Function.Injective kj := injective_of_conj_action n kj δj hconj
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective kj hk_inj.bijective_of_finite
  refine ⟨e.symm, fun i => δj (e.symm i), fun i => hδj (e.symm i), ?_⟩
  intro v
  simpa using action_a11Coords n kj hk_inj δj (Multiplicative.toAdd v) hconj

private lemma exists_realizer (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n : alternatingGroup (Fin 11), ∀ v, n * a11Coords v * n⁻¹ =
      a11Coords (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  let δ : Fin 3 → ZMod 3 := fun j => ε (σ.symm j)
  refine ⟨signRep ε * permRep σ, fun v => ?_⟩
  have hconj : ∀ j, (signRep ε * permRep σ) * a11c j * (signRep ε * permRep σ)⁻¹ =
      a11c (σ.symm j) ^ (δ j).val := by
    intro j
    calc (signRep ε * permRep σ) * a11c j * (signRep ε * permRep σ)⁻¹
        = signRep ε * (permRep σ * a11c j * (permRep σ)⁻¹) * (signRep ε)⁻¹ := by group
      _ = signRep ε * a11c (σ.symm j) * (signRep ε)⁻¹ := by rw [permRep_spec]
      _ = a11c (σ.symm j) ^ (δ j).val := by
            rw [signRep_spec ε hε]
  have hmain := action_a11Coords (signRep ε * permRep σ) σ.symm σ.symm.injective δ
    (Multiplicative.toAdd v) hconj
  have hes : (Equiv.ofBijective σ.symm σ.symm.injective.bijective_of_finite).symm = σ := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
    exact (Equiv.symm_apply_apply σ i).symm
  simpa [δ, hes] using hmain

theorem isSignedCoords_a11Coords : Theorem82.IsSignedCoords a11A0 a11Coords := by
  have hf := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.wFacts_eleven.toA0Facts
  exact ⟨fun u v huv =>
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.vecHom_injective hf
        (congrArg Subtype.val huv),
    a11Coords_range, exists_normalizer_action, exists_realizer⟩

private def a11d5 : Fin 3 → alternatingGroup (Fin 11) :=
  ![⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 9 * Equiv.swap 9 10,
      by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 9 * Equiv.swap 9 10,
      by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 6 7 * Equiv.swap 7 8 * Equiv.swap 8 9 * Equiv.swap 9 10,
      by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩]

private theorem d5_pow_five (j : Fin 3) : a11d5 j ^ 5 = 1 := by
  fin_cases j <;> decide

private theorem d5_ne_one (j : Fin 3) : a11d5 j ≠ 1 := by
  fin_cases j <;> decide

private theorem d5_order (j : Fin 3) : orderOf (a11d5 j) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (d5_pow_five j) (d5_ne_one j)

private theorem d5_commute_coords (j : Fin 3) (v : Fin 3 → ZMod 3) (hj : v j = 0) :
    Commute (a11d5 j) (a11Coords (Multiplicative.ofAdd v)) := by
  rw [commute_iff_eq]
  revert j v
  decide +kernel

private theorem a11c_isThreeCycle (i : Fin 3) :
    ((a11c i : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).IsThreeCycle := by
  fin_cases i
  · change (Equiv.swap (0 : Fin 11) 1 * Equiv.swap 1 2).IsThreeCycle
    rw [Equiv.swap_comm (0 : Fin 11) 1]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · change (Equiv.swap (3 : Fin 11) 4 * Equiv.swap 4 5).IsThreeCycle
    rw [Equiv.swap_comm (3 : Fin 11) 4]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · change (Equiv.swap (6 : Fin 11) 7 * Equiv.swap 7 8).IsThreeCycle
    rw [Equiv.swap_comm (6 : Fin 11) 7]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem exists_mem_support_a11c (p : Fin 11) (hp : p.val < 9) :
    ∃ i : Fin 3, ((a11c i : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) p ≠ p := by
  revert p
  decide +kernel

private lemma sq_eq_one_of_fixes_lt_nine {y : Equiv.Perm (Fin 11)}
    (h : ∀ p : Fin 11, p.val < 9 → y p = p) : y ^ 2 = 1 := by
  have h9 : y 9 = 9 ∨ y 9 = 10 := by
    by_contra hc
    simp only [not_or] at hc
    have hv9 : (y 9).val ≠ 9 := fun hv => hc.1 (Fin.ext hv)
    have hv10 : (y 9).val ≠ 10 := fun hv => hc.2 (Fin.ext hv)
    have hlt : (y 9).val < 9 := by
      have := (y 9).isLt
      omega
    have hpp : y (y 9) = y 9 := h (y 9) hlt
    exact hc.1 (y.injective hpp)
  have h10 : y 10 = 9 ∨ y 10 = 10 := by
    by_contra hc
    simp only [not_or] at hc
    have hv9 : (y 10).val ≠ 9 := fun hv => hc.1 (Fin.ext hv)
    have hv10 : (y 10).val ≠ 10 := fun hv => hc.2 (Fin.ext hv)
    have hlt : (y 10).val < 9 := by
      have := (y 10).isLt
      omega
    have hpp : y (y 10) = y 10 := h (y 10) hlt
    exact hc.2 (y.injective hpp)
  ext p
  fin_cases p
  · simp [pow_two, Equiv.Perm.mul_apply, h 0 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 1 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 2 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 3 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 4 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 5 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 6 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 7 (by norm_num)]
  · simp [pow_two, Equiv.Perm.mul_apply, h 8 (by norm_num)]
  · rcases h9 with h9 | h9
    · simp [pow_two, Equiv.Perm.mul_apply, h9]
    · rcases h10 with h10 | h10
      · simp [pow_two, Equiv.Perm.mul_apply, h9, h10]
      · exfalso
        exact absurd (y.injective (h9.trans h10.symm)) (by decide)
  · rcases h10 with h10 | h10
    · rcases h9 with h9 | h9
      · exfalso
        exact absurd (y.injective (h10.trans h9.symm)) (by decide)
      · simp [pow_two, Equiv.Perm.mul_apply, h10, h9]
    · simp [pow_two, Equiv.Perm.mul_apply, h10]

theorem five_dvd_card_centralizer_a11Coords {v : Fin 3 → ZMod 3} (hz : ∃ i, v i = 0) :
    5 ∣ Nat.card (Subgroup.centralizer
      ({a11Coords (Multiplicative.ofAdd v)} : Set (alternatingGroup (Fin 11)))) := by
  obtain ⟨j, hj0⟩ := hz
  have hmem : a11d5 j ∈ Subgroup.centralizer
      ({a11Coords (Multiplicative.ofAdd v)} : Set (alternatingGroup (Fin 11))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d5_commute_coords j v hj0)
  have hle : Subgroup.zpowers (a11d5 j) ≤ Subgroup.centralizer
      ({a11Coords (Multiplicative.ofAdd v)} : Set (alternatingGroup (Fin 11))) :=
    Subgroup.zpowers_le.mpr hmem
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, d5_order j] at hdvd

private lemma card_centralizer_eq_of_elemAbelian_a11
    {E : Subgroup (alternatingGroup (Fin 11))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) :
    Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))) =
      Nat.card (Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11)))) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_a11A0 hE h27
  have hcard1 : Nat.card (Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11)))) ≤
      Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))) := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      (a11A0 : Set (alternatingGroup (Fin 11))) (MulAut.conj g).toMonoidHom
    have hset : (MulAut.conj g).toMonoidHom '' (a11A0 : Set (alternatingGroup (Fin 11))) =
        (E : Set (alternatingGroup (Fin 11))) := by
      rw [hg, Subgroup.coe_map]
    rw [hset] at h
    calc Nat.card (Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11))))
        = Nat.card ((Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11)))).map
            (MulAut.conj g).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
      _ ≤ Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))) :=
          Subgroup.card_le_of_le h
  have hcard2 : Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))) ≤
      Nat.card (Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11)))) := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      (E : Set (alternatingGroup (Fin 11))) (MulAut.conj g⁻¹).toMonoidHom
    have hset : (MulAut.conj g⁻¹).toMonoidHom '' (E : Set (alternatingGroup (Fin 11))) =
        (a11A0 : Set (alternatingGroup (Fin 11))) := by
      rw [hg, Subgroup.coe_map]
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hz
      · intro hx
        refine ⟨(MulAut.conj g) x, ⟨x, hx, rfl⟩, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    rw [hset] at h
    calc Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11))))
        = Nat.card ((Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))).map
            (MulAut.conj g⁻¹).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
      _ ≤ Nat.card (Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11)))) :=
          Subgroup.card_le_of_le h
  exact le_antisymm hcard2 hcard1

theorem not_five_dvd_card_centralizer_of_elemAbelian_a11
    {E : Subgroup (alternatingGroup (Fin 11))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer (E : Set (alternatingGroup (Fin 11)))) := by
  intro h5
  rw [card_centralizer_eq_of_elemAbelian_a11 hE h27] at h5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy5⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (a11A0 : Set (alternatingGroup (Fin 11))))) 5 h5
  have horderPerm : orderOf ((y : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) = 5 := by
    rw [Subgroup.orderOf_coe (y : alternatingGroup (Fin 11)), Subgroup.orderOf_coe y, hy5]
  have hycomm : ∀ i : Fin 3, Commute (((y : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)))
      (((a11c i : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11))) := by
    intro i
    have h := (Subgroup.mem_centralizer_iff.mp y.2) (a11c i) (a11c_mem_a11A0 i)
    rw [commute_iff_eq]
    exact congrArg (fun z : alternatingGroup (Fin 11) => (z : Equiv.Perm (Fin 11))) h.symm
  have hfix : ∀ p : Fin 11, p.val < 9 →
      (((y : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11))) p = p := by
    intro p hp
    obtain ⟨i, hi⟩ := exists_mem_support_a11c p hp
    have hcop : Nat.Coprime
        (orderOf (((y : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)))) 3 := by
      rw [horderPerm]
      norm_num
    exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.apply_eq_self_of_commute_isThreeCycle
      (a11c_isThreeCycle i) (hycomm i) hcop hi
  have hy2 := sq_eq_one_of_fixes_lt_nine hfix
  have hdvd := orderOf_dvd_of_pow_eq_one hy2
  rw [horderPerm] at hdvd
  norm_num at hdvd

theorem pRank_five_a11_le_two :
    CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 11))) ≤ 2 := by
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) (p := 5) (k := 2)
    Nat.prime_five ?_
  rw [Subgroup.card_top, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

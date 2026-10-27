module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeChain
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
import CFSG.Fischer.Classification.PartIII.Beta.Points
import CFSG.Fischer.Classification.PartIII.U.Points117
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private theorem diagF3Entry_eq_one_of_lt_seven {m : ℕ} {δ : ZMod 3}
    (hm : 8 ≤ m ∨ (m = 7 ∧ δ = 1)) {j : ℕ} (hj : j < 7) (hjm : j < m) :
    diagF3Entry m δ ⟨j, hjm⟩ = 1 := by
  rw [diagF3Entry]
  split_ifs with h
  · rw [Fin.val_mk] at h
    rcases hm with h8 | ⟨rfl, rfl⟩
    · exfalso; omega
    · rfl
  · rfl

private theorem diagF3_single_single {m : ℕ} {δ : ZMod 3} (hm : 8 ≤ m ∨ (m = 7 ∧ δ = 1))
    (j k : Fin m) (hj : (j : ℕ) < 7) (_hk : (k : ℕ) < 7) :
    diagF3 m δ (Pi.single j 1) (Pi.single k 1) = if j = k then 1 else 0 := by
  rw [diagF3_apply, Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, diagF3Entry_eq_one_of_lt_seven hm hj j.isLt, one_mul, mul_one]
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem zmodThree_add_self : ∀ x : ZMod 3, x + x = -x := by
  decide

private def frameVec (m : ℕ) (hm : 7 ≤ m) (i : Fin 7) : Fin m → ZMod 3 :=
  Pi.single (Fin.castLE hm i) 1

private def frameSum (m : ℕ) (hm : 7 ≤ m) : Fin m → ZMod 3 :=
  ∑ i : Fin 7, frameVec m hm i

private theorem frameVec_frameSum_forms {m : ℕ} {δ : ZMod 3} (hm : 8 ≤ m ∨ (m = 7 ∧ δ = 1)) :
    let v := frameVec m (by rcases hm with h8 | ⟨rfl, _⟩ <;> omega)
    let w := frameSum m (by rcases hm with h8 | ⟨rfl, _⟩ <;> omega)
    (∀ i, diagF3 m δ (v i) (v i) = 1) ∧ (∀ i j, i ≠ j → diagF3 m δ (v i) (v j) = 0) ∧
      (∀ i, diagF3 m δ w (v i) = 1) ∧ diagF3 m δ w w = 1 := by
  have hm7 : 7 ≤ m := by rcases hm with h8 | ⟨rfl, _⟩ <;> omega
  have hunit : ∀ i, diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 i) = 1 := by
    intro i
    rw [frameVec, diagF3_single_single hm (Fin.castLE hm7 i) (Fin.castLE hm7 i) (by simp) (by simp)]
    simp
  have hpair : ∀ i j, i ≠ j → diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 j) = 0 := by
    intro i j hij
    change diagF3 m δ (Pi.single (Fin.castLE hm7 i) 1) (Pi.single (Fin.castLE hm7 j) 1) = 0
    rw [diagF3_single_single hm (Fin.castLE hm7 i) (Fin.castLE hm7 j) (by simp) (by simp)]
    rw [if_neg (fun h => hij (Fin.castLE_injective hm7 h))]
  have hwv : ∀ i, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) = 1 := by
    intro i
    rw [frameSum, LinearMap.BilinForm.sum_left, Finset.sum_eq_single i]
    · simpa using hunit i
    · intro j _ hji
      rw [hpair j i hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hww : diagF3 m δ (frameSum m hm7) (frameSum m hm7) = 1 := by
    rw [frameSum, LinearMap.BilinForm.sum_right]
    have hwv' : ∀ i, diagF3 m δ (∑ j : Fin 7, frameVec m hm7 j) (frameVec m hm7 i) = 1 :=
      fun i => by simpa [frameSum] using hwv i
    simp only [hwv', Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  exact ⟨hunit, hpair, hwv, hww⟩

private theorem frameVec_injective {m : ℕ} {hm : 7 ≤ m} :
    ∀ i j : Fin 7, frameVec m hm j = frameVec m hm i → j = i := by
  intro i j h
  have h' : frameVec m hm j (Fin.castLE hm j) = frameVec m hm i (Fin.castLE hm j) :=
    congrFun h (Fin.castLE hm j)
  simp only [frameVec, Pi.single_eq_same] at h'
  by_cases hc : Fin.castLE hm i = Fin.castLE hm j
  · exact (Fin.castLE_injective hm hc).symm
  · rw [Pi.single_eq_of_ne (Ne.symm hc)] at h'
    exact absurd h' (by decide)

private theorem frameVec_ne_neg {m : ℕ} {hm : 7 ≤ m} :
    ∀ i j : Fin 7, frameVec m hm j ≠ -frameVec m hm i := by
  intro i j h
  have h' : frameVec m hm j (Fin.castLE hm j) = -frameVec m hm i (Fin.castLE hm j) :=
    congrFun h (Fin.castLE hm j)
  simp only [frameVec, Pi.single_eq_same] at h'
  by_cases hc : Fin.castLE hm i = Fin.castLE hm j
  · rw [← hc, Pi.single_eq_same] at h'
    exact absurd h' (by decide)
  · rw [Pi.single_eq_of_ne (Ne.symm hc)] at h'
    exact absurd h' (by decide)

private theorem frameVec_ne_frameSum {m : ℕ} {δ : ZMod 3} {hm7 : 7 ≤ m}
    (hpair : ∀ i j, i ≠ j → diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 j) = 0)
    (hwv : ∀ i, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) = 1) :
    ∀ i, frameVec m hm7 i ≠ frameSum m hm7 ∧ frameVec m hm7 i ≠ -frameSum m hm7 := by
  intro i
  let k : Fin 7 := if i = 0 then 1 else 0
  have hk : k ≠ i := by
    dsimp only [k]
    split_ifs with h
    · rw [h]; decide
    · exact fun h0 => h h0.symm
  have h0 : diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 k) = 0 :=
    hpair i k (fun h => hk h.symm)
  have h1 : diagF3 m δ (frameSum m hm7) (frameVec m hm7 k) = 1 := hwv k
  constructor
  · intro h
    rw [h, h1] at h0
    exact one_ne_zero h0
  · intro h
    rw [h] at h0
    have hneg : diagF3 m δ (-frameSum m hm7) (frameVec m hm7 k) =
        -diagF3 m δ (frameSum m hm7) (frameVec m hm7 k) :=
      LinearMap.BilinForm.neg_left (frameSum m hm7) (frameVec m hm7 k)
    rw [hneg, h1] at h0
    exact absurd h0 (by decide)

private theorem scalarFrame_not_commute {m : ℕ} {δ : ZMod 3} (hm7 : 7 ≤ m) (hδ : δ ≠ 0)
    (hunit : ∀ i, diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 i) = 1)
    (hpair : ∀ i j, i ≠ j → diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 j) = 0)
    (hwv : ∀ i, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) = 1)
    (hww : diagF3 m δ (frameSum m hm7) (frameSum m hm7) = 1) :
    (∀ i, reflBar (diagF3 m δ) (frameSum m hm7) ≠
        reflBar (diagF3 m δ) (frameVec m hm7 i)) ∧
      (∀ i, ¬ Commute (reflBar (diagF3 m δ) (frameSum m hm7))
        (reflBar (diagF3 m δ) (frameVec m hm7 i))) := by
  have hm4 : 4 ≤ m := by omega
  have hf : IsF3Form (diagF3 m δ) := isF3Form_diagF3 hδ
  have hne_w := frameVec_ne_frameSum (δ := δ) hpair hwv
  constructor
  · intro i h
    rcases (reflBar_eq_reflBar_iff hf hm4 hww (hunit i)).1 h with h' | h'
    · exact (hne_w i).1 h'
    · exact (hne_w i).2 h'
  · intro i hc
    rcases (reflBar_commute_iff hf hm4 hww (hunit i)).1 hc with h | h | h
    · rw [hwv i] at h
      exact one_ne_zero h
    · exact (hne_w i).1 h
    · exact (hne_w i).2 h

private theorem scalarFrame_static_part {m : ℕ} {δ : ZMod 3}
    (hm7 : 7 ≤ m) (hδ : δ ≠ 0)
    (hunit : ∀ i, diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 i) = 1)
    (hpair : ∀ i j, i ≠ j → diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 j) = 0)
    (hwv : ∀ i, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) = 1)
    (hww : diagF3 m δ (frameSum m hm7) (frameSum m hm7) = 1) :
    (∀ i, reflBar (diagF3 m δ) (frameVec m hm7 i) ∈ D3 (diagF3 m δ)) ∧
      Function.Injective (fun i => reflBar (diagF3 m δ) (frameVec m hm7 i)) ∧
      Pairwise (fun i j => Commute (reflBar (diagF3 m δ) (frameVec m hm7 i))
        (reflBar (diagF3 m δ) (frameVec m hm7 j))) ∧
      reflBar (diagF3 m δ) (frameSum m hm7) ∈ D3 (diagF3 m δ) ∧
      (∀ i, reflBar (diagF3 m δ) (frameSum m hm7) ≠
        reflBar (diagF3 m δ) (frameVec m hm7 i)) ∧
      (∀ i, ¬ Commute (reflBar (diagF3 m δ) (frameSum m hm7))
        (reflBar (diagF3 m δ) (frameVec m hm7 i))) := by
  have hm4 : 4 ≤ m := by omega
  have hf : IsF3Form (diagF3 m δ) := isF3Form_diagF3 hδ
  let v := frameVec m hm7
  let d : Fin 7 → R3 (diagF3 m δ) := fun i => reflBar (diagF3 m δ) (v i)
  have hmem_d : ∀ i, d i ∈ D3 (diagF3 m δ) := fun i => reflBar_mem_D3 (hunit i)
  have hmem_e : reflBar (diagF3 m δ) (frameSum m hm7) ∈ D3 (diagF3 m δ) :=
    reflBar_mem_D3 hww
  have hd : Function.Injective d := by
    intro i j hij
    rcases (reflBar_eq_reflBar_iff hf hm4 (hunit i) (hunit j)).1 hij with h | h
    · exact (frameVec_injective i j h).symm
    · exact absurd h (frameVec_ne_neg i j)
  have hpairwise : Pairwise fun i j => Commute (d i) (d j) := by
    intro i j hij
    exact (reflBar_commute_iff hf hm4 (hunit i) (hunit j)).2 (Or.inl (hpair i j hij))
  obtain ⟨he_ne, hnoncomm⟩ := scalarFrame_not_commute hm7 hδ hunit hpair hwv hww
  exact ⟨hmem_d, hd, hpairwise, hmem_e, he_ne, hnoncomm⟩

private theorem scalarFrame_commute {m : ℕ} {δ : ZMod 3}
    (hm7 : 7 ≤ m) (hδ : δ ≠ 0)
    (hunit : ∀ i, diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 i) = 1)
    (hpair : ∀ i j, i ≠ j → diagF3 m δ (frameVec m hm7 i) (frameVec m hm7 j) = 0)
    (hwv : ∀ i, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) = 1) :
    Commute (reflBar (diagF3 m δ) (frameSum m hm7))
      (List.ofFn fun i => reflBar (diagF3 m δ) (frameVec m hm7 i)).prod := by
  have hm4 : 4 ≤ m := by omega
  have hf : IsF3Form (diagF3 m δ) := isF3Form_diagF3 hδ
  let v := frameVec m hm7
  let w := frameSum m hm7
  let d : Fin 7 → R3 (diagF3 m δ) := fun i => reflBar (diagF3 m δ) (v i)
  let e : R3 (diagF3 m δ) := reflBar (diagF3 m δ) w
  have hzcomm : Commute e (List.ofFn d).prod := by
    let g : F3.reflGroup (diagF3 m δ) :=
      (List.ofFn fun i => reflElt (diagF3 m δ) (v i)).prod
    have hz : (List.ofFn d).prod = (QuotientGroup.mk g : R3 (diagF3 m δ)) := by
      have h := List.prod_hom (List.ofFn fun i => reflElt (diagF3 m δ) (v i))
        (QuotientGroup.mk' (Subgroup.center (F3.reflGroup (diagF3 m δ))))
      rw [List.map_ofFn] at h
      simp [d, g, reflBar]
    have hact : F3.act (g : GL (Fin m) (ZMod 3)) w = -w := by
      have hg : (g : GL (Fin m) (ZMod 3)) =
          (List.ofFn fun i => F3.refl (diagF3 m δ) (v i)).prod := by simp [g]
      rw [hg, act_prod_ofFn_refl 7 v hunit hpair]
      have hsum : (∑ i : Fin 7, diagF3 m δ w (v i) • v i) = w := by
        change (∑ i : Fin 7, diagF3 m δ (frameSum m hm7) (frameVec m hm7 i) •
          frameVec m hm7 i) = frameSum m hm7
        simp only [hwv, one_smul]
        rw [frameSum]
      rw [hsum]
      ext k
      exact zmodThree_add_self (w k)
    have hconj : (QuotientGroup.mk g : R3 (diagF3 m δ)) * e *
        (QuotientGroup.mk g)⁻¹ = e := by
      rw [mk_conj_reflBar hf g w, hact]
      change reflBar (diagF3 m δ) (-w) = reflBar (diagF3 m δ) w
      exact reflBar_neg (f := diagF3 m δ) w
    rw [hz, commute_iff_eq]
    have h2 : (QuotientGroup.mk g : R3 (diagF3 m δ)) * e = e * (QuotientGroup.mk g) := by
      calc (QuotientGroup.mk g) * e =
          ((QuotientGroup.mk g) * e * (QuotientGroup.mk g)⁻¹) * (QuotientGroup.mk g) := by
            group
        _ = e * (QuotientGroup.mk g) := by rw [hconj]
    exact h2.symm
  exact hzcomm

theorem exists_scalarFrame_D3_diagF3 {m : ℕ} {δ : ZMod 3} (hm : 8 ≤ m ∨ (m = 7 ∧ δ = 1))
    (hδ : δ ≠ 0) :
    ∃ (d : Fin 7 → R3 (diagF3 m δ)) (e : R3 (diagF3 m δ)),
      ScalarFrame (D3 (diagF3 m δ)) d e ∧ ∀ i, ¬ Commute e (d i) := by
  have hm7 : 7 ≤ m := by rcases hm with h8 | ⟨rfl, _⟩ <;> omega
  obtain ⟨hunit, hpair, hwv, hww⟩ := frameVec_frameSum_forms (δ := δ) hm
  obtain ⟨hmem_d, hd, hpairwise, hmem_e, he_ne, hnoncomm⟩ :=
    scalarFrame_static_part hm7 hδ hunit hpair hwv hww
  have hzcomm := scalarFrame_commute hm7 hδ hunit hpair hwv
  exact ⟨fun i => reflBar (diagF3 m δ) (frameVec m hm7 i),
    reflBar (diagF3 m δ) (frameSum m hm7), ⟨hmem_d, hd, hpairwise, hmem_e, he_ne, hzcomm⟩,
    hnoncomm⟩

private def triangleC : Fin 6 → ZMod 3 := ![0, 1, 0, 1, 2, 1]

private def e₆Vec : Fin 6 → Fin 5 → ZMod 3 :=
  ![![0, 1, 0, 1, 2], ![1, 1, 0, 0, 2], ![0, 1, 0, 2, 2],
    ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 2], ![0, 0, 1, 0, 0]]

private theorem e₆Vec_norm : ∀ i : Fin 6, Beta.dot5 2 (e₆Vec i) (e₆Vec i) = 1 := by
  decide +kernel

private theorem e₆Vec_edge_pair : ∀ p : Fin 6 × Fin 6,
    CoxeterMatrix.E₆ p.1 p.2 = 3 → Beta.dot5 2 (e₆Vec p.1) (e₆Vec p.2) ≠ 0 := by
  decide +kernel

private theorem e₆Vec_off_pair : ∀ p : Fin 6 × Fin 6, p.1 ≠ p.2 →
    CoxeterMatrix.E₆ p.1 p.2 = 2 → Beta.dot5 2 (e₆Vec p.1) (e₆Vec p.2) = 0 := by
  decide +kernel

private theorem e₆Vec_injective_pair : ∀ p : Fin 6 × Fin 6,
    e₆Vec p.1 = e₆Vec p.2 → p.1 = p.2 := by
  decide +kernel

private theorem e₆Vec_ne_neg_pair : ∀ p : Fin 6 × Fin 6,
    e₆Vec p.2 ≠ -e₆Vec p.1 := by
  decide +kernel

private theorem e₆Vec_edge : ∀ i j : Fin 6, CoxeterMatrix.E₆ i j = 3 →
    Beta.dot5 2 (e₆Vec i) (e₆Vec j) ≠ 0 := by
  intro i j
  exact e₆Vec_edge_pair (i, j)

private theorem e₆Vec_off : ∀ i j : Fin 6, i ≠ j → CoxeterMatrix.E₆ i j = 2 →
    Beta.dot5 2 (e₆Vec i) (e₆Vec j) = 0 := by
  intro i j
  exact e₆Vec_off_pair (i, j)

private theorem e₆Vec_injective : Function.Injective e₆Vec := by
  intro i j h
  exact e₆Vec_injective_pair (i, j) h

private theorem e₆Vec_ne_neg : ∀ i j : Fin 6, e₆Vec j ≠ -e₆Vec i := by
  intro i j
  exact e₆Vec_ne_neg_pair (i, j)

private theorem coxeterMatrixE₆_diag : ∀ i : Fin 6, CoxeterMatrix.E₆ i i = 1 := by decide +kernel

private def e₆Code (v : Fin 5 → ZMod 3) : ℕ :=
  (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val + 81 * (v 4).val

private def e₆Decode (k : ℕ) : Fin 5 → ZMod 3 :=
  ![((k % 3 : ℕ) : ZMod 3), ((k / 3 % 3 : ℕ) : ZMod 3), ((k / 9 % 3 : ℕ) : ZMod 3),
    ((k / 27 % 3 : ℕ) : ZMod 3), ((k / 81 % 3 : ℕ) : ZMod 3)]

private theorem e₆Decode_e₆Code (v : Fin 5 → ZMod 3) :
    e₆Decode (e₆Code v) = v := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  funext i
  fin_cases i
  · change ((e₆Code v % 3 : ℕ) : ZMod 3) = v 0
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
    simp only [e₆Code]
    omega
  · change ((e₆Code v / 3 % 3 : ℕ) : ZMod 3) = v 1
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
    simp only [e₆Code]
    omega
  · change ((e₆Code v / 9 % 3 : ℕ) : ZMod 3) = v 2
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
    simp only [e₆Code]
    omega
  · change ((e₆Code v / 27 % 3 : ℕ) : ZMod 3) = v 3
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
    simp only [e₆Code]
    omega
  · change ((e₆Code v / 81 % 3 : ℕ) : ZMod 3) = v 4
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
    simp only [e₆Code]
    omega

private theorem e₆Code_lt (v : Fin 5 → ZMod 3) : e₆Code v < 243 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  simp only [e₆Code]
  omega

private def e₆Next (a b : ℕ) : ℕ :=
  e₆Code (e₆Decode a + Beta.dot5 2 (e₆Decode a) (e₆Decode b) • e₆Decode b)

private def e₆Ok (a b : ℕ) : Bool :=
  decide (Beta.dot5 2 (e₆Decode a) (e₆Decode a) = 1 ∧
    Beta.dot5 2 (e₆Decode b) (e₆Decode b) = 1 ∧
    Beta.dot5 2 (e₆Decode a) (e₆Decode b) ≠ 0)

private def e₆Init : List ℕ := [192, 166, 219, 111, 174, 9]

private def e₆Steps : List (ℕ × ℕ) :=
  [(9, 9), (174, 9), (111, 111), (166, 111), (174, 111), (144, 9), (219, 111), (6, 6),
   (111, 3), (166, 3), (174, 3), (183, 3), (192, 3), (195, 111), (54, 54), (111, 27), (138, 3),
   (136, 27), (144, 27), (117, 9), (54, 109), (191, 27), (144, 109), (172, 9), (174, 109),
   (40, 3), (40, 9), (49, 3), (40, 27), (67, 3), (67, 9), (76, 3), (6, 40), (77, 3), (77, 9),
   (68, 3), (68, 27), (41, 3), (41, 9), (50, 3), (41, 40), (1, 1), (109, 1), (136, 1),
   (166, 1), (169, 1), (172, 1), (181, 1), (191, 1), (218, 1), (109, 40), (105, 3), (102, 9),
   (93, 3), (111, 40), (101, 1), (100, 9), (91, 1), (117, 40), (89, 1), (88, 3), (85, 1),
   (166, 40), (234, 9), (225, 27), (198, 9)]

private theorem e₆_chainOK : chainOK e₆Next e₆Ok e₆Init e₆Steps = true := by
  decide +kernel

private theorem e₆_cover : ∀ k < 243, Beta.dot5 2 (e₆Decode k) (e₆Decode k) = 1 →
    k ∈ chainLabels e₆Next e₆Init e₆Steps := by
  decide +kernel

private theorem e₆Init_spec : ∀ k ∈ e₆Init, ∃ i : Fin 6, e₆Code (e₆Vec i) = k := by
  decide +kernel

private theorem closure_range_e₆Vec_eq_top :
    Subgroup.closure (Set.range fun i => reflBar (diagF3 5 2) (e₆Vec i)) = ⊤ := by
  have hf : IsF3Form (diagF3 5 2) := isF3Form_diagF3 (by decide)
  have hm4 : 4 ≤ 5 := by decide
  let d : Fin 6 → R3 (diagF3 5 2) := fun i => reflBar (diagF3 5 2) (e₆Vec i)
  let H : Subgroup (R3 (diagF3 5 2)) := Subgroup.closure (Set.range d)
  let τ : ℕ → R3 (diagF3 5 2) := fun k => reflBar (diagF3 5 2) (e₆Decode k)
  have hτd : ∀ i : Fin 6, τ (e₆Code (e₆Vec i)) = d i := by
    intro i
    simp only [τ, d, e₆Decode_e₆Code]
  have hstep : ∀ a b, τ a ∈ H → τ b ∈ H → e₆Ok a b = true →
      τ (e₆Next a b) ∈ H := by
    intro a b ha hb hab
    simp only [e₆Ok, decide_eq_true_eq] at hab
    obtain ⟨-, hnb, habf⟩ := hab
    have hnb' : diagF3 5 2 (e₆Decode b) (e₆Decode b) = 1 := by
      rw [Beta.diagF3_five_apply]
      exact hnb
    have hact :
        e₆Decode a + Beta.dot5 2 (e₆Decode a) (e₆Decode b) • e₆Decode b =
          F3.act (F3.refl (diagF3 5 2) (e₆Decode b)) (e₆Decode a) := by
      rw [F3.act_refl hnb', Beta.diagF3_five_apply]
    have hτnext : τ (e₆Next a b) = τ b * τ a * τ b := by
      dsimp only [τ]
      rw [e₆Next, e₆Decode_e₆Code, hact]
      exact (reflBar_conj hf (e₆Decode b) (e₆Decode a)).symm
    rw [hτnext]
    exact mul_mem (mul_mem hb ha) hb
  have hk : ∀ k ∈ e₆Init, τ k ∈ H := by
    intro k hk
    obtain ⟨i, hi⟩ := e₆Init_spec k hk
    rw [← hi, hτd i]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hmemD : ∀ q ∈ D3 (diagF3 5 2), q ∈ H := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 hq
    have hv5 : Beta.dot5 2 v v = 1 := by
      rwa [Beta.diagF3_five_apply] at hv
    let k := e₆Code v
    have hklt : k < 243 := e₆Code_lt v
    have hknorm : Beta.dot5 2 (e₆Decode k) (e₆Decode k) = 1 := by
      rw [e₆Decode_e₆Code]
      exact hv5
    have hklabels : k ∈ chainLabels e₆Next e₆Init e₆Steps := e₆_cover k hklt hknorm
    have hτk := mem_of_chainOK H τ e₆Next e₆Ok hstep e₆Steps e₆Init hk e₆_chainOK
      k hklabels
    simpa [τ, k, e₆Decode_e₆Code] using hτk
  have hle : Subgroup.closure (D3 (diagF3 5 2)) ≤ H := (Subgroup.closure_le H).2 hmemD
  rw [CFSG.Fischer.Pair.closure_eq (pair_R3 hf hm4)] at hle
  exact le_antisymm le_top hle

theorem exists_coxeterConfig_E₆_D3_diagF3_five_two :
    ∃ d : Fin 6 → R3 (diagF3 5 2), CoxeterConfig (D3 (diagF3 5 2)) CoxeterMatrix.E₆ d ∧
      Subgroup.closure (Set.range d) = ⊤ := by
  have hf : IsF3Form (diagF3 5 2) := isF3Form_diagF3 (by decide)
  have hm4 : 4 ≤ 5 := by decide
  let d : Fin 6 → R3 (diagF3 5 2) := fun i => reflBar (diagF3 5 2) (e₆Vec i)
  have hnorm : ∀ i, diagF3 5 2 (e₆Vec i) (e₆Vec i) = 1 := by
    intro i
    rw [Beta.diagF3_five_apply]
    exact e₆Vec_norm i
  have hmem : ∀ i, d i ∈ D3 (diagF3 5 2) := fun i => reflBar_mem_D3 (hnorm i)
  have hinj : Function.Injective d := by
    intro i j hij
    rcases (reflBar_eq_reflBar_iff hf hm4 (hnorm i) (hnorm j)).1 hij with h | h
    · exact e₆Vec_injective h.symm
    · exact absurd h (e₆Vec_ne_neg i j)
  have hedge : ∀ i j, CoxeterMatrix.E₆ i j = 3 →
      orderOf (d i * d j) = 3 := by
    intro i j hM
    have hij : i ≠ j := by
      intro h
      subst h
      rw [coxeterMatrixE₆_diag i] at hM
      omega
    have hvw : diagF3 5 2 (e₆Vec i) (e₆Vec j) ≠ 0 := by
      rw [Beta.diagF3_five_apply]
      exact e₆Vec_edge i j hM
    have hne : e₆Vec j ≠ e₆Vec i ∧ e₆Vec j ≠ -e₆Vec i :=
      ⟨fun h => hij (e₆Vec_injective h).symm, e₆Vec_ne_neg i j⟩
    exact orderOf_reflBar_mul_reflBar_eq_three hf hm4 (hnorm i) (hnorm j) hvw hne
  have hnonedge : ∀ i j, i ≠ j → CoxeterMatrix.E₆ i j = 2 → Commute (d i) (d j) := by
    intro i j hij hM
    have h0 : diagF3 5 2 (e₆Vec i) (e₆Vec j) = 0 := by
      rw [Beta.diagF3_five_apply]
      exact e₆Vec_off i j hij hM
    exact (reflBar_commute_iff hf hm4 (hnorm i) (hnorm j)).2 (Or.inl h0)
  exact ⟨d, ⟨hmem, hinj, hedge, hnonedge⟩, by simpa [d] using closure_range_e₆Vec_eq_top⟩

private def zx5_perm : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def zx5_vec : Fin 6 → Fin 5 → ZMod 3 := fun i => e₆Vec (zx5_perm i)

private def zx5_coeff : Fin 5 → Fin 6 → ZMod 3 :=
  ![![1, 1, 0, 1, 0, 0], ![1, 0, 2, 0, 1, 2], ![0, 0, 0, 0, 0, 1],
    ![2, 1, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0]]

private theorem zx5_coeff_spec : ∀ (k : Fin 5) (j : Fin 5),
    (∑ i : Fin 6, zx5_coeff k i • zx5_vec i) j = (Pi.single k (1 : ZMod 3) : Fin 5 → ZMod 3) j := by
  decide +kernel

private theorem zx5_coeff_sum (k : Fin 5) :
    ∑ i : Fin 6, zx5_coeff k i • zx5_vec i = (Pi.single k (1 : ZMod 3) : Fin 5 → ZMod 3) := by
  funext j
  exact zx5_coeff_spec k j

theorem exists_forest_spanning_diagF3_five_two :
    ∃ y : Fin 6 → Fin 5 → ZMod 3, (∀ i, diagF3 5 2 (y i) (y i) = 1) ∧
      (∀ i j, i ≠ j → y j ≠ y i ∧ y j ≠ -y i) ∧
      (∀ i i' j, i < j → i' < j → diagF3 5 2 (y i) (y j) ≠ 0 →
        diagF3 5 2 (y i') (y j) ≠ 0 → i = i') ∧
      Submodule.span (ZMod 3) (Set.range y) = ⊤ ∧
      Subgroup.closure (Set.range fun i => reflBar (diagF3 5 2) (y i)) = ⊤ := by
  have hdot : ∀ i : Fin 6, Beta.dot5 2 (zx5_vec i) (zx5_vec i) = 1 := by
    decide +kernel
  have hnorm : ∀ i : Fin 6, diagF3 5 2 (zx5_vec i) (zx5_vec i) = 1 := by
    intro i
    rw [Beta.diagF3_five_apply]
    exact hdot i
  have hsign : ∀ i j : Fin 6, i ≠ j →
      zx5_vec j ≠ zx5_vec i ∧ zx5_vec j ≠ -zx5_vec i := by
    intro i j hij
    exact ⟨fun h => hij (zx5_perm.injective (e₆Vec_injective h)).symm,
      fun h => e₆Vec_ne_neg (zx5_perm i) (zx5_perm j) h⟩
  have hforest : ∀ i i' j : Fin 6, i < j → i' < j →
      diagF3 5 2 (zx5_vec i) (zx5_vec j) ≠ 0 →
      diagF3 5 2 (zx5_vec i') (zx5_vec j) ≠ 0 → i = i' := by
    simp only [Beta.diagF3_five_apply]
    decide +kernel
  have hspan : Submodule.span (ZMod 3) (Set.range zx5_vec) = ⊤ := by
    have hsingle : ∀ k : Fin 5,
        Pi.single k 1 ∈ Submodule.span (ZMod 3) (Set.range zx5_vec) := by
      intro k
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨zx5_coeff k, zx5_coeff_sum k⟩
    refine le_antisymm le_top ?_
    intro v _
    rw [← (Pi.basisFun (ZMod 3) (Fin 5)).sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (hsingle k)
  have hgen : Subgroup.closure (Set.range fun i => reflBar (diagF3 5 2) (zx5_vec i)) = ⊤ := by
    have hcomp : (fun i => reflBar (diagF3 5 2) (zx5_vec i)) =
        (fun i => reflBar (diagF3 5 2) (e₆Vec i)) ∘ zx5_perm := rfl
    rw [hcomp, Set.range_comp, zx5_perm.surjective.range_eq, Set.image_univ]
    exact closure_range_e₆Vec_eq_top
  exact ⟨zx5_vec, hnorm, hsign, hforest, hspan, hgen⟩

end CFSG.StandardType.ZS

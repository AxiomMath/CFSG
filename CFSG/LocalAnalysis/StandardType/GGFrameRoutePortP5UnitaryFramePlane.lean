module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

private def Cst {ι : Type*} (v w : ι → ZMod 3) : Prop :=
  ∃ c : ZMod 3, ∀ i, v i = w i + c

private lemma cst_refl {ι : Type*} (v : ι → ZMod 3) : Cst v v :=
  ⟨0, fun _ => by simp⟩

private lemma cst_symm {ι : Type*} {v w : ι → ZMod 3} (h : Cst v w) : Cst w v := by
  obtain ⟨c, hc⟩ := h
  refine ⟨-c, fun i => ?_⟩
  rw [hc i]
  abel

private lemma cst_trans {ι : Type*} {u v w : ι → ZMod 3} (h1 : Cst u v) (h2 : Cst v w) :
    Cst u w := by
  obtain ⟨c1, h1⟩ := h1
  obtain ⟨c2, h2⟩ := h2
  refine ⟨c1 + c2, fun i => ?_⟩
  rw [h1 i, h2 i]
  abel

private lemma cst_add {ι : Type*} {v w v' w' : ι → ZMod 3}
    (h1 : Cst v w) (h2 : Cst v' w') : Cst (v + v') (w + w') := by
  obtain ⟨c1, h1⟩ := h1
  obtain ⟨c2, h2⟩ := h2
  refine ⟨c1 + c2, fun i => ?_⟩
  simp only [Pi.add_apply]
  rw [h1 i, h2 i]
  abel

private lemma cst_mul {ι : Type*} (a : ZMod 3) {v w : ι → ZMod 3} (h : Cst v w) :
    Cst (fun i => a * v i) (fun i => a * w i) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨a * c, fun i => ?_⟩
  change a * v i = a * w i + a * c
  rw [hc i]
  ring

private lemma cst_hmul {G : Type*} [Group G] {Bs : Subgroup G} {ι : Type*}
    {u : G → ι → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3,
      ∀ i, u (b * b') i = u b i + u b' i + c) :
    ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b') := by
  intro b hb b' hb'
  obtain ⟨c, hc⟩ := hmul b hb b' hb'
  exact ⟨c, fun i => by simpa using hc i⟩

private lemma cst_one {G : Type*} [Group G] {Bs : Subgroup G} {x : G} {ι : Type*}
    {u : G → ι → ZMod 3}
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x) :
    Cst (u 1) (0 : ι → ZMod 3) := by
  obtain ⟨c, hc⟩ := (hconst 1 (one_mem Bs)).2 (one_mem (Subgroup.zpowers x))
  exact ⟨c, fun i => by simpa using hc i⟩

private lemma cst_inv {G : Type*} [Group G] {Bs : Subgroup G} {ι : Type*}
    {u : G → ι → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : ι → ZMod 3)) {b : G} (hb : b ∈ Bs) :
    Cst (u b⁻¹) (fun i => -u b i) := by
  have hm : Cst (u 1) (u b + u b⁻¹) := by
    simpa [mul_inv_cancel] using hmul b hb b⁻¹ (inv_mem hb)
  have hsum : Cst (u b + u b⁻¹) (0 : ι → ZMod 3) := cst_trans (cst_symm hm) h1
  obtain ⟨c, hc⟩ := hsum
  refine ⟨c, fun i => ?_⟩
  have hi : u b i + u b⁻¹ i = c := by simpa using hc i
  rw [← hi]
  rw [neg_add_cancel_left]

private lemma cst_pow {G : Type*} [Group G] {Bs : Subgroup G} {ι : Type*}
    {u : G → ι → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : ι → ZMod 3)) {b : G} (hb : b ∈ Bs) (n : ℕ) :
    Cst (u (b ^ n)) (fun i => (n : ZMod 3) * u b i) := by
  induction n with
  | zero => simpa [Cst, zero_mul] using h1
  | succ n ih =>
      have hm : Cst (u (b ^ (n + 1))) (u (b ^ n) + u b) := by
        simpa [pow_succ] using hmul (b ^ n) (pow_mem hb n) b hb
      have hadd : Cst (u (b ^ n) + u b)
          (fun i => (n : ZMod 3) * u b i + u b i) :=
        cst_add ih (cst_refl (u b))
      have hgg : Cst (fun i => (n : ZMod 3) * u b i + u b i)
          (fun i => ((n + 1 : ℕ) : ZMod 3) * u b i) := by
        have heq : (fun i => (n : ZMod 3) * u b i + u b i) =
            fun i => ((n + 1 : ℕ) : ZMod 3) * u b i := by
          funext i
          rw [Nat.cast_succ, add_mul, one_mul]
        rw [heq]
        exact cst_refl _
      exact cst_trans (cst_trans hm hadd) hgg

private lemma closure_const {G : Type*} [Group G] {Bs : Subgroup G} {x z : G} {ι : Type*}
    {u : G → ι → ZMod 3}
    (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    {I : Finset ι} (hzI : ∀ i ∈ I, ∀ j ∈ I, u z i = u z j) :
    ∀ b ∈ Subgroup.closure ({x, z} : Set G),
      b ∈ Bs ∧ ∀ i ∈ I, ∀ j ∈ I, u b i = u b j := by
  have h1 : Cst (u 1) (0 : ι → ZMod 3) := cst_one hconst
  have hxconst : ∃ c : ZMod 3, ∀ i, u x i = c :=
    (hconst x hxBs).2 (Subgroup.mem_zpowers x)
  intro b hb
  refine Subgroup.closure_induction (k := ({x, z} : Set G))
    (p := fun b _ => b ∈ Bs ∧ ∀ i ∈ I, ∀ j ∈ I, u b i = u b j) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨hxBs, fun i _ j _ => by
        rw [hxconst.choose_spec i, hxconst.choose_spec j]⟩
    · exact ⟨hzBs, hzI⟩
  · refine ⟨one_mem Bs, fun i _ j _ => ?_⟩
    obtain ⟨c, hc⟩ := h1
    rw [show u 1 i = 0 + c from hc i, show u 1 j = 0 + c from hc j]
  · intro y y' hy hy' hY hY'
    refine ⟨mul_mem hY.1 hY'.1, fun i hi j hj => ?_⟩
    obtain ⟨c, hc⟩ := hmul y hY.1 y' hY'.1
    simp only [Pi.add_apply] at hc
    rw [hc i, hc j, hY.2 i hi j hj, hY'.2 i hi j hj]
  · intro y hy hY
    refine ⟨inv_mem hY.1, fun i hi j hj => ?_⟩
    obtain ⟨c, hc⟩ := cst_inv hmul h1 hY.1
    simp only at hc
    rw [hc i, hc j, hY.2 i hi j hj]

private lemma mem_closure_of_cst_mul {G : Type*} [Group G] {Bs : Subgroup G} {x z b : G}
    {ι : Type*} {u : G → ι → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : ι → ZMod 3))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hb : b ∈ Bs) (hz : z ∈ Bs) {α : ZMod 3}
    (h : Cst (u b) (fun i => α * u z i)) :
    b ∈ Subgroup.closure ({x, z} : Set G) := by
  let n : ℕ := (-α).val
  have hn : (n : ZMod 3) = -α := by
    dsimp [n]
    exact ZMod.natCast_zmod_val (-α)
  have hzpow : Cst (u (z ^ n)) (fun i => (-α) * u z i) := by
    simpa [hn] using cst_pow hmul h1 hz n
  have hbzn : b * z ^ n ∈ Bs := mul_mem hb (pow_mem hz n)
  have hprod : Cst (u (b * z ^ n)) (u b + u (z ^ n)) :=
    hmul b hb (z ^ n) (pow_mem hz n)
  have hsum : Cst (u b + u (z ^ n)) (fun i => α * u z i + (-α) * u z i) :=
    cst_add h hzpow
  have hzero : Cst (u (b * z ^ n)) (0 : ι → ZMod 3) := by
    refine cst_trans (cst_trans hprod hsum) ⟨0, fun i => ?_⟩
    change α * u z i + (-α) * u z i = (0 : ZMod 3) + 0
    ring
  have hmemx : b * z ^ n ∈ Subgroup.zpowers x :=
    (hconst (b * z ^ n) hbzn).1 (by simpa [Cst] using hzero)
  have hxcl : x ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hzmem : z ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hzcl : z ^ n ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.pow_mem (Subgroup.closure ({x, z} : Set G)) hzmem n
  have hbzcl : b * z ^ n ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.zpowers_le_of_mem hxcl hmemx
  have hmem := mul_mem hbzcl (inv_mem hzcl)
  simpa [mul_assoc] using hmem

private lemma exists_ne_map_eq_of_natCard_lt {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (h : Nat.card β < Nat.card α) : ∃ x y, x ≠ y ∧ f x = f y := by
  have hnot : ¬Function.Injective f := by
    intro hinj
    have hle : Nat.card α ≤ Nat.card β := Nat.card_le_card_of_injective f hinj
    exact (not_lt_of_ge hle) h
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  exact ⟨x, y, hne, hxy⟩

private lemma exists_mem_relIndex {G : Type*} [Group G] [Finite G] {B Bs : Subgroup G}
    (hBBs : B ≤ Bs) (hidx : Nat.card Bs ≤ 3 * Nat.card B)
    {y : Fin 4 → G} (hy : ∀ k, y k ∈ Bs) :
    ∃ j k : Fin 4, j ≠ k ∧ (y j)⁻¹ * y k ∈ B := by
  have hcard_sub : Nat.card (B.subgroupOf Bs) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBBs).toEquiv
  have hcard : Nat.card (Bs ⧸ B.subgroupOf Bs) * Nat.card B = Nat.card Bs := by
    rw [← hcard_sub]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf Bs)).symm
  have hpos : 0 < Nat.card B := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨1, one_mem B⟩, inferInstance⟩
  have hQ : Nat.card (Bs ⧸ B.subgroupOf Bs) ≤ 3 := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc Nat.card (Bs ⧸ B.subgroupOf Bs) * Nat.card B = Nat.card Bs := hcard
      _ ≤ 3 * Nat.card B := hidx
  let f : Fin 4 → Bs ⧸ B.subgroupOf Bs := fun k => (⟨y k, hy k⟩ : Bs)
  have hlt : Nat.card (Bs ⧸ B.subgroupOf Bs) < Nat.card (Fin 4) := by
    rw [Nat.card_fin]
    exact lt_of_le_of_lt hQ (by norm_num)
  obtain ⟨j, k, hjk_ne, hjk_eq⟩ := exists_ne_map_eq_of_natCard_lt f hlt
  refine ⟨j, k, hjk_ne, ?_⟩
  have hmem : (⟨y j, hy j⟩ : Bs)⁻¹ * ⟨y k, hy k⟩ ∈ B.subgroupOf Bs :=
    QuotientGroup.eq.mp hjk_eq
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private lemma zmod3_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma zmod3_neg_one_ne_zero : (-1 : ZMod 3) ≠ 0 := by decide

private lemma zmod3_one_ne_neg_one : (1 : ZMod 3) ≠ -1 := by decide

private lemma zmod3_nine_eq_zero : (9 : ZMod 3) = 0 := by decide

private lemma zmod3_add_ne_self {a : ZMod 3} (ha : a ≠ 0) (t : ZMod 3) :
    a + t ≠ t := by
  intro h
  have h' : a + t = 0 + t := by
    rw [zero_add]
    exact h
  exact ha (add_right_cancel h')

private lemma zmod3_sq_eq_one : ∀ s : ZMod 3, s ≠ 0 → s * s = 1 := by decide

private lemma sum_single_sub_single_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) :
    ∑ i, (Pi.single a 1 - Pi.single b 1 : ι → ZMod 3) i = 0 := by
  have ha : ∑ i, (Pi.single a 1 : ι → ZMod 3) i = 1 := by
    simp
  have hb : ∑ i, (Pi.single b 1 : ι → ZMod 3) i = 1 := by
    simp
  change ∑ i, ((Pi.single a 1 : ι → ZMod 3) i -
    (Pi.single b 1 : ι → ZMod 3) i) = 0
  rw [Finset.sum_sub_distrib, ha, hb]
  simp

private lemma cst_inv_mul_single {G : Type*} [Group G] {Bs : Subgroup G} {ι : Type*}
    [DecidableEq ι] {u : G → ι → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : ι → ZMod 3))
    {a b : G} (ha : a ∈ Bs) (hb : b ∈ Bs) {k j : ι}
    (hca : Cst (u a) (Pi.single k 1 : ι → ZMod 3))
    (hcb : Cst (u b) (Pi.single j 1 : ι → ZMod 3)) :
    Cst (u (a⁻¹ * b)) ((Pi.single j 1 : ι → ZMod 3) - (Pi.single k 1 : ι → ZMod 3)) := by
  have hinv : Cst (u a⁻¹) (fun i => -u a i) := cst_inv hmul h1 ha
  have hprod : Cst (u (a⁻¹ * b)) (u a⁻¹ + u b) :=
    hmul (a⁻¹) (inv_mem ha) b hb
  have hneg : Cst (fun i => -u a i) (fun i => -(Pi.single k 1 : ι → ZMod 3) i) := by
    simpa using cst_mul (-1 : ZMod 3) hca
  have hneg' : Cst (u a⁻¹) (fun i => -(Pi.single k 1 : ι → ZMod 3) i) :=
    cst_trans hinv hneg
  have hsum : Cst (u a⁻¹ + u b)
      (fun i => -(Pi.single k 1 : ι → ZMod 3) i + (Pi.single j 1 : ι → ZMod 3) i) :=
    cst_add hneg' hcb
  have heq : (fun i => -(Pi.single k 1 : ι → ZMod 3) i + (Pi.single j 1 : ι → ZMod 3) i) =
      (fun i => ((Pi.single j 1 : ι → ZMod 3) - (Pi.single k 1 : ι → ZMod 3)) i) := by
    funext i
    rw [Pi.sub_apply]
    ring
  have hfinal : Cst (u (a⁻¹ * b))
      (fun i => (Pi.single j 1 : ι → ZMod 3) i - (Pi.single k 1 : ι → ZMod 3) i) :=
    cst_trans hprod (by simpa [heq, Pi.sub_apply] using hsum)
  rw [show ((Pi.single j 1 : ι → ZMod 3) - (Pi.single k 1 : ι → ZMod 3) : ι → ZMod 3) =
      fun i => (Pi.single j 1 : ι → ZMod 3) i - (Pi.single k 1 : ι → ZMod 3) i from by
    funext i
    rw [Pi.sub_apply]]
  exact hfinal

private lemma card_erase_one {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    (Finset.univ.erase j).card = Fintype.card ι - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]

private lemma card_erase_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {j k : ι}
    (hjk : j ≠ k) :
    ((Finset.univ.erase j).erase k).card = Fintype.card ι - 2 := by
  have hk : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
  rw [Finset.card_erase_of_mem hk, card_erase_one, Nat.sub_sub]

private lemma sum_eq_of_eq_on_compl_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ZMod 3} {j k : ι} (hjk : j ≠ k) (h2 : 2 ≤ Fintype.card ι)
    {lam : ZMod 3} (hlam : ∀ i, i ≠ j → i ≠ k → f i = lam) :
    ∑ i, f i = (Fintype.card ι : ZMod 3) * lam + (f j - lam) + (f k - lam) := by
  let I : Finset ι := (Finset.univ.erase j).erase k
  have hk : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
  have hj : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ j
  have hsumI : Finset.sum I f = (I.card : ZMod 3) * lam := by
    have hcongr : ∀ i ∈ I, f i = lam := by
      intro i hi
      exact hlam i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        (Finset.mem_erase.mp hi).1
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  have h1 := Finset.sum_erase_add (Finset.univ.erase j) f hk
  have h2' := Finset.sum_erase_add (Finset.univ : Finset ι) f hj
  have h3 : ∑ i, f i = Finset.sum I f + f k + f j := by
    rw [← h2', ← h1]
  have hcard : I.card + 2 = Fintype.card ι := by
    dsimp [I]
    rw [card_erase_pair hjk]
    exact Nat.sub_add_cancel h2
  have hcast : (Fintype.card ι : ZMod 3) = (I.card : ZMod 3) + 2 := by
    rw [← hcard, Nat.cast_add]
    norm_num
  rw [h3, hsumI, hcast]
  ring

private lemma two_coord_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι) {G : Type*} [Group G] {B Bs : Subgroup G} {x z : G}
    {u : G → ι → ZMod 3} (hBBs : B ≤ Bs)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) {j k : ι} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : ι → ZMod 3) - (Pi.single j 1 : ι → ZMod 3)) i + t) :
    ∃ I : Finset ι, (∀ i, i ∈ I ↔ u z i = t) ∧
      I.card = Fintype.card ι - 2 ∧ z ∉ Subgroup.zpowers x ∧ I.Nonempty ∧
      (∀ i ∈ I, ∀ i' ∈ I, u z i = u z i') := by
  let I : Finset ι := (Finset.univ.erase j).erase k
  have hztk : u z k = 1 + t := by
    rw [hzt k, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk.symm]
    simp
  have hztj : u z j = -1 + t := by
    rw [hzt j, Pi.sub_apply, Pi.single_eq_of_ne hjk, Pi.single_eq_same]
    simp
  have hiff : ∀ i, i ∈ I ↔ u z i = t := by
    intro i
    constructor
    · intro hi
      simp only [I, Finset.mem_erase, Finset.mem_univ, and_true] at hi
      rw [hzt i, Pi.sub_apply, Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2]
      simp
    · intro hi
      have hik : i ≠ k := by
        intro h
        subst i
        exact (zmod3_add_ne_self zmod3_one_ne_zero t) (hztk.symm.trans hi)
      have hij : i ≠ j := by
        intro h
        subst i
        exact (zmod3_add_ne_self zmod3_neg_one_ne_zero t) (hztj.symm.trans hi)
      exact Finset.mem_erase.mpr ⟨hik, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩⟩
  have hcardI : I.card = Fintype.card ι - 2 := by
    dsimp [I]
    exact card_erase_pair hjk
  have hIne : I.Nonempty :=
    Finset.card_pos.mp (by rw [hcardI]; exact Nat.sub_pos_of_lt hcard)
  have hznot : z ∉ Subgroup.zpowers x := by
    intro hzpow
    obtain ⟨c, hc⟩ := (hconst z (hBBs hzB)).2 hzpow
    have h1t : (1 : ZMod 3) + t = -1 + t := by
      rw [← hztk, hc k, ← hc j, hztj]
    exact zmod3_one_ne_neg_one (add_right_cancel h1t)
  have hzI : ∀ i ∈ I, ∀ i' ∈ I, u z i = u z i' := by
    intro i hi i' hi'
    rw [(hiff i).mp hi, (hiff i').mp hi']
  exact ⟨I, hiff, hcardI, hznot, hIne, hzI⟩

private lemma two_coord_cst {ι : Type*} [DecidableEq ι] {G : Type*} [Group G]
    {u : G → ι → ZMod 3} {z b : G} {j k : ι} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : ι → ZMod 3) - (Pi.single j 1 : ι → ZMod 3)) i + t)
    {I : Finset ι} (hiff : ∀ i, i ∈ I ↔ u z i = t)
    {lam α β : ZMod 3} (hlam : ∀ i ∈ I, u b i = lam)
    (hα : α = u b k - lam) (hβ : β = u b j - lam) (hs : α + β = 0) :
    Cst (u b) (fun i => α * u z i) := by
  have hβ' : β = -α := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hs
  refine ⟨lam - α * t, fun i => ?_⟩
  dsimp only
  by_cases hij : i = j
  · subst i
    have hzj : u z j = -1 + t := by
      rw [hzt j, Pi.sub_apply, Pi.single_eq_of_ne hjk, Pi.single_eq_same]
      simp
    have hbj : u b j = lam + β := by rw [hβ]; abel
    rw [hzj, hbj, hβ']
    ring
  · by_cases hik : i = k
    · subst i
      have hzk : u z k = 1 + t := by
        rw [hzt k, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk.symm]
        simp
      have hbk : u b k = lam + α := by rw [hα]; abel
      rw [hzk, hbk]
      ring
    · have hzi : u z i = t := by
        rw [hzt i, Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
        simp
      have hi : i ∈ I := (hiff i).mpr hzi
      have hbi : u b i = lam := hlam i hi
      rw [hbi, hzi]
      ring

private lemma two_coord_mem_closure {ι : Type*} [DecidableEq ι]
    {G : Type*} [Group G] {B Bs : Subgroup G} {x z b : G} {u : G → ι → ZMod 3}
    (hBBs : B ≤ Bs)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) (hbB : b ∈ B) {j k : ι} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : ι → ZMod 3) - (Pi.single j 1 : ι → ZMod 3)) i + t)
    {I : Finset ι} (hiff : ∀ i, i ∈ I ↔ u z i = t)
    {i0 : ι} (hi0 : i0 ∈ I)
    (hbI : ∀ i ∈ I, ∀ i' ∈ I, u b i = u b i')
    (hs : (u b k - u b i0) + (u b j - u b i0) = 0) :
    b ∈ Subgroup.closure ({x, z} : Set G) := by
  let lam : ZMod 3 := u b i0
  let α : ZMod 3 := u b k - lam
  let β : ZMod 3 := u b j - lam
  have hlam : ∀ i ∈ I, u b i = lam := by
    intro i hi
    simpa [lam] using hbI i hi i0 hi0
  have hs' : α + β = 0 := by simpa [α, β, lam] using hs
  have hCst : Cst (u b) (fun i => α * u z i) :=
    two_coord_cst hjk hzt hiff hlam rfl rfl hs'
  exact mem_closure_of_cst_mul hmul (cst_one hconst) hconst (hBBs hbB) (hBBs hzB) hCst

private lemma cst_coord_pair {ι : Type*} [DecidableEq ι] {G : Type*} [Group G]
    {u : G → ι → ZMod 3} {z b : G} {j k : ι} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : ι → ZMod 3) - (Pi.single j 1 : ι → ZMod 3)) i + t)
    {I : Finset ι} (hiff : ∀ i, i ∈ I ↔ u z i = t)
    {lam α β : ZMod 3} (hlam : ∀ i ∈ I, u b i = lam)
    (hα : α = u b k - lam) (hβ : β = u b j - lam) :
    Cst (u b) (fun i => β * (Pi.single j 1 : ι → ZMod 3) i +
      α * (Pi.single k 1 : ι → ZMod 3) i) := by
  refine ⟨lam, fun i => ?_⟩
  dsimp only
  by_cases hij : i = j
  · subst i
    have hbj : u b j = lam + β := by rw [hβ]; abel
    rw [hbj, Pi.single_eq_same, Pi.single_eq_of_ne hjk]
    ring
  · by_cases hik : i = k
    · subst i
      have hbk : u b k = lam + α := by rw [hα]; abel
      rw [hbk, Pi.single_eq_of_ne hjk.symm, Pi.single_eq_same]
      ring
    · have hzi : u z i = t := by
        rw [hzt i, Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
        simp
      have hi : i ∈ I := (hiff i).mpr hzi
      have hbi : u b i = lam := hlam i hi
      rw [hbi, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
      ring

private lemma seven_two_shift {G : Type*} [Group G] {Bs : Subgroup G} {b z : G}
    {u : G → Fin 7 → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : Fin 7 → ZMod 3))
    (hb : b ∈ Bs) (hz : z ∈ Bs) {j k : Fin 7} {t α β : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : Fin 7 → ZMod 3) - (Pi.single j 1 : Fin 7 → ZMod 3)) i + t)
    (hbCst : Cst (u b) (fun i => β * (Pi.single j 1 : Fin 7 → ZMod 3) i +
      α * (Pi.single k 1 : Fin 7 → ZMod 3) i))
    {n : ℕ} (hn : (n : ZMod 3) = β) :
    Cst (u (b * z ^ n)) (fun i => (α + β) * (Pi.single k 1 : Fin 7 → ZMod 3) i) := by
  have hzpow : Cst (u (z ^ n)) (fun i => β * u z i) := by
    simpa [hn] using cst_pow hmul h1 hz n
  have hm := hmul b hb (z ^ n) (pow_mem hz n)
  have hcomb : Cst (u b + u (z ^ n))
      (fun i => (β * (Pi.single j 1 : Fin 7 → ZMod 3) i +
        α * (Pi.single k 1 : Fin 7 → ZMod 3) i) + β * u z i) :=
    cst_add hbCst hzpow
  have hred : Cst (fun i => (β * (Pi.single j 1 : Fin 7 → ZMod 3) i +
        α * (Pi.single k 1 : Fin 7 → ZMod 3) i) + β * u z i)
      (fun i => (α + β) * (Pi.single k 1 : Fin 7 → ZMod 3) i) := by
    refine ⟨β * t, fun i => ?_⟩
    dsimp only
    rw [hzt i, Pi.sub_apply]
    ring
  exact cst_trans hm (cst_trans hcomb hred)
private lemma seven_two_forbid {G : Type*} [Group G] {B Bs : Subgroup G} {x z b : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hcaseB : ∀ (m : Fin 7) (w : G), w ∈ B → ¬ Cst (u w) ((Pi.single m 1 : Fin 7 → ZMod 3)))
    (hzB : z ∈ B) (hbB : b ∈ B) {j k : Fin 7} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : Fin 7 → ZMod 3) - (Pi.single j 1 : Fin 7 → ZMod 3)) i + t)
    {I : Finset (Fin 7)} (hiff : ∀ i, i ∈ I ↔ u z i = t)
    {lam α β : ZMod 3} (hlam : ∀ i ∈ I, u b i = lam)
    (hα : α = u b k - lam) (hβ : β = u b j - lam) (hs : α + β ≠ 0) :
    False := by
  have h1 : Cst (u 1) (0 : Fin 7 → ZMod 3) := cst_one hconst
  have hbCst : Cst (u b) (fun i => β * (Pi.single j 1 : Fin 7 → ZMod 3) i +
      α * (Pi.single k 1 : Fin 7 → ZMod 3) i) :=
    cst_coord_pair hjk hzt hiff hlam hα hβ
  let n : ℕ := β.val
  have hn : (n : ZMod 3) = β := by
    dsimp [n]
    exact ZMod.natCast_zmod_val β
  have hwCst := seven_two_shift hmul h1 (hBBs hbB) (hBBs hzB) hzt hbCst hn
  have hwB : b * z ^ n ∈ B := mul_mem hbB (pow_mem hzB n)
  let m : ℕ := (α + β).val
  have hmcast : (m : ZMod 3) = α + β := by
    dsimp [m]
    exact ZMod.natCast_zmod_val (α + β)
  have hpow := cst_pow hmul h1 (hBBs hwB) m
  have hscaled : Cst (fun i => (m : ZMod 3) * u (b * z ^ n) i)
      ((Pi.single k 1 : Fin 7 → ZMod 3)) := by
    have h := cst_mul (m : ZMod 3) hwCst
    have heq : (fun i => (m : ZMod 3) * ((α + β) * (Pi.single k 1 : Fin 7 → ZMod 3) i)) =
        ((Pi.single k 1 : Fin 7 → ZMod 3) : Fin 7 → ZMod 3) := by
      funext i
      rw [hmcast, ← mul_assoc, zmod3_sq_eq_one (α + β) hs, one_mul]
    simpa [heq] using h
  exact hcaseB k ((b * z ^ n) ^ m) (pow_mem hwB m) (cst_trans hpow hscaled)

private lemma seven_two_forward {G : Type*} [Group G] {B Bs : Subgroup G} {x z b : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs) (_hx : x ∈ B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hcaseB : ∀ (m : Fin 7) (w : G), w ∈ B → ¬ Cst (u w) ((Pi.single m 1 : Fin 7 → ZMod 3)))
    (hzB : z ∈ B) {j k : Fin 7} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : Fin 7 → ZMod 3) - (Pi.single j 1 : Fin 7 → ZMod 3)) i + t)
    {I : Finset (Fin 7)} (hiff : ∀ i, i ∈ I ↔ u z i = t) (hIne : I.Nonempty)
    (hbB : b ∈ B) (hbI : ∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') :
    b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨i0, hi0⟩ := hIne
  let lam : ZMod 3 := u b i0
  let α : ZMod 3 := u b k - lam
  let β : ZMod 3 := u b j - lam
  have hlam : ∀ i ∈ I, u b i = lam := by
    intro i hi
    simpa [lam] using hbI i hi i0 hi0
  by_cases hs : α + β = 0
  · exact two_coord_mem_closure hBBs hmul hconst hzB hbB hjk hzt hiff hi0 hbI
      (by simpa [α, β, lam] using hs)
  · exact (seven_two_forbid hBBs hmul hconst hcaseB hzB hbB hjk hzt hiff hlam
      rfl rfl hs).elim

private lemma seven_two {G : Type*} [Group G] {B Bs : Subgroup G} {x z : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs) (hx : x ∈ B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hcaseB : ∀ (m : Fin 7) (w : G), w ∈ B → ¬ Cst (u w) ((Pi.single m 1 : Fin 7 → ZMod 3)))
    (hzB : z ∈ B) {j k : Fin 7} (hjk : j ≠ k)
    (hzCst : Cst (u z) ((Pi.single k 1 : Fin 7 → ZMod 3) - (Pi.single j 1 : Fin 7 → ZMod 3))) :
    ∃ (I : Finset (Fin 7)) (t : ZMod 3), (∀ i, i ∈ I ↔ u z i = t) ∧
      I.card = 5 ∧ z ∉ Subgroup.zpowers x ∧
      ∀ b ∈ B, (∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') ↔
        b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨t, hzt⟩ := hzCst
  obtain ⟨I, hiff, hcard, hznot, hIne, hzI⟩ :=
    two_coord_data (ι := Fin 7) (by decide) hBBs hconst hzB hjk hzt
  have hcard5 : I.card = 5 := by
    rw [Fintype.card_fin] at hcard
    norm_num at hcard
    exact hcard
  refine ⟨I, t, hiff, hcard5, hznot, fun b hbB => ⟨?_, ?_⟩⟩
  · intro hbI
    exact seven_two_forward hBBs hx hmul hconst hcaseB hzB hjk hzt hiff hIne hbB hbI
  · intro hbcl
    exact (closure_const (hBBs hx) (hBBs hzB) hmul hconst hzI b hbcl).2

private lemma seven_one_data {G : Type*} [Group G] {B Bs : Subgroup G} {x z : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) {j : Fin 7} {t : ZMod 3}
    (hzt : ∀ i, u z i = (Pi.single j 1 : Fin 7 → ZMod 3) i + t) :
    ∃ I : Finset (Fin 7), (∀ i, i ∈ I ↔ u z i = t) ∧ I.card = 6 ∧
      z ∉ Subgroup.zpowers x ∧ I.Nonempty ∧
      (∀ i ∈ I, ∀ i' ∈ I, u z i = u z i') := by
  let I : Finset (Fin 7) := Finset.univ.erase j
  have hztj : u z j = 1 + t := by simpa using hzt j
  have hiff : ∀ i, i ∈ I ↔ u z i = t := by
    intro i
    constructor
    · intro hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      rw [hzt i, Pi.single_eq_of_ne hij]
      simp
    · intro hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      intro hij
      subst i
      exact (zmod3_add_ne_self zmod3_one_ne_zero t) (hztj.symm.trans hi)
  have hcard : I.card = 6 := by
    dsimp [I]
    rw [card_erase_one, Fintype.card_fin]
  have hIne : I.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hznot : z ∉ Subgroup.zpowers x := by
    intro hzpow
    obtain ⟨c, hc⟩ := (hconst z (hBBs hzB)).2 hzpow
    obtain ⟨j', hj'⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin 7) (by decide) j
    have hztj' : u z j' = t := by
      rw [hzt j', Pi.single_eq_of_ne hj']
      simp
    exact (zmod3_add_ne_self zmod3_one_ne_zero t)
      (by rw [← hztj, hc j, ← hc j', hztj'])
  have hzI : ∀ i ∈ I, ∀ i' ∈ I, u z i = u z i' := by
    intro i hi i' hi'
    rw [(hiff i).mp hi, (hiff i').mp hi']
  exact ⟨I, hiff, hcard, hznot, hIne, hzI⟩

private lemma seven_one_forward {G : Type*} [Group G] {B Bs : Subgroup G} {x z b : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) {j : Fin 7} {t : ZMod 3}
    (hzt : ∀ i, u z i = (Pi.single j 1 : Fin 7 → ZMod 3) i + t)
    {I : Finset (Fin 7)} (hiff : ∀ i, i ∈ I ↔ u z i = t) (hIne : I.Nonempty)
    (hbB : b ∈ B) (hbI : ∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') :
    b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨i0, hi0⟩ := hIne
  let lam : ZMod 3 := u b i0
  let α : ZMod 3 := u b j - lam
  have hlam : ∀ i ∈ I, u b i = lam := by
    intro i hi
    simpa [lam] using hbI i hi i0 hi0
  have hCst : Cst (u b) (fun i => α * u z i) := by
    refine ⟨lam - α * t, fun i => ?_⟩
    dsimp only
    by_cases hij : i = j
    · subst i
      have hzj : u z j = 1 + t := by simpa using hzt j
      have hbj : u b j = lam + α := by dsimp [α]; abel
      rw [hzj, hbj]
      ring
    · have hzi : u z i = t := by
        rw [hzt i, Pi.single_eq_of_ne hij]
        simp
      have hi : i ∈ I := (hiff i).mpr hzi
      have hbi : u b i = lam := hlam i hi
      rw [hbi, hzi]
      ring
  exact mem_closure_of_cst_mul hmul (cst_one hconst) hconst (hBBs hbB) (hBBs hzB) hCst

private lemma seven_one {G : Type*} [Group G] {B Bs : Subgroup G} {x z : G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs) (hx : x ∈ B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hzB : z ∈ B) {j : Fin 7} (hzCst : Cst (u z) ((Pi.single j 1 : Fin 7 → ZMod 3))) :
    ∃ (I : Finset (Fin 7)) (t : ZMod 3), (∀ i, i ∈ I ↔ u z i = t) ∧
      I.card = 6 ∧ z ∉ Subgroup.zpowers x ∧
      ∀ b ∈ B, (∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') ↔
        b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨t, hzt⟩ := hzCst
  obtain ⟨I, hiff, hcard, hznot, hIne, hzI⟩ :=
    seven_one_data hBBs hconst hzB hzt
  refine ⟨I, t, hiff, hcard, hznot, fun b hbB => ⟨?_, ?_⟩⟩
  · intro hbI
    exact seven_one_forward hBBs hmul hconst hzB hzt hiff hIne hbB hbI
  · intro hbcl
    exact (closure_const (hBBs hx) (hBBs hzB) hmul hconst hzI b hbcl).2
private def sevenY {G : Type*} [One G] (y : Fin 7 → G) : Fin 4 → G :=
  fun k => if k = 0 then 1 else if k = 1 then y 0 else if k = 2 then y 1 else y 2

private def sevenM : Fin 4 → Fin 7 :=
  fun k => if k = 0 then 0 else if k = 1 then 0 else if k = 2 then 1 else 2

private lemma sevenY_apply {G : Type*} [One G] {y : Fin 7 → G} (k : Fin 4) (hk : k ≠ 0) :
    sevenY y k = y (sevenM k) := by
  fin_cases k <;> simp_all [sevenY, sevenM]

private lemma sevenY_mem {G : Type*} [Group G] {Bs : Subgroup G} {y : Fin 7 → G}
    (hy : ∀ m, y m ∈ Bs) : ∀ k, sevenY y k ∈ Bs := by
  intro k
  fin_cases k <;> simp [sevenY, one_mem Bs, hy 0, hy 1, hy 2]

private lemma sevenM_inj {a b : Fin 4} (ha : a ≠ 0) (hb : b ≠ 0) :
    sevenM a = sevenM b → a = b := by
  intro h
  fin_cases a <;> fin_cases b <;> simp_all [sevenM]

private lemma seven_caseB_pair {G : Type*} [Group G] [Finite G] {B Bs : Subgroup G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs)
    (hidx : Nat.card Bs ≤ 3 * Nat.card B)
    {y : Fin 7 → G} (hy : ∀ m, y m ∈ Bs)
    (hyCst : ∀ m, Cst (u (y m)) ((Pi.single m 1 : Fin 7 → ZMod 3)))
    (hcaseB : ∀ (m : Fin 7) (w : G), w ∈ B → ¬ Cst (u w) ((Pi.single m 1 : Fin 7 → ZMod 3))) :
    ∃ (a b : Fin 4), a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      (sevenY y a)⁻¹ * sevenY y b ∈ B := by
  obtain ⟨a, b, hab, hzB⟩ := exists_mem_relIndex hBBs hidx (sevenY_mem hy)
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    have hb0 : b ≠ 0 := by
      intro hb0
      subst b
      exact hab rfl
    have hbB : sevenY y b ∈ B := by simpa [sevenY] using hzB
    rw [sevenY_apply b hb0] at hbB
    exact hcaseB (sevenM b) (y (sevenM b)) hbB (hyCst (sevenM b))
  have hb : b ≠ 0 := by
    intro hb0
    subst b
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact hab rfl
    have haB : sevenY y a ∈ B := by
      have hinv : (sevenY y a)⁻¹ ∈ B := by simpa [sevenY] using hzB
      simpa using inv_mem hinv
    rw [sevenY_apply a ha0] at haB
    exact hcaseB (sevenM a) (y (sevenM a)) haB (hyCst (sevenM a))
  exact ⟨a, b, ha, hb, hab, hzB⟩

private lemma seven_caseB_z {G : Type*} [Group G] [Finite G] {B Bs : Subgroup G}
    {u : G → Fin 7 → ZMod 3} (hBBs : B ≤ Bs)
    (hidx : Nat.card Bs ≤ 3 * Nat.card B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : Fin 7 → ZMod 3))
    {y : Fin 7 → G} (hy : ∀ m, y m ∈ Bs)
    (hyCst : ∀ m, Cst (u (y m)) ((Pi.single m 1 : Fin 7 → ZMod 3)))
    (hcaseB : ∀ (m : Fin 7) (w : G), w ∈ B → ¬ Cst (u w) ((Pi.single m 1 : Fin 7 → ZMod 3))) :
    ∃ (j k : Fin 7) (z : G), j ≠ k ∧ z ∈ B ∧
      Cst (u z) ((Pi.single k 1 : Fin 7 → ZMod 3) - (Pi.single j 1 : Fin 7 → ZMod 3)) := by
  obtain ⟨a, b, ha, hb, hab, hzB⟩ := seven_caseB_pair hBBs hidx hy hyCst hcaseB
  have hYa : sevenY y a = y (sevenM a) := sevenY_apply a ha
  have hYb : sevenY y b = y (sevenM b) := sevenY_apply b hb
  have hmn : sevenM a ≠ sevenM b := fun h => hab (sevenM_inj ha hb h)
  refine ⟨sevenM a, sevenM b, (y (sevenM a))⁻¹ * y (sevenM b), hmn, ?_, ?_⟩
  · simpa [hYa, hYb] using hzB
  · have hCa : Cst (u (sevenY y a)) ((Pi.single (sevenM a) 1 : Fin 7 → ZMod 3)) := by
      rw [hYa]
      exact hyCst (sevenM a)
    have hCb : Cst (u (sevenY y b)) ((Pi.single (sevenM b) 1 : Fin 7 → ZMod 3)) := by
      rw [hYb]
      exact hyCst (sevenM b)
    have hCst := cst_inv_mul_single hmul h1 (sevenY_mem hy a) (sevenY_mem hy b) hCa hCb
    simpa [hYa, hYb] using hCst

private def nineIdx : Fin 4 → Fin 9 := Fin.castLE (by norm_num)

private lemma nineIdx_injective : Function.Injective nineIdx := by
  simpa [nineIdx] using Fin.castLE_injective (by norm_num : 4 ≤ 9)

private lemma nine_z {G : Type*} [Group G] [Finite G] {B Bs : Subgroup G}
    {u : G → Fin 9 → ZMod 3} (hBBs : B ≤ Bs)
    (hidx : Nat.card Bs ≤ 3 * Nat.card B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (h1 : Cst (u 1) (0 : Fin 9 → ZMod 3))
    {y : Fin 4 → G} (hy : ∀ k, y k ∈ Bs)
    (hyCst : ∀ k, Cst (u (y k)) ((Pi.single 0 1 : Fin 9 → ZMod 3) -
      (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3))) :
    ∃ (j k : Fin 4) (z : G), j ≠ k ∧ z ∈ B ∧
      Cst (u z) ((Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) := by
  obtain ⟨j, k, hjk, hzB⟩ := exists_mem_relIndex hBBs hidx hy
  refine ⟨j, k, (y j)⁻¹ * y k, hjk, hzB, ?_⟩
  have hprod : Cst (u ((y j)⁻¹ * y k)) (u (y j)⁻¹ + u (y k)) :=
    hmul _ (inv_mem (hy j)) _ (hy k)
  have hinv : Cst (u (y j)⁻¹) (fun i => -u (y j) i) :=
    cst_inv hmul h1 (hy j)
  have hneg : Cst (fun i => -u (y j) i)
      (fun i => -((Pi.single 0 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3)) i) := by
    simpa using cst_mul (-1 : ZMod 3) (hyCst j)
  have hneg' : Cst (u (y j)⁻¹)
      (fun i => -((Pi.single 0 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3)) i) :=
    cst_trans hinv hneg
  have hsum : Cst (u (y j)⁻¹ + u (y k))
      (fun i => -((Pi.single 0 1 : Fin 9 → ZMod 3) - (Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3)) i +
        ((Pi.single 0 1 : Fin 9 → ZMod 3) - (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i) :=
    cst_add hneg' (hyCst k)
  have heq : (fun i => -((Pi.single 0 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3)) i +
        ((Pi.single 0 1 : Fin 9 → ZMod 3) - (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i) =
      (fun i => ((Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i) := by
    funext i
    simp only [Pi.sub_apply]
    ring
  have hfinal : Cst (u ((y j)⁻¹ * y k))
      (fun i => ((Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i) :=
    cst_trans hprod (by simpa [heq] using hsum)
  rw [show ((Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3) -
      (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3) : Fin 9 → ZMod 3) =
      fun i => ((Pi.single (nineIdx j) 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i from by
    funext i
    rw [Pi.sub_apply]]
  exact hfinal

private lemma nine_forward {G : Type*} [Group G] {B Bs : Subgroup G} {x z b : G}
    {u : G → Fin 9 → ZMod 3} (hBBs : B ≤ Bs) (_hx : x ∈ B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hsum : ∀ b ∈ Bs, ∑ i, u b i = 0)
    (hzB : z ∈ B) (hbB : b ∈ B) {j k : Fin 9} (hjk : j ≠ k) {t : ZMod 3}
    (hzt : ∀ i, u z i = ((Pi.single k 1 : Fin 9 → ZMod 3) - (Pi.single j 1 : Fin 9 → ZMod 3)) i + t)
    {I : Finset (Fin 9)} (hiff : ∀ i, i ∈ I ↔ u z i = t) (hIne : I.Nonempty)
    (hbI : ∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') :
    b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨i0, hi0⟩ := hIne
  let lam : ZMod 3 := u b i0
  let α : ZMod 3 := u b k - lam
  let β : ZMod 3 := u b j - lam
  have hlam : ∀ i ∈ I, u b i = lam := by
    intro i hi
    simpa [lam] using hbI i hi i0 hi0
  have hlamI : ∀ i, i ≠ j → i ≠ k → u b i = lam := by
    intro i hij hik
    have hzi : u z i = t := by
      rw [hzt i, Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
      simp
    exact hlam i ((hiff i).mpr hzi)
  have hpair := sum_eq_of_eq_on_compl_pair (f := u b) hjk (by decide) (lam := lam) hlamI
  have hsum0 : ∑ i, u b i = 0 := hsum b (hBBs hbB)
  have h9 : (Fintype.card (Fin 9) : ZMod 3) = 0 := by
    rw [Fintype.card_fin]
    exact zmod3_nine_eq_zero
  rw [hsum0, h9, zero_mul, zero_add] at hpair
  have hs' : (u b j - lam) + (u b k - lam) = 0 := hpair.symm
  have hs : α + β = 0 := by
    dsimp [α, β]
    rw [add_comm]
    exact hs'
  exact two_coord_mem_closure hBBs hmul hconst hzB hbB hjk hzt hiff hi0 hbI
    (by simpa [α, β, lam] using hs)

private lemma nine {G : Type*} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G}
    {u : G → Fin 9 → ZMod 3} (hBBs : B ≤ Bs) (hx : x ∈ B)
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b'))
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔
      b ∈ Subgroup.zpowers x)
    (hsum : ∀ b ∈ Bs, ∑ i, u b i = 0)
    (hzB : z ∈ B) {j k : Fin 9} (hjk : j ≠ k)
    (hzCst : Cst (u z) ((Pi.single j 1 : Fin 9 → ZMod 3) - (Pi.single k 1 : Fin 9 → ZMod 3))) :
    ∃ (I : Finset (Fin 9)) (t : ZMod 3), (∀ i, i ∈ I ↔ u z i = t) ∧
      I.card = 7 ∧ z ∉ Subgroup.zpowers x ∧
      ∀ b ∈ B, (∀ i ∈ I, ∀ i' ∈ I, u b i = u b i') ↔
        b ∈ Subgroup.closure ({x, z} : Set G) := by
  obtain ⟨t, hzt⟩ := hzCst
  obtain ⟨I, hiff, hcard, hznot, hIne, hzI⟩ :=
    two_coord_data (ι := Fin 9) (by decide) (j := k) (k := j)
      hBBs hconst hzB hjk.symm hzt
  have hcard7 : I.card = 7 := by
    rw [Fintype.card_fin] at hcard
    norm_num at hcard
    exact hcard
  refine ⟨I, t, hiff, hcard7, hznot, fun b hbB => ⟨?_, ?_⟩⟩
  · intro hbI
    exact nine_forward (j := k) (k := j) hBBs hx hmul hconst hsum hzB hbB hjk.symm hzt
      hiff hIne hbI
  · intro hbcl
    exact (closure_const (hBBs hx) (hBBs hzB) hmul hconst hzI b hbcl).2

theorem exists_goodPlane_seven {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    (hBBs : B ≤ Bs) (hidx : Nat.card Bs ≤ 3 * Nat.card B) (hx : x ∈ B)
    {u : G → Fin 7 → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v : Fin 7 → ZMod 3, ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) :
    ∃ z ∈ B, ∃ (I : Finset (Fin 7)) (t : ZMod 3), (∀ i, i ∈ I ↔ u z i = t) ∧
      z ∉ Subgroup.zpowers x ∧
      (∀ b ∈ B, (∀ i ∈ I, ∀ j ∈ I, u b i = u b j) ↔ b ∈ Subgroup.closure {x, z}) ∧
      ((I.card = 6 ∧ ∃ j : Fin 7, ∃ c : ZMod 3, ∀ i,
          u z i = (Pi.single j 1 : Fin 7 → ZMod 3) i + c) ∨
        (I.card = 5 ∧ ∃ j k : Fin 7, j ≠ k ∧ ∃ c : ZMod 3, ∀ i,
          u z i = (Pi.single j 1 - Pi.single k 1 : Fin 7 → ZMod 3) i + c)) := by
  choose y hy hyc using fun j : Fin 7 => hsurj ((Pi.single j 1 : Fin 7 → ZMod 3))
  have hmulC : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b') := cst_hmul hmul
  have h1 : Cst (u 1) (0 : Fin 7 → ZMod 3) := cst_one hconst
  by_cases hcaseA : ∃ (j : Fin 7) (b : G), b ∈ B ∧ Cst (u b) ((Pi.single j 1 : Fin 7 → ZMod 3))
  · obtain ⟨j, b, hbB, hbCst⟩ := hcaseA
    obtain ⟨I, t, hI, hIc, hb, hBF⟩ := seven_one hBBs hx hmulC hconst hbB hbCst
    exact ⟨b, hbB, I, t, hI, hb, hBF, Or.inl ⟨hIc, j, hbCst⟩⟩
  · have hcaseB : ∀ (m : Fin 7) (b : G), b ∈ B →
        ¬ Cst (u b) (Pi.single m 1 : Fin 7 → ZMod 3) := by
      intro m b hbB hbCst
      exact hcaseA ⟨m, b, hbB, hbCst⟩
    obtain ⟨m, n, z, hmn, hzB, hzCst⟩ :=
      seven_caseB_z hBBs hidx hmulC h1 hy hyc hcaseB
    obtain ⟨I, t, hI, hIc, hz, hBF⟩ := seven_two hBBs hx hmulC hconst hcaseB hzB hmn hzCst
    exact ⟨z, hzB, I, t, hI, hz, hBF, Or.inr ⟨hIc, n, m, hmn.symm, hzCst⟩⟩

theorem exists_goodPlane_nine {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    (hBBs : B ≤ Bs) (hidx : Nat.card Bs ≤ 3 * Nat.card B) (hx : x ∈ B)
    {u : G → Fin 9 → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x)
    (hsum : ∀ b ∈ Bs, ∑ i, u b i = 0)
    (hsurj : ∀ v : Fin 9 → ZMod 3, ∑ i, v i = 0 →
      ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) :
    ∃ z ∈ B, ∃ (I : Finset (Fin 9)) (t : ZMod 3), (∀ i, i ∈ I ↔ u z i = t) ∧
      I.card = 7 ∧ z ∉ Subgroup.zpowers x ∧
      (∀ b ∈ B, (∀ i ∈ I, ∀ j ∈ I, u b i = u b j) ↔ b ∈ Subgroup.closure {x, z}) ∧
      ∃ j k : Fin 9, j ≠ k ∧ ∃ c : ZMod 3, ∀ i,
        u z i = (Pi.single j 1 - Pi.single k 1 : Fin 9 → ZMod 3) i + c := by
  have hzero : ∀ k : Fin 4,
      ∑ i : Fin 9, ((Pi.single 0 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3) : Fin 9 → ZMod 3) i = 0 :=
    fun k => sum_single_sub_single_zero 0 (nineIdx k)
  have hsurj' : ∀ k : Fin 4, ∃ b ∈ Bs, ∃ c, ∀ i : Fin 9,
      u b i = ((Pi.single 0 1 : Fin 9 → ZMod 3) -
        (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) i + c := by
    intro k
    exact hsurj ((Pi.single 0 1 : Fin 9 → ZMod 3) -
      (Pi.single (nineIdx k) 1 : Fin 9 → ZMod 3)) (hzero k)
  choose y hy hyc using hsurj'
  have hmulC : ∀ b ∈ Bs, ∀ b' ∈ Bs, Cst (u (b * b')) (u b + u b') := cst_hmul hmul
  have h1 : Cst (u 1) (0 : Fin 9 → ZMod 3) := cst_one hconst
  obtain ⟨j, k, z, hjk, hzB, hzCst⟩ := nine_z hBBs hidx hmulC h1 hy hyc
  have hjk9 : nineIdx j ≠ nineIdx k := fun h => hjk (nineIdx_injective h)
  obtain ⟨I, t, hI, hIc, hz, hBF⟩ := nine hBBs hx hmulC hconst hsum hzB hjk9 hzCst
  exact ⟨z, hzB, I, t, hI, hIc, hz, hBF, nineIdx j, nineIdx k, hjk9, hzCst⟩

end CFSG.StandardType.FrameRoute.UnitaryModel
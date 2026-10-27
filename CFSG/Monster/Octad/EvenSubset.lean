module

public import CFSG.Monster.FourierTriality
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.Monster.Octad

open Module Matrix

variable {I : Type*} [DecidableEq I]

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

@[expose] def ind (s : Finset I) : I → ZMod 2 := fun i => if i ∈ s then 1 else 0

theorem ind_apply (s : Finset I) (i : I) : ind s i = if i ∈ s then 1 else 0 := rfl

@[expose] def evenSubsets (d : Finset I) : Submodule (ZMod 2) (I → ZMod 2) where
  carrier := {x | (∀ i, i ∉ d → x i = 0) ∧ ∑ i ∈ d, x i = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun i hi => by simp [hx i hi, hy i hi], by simp [Finset.sum_add_distrib, hx', hy']⟩
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨fun i hi => by simp [hx i hi], by simp [← Finset.mul_sum, hx']⟩

omit [DecidableEq I] in
theorem mem_evenSubsets {d : Finset I} {x : I → ZMod 2} :
    x ∈ evenSubsets d ↔ (∀ i, i ∉ d → x i = 0) ∧ ∑ i ∈ d, x i = 0 := Iff.rfl

@[expose] def complSpan (d : Finset I) : Submodule (ZMod 2) (evenSubsets d) :=
  (Submodule.span (ZMod 2) {ind d}).comap (evenSubsets d).subtype

@[expose] def EvenQuot (d : Finset I) : Type _ := evenSubsets d ⧸ complSpan d

instance (d : Finset I) : AddCommGroup (EvenQuot d) :=
  inferInstanceAs (AddCommGroup (evenSubsets d ⧸ complSpan d))

instance (d : Finset I) : Module (ZMod 2) (EvenQuot d) :=
  inferInstanceAs (Module (ZMod 2) (evenSubsets d ⧸ complSpan d))

@[expose] def mk (d : Finset I) : evenSubsets d →ₗ[ZMod 2] EvenQuot d := (complSpan d).mkQ

theorem mk_surjective (d : Finset I) : Function.Surjective (mk d) :=
  Submodule.mkQ_surjective _

instance (d : Finset I) : Finite (evenSubsets d) := by
  refine Finite.of_injective (fun x : evenSubsets d => fun i : d => (x : I → ZMod 2) i) ?_
  intro x y h
  ext i
  by_cases hi : i ∈ d
  · exact congrFun h ⟨i, hi⟩
  · rw [x.2.1 i hi, y.2.1 i hi]

instance (d : Finset I) : Finite (EvenQuot d) := Finite.of_surjective _ (mk_surjective d)

instance (d : Finset I) : Fintype (EvenQuot d) := Fintype.ofFinite _

instance (d : Finset I) : DecidableEq (EvenQuot d) := Classical.decEq _

theorem mem_complSpan_iff {d : Finset I} (x : evenSubsets d) :
    x ∈ complSpan d ↔ (x : I → ZMod 2) = 0 ∨ (x : I → ZMod 2) = ind d := by
  simp only [complSpan, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    rcases zmod2_cases c with rfl | rfl
    · left; rw [← hc, zero_smul]
    · right; rw [← hc, one_smul]
  · rintro (h | h)
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩

theorem mk_eq_mk_iff {d : Finset I} (x y : evenSubsets d) :
    mk d x = mk d y ↔ (x : I → ZMod 2) = y ∨ (x : I → ZMod 2) = y + ind d := by
  refine (Submodule.Quotient.eq (complSpan d) (x := x) (y := y)).trans ?_
  rw [mem_complSpan_iff, Submodule.coe_sub, sub_eq_zero, sub_eq_iff_eq_add']

theorem mk_eq_zero_iff {d : Finset I} (x : evenSubsets d) :
    mk d x = 0 ↔ x ∈ complSpan d :=
  Submodule.Quotient.mk_eq_zero (complSpan d)

theorem sum_ind {d s : Finset I} (hs : s ⊆ d) : ∑ i ∈ d, ind s i = (s.card : ZMod 2) := by
  simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]

theorem sum_mul_ind (x : I → ZMod 2) {d s : Finset I} (hs : s ⊆ d) :
    ∑ i ∈ d, x i * ind s i = ∑ i ∈ s, x i := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]

theorem ind_mem_evenSubsets {d δ : Finset I} (hδ : δ ⊆ d) (he : Even δ.card) :
    ind δ ∈ evenSubsets d :=
  ⟨fun i hi => ite_eq_right fun h => hi (hδ h), by
    rw [sum_ind hδ]; exact (ZMod.natCast_eq_zero_iff_even).2 he⟩

def cls (d δ : Finset I) : EvenQuot d :=
  if h : δ ⊆ d ∧ Even δ.card then mk d ⟨ind δ, ind_mem_evenSubsets h.1 h.2⟩ else 0

theorem cls_eq {d δ : Finset I} (hδ : δ ⊆ d) (he : Even δ.card) :
    cls d δ = mk d ⟨ind δ, ind_mem_evenSubsets hδ he⟩ := dite_eq_left ⟨hδ, he⟩

theorem exists_cls_eq {d : Finset I} (v : EvenQuot d) :
    ∃ δ, δ ⊆ d ∧ Even δ.card ∧ cls d δ = v := by
  obtain ⟨x, rfl⟩ := mk_surjective d v
  set δ := d.filter fun i => (x : I → ZMod 2) i ≠ 0 with hδdef
  have hind : ind δ = x := by
    funext i
    by_cases hi : i ∈ d
    · rcases zmod2_cases ((x : I → ZMod 2) i) with h | h <;> simp [ind, δ, hi, h]
    · simp [ind, δ, hi, x.2.1 i hi]
  have hδ : δ ⊆ d := Finset.filter_subset _ _
  have he : Even δ.card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← sum_ind hδ, hind]
    exact x.2.2
  refine ⟨δ, hδ, he, ?_⟩
  rw [cls_eq hδ he]
  congr 1
  exact Subtype.ext hind

theorem cls_eq_cls_iff {d δ ε : Finset I} (hδ : δ ⊆ d) (hδe : Even δ.card) (hε : ε ⊆ d)
    (hεe : Even ε.card) : cls d δ = cls d ε ↔ ε = δ ∨ ε = d \ δ := by
  rw [cls_eq hδ hδe, cls_eq hε hεe, mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · left
      ext i
      have := congrFun h i
      by_cases hδi : i ∈ δ <;> by_cases hεi : i ∈ ε <;> simp_all [ind]
    · right
      ext i
      have := congrFun h i
      by_cases hdi : i ∈ d
      · by_cases hδi : i ∈ δ <;> by_cases hεi : i ∈ ε <;> simp_all [ind]
      · simp only [Finset.mem_sdiff, hdi, false_and, iff_false]
        exact fun h => hdi (hε h)
  · rintro (rfl | rfl)
    · left; rfl
    · right
      funext i
      simp only [Pi.add_apply, ind, Finset.mem_sdiff]
      by_cases hdi : i ∈ d
      · by_cases hδi : i ∈ δ
        · simp [hdi, hδi]
        · simp [hdi, hδi]; decide
      · have : i ∉ δ := fun h => hdi (hδ h)
        simp [hdi, this]

theorem even_card_sdiff {d δ : Finset I} (hd : Even d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    Even (d \ δ).card := by
  rw [Finset.card_sdiff_of_subset hδ, Nat.even_sub (Finset.card_le_card hδ)]
  exact iff_of_true hd he

theorem cls_compl {d δ : Finset I} (hd : Even d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    cls d (d \ δ) = cls d δ := by
  rw [cls_eq_cls_iff Finset.sdiff_subset (even_card_sdiff hd hδ he) hδ he]
  exact Or.inr (Finset.sdiff_sdiff_eq_self hδ).symm

@[expose] def wt (d : Finset I) (x : I → ZMod 2) : ℕ := ∑ i ∈ d, (x i).val

@[expose] def dotForm (d : Finset I) : LinearMap.BilinForm (ZMod 2) (evenSubsets d) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i ∈ d, (x : I → ZMod 2) i * (y : I → ZMod 2) i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_assoc, Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_left_comm, Finset.mul_sum])

omit [DecidableEq I] in
theorem dotForm_apply (d : Finset I) (x y : evenSubsets d) :
    dotForm d x y = ∑ i ∈ d, (x : I → ZMod 2) i * (y : I → ZMod 2) i := rfl

private theorem val_add_add : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by
  decide

omit [DecidableEq I] in
theorem wt_add (d : Finset I) (x y : I → ZMod 2) :
    wt d (x + y) + 2 * ∑ i ∈ d, (x i * y i).val = wt d x + wt d y := by
  simp only [wt, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib, val_add_add]

omit [DecidableEq I] in
theorem natCast_wt (d : Finset I) (x : I → ZMod 2) : (wt d x : ZMod 2) = ∑ i ∈ d, x i := by
  simp only [wt, Nat.cast_sum, ZMod.natCast_zmod_val]

omit [DecidableEq I] in
theorem even_wt {d : Finset I} {x : I → ZMod 2} (hx : x ∈ evenSubsets d) : Even (wt d x) := by
  rw [← ZMod.natCast_eq_zero_iff_even, natCast_wt]
  exact hx.2

theorem wt_ind {d s : Finset I} (hs : s ⊆ d) : wt d (ind s) = s.card := by
  have h : ∀ i, (ind s i).val = if i ∈ s then 1 else 0 := fun i => by
    unfold ind; split_ifs <;> rfl
  simp only [wt, h, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs,
    Nat.cast_id]

omit [DecidableEq I] in
theorem evenQuad_add_aux (d : Finset I) (x y : evenSubsets d) :
    ((wt d ↑(x + y) / 2 : ℕ) : ZMod 2) =
      ((wt d x / 2 : ℕ) : ZMod 2) + ((wt d y / 2 : ℕ) : ZMod 2) + dotForm d x y := by
  have h := wt_add d x y
  rw [← Submodule.coe_add] at h
  obtain ⟨a, ha⟩ := even_wt x.2
  obtain ⟨b, hb⟩ := even_wt y.2
  set c := ∑ i ∈ d, ((x : I → ZMod 2) i * (y : I → ZMod 2) i).val with hcdef
  have hc : (c : ZMod 2) = dotForm d x y := by
    simp only [c, dotForm_apply, Nat.cast_sum, ZMod.natCast_zmod_val]
  have key : wt d ↑(x + y) / 2 + c = wt d x / 2 + wt d y / 2 := by omega
  have key' := congrArg (Nat.cast : ℕ → ZMod 2) key
  push_cast at key'
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← hc]
  linear_combination key' - (c : ZMod 2) * h2

@[expose] def evenQuad (d : Finset I) : QuadraticForm (ZMod 2) (evenSubsets d) where
  toFun x := ((wt d x / 2 : ℕ) : ZMod 2)
  toFun_smul a x := by
    rcases zmod2_cases a with rfl | rfl
    · simp [wt]
    · simp
  exists_companion' := ⟨dotForm d, evenQuad_add_aux d⟩

omit [DecidableEq I] in
theorem evenQuad_apply (d : Finset I) (x : evenSubsets d) :
    evenQuad d x = ((wt d x / 2 : ℕ) : ZMod 2) := rfl

omit [DecidableEq I] in
theorem evenQuad_add (d : Finset I) (x y : evenSubsets d) :
    evenQuad d (x + y) = evenQuad d x + evenQuad d y + dotForm d x y :=
  evenQuad_add_aux d x y

theorem complSpan_le_radical {d : Finset I} (hd : 4 ∣ d.card) :
    complSpan d ≤ (evenQuad d).radical := by
  intro x hx
  rcases (mem_complSpan_iff x).1 hx with h | h
  · rw [show x = 0 from Subtype.ext h]
    exact Submodule.zero_mem _
  · have hq : evenQuad d x = 0 := by
      rw [evenQuad_apply, h, wt_ind subset_rfl]
      obtain ⟨k, hk⟩ := hd
      rw [hk, show 4 * k / 2 = 2 * k by omega, Nat.cast_mul]
      exact mul_eq_zero_of_left rfl _
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hq, fun n => ?_⟩
    rw [evenQuad_add, hq, zero_add, dotForm_apply, h]
    simp only [ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.inter_self]
    rw [n.2.2, add_zero]

def liftQuad (d : Finset I) (h : 4 ∣ d.card) : QuadraticForm (ZMod 2) (EvenQuot d) :=
  (evenQuad d).lift (complSpan d) (complSpan_le_radical h)

def quadForm (d : Finset I) : QuadraticForm (ZMod 2) (EvenQuot d) :=
  if h : 4 ∣ d.card then liftQuad d h else 0

theorem quadForm_mk {d : Finset I} (hd : 4 ∣ d.card) (x : evenSubsets d) :
    quadForm d (mk d x) = evenQuad d x := by
  rw [quadForm, dite_eq_left hd]
  rfl

theorem polarBilin_quadForm_mk {d : Finset I} (hd : 4 ∣ d.card) (x y : evenSubsets d) :
    QuadraticMap.polarBilin (quadForm d) (mk d x) (mk d y) = dotForm d x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, quadForm_mk hd,
    quadForm_mk hd, quadForm_mk hd, evenQuad_add]
  ring

theorem quadForm_cls {d δ : Finset I} (hd : 4 ∣ d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    quadForm d (cls d δ) = ((δ.card / 2 : ℕ) : ZMod 2) := by
  rw [cls_eq hδ he, quadForm_mk hd, evenQuad_apply, wt_ind hδ]

theorem polarBilin_quadForm_cls {d δ ε : Finset I} (hd : 4 ∣ d.card) (hδ : δ ⊆ d)
    (hδe : Even δ.card) (hε : ε ⊆ d) (hεe : Even ε.card) :
    QuadraticMap.polarBilin (quadForm d) (cls d δ) (cls d ε) = ((δ ∩ ε).card : ZMod 2) := by
  rw [cls_eq hδ hδe, cls_eq hε hεe, polarBilin_quadForm_mk hd, dotForm_apply]
  have h : ∀ i, ind δ i * ind ε i = ind (δ ∩ ε) i := fun i => by
    simp only [ind, ite_zero_mul_ite_zero, mul_one, Finset.mem_inter]
  simp only [h]
  exact sum_ind (Finset.inter_subset_left.trans hδ)

theorem polarBilin_quadForm_separatingLeft {d : Finset I} (hd : 4 ∣ d.card) (hne : d.Nonempty) :
    (QuadraticMap.polarBilin (quadForm d)).SeparatingLeft := by
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective d v
  have hpair : ∀ i ∈ d, ∀ j ∈ d, (x : I → ZMod 2) i = (x : I → ZMod 2) j := by
    intro i hi j hj
    by_cases hij : i = j
    · rw [hij]
    · have hsub : ({i, j} : Finset I) ⊆ d :=
        Finset.insert_subset hi (Finset.singleton_subset_iff.2 hj)
      have he : Even ({i, j} : Finset I).card := by
        rw [Finset.card_pair hij]; exact even_two
      have h := hv (cls d {i, j})
      rw [cls_eq hsub he, polarBilin_quadForm_mk hd, dotForm_apply, sum_mul_ind _ hsub,
        Finset.sum_pair hij] at h
      exact zmod2_eq_of_add_eq_zero _ _ h
  obtain ⟨i₀, hi₀⟩ := hne
  refine (mk_eq_zero_iff x).2 ((mem_complSpan_iff x).2 ?_)
  rcases zmod2_cases ((x : I → ZMod 2) i₀) with h | h
  · left
    funext i
    by_cases hi : i ∈ d
    · rw [hpair i hi i₀ hi₀, h]; rfl
    · exact x.2.1 i hi
  · right
    funext i
    by_cases hi : i ∈ d
    · rw [hpair i hi i₀ hi₀, h, ind_apply, ite_eq_left hi]
    · rw [x.2.1 i hi, ind_apply, ite_eq_right hi]

theorem polarBilin_quadForm_nondegenerate {d : Finset I} (hd : 4 ∣ d.card) (hne : d.Nonempty) :
    (QuadraticMap.polarBilin (quadForm d)).Nondegenerate := by
  have hl := polarBilin_quadForm_separatingLeft hd hne
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [polarBilin_symm]
  exact hy x

theorem sum_evenQuot_eq {M : Type*} [AddCommMonoid M] {d : Finset I} (hd : Even d.card) {i₀ : I}
    (hi₀ : i₀ ∈ d) (F : EvenQuot d → M) :
    ∑ v, F v = ∑ δ ∈ (d.erase i₀).powerset with Even δ.card, F (cls d δ) := by
  symm
  refine Finset.sum_bij (fun δ _ => cls d δ) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro δ hδ ε hε h
    simp only [Finset.mem_filter, Finset.mem_powerset] at hδ hε
    have hδd : δ ⊆ d := hδ.1.trans (Finset.erase_subset _ _)
    have hεd : ε ⊆ d := hε.1.trans (Finset.erase_subset _ _)
    rcases (cls_eq_cls_iff hδd hδ.2 hεd hε.2).1 h with h' | h'
    · exact h'.symm
    · exfalso
      have : i₀ ∈ ε := by
        rw [h']
        exact Finset.mem_sdiff.2 ⟨hi₀, fun h => Finset.notMem_erase i₀ d (hδ.1 h)⟩
      exact Finset.notMem_erase i₀ d (hε.1 this)
  · intro v _
    obtain ⟨δ, hδ, he, rfl⟩ := exists_cls_eq v
    by_cases h : i₀ ∈ δ
    · refine ⟨d \ δ, ?_, cls_compl hd hδ he⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => ?_, even_card_sdiff hd hδ he⟩
      rw [Finset.mem_sdiff] at hi
      exact Finset.mem_erase.2 ⟨fun h' => hi.2 (h' ▸ h), hi.1⟩
    · refine ⟨δ, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun i hi => Finset.mem_erase.2 ⟨fun h' => h (h' ▸ hi), hδ hi⟩, he⟩

theorem card_evenQuot {d : Finset I} (hd : d.card = 8) : Fintype.card (EvenQuot d) = 64 := by
  obtain ⟨i₀, hi₀⟩ : d.Nonempty := Finset.card_pos.1 (by omega)
  have h7 : (d.erase i₀).card = 7 := by rw [Finset.card_erase_of_mem hi₀, hd]
  rw [Fintype.card_eq_sum_ones, sum_evenQuot_eq (by rw [hd]; decide) hi₀, Finset.sum_filter]
  have := Finset.sum_powerset_apply_card (fun n => if Even n then (1 : ℕ) else 0)
    (x := d.erase i₀)
  rw [this, h7]
  decide

theorem finrank_evenQuot {d : Finset I} (hd : d.card = 8) :
    finrank (ZMod 2) (EvenQuot d) = 6 := by
  have h := FiniteField.pow_finrank_eq_card 2 (EvenQuot d)
  rw [card_evenQuot hd, show (64 : ℕ) = 2 ^ 6 from rfl] at h
  exact Nat.pow_right_injective le_rfl h

theorem sgn_natCast (n : ℕ) : sgn (n : ZMod 2) = (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [(ZMod.natCast_eq_zero_iff_even).2 h, h.neg_one_pow]; rfl
  · rw [(ZMod.natCast_eq_one_iff_odd).2 h, h.neg_one_pow]; rfl

theorem sum_sgn_quadForm {d : Finset I} (hd : d.card = 8) :
    ∑ v : EvenQuot d, sgn (quadForm d v) = 8 := by
  obtain ⟨i₀, hi₀⟩ : d.Nonempty := Finset.card_pos.1 (by omega)
  have h4 : 4 ∣ d.card := by rw [hd]; norm_num
  have h7 : (d.erase i₀).card = 7 := by rw [Finset.card_erase_of_mem hi₀, hd]
  rw [sum_evenQuot_eq (by rw [hd]; decide) hi₀]
  rw [Finset.sum_congr rfl fun δ hδ => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at hδ
    rw [quadForm_cls h4 (hδ.1.trans (Finset.erase_subset _ _)) hδ.2, sgn_natCast]]
  rw [Finset.sum_filter]
  have := Finset.sum_powerset_apply_card (fun n => if Even n then ((-1 : ℚ) ^ (n / 2)) else 0)
    (x := d.erase i₀)
  rw [this, h7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.even_iff]
  norm_num [Nat.choose]

theorem eight_point_even_subset_quadratic_space (d : Finset I) (hd : d.card = 8) :
    let H := fourierMatrix (QuadraticMap.polarBilin (quadForm d)) 3
    let D := signMatrix (quadForm d)
    (∀ δ ε, δ ⊆ d → Even δ.card → ε ⊆ d → Even ε.card →
      quadForm d (cls d δ) = ((δ.card / 2 : ℕ) : ZMod 2) ∧
      QuadraticMap.polarBilin (quadForm d) (cls d δ) (cls d ε) = ((δ ∩ ε).card : ZMod 2)) ∧
    finrank (ZMod 2) (EvenQuot d) = 6 ∧
    (QuadraticMap.polarBilin (quadForm d)).Nondegenerate ∧
    ∑ v : EvenQuot d, sgn (quadForm d v) = 8 ∧
    (∀ δ ε, δ ⊆ d → Even δ.card → ε ⊆ d → Even ε.card →
      H (cls d δ) (cls d ε) = (-1) ^ (δ ∩ ε).card / 8 ∧
      D (cls d δ) (cls d ε) = if cls d δ = cls d ε then (-1) ^ (δ.card / 2) else 0) ∧
    H * Hᵀ = 1 ∧ H * H = 1 ∧ D * Dᵀ = 1 ∧ D * D = 1 ∧
    orderOf (H * D) = 3 ∧ Matrix.trace (H * D) = 1 ∧
    finrank ℚ (LinearMap.ker (Matrix.toLin' (H * D - 1))) = 22 := by
  intro H D
  have h4 : 4 ∣ d.card := by rw [hd]; norm_num
  have hne : d.Nonempty := Finset.card_pos.1 (by omega)
  have hb := polarBilin_quadForm_nondegenerate h4 hne
  have hdim : finrank (ZMod 2) (EvenQuot d) = 2 * 3 := finrank_evenQuot hd
  have hgauss : ∑ u, sgn (quadForm d u) = 2 ^ 3 := by rw [sum_sgn_quadForm hd]; norm_num
  obtain ⟨-, -, hHH', hDD', hHH, hDD, -, -, -, htr, hker, hord⟩ :=
    binary_quadratic_fourier_triality (quadForm d) hb hdim hgauss
  refine ⟨fun δ ε hδ hδe hε hεe =>
      ⟨quadForm_cls h4 hδ hδe, polarBilin_quadForm_cls h4 hδ hδe hε hεe⟩,
    finrank_evenQuot hd, hb, sum_sgn_quadForm hd, fun δ ε hδ hδe hε hεe => ⟨?_, ?_⟩,
    hHH', hHH, hDD', hDD, hord (by norm_num), htr, ?_⟩
  · simp only [H, fourierMatrix]
    rw [polarBilin_quadForm_cls h4 hδ hδe hε hεe, sgn_natCast]
    ring
  · simp only [D, signMatrix, Matrix.diagonal_apply]
    rw [quadForm_cls h4 hδ hδe, sgn_natCast]
  · rw [hker]
    norm_num

end CFSG.Monster.Octad

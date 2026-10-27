module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open43
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Certificate8006
import CFSG.RankThree.PartOne.Census3.Interface
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open TauCeti hiding wordProd
open CFSG.Sporadic.Bridge

namespace TripleCoverSuz

open Native

attribute [local irreducible] gen0 gen1 gen2 gen3 gen4 gen5 gen6

theorem ent_eq (P i : ℕ) : ent P i = P / 2 ^ (11 * i) % 2048 := by
  show (P >>> (11 * i)) &&& (2 ^ 11 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ent_lt (P i : ℕ) : ent P i < 2048 := by
  rw [ent_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem lor_shiftLeft_eq (a v : ℕ) (hv : v < 2048) :
    Nat.lor (Nat.shiftLeft a 11) v = a * 2048 + v := by
  show a <<< 11 ||| v = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 11) (lt_of_lt_of_eq hv (by norm_num)) a,
    Nat.shiftLeft_eq]

theorem ent_mul_add_zero (a v : ℕ) (hv : v < 2048) : ent (a * 2048 + v) 0 = v := by
  rw [ent_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

theorem ent_mul_add_succ (a v m : ℕ) (hv : v < 2048) : ent (a * 2048 + v) (m + 1) = ent a m := by
  rw [ent_eq, ent_eq, show 11 * (m + 1) = 11 + 11 * m by ring, Nat.pow_add,
    ← Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 11 = 2048 by norm_num,
    show (a * 2048 + v) / 2048 = a by omega]

theorem ent_pack {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2048) (acc i : ℕ) :
    ent (pack f n acc) i = if i < n then f i else ent acc (i - n) := by
  induction n generalizing acc with
  | zero =>
    show ent acc i = _
    rw [ite_eq_right (Nat.not_lt_zero i), Nat.sub_zero]
  | succ n ih =>
    have h1 : pack f (n + 1) acc = pack f n (Nat.lor (Nat.shiftLeft acc 11) (f n)) := rfl
    rw [h1, ih (fun k hk => hf k (by omega)), lor_shiftLeft_eq _ _ (hf n (by omega))]
    by_cases hi : i < n
    · rw [ite_eq_left hi, ite_eq_left (by omega)]
    · rw [ite_eq_right hi]
      by_cases hin : i = n
      · subst hin
        rw [Nat.sub_self, ent_mul_add_zero _ _ (hf _ (by omega)), ite_eq_left (by omega)]
      · rw [show i - n = i - (n + 1) + 1 by omega, ent_mul_add_succ _ _ _ (hf n (by omega)),
          ite_eq_right (by omega)]

theorem ent_comp (a b : ℕ) {i : ℕ} (hi : i < 1782) : ent (comp a b) i = ent a (ent b i) := by
  have h := ent_pack (f := fun k => ent a (ent b k)) (n := 1782) (fun k _ => ent_lt _ _) 0 i
  rwa [ite_eq_left hi] at h

theorem ent_pid {i : ℕ} (hi : i < 1782) : ent pid i = i := by
  have h := ent_pack (f := fun k => k) (n := 1782) (fun k hk => by omega) 0 i
  rwa [ite_eq_left hi] at h

theorem allBelow_spec {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) :
    ∀ k < n, p k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have h' : (p n && allBelow n p) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h'.2 k hk
    · exact h'.1

@[expose] def RepN (P : ℕ) (g : Equiv.Perm (Fin 1782)) : Prop :=
  ∀ x : Fin 1782, ent P x = g x

theorem RepN.comp {a b : ℕ} {g h : Equiv.Perm (Fin 1782)} (ha : RepN a g) (hb : RepN b h) :
    RepN (Native.comp a b) (g * h) := fun x => by
  rw [ent_comp a b x.2, hb x, ha (h x), Equiv.Perm.mul_apply]

theorem repN_pid : RepN pid 1 := fun x => by
  rw [ent_pid x.2]
  rfl

theorem RepN.eq {P Q : ℕ} {g h : Equiv.Perm (Fin 1782)} (hP : RepN P g) (hQ : RepN Q h)
    (e : P = Q) : g = h :=
  Equiv.ext fun x => Fin.ext (by rw [← hP x, ← hQ x, e])

theorem RepN.sq {P : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : RepN P g) : RepN (sqN P) (g * g) :=
  hP.comp hP

theorem RepN.pw3 {P : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : RepN P g) {e : ℕ} (he : e < 3) :
    RepN (pw3 P e) (g ^ e) := by
  interval_cases e
  · rw [pow_zero]
    exact repN_pid
  · rw [pow_one]
    exact hP
  · rw [pow_two]
    exact hP.sq

@[irreducible] noncomputable def involOf (P : ℕ) : Equiv.Perm (Fin 1782) :=
  @dite _ (∀ x : Fin 1782, ent P x < 1782 ∧ ent P (ent P x) = x) (Classical.propDecidable _)
    (fun h =>
      { toFun := fun x => ⟨ent P x, (h x).1⟩
        invFun := fun x => ⟨ent P x, (h x).1⟩
        left_inv := fun x => Fin.ext (h x).2
        right_inv := fun x => Fin.ext (h x).2 })
    (fun _ => 1)

theorem repN_involOf {P : ℕ} (h : ∀ x : Fin 1782, ent P x < 1782 ∧ ent P (ent P x) = x) :
    RepN P (involOf P) := fun x => by
  rw [involOf, @dite_eq_left_of_eq_true _ _ (Classical.propDecidable _) _ _ (eq_true h)]
  rfl

noncomputable def gpl (i : ℕ) : Equiv.Perm (Fin 1782) := involOf (gen i)

theorem gen_of_le {i : ℕ} (hi : 7 ≤ i) : gen i = gen 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 7 := ⟨i - 7, by omega⟩
  rfl

noncomputable def suzX : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure (Set.range gpl)

noncomputable def gplX (i : ℕ) : suzX := ⟨gpl i, Subgroup.subset_closure ⟨i, rfl⟩⟩

theorem gplX_of_le {i : ℕ} (hi : 7 ≤ i) : gplX i = gplX 0 := by
  have e : gpl i = gpl 0 := by
    unfold gpl
    rw [gen_of_le hi]
  exact Subtype.ext e

theorem coe_wordProd_gplX (w : List (ℕ × Bool)) :
    ((wordProd gplX w : suzX) : Equiv.Perm (Fin 1782)) = wordProd gpl w :=
  coe_wordProd gplX w

private theorem presentation_eq : SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl

theorem relatorLetters_eq :
    Sporadic.suzPresentation.relatorLetters = CFSG.Sporadic.Bridge.SuzGPL.Native.rels := by
  rw [Sporadic.suzPresentation_relatorLetters]
  rfl

theorem generatorCount_eq : SporadicName.Suz.presentation.generatorCount = 7 := by
  rw [presentation_eq]
  simp [GroupPresentation.generatorCount]

theorem allRels_spec {vs : List (List (ℕ × Bool))} (h : allRels vs = true) :
    ∀ v ∈ vs, wordN v = pid := by
  induction vs with
  | nil => intro v hv; cases hv
  | cons u vs ih =>
    have h' : (Nat.beq (wordN u) pid && allRels vs) = true := h
    rw [Bool.and_eq_true] at h'
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Nat.eq_of_beq_eq_true h'.1
    · exact ih h'.2 v hv

noncomputable def tX : suzX := gplX 0

noncomputable def y1X : suzX := wordProd gplX wordY1

noncomputable def y2X : suzX := wordProd gplX wordY2

noncomputable def y3X : suzX := wordProd gplX wordY3

noncomputable def n1X : suzX := wordProd gplX wordN1

noncomputable def n2X : suzX := wordProd gplX wordN2

noncomputable def n3X : suzX := wordProd gplX wordN3

noncomputable def suzE : Subgroup suzX := Subgroup.closure {y1X, y2X, y3X}

theorem eq_of_repN {P Q : ℕ} {x y : suzX} (hx : RepN P (x : Equiv.Perm (Fin 1782)))
    (hy : RepN Q (y : Equiv.Perm (Fin 1782))) (e : P = Q) : x = y :=
  Subtype.ext (hx.eq hy e)

theorem RepN.compX {a b : ℕ} {x y : suzX} (ha : RepN a (x : Equiv.Perm (Fin 1782)))
    (hb : RepN b (y : Equiv.Perm (Fin 1782))) :
    RepN (Native.comp a b) ((x * y : suzX) : Equiv.Perm (Fin 1782)) :=
  ha.comp hb

theorem RepN.sqX {a : ℕ} {x : suzX} (ha : RepN a (x : Equiv.Perm (Fin 1782))) :
    RepN (sqN a) ((x * x : suzX) : Equiv.Perm (Fin 1782)) :=
  ha.compX ha

theorem repN_oneX : RepN pid ((1 : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_pid

theorem pow_three_of_comp {a : ℕ} {y : suzX} (ha : RepN a (y : Equiv.Perm (Fin 1782)))
    (h : comp a (sqN a) = pid) : y ^ 3 = 1 := by
  rw [pow_three]
  exact eq_of_repN (ha.compX ha.sqX) repN_oneX h

theorem mul_comm_of_comp {a b : ℕ} {x y : suzX} (ha : RepN a (x : Equiv.Perm (Fin 1782)))
    (hb : RepN b (y : Equiv.Perm (Fin 1782))) (h : comp a b = comp b a) : x * y = y * x :=
  eq_of_repN (ha.compX hb) (hb.compX ha) h

theorem conj_eq_inv_of_comp {a b : ℕ} {n y : suzX} (ha : RepN a (n : Equiv.Perm (Fin 1782)))
    (hb : RepN b (y : Equiv.Perm (Fin 1782))) (h : comp a b = comp (sqN b) a) (hy : y ^ 3 = 1) :
    n * y * n⁻¹ = y⁻¹ := by
  have e : n * y = y * y * n := eq_of_repN (ha.compX hb) (hb.sqX.compX ha) h
  rw [e, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, ← pow_three', hy]

end TripleCoverSuz

section Certified

namespace TripleCoverSuz

open Native

attribute [local irreducible] gen0 gen1 gen2 gen3 gen4 gen5 gen6

theorem suz_gen_check : genOK = true :=
  Certificates.certificate8006.1

theorem gen_valid (i : ℕ) :
    (∀ x : Fin 1782, ent (gen i) x < 1782) ∧ comp (gen i) (gen i) = pid := by
  have h := suz_gen_check
  have h7 : allBelow 7 (fun i => allBelow 1782 (fun k => Nat.ble (ent (gen i) k) 1781) &&
      Nat.beq (comp (gen i) (gen i)) pid) = true := by
    have h' : (allBelow 7 (fun i => allBelow 1782 (fun k => Nat.ble (ent (gen i) k) 1781) &&
        Nat.beq (comp (gen i) (gen i)) pid) && !(Nat.beq (ent (gen 0) 0) 0)) = true := h
    rw [Bool.and_eq_true] at h'
    exact h'.1
  have key : ∀ j < 7,
      (∀ x : Fin 1782, ent (gen j) x < 1782) ∧ comp (gen j) (gen j) = pid := fun j hj => by
    have hj' := allBelow_spec h7 j hj
    rw [Bool.and_eq_true] at hj'
    refine ⟨fun x => ?_, Nat.eq_of_beq_eq_true hj'.2⟩
    have := allBelow_spec hj'.1 x x.2
    exact Nat.lt_succ_of_le (Nat.le_of_ble_eq_true this)
  by_cases hi : i < 7
  · exact key i hi
  · rw [gen_of_le (by omega)]
    exact key 0 (by norm_num)

theorem repN_gen (i : ℕ) : RepN (gen i) (gpl i) := by
  refine repN_involOf fun x => ⟨(gen_valid i).1 x, ?_⟩
  have h := ent_comp (gen i) (gen i) x.2
  rw [(gen_valid i).2, ent_pid x.2] at h
  exact h.symm

theorem gpl_mul_self (i : ℕ) : gpl i * gpl i = 1 :=
  ((repN_gen i).comp (repN_gen i)).eq repN_pid (gen_valid i).2

theorem gpl_inv (i : ℕ) : (gpl i)⁻¹ = gpl i :=
  inv_eq_of_mul_eq_one_right (gpl_mul_self i)

theorem gpl_zero_apply_ne : gpl 0 0 ≠ 0 := by
  have h' : (allBelow 7 (fun i => allBelow 1782 (fun k => Nat.ble (ent (gen i) k) 1781) &&
      Nat.beq (comp (gen i) (gen i)) pid) && !(Nat.beq (ent (gen 0) 0) 0)) = true :=
    suz_gen_check
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h'
  intro e
  have h0 : ent (gen 0) 0 = 0 := by
    have := repN_gen 0 0
    rw [e] at this
    exact this
  rw [h0] at h'
  exact absurd h'.2 (by decide)

theorem repN_wordN (w : List (ℕ × Bool)) :
    RepN (wordN w) (wordProd gpl w) := by
  induction w with
  | nil => exact repN_pid
  | cons l w ih =>
    have hl : (if l.2 then gpl l.1 else (gpl l.1)⁻¹) = gpl l.1 := by
      split <;> simp [gpl_inv]
    cases w with
    | nil =>
      have e : wordProd gpl [l] = gpl l.1 := by
        simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, hl]
      rw [e]
      exact repN_gen l.1
    | cons l' w =>
      have e : wordProd gpl (l :: l' :: w) = gpl l.1 * wordProd gpl (l' :: w) := by
        simp only [wordProd, List.map_cons, List.prod_cons, hl]
      rw [e]
      exact (repN_gen l.1).comp ih

theorem suz_rels_check : relsOK = true :=
  Certificates.certificate8006.2.1

theorem relators_eval :
    ∀ v ∈ SporadicName.Suz.presentation.relatorLetters, wordProd gplX v = 1 := by
  rw [presentation_eq, relatorLetters_eq]
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd_gplX, OneMemClass.coe_one]
  exact (repN_wordN v).eq repN_pid (allRels_spec suz_rels_check v hv)

noncomputable def toX : SporadicName.Suz.Group →* suzX :=
  presHom SporadicName.Suz.presentation gplX relators_eval

theorem toX_presGen {i : ℕ} (hi : i < 7) :
    toX (presGen SporadicName.Suz.presentation i) = gplX i :=
  presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hi)

theorem gplX_mem_range (i : ℕ) : gplX i ∈ toX.range := by
  by_cases h7 : i < 7
  · exact ⟨_, toX_presGen h7⟩
  · rw [gplX_of_le (by omega)]
    exact ⟨_, toX_presGen (by norm_num)⟩

theorem toX_surjective : Function.Surjective toX := by
  intro x
  suffices h : ∀ (g : Equiv.Perm (Fin 1782)) (hg : g ∈ Subgroup.closure (Set.range gpl)),
      (⟨g, hg⟩ : suzX) ∈ toX.range from h x x.2
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact gplX_mem_range i
  | one => exact toX.range.one_mem
  | mul g h _ _ ihg ihh => exact toX.range.mul_mem ihg ihh
  | inv g _ ih => exact toX.range.inv_mem ih

theorem gplX_zero_ne_one : gplX 0 ≠ 1 := fun h =>
  gpl_zero_apply_ne (by rw [show gpl 0 = 1 from congrArg Subtype.val h]; rfl)

theorem toX_injective [IsSimpleGroup SporadicName.Suz.Group] :
    Function.Injective toX := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal toX.ker with h | h
  · exact h
  · exfalso
    apply gplX_zero_ne_one
    rw [← toX_presGen (by norm_num : 0 < 7)]
    have hk : presGen SporadicName.Suz.presentation 0 ∈ toX.ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.1 hk

theorem nonempty_mulEquiv_suzX
    [IsSimpleGroup SporadicName.Suz.Group] : Nonempty (SporadicName.Suz.Group ≃* suzX) :=
  ⟨MulEquiv.ofBijective toX ⟨toX_injective, toX_surjective⟩⟩

theorem suz_config_check : configOK = true :=
  Certificates.certificate8006.2.2

theorem config_facts :
    comp nY1 (sqN nY1) = pid ∧ comp nY2 (sqN nY2) = pid ∧ comp nY3 (sqN nY3) = pid ∧
      comp nY1 nY2 = comp nY2 nY1 ∧ comp nY1 nY3 = comp nY3 nY1 ∧
      comp nY2 nY3 = comp nY3 nY2 ∧
      comp nT nY1 = comp nY1 nT ∧ comp nT nY2 = comp nY2 nT ∧ comp nT nY3 = comp nY3 nT ∧
      comp nN1 nY1 = comp (sqN nY1) nN1 ∧ comp nN2 nY2 = comp (sqN nY2) nN2 ∧
      comp nN3 nY3 = comp (sqN nY3) nN3 ∧
      comp nN2 nY1 = comp nY1 nN2 ∧ comp nN3 nY1 = comp nY1 nN3 ∧
      comp nN3 nY2 = comp nY2 nN3 ∧ orbitOK = true := by
  have h := suz_config_check
  simp only [configOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9,
    Nat.eq_of_beq_eq_true h10, Nat.eq_of_beq_eq_true h11, Nat.eq_of_beq_eq_true h12,
    Nat.eq_of_beq_eq_true h13, Nat.eq_of_beq_eq_true h14, Nat.eq_of_beq_eq_true h15, h16⟩

theorem repN_wordX (w : List (ℕ × Bool)) :
    RepN (wordN w) ((wordProd gplX w : suzX) : Equiv.Perm (Fin 1782)) := by
  rw [coe_wordProd_gplX]
  exact repN_wordN w

theorem repN_y1 : RepN nY1 ((y1X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordY1

theorem repN_y2 : RepN nY2 ((y2X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordY2

theorem repN_y3 : RepN nY3 ((y3X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordY3

theorem repN_n1 : RepN nN1 ((n1X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordN1

theorem repN_n2 : RepN nN2 ((n2X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordN2

theorem repN_n3 : RepN nN3 ((n3X : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_wordX wordN3

theorem repN_tX :
    RepN nT ((tX : suzX) : Equiv.Perm (Fin 1782)) :=
  repN_gen 0

theorem y1X_pow : y1X ^ 3 = 1 :=
  pow_three_of_comp repN_y1 config_facts.1

theorem y2X_pow : y2X ^ 3 = 1 :=
  pow_three_of_comp repN_y2 config_facts.2.1

theorem y3X_pow : y3X ^ 3 = 1 :=
  pow_three_of_comp repN_y3 config_facts.2.2.1

theorem y12_comm : y1X * y2X = y2X * y1X :=
  mul_comm_of_comp repN_y1 repN_y2 config_facts.2.2.2.1

theorem y13_comm : y1X * y3X = y3X * y1X :=
  mul_comm_of_comp repN_y1 repN_y3 config_facts.2.2.2.2.1

theorem y23_comm : y2X * y3X = y3X * y2X :=
  mul_comm_of_comp repN_y2 repN_y3 config_facts.2.2.2.2.2.1

theorem t1_comm : tX * y1X = y1X * tX :=
  mul_comm_of_comp repN_tX repN_y1 config_facts.2.2.2.2.2.2.1

theorem t2_comm : tX * y2X = y2X * tX :=
  mul_comm_of_comp repN_tX repN_y2 config_facts.2.2.2.2.2.2.2.1

theorem t3_comm : tX * y3X = y3X * tX :=
  mul_comm_of_comp repN_tX repN_y3 config_facts.2.2.2.2.2.2.2.2.1

theorem n1_conj : n1X * y1X * n1X⁻¹ = y1X⁻¹ :=
  conj_eq_inv_of_comp repN_n1 repN_y1
    config_facts.2.2.2.2.2.2.2.2.2.1 y1X_pow

theorem n2_conj : n2X * y2X * n2X⁻¹ = y2X⁻¹ :=
  conj_eq_inv_of_comp repN_n2 repN_y2
    config_facts.2.2.2.2.2.2.2.2.2.2.1 y2X_pow

theorem n3_conj : n3X * y3X * n3X⁻¹ = y3X⁻¹ :=
  conj_eq_inv_of_comp repN_n3 repN_y3
    config_facts.2.2.2.2.2.2.2.2.2.2.2.1 y3X_pow

theorem n2_y1 : n2X * y1X * n2X⁻¹ = y1X := by
  rw [mul_comm_of_comp repN_n2 repN_y1
    config_facts.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_inv_cancel_right]

theorem n3_y1 : n3X * y1X * n3X⁻¹ = y1X := by
  rw [mul_comm_of_comp repN_n3 repN_y1
    config_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_inv_cancel_right]

theorem n3_y2 : n3X * y2X * n3X⁻¹ = y2X := by
  rw [mul_comm_of_comp repN_n3 repN_y2
    config_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_inv_cancel_right]

theorem tX_sq : tX ^ 2 = 1 := by
  rw [pow_two]
  exact Subtype.ext (gpl_mul_self 0)

theorem tX_ne_one : tX ≠ 1 :=
  gplX_zero_ne_one

theorem commute_tX {e : suzX} (he : e ∈ suzE) : Commute tX e := by
  have hle : suzE ≤ Subgroup.centralizer {tX} := by
    rw [suzE, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact t1_comm.symm
    · exact t2_comm.symm
    · exact t3_comm.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm

theorem orbitPt_eq {u : ℕ} (hu : u < 27) :
    orbitPt u = ((((y1X ^ (u / 9) * y2X ^ (u / 3 % 3) * y3X ^ (u % 3) : suzX) :
      Equiv.Perm (Fin 1782)) (0 : Fin 1782) : Fin 1782) : ℕ) := by
  have h1 := repN_y1.pw3 (e := u / 9) (by omega)
  have h2 := repN_y2.pw3 (e := u / 3 % 3) (by omega)
  have h3 := repN_y3.pw3 (e := u % 3) (by omega)
  show ent (pw3 nY1 (u / 9)) (ent (pw3 nY2 (u / 3 % 3)) (ent (pw3 nY3 (u % 3)) 0)) = _
  have e0 : ent (pw3 nY3 (u % 3)) 0 = (((y3X : Equiv.Perm (Fin 1782)) ^ (u % 3)) 0 : ℕ) :=
    h3 0
  rw [e0, h2, h1]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Equiv.Perm.mul_apply]

theorem card_suzE : 3 ^ 3 ≤ Nat.card suzE := by
  have hO := allBelow_spec config_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let f : Fin 27 → suzE := fun u =>
    ⟨y1X ^ ((u : ℕ) / 9) * y2X ^ ((u : ℕ) / 3 % 3) * y3X ^ ((u : ℕ) % 3),
      suzE.mul_mem (suzE.mul_mem (suzE.pow_mem (Subgroup.subset_closure (by simp)) _)
        (suzE.pow_mem (Subgroup.subset_closure (by simp)) _))
        (suzE.pow_mem (Subgroup.subset_closure (by simp)) _)⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hval : y1X ^ ((u : ℕ) / 9) * y2X ^ ((u : ℕ) / 3 % 3) * y3X ^ ((u : ℕ) % 3) =
        y1X ^ ((v : ℕ) / 9) * y2X ^ ((v : ℕ) / 3 % 3) * y3X ^ ((v : ℕ) % 3) :=
      congrArg Subtype.val huv
    have e : orbitPt u = orbitPt v := by
      rw [orbitPt_eq u.2, orbitPt_eq v.2, hval]
    have h : (Nat.beq (u : ℕ) v || !Nat.beq (orbitPt u) (orbitPt v)) = true :=
      allBelow_spec (hO u u.2) v v.2
    rw [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact Fin.ext (Nat.eq_of_beq_eq_true h)
    · rw [e, Nat.beq_refl] at h
      exact absurd h (by decide)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  norm_num
  exact this

section Lift

variable {G : Type} [Group G] {φ : G →* suzX}

theorem commute_lift_gens (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (x y : G) (hx : φ x ∈ ({y1X, y2X, y3X} : Set suzX))
    (hy : φ y ∈ ({y1X, y2X, y3X} : Set suzX)) (hxy : φ x ≠ φ y) : x * y = y * x := by
  have h3 : Odd 3 := by decide
  have key : ∀ {u v n : suzX} {x' y' : G}, φ x' = u → φ y' = v → u * v = v * u → v ^ 3 = 1 →
      n * u * n⁻¹ = u → n * v * n⁻¹ = v⁻¹ → x' * y' = y' * x' := by
    intro u v n x' y' hu hv huv hv3 hnu hnv
    subst hu hv
    exact TripleCoverLift.commute_of_conj hφ hker h3 huv hv3 (Or.inl ⟨hnu, hnv⟩)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exact absurd (hx.trans hy.symm) hxy
  · exact key hx hy y12_comm y2X_pow n2_y1 n2_conj
  · exact key hx hy y13_comm y3X_pow n3_y1 n3_conj
  · exact (key hy hx y12_comm y2X_pow n2_y1 n2_conj).symm
  · exact absurd (hx.trans hy.symm) hxy
  · exact key hx hy y23_comm y3X_pow n3_y2 n3_conj
  · exact (key hy hx y13_comm y3X_pow n3_y1 n3_conj).symm
  · exact (key hy hx y23_comm y3X_pow n3_y2 n3_conj).symm
  · exact absurd (hx.trans hy.symm) hxy

theorem commute_of_mem_suzE (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {x y : G} (hx : φ x ∈ suzE) (hy : φ y ∈ suzE) : x * y = y * x :=
  TripleCoverLift.commute_of_mem_closure hφ hker (commute_lift_gens hφ hker) hx hy

theorem exists_lift_of_mem_suzE (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {e : suzX} (he : e ∈ suzE) : ∃ y : G, φ y = e ∧ y ^ 3 = 1 := by
  have h3 : Odd 3 := by decide
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure (E := suzE)
    (fun x hx y hy => commute_of_mem_suzE hφ hker hx hy) Subgroup.subset_closure ?_ he
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker h3 y1X_pow n1_conj
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker h3 y2X_pow n2_conj
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker h3 y3X_pow n3_conj

theorem four_le_twoLocalOddRank_of_cover [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (h3 : 3 ∣ Nat.card φ.ker) :
    4 ≤ CFSG.twoLocalOddRank G := by
  have h := TripleCoverLift.succ_le_localRank_of_lift hφ hker Nat.prime_three (by norm_num) h3
    (E := suzE) (fun x hx y hy => commute_of_mem_suzE hφ hker hx hy)
    (fun e he => exists_lift_of_mem_suzE hφ hker he) tX_ne_one tX_sq
    (fun e he => commute_tX he) (r := 3) card_suzE
  exact CFSG.RankThree.PartOne.Census3.four_le_twoLocalOddRank_of_localRank Nat.prime_three
    (by norm_num) h

end Lift

end TripleCoverSuz

open TripleCoverSuz in
theorem tripleCoverSuzRankFour : TripleCoverSuzRankFour := by
  intro G _ _ hG
  obtain ⟨hq, h3, ⟨e⟩⟩ := hG
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have : IsSimpleGroup SporadicName.Suz.Group := e.symm.isSimpleGroup
  obtain ⟨eX⟩ := nonempty_mulEquiv_suzX
  let φ : G →* suzX := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center G := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact four_le_twoLocalOddRank_of_cover hφ hker.le (hker ▸ h3)

end Certified

end CFSG.RankThree.PartTwo.Sec4.Census

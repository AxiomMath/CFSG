module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA9
import CFSG.RankThree.PartTwo.Sec4.Item413A9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv Equiv.Perm Item434AltPerm Res423Two

@[expose] def lv : Fin 4 → (Fin 3 → ZMod 3) :=
  ![![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![1, 2, 1]]

@[expose] def lineIdx (x : Perm (Fin 9)) : Fin 4 :=
  if x = vecPerm 9 (lv 1) ∨ x = vecPerm 9 (lv 1) ^ 2 then 1 else
  if x = vecPerm 9 (lv 2) ∨ x = vecPerm 9 (lv 2) ^ 2 then 2 else
  if x = vecPerm 9 (lv 3) ∨ x = vecPerm 9 (lv 3) ^ 2 then 3 else 0

@[expose] def t6 : Fin 6 → Perm (Fin 9) := ![c1 9, c1 9 ^ 2, c2 9, c2 9 ^ 2, c3 9, c3 9 ^ 2]

@[expose] def tInv9 : Perm (Fin 9) := swap 1 2 * swap 4 5 * swap 7 8

@[expose] def ha9 : Perm (Fin 9) := swap 0 3 * swap 1 4 * swap 2 5 * swap 7 8

@[expose] def hb9 : Perm (Fin 9) := ha9 * tt 9

theorem lv_spec : ∀ k : Fin 4, lineIdx (vecPerm 9 (lv k)) = k ∧
    lineIdx (vecPerm 9 (lv k) ^ 2) = k ∧ (vecPerm 9 (lv k) ^ 2) ^ 2 = vecPerm 9 (lv k) ∧
    (vecPerm 9 (lv k)).support.card = 9 ∧
    vecPerm 9 (lv k) = c1 9 * c2 9 ^ (lv k 1).val * c3 9 ^ (lv k 2).val := by
  decide +kernel

theorem fpf_cases : ∀ v : Fin 3 → ZMod 3, (vecPerm 9 v).support.card = 9 →
    ∃ k : Fin 4, vecPerm 9 v = vecPerm 9 (lv k) ∨ vecPerm 9 v = vecPerm 9 (lv k) ^ 2 := by
  decide +kernel

theorem threeCycle_cases9 : ∀ v : Fin 3 → ZMod 3, (vecPerm 9 v).support.card = 3 →
    ∃ i : Fin 6, vecPerm 9 v = t6 i := by
  decide +kernel

theorem fixing_cases : ∀ i j k : Fin 6,
    (∀ l : Fin 4, lineIdx (t6 i * t6 j ^ (lv l 1).val * t6 k ^ (lv l 2).val) = l) →
    (t6 i = c1 9 ∧ t6 j = c2 9 ∧ t6 k = c3 9) ∨
      (t6 i = (c1 9)⁻¹ ∧ t6 j = (c2 9)⁻¹ ∧ t6 k = (c3 9)⁻¹) := by
  decide +kernel

theorem gens_spec : (c1 9).support.card = 3 ∧ (c2 9).support.card = 3 ∧
    (c3 9).support.card = 3 ∧ sign tInv9 = -1 ∧
    tInv9 * (c1 9)⁻¹ * tInv9⁻¹ = c1 9 ∧ tInv9 * (c2 9)⁻¹ * tInv9⁻¹ = c2 9 ∧
    tInv9 * (c3 9)⁻¹ * tInv9⁻¹ = c3 9 ∧
    sign ha9 = 1 ∧ ha9 * c1 9 * ha9⁻¹ = c2 9 ∧ ha9 * c2 9 * ha9⁻¹ = c1 9 ∧
    ha9 * c3 9 * ha9⁻¹ = c3 9 ^ 2 ∧
    sign hb9 = 1 ∧ hb9 * c1 9 * hb9⁻¹ = c1 9 ∧ hb9 * c2 9 * hb9⁻¹ = c3 9 ^ 2 ∧
    hb9 * c3 9 * hb9⁻¹ = c2 9 ∧
    (∀ k : Fin 4, lineIdx (ha9 * vecPerm 9 (lv k) * ha9⁻¹) = swap (0 : Fin 4) 1 k) ∧
    (∀ k : Fin 4, lineIdx (hb9 * vecPerm 9 (lv k) * hb9⁻¹) = finRotate 4 k) := by
  decide +kernel

theorem points_spec :
    (∀ p : Fin 9, c2 9 p = p → c3 9 p = p → ∃ a : ZMod 3, p = (c1 9 ^ a.val) 0) ∧
    (∀ p : Fin 9, c1 9 p = p → c3 9 p = p → ∃ a : ZMod 3, p = (c2 9 ^ a.val) 3) ∧
    (∀ p : Fin 9, c1 9 p = p → c2 9 p = p → ∃ a : ZMod 3, p = (c3 9 ^ a.val) 6) ∧
    (∀ p : Fin 9, ∃ a : ℕ, p = (c1 9 ^ a) 0 ∨ p = (c2 9 ^ a) 3 ∨ p = (c3 9 ^ a) 6) ∧
    c2 9 0 = 0 ∧ c3 9 0 = 0 ∧ c1 9 3 = 3 ∧ c3 9 3 = 3 ∧ c1 9 6 = 6 ∧ c2 9 6 = 6 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun p => ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have h : ∀ p : Fin 9, ∃ a : Fin 3, p = (c1 9 ^ (a : ℕ)) 0 ∨ p = (c2 9 ^ (a : ℕ)) 3 ∨
      p = (c3 9 ^ (a : ℕ)) 6 := by
    decide +kernel
  obtain ⟨a, ha⟩ := h p
  exact ⟨a, ha⟩

theorem vecPerm_base : ∀ u : Fin 3 → ZMod 3, vecPerm 9 u 0 = (c1 9 ^ (u 0).val) 0 ∧
    vecPerm 9 u 3 = (c2 9 ^ (u 1).val) 3 ∧ vecPerm 9 u 6 = (c3 9 ^ (u 2).val) 6 := by
  decide +kernel

theorem c1_mem_A0 : c1 9 ∈ A0 9 :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem c2_mem_A0 : c2 9 ∈ A0 9 :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem c3_mem_A0 : c3 9 ∈ A0 9 :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem apply_pow_of_commute {y c : Perm (Fin 9)} (h : y * c = c * y) (a : ℕ) (x : Fin 9) :
    y ((c ^ a) x) = (c ^ a) (y x) := by
  have h' : y * c ^ a = c ^ a * y := ((Commute.pow_right (show Commute y c from h) a)).eq
  rw [← Perm.mul_apply, h', Perm.mul_apply]

theorem sign_eq_one_of_commute {y : Perm (Fin 9)} (h1 : y * c1 9 = c1 9 * y)
    (h2 : y * c2 9 = c2 9 * y) (h3 : y * c3 9 = c3 9 * y) : sign y = 1 := by
  obtain ⟨hp1, hp2, hp3, hcov, h20, h30, h13, h33, h16, h26⟩ := points_spec
  have hA := wFacts_nine.toA0Facts
  have hfix : ∀ {c : Perm (Fin 9)} {p : Fin 9}, y * c = c * y → c p = p → c (y p) = y p := by
    intro c p hc hp
    rw [← Perm.mul_apply, ← hc, Perm.mul_apply, hp]
  obtain ⟨a, ha⟩ := hp1 _ (hfix h2 h20) (hfix h3 h30)
  obtain ⟨b, hb⟩ := hp2 _ (hfix h1 h13) (hfix h3 h33)
  obtain ⟨c, hc⟩ := hp3 _ (hfix h1 h16) (hfix h2 h26)
  set u : Fin 3 → ZMod 3 := ![a, b, c] with hu
  obtain ⟨hu0, hu3, hu6⟩ := vecPerm_base u
  have hvu : vecPerm 9 u ∈ A0 9 := vecPerm_mem_A0 hA u
  have hc1 := commute_of_mem_A0 hA hvu c1_mem_A0
  have hc2 := commute_of_mem_A0 hA hvu c2_mem_A0
  have hc3 := commute_of_mem_A0 hA hvu c3_mem_A0
  have hyu : y = vecPerm 9 u := by
    ext p
    obtain ⟨k, hk | hk | hk⟩ := hcov p <;> rw [hk]
    · rw [apply_pow_of_commute h1, apply_pow_of_commute hc1, hu0, ha]
      rfl
    · rw [apply_pow_of_commute h2, apply_pow_of_commute hc2, hu3, hb]
      rfl
    · rw [apply_pow_of_commute h3, apply_pow_of_commute hc3, hu6, hc]
      rfl
  rw [hyu]
  exact mem_alternatingGroup.mp (A0_nine_le hvu)

theorem mul_comm_of_conj_eq {y c : Perm (Fin 9)} (h : y * c * y⁻¹ = c) : y * c = c * y := by
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [h]

@[expose] def A0A : Subgroup (alternatingGroup (Fin 9)) :=
  (A0 9).subgroupOf (alternatingGroup (Fin 9))

@[expose] def vtxA (k : Fin 4) : A0A :=
  ⟨⟨vecPerm 9 (lv k), A0_nine_le (vecPerm_mem_A0 wFacts_nine.toA0Facts _)⟩,
    Subgroup.mem_subgroupOf.mpr (vecPerm_mem_A0 wFacts_nine.toA0Facts _)⟩

theorem nmh9_apply (h : Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9)))) (x : A0A) :
    (((A0A.normalizerMonoidHom h x : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)) * ((x : alternatingGroup (Fin 9)) :
        Perm (Fin 9)) * ((h : alternatingGroup (Fin 9)) : Perm (Fin 9))⁻¹ :=
  rfl

theorem mem_normalizer_A0A {g : alternatingGroup (Fin 9)}
    (h1 : (g : Perm (Fin 9)) * c1 9 * (g : Perm (Fin 9))⁻¹ ∈ A0 9)
    (h2 : (g : Perm (Fin 9)) * c2 9 * (g : Perm (Fin 9))⁻¹ ∈ A0 9)
    (h3 : (g : Perm (Fin 9)) * c3 9 * (g : Perm (Fin 9))⁻¹ ∈ A0 9) :
    g ∈ Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9))) := by
  have hle : A0 9 ≤ (A0 9).comap (MulAut.conj (g : Perm (Fin 9))).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    · exact h1
    · exact h2
    · exact h3
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' : (x : Perm (Fin 9)) ∈ A0 9 := Subgroup.mem_subgroupOf.mp hx
  exact Subgroup.mem_subgroupOf.mpr (hle hx')

theorem conj_mem_A0 {g : alternatingGroup (Fin 9)}
    (hN : g ∈ Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9)))) {x : Perm (Fin 9)}
    (hx : x ∈ A0 9) : (g : Perm (Fin 9)) * x * (g : Perm (Fin 9))⁻¹ ∈ A0 9 := by
  have hxA : (⟨x, A0_nine_le hx⟩ : alternatingGroup (Fin 9)) ∈ A0A :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hN _).mp hxA)

theorem conj_vtx {g : alternatingGroup (Fin 9)}
    (hN : g ∈ Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9)))) (k : Fin 4) :
    ∃ j : Fin 4, (g : Perm (Fin 9)) * vecPerm 9 (lv k) * (g : Perm (Fin 9))⁻¹ = vecPerm 9 (lv j) ∨
      (g : Perm (Fin 9)) * vecPerm 9 (lv k) * (g : Perm (Fin 9))⁻¹ = vecPerm 9 (lv j) ^ 2 := by
  obtain ⟨v, hv⟩ := (mem_A0 wFacts_nine.toA0Facts).mp
    (conj_mem_A0 hN (vecPerm_mem_A0 wFacts_nine.toA0Facts (lv k)))
  have hcard : (vecPerm 9 v).support.card = 9 := by
    rw [hv, card_support_conj]
    exact (lv_spec k).2.2.2.1
  obtain ⟨j, hj⟩ := fpf_cases v hcard
  exact ⟨j, hv ▸ hj⟩

theorem conj_three {g : alternatingGroup (Fin 9)}
    (hN : g ∈ Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9)))) {c : Perm (Fin 9)}
    (hc : c ∈ A0 9) (h3 : c.support.card = 3) :
    ∃ i : Fin 6, (g : Perm (Fin 9)) * c * (g : Perm (Fin 9))⁻¹ = t6 i := by
  obtain ⟨v, hv⟩ := (mem_A0 wFacts_nine.toA0Facts).mp (conj_mem_A0 hN hc)
  have hcard : (vecPerm 9 v).support.card = 3 := by
    rw [hv, card_support_conj]
    exact h3
  obtain ⟨i, hi⟩ := threeCycle_cases9 v hcard
  exact ⟨i, hv ▸ hi⟩

theorem autIn_vtx (φ : autIn ⊤ A0A) (k : Fin 4) :
    (φ : MulAut A0A) (vtxA k) = vtxA (lineIdx (((((φ : MulAut A0A) (vtxA k) : A0A) :
      alternatingGroup (Fin 9)) : Perm (Fin 9)))) ∨
    (φ : MulAut A0A) (vtxA k) = vtxA (lineIdx (((((φ : MulAut A0A) (vtxA k) : A0A) :
      alternatingGroup (Fin 9)) : Perm (Fin 9)))) ^ 2 := by
  obtain ⟨g, hN, -, hg⟩ := mem_autIn_iff.mp φ.2
  have h1 : (((((φ : MulAut A0A) (vtxA k) : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9))) =
      (g : Perm (Fin 9)) * vecPerm 9 (lv k) * (g : Perm (Fin 9))⁻¹ := by
    rw [← hg]
    rfl
  obtain ⟨j, hj | hj⟩ := conj_vtx hN k
  · left
    rw [h1, hj, (lv_spec j).1]
    apply Subtype.ext
    apply Subtype.ext
    rw [h1, hj]
    rfl
  · right
    rw [h1, hj, (lv_spec j).2.1]
    apply Subtype.ext
    apply Subtype.ext
    rw [h1, hj]
    rfl

theorem vtxA_lines (j : Fin 4) :
    lineIdx (((vtxA j : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = j ∧
    lineIdx (((vtxA j ^ 2 : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = j ∧
    lineIdx ((((vtxA j ^ 2) ^ 2 : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = j := by
  refine ⟨(lv_spec j).1, ?_, ?_⟩
  · change lineIdx (vecPerm 9 (lv j) ^ 2) = j
    exact (lv_spec j).2.1
  · change lineIdx ((vecPerm 9 (lv j) ^ 2) ^ 2) = j
    rw [(lv_spec j).2.2.1]
    exact (lv_spec j).1

theorem lineIdx_sq (φ : autIn ⊤ A0A) (k : Fin 4) :
    lineIdx (((((φ : MulAut A0A) (vtxA k ^ 2) : A0A) : alternatingGroup (Fin 9)) :
      Perm (Fin 9))) =
    lineIdx (((((φ : MulAut A0A) (vtxA k) : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9))) := by
  rw [map_pow]
  rcases autIn_vtx φ k with h | h
  · rw [h, (vtxA_lines _).1, (vtxA_lines _).2.1]
  · rw [h, (vtxA_lines _).2.1, (vtxA_lines _).2.2]

@[expose] noncomputable def lineAct : autIn ⊤ A0A →* Function.End (Fin 4) where
  toFun φ := fun k => lineIdx (((((φ : MulAut A0A) (vtxA k) : A0A) :
    alternatingGroup (Fin 9)) : Perm (Fin 9)))
  map_one' := by
    funext k
    exact (lv_spec k).1
  map_mul' φ ψ := by
    funext k
    change lineIdx (((((φ : MulAut A0A) ((ψ : MulAut A0A) (vtxA k)) : A0A) :
      alternatingGroup (Fin 9)) : Perm (Fin 9))) = lineIdx (((((φ : MulAut A0A) (vtxA
        (lineIdx (((((ψ : MulAut A0A) (vtxA k) : A0A) : alternatingGroup (Fin 9)) :
          Perm (Fin 9))))) : A0A) : alternatingGroup (Fin 9)) : Perm (Fin 9)))
    rcases autIn_vtx ψ k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact lineIdx_sq φ _

@[expose] noncomputable def linePerm : autIn ⊤ A0A →* Perm (Fin 4) :=
  Equiv.Perm.equivUnitsEnd.symm.toMonoidHom.comp lineAct.toHomUnits

theorem linePerm_apply (φ : autIn ⊤ A0A) (k : Fin 4) :
    linePerm φ k = lineIdx (((((φ : MulAut A0A) (vtxA k) : A0A) :
      alternatingGroup (Fin 9)) : Perm (Fin 9))) :=
  rfl

theorem nmh9_eq_one (h : Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9))))
    (h1 : ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)) * c1 9 =
      c1 9 * ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)))
    (h2 : ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)) * c2 9 =
      c2 9 * ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)))
    (h3 : ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)) * c3 9 =
      c3 9 * ((h : alternatingGroup (Fin 9)) : Perm (Fin 9))) :
    A0A.normalizerMonoidHom h = 1 := by
  set a : Perm (Fin 9) := ((h : alternatingGroup (Fin 9)) : Perm (Fin 9))
  have hle : A0 9 ≤ Subgroup.centralizer ({a} : Set (Perm (Fin 9))) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  refine MulEquiv.ext fun x => Subtype.ext (Subtype.ext ?_)
  rw [nmh9_apply]
  have hx : ((x : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ A0 9 :=
    Subgroup.mem_subgroupOf.mp x.2
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  change a * _ * a⁻¹ = _
  rw [← hc, mul_inv_cancel_right]
  rfl

theorem linePerm_injective : Function.Injective linePerm := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hfix : ∀ l : Fin 4, lineIdx (((((φ : MulAut A0A) (vtxA l) : A0A) :
      alternatingGroup (Fin 9)) : Perm (Fin 9))) = l := fun l => by
    rw [← linePerm_apply, hφ]
    rfl
  obtain ⟨g, hN, -, hg⟩ := mem_autIn_iff.mp φ.2
  obtain ⟨hs1, hs2, hs3, ht, ht1, ht2, ht3, -⟩ := gens_spec
  obtain ⟨i, hi⟩ := conj_three hN c1_mem_A0 hs1
  obtain ⟨j, hj⟩ := conj_three hN c2_mem_A0 hs2
  obtain ⟨k, hk⟩ := conj_three hN c3_mem_A0 hs3
  set g' : Perm (Fin 9) := (g : Perm (Fin 9)) with hg'
  have hline : ∀ l : Fin 4,
      lineIdx (t6 i * t6 j ^ (lv l 1).val * t6 k ^ (lv l 2).val) = l := by
    intro l
    have h1 : (((((φ : MulAut A0A) (vtxA l) : A0A) : alternatingGroup (Fin 9)) :
        Perm (Fin 9))) = g' * vecPerm 9 (lv l) * g'⁻¹ := by
      rw [← hg]
      rfl
    have h2 := hfix l
    rw [h1] at h2
    have h3 : t6 i * t6 j ^ (lv l 1).val * t6 k ^ (lv l 2).val =
        g' * vecPerm 9 (lv l) * g'⁻¹ := by
      rw [(lv_spec l).2.2.2.2, ← hi, ← hj, ← hk, conj_pow, conj_pow]
      group
    rw [h3]
    exact h2
  rcases fixing_cases i j k hline with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · apply Subtype.ext
    rw [← hg]
    refine nmh9_eq_one _ (mul_comm_of_conj_eq (by rw [hi, h1])) (mul_comm_of_conj_eq
      (by rw [hj, h2])) (mul_comm_of_conj_eq (by rw [hk, h3]))
  · exfalso
    have hc : ∀ {c : Perm (Fin 9)}, g' * c * g'⁻¹ = c⁻¹ → tInv9 * c⁻¹ * tInv9⁻¹ = c →
        (tInv9 * g') * c = c * (tInv9 * g') := by
      intro c hgc htc
      refine mul_comm_of_conj_eq ?_
      rw [mul_inv_rev, show tInv9 * g' * c * (g'⁻¹ * tInv9⁻¹) =
        tInv9 * (g' * c * g'⁻¹) * tInv9⁻¹ by group, hgc, htc]
    have hs := sign_eq_one_of_commute (hc (by rw [hi, h1]) ht1) (hc (by rw [hj, h2]) ht2)
      (hc (by rw [hk, h3]) ht3)
    rw [Perm.sign_mul, ht, mem_alternatingGroup.mp g.2] at hs
    exact absurd hs (by decide)

@[expose] def haN : Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9))) :=
  ⟨⟨ha9, gens_spec.2.2.2.2.2.2.2.1⟩, mem_normalizer_A0A
    (by
      change ha9 * c1 9 * ha9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.1]
      exact c2_mem_A0)
    (by
      change ha9 * c2 9 * ha9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.2.1]
      exact c1_mem_A0)
    (by
      change ha9 * c3 9 * ha9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.2.2.1]
      exact Subgroup.pow_mem _ c3_mem_A0 2)⟩

@[expose] def hbN : Subgroup.normalizer (A0A : Set (alternatingGroup (Fin 9))) :=
  ⟨⟨hb9, gens_spec.2.2.2.2.2.2.2.2.2.2.2.1⟩, mem_normalizer_A0A
    (by
      change hb9 * c1 9 * hb9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact c1_mem_A0)
    (by
      change hb9 * c2 9 * hb9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact Subgroup.pow_mem _ c3_mem_A0 2)
    (by
      change hb9 * c3 9 * hb9⁻¹ ∈ A0 9
      rw [gens_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact c2_mem_A0)⟩

theorem linePerm_surjective : Function.Surjective linePerm := by
  have hamem : A0A.normalizerMonoidHom haN ∈ autIn ⊤ A0A :=
    mem_autIn_iff.mpr ⟨_, haN.2, Subgroup.mem_top _, rfl⟩
  have hbmem : A0A.normalizerMonoidHom hbN ∈ autIn ⊤ A0A :=
    mem_autIn_iff.mpr ⟨_, hbN.2, Subgroup.mem_top _, rfl⟩
  have hA : linePerm ⟨_, hamem⟩ = swap 0 1 := by
    ext k
    rw [linePerm_apply]
    exact congrArg Fin.val (gens_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k)
  have hB : linePerm ⟨_, hbmem⟩ = finRotate 4 := by
    ext k
    rw [linePerm_apply]
    exact congrArg Fin.val (gens_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k)
  have htop := closure_cycle_adjacent_swap (isCycle_finRotate (n := 2)) support_finRotate
    (0 : Fin 4)
  have h01 : finRotate 4 (0 : Fin 4) = 1 := by decide
  rw [h01] at htop
  have hle : Subgroup.closure ({finRotate 4, swap (0 : Fin 4) 1} : Set (Perm (Fin 4))) ≤
      linePerm.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hB⟩
    · exact ⟨_, hA⟩
  intro σ
  exact hle (htop ▸ Subgroup.mem_top σ)

@[expose] noncomputable def autIn_A0A_equiv : autIn ⊤ A0A ≃* Perm (Fin 4) :=
  MulEquiv.ofBijective linePerm ⟨linePerm_injective, linePerm_surjective⟩

theorem nonempty_autIn_alt9 {D : Subgroup (alternatingGroup (Fin 9))}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (h27 : Nat.card D = 27) :
    Nonempty (autIn ⊤ D ≃* Perm (Fin 4)) := by
  have hD'e := isElemAbelian_map' (alternatingGroup (Fin 9)).subtype hD
  have hD'27 : Nat.card (D.map (alternatingGroup (Fin 9)).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective, h27]
  obtain ⟨g, hg⟩ := exists_eq_map_conj_A0 wFacts_nine factorization_nine ⟨hD'e.1, hD'e.2⟩ hD'27
  set θ : MulAut (alternatingGroup (Fin 9)) := MulAut.conjNormal g⁻¹ with hθ
  have hθD : D.map θ.toMonoidHom = A0A := by
    apply Subgroup.map_injective (alternatingGroup (Fin 9)).subtype_injective
    rw [Subgroup.map_map, A0A, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr A0_nine_le]
    have hcomp : (alternatingGroup (Fin 9)).subtype.comp θ.toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (alternatingGroup (Fin 9)).subtype := by
      ext x
      simp [hθ]
    rw [hcomp, ← Subgroup.map_map, hg, Subgroup.map_map]
    convert Subgroup.map_id (A0 9)
    ext x
    simp
  have f := Sporadic.autInTopCongr θ D
  rw [hθD] at f
  exact ⟨f.trans autIn_A0A_equiv⟩

theorem card_le_27 {D : Subgroup (alternatingGroup (Fin 9))}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : Nat.card D ≤ 27 := by
  set f := (alternatingGroup (Fin 9)).subtype
  have hDe := isElemAbelian_map' f hD
  have hcomm : ∀ x ∈ D.map f, ∀ y ∈ D.map f, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hle := Sec4.card_pow_three_le_of_faithful (Set.univ : Set (Fin 9)).ncard (D.map f)
    Set.univ le_rfl hcomm hDe.2 (fun _ _ _ _ => Set.mem_univ _)
    (fun e _ he => Equiv.ext fun x => he x (Set.mem_univ x))
  rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective,
    Set.ncard_univ, Nat.card_fin] at hle
  by_contra h
  have h1 : 28 ^ 3 ≤ Nat.card D ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (3 : ℕ) ^ 9 < 28 ^ 3 := by norm_num
  omega

theorem le_center_of_map_conj_eq_bot' {X : Type*} [Group X] {T : Subgroup X}
    (h : T.map (MulAut.conj : X →* MulAut X) = ⊥) : T ≤ Subgroup.center X := by
  intro t ht
  rw [← ker_conj_eq_center, MonoidHom.mem_ker]
  have : MulAut.conj t ∈ T.map (MulAut.conj : X →* MulAut X) := ⟨t, ht, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem k417OutA9_holds : Res417Three.K417OutA9 := by
  intro D hD
  obtain ⟨hDe, hmax, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 3 D := fun x =>
    ⟨1, Subtype.ext (by simpa using hDe.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
  have hle := card_le_27 hDe
  have hge : 9 ≤ Nat.card D := hF9.trans (Subgroup.card_le_of_le hFD)
  rw [hk] at hle hge
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk2 : 2 ≤ k := by
    by_contra h
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · exfalso
    have hD9 : Nat.card D = 9 := by rw [hk]; norm_num
    have hFeq : F = D := Subgroup.eq_of_le_of_card_ge hFD (by rw [hD9]; exact hF9)
    subst hFeq
    have hmax' : ∀ E : Subgroup (alternatingGroup (Fin 9)), CFSG.Assembly.IsElemAbelian 3 E →
        F ≤ E → E ≤ F := by
      intro E hE hFE x hx
      refine hmax x (hE.2 x hx) fun d hd => ?_
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨d, hFE hd⟩)
    set Q := T.map (MulAut.conj : alternatingGroup (Fin 9) →* MulAut (alternatingGroup (Fin 9)))
    have hQ3 : ¬ 3 ∣ Nat.card Q := by
      intro h3
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hT2.map (MulAut.conj :
        alternatingGroup (Fin 9) →* MulAut (alternatingGroup (Fin 9))))
      rw [hn] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hN : F.map (MulAut.conj : alternatingGroup (Fin 9) →* MulAut (alternatingGroup (Fin 9))) ≤
        Subgroup.normalizer (Q : Set (MulAut (alternatingGroup (Fin 9)))) :=
      (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map _)
    have hQ := noSignalizer_alt9 hDe hD9 hmax' Q hQ3 hN
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact (Subgroup.mem_center_iff.mp (le_center_of_map_conj_eq_bot' hQ ht) f)
  · have h27 : Nat.card D = 27 := by rw [hk]; norm_num
    exact ⟨h27, nonempty_autIn_alt9 hDe h27⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Four

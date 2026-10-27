module

public import CFSG.LocalAnalysis.WeakClosure81.W172ModHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private instance w172_finite_subgroup : Finite (Subgroup (LGL 2 W)) :=
  Finite.of_injective (fun H : Subgroup (LGL 2 W) => (H : Set (LGL 2 W))) SetLike.coe_injective

private noncomputable instance w172_fintype_lgl : Fintype (LGL 2 W) :=
  Fintype.ofFinite _

private noncomputable instance w172_fintype_subgroup : Fintype (Subgroup (LGL 2 W)) :=
  Fintype.ofFinite _

private noncomputable def w172K (p : ℕ) (Y : Subgroup (LGL 2 W)) :
    Finset {K : Subgroup (LGL 2 W) // W172Hyp p Y K} := by
  classical
  exact Finset.univ.filter (fun K => w172X Y K.1 ≠ ⊥)

private lemma w172_mem_w172K {p : ℕ} {Y : Subgroup (LGL 2 W)}
    {K : {K : Subgroup (LGL 2 W) // W172Hyp p Y K}} :
    K ∈ w172K p Y ↔ w172X Y K.1 ≠ ⊥ := by
  simp only [w172K, Finset.mem_filter, Finset.mem_univ, true_and]

private lemma w172_finrank_finset_sup_eq_sum {ι : Type*} {X : ι → Submodule (ZMod 2) W}
    (hX : iSupIndep X) (T : Finset ι) :
    ∑ i ∈ T, Module.finrank (ZMod 2) (X i) = Module.finrank (ZMod 2) ↥(T.sup X) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sup_empty, finrank_bot]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert, ih]
    have hdisj : Disjoint (X a) (T.sup X) := by
      rw [Finset.sup_eq_iSup]
      exact hX.disjoint_biSup (y := (T : Set ι)) (by simpa using ha)
    rw [disjoint_iff] at hdisj
    have h := Submodule.finrank_sup_add_finrank_inf_eq (X a) (T.sup X)
    rw [hdisj, finrank_bot, add_zero] at h
    exact h.symm

private lemma w172_sum_finrank_le_of_le {ι : Type*} {X : ι → Submodule (ZMod 2) W}
    (hX : iSupIndep X) (T : Finset ι) {M : Submodule (ZMod 2) W}
    (hM : ∀ i ∈ T, X i ≤ M) :
    ∑ i ∈ T, Module.finrank (ZMod 2) (X i) ≤ Module.finrank (ZMod 2) ↥M := by
  rw [w172_finrank_finset_sup_eq_sum hX T]
  exact Submodule.finrank_mono (Finset.sup_le hM)

private lemma w172_card_hyp_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hexp : ∀ y ∈ Y, y ^ p = 1) {a : ℕ} (hcard : Nat.card Y = p ^ a) (ha : 1 ≤ a) :
    a ≤ (w172K p Y).card := by
  classical
  have hYne : Y ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    rw [hcard]
    exact one_lt_pow' hp.one_lt (by omega : a ≠ 0)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hz1' : z.1 ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨K0, hK0, _hzK0, hX0⟩ := w172_exists_hyp hp hp2 hcomm hexp z.2 hz1'
  have hK0mem : (⟨K0, hK0⟩ : {K : Subgroup (LGL 2 W) // W172Hyp p Y K}) ∈ w172K p Y :=
    w172_mem_w172K.mpr hX0
  have hbot : (⨅ K : ↥(w172K p Y), (K.1).1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxY : x ∈ Y := by
      have hxK0 := Subgroup.mem_iInf.mp hx (⟨⟨K0, hK0⟩, hK0mem⟩ : ↥(w172K p Y))
      exact hK0.1 hxK0
    obtain ⟨K1, hK1, hxK1, hX1⟩ := w172_exists_hyp hp hp2 hcomm hexp hxY hx1
    have hK1mem : (⟨K1, hK1⟩ : {K : Subgroup (LGL 2 W) // W172Hyp p Y K}) ∈ w172K p Y :=
      w172_mem_w172K.mpr hX1
    exact hxK1 (Subgroup.mem_iInf.mp hx (⟨⟨K1, hK1⟩, hK1mem⟩ : ↥(w172K p Y)))
  have hle := Subgroup.relIndex_iInf_le (L := Y) (fun K : ↥(w172K p Y) => (K.1).1)
  rw [hbot, Subgroup.relIndex_bot_left] at hle
  have hprod : ∏ K : ↥(w172K p Y), ((K.1).1).relIndex Y = p ^ (w172K p Y).card := by
    rw [Finset.prod_congr rfl (fun K _ => K.1.2.2)]
    simp [Finset.prod_const, Fintype.card_coe]
  rw [hprod] at hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (hcard ▸ hle)

theorem w172_ab_exists_moving {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hexp : ∀ y ∈ Y, y ^ p = 1) {a : ℕ} (hcard : Nat.card Y = p ^ a) (ha : 2 ≤ a) :
    ∃ y ∈ Y, y ≠ 1 ∧
      (a = 2 → 2 * orderOf (2 : ZMod p) ≤
        Module.finrank (ZMod 2) ↥(commSub (zpowers y))) ∧
      (3 ≤ a → 16 * a * orderOf (2 : ZMod p) ≤
        27 * Module.finrank (ZMod 2) ↥(commSub (zpowers y))) := by
  classical
  have hp3 : 3 ≤ p := by
    have : 2 ≤ p := hp.two_le
    omega
  have ho : 0 < orderOf (2 : ZMod p) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exact Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one h2) (by omega)
  have hapos : 1 ≤ a := by omega
  have hXind : iSupIndep (fun K : {K : Subgroup (LGL 2 W) // W172Hyp p Y K} =>
      w172X Y K.1) := w172_X_iSupIndep hp hp2 hcomm hexp
  have hsq : a ≤ (w172K p Y).card := w172_card_hyp_le hp hp2 hcomm hexp hcard hapos
  have hA2 : a * orderOf (2 : ZMod p) ≤
      ∑ K ∈ w172K p Y, Module.finrank (ZMod 2) (w172X Y K.1) := by
    have h1 : ∑ K ∈ w172K p Y, orderOf (2 : ZMod p) ≤
        ∑ K ∈ w172K p Y, Module.finrank (ZMod 2) (w172X Y K.1) := by
      apply Finset.sum_le_sum
      intro K hK
      exact w172_orderOf_two_le_finrank_X hp hp2 hcomm hexp K.2 (w172_mem_w172K.mp hK)
    have h2 : ∑ K ∈ w172K p Y, orderOf (2 : ZMod p) =
        (w172K p Y).card * orderOf (2 : ZMod p) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have h3 : a * orderOf (2 : ZMod p) ≤
        (w172K p Y).card * orderOf (2 : ZMod p) := Nat.mul_le_mul_right _ hsq
    exact h3.trans (h2 ▸ h1)
  have hcount : ∀ K : {K : Subgroup (LGL 2 W) // W172Hyp p Y K},
      (Finset.univ.filter (fun y : ↥Y => y.1 ∉ K.1)).card = Nat.card Y - Nat.card K.1 := by
    intro K
    have h1 : (Finset.univ.filter (fun y : ↥Y => y.1 ∈ K.1)).card = Nat.card K.1 := by
      let g : K.1 → ↥Y := fun k => ⟨k.1, K.2.1 k.2⟩
      have hg : Function.Injective g :=
        fun a b h => Subtype.ext (congrArg (fun y : ↥Y => y.1) h)
      have himg : (Finset.univ.filter (fun y : ↥Y => y.1 ∈ K.1))
          = (Finset.univ : Finset K.1).map ⟨g, hg⟩ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · intro hy
          exact ⟨⟨y.1, hy⟩, Subtype.ext rfl⟩
        · rintro ⟨k, hk⟩
          rw [← hk]
          exact k.2
      rw [himg, Finset.card_map, Finset.card_univ, Fintype.card_eq_nat_card]
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ↥Y)) (p := fun y : ↥Y => y.1 ∈ K.1)
    rw [h1, Finset.card_univ, Fintype.card_eq_nat_card] at h2
    omega
  have hm : ∀ K : {K : Subgroup (LGL 2 W) // W172Hyp p Y K}, Nat.card K.1 = p ^ (a - 1) := by
    intro K
    have hrel : K.1.relIndex Y = p := K.2.2
    have hle : K.1 ≤ Y := K.2.1
    have h := Subgroup.relIndex_mul_card (H := K.1) (K := Y)
    rw [hrel, inf_eq_left.mpr hle, hcard] at h
    have hpa : p ^ a = p * p ^ (a - 1) := by
      have hsucc : a = (a - 1) + 1 := (Nat.sub_add_cancel (show 1 ≤ a by omega)).symm
      conv_lhs => rw [hsucc, pow_succ']
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [← hpa]; exact h)
  have hN : Nat.card Y = p * p ^ (a - 1) := by
    rw [hcard]
    have hsucc : a = (a - 1) + 1 := (Nat.sub_add_cancel (show 1 ≤ a by omega)).symm
    conv_lhs => rw [hsucc, pow_succ']
  have hNm : Nat.card Y - p ^ (a - 1) = (p - 1) * p ^ (a - 1) := by
    rw [hN, Nat.mul_sub_right_distrib, one_mul]
  rcases eq_or_ne a 2 with ha2 | ha2
  · subst a
    obtain ⟨K1, hK1, K2, hK2, hK12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (w172K p Y).card)
    have hnotle1 : ¬ K1.1 ≤ K2.1 := by
      intro hle
      have h1 := Subgroup.relIndex_mul_relIndex (H := K1.1) (K := K2.1) (L := Y) hle K2.2.1
      rw [K2.2.2, K1.2.2] at h1
      have h2 : K1.1.relIndex K2.1 = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (by rw [one_mul]; exact h1)
      exact hK12 (Subtype.ext (le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)))
    have hnotle2 : ¬ K2.1 ≤ K1.1 := by
      intro hle
      have h1 := Subgroup.relIndex_mul_relIndex (H := K2.1) (K := K1.1) (L := Y) hle K1.2.1
      rw [K1.2.2, K2.2.2] at h1
      have h2 : K2.1.relIndex K1.1 = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (by rw [one_mul]; exact h1)
      exact hK12 (Subtype.ext (le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle))
    have hex1 : ∃ x : LGL 2 W, x ∈ K1.1 ∧ x ∉ K2.1 := by
      have h1 : ¬ ∀ x : LGL 2 W, x ∈ K1.1 → x ∈ K2.1 :=
        fun h => hnotle1 (IsConcreteLE.le_iff.mpr h)
      rw [not_forall] at h1
      obtain ⟨x, hx⟩ := h1
      rw [not_imp] at hx
      exact ⟨x, hx.1, hx.2⟩
    have hex2 : ∃ x : LGL 2 W, x ∈ K2.1 ∧ x ∉ K1.1 := by
      have h1 : ¬ ∀ x : LGL 2 W, x ∈ K2.1 → x ∈ K1.1 :=
        fun h => hnotle2 (IsConcreteLE.le_iff.mpr h)
      rw [not_forall] at h1
      obtain ⟨x, hx⟩ := h1
      rw [not_imp] at hx
      exact ⟨x, hx.1, hx.2⟩
    obtain ⟨a', ha'K1, ha'K2⟩ := hex1
    obtain ⟨b', hb'K2, hb'K1⟩ := hex2
    have ha'Y : a' ∈ Y := K1.2.1 ha'K1
    have hb'Y : b' ∈ Y := K2.2.1 hb'K2
    have hyY : a' * b' ∈ Y := Y.mul_mem ha'Y hb'Y
    have hyK1 : a' * b' ∉ K1.1 := by
      intro hy
      have hbK1 : b' ∈ K1.1 := by
        have hh := K1.1.mul_mem (K1.1.inv_mem ha'K1) hy
        rwa [inv_mul_cancel_left] at hh
      exact hb'K1 hbK1
    have hyK2 : a' * b' ∉ K2.1 := by
      intro hy
      have haK2 : a' ∈ K2.1 := by
        have hh := K2.1.mul_mem hy (K2.1.inv_mem hb'K2)
        rwa [mul_inv_cancel_right] at hh
      exact ha'K2 haK2
    have hy1 : a' * b' ≠ 1 := by
      intro hy
      have hh : a' = b'⁻¹ := eq_inv_of_mul_eq_one_left hy
      exact ha'K2 (by rw [hh]; exact K2.1.inv_mem hb'K2)
    refine ⟨a' * b', hyY, hy1, ?_, ?_⟩
    · intro _
      have ho1 := w172_orderOf_two_le_finrank_X hp hp2 hcomm hexp K1.2 (w172_mem_w172K.mp hK1)
      have ho2 := w172_orderOf_two_le_finrank_X hp hp2 hcomm hexp K2.2 (w172_mem_w172K.mp hK2)
      have hsum2 : Module.finrank (ZMod 2) (w172X Y K1.1) +
          Module.finrank (ZMod 2) (w172X Y K2.1) ≤
          Module.finrank (ZMod 2) (commSub (zpowers (a' * b'))) := by
        have h := w172_sum_finrank_le_of_le
          (X := fun K : {K : Subgroup (LGL 2 W) // W172Hyp p Y K} => w172X Y K.1)
          hXind ({K1, K2} : Finset _) (M := commSub (zpowers (a' * b')))
          (fun K hK => by
            have hK' : K = K1 ∨ K = K2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hK
            rcases hK' with h | h
            · rw [h]
              exact w172_X_le_commSub_of_not_mem hp hp2 hcomm hexp K1.2 hyY hyK1
            · rw [h]
              exact w172_X_le_commSub_of_not_mem hp hp2 hcomm hexp K2.2 hyY hyK2)
        rwa [Finset.sum_pair hK12] at h
      have h22 : 2 * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (w172X Y K1.1) +
          Module.finrank (ZMod 2) (w172X Y K2.1) := by omega
      exact h22.trans hsum2
    · intro h3
      omega
  · have ha3 : 3 ≤ a := by omega
    have hstep1 : ∀ y : ↥Y,
        ∑ K ∈ (w172K p Y).filter (fun K => y.1 ∉ K.1),
            Module.finrank (ZMod 2) (w172X Y K.1) ≤
          Module.finrank (ZMod 2) (commSub (zpowers y.1)) := by
      intro y
      rw [w172_finrank_finset_sup_eq_sum hXind]
      exact Submodule.finrank_mono (Finset.sup_le (fun K hK =>
        w172_X_le_commSub_of_not_mem hp hp2 hcomm hexp K.2 y.2 (Finset.mem_filter.mp hK).2))
    have hstep2 :
        (∑ y : ↥Y, ∑ K ∈ (w172K p Y).filter (fun K => y.1 ∉ K.1),
            Module.finrank (ZMod 2) (w172X Y K.1))
          = (Nat.card Y - p ^ (a - 1)) *
              ∑ K ∈ w172K p Y, Module.finrank (ZMod 2) (w172X Y K.1) := by
      have hswap :
          (∑ y : ↥Y, ∑ K ∈ (w172K p Y).filter (fun K => y.1 ∉ K.1),
              Module.finrank (ZMod 2) (w172X Y K.1))
            = ∑ K ∈ w172K p Y, (Finset.univ.filter (fun y : ↥Y => y.1 ∉ K.1)).card *
                Module.finrank (ZMod 2) (w172X Y K.1) := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro K _hK
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hswap]
      calc ∑ K ∈ w172K p Y, (Finset.univ.filter (fun y : ↥Y => y.1 ∉ K.1)).card *
              Module.finrank (ZMod 2) (w172X Y K.1)
          = ∑ K ∈ w172K p Y, (Nat.card Y - p ^ (a - 1)) *
              Module.finrank (ZMod 2) (w172X Y K.1) := by
            apply Finset.sum_congr rfl
            intro K _hK
            rw [hcount K, hm K]
        _ = (Nat.card Y - p ^ (a - 1)) *
              ∑ K ∈ w172K p Y, Module.finrank (ZMod 2) (w172X Y K.1) := by
            rw [Finset.mul_sum]
    have hfind : ∃ y : ↥Y, 2 * a * orderOf (2 : ZMod p) ≤
        3 * Module.finrank (ZMod 2) (commSub (zpowers y.1)) := by
      by_contra hcon
      rw [not_exists] at hcon
      have hlt : ∀ y : ↥Y, 3 * Module.finrank (ZMod 2) (commSub (zpowers y.1)) <
          2 * a * orderOf (2 : ZMod p) := fun y => by
        have := hcon y
        omega
      have hLower : (Nat.card Y - p ^ (a - 1)) * (a * orderOf (2 : ZMod p)) ≤
          ∑ y : ↥Y, Module.finrank (ZMod 2) (commSub (zpowers y.1)) := by
        calc (Nat.card Y - p ^ (a - 1)) * (a * orderOf (2 : ZMod p))
            ≤ (Nat.card Y - p ^ (a - 1)) *
                ∑ K ∈ w172K p Y, Module.finrank (ZMod 2) (w172X Y K.1) :=
              Nat.mul_le_mul_left _ hA2
          _ = ∑ y : ↥Y, ∑ K ∈ (w172K p Y).filter (fun K => y.1 ∉ K.1),
                Module.finrank (ZMod 2) (w172X Y K.1) := hstep2.symm
          _ ≤ ∑ y : ↥Y, Module.finrank (ZMod 2) (commSub (zpowers y.1)) :=
              Finset.sum_le_sum (fun y _ => hstep1 y)
      have hUpper : 3 * (∑ y : ↥Y, Module.finrank (ZMod 2) (commSub (zpowers y.1))) +
          Nat.card Y ≤ Nat.card Y * (2 * a * orderOf (2 : ZMod p)) := by
        have hsum : (∑ y : ↥Y,
            (3 * Module.finrank (ZMod 2) (commSub (zpowers y.1)) + 1))
              = 3 * (∑ y : ↥Y, Module.finrank (ZMod 2) (commSub (zpowers y.1))) +
                Nat.card Y := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one]
          simp
        rw [← hsum]
        calc (∑ y : ↥Y, (3 * Module.finrank (ZMod 2) (commSub (zpowers y.1)) + 1))
            ≤ ∑ _y : ↥Y, 2 * a * orderOf (2 : ZMod p) :=
              Finset.sum_le_sum (fun y _ => by have := hlt y; omega)
          _ = Nat.card Y * (2 * a * orderOf (2 : ZMod p)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, nsmul_eq_mul]
              simp
      have hcomb0 : 3 * ((Nat.card Y - p ^ (a - 1)) * (a * orderOf (2 : ZMod p))) +
          Nat.card Y ≤ Nat.card Y * (2 * a * orderOf (2 : ZMod p)) :=
        calc 3 * ((Nat.card Y - p ^ (a - 1)) * (a * orderOf (2 : ZMod p))) + Nat.card Y
            ≤ 3 * (∑ y : ↥Y, Module.finrank (ZMod 2) (commSub (zpowers y.1))) +
                Nat.card Y := Nat.add_le_add_right (Nat.mul_le_mul_left 3 hLower) _
          _ ≤ Nat.card Y * (2 * a * orderOf (2 : ZMod p)) := hUpper
      rw [hNm, hN] at hcomb0
      have hL : 3 * (((p - 1) * p ^ (a - 1)) * (a * orderOf (2 : ZMod p))) +
          p * p ^ (a - 1)
            = (3 * (p - 1)) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) +
              p * p ^ (a - 1) := by ring
      have hR : (p * p ^ (a - 1)) * (2 * a * orderOf (2 : ZMod p))
            = (2 * p) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) := by ring
      rw [hL, hR] at hcomb0
      have hge2 : 2 * p ≤ 3 * (p - 1) := by omega
      have hlt2 : (2 * p) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) <
          (3 * (p - 1)) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) +
            p * p ^ (a - 1) := by
        have hpmp : 0 < p * p ^ (a - 1) := Nat.mul_pos hp.pos (pow_pos hp.pos _)
        calc (2 * p) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p)))
            ≤ (3 * (p - 1)) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) :=
              Nat.mul_le_mul_right _ hge2
          _ < (3 * (p - 1)) * (p ^ (a - 1) * (a * orderOf (2 : ZMod p))) +
              p * p ^ (a - 1) := Nat.lt_add_of_pos_right hpmp
      exact absurd hcomb0 (not_le.mpr hlt2)
    obtain ⟨y, hy⟩ := hfind
    have hy1 : y.1 ≠ 1 := by
      intro h
      have hf0 : Module.finrank (ZMod 2) (commSub (zpowers y.1)) = 0 := by
        rw [h, Subgroup.zpowers_one_eq_bot, commSub_bot, finrank_bot]
      rw [hf0] at hy
      have hpos : 0 < 2 * a * orderOf (2 : ZMod p) := by positivity
      omega
    refine ⟨y.1, y.2, hy1, ?_, ?_⟩
    · intro h2
      omega
    · intro _
      have : 16 * a * orderOf (2 : ZMod p) ≤
          27 * Module.finrank (ZMod 2) (commSub (zpowers y.1)) := by
        nlinarith [hy]
      exact this

end CFSG.LocalAnalysis.WeakClosure81

end

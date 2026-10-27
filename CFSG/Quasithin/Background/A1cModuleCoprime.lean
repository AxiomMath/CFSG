module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem isCompl_fixed_commOf_of_odd [Finite A] (hodd : Odd (Nat.card A))
    (hQ : ∀ q : Q, q ^ 2 = 1) :
    IsCompl (fixed A (⊤ : Subgroup Q)) (commOf A (⊤ : Subgroup Q)) := by
  classical
  have := Fintype.ofFinite A
  have hn : Odd (Fintype.card A) := by rwa [← Nat.card_eq_fintype_card]
  have hpow : ∀ q : Q, q ^ Fintype.card A = q := by
    intro q
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_succ, pow_mul, hQ q, one_pow, one_mul]
  let N : Q →* Q :=
    { toFun := fun q => ∏ a : A, a • q
      map_one' := by simp
      map_mul' := fun x y => by simp only [smul_mul']; exact Finset.prod_mul_distrib }
  have hNdef : ∀ q, N q = ∏ a : A, a • q := fun q => rfl
  have hN_smul : ∀ (b : A) (q : Q), N (b • q) = N q := by
    intro b q
    rw [hNdef, hNdef]
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ (fun a => rfl)
  have hN_fixed : ∀ q : Q, N q ∈ fixed A (⊤ : Subgroup Q) := by
    intro q
    refine ⟨trivial, fun b => ?_⟩
    have h1 := map_prod (MulDistribMulAction.toMonoidHom Q b) (fun a : A => a • q) Finset.univ
    have h2 : b • ∏ a : A, a • q = ∏ a : A, b • a • q := h1
    rw [hNdef, h2]
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun a => rfl)
  have hN_ker : ∀ q ∈ commOf A (⊤ : Subgroup Q), N q = 1 := by
    intro q hq
    have : commOf A (⊤ : Subgroup Q) ≤ N.ker := by
      rw [commOf_le_iff]
      intro a l _
      rw [MonoidHom.mem_ker, map_mul, map_inv, hN_smul, mul_inv_cancel]
    exact this hq
  have hN_self : ∀ q ∈ fixed A (⊤ : Subgroup Q), N q = q := by
    intro q hq
    rw [hNdef]
    simp_rw [hq.2]
    rw [Finset.prod_const, Finset.card_univ, hpow]
  have hdecomp : ∀ q : Q, q * (N q)⁻¹ ∈ commOf A (⊤ : Subgroup Q) := by
    intro q
    have h1 : q * (N q)⁻¹ = ∏ a : A, (q * (a • q)⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hpow, hNdef,
        Finset.prod_inv_distrib]
    rw [h1]
    refine Subgroup.prod_mem _ fun a _ => ?_
    have : q * (a • q)⁻¹ = ((a • q) * q⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem (mem_commOf_of_mem a trivial)
  rw [isCompl_iff, disjoint_iff_inf_le, codisjoint_iff]
  constructor
  · intro q ⟨hq1, hq2⟩
    rw [Subgroup.mem_bot, ← hN_self q hq1]
    exact hN_ker q hq2
  · rw [eq_top_iff]
    intro q _
    have : q = N q * (q * (N q)⁻¹) := by
      rw [mul_comm q, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup (hN_fixed q) (hdecomp q)

end XMod

section Dihedral

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

theorem eq_one_or_eq_of_mem_zpowers_of_sq {t a : G} (ht : t ^ 2 = 1)
    (ha : a ∈ Subgroup.zpowers t) : a = 1 ∨ a = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have ht' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact ht
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, ht', one_zpow]
  · right; rw [zpow_add_one, zpow_mul, ht', one_zpow, one_mul]

theorem isModInv_zpowers_of_sq {t : G} (ht : t ^ 2 = 1) {W : Subgroup V}
    (h : ∀ w ∈ W, t • w ∈ W) : IsModInv (Subgroup.zpowers t) W := by
  intro a w hw
  change (a : G) • w ∈ W
  rcases eq_one_or_eq_of_mem_zpowers_of_sq ht a.2 with h1 | h1
  · rw [h1, one_smul]; exact hw
  · rw [h1]; exact h w hw

theorem mem_modFix_zpowers_iff {t : G} {W : Subgroup V} {v : V} :
    v ∈ modFix (Subgroup.zpowers t) W ↔ v ∈ W ∧ t • v = v := by
  constructor
  · intro h
    exact ⟨h.1, h.2 ⟨t, Subgroup.mem_zpowers t⟩⟩
  · rintro ⟨hW, hv⟩
    refine ⟨hW, fun a => ?_⟩
    have : Subgroup.zpowers t ≤ MulAction.stabilizer G v :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hv)
    exact MulAction.mem_stabilizer_iff.1 (this a.2)

theorem smul_commutator_of_sq {t : G} (ht : t ^ 2 = 1) (hV : ∀ v : V, v ^ 2 = 1) (w : V) :
    t • ((t • w) * w⁻¹) = (t • w) * w⁻¹ := by
  have h1 : t • t • w = w := by rw [smul_smul, ← sq, ht, one_smul]
  have hw : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV w)
  have htw : (t • w)⁻¹ = t • w := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV _)
  rw [smul_mul', h1, smul_inv', htw, hw]
  exact mul_comm _ _

theorem modComm_zpowers_le_modFix {t : G} (ht : t ^ 2 = 1) (hV : ∀ v : V, v ^ 2 = 1)
    {W : Subgroup V} (hW : IsModInv (Subgroup.zpowers t) W) :
    modComm (Subgroup.zpowers t) W ≤ modFix (Subgroup.zpowers t) W := by
  have h1 : modComm (Subgroup.zpowers t) W ≤ modFix (Subgroup.zpowers t) ⊤ := by
    rw [XMod.commOf_le_iff]
    intro a w hw
    refine ⟨trivial, fun b => ?_⟩
    change (b : G) • ((a : G) • w * w⁻¹) = (a : G) • w * w⁻¹
    rcases eq_one_or_eq_of_mem_zpowers_of_sq ht a.2 with ha | ha
    · rw [ha, one_smul, mul_inv_cancel, smul_one]
    · rcases eq_one_or_eq_of_mem_zpowers_of_sq ht b.2 with hb | hb
      · rw [hb, one_smul]
      · rw [ha, hb]; exact smul_commutator_of_sq ht hV w
  intro e he
  exact ⟨XMod.commOf_le_of_isInv hW he, (h1 he).2⟩

theorem mem_normalizer_zpowers_of_inv {t x : G} (ht : t ^ 2 = 1) (hx : t * x * t⁻¹ = x⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have h2 : t * t = 1 := by rw [← sq]; exact ht
  have h3 : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  have key : ∀ h ∈ Subgroup.zpowers x, t * h * t⁻¹ ∈ Subgroup.zpowers x := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, hx]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers x)) k
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key h, fun hh => ?_⟩
  have := key _ hh
  rwa [h3, ← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, h2, mul_one] at this

theorem smul_top_eq_top (g : G) : g • (⊤ : Subgroup V) = ⊤ := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem inv_conj_of_sq {t u : G} (ht : t ^ 2 = 1) (hu : u ^ 2 = 1) :
    t * (t * u) * t⁻¹ = (t * u)⁻¹ ∧ u * (t * u) * u⁻¹ = (t * u)⁻¹ := by
  have ht2 : t * t = 1 := by rw [← sq]; exact ht
  have hu2 : u * u = 1 := by rw [← sq]; exact hu
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [mul_inv_rev, htinv, huinv]
  exact ⟨by rw [← mul_assoc, ht2, one_mul],
    by rw [← mul_assoc u t u, mul_assoc, hu2, mul_one]⟩

theorem dihedral_decomposition (hV : ∀ v : V, v ^ 2 = 1) {t u : G} (ht : t ^ 2 = 1)
    (hu : u ^ 2 = 1) (hodd : Odd (orderOf (t * u))) {W : Subgroup V}
    (hW : W = modComm (Subgroup.zpowers (t * u)) ⊤) :
    IsCompl W (modFix (Subgroup.zpowers (t * u)) ⊤) ∧
      (Disjoint (modComm (Subgroup.zpowers t) W) (modComm (Subgroup.zpowers u) W) ∧
        modComm (Subgroup.zpowers t) W ⊔ modComm (Subgroup.zpowers u) W = W) ∧
      modFix (Subgroup.zpowers t) W = modComm (Subgroup.zpowers t) W := by
  set x := t * u with hxdef
  set Y := Subgroup.zpowers x with hYdef
  have hxt : t * x * t⁻¹ = x⁻¹ := (inv_conj_of_sq ht hu).1
  have hxu : u * x * u⁻¹ = x⁻¹ := (inv_conj_of_sq ht hu).2
  have hnt : t ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_zpowers_of_inv ht hxt
  have hnu : u ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_zpowers_of_inv hu hxu
  have hfin : Finite ↥Y :=
    Nat.finite_of_card_ne_zero (by rw [hYdef, Nat.card_zpowers]; exact hodd.pos.ne')
  have hodd' : Odd (Nat.card ↥Y) := by rw [hYdef, Nat.card_zpowers]; exact hodd
  have hcompl : IsCompl (modFix Y ⊤) (modComm Y ⊤) :=
    XMod.isCompl_fixed_commOf_of_odd hodd' hV
  have hcompl' : IsCompl W (modFix Y ⊤) := by rw [hW]; exact hcompl.symm
  have hWt : t • W = W := by rw [hW, smul_modComm hnt, smul_top_eq_top]
  have hWu : u • W = W := by rw [hW, smul_modComm hnu, smul_top_eq_top]
  have hWt' : ∀ w ∈ W, t • w ∈ W := fun w hw => by
    have := Subgroup.smul_mem_pointwise_smul w t W hw
    rwa [hWt] at this
  have hWu' : ∀ w ∈ W, u • w ∈ W := fun w hw => by
    have := Subgroup.smul_mem_pointwise_smul w u W hw
    rwa [hWu] at this
  have hWY : IsModInv Y W := by rw [hW]; exact XMod.isInv_commOf _
  have hIt : IsModInv (Subgroup.zpowers t) W := isModInv_zpowers_of_sq ht hWt'
  have hIu : IsModInv (Subgroup.zpowers u) W := isModInv_zpowers_of_sq hu hWu'
  have hWY' : modComm Y W = W := by
    have hsup : W ⊔ modFix Y ⊤ = ⊤ := hcompl'.sup_eq_top
    calc modComm Y W = modComm Y (W ⊔ modFix Y ⊤) :=
          (XMod.commOf_sup_eq_of_le_fixed le_rfl).symm
      _ = modComm Y ⊤ := by rw [hsup]
      _ = W := hW.symm
  have hle : modComm Y W ≤ modComm (Subgroup.zpowers t) W ⊔ modComm (Subgroup.zpowers u) W := by
    set M := modComm (Subgroup.zpowers t) W ⊔ modComm (Subgroup.zpowers u) W with hMdef
    have key : ∀ y ∈ Subgroup.closure ({x} : Set G), ∀ w ∈ W, (y • w) * w⁻¹ ∈ M := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy' =>
        intro w hw
        rw [Set.mem_singleton_iff] at hy'
        rw [hy', hxdef, mul_smul]
        have h1 : (t • u • w) * w⁻¹ = ((t • (u • w)) * (u • w)⁻¹) * ((u • w) * w⁻¹) := by
          group
        rw [h1]
        exact Subgroup.mul_mem_sup
          (XMod.mem_commOf_of_mem (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t) (hWu' w hw))
          (XMod.mem_commOf_of_mem (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) hw)
      | one =>
        intro w _
        rw [one_smul, mul_inv_cancel]
        exact one_mem _
      | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
        intro w hw
        have hy₂' : y₂ ∈ Y := by rwa [hYdef, Subgroup.zpowers_eq_closure]
        have hw' : y₂ • w ∈ W := hWY ⟨y₂, hy₂'⟩ w hw
        have h1 : ((y₁ * y₂) • w) * w⁻¹ = ((y₁ • (y₂ • w)) * (y₂ • w)⁻¹) * ((y₂ • w) * w⁻¹) := by
          rw [mul_smul]; group
        rw [h1]
        exact mul_mem (ih₁ _ hw') (ih₂ w hw)
      | inv y₁ hy₁ ih =>
        intro w hw
        have hy₁' : y₁⁻¹ ∈ Y := by
          rw [hYdef, Subgroup.zpowers_eq_closure]; exact inv_mem hy₁
        have hw' : y₁⁻¹ • w ∈ W := hWY ⟨y₁⁻¹, hy₁'⟩ w hw
        have h1 : (y₁⁻¹ • w) * w⁻¹ = ((y₁ • (y₁⁻¹ • w)) * (y₁⁻¹ • w)⁻¹)⁻¹ := by
          rw [smul_inv_smul]; group
        rw [h1]
        exact inv_mem (ih _ hw')
    rw [XMod.commOf_le_iff]
    intro a w hw
    exact key a (by rw [← Subgroup.zpowers_eq_closure]; exact a.2) w hw
  have hsum : modComm (Subgroup.zpowers t) W ⊔ modComm (Subgroup.zpowers u) W = W :=
    le_antisymm (sup_le (XMod.commOf_le_of_isInv hIt) (XMod.commOf_le_of_isInv hIu))
      (calc W = modComm Y W := hWY'.symm
        _ ≤ _ := hle)
  have hfixt := modComm_zpowers_le_modFix ht hV hIt
  have hfixu := modComm_zpowers_le_modFix hu hV hIu
  have hkey : ∀ e ∈ modFix (Subgroup.zpowers t) W, e ∈ modFix (Subgroup.zpowers u) W → e = 1 := by
    intro e het heu
    have ht1 : t • e = e := (mem_modFix_zpowers_iff.1 het).2
    have hu1 : u • e = e := (mem_modFix_zpowers_iff.1 heu).2
    have hxe : x • e = e := by rw [hxdef, mul_smul, hu1, ht1]
    have hefix : e ∈ modFix Y ⊤ := mem_modFix_zpowers_iff.2 ⟨trivial, hxe⟩
    exact Subgroup.disjoint_def.1 hcompl'.disjoint (mem_modFix_zpowers_iff.1 het).1 hefix
  refine ⟨hcompl', ⟨Subgroup.disjoint_def.2 fun {e} het heu => hkey e (hfixt het) (hfixu heu),
    hsum⟩, le_antisymm ?_ hfixt⟩
  intro e he
  have heW : e ∈ W := he.1
  rw [← hsum] at heW
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 heW
  have hfa : a ∈ modFix (Subgroup.zpowers t) W := hfixt ha
  have hbfix : b ∈ modFix (Subgroup.zpowers t) W := by
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    exact mul_mem (inv_mem hfa) he
  have hb1 : b = 1 := hkey b hbfix (hfixu hb)
  rw [hb1, mul_one]
  exact ha

theorem odd_orderOf_mul_of_dihedral [Finite G] {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : t ≠ u) (hgen : Subgroup.closure ({t, u} : Set G) = ⊤) {k : ℕ}
    (hk : Nat.card G = 2 * k) (hkodd : Odd k) : Odd (orderOf (t * u)) := by
  classical
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  set x := t * u with hxdef
  set H := Subgroup.zpowers x with hHdef
  have hxt : t * x * t⁻¹ = x⁻¹ := (inv_conj_of_sq ht2 hu2).1
  have hxu : u * x * u⁻¹ = x⁻¹ := (inv_conj_of_sq ht2 hu2).2
  have hnorm : Subgroup.normalizer (H : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact mem_normalizer_zpowers_of_inv ht2 hxt
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact mem_normalizer_zpowers_of_inv hu2 hxu
  have hH : H.Normal := Subgroup.normalizer_eq_top_iff.1 hnorm
  have ht2' : t * t = 1 := by rw [← sq]; exact ht2
  have hq_t2 : (QuotientGroup.mk t : G ⧸ H) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
  have hq_u : (QuotientGroup.mk u : G ⧸ H) = (QuotientGroup.mk t)⁻¹ := by
    have h1 : u = t⁻¹ * x := by
      rw [hxdef, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff x).2 (Subgroup.mem_zpowers x), mul_one]
  have hall : ∀ g : G ⧸ H, g ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ H) := by
    intro g
    refine QuotientGroup.induction_on g fun g' => ?_
    have hg' : g' ∈ Subgroup.closure ({t, u} : Set G) := by rw [hgen]; trivial
    induction hg' using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Subgroup.mem_zpowers _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [hq_u]
        exact inv_mem (Subgroup.mem_zpowers _)
    | one => rw [QuotientGroup.mk_one]; exact one_mem _
    | mul y z _ _ hy hz => rw [QuotientGroup.mk_mul]; exact mul_mem hy hz
    | inv y _ hy => rw [QuotientGroup.mk_inv]; exact inv_mem hy
  have hcard_quot : Nat.card (G ⧸ H) ≤ 2 := by
    have h1 : Subgroup.zpowers (QuotientGroup.mk t : G ⧸ H) = ⊤ :=
      eq_top_iff.2 fun g _ => hall g
    have h2 : Nat.card (G ⧸ H) = orderOf (QuotientGroup.mk t : G ⧸ H) := by
      rw [← Nat.card_zpowers, h1, Subgroup.card_top]
    rw [h2]
    exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hq_t2)
  have hindex : H.index ≤ 2 := by rw [Subgroup.index_eq_card]; exact hcard_quot
  have hindex0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.card_mul_index H
  have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
  have hcases : H.index = 1 ∨ H.index = 2 := by omega
  rcases hcases with h1 | h2
  ·
    exfalso
    have hHtop : H = ⊤ := Subgroup.index_eq_one.1 h1
    have hcyc : IsCyclic G := ⟨⟨x, fun g => by
      have : g ∈ H := by rw [hHtop]; trivial
      exact this⟩⟩
    have := Fintype.ofFinite G
    have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) two_pos
    have ht1 : t ≠ 1 := fun h => by
      rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
    have hu1 : u ≠ 1 := fun h => by
      rw [h, orderOf_one] at hu; exact absurd hu (by norm_num)
    have h3 : (({1, t, u} : Finset G)).card = 3 :=
      Finset.card_eq_three.2 ⟨1, t, u, ht1.symm, hu1.symm, htu, rfl⟩
    have hsub : ({1, t, u} : Finset G) ⊆ Finset.univ.filter (fun a : G => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · exact one_pow 2
      · exact ht2
      · exact hu2
    have := Finset.card_le_card hsub
    omega
  · rw [h2] at hmul
    have : orderOf x = k := by omega
    rw [this]
    exact hkodd

theorem dihedral_module_decomposition [Finite G] (hV : ∀ v : V, v ^ 2 = 1) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : t ≠ u)
    (hgen : Subgroup.closure ({t, u} : Set G) = ⊤) {k : ℕ} (hk : Nat.card G = 2 * k)
    (hkodd : Odd k) {W : Subgroup V} (hW : W = modComm (Subgroup.zpowers (t * u)) ⊤) :
    IsCompl W (modFix (Subgroup.zpowers (t * u)) ⊤) ∧
      (Disjoint (modComm (Subgroup.zpowers t) W) (modComm (Subgroup.zpowers u) W) ∧
        modComm (Subgroup.zpowers t) W ⊔ modComm (Subgroup.zpowers u) W = W) ∧
      modFix (Subgroup.zpowers t) W = modComm (Subgroup.zpowers t) W :=
  dihedral_decomposition hV (by rw [← ht]; exact pow_orderOf_eq_one t)
    (by rw [← hu]; exact pow_orderOf_eq_one u)
    (odd_orderOf_mul_of_dihedral ht hu htu hgen hk hkodd) hW

end Dihedral

end CFSG.Quasithin

module

public import CFSG.Monster.GMS.S37Basic
public import CFSG.Monster.GMS.S37One
public import CFSG.Monster.GMS.S36LinesBasic
import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.GMS.S36LinesA12

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic S36Lines

namespace S37

section Involutions

variable {G : Type*} [Group G]

theorem mem_cent_iff {x y : G} : x ∈ Subgroup.centralizer ({y} : Set G) ↔ x * y = y * x :=
  Subgroup.mem_centralizer_singleton_iff

theorem cent_symm {x y : G} :
    x ∈ Subgroup.centralizer ({y} : Set G) ↔ y ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [mem_cent_iff, mem_cent_iff]
  exact ⟨Eq.symm, Eq.symm⟩

theorem eq_of_mul_comm_of_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x)
    (hodd : Odd (orderOf (x * y))) : x = y := by
  have hsq : (x * y) * (x * y) = 1 :=
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have hd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h1 : orderOf (x * y) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h2 : x * y = 1 := orderOf_eq_one_iff.mp h1
  exact (eq_inv_of_mul_eq_one_left h2).trans (inv_eq_of_mul_eq_one_right hy)

theorem ne_of_isConj_mul {z₀ v s : G} (hz : orderOf z₀ = 2) (hss : s * s = 1)
    (h : IsConj z₀ (v * s)) : v ≠ s := by
  rintro rfl
  rw [hss] at h
  have h1 : z₀ = 1 := isConj_one_right.mp h.symm
  rw [h1, orderOf_one] at hz
  omega

theorem orderOf_mul_eq_two {b t : G} (hbb : b * b = 1) (htt : t * t = 1) (hbt : b * t = t * b)
    (hne : b ≠ t) : orderOf (b * t) = 2 := by
  have hsq : (b * t) * (b * t) = 1 :=
    calc (b * t) * (b * t) = b * (t * b) * t := by group
      _ = b * (b * t) * t := by rw [hbt]
      _ = (b * b) * (t * t) := by group
      _ = 1 := by rw [hbb, htt, one_mul]
  refine orderOf_eq_two_of_mul_self hsq fun h => hne ?_
  rw [eq_inv_of_mul_eq_one_left h]
  exact inv_eq_of_mul_eq_one_right htt

theorem mem_zpowers_of_orderOf_two {b g : G} (hb : orderOf b = 2) :
    g ∈ Subgroup.zpowers b ↔ g = 1 ∨ g = b := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← zpow_mod_orderOf, hb]
      simp [h]
    · right
      rw [← zpow_mod_orderOf, hb]
      simp [h]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

end Involutions

section Arith

theorem arith_eight_three (n : ℕ) (h : (2 ^ 35 * 3 ^ 4 * 5 * 7) * (2 ^ 35 * 3 ^ 4 * 5 * 7) ≤
    n * tableVOrderB) : 30995 < n := by
  unfold tableVOrderB at h
  omega

theorem arith_eight_one (n : ℕ) (h : (2 ^ 38 * 3 ^ 6 * 5 * 7 * 11) * tableVOrderZ ≤
    n * twoBabyOrder) : 6589 < n := by
  unfold tableVOrderZ twoBabyOrder at h
  omega

end Arith

section Ctx

variable {G : Type} [Group G] {d₀ : B} {a z₀ x y : G}

structure Ctx (a z₀ x y : G) : Prop where
  hx : IsConj a x
  hy : IsConj a y
  hyx : y ≠ x
  hodd : Odd (orderOf (x * y))
  noB : ∀ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, ¬ IsConj z₀ w
  noA : ∀ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y},
    t ∈ twoANbr a x → t ∈ twoANbr a y → False

theorem Ctx.xx (c : Ctx a z₀ x y) (hG : GMSF1Type d₀ a z₀) : x * x = 1 :=
  sq_eq_one_of_isConj hG.1.1 c.hx

theorem Ctx.yy (c : Ctx a z₀ x y) (hG : GMSF1Type d₀ a z₀) : y * y = 1 :=
  sq_eq_one_of_isConj hG.1.1 c.hy

theorem Ctx.not_comm (c : Ctx a z₀ x y) (hG : GMSF1Type d₀ a z₀) : x * y ≠ y * x :=
  fun h => c.hyx (eq_of_mul_comm_of_odd (c.xx hG) (c.yy hG) h c.hodd).symm

end Ctx

section CtxFin

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem Ctx.of_not_mem
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hx : IsConj a x) (hy : IsConj a y) (hno : y ∉ gammaNbr a z₀ x) :
    Ctx a z₀ x y where
  hx := hx
  hy := hy
  hyx := fun h => hno (by rw [h]; exact self_mem_gammaNbr)
  hodd := by
    rcases Nat.even_or_odd (orderOf (x * y)) with hev | hodd
    · exact absurd (mem_gammaNbr_of_even I hG hx hy hev) hno
    · exact hodd
  noB := fun w hw hwB => hno (mem_gammaNbr_of_twoB I hG hx hy ⟨w, hw, hwB⟩)
  noA := fun t _ htx hty => hno (mem_gammaNbr_of_twoA I hG hCN hx hy ⟨t, htx, hty⟩)

theorem Ctx.claimA
    (c : Ctx a z₀ x y) (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {t : G}
    (ht : t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (ht2 : orderOf t = 2) : IsConj a t ∧ IsConj z₀ (x * t) ∧ IsConj z₀ (y * t) := by
  have hxx := c.xx hG
  have hyy := c.yy hG
  obtain ⟨htx, hty⟩ := Subgroup.mem_inf.mp ht
  have hxt : x * t = t * x := (mem_cent_iff.mp htx).symm
  have htA : IsConj a t :=
    (s31_five I.sls I.tableV I.leech hG I.leechInv ht2).resolve_right (c.noB t ht)
  obtain ⟨g, hgC, hg⟩ := exists_mem_centralizer_conj_of_odd (w := t) (x := x) (y := y)
    (cent_symm.mp htx) (cent_symm.mp hty) hxx hyy c.hodd
  have hgt : g * t * g⁻¹ = t := by
    rw [mem_cent_iff.mp hgC]
    group
  have hconj : g * (x * t) * g⁻¹ = y * t :=
    calc g * (x * t) * g⁻¹ = (g * x * g⁻¹) * (g * t * g⁻¹) := by group
      _ = y * t := by rw [hg, hgt]
  have hxt1 : x * t ≠ 1 := by
    intro h
    have hteq : t = x := by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hxx]
    apply c.not_comm hG
    rw [hteq] at hty
    exact mem_cent_iff.mp hty
  have hxtt : (x * t) * (x * t) = 1 :=
    calc (x * t) * (x * t) = x * (t * x) * t := by group
      _ = x * (x * t) * t := by rw [← hxt]
      _ = (x * x) * (t * t) := by group
      _ = 1 := by rw [hxx, mul_self_eq_one_of_orderOf ht2, one_mul]
  have hxt2 : orderOf (x * t) = 2 := orderOf_eq_two_of_mul_self hxtt hxt1
  have hyt : IsConj (x * t) (y * t) := by
    rw [← hconj]
    exact isConj_conj_self g (x * t)
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv hxt2 with hA | hB
  · exact (c.noA t ht ⟨htA, hA⟩ ⟨htA, hA.trans hyt⟩).elim
  · exact ⟨htA, hB, hB.trans hyt⟩

theorem card_centralizer_two
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x : G}
    (hx : IsConj a x) : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = twoBabyOrder := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  exact (card_centralizer_eq_of_isConj hx).symm.trans h.tableV.card_centralizer

theorem card_eightCent_three (hG : GMSF1Type d₀ a z₀) (hEC : EightCentOrders a z₀) {b t v : G}
    (hline : IsLineTriple a b t) (hv : IsConj a v) (hvb : v * b = b * v) (hvt : v * t = t * v)
    (h1 : IsConj z₀ (v * b)) (h2 : IsConj z₀ (v * t)) (h3 : IsConj z₀ (v * (b * t))) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t} ⊓
      Subgroup.centralizer {v}) = 2 ^ 35 * 3 ^ 4 * 5 * 7 := by
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  have hnv : ¬ IsConj z₀ v := fun h => hG.not_isConj (hv.trans h.symm)
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha hline.1
  have htt : t * t = 1 := sq_eq_one_of_isConj ha hline.2.1
  have hext : IsEightExt b t v :=
    ⟨sq_eq_one_of_isConj ha hv, hvb, hvt, ne_one_of_isConj ha hv, ne_of_isConj_mul hz hbb h1,
      ne_of_isConj_mul hz htt h2, ne_of_isConj_mul hz (sq_eq_one_of_isConj ha hline.2.2) h3⟩
  have hcount : twoBCount z₀ b t v = 3 := by
    classical
    unfold twoBCount
    rw [← mul_assoc] at h3
    simp only [List.filter_cons, List.filter_nil, decide_eq_false hnv, decide_eq_true h1,
      decide_eq_true h2, decide_eq_true h3]
    simp
  rw [hEC b t v hline hext, hcount]
  rfl

theorem card_eightCent_one (hG : GMSF1Type d₀ a z₀) (hEC : EightCentOrders a z₀) {b t v : G}
    (hline : IsLineTriple a b t) (hbt : b * t = t * b) (hv : IsConj a v) (hvb : v * b = b * v)
    (hvt : v * t = t * v) (h1 : IsConj z₀ (v * b)) (h2 : IsConj a (v * t)) :
    IsEightExt b t v ∧ twoBCount z₀ b t v = 1 ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t} ⊓
        Subgroup.centralizer {v}) = 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11 := by
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  have hnv : ¬ IsConj z₀ v := fun h => hG.not_isConj (hv.trans h.symm)
  have hnvt : ¬ IsConj z₀ (v * t) := fun h => hG.not_isConj (h2.trans h.symm)
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha hline.1
  have htt : t * t = 1 := sq_eq_one_of_isConj ha hline.2.1
  have hvbt : v ≠ b * t := by
    intro h
    rw [h] at h1
    have e : b * t * b = t :=
      calc b * t * b = t * b * b := by rw [hbt]
        _ = t := by rw [mul_assoc, hbb, mul_one]
    rw [e] at h1
    exact hG.not_isConj (hline.2.1.trans h1.symm)
  have hext : IsEightExt b t v :=
    ⟨sq_eq_one_of_isConj ha hv, hvb, hvt, ne_one_of_isConj ha hv, ne_of_isConj_mul hz hbb h1,
      ne_of_isConj_mul ha htt h2, hvbt⟩
  have hcard := hEC b t v hline hext
  have hcount : twoBCount z₀ b t v = 1 := by
    classical
    have hle : twoBCount z₀ b t v = 1 ∨ twoBCount z₀ b t v = 2 := by
      unfold twoBCount
      by_cases h3 : IsConj z₀ (v * b * t)
      · right
        simp only [List.filter_cons, List.filter_nil, decide_eq_false hnv, decide_eq_true h1,
          decide_eq_false hnvt, decide_eq_true h3]
        simp
      · left
        simp only [List.filter_cons, List.filter_nil, decide_eq_false hnv, decide_eq_true h1,
          decide_eq_false hnvt, decide_eq_false h3]
        simp
    rcases hle with h | h
    · exact h
    · exfalso
      rw [h] at hcard
      have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓
        Subgroup.centralizer {t} ⊓ Subgroup.centralizer {v}) := Nat.card_pos
      rw [hcard] at hpos
      exact absurd hpos (by simp [eightCentOrder])
  refine ⟨hext, hcount, ?_⟩
  rw [hcard, hcount]
  rfl

theorem Ctx.unique_involution
    (c : Ctx a z₀ x y) (I : GMSInterfaces d₀ G)
    (hG : GMSF1Type d₀ a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀) {b : G}
    (hb : b ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) (hbA : IsConj a b)
    {t : G}
    (ht : t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {b})
    (ht2 : orderOf t = 2) : t = b := by
  by_contra hne
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨htxy, htb⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨htx, hty⟩ := Subgroup.mem_inf.mp htxy
  obtain ⟨hbx, hby⟩ := Subgroup.mem_inf.mp hb
  have hbb : b * b = 1 := sq_eq_one_of_isConj ha hbA
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf ht2
  have hbt : b * t = t * b := (mem_cent_iff.mp htb).symm
  have hb2 : orderOf b = 2 := (orderOf_eq_of_isConj hbA).symm.trans ha
  have hbt2 : orderOf (b * t) = 2 := orderOf_mul_eq_two hbb htt hbt (Ne.symm hne)
  have hbtxy : b * t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} :=
    Subgroup.mul_mem _ hb htxy
  obtain ⟨-, hxb, -⟩ := c.claimA I hG hb hb2
  obtain ⟨htA, hxt, hyt⟩ := c.claimA I hG htxy ht2
  obtain ⟨hbtA, hxbt, hybt⟩ := c.claimA I hG hbtxy hbt2
  obtain ⟨-, -, hyb⟩ := c.claimA I hG hb hb2
  have hline : IsLineTriple a b t := ⟨hbA, htA, hbtA⟩
  have hnbr : t ∈ twoANbr a b := ⟨htA, hbtA⟩
  have hxb' : x * b = b * x := (mem_cent_iff.mp hbx).symm
  have hxt' : x * t = t * x := (mem_cent_iff.mp htx).symm
  have hyb' : y * b = b * y := (mem_cent_iff.mp hby).symm
  have hyt' : y * t = t * y := (mem_cent_iff.mp hty).symm
  have hcx := card_eightCent_three hG hEC hline c.hx hxb' hxt' hxb hxt hxbt
  have hcy := card_eightCent_three hG hEC hline c.hy hyb' hyt' hyb hyt hybt
  have hLcard : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t}) =
      tableVOrderB :=
    card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hbA hnbr
  set L : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t} with hL
  set H₁ : Subgroup G := L ⊓ Subgroup.centralizer {x} with hH₁
  set H₂ : Subgroup G := L ⊓ Subgroup.centralizer {y} with hH₂
  set X : Subgroup G := H₁ ⊓ H₂ with hX
  have hH₁L : H₁ ≤ L := inf_le_left
  have hH₂L : H₂ ≤ L := inf_le_left
  have hXH₁ : X ≤ H₁ := inf_le_left
  have hXH₂ : X ≤ H₂ := inf_le_right
  have hXL : X ≤ L := hXH₁.trans hH₁L
  have hXbig : 30995 < Nat.card X :=
    arith_eight_three _ (by
      have hprod := card_mul_card_le hH₁L hH₂L
      rwa [hcx, hcy, hLcard] at hprod)
  have hbX : b ∈ X :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mem_cent_iff.mpr rfl, mem_cent_iff.mpr hbt⟩,
        hbx⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
          ⟨mem_cent_iff.mpr rfl, mem_cent_iff.mpr hbt⟩, hby⟩⟩
  have htX : t ∈ X :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨htb, mem_cent_iff.mpr rfl⟩, htx⟩,
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨htb, mem_cent_iff.mpr rfl⟩, hty⟩⟩
  have hXxy : ∀ g ∈ X, g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} :=
    fun g hg => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hXH₁ hg)).2,
      (Subgroup.mem_inf.mp (hXH₂ hg)).2⟩
  by_cases h8 : 8 ∣ Nat.card X
  ·
    have hV4 : Nat.card (fourSub b t hbb htt hbt) = 2 ^ 2 := by
      rw [card_fourSub hbb htt hbt (ne_one_of_isConj ha hbA) (ne_one_of_isConj ha htA)
        (Ne.symm hne)]
      norm_num
    have hVX : fourSub b t hbb htt hbt ≤ X := by
      intro g hg
      rcases mem_fourSub.mp hg with h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact hbX
      · exact htX
      · exact Subgroup.mul_mem _ hbX htX
    obtain ⟨K', -, hK'X, hK'c, hK'sq⟩ :=
      exists_sq_mem_of_card_dvd hVX hV4 (by simpa using h8)
    have hK'1 : ∀ g ∈ K', g * g = 1 := by
      intro g hg
      refine hES b t hbA hnbr g (hXL (hK'X hg)) ?_
      rcases mem_fourSub.mp (hK'sq g hg) with h | h | h | h <;> simp [h]
    obtain ⟨g, hgK, hg1, hgA⟩ := s33 I.sls I.tableV I.leech hG I.tableIV K'
      (by simpa using hK'c) hK'1
    exact hgA (c.claimA I hG (hXxy g (hK'X hgK))
      (orderOf_eq_two_of_mul_self (hK'1 g hgK) hg1)).1
  ·
    have hdvd : Nat.card X ∣ 2 ^ 35 * (3 ^ 4 * 5 * 7) := by
      have := Subgroup.card_dvd_of_le hXH₁
      rw [hcx] at this
      simpa [mul_assoc] using this
    have hle := le_two_pow_mul_of_dvd (k := 2) (by norm_num) hdvd (by simpa using h8)
    omega

theorem Ctx.false_of_unique
    (c : Ctx a z₀ x y) (I : GMSInterfaces d₀ G)
    (hG : GMSF1Type d₀ a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) {b : G}
    (hb : b ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) (hbA : IsConj a b)
    (huniq : ∀ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {b}, orderOf t = 2 → t = b) : False := by
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨hbx, hby⟩ := Subgroup.mem_inf.mp hb
  have hb2 : orderOf b = 2 := (orderOf_eq_of_isConj hbA).symm.trans ha
  obtain ⟨-, hxb, hyb⟩ := c.claimA I hG hb hb2
  have hby' : b * y = y * b := mem_cent_iff.mp hby
  have hbxB : b ∈ twoBNbr a z₀ x := ⟨hbA, hxb⟩
  have hbyB : y ∈ twoBNbr a z₀ b := ⟨c.hy, by rw [hby']; exact hyb⟩
  have h9200 := ncard_commonNbr_twoB I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
    I.leechPair hG c.hx hbxB
  obtain ⟨t₁, ht₁x, ht₁b⟩ : (twoANbr a x ∩ twoANbr a b).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  have hxt₁ : x * t₁ = t₁ * x := mul_comm_of_isConj_mul ha c.hx ht₁x.1 ht₁x.2
  have hbt₁ : b * t₁ = t₁ * b := mul_comm_of_isConj_mul ha hbA ht₁b.1 ht₁b.2
  have hxb' : x * b = b * x := (mem_cent_iff.mp hbx).symm
  have hline : IsLineTriple a b t₁ := ⟨hbA, ht₁b.1, ht₁b.2⟩
  obtain ⟨hext, hcount, hA⟩ := card_eightCent_one hG hEC hline hbt₁ c.hx hxb' hxt₁ hxb ht₁x.2
  have hBcard : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y}) =
      tableVOrderZ := card_centralizer_inf_of_mem_twoBNbr I.sls I.tableV I.leech hG hbA hbyB
  have hLcard := card_centralizer_two I hG hbA
  set A : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t₁} ⊓
    Subgroup.centralizer {x} with hAdef
  set B : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} with hBdef
  set X : Subgroup G := A ⊓ B with hX
  have hAL : A ≤ Subgroup.centralizer ({b} : Set G) := inf_le_left.trans inf_le_left
  have hBL : B ≤ Subgroup.centralizer ({b} : Set G) := inf_le_left
  have hXA : X ≤ A := inf_le_left
  have hXB : X ≤ B := inf_le_right
  have hXbig : 6589 < Nat.card X :=
    arith_eight_one _ (by
      have hprod := card_mul_card_le hAL hBL
      rwa [hA, hBcard, hLcard] at hprod)
  have hbX : b ∈ X :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mem_cent_iff.mpr rfl,
      mem_cent_iff.mpr hbt₁⟩, hbx⟩, Subgroup.mem_inf.mpr ⟨mem_cent_iff.mpr rfl, hby⟩⟩
  have hnotfour : ¬ 4 ∣ Nat.card X := by
    intro h4
    have hVX : Subgroup.zpowers b ≤ X := Subgroup.zpowers_le.mpr hbX
    obtain ⟨K', -, hK'X, hK'c, hK'sq⟩ := exists_sq_mem_of_card_dvd hVX (n := 1)
      (by rw [Nat.card_zpowers, hb2]; norm_num) (by simpa using h4)
    obtain ⟨g, hgK, hgV⟩ : ∃ g ∈ K', g ∉ Subgroup.zpowers b := by
      by_contra hall
      push Not at hall
      have hle := Subgroup.card_le_of_le (fun g hg => hall g hg : K' ≤ Subgroup.zpowers b)
      rw [hK'c, Nat.card_zpowers, hb2] at hle
      norm_num at hle
    have hgX := hK'X hgK
    have hgA : g ∈ A := hXA hgX
    have hgB : g ∈ B := hXB hgX
    have hgL : g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {t₁} :=
      (Subgroup.mem_inf.mp hgA).1
    have hsq : g * g ∈ ({1, b, t₁, b * t₁} : Set G) := by
      rcases (mem_zpowers_of_orderOf_two hb2).mp (hK'sq g hgK) with h | h <;> simp [h]
    have hg2 : g * g = 1 := hES b t₁ hbA ht₁b g hgL hsq
    have hg1 : g ≠ 1 := fun h => hgV (h ▸ one_mem _)
    have hgord : orderOf g = 2 := orderOf_eq_two_of_mul_self hg2 hg1
    have hgmem : g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
        Subgroup.centralizer {b} :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hgA).2,
        (Subgroup.mem_inf.mp hgB).2⟩, (Subgroup.mem_inf.mp hgB).1⟩
    exact hgV (huniq g hgmem hgord ▸ Subgroup.mem_zpowers b)
  have hdvd2 : 2 ∣ Nat.card X := by
    have := orderOf_dvd_natCard (⟨b, hbX⟩ : X)
    rwa [Subgroup.orderOf_mk, hb2] at this
  obtain ⟨N, hNX, hNc⟩ := exists_subgroup_card_mul_two hdvd2 hnotfour
  have hNodd : Odd (Nat.card N) := by
    rcases Nat.even_or_odd (Nat.card N) with ⟨k, hk⟩ | h
    · exact absurd ⟨k, by omega⟩ hnotfour
    · exact h
  have hlt := hE1 b t₁ x hline hext hcount N (hNX.trans hXA) hNodd
  omega

end CtxFin

end S37

section Headline

open S37

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem s371_two
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hCN : CommonNbrTwoB a z₀)
    (hES : EdgeSquares a) (hEC : EightCentOrders a z₀) (hE1 : EightOneOddOrder a z₀)
    (hx : IsConj a x) (hy : IsConj a y)
    (h : ∃ b ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj a b) :
    y ∈ gammaNbr a z₀ x := by
  by_contra hno
  obtain ⟨b, hb, hbA⟩ := h
  have c : Ctx a z₀ x y := Ctx.of_not_mem I hG hCN hx hy hno
  exact c.false_of_unique I hG hES hEC hE1 hb hbA
    (fun t ht ht2 => c.unique_involution I hG hES hEC hb hbA ht ht2)

end Headline

end CFSG.Monster.GMS

module

public import CFSG.RankThree.GF2n.Tim77Prop24Core
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.CGT.Timmesfeld75.Cfg214Gen

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G] [Finite G]

theorem conjSubgroup_eq_of_inf_ne_bot {T : Subgroup G} (hT : IsTI T) {g h : G}
    (hne : conjSubgroup g T ⊓ conjSubgroup h T ≠ ⊥) : conjSubgroup g T = conjSubgroup h T := by
  have hTI : IsTI (conjSubgroup h T) := isTI_conjSubgroup hT h
  have e : conjSubgroup g T = conjSubgroup (g * h⁻¹) (conjSubgroup h T) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  rw [e] at hne ⊢
  exact conjSubgroup_eq_of_isTI hTI (by rwa [inf_comm] at hne)

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

omit [Finite G] in
theorem A_ne_bot : A ≠ ⊥ := fun h => S.ne_bot (le_bot_iff.mp (h ▸ S.L_le))

omit [Finite G] in
theorem Ab_ne_bot : Ab ≠ ⊥ := by
  obtain ⟨g, hg⟩ := S.conj
  intro h
  apply S.A_ne_bot
  rw [eq_bot_iff]
  intro a ha
  have : g * a * g⁻¹ ∈ Ab := by
    rw [hg, mem_conjSubgroup]
    simpa [mul_assoc] using ha
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have h2 : a = g⁻¹ * (g * a * g⁻¹) * g := by group
  rw [h2, this]
  group

theorem Lb_ne_bot : Lb ≠ ⊥ := by
  obtain ⟨⟨l, hl⟩, hl1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.ne_bot
  have hl1 : l ≠ 1 := fun h => hl1' (Subtype.ext h)
  obtain ⟨⟨b, hb⟩, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.Ab_ne_bot
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  intro hbot
  have hc := S.commutator_mem_Lb hb hl
  rw [hbot, Subgroup.mem_bot] at hc
  have hbl : b * l = l * b := by
    calc b * l = b * l * b⁻¹ * l⁻¹ * (l * b) := by group
      _ = l * b := by rw [hc, one_mul]
  have hbLb : b ∈ Lb :=
    S.mem_Lb.mpr ⟨hb, mem_normalizer_of_commute_of_isTI S.ti (S.L_le hl) hl1 hbl⟩
  rw [hbot, Subgroup.mem_bot] at hbLb
  exact hb1 hbLb

theorem Lb_ne : Lb ≠ Ab := by
  intro h
  obtain ⟨g, hg⟩ := S.conj
  have hle : conjSubgroup g A ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hg]
    intro b hb
    rw [← h] at hb
    exact (S.mem_Lb.mp hb).2
  have hel := tim77_2_3 S.elem S.ti hle
  apply S.ne
  refine le_antisymm S.L_le fun a ha => S.mem_L.mpr ⟨ha, ?_⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hxA : x ∈ A ⊔ conjSubgroup g A := Subgroup.mem_sup_right (hg ▸ hx)
    have hc := congrArg Subtype.val (hel.1.is_comm.comm ⟨a, Subgroup.mem_sup_left ha⟩ ⟨x, hxA⟩)
    have hc' : a * x = x * a := hc
    rw [hc', mul_inv_cancel_right]
    exact hx
  · have hxA : a * x * a⁻¹ ∈ A ⊔ conjSubgroup g A := Subgroup.mem_sup_right (hg ▸ hx)
    have hc := congrArg Subtype.val
      (hel.1.is_comm.comm ⟨a, Subgroup.mem_sup_left ha⟩ ⟨a * x * a⁻¹, hxA⟩)
    have hc' : a * (a * x * a⁻¹) = a * x * a⁻¹ * a := hc
    have : x = a * x * a⁻¹ := by
      have h1 : a * (a * x * a⁻¹) * a⁻¹ = a * x * a⁻¹ := by rw [hc', mul_inv_cancel_right]
      have h2 : a * a = 1 := S.sq_A ha
      calc x = a * a * x * (a * a)⁻¹ := by rw [h2, one_mul, inv_one, mul_one]
        _ = a * (a * x * a⁻¹) * a⁻¹ := by group
        _ = a * x * a⁻¹ := h1
    rw [this]
    exact hx

theorem symm : Prop24Setup Ab A Lb L M where
  elem := S.elem_Ab
  ti := S.ti_Ab
  conj := by
    obtain ⟨g, hg⟩ := S.conj
    exact ⟨g⁻¹, by rw [hg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]⟩
  hL := S.hLb
  hLb := S.hL
  hM := S.hM.trans (sup_comm L Lb)
  ne_bot := S.Lb_ne_bot
  ne := S.Lb_ne

theorem sup_le_normalizer_M : A ⊔ Ab ≤ Subgroup.normalizer (M : Set G) :=
  sup_le S.A_le_normalizer_M S.Ab_le_normalizer_M

theorem conj_eq_of_commutator_mem {x a b : G} (hx : x ∈ Subgroup.normalizer (M : Set G))
    (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    (hc : (x⁻¹ * a * x) * b * (x⁻¹ * a * x)⁻¹ * b⁻¹ ∈ M) : conjSubgroup x⁻¹ A = Ab := by
  obtain ⟨g₀, hg₀⟩ := S.conj
  have hsuff : ∀ y, y ∈ conjSubgroup x⁻¹ A → y ∈ Ab → y ≠ 1 → conjSubgroup x⁻¹ A = Ab := by
    intro y hy1 hy2 hy
    rw [hg₀] at hy2 ⊢
    refine conjSubgroup_eq_of_inf_ne_bot S.ti fun hbot => hy ?_
    have : y ∈ conjSubgroup x⁻¹ A ⊓ conjSubgroup g₀ A := Subgroup.mem_inf.mpr ⟨hy1, hy2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hmemx : ∀ y, x * y * x⁻¹ ∈ A → y ∈ conjSubgroup x⁻¹ A := fun y hy => by
    rw [mem_conjSubgroup, inv_inv]
    exact hy
  set a' := x⁻¹ * a * x with ha'
  have ha'2 : a' * a' = 1 := by
    rw [ha', show x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x by group, S.sq_A ha]
    group
  have hb2 : b * b = 1 := S.sq_Ab hb
  set c := a' * b * a'⁻¹ * b⁻¹ with hcdef
  have hcc : c * c = 1 := by rw [← sq]; exact S.isElemAbelian_M.2 c hc
  obtain ⟨ha'c, hcb⟩ := commute_commutator_of_involutions ha'2 hb2 hcdef hcc
  have hcLb : c ∈ Lb := S.symm.mem_L_of_commute_M hb hbL hc hcb.symm
  have hcL : x * c * x⁻¹ ∈ L := S.conj_mem_L_of_commute_M hx ha haL hc ha'c.symm
  by_cases hc1 : c = 1
  ·
    have ha'b : a' * b = b * a' := by
      calc a' * b = c * (b * a') := by rw [hcdef]; group
        _ = b * a' := by rw [hc1, one_mul]
    have hb1 : b ≠ 1 := fun h => hbL (h ▸ Lb.one_mem)
    have ha'N : a' ∈ Subgroup.normalizer (Ab : Set G) :=
      mem_normalizer_of_commute_of_isTI S.ti_Ab hb hb1 ha'b
    have ha'M : a' ∈ Subgroup.normalizer (M : Set G) := by
      rw [ha']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
        (S.A_le_normalizer_M ha)) hx
    have hLbeq : Lb = Ab ⊓ M := S.symm.inf_M.symm
    have ha'NLb : a' ∈ Subgroup.normalizer (Lb : Set G) := by
      rw [hLbeq]
      exact mem_normalizer_inf ha'N ha'M
    have hLbe : Assembly.IsElemAbelian 2 Lb := by
      refine ⟨⟨⟨fun u v => Subtype.ext (S.comm_M (S.Lb_le_M u.2) (S.Lb_le_M v.2))⟩⟩,
        fun u hu => S.elem_Ab.2 u (S.Lb_le hu)⟩
    obtain ⟨y, hy, hy1, hya'⟩ := exists_ne_one_commute hLbe S.Lb_ne_bot ha'NLb ha'2
    have hyL : x * y * x⁻¹ ∈ L :=
      S.conj_mem_L_of_commute_M hx ha haL (S.Lb_le_M hy) hya'.symm
    exact hsuff y (hmemx y (S.L_le hyL)) (S.Lb_le hy) hy1
  · exact hsuff c (hmemx c (S.L_le hcL)) (S.Lb_le hcLb) hc1

theorem exists_conj_eq : ∃ x ∈ A ⊔ Ab, Ab = conjSubgroup x A := by
  have hXN := S.sup_le_normalizer_M
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have haa : a * a = 1 := S.sq_A ha
  have hbb : b * b = 1 := S.sq_Ab hb
  have haX : a ∈ A ⊔ Ab := Subgroup.mem_sup_left ha
  have hbX : b ∈ A ⊔ Ab := Subgroup.mem_sup_right hb
  have hclX : Subgroup.closure ({b, a} : Set G) ≤ A ⊔ Ab := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hbX, haX⟩
  have hcrit : ∀ d ∈ A ⊔ Ab, (d⁻¹ * a * d) * b = b * (d⁻¹ * a * d) →
      ∃ x ∈ A ⊔ Ab, Ab = conjSubgroup x A := by
    intro d hd hcomm
    refine ⟨d⁻¹, (A ⊔ Ab).inv_mem hd, (S.conj_eq_of_commutator_mem (hXN hd) ha haL hb hbL ?_).symm⟩
    rw [show (d⁻¹ * a * d) * b * (d⁻¹ * a * d)⁻¹ * b⁻¹ =
      ((d⁻¹ * a * d) * b) * (b * (d⁻¹ * a * d))⁻¹ by group, hcomm, mul_inv_cancel]
    exact M.one_mem
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | ⟨k, hk⟩
  · have hm0 : 0 < m := by
      have := orderOf_pos (a * b)
      omega
    have hord : orderOf (b * a) = 2 * m := by
      have h1 : b * a = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
      rw [h1, orderOf_inv]
      omega
    obtain ⟨z, hzz, hz1, hbz, haz, hconjz⟩ := dihedral_central_of_even_order_mem hbb haa hm0 hord
    rcases hconjz with ⟨g, hg, hgz⟩ | ⟨g, hg, hgz⟩
    ·
      refine hcrit g⁻¹ ((A ⊔ Ab).inv_mem (hclX hg)) ?_
      have h1 : a * (g⁻¹ * b * g) = (g⁻¹ * b * g) * a := by
        rw [← hgz]
        calc a * (a * z) = a * (z * a) := by rw [haz]
          _ = a * z * a := by group
      rw [inv_inv]
      calc g * a * g⁻¹ * b = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by rw [h1]
        _ = b * (g * a * g⁻¹) := by group
    ·
      exfalso
      have hcom : a * (g⁻¹ * a * g) * a⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ M := by
        rw [← hgz]
        have e : a * (a * z) * a⁻¹ * (a * z)⁻¹ = 1 := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa]
          calc a * (a * z) * a * (z⁻¹ * a) = a * (a * (z * a)) * z⁻¹ * a := by group
            _ = a * (a * (a * z)) * z⁻¹ * a := by rw [haz]
            _ = 1 := by
              rw [show a * (a * (a * z)) * z⁻¹ * a = (a * a) * (a * a) by group, haa, one_mul]
        rw [e]
        exact M.one_mem
      have hgA := S.conj_mem_of_commutator_mem (hXN (hclX hg)) ha haL ha haL hcom
      rw [← hgz] at hgA
      have hzA : z ∈ A := by
        have := A.mul_mem (A.inv_mem ha) hgA
        rwa [inv_mul_cancel_left] at this
      exact hbL (S.mem_Lb.mpr ⟨hb, mem_normalizer_of_commute_of_isTI S.ti hzA hz1 hbz⟩)
  ·
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts haa hbb) (k + 1)
    have hpow : (a * b) ^ (2 * (k + 1)) = a * b := by
      rw [show 2 * (k + 1) = orderOf (a * b) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hpow] at h1
    have hbconj : ((a * b) ^ (k + 1))⁻¹ * a * (a * b) ^ (k + 1) = b := by
      rw [h1]
      exact (invol_eq_inv_mul_mul hbb).symm
    have hd : (a * b) ^ (k + 1) ∈ A ⊔ Ab := (A ⊔ Ab).pow_mem ((A ⊔ Ab).mul_mem haX hbX) _
    refine hcrit _ hd ?_
    rw [hbconj]

theorem odd_orderOf_mul {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb) :
    Odd (orderOf (a * b)) := by
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  exfalso
  have hXN := S.sup_le_normalizer_M
  have haa : a * a = 1 := S.sq_A ha
  have hbb : b * b = 1 := S.sq_Ab hb
  have hm0 : 0 < m := by
    have := orderOf_pos (a * b)
    omega
  have hord : orderOf (b * a) = 2 * m := by
    have h1 : b * a = (a * b)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
    rw [h1, orderOf_inv]
    omega
  have hclX : Subgroup.closure ({b, a} : Set G) ≤ A ⊔ Ab := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Subgroup.mem_sup_right hb, Subgroup.mem_sup_left ha⟩
  obtain ⟨z, hzz, hz1, hbz, haz, hconjz⟩ := dihedral_central_of_even_order_mem hbb haa hm0 hord
  obtain ⟨t, ht, htL, h, hhX, hth⟩ : ∃ t ∈ A, t ∉ L ∧ ∃ h ∈ A ⊔ Ab, a * z = h⁻¹ * t * h := by
    rcases hconjz with ⟨g, hg, hgz⟩ | ⟨g, hg, hgz⟩
    · obtain ⟨x, hxX, hx⟩ := S.exists_conj_eq
      have hbx : x⁻¹ * b * x ∈ A := by
        have : b ∈ conjSubgroup x A := hx ▸ hb
        exact mem_conjSubgroup.mp this
      refine ⟨x⁻¹ * b * x, hbx, fun hL => hbL ?_, x⁻¹ * g, (A ⊔ Ab).mul_mem
        ((A ⊔ Ab).inv_mem hxX) (hclX hg), by rw [hgz]; group⟩
      have hM : b ∈ M := by
        have := (Subgroup.mem_normalizer_iff.mp (hXN hxX) _).mp (S.L_le_M hL)
        rwa [show x * (x⁻¹ * b * x) * x⁻¹ = b by group] at this
      rw [← S.symm.inf_M]
      exact Subgroup.mem_inf.mpr ⟨hb, hM⟩
    · exact ⟨a, ha, haL, g, hclX hg, hgz⟩
  have hcom : a * (h⁻¹ * t * h) * a⁻¹ * (h⁻¹ * t * h)⁻¹ ∈ M := by
    rw [← hth]
    have e : a * (a * z) * a⁻¹ * (a * z)⁻¹ = 1 := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa]
      calc a * (a * z) * a * (z⁻¹ * a) = a * (a * (z * a)) * z⁻¹ * a := by group
        _ = a * (a * (a * z)) * z⁻¹ * a := by rw [haz]
        _ = 1 := by
          rw [show a * (a * (a * z)) * z⁻¹ * a = (a * a) * (a * a) by group, haa, one_mul]
    rw [e]
    exact M.one_mem
  have hA := S.conj_mem_of_commutator_mem (hXN hhX) ha haL ht htL hcom
  rw [← hth] at hA
  have hzA : z ∈ A := by
    have := A.mul_mem (A.inv_mem ha) hA
    rwa [inv_mul_cancel_left] at this
  exact hbL (S.mem_Lb.mpr ⟨hb, mem_normalizer_of_commute_of_isTI S.ti hzA hz1 hbz⟩)

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77

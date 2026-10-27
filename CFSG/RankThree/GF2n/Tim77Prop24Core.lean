module

public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

theorem mem_normalizer_of_commute_of_isTI [Finite G] {T : Subgroup G} (hT : IsTI T) {c x : G}
    (hx : x ∈ T) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.normalizer (T : Set G) := by
  rw [← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTI hT fun h => hx1 ?_
  have hmem : x ∈ T ⊓ conjSubgroup c T := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup, show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx]; group]
    exact hx
  rw [h] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem commutator_mem_of_isTI [Finite G] {T T' : Subgroup G}
    (hT : Assembly.IsElemAbelian 2 T) (hT' : Assembly.IsElemAbelian 2 T') (hTI' : IsTI T')
    {a l : G} (ha : a ∈ T) (hl : l ∈ T') (hlN : l ∈ Subgroup.normalizer (T : Set G)) :
    a * l * a⁻¹ * l⁻¹ ∈ T ∧ a * l * a⁻¹ * l⁻¹ ∈ Subgroup.normalizer (T' : Set G) := by
  have hll : l * l = 1 := by rw [← sq]; exact hT'.2 l hl
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT.2 a ha)
  set a' := l * a * l with ha'def
  have ha' : a' ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp hlN a).mp ha
    rwa [hlinv] at this
  have hc_eq : a * l * a⁻¹ * l⁻¹ = a * a' := by rw [hainv, hlinv, ha'def]; group
  rw [hc_eq]
  refine ⟨T.mul_mem ha ha', ?_⟩
  by_cases hl1 : l = 1
  · have : a' = a := by rw [ha'def, hl1]; group
    rw [this, show a * a = 1 by rw [← sq]; exact hT.2 a ha]
    exact Subgroup.one_mem _
  refine mem_normalizer_of_commute_of_isTI hTI' hl hl1 ?_
  have hcomm : a' * a = a * a' :=
    congrArg Subtype.val (hT.1.is_comm.comm ⟨a', ha'⟩ ⟨a, ha⟩)
  have h1 : l * a' * l = a := by
    rw [ha'def, show l * (l * a * l) * l = (l * l) * a * (l * l) by group, hll, one_mul,
      mul_one]
  have h2 : l * (a * a') * l = a * a' := by
    calc l * (a * a') * l = (l * a * l) * (l * a' * l) := by
          rw [show (l * a * l) * (l * a' * l) = l * a * (l * l) * a' * l by group, hll, mul_one]
          group
      _ = a' * a := by rw [← ha'def, h1]
      _ = a * a' := hcomm
  calc a * a' * l = (l * (a * a') * l) * l := by rw [h2]
    _ = l * (a * a') * (l * l) := by group
    _ = l * (a * a') := by rw [hll, mul_one]

theorem exists_ne_one_commute [Finite G] {U : Subgroup G} (hU : Assembly.IsElemAbelian 2 U)
    (hU1 : U ≠ ⊥) {t : G} (htN : t ∈ Subgroup.normalizer (U : Set G)) (ht : t * t = 1) :
    ∃ x ∈ U, x ≠ 1 ∧ t * x = x * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨⟨u, hu⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  have hσ : ∀ x ∈ U, t * x * t⁻¹ ∈ U := fun x hx => (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  by_cases h : u * (t * u * t⁻¹) = 1
  ·
    refine ⟨u, hu, hu1, ?_⟩
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU.2 u hu)
    have : t * u * t⁻¹ = u := by
      have h' := eq_inv_of_mul_eq_one_right h
      rwa [huinv] at h'
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [this]
  · refine ⟨u * (t * u * t⁻¹), U.mul_mem hu (hσ u hu), h, ?_⟩
    have e : t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * u := by
      rw [htinv]
      calc t * (u * (t * u * t)) * t = t * u * t * u * (t * t) := by group
        _ = t * u * t * u := by rw [ht, mul_one]
    have e2 : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
      rw [e, hcomm _ (hσ u hu) u hu]
    calc t * (u * (t * u * t⁻¹)) = t * (u * (t * u * t⁻¹)) * t⁻¹ * t := by group
      _ = u * (t * u * t⁻¹) * t := by rw [e2]

theorem commute_commutator_of_involutions {t τ c : G} (ht : t * t = 1) (hτ : τ * τ = 1)
    (hc : c = t * τ * t⁻¹ * τ⁻¹) (hcc : c * c = 1) : t * c = c * t ∧ c * τ = τ * c := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcinv' : c⁻¹ = τ * t * τ * t := by
    rw [hc, htinv, hτinv]
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htinv, hτinv]
    group
  have e1 : t * c * t⁻¹ = τ * t * τ * t := by
    rw [hc, htinv, hτinv]
    calc t * (t * τ * t * τ) * t = (t * t) * τ * t * τ * t := by group
      _ = τ * t * τ * t := by rw [ht, one_mul]
  have e2 : τ * c * τ⁻¹ = τ * t * τ * t := by
    rw [hc, htinv, hτinv]
    calc τ * (t * τ * t * τ) * τ = τ * t * τ * t * (τ * τ) := by group
      _ = τ * t * τ * t := by rw [hτ, mul_one]
  constructor
  · have e : t * c * t⁻¹ = c := by rw [e1, ← hcinv', hcinv]
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [e]
  · have e : τ * c * τ⁻¹ = c := by rw [e2, ← hcinv', hcinv]
    calc c * τ = (τ * c * τ⁻¹) * τ := by rw [e]
      _ = τ * c := by group

structure Prop24Setup (A Ab L Lb M : Subgroup G) : Prop where
  elem : Assembly.IsElemAbelian 2 A
  ti : IsTI A
  conj : ∃ g : G, Ab = conjSubgroup g A
  hL : L = A ⊓ Subgroup.normalizer (Ab : Set G)
  hLb : Lb = Ab ⊓ Subgroup.normalizer (A : Set G)
  hM : M = L ⊔ Lb
  ne_bot : L ≠ ⊥
  ne : L ≠ A

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem mem_L {x : G} : x ∈ L ↔ x ∈ A ∧ x ∈ Subgroup.normalizer (Ab : Set G) := by
  rw [S.hL, Subgroup.mem_inf]

theorem mem_Lb {x : G} : x ∈ Lb ↔ x ∈ Ab ∧ x ∈ Subgroup.normalizer (A : Set G) := by
  rw [S.hLb, Subgroup.mem_inf]

theorem L_le : L ≤ A := fun _ hx => (S.mem_L.mp hx).1

theorem Lb_le : Lb ≤ Ab := fun _ hx => (S.mem_Lb.mp hx).1

theorem elem_Ab : Assembly.IsElemAbelian 2 Ab := by
  obtain ⟨g, rfl⟩ := S.conj
  obtain ⟨hc, h2⟩ := S.elem
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have h := congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ h
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h2 x' hx', map_one]

theorem ti_Ab : IsTI Ab := by
  obtain ⟨g, rfl⟩ := S.conj
  exact isTI_conjSubgroup S.ti g

theorem comm_A {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (S.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem sq_A {a : G} (ha : a ∈ A) : a * a = 1 := by
  rw [← sq]
  exact S.elem.2 a ha

theorem sq_Ab {a : G} (ha : a ∈ Ab) : a * a = 1 := by
  rw [← sq]
  exact S.elem_Ab.2 a ha

theorem Ab_ne : Ab ≠ A := by
  intro h
  apply S.ne
  rw [S.hL, h]
  exact le_antisymm inf_le_left (le_inf le_rfl Subgroup.le_normalizer)

theorem mul_mem_M {l lb : G} (hl : l ∈ L) (hlb : lb ∈ Lb) : l * lb ∈ M := by
  rw [S.hM]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hlb)

theorem L_le_M : L ≤ M := S.hM ▸ le_sup_left

theorem Lb_le_M : Lb ≤ M := S.hM ▸ le_sup_right

variable [Finite G]

theorem inf_eq_bot : A ⊓ Ab = ⊥ := by
  obtain ⟨g, hg⟩ := S.conj
  rw [hg]
  exact inf_conjSubgroup_eq_bot_of_isTI S.ti (hg ▸ S.Ab_ne)

theorem mem_Lb_of_commute {c a : G} (hc : c ∈ Ab) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hca : c * a = a * c) : c ∈ Lb :=
  S.mem_Lb.mpr ⟨hc, mem_normalizer_of_commute_of_isTI S.ti ha ha1 hca⟩

theorem mem_L_of_commute {c a : G} (hc : c ∈ A) (ha : a ∈ Ab) (ha1 : a ≠ 1)
    (hca : c * a = a * c) : c ∈ L :=
  S.mem_L.mpr ⟨hc, mem_normalizer_of_commute_of_isTI S.ti_Ab ha ha1 hca⟩

theorem commutator_mem_L {a lb : G} (ha : a ∈ A) (hlb : lb ∈ Lb) :
    a * lb * a⁻¹ * lb⁻¹ ∈ L := by
  obtain ⟨hlbAb, hlbN⟩ := S.mem_Lb.mp hlb
  obtain ⟨h1, h2⟩ := commutator_mem_of_isTI S.elem S.elem_Ab S.ti_Ab ha hlbAb hlbN
  exact S.mem_L.mpr ⟨h1, h2⟩

theorem commutator_mem_Lb {ab l : G} (hab : ab ∈ Ab) (hl : l ∈ L) :
    ab * l * ab⁻¹ * l⁻¹ ∈ Lb := by
  obtain ⟨hlA, hlN⟩ := S.mem_L.mp hl
  obtain ⟨h1, h2⟩ := commutator_mem_of_isTI S.elem_Ab S.elem S.ti hab hlA hlN
  exact S.mem_Lb.mpr ⟨h1, h2⟩

theorem comm_L_Lb {l lb : G} (hl : l ∈ L) (hlb : lb ∈ Lb) : l * lb = lb * l := by
  have h1 : l * lb * l⁻¹ * lb⁻¹ ∈ L := S.commutator_mem_L (S.L_le hl) hlb
  have h2 : l * lb * l⁻¹ * lb⁻¹ ∈ Ab := by
    have h3 : l * lb * l⁻¹ ∈ Ab :=
      (Subgroup.mem_normalizer_iff.mp (S.mem_L.mp hl).2 lb).mp (S.Lb_le hlb)
    exact Ab.mul_mem h3 (Ab.inv_mem (S.Lb_le hlb))
  have h4 : l * lb * l⁻¹ * lb⁻¹ ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le h1, h2⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at h4
  calc l * lb = l * lb * l⁻¹ * lb⁻¹ * (lb * l) := by group
    _ = lb * l := by rw [h4, one_mul]

theorem exists_mul_of_mem_M {x : G} (hx : x ∈ M) : ∃ l ∈ L, ∃ lb ∈ Lb, x = l * lb := by
  rw [S.hM] at hx
  exact exists_mul_of_mem_sup (le_normalizer_of_comm fun a ha b hb => (S.comm_L_Lb hb ha).symm)
    hx

theorem isElemAbelian_M : Assembly.IsElemAbelian 2 M := by
  have hcM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
    obtain ⟨l', hl', lb', hlb', rfl⟩ := S.exists_mul_of_mem_M hy
    have e1 := S.comm_A (S.L_le hl) (S.L_le hl')
    have e2 := (S.elem_Ab).1.is_comm.comm (⟨lb, S.Lb_le hlb⟩ : Ab) ⟨lb', S.Lb_le hlb'⟩
    have e2' : lb * lb' = lb' * lb := congrArg Subtype.val e2
    have e3 := S.comm_L_Lb hl' hlb
    have e4 := S.comm_L_Lb hl hlb'
    calc l * lb * (l' * lb') = l * (lb * l') * lb' := by group
      _ = l * (l' * lb) * lb' := by rw [e3]
      _ = (l * l') * (lb * lb') := by group
      _ = (l' * l) * (lb' * lb) := by rw [e1, e2']
      _ = l' * (l * lb') * lb := by group
      _ = l' * (lb' * l) * lb := by rw [e4]
      _ = l' * lb' * (l * lb) := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcM a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
  rw [sq, show l * lb * (l * lb) = l * (lb * l) * lb by group, ← S.comm_L_Lb hl hlb,
    show l * (l * lb) * lb = (l * l) * (lb * lb) by group, S.sq_A (S.L_le hl),
    S.sq_Ab (S.Lb_le hlb), one_mul]

theorem comm_M {x y : G} (hx : x ∈ M) (hy : y ∈ M) : x * y = y * x :=
  congrArg Subtype.val (S.isElemAbelian_M.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem A_le_normalizer_M : A ≤ Subgroup.normalizer (M : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ M, a * x * a⁻¹ ∈ M := by
    intro a ha x hx
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
    have hc := S.commutator_mem_L ha hlb
    have e : a * (l * lb) * a⁻¹ = (l * (a * lb * a⁻¹ * lb⁻¹)) * lb := by
      have := S.comm_A ha (S.L_le hl)
      calc a * (l * lb) * a⁻¹ = (a * l) * lb * a⁻¹ := by group
        _ = (l * a) * lb * a⁻¹ := by rw [this]
        _ = (l * (a * lb * a⁻¹ * lb⁻¹)) * lb := by group
    rw [e]
    exact S.mul_mem_M (L.mul_mem hl hc) hlb
  intro a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S.sq_A ha)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key a ha x, fun hx => ?_⟩
  have := key a ha _ hx
  rwa [show a * (a * x * a⁻¹) * a⁻¹ = x by rw [hainv]; rw [← mul_assoc, ← mul_assoc,
    S.sq_A ha, one_mul, mul_assoc, S.sq_A ha, mul_one]] at this

theorem Ab_le_normalizer_M : Ab ≤ Subgroup.normalizer (M : Set G) := by
  have key : ∀ a ∈ Ab, ∀ x ∈ M, a * x * a⁻¹ ∈ M := by
    intro a ha x hx
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
    have hc := S.commutator_mem_Lb ha hl
    have hcomm : a * lb = lb * a :=
      congrArg Subtype.val (S.elem_Ab.1.is_comm.comm ⟨a, ha⟩ ⟨lb, S.Lb_le hlb⟩)
    have e : a * (l * lb) * a⁻¹ = l * ((a * l * a⁻¹ * l⁻¹) * lb) := by
      have hcLb := S.comm_L_Lb hl (Lb.mul_mem hc hlb)
      calc a * (l * lb) * a⁻¹ = a * l * a⁻¹ * (a * lb * a⁻¹) := by group
        _ = a * l * a⁻¹ * lb := by rw [hcomm]; group
        _ = (a * l * a⁻¹ * l⁻¹) * lb * l := by
            rw [show a * l * a⁻¹ * l⁻¹ * lb * l = a * l * a⁻¹ * (l⁻¹ * (lb * l)) by group,
              ← S.comm_L_Lb hl hlb]
            group
        _ = l * ((a * l * a⁻¹ * l⁻¹) * lb) := by rw [hcLb.symm]
    rw [e]
    exact S.mul_mem_M hl (Lb.mul_mem hc hlb)
  intro a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S.sq_Ab ha)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key a ha x, fun hx => ?_⟩
  have := key a ha _ hx
  rwa [show a * (a * x * a⁻¹) * a⁻¹ = x by rw [hainv]; rw [← mul_assoc, ← mul_assoc,
    S.sq_Ab ha, one_mul, mul_assoc, S.sq_Ab ha, mul_one]] at this

theorem inf_M : A ⊓ M = L := by
  refine le_antisymm (fun x hx => ?_) (le_inf S.L_le S.L_le_M)
  obtain ⟨hxA, hxM⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hxM
  have hlbA : lb ∈ A := by
    have := A.mul_mem (A.inv_mem (S.L_le hl)) hxA
    rwa [inv_mul_cancel_left] at this
  have : lb ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨hlbA, S.Lb_le hlb⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hl

theorem mem_L_of_commute_M {t m : G} (ht : t ∈ A) (htL : t ∉ L) (hm : m ∈ M)
    (htm : t * m = m * t) : m ∈ L := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
  have hc := S.commutator_mem_L ht hlb
  have e : t * (l * lb) * t⁻¹ = (l * (t * lb * t⁻¹ * lb⁻¹)) * lb := by
    have := S.comm_A ht (S.L_le hl)
    calc t * (l * lb) * t⁻¹ = (t * l) * lb * t⁻¹ := by group
      _ = (l * t) * lb * t⁻¹ := by rw [this]
      _ = (l * (t * lb * t⁻¹ * lb⁻¹)) * lb := by group
  have hfix : t * (l * lb) * t⁻¹ = l * lb := by rw [htm]; group
  rw [e] at hfix
  have h1 : t * lb * t⁻¹ * lb⁻¹ = 1 := by
    have := mul_right_cancel hfix
    exact mul_left_cancel (this.trans (mul_one l).symm)
  have htlb : t * lb = lb * t := by
    calc t * lb = t * lb * t⁻¹ * lb⁻¹ * (lb * t) := by group
      _ = lb * t := by rw [h1, one_mul]
  by_cases hlb1 : lb = 1
  · rw [hlb1, mul_one]
    exact hl
  · exact absurd (S.mem_L_of_commute ht (S.Lb_le hlb) hlb1 htlb) htL

theorem conj_mem_L_of_commute_M {g a m : G} (hg : g ∈ Subgroup.normalizer (M : Set G))
    (ha : a ∈ A) (haL : a ∉ L) (hm : m ∈ M) (hcomm : m * (g⁻¹ * a * g) = (g⁻¹ * a * g) * m) :
    g * m * g⁻¹ ∈ L := by
  have hgm : g * m * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hg m).mp hm
  refine S.mem_L_of_commute_M ha haL hgm ?_
  calc a * (g * m * g⁻¹) = g * ((g⁻¹ * a * g) * m) * g⁻¹ := by group
    _ = g * (m * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
    _ = g * m * g⁻¹ * a := by group

theorem conj_mem_of_commutator_mem {g t a : G} (hg : g ∈ Subgroup.normalizer (M : Set G))
    (ht : t ∈ A) (htL : t ∉ L) (ha : a ∈ A) (haL : a ∉ L)
    (hc : t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ M) : g⁻¹ * a * g ∈ A := by
  set τ := g⁻¹ * a * g with hτ
  set T := conjSubgroup g⁻¹ A with hT
  have hτT : τ ∈ T := by
    rw [hT, mem_conjSubgroup, inv_inv, hτ]
    simpa [mul_assoc] using ha
  have hTTI : IsTI T := isTI_conjSubgroup S.ti g⁻¹
  have hsuff : ∀ x, x ∈ A → x ∈ T → x ≠ 1 → τ ∈ A := by
    intro x hxA hxT hx1
    have hne : A ⊓ conjSubgroup g⁻¹ A ≠ ⊥ := fun h => by
      have : x ∈ A ⊓ conjSubgroup g⁻¹ A := Subgroup.mem_inf.mpr ⟨hxA, hxT⟩
      rw [h, Subgroup.mem_bot] at this
      exact hx1 this
    have hTA : conjSubgroup g⁻¹ A = A := conjSubgroup_eq_of_isTI S.ti hne
    rw [← hTA]
    exact hτT
  have ht2 : t * t = 1 := S.sq_A ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτ2 : τ * τ = 1 := by
    rw [hτ, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, S.sq_A ha]
    group
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  set c := t * τ * t⁻¹ * τ⁻¹ with hcdef
  have hcM : c ∈ M := hc
  have hcc : c * c = 1 := by rw [← sq]; exact S.isElemAbelian_M.2 c hcM
  obtain ⟨htc, hτc⟩ := commute_commutator_of_involutions ht2 hτ2 hcdef hcc
  have hcL : c ∈ L := S.mem_L_of_commute_M ht htL hcM htc
  have hgcL : g * c * g⁻¹ ∈ L := S.conj_mem_L_of_commute_M hg ha haL hcM hτc
  have hcT : c ∈ T := by
    rw [hT, mem_conjSubgroup, inv_inv]
    exact S.L_le hgcL
  by_cases hc1 : c = 1
  ·
    have htτ : t * τ = τ * t := by
      calc t * τ = c * (τ * t) := by rw [hcdef]; group
        _ = τ * t := by rw [hc1, one_mul]
    have hτ1 : τ ≠ 1 := by
      intro h
      apply haL
      have : a = 1 := by
        have h' : g * τ * g⁻¹ = 1 := by rw [h]; group
        rw [hτ] at h'
        simpa [mul_assoc] using h'
      rw [this]
      exact L.one_mem
    have htNT : t ∈ Subgroup.normalizer (T : Set G) :=
      mem_normalizer_of_commute_of_isTI hTTI hτT hτ1 htτ
    set U := T ⊓ M with hU
    have hUe : Assembly.IsElemAbelian 2 U := by
      refine ⟨⟨⟨fun x y => Subtype.ext (S.comm_M x.2.2 y.2.2)⟩⟩, fun x hx => ?_⟩
      exact S.isElemAbelian_M.2 x hx.2
    have hU1 : U ≠ ⊥ := by
      obtain ⟨⟨l, hl⟩, hl1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.ne_bot
      have hl1 : l ≠ 1 := fun h => hl1' (Subtype.ext h)
      intro hbot
      have hmem : g⁻¹ * l * g ∈ U := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [hT, mem_conjSubgroup, inv_inv]
          simpa [mul_assoc] using S.L_le hl
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp (S.L_le_M hl)
          simpa using this
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hl1
      have : g * (g⁻¹ * l * g) * g⁻¹ = 1 := by rw [hmem]; group
      simpa [mul_assoc] using this
    have htNU : t ∈ Subgroup.normalizer (U : Set G) :=
      mem_normalizer_inf htNT (S.A_le_normalizer_M ht)
    obtain ⟨x, hxU, hx1, htx⟩ := exists_ne_one_commute hUe hU1 htNU ht2
    have hxL : x ∈ L := S.mem_L_of_commute_M ht htL hxU.2 htx
    exact hsuff x (S.L_le hxL) hxU.1 hx1
  · exact hsuff c (S.L_le hcL) hcT hc1

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77

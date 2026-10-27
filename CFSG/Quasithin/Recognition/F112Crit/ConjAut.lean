module

public import CFSG.Quasithin.Recognition.F112Crit.GaloisDescent

public section

namespace CFSG.Quasithin.F112Crit

open GaloisDescent

variable {G : Type*} [Group G]

theorem relIndex_le_two_of_forall {H K : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ K, a ∉ H → b ∉ H → b * a ∈ H) : H.relIndex K ≤ 2 := by
  by_cases hK : K ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hK]; norm_num
  · obtain ⟨a, haK, haH⟩ := Set.not_subset.mp hK
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr ⟨a, haK, haH, fun b hb => ?_⟩).le
    by_cases hbH : b ∈ H
    · exact Or.inr hbH
    · exact Or.inl (h a haK b hb haH hbH)

theorem card_sup_le_of_le_normalizer [Finite G] {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have hsurj : Function.Surjective
      (fun q : H × K => (⟨(q.1 : G) * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2)
        (Subgroup.mem_sup_right q.2.2)⟩ : ↥(H ⊔ K))) := by
    intro s
    have hs : (s : G) ∈ ((H ⊔ K : Subgroup G) : Set G) := s.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H K h] at hs
    obtain ⟨a, ha, b, hb, hab⟩ := hs
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card ↥(H ⊔ K) ≤ Nat.card (H × K) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

namespace ConjAut

variable (V : Subgroup G)

theorem conj_mem {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hg v).mp hv

theorem conj_inv_mem {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    g⁻¹ * v * g ∈ V := by
  have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * v * g)).mpr
  have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
  rw [e] at h
  exact h hv

@[expose] def conjMulEquiv (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) : ↥V ≃* ↥V where
  toFun a := ⟨g * (a : G) * g⁻¹, conj_mem V hg a.2⟩
  invFun a := ⟨g⁻¹ * (a : G) * g, conj_inv_mem V hg a.2⟩
  left_inv a := Subtype.ext (by show g⁻¹ * (g * (a : G) * g⁻¹) * g = a; group)
  right_inv a := Subtype.ext (by show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a; group)
  map_mul' a b := Subtype.ext (by
    show g * ((a : G) * b) * g⁻¹ = g * (a : G) * g⁻¹ * (g * (b : G) * g⁻¹); group)

@[expose] def conjAut (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    Additive ↥V ≃+ Additive ↥V :=
  MulEquiv.toAdditive (conjMulEquiv V g hg)

theorem val_conjAut (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) (a : Additive ↥V) :
    ((Additive.toMul (conjAut V g hg a) : ↥V) : G) = g * ((Additive.toMul a : ↥V) : G) * g⁻¹ :=
  rfl

theorem val_conjAut_symm (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) (a : Additive ↥V) :
    ((Additive.toMul ((conjAut V g hg).symm a) : ↥V) : G) =
      g⁻¹ * ((Additive.toMul a : ↥V) : G) * g :=
  rfl

theorem val_iterate_conjAut (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) (n : ℕ)
    (a : Additive ↥V) :
    ((Additive.toMul ((⇑(conjAut V g hg))^[n] a) : ↥V) : G) =
      g ^ n * ((Additive.toMul a : ↥V) : G) * (g ^ n)⁻¹ := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, val_conjAut, pow_succ]
    group

theorem eq_iff_val {a b : Additive ↥V} :
    a = b ↔ ((Additive.toMul a : ↥V) : G) = ((Additive.toMul b : ↥V) : G) :=
  ⟨fun h => by rw [h], fun h => Additive.toMul.injective (Subtype.ext h)⟩

section Commutative

open scoped IsMulCommutative

variable [IsMulCommutative ↥V]

theorem add_self_eq_zero (h2 : ∀ v ∈ V, v * v = 1) (a : Additive ↥V) : a + a = 0 := by
  rw [eq_iff_val]
  show ((Additive.toMul a : ↥V) : G) * ((Additive.toMul a : ↥V) : G) = 1
  exact h2 _ (Additive.toMul a).2

theorem mem_fixSub_conjAut (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) {a : Additive ↥V} :
    a ∈ fixSub (conjAut V g hg) ↔
      g * ((Additive.toMul a : ↥V) : G) = ((Additive.toMul a : ↥V) : G) * g := by
  rw [mem_fixSub, eq_iff_val, val_conjAut, mul_inv_eq_iff_eq_mul]

theorem fixSub_conjAut_eq (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    fixSub (conjAut V g hg) =
      Subgroup.toAddSubgroup ((Subgroup.centralizer ({g} : Set G)).subgroupOf V) := by
  ext a
  rw [mem_fixSub_conjAut, Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact h
  · intro h
    exact h g rfl

theorem index_fixSub_conjAut (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    (fixSub (conjAut V g hg)).index = (Subgroup.centralizer ({g} : Set G)).relIndex V := by
  rw [fixSub_conjAut_eq, Subgroup.index_toAddSubgroup]
  rfl

theorem commSub_ne_bot_of (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hne : ∃ a ∈ V, g * a * g⁻¹ ≠ a) : commSub (conjAut V g hg) ≠ ⊥ := by
  obtain ⟨a, haV, hne⟩ := hne
  intro hbot
  have h1 := x_sub_mem_commSub (conjAut V g hg) (Additive.ofMul (⟨a, haV⟩ : ↥V))
  rw [hbot, AddSubgroup.mem_bot, sub_eq_zero, eq_iff_val, val_conjAut] at h1
  exact hne h1

theorem lemma74_group [Finite G] (h2 : ∀ v ∈ V, v * v = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p % 2 = 1) {x t : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hxp : ∀ a ∈ V, x ^ p * a * (x ^ p)⁻¹ = a)
    (htt : ∀ a ∈ V, t * (t * a * t⁻¹) * t⁻¹ = a)
    (htx : ∀ a ∈ V, t * (x * a * x⁻¹) * t⁻¹ = x⁻¹ * (t * a * t⁻¹) * x)
    (hne : ∃ a ∈ V, x * a * x⁻¹ ≠ a)
    (hidx : (Subgroup.centralizer ({t} : Set G)).relIndex V ≤ 2) :
    p = 3 ∧ Nat.card (commSub (conjAut V x hx)) = 4 := by
  have hxp' : ∀ a, (⇑(conjAut V x hx))^[p] a = a := fun a => by
    rw [eq_iff_val, val_iterate_conjAut]
    exact hxp _ (Additive.toMul a).2
  have htt' : ∀ a, conjAut V t ht (conjAut V t ht a) = a := fun a => by
    rw [eq_iff_val, val_conjAut, val_conjAut]
    exact htt _ (Additive.toMul a).2
  have htx' : ∀ a, conjAut V t ht (conjAut V x hx a) =
      (conjAut V x hx).symm (conjAut V t ht a) := fun a => by
    rw [eq_iff_val, val_conjAut, val_conjAut, val_conjAut_symm, val_conjAut]
    exact htx _ (Additive.toMul a).2
  have hidx' : (fixSub (conjAut V t ht)).index ≤ 2 := by
    rw [index_fixSub_conjAut]; exact hidx
  obtain ⟨h3, h4, -⟩ := eq_three_of_index_le_two (add_self_eq_zero V h2) hp hp2 hxp' htt' htx'
    (commSub_ne_bot_of V x hx hne) hidx'
  exact ⟨h3, h4⟩

theorem card_le_two_group [Finite G] (h2 : ∀ v ∈ V, v * v = 1) {p : ℕ} (hp2 : p % 2 = 1)
    {x t : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hxp : ∀ a ∈ V, x ^ p * a * (x ^ p)⁻¹ = a)
    (htt : ∀ a ∈ V, t * (t * a * t⁻¹) * t⁻¹ = a)
    (htx : ∀ a ∈ V, t * (x * a * x⁻¹) * t⁻¹ = x⁻¹ * (t * a * t⁻¹) * x)
    (hW4 : Nat.card (commSub (conjAut V x hx)) = 4) {K : Subgroup G} (hKV : K ≤ V)
    (hKt : ∀ a ∈ K, t * a * t⁻¹ = a) (hKx : ∀ a ∈ K, x * a * x⁻¹ = a → a = 1) :
    Nat.card K ≤ 2 := by
  have hxp' : ∀ a, (⇑(conjAut V x hx))^[p] a = a := fun a => by
    rw [eq_iff_val, val_iterate_conjAut]
    exact hxp _ (Additive.toMul a).2
  have htt' : ∀ a, conjAut V t ht (conjAut V t ht a) = a := fun a => by
    rw [eq_iff_val, val_conjAut, val_conjAut]
    exact htt _ (Additive.toMul a).2
  have htx' : ∀ a, conjAut V t ht (conjAut V x hx a) =
      (conjAut V x hx).symm (conjAut V t ht a) := fun a => by
    rw [eq_iff_val, val_conjAut, val_conjAut, val_conjAut_symm, val_conjAut]
    exact htx _ (Additive.toMul a).2
  have h2' := add_self_eq_zero V h2
  set Z' : AddSubgroup (Additive ↥V) := Subgroup.toAddSubgroup (K.subgroupOf V) with hZ'
  have hZt : ∀ a ∈ Z', conjAut V t ht a = a := fun a ha => by
    rw [eq_iff_val, val_conjAut]
    exact hKt _ ha
  have hZx : ∀ a ∈ Z', conjAut V x hx a = a → a = 0 := fun a ha h => by
    rw [eq_iff_val, val_conjAut] at h
    have := hKx _ ha h
    rw [eq_iff_val]
    exact this
  have h1 := card_le_card_fix h2' hp2 hxp' htx' Z' hZt hZx
  have hsq := card_commSub_eq_sq h2' hp2 hxp' htt' htx' (t := conjAut V t ht)
  rw [hW4] at hsq
  have hc : Nat.card ↥(commSub (conjAut V x hx) ⊓ fixSub (conjAut V t ht)) = 2 :=
    Nat.pow_left_injective (n := 2) (by norm_num) (by simpa using hsq.symm)
  have hcard : Nat.card Z' = Nat.card K := by
    have e1 : Nat.card Z' = Nat.card ↥(K.subgroupOf V) :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun a => Iff.rfl))
    rw [e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKV).toEquiv
  rw [← hcard]
  exact h1.trans hc.le

end Commutative

@[expose] def commSubgroup (V : Subgroup G) (x : G) : Subgroup G :=
  Subgroup.closure {w : G | ∃ a ∈ V, w = x * a * x⁻¹ * a⁻¹}

section Commutative

open scoped IsMulCommutative

variable [IsMulCommutative ↥V]

theorem commSubgroup_eq_map (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    commSubgroup V x = (AddSubgroup.toSubgroup' (commSub (conjAut V x hx))).map V.subtype := by
  have hval : ∀ a : Additive ↥V, ((Additive.toMul (subId (conjAut V x hx) a) : ↥V) : G) =
      x * ((Additive.toMul a : ↥V) : G) * x⁻¹ * ((Additive.toMul a : ↥V) : G)⁻¹ := fun a => by
    show ((Additive.toMul (conjAut V x hx a - a) : ↥V) : G) = _
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv, val_conjAut]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨a, haV, rfl⟩
    have hm : x * a * x⁻¹ * a⁻¹ ∈ V :=
      V.mul_mem (conj_mem V hx haV) (V.inv_mem haV)
    refine ⟨⟨x * a * x⁻¹ * a⁻¹, hm⟩, ?_, rfl⟩
    show Additive.ofMul (⟨x * a * x⁻¹ * a⁻¹, hm⟩ : ↥V) ∈ commSub (conjAut V x hx)
    exact ⟨Additive.ofMul ⟨a, haV⟩, (eq_iff_val V).mpr (by rw [hval]; rfl)⟩
  · rintro w ⟨c, hc, rfl⟩
    have hc' : Additive.ofMul c ∈ commSub (conjAut V x hx) := hc
    obtain ⟨b, hb⟩ := hc'
    have h1 := congrArg (fun u => ((Additive.toMul u : ↥V) : G)) hb
    simp only [hval] at h1
    exact Subgroup.subset_closure ⟨_, (Additive.toMul b).2, h1.symm⟩

theorem card_commSubgroup [Finite G] (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    Nat.card (commSubgroup V x) = Nat.card (commSub (conjAut V x hx)) := by
  rw [commSubgroup_eq_map V x hx, Subgroup.card_map_of_injective V.subtype_injective]
  exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun a => Iff.rfl))

theorem commSubgroup_le (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) : commSubgroup V x ≤ V := by
  rw [commSubgroup_eq_map V x hx]
  rintro w ⟨c, _, rfl⟩
  exact c.2

end Commutative

end ConjAut

end CFSG.Quasithin.F112Crit

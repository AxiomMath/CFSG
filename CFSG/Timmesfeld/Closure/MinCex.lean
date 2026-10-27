module

public import CFSG.Timmesfeld.Closure.Reduction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Timmesfeld.Connectivity
open CFSG.Timmesfeld

universe u

section Reach

variable {G : Type u} [Group G] (D : Set G)

@[expose] def CommRel (a b : G) : Prop := a ∈ D ∧ b ∈ D ∧ Commute a b

@[expose] def Reach : G → G → Prop := Relation.ReflTransGen (CommRel D)

@[expose] def IsNormalSet : Prop := ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D

variable {D}

theorem reach_refl (x : G) : Reach D x x := Relation.ReflTransGen.refl

theorem reach_of_commute {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : Commute x y) :
    Reach D x y := Relation.ReflTransGen.single ⟨hx, hy, hxy⟩

theorem reach_trans {x y z : G} (h1 : Reach D x y) (h2 : Reach D y z) : Reach D x z :=
  Relation.ReflTransGen.trans h1 h2

theorem reach_symm {x y : G} (h : Reach D x y) : Reach D y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

theorem reach_conj (hN : IsNormalSet D) (g : G) {x y : G} (h : Reach D x y) :
    Reach D (g * x * g⁻¹) (g * y * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨hN g _ hbc.1, hN g _ hbc.2.1, (Commute.conj_iff g).2 hbc.2.2⟩

theorem mem_of_reach {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ D, Commute x y → y ∈ S) {x y : G}
    (hx : x ∈ S) (h : Reach D x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hS _ ih _ hbc.2.1 hbc.2.2

theorem commConnected_of_reach (h : ∀ x ∈ D, ∀ y ∈ D, Reach D x y) :
    Closure.CommConnected D := by
  intro S hSD hSne hS y hy
  obtain ⟨x, hx⟩ := hSne
  exact mem_of_reach hS hx (h x (hSD hx) y hy)

end Reach

section Basic

variable {G : Type u} [Group G] {D : Set G}

theorem opposite_of_not_reach (hD : IsRootInvolutionSet D) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (h : ¬ Reach D x y) : ¬ Commute x y ∧ Odd (orderOf (x * y)) := by
  have hx2 := hD.mul_self_eq_one hx
  have hy2 := hD.mul_self_eq_one hy
  have hnc : ¬ Commute x y := fun hc => h (reach_of_commute hx hy hc)
  refine ⟨hnc, ?_⟩
  rcases hD.orderOf_mul hx hy with h2 | h4 | hodd
  · exfalso
    apply hnc
    rw [commute_iff_mul_sq_eq_one hx2 hy2, ← h2]
    exact pow_orderOf_eq_one _
  · exfalso
    obtain ⟨hzD, hxz, hyz, -⟩ := sq_mem_of_orderOf_eq_four hD hx hy h4
    exact h (reach_trans (reach_of_commute hx hzD hxz) (reach_symm (reach_of_commute hy hzD hyz)))
  · exact hodd

@[expose] def compStab (hN : IsNormalSet D) (x : G) : Subgroup G where
  carrier := {g | Reach D x (g * x * g⁻¹)}
  one_mem' := by
    show Reach D x (1 * x * 1⁻¹)
    simpa using reach_refl (D := D) x
  mul_mem' := by
    intro g h hg hh
    show Reach D x (g * h * x * (g * h)⁻¹)
    have h1 := reach_conj hN g hh
    have e1 : g * (h * x * h⁻¹) * g⁻¹ = g * h * x * (g * h)⁻¹ := by group
    rw [e1] at h1
    exact reach_trans hg h1
  inv_mem' := by
    intro g hg
    show Reach D x (g⁻¹ * x * g⁻¹⁻¹)
    have h1 := reach_conj hN g⁻¹ hg
    have e1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e1] at h1
    exact reach_symm h1

theorem mem_compStab_iff (hN : IsNormalSet D) {x g : G} :
    g ∈ compStab hN x ↔ Reach D x (g * x * g⁻¹) := Iff.rfl

theorem mem_compStab_self (hN : IsNormalSet D) (x : G) : x ∈ compStab hN x := by
  show Reach D x (x * x * x⁻¹)
  simpa using reach_refl (D := D) x

theorem reach_of_mem_compStab (hN : IsNormalSet D) (hD : IsRootInvolutionSet D) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) (hyS : y ∈ compStab hN x) : Reach D x y := by
  by_contra h
  obtain ⟨-, hodd⟩ := opposite_of_not_reach hD hx hy h
  obtain ⟨g, hg, hgx⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hx)
    (hD.mul_self_eq_one hy) hodd
  have hle : Subgroup.closure ({x, y} : Set G) ≤ compStab hN x := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact mem_compStab_self hN z
    · exact hyS
  have := hle hg
  rw [mem_compStab_iff, hgx] at this
  exact h this

@[expose] def Disconnected (D : Set G) : Prop := ∃ x ∈ D, ∃ y ∈ D, ¬ Reach D x y

theorem exists_not_reach (hdisc : Disconnected D) {x : G} :
    ∃ z ∈ D, ¬ Reach D x z := by
  obtain ⟨a, ha, b, hb, hab⟩ := hdisc
  by_cases hxa : Reach D x a
  · refine ⟨b, hb, fun hxb => hab (reach_trans (reach_symm hxa) hxb)⟩
  · exact ⟨a, ha, hxa⟩

theorem isConj_of_disconnected (hD : IsRootInvolutionSet D) (hdisc : Disconnected D) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) : IsConj x y := by
  have key : ∀ {a b : G}, a ∈ D → b ∈ D → ¬ Reach D a b → IsConj a b := by
    intro a b ha hb hab
    obtain ⟨-, hodd⟩ := opposite_of_not_reach hD ha hb hab
    obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hb) hodd
    exact isConj_iff.2 ⟨g, hg⟩
  by_cases hxy : Reach D x y
  · obtain ⟨z, hz, hxz⟩ := exists_not_reach hdisc (x := x)
    have hyz : ¬ Reach D y z := fun h => hxz (reach_trans hxy h)
    exact (key hx hz hxz).trans (key hy hz hyz).symm
  · exact key hx hy hxy

theorem not_forall_mem_compStab (hN : IsNormalSet D) (hD : IsRootInvolutionSet D)
    (hdisc : Disconnected D) {x : G} (hx : x ∈ D) : ∃ y ∈ D, x ∉ compStab hN y := by
  obtain ⟨y, hy, hxy⟩ := exists_not_reach hdisc (x := x)
  exact ⟨y, hy, fun h => hxy (reach_symm (reach_of_mem_compStab hN hD hy hx h))⟩


@[expose] def ker (hN : IsNormalSet D) : Subgroup G := ⨅ (x : G) (_ : x ∈ D), compStab hN x

theorem mem_ker_iff (hN : IsNormalSet D) {g : G} :
    g ∈ ker hN ↔ ∀ x ∈ D, Reach D x (g * x * g⁻¹) := by
  simp only [ker, Subgroup.mem_iInf, mem_compStab_iff]

theorem ker_normal (hN : IsNormalSet D) : (ker hN).Normal := by
  refine ⟨fun k hk g => ?_⟩
  rw [mem_ker_iff] at hk ⊢
  intro x hx
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ D := hN g⁻¹ x hx
  have h1 := reach_conj hN g (hk _ hx')
  have e1 : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  have e2 : g * (k * (g⁻¹ * x * g⁻¹⁻¹) * k⁻¹) * g⁻¹ = g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ := by
    group
  rwa [e1, e2] at h1

instance ker.instNormal (hN : IsNormalSet D) : (ker hN).Normal := ker_normal hN

theorem not_mem_ker (hN : IsNormalSet D) (hD : IsRootInvolutionSet D) (hdisc : Disconnected D)
    {x : G} (hx : x ∈ D) : x ∉ ker hN := by
  obtain ⟨y, hy, hxy⟩ := not_forall_mem_compStab hN hD hdisc hx
  intro hk
  exact hxy ((mem_ker_iff hN).1 hk y hy)

theorem reach_of_mul_mem_ker (hN : IsNormalSet D) (hD : IsRootInvolutionSet D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ ker hN) : Reach D a b := by
  apply reach_of_mem_compStab hN hD ha hb
  rw [mem_compStab_iff]
  have hk := (mem_ker_iff hN).1 hab a ha
  have h1 := reach_conj hN a hk
  have ha2 := hD.mul_self_eq_one ha
  have hainv : a⁻¹ = a := hD.inv_eq ha
  have e1 : a * a * a⁻¹ = a := by group
  have e2 : a * (a * b * a * (a * b)⁻¹) * a⁻¹ = b * a * b⁻¹ := by
    rw [hainv]
    calc a * (a * b * a * (a * b)⁻¹) * a = (a * a) * b * a * b⁻¹ * (a⁻¹ * a) := by group
      _ = b * a * b⁻¹ := by rw [ha2, inv_mul_cancel, one_mul, mul_one]
  rwa [e1, e2] at h1

section Image

variable {Q : Type u} [Group Q]

theorem isRootInvolutionSet_image (hD : IsRootInvolutionSet D) (φ : G →* Q)
    (hφ : ∀ x ∈ D, φ x ≠ 1) : IsRootInvolutionSet (φ '' D) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine orderOf_eq_prime ?_ (hφ x hx)
    rw [← map_pow, pow_two, hD.mul_self_eq_one hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have hdvd : orderOf (φ (x * y)) ∣ orderOf (x * y) := orderOf_map_dvd φ (x * y)
    rcases hD.orderOf_mul hx hy with h2 | h4 | hodd
    · rw [h2] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
      · exact Or.inr (Or.inr (by rw [h1]; decide))
      · exact Or.inl h1
    · rw [h4, show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      interval_cases k
      · exact Or.inr (Or.inr (by rw [hk']; decide))
      · exact Or.inl hk'
      · exact Or.inr (Or.inl hk')
    · exact Or.inr (Or.inr (Odd.of_dvd_nat hodd hdvd))
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h4
    rw [← map_mul] at h4 ⊢
    have hdvd : orderOf (φ (x * y)) ∣ orderOf (x * y) := orderOf_map_dvd φ (x * y)
    rw [h4] at hdvd
    have hxy4 : orderOf (x * y) = 4 := by
      rcases hD.orderOf_mul hx hy with h2 | h4' | hodd
      · rw [h2] at hdvd; exact absurd hdvd (by decide)
      · exact h4'
      · exfalso
        obtain ⟨m, hm⟩ := hdvd
        rcases hodd with ⟨k, hk⟩
        omega
    exact ⟨(x * y) ^ 2, hD.sq_mem hx hy hxy4, by rw [map_pow]⟩

theorem isNormalSet_image (hN : IsNormalSet D) (φ : G →* Q) (hφ : Function.Surjective φ) :
    IsNormalSet (φ '' D) := by
  rintro g _ ⟨x, hx, rfl⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact ⟨g' * x * g'⁻¹, hN g' x hx, by simp only [map_mul, map_inv]⟩

theorem closure_image_eq_top (hgen : Subgroup.closure D = ⊤) (φ : G →* Q)
    (hφ : Function.Surjective φ) : Subgroup.closure (φ '' D) = ⊤ := by
  rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective φ hφ]

end Image

structure Setting (D : Set G) : Prop where
  finite : Finite G
  normal : IsNormalSet D
  root : IsRootInvolutionSet D
  gen : Subgroup.closure D = ⊤
  nondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4

section Quotient

variable (hS : Setting D)

theorem reach_of_commute_mk {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : Commute (QuotientGroup.mk' (ker hS.normal) a)
      (QuotientGroup.mk' (ker hS.normal) b)) : Reach D a b := by
  by_contra h
  obtain ⟨-, hodd⟩ := opposite_of_not_reach hS.root ha hb h
  set φ := QuotientGroup.mk' (ker hS.normal)
  have ha2 : φ a * φ a = 1 := by rw [← map_mul, hS.root.mul_self_eq_one ha, map_one]
  have hb2 : φ b * φ b = 1 := by rw [← map_mul, hS.root.mul_self_eq_one hb, map_one]
  have hsq : (φ (a * b)) ^ 2 = 1 := by
    rw [map_mul]
    exact (commute_iff_mul_sq_eq_one ha2 hb2).1 hab
  have h1 : orderOf (φ (a * b)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h2 : orderOf (φ (a * b)) ∣ orderOf (a * b) := orderOf_map_dvd φ (a * b)
  have h3 : orderOf (φ (a * b)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (Odd.of_dvd_nat hodd h2) (by decide)
  have hmem : a * b ∈ ker hS.normal := by
    rw [← QuotientGroup.eq_one_iff]
    exact orderOf_eq_one_iff.1 h3
  exact h (reach_of_mul_mem_ker hS.normal hS.root ha hb hmem)

theorem reach_of_reach_image {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (h : Reach (QuotientGroup.mk' (ker hS.normal) '' D) (QuotientGroup.mk' (ker hS.normal) a)
      (QuotientGroup.mk' (ker hS.normal) b)) : Reach D a b := by
  set φ := QuotientGroup.mk' (ker hS.normal)
  suffices key : ∀ y, Reach (φ '' D) (φ a) y → ∀ b ∈ D, φ b = y → Reach D a b from
    key _ h b hb rfl
  intro y hy
  induction hy with
  | refl =>
    intro b hb hba
    apply reach_of_commute_mk hS ha hb
    rw [hba]
  | tail _ hbc ih =>
    intro c hc hcy
    obtain ⟨⟨b, hb, rfl⟩, -, hcomm⟩ := hbc
    refine reach_trans (ih b hb rfl) (reach_of_commute_mk hS hb hc ?_)
    rw [hcy]
    exact hcomm

theorem quotient_setting (hdisc : Disconnected D) :
    Setting (QuotientGroup.mk' (ker hS.normal) '' D) := by
  have := hS.finite
  set φ := QuotientGroup.mk' (ker hS.normal)
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hφ : ∀ x ∈ D, φ x ≠ 1 := fun x hx h1 =>
    not_mem_ker hS.normal hS.root hdisc hx ((QuotientGroup.eq_one_iff x).1 h1)
  refine ⟨inferInstance, isNormalSet_image hS.normal φ hsurj,
    isRootInvolutionSet_image hS.root φ hφ, closure_image_eq_top hS.gen φ hsurj, ?_⟩
  obtain ⟨d, hd, e, he, h4⟩ := hS.nondeg
  refine ⟨φ d, ⟨d, hd, rfl⟩, φ e, ⟨e, he, rfl⟩, ?_⟩
  rw [← map_mul]
  have hdvd : orderOf (φ (d * e)) ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← h4]
    exact orderOf_map_dvd φ (d * e)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hsq : φ (d * e) ^ 2 ≠ 1 := by
    rw [← map_pow]
    exact hφ _ (hS.root.sq_mem hd he h4)
  interval_cases k
  · exfalso; apply hsq
    have h1 : φ (d * e) = 1 := orderOf_eq_one_iff.1 (by simpa using hk')
    rw [h1, one_pow]
  · exfalso; apply hsq
    have h1 := pow_orderOf_eq_one (φ (d * e))
    rwa [hk', pow_one] at h1
  · simpa using hk'

theorem quotient_disconnected (hdisc : Disconnected D) :
    Disconnected (QuotientGroup.mk' (ker hS.normal) '' D) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hdisc
  exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, fun h => hxy (reach_of_reach_image hS hx hy h)⟩

theorem card_quotient_lt (hK : ker hS.normal ≠ ⊥) :
    Nat.card (G ⧸ ker hS.normal) < Nat.card G := by
  have := hS.finite
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ker hS.normal)
  have h2 : 1 < Nat.card (ker hS.normal) := (Subgroup.one_lt_card_iff_ne_bot _).2 hK
  have h3 : 0 < Nat.card (G ⧸ ker hS.normal) := Nat.card_pos
  rw [h1]
  exact lt_mul_of_one_lt_right h3 h2

end Quotient

section Sub

abbrev subL (D : Set G) (L : Subgroup G) : Subgroup G := Subgroup.closure (D ∩ (L : Set G))

@[expose] def subD (D : Set G) (L : Subgroup G) : Set (subL D L) := {x | (x : G) ∈ D}

theorem subL_le (L : Subgroup G) : subL D L ≤ L :=
  (Subgroup.closure_le L).2 Set.inter_subset_right

theorem reach_of_reach_subD {L : Subgroup G} {a b : subL D L} (h : Reach (subD D L) a b) :
    Reach D (a : G) (b : G) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih =>
    exact reach_trans ih (reach_of_commute hbc.1 hbc.2.1 (hbc.2.2.map (subL D L).subtype))

theorem sub_setting (hS : Setting D) (L : Subgroup G) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hdL : d ∈ L) (heL : e ∈ L) (h4 : orderOf (d * e) = 4) : Setting (subD D L) := by
  have := hS.finite
  have hdm : d ∈ subL D L := Subgroup.subset_closure ⟨hd, hdL⟩
  have hem : e ∈ subL D L := Subgroup.subset_closure ⟨he, heL⟩
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro g x hx
    show ((g * x * g⁻¹ : subL D L) : G) ∈ D
    simpa using hS.normal g x hx
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [← Subgroup.orderOf_coe]
      exact hS.root.orderOf_eq_two hx
    · intro x hx y hy
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      exact hS.root.orderOf_mul hx hy
    · intro x hx y hy h4'
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4'
      show (((x * y) ^ 2 : subL D L) : G) ∈ D
      simpa using hS.root.sq_mem hx hy h4'
  · have hset : subD D L = ((↑) : subL D L → G) ⁻¹' (D ∩ (L : Set G)) := by
      ext x
      exact ⟨fun h => ⟨h, subL_le L x.2⟩, fun h => h.1⟩
    rw [hset]
    exact Subgroup.closure_closure_coe_preimage
  · refine ⟨⟨d, hdm⟩, hd, ⟨e, hem⟩, he, ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact h4

theorem card_subL_lt (hS : Setting D) {L : Subgroup G} (hL : L ≠ ⊤) :
    Nat.card (subL D L) < Nat.card G := by
  have := hS.finite
  calc Nat.card (subL D L) ≤ Nat.card L := Subgroup.card_le_of_le (subL_le L)
    _ < Nat.card (⊤ : Subgroup G) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hL)
    _ = Nat.card G := Subgroup.card_top

theorem le_compStab_of_connected (hS : Setting D) (L : Subgroup G) {d : G} (hd : d ∈ D)
    (hdL : d ∈ L) (hconn : ¬ Disconnected (subD D L)) : L ≤ compStab hS.normal d := by
  intro l hl
  rw [mem_compStab_iff]
  have hx : l * d * l⁻¹ ∈ D := hS.normal l d hd
  have hxL : l * d * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hdL) (L.inv_mem hl)
  have hdm : d ∈ subL D L := Subgroup.subset_closure ⟨hd, hdL⟩
  have hxm : l * d * l⁻¹ ∈ subL D L := Subgroup.subset_closure ⟨hx, hxL⟩
  by_contra h
  apply hconn
  refine ⟨⟨d, hdm⟩, hd, ⟨l * d * l⁻¹, hxm⟩, hx, fun h' => h ?_⟩
  exact reach_of_reach_subD h'

end Sub

section Simple

theorem le_ker_of_le_compStab (hS : Setting D) (hdisc : Disconnected D) {N : Subgroup G}
    [N.Normal] {d : G} (hd : d ∈ D) (hN : N ≤ compStab hS.normal d) : N ≤ ker hS.normal := by
  intro n hn
  rw [mem_ker_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_disconnected hS.root hdisc hd hx)
  have hn' : g⁻¹ * n * g⁻¹⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
  have h1 := reach_conj hS.normal g (hN hn')
  have e2 : g * (g⁻¹ * n * g⁻¹⁻¹ * d * (g⁻¹ * n * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      n * (g * d * g⁻¹) * n⁻¹ := by group
  rwa [e2] at h1

theorem isSimpleGroup (hS : Setting D) (hdisc : Disconnected D) (hfaith : ker hS.normal = ⊥)
    (hM2 : ∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L → e ∈ L →
      L ≤ compStab hS.normal d) : IsSimpleGroup G := by
  obtain ⟨d, hd, e, he, h4⟩ := hS.nondeg
  have hd1 : d ≠ 1 := hS.root.ne_one hd
  have : Nontrivial G := ⟨⟨d, 1, hd1⟩⟩
  refine ⟨fun N hNn => ?_⟩
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  have hNS : ¬ N ≤ compStab hS.normal d := fun hle => hbot (by
    rw [eq_bot_iff, ← hfaith]
    exact le_ker_of_le_compStab hS hdisc hd hle)
  set P := Subgroup.closure ({d, e} : Set G)
  have hdP : d ∈ P := Subgroup.subset_closure (by simp)
  have heP : e ∈ P := Subgroup.subset_closure (by simp)
  have htop : P ⊔ N = ⊤ := by
    by_contra hne
    exact hNS (le_trans le_sup_right (hM2 _ hne d hd e he h4
      (Subgroup.mem_sup_left hdP) (Subgroup.mem_sup_left heP)))
  let φ := QuotientGroup.mk' N
  have hpow : (d * e) ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← h4]
    exact pow_orderOf_eq_one _
  have hP2 : IsPGroup 2 P := isPGroup_two_closure_pair (hS.root.mul_self_eq_one hd)
    (hS.root.mul_self_eq_one he) hpow
  have hmapP : P.map φ = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) htop
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective N)] at h1
    have h2 : N.map φ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨n, hn, rfl⟩
      exact (QuotientGroup.eq_one_iff n).2 hn
    rwa [h2, sup_bot_eq] at h1
  have hQ2 : ∀ q : G ⧸ N, ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    intro q
    have hq : q ∈ P.map φ := by rw [hmapP]; trivial
    obtain ⟨k, hk⟩ := hP2.map φ ⟨q, hq⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcross : ∀ x ∈ D, ∀ y ∈ D, ¬ Reach D x y → φ x = φ y := by
    intro x hx y hy hxy
    obtain ⟨-, hodd⟩ := opposite_of_not_reach hS.root hx hy hxy
    obtain ⟨k, hk⟩ := hQ2 (φ (x * y))
    have h1 : orderOf (φ (x * y)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (φ (x * y)) ∣ orderOf (x * y) := orderOf_map_dvd φ (x * y)
    have hcop : Nat.Coprime (orderOf (x * y)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
    have h3 : orderOf (φ (x * y)) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    have h4' : φ x * φ y = 1 := by rw [← map_mul]; exact orderOf_eq_one_iff.1 h3
    have hy2 : φ y * φ y = 1 := by rw [← map_mul, hS.root.mul_self_eq_one hy, map_one]
    calc φ x = φ x * (φ y * φ y) := by rw [hy2, mul_one]
      _ = (φ x * φ y) * φ y := by group
      _ = φ y := by rw [h4', one_mul]
  have hall : ∀ x ∈ D, φ x = φ d := by
    intro x hx
    by_cases hxd : Reach D x d
    · obtain ⟨z, hz, hxz⟩ := exists_not_reach hdisc (x := x)
      have hdz : ¬ Reach D d z := fun h => hxz (reach_trans hxd h)
      rw [hcross x hx z hz hxz, hcross d hd z hz hdz]
    · exact hcross x hx d hd hxd
  have hz := hall _ (hS.root.sq_mem hd he h4)
  have hd2 : φ d * φ d = 1 := by rw [← map_mul, hS.root.mul_self_eq_one hd, map_one]
  have hz1 : φ ((d * e) ^ 2) = 1 := by
    rw [map_pow, map_mul, hall e he, pow_two, hd2, one_mul]
  have hd1' : φ d = 1 := by rw [← hz, hz1]
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
  exact (hall x hx).trans hd1'

end Simple

end Basic

@[expose] def SimpleCaseInput : Prop :=
  ∀ (G : Type u) [Group G] (D : Set G) (hS : Setting D), Disconnected D → IsSimpleGroup G →
    ker hS.normal = ⊥ →
    (∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L → e ∈ L →
      L ≤ compStab hS.normal d) → False

theorem not_disconnected (hSC : SimpleCaseInput.{u}) {G : Type u} [Group G] {D : Set G}
    (hS : Setting D) : ¬ Disconnected D := by
  have key : ∀ n : ℕ, ∀ (G : Type u) [Group G] (D : Set G), Setting D → Nat.card G = n →
      ¬ Disconnected D := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ D hS hn hdisc
      have hfaith : ker hS.normal = ⊥ := by
        by_contra hK
        exact ih _ (hn ▸ card_quotient_lt hS hK) (G ⧸ ker hS.normal) _
          (quotient_setting hS hdisc) rfl (quotient_disconnected hS hdisc)
      have hM2 : ∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L →
          e ∈ L → L ≤ compStab hS.normal d := by
        intro L hL d hd e he h4 hdL heL
        exact le_compStab_of_connected hS L hd hdL
          (ih _ (hn ▸ card_subL_lt hS hL) (subL D L) (subD D L)
            (sub_setting hS L hd he hdL heL h4) rfl)
      exact hSC G D hS hdisc (isSimpleGroup hS hdisc hfaith hM2) hfaith hM2
  exact key _ G D hS rfl

theorem commConnected_of_simpleCase (hSC : SimpleCaseInput.{u}) {G : Type u} [Group G]
    {D : Set G} (h : Hyp G D) : Closure.CommConnected D := by
  have hS : Setting D :=
    ⟨h.finite, fun g _ hx => conj_mem_of_isClass h.isClass g hx, h.root, h.gen, h.nondeg⟩
  apply commConnected_of_reach
  intro x hx y hy
  by_contra hxy
  exact not_disconnected hSC hS ⟨x, hx, y, hy, hxy⟩

end CFSG.Timmesfeld.Connectivity

module

public import CFSG.Timmesfeld.Bridge.RootStructQD

public section

universe u

namespace CFSG.Timmesfeld

namespace Components

open Relation

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (show g * x = g * x * g⁻¹ * g by group)).symm

theorem conj_eq_of_pow_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : (a * b) * a * (a * b)⁻¹ = b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h' : a * (b * (a * (b * (a * b)))) = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc (a * b) * a * (a * b)⁻¹ = a * (b * (a * (b * a))) := by
        simp only [mul_inv_rev, hai, hbi, mul_assoc]
    _ = a * (b * (a * (b * (a * b)))) * b := by simp only [mul_assoc, hb, mul_one]
    _ = b := by rw [h', one_mul]

@[expose] def OddRel (D : Set G) (u v : G) : Prop := u ∈ D ∧ v ∈ D ∧ orderOf (u * v) = 3

variable {D : Set G}

theorem oddRel_mk {u v : G} (hu : u ∈ D) (hv : v ∈ D) (h : orderOf (u * v) = 3) :
    OddRel D u v :=
  ⟨hu, hv, h⟩

theorem oddRel_symm {u v : G} (h : OddRel D u v) : OddRel D v u :=
  oddRel_mk h.2.1 h.1 (by rw [orderOf_mul_comm_eq]; exact h.2.2)

theorem not_commute_of_oddRel (hD : IsRootInvolutionSet D) {u v : G} (h : OddRel D u v) :
    ¬ Commute u v := by
  intro huv
  have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one h.1)
    (hD.mul_self_eq_one h.2.1)).1 huv)
  rw [h.2.2] at this
  exact absurd this (by decide)

theorem reflTransGen_oddRel_symm {u v : G} (h : ReflTransGen (OddRel D) u v) :
    ReflTransGen (OddRel D) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (oddRel_symm hbc) ih

theorem reflTransGen_oddRel_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g : G) {u v : G}
    (h : ReflTransGen (OddRel D) u v) :
    ReflTransGen (OddRel D) (g * u * g⁻¹) (g * v * g⁻¹) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    refine ih.tail ⟨hN g _ hbc.1, hN g _ hbc.2.1, ?_⟩
    rw [show g * b * g⁻¹ * (g * c * g⁻¹) = g * (b * c) * g⁻¹ by group, orderOf_conj_eq]
    exact hbc.2.2

theorem reflTransGen_sq [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (hK : ∀ a ∈ D, ∃ c ∈ D, orderOf (a * c) = 3) {a x : G} (ha : a ∈ D) (hx : x ∈ D)
    (hax : orderOf (a * x) = 4) : ReflTransGen (OddRel D) a ((a * x) ^ 2) := by
  have ha2 := hD.mul_self_eq_one ha
  have hx2 := hD.mul_self_eq_one hx
  obtain ⟨hwD, haw, hxw, hxax⟩ := sq_mem_of_orderOf_eq_four hD ha hx hax
  set w := (a * x) ^ 2
  have hw2 := hD.mul_self_eq_one hwD
  have hwa : w * a = x * a * x⁻¹ := by
    rw [hD.inv_eq hx, hxax, haw.eq]
  have hwaD : w * a ∈ D := by rw [hwa]; exact hN x a ha
  obtain ⟨c, hc, hwc⟩ := hK w hwD
  have hcw : orderOf (c * w) = 3 := by rw [orderOf_mul_comm_eq]; exact hwc
  have hca_pos := orderOf_pos (c * a)
  have hca4 := h4 c hc a ha
  have hc2 := hD.mul_self_eq_one hc
  have hnc : ¬ Commute c a := by
    intro hca
    have hcwa : Commute (c * w) a := hca.mul_left haw.symm
    have h6 : orderOf (c * (w * a)) = 6 := by
      rw [← mul_assoc, hcwa.orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [hcw, hD.orderOf_eq_two ha]; decide), hcw, hD.orderOf_eq_two ha]
    have := h4 c hc _ hwaD
    omega
  have hca : orderOf (c * a) = 3 ∨ orderOf (c * a) = 4 := by
    have h12 : orderOf (c * a) ≠ 1 ∧ orderOf (c * a) ≠ 2 := by
      constructor <;> intro h <;> refine hnc ((commute_iff_mul_sq_eq_one hc2 ha2).2 ?_)
      · rw [orderOf_eq_one_iff.1 h, one_pow]
      · rw [← h]; exact pow_orderOf_eq_one _
    omega
  rcases hca with h3 | h4'
  ·
    have hac : orderOf (a * c) = 3 := by rw [orderOf_mul_comm_eq]; exact h3
    exact (ReflTransGen.single (oddRel_mk ha hc hac)).tail (oddRel_mk hc hwD hcw)
  ·
    have hwc' : ¬ Commute w c := by
      intro h
      have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hw2 hc2).1 h)
      rw [hwc] at this
      exact absurd this (by decide)
    obtain ⟨z, hz, -, hcz, -, hzw⟩ := Bridge.exists_conj_eq_mul_of_odd_special hD hN hwD hc ha
      hwc' (by rw [hwc]; decide) h4' haw.symm hwaD
    have hz2 := hD.mul_self_eq_one hz
    have hcwa : orderOf (c * (w * a)) = 3 := by
      rw [← hzw, show c * (z * w * z) = z * (c * w) * z⁻¹ by
        rw [inv_eq_of_mul_eq_one_right hz2, ← mul_assoc, ← mul_assoc, hcz.eq]; group,
        orderOf_conj_eq, hcw]
    have hpath : ReflTransGen (OddRel D) w (w * a) :=
      (ReflTransGen.single (oddRel_mk hwD hc hwc)).tail (oddRel_mk hc hwaD hcwa)
    have hconj := reflTransGen_oddRel_conj hN x⁻¹ hpath
    rw [hwa, show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group,
      show x⁻¹ * w * x⁻¹⁻¹ = w by rw [inv_inv, mul_assoc, ← hxw.eq, ← mul_assoc,
        inv_mul_cancel, one_mul]] at hconj
    exact reflTransGen_oddRel_symm hconj

theorem reflTransGen_of_not_commute [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (hK : ∀ a ∈ D, ∃ c ∈ D, orderOf (a * c) = 3) {a y : G} (ha : a ∈ D) (hy : y ∈ D)
    (hay : ¬ Commute a y) : ReflTransGen (OddRel D) a y := by
  have hpos := orderOf_pos (a * y)
  have hle := h4 a ha y hy
  have h12 : orderOf (a * y) ≠ 1 ∧ orderOf (a * y) ≠ 2 := by
    constructor <;> intro h <;>
      refine hay ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ha)
        (hD.mul_self_eq_one hy)).2 ?_)
    · rw [orderOf_eq_one_iff.1 h, one_pow]
    · rw [← h]; exact pow_orderOf_eq_one _
  rcases (show orderOf (a * y) = 3 ∨ orderOf (a * y) = 4 by omega) with h3 | h4'
  · exact ReflTransGen.single (oddRel_mk ha hy h3)
  · have h1 := reflTransGen_sq hD hN h4 hK ha hy h4'
    have hya : orderOf (y * a) = 4 := by rw [orderOf_mul_comm_eq]; exact h4'
    have h2 := reflTransGen_sq hD hN h4 hK hy ha hya
    have hsq : (y * a) ^ 2 = (a * y) ^ 2 := by
      obtain ⟨-, -, hyw, -⟩ := sq_mem_of_orderOf_eq_four hD ha hy h4'
      have hyy := hD.mul_self_eq_one hy
      calc (y * a) ^ 2 = y * (a * y) ^ 2 * y⁻¹ := by rw [sq, sq]; group
        _ = (a * y) ^ 2 := by rw [hyw.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hsq] at h2
    exact h1.trans (reflTransGen_oddRel_symm h2)

theorem exists_conj_of_reflTransGen (hD : IsRootInvolutionSet D) {d e : G}
    (h : ReflTransGen (OddRel D) d e) :
    ∃ g ∈ Subgroup.closure {f | ReflTransGen (OddRel D) d f}, e = g * d * g⁻¹ := by
  induction h with
  | refl => exact ⟨1, Subgroup.one_mem _, by group⟩
  | @tail b c hb hbc ih =>
    obtain ⟨g, hg, rfl⟩ := ih
    have hbmem : g * d * g⁻¹ ∈ Subgroup.closure {f | ReflTransGen (OddRel D) d f} :=
      Subgroup.subset_closure hb
    have hcmem : c ∈ Subgroup.closure {f | ReflTransGen (OddRel D) d f} :=
      Subgroup.subset_closure (hb.tail hbc)
    refine ⟨g * d * g⁻¹ * c * g, Subgroup.mul_mem _ (Subgroup.mul_mem _ hbmem hcmem) hg, ?_⟩
    have := conj_eq_of_pow_three (hD.mul_self_eq_one hbc.1) (hD.mul_self_eq_one hbc.2.1)
      (by rw [← hbc.2.2]; exact pow_orderOf_eq_one _)
    rw [show g * d * g⁻¹ * c * g * d * (g * d * g⁻¹ * c * g)⁻¹ =
      g * d * g⁻¹ * c * (g * d * g⁻¹) * (g * d * g⁻¹ * c)⁻¹ by group]
    exact this.symm

end Components

open Relation Components

theorem components_conj {Y : Type u} [Group Y] [Finite Y] (H : Subgroup Y) (D : Set Y)
    (hDH : D ⊆ H) (hN : ∀ x ∈ H, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hinv : ∀ d ∈ D, orderOf d = 2)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (hsq : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hO2 : ∀ P : Subgroup Y, P ≤ H → IsPGroup 2 P → H ≤ Subgroup.normalizer (P : Set Y) →
      P = ⊥) :
    ∀ d ∈ D, ∀ e, Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d e →
      ∃ x ∈ Subgroup.closure
        {f | Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d f},
        e = x * d * x⁻¹ := by
  classical
  set D' : Set H := {x | (x : Y) ∈ D} with hD'
  have hord : ∀ x : H, orderOf x = orderOf (x : Y) := fun x => (Subgroup.orderOf_coe x).symm
  have hcases : ∀ d ∈ D', ∀ e ∈ D', orderOf (d * e) = 1 ∨ orderOf (d * e) = 2 ∨
      orderOf (d * e) = 3 ∨ orderOf (d * e) = 4 := by
    intro d hd e he
    have hle := h4 _ hd _ he
    have hpos := orderOf_pos (d * e)
    rw [hord, Subgroup.coe_mul] at hpos ⊢
    omega
  have hroot : IsRootInvolutionSet D' := by
    refine ⟨fun d hd => by rw [hord]; exact hinv _ hd, fun d hd e he => ?_,
      fun d hd e he h => ?_⟩
    · rcases hcases d hd e he with h | h | h | h <;> rw [h]
      · exact Or.inr (Or.inr odd_one)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (by decide))
      · exact Or.inr (Or.inl rfl)
    · show (((d * e) ^ 2 : H) : Y) ∈ D
      rw [Subgroup.coe_pow, Subgroup.coe_mul]
      exact hsq _ hd _ he (by rw [← Subgroup.coe_mul, ← hord]; exact h)
  have hN' : ∀ g x : H, x ∈ D' → g * x * g⁻¹ ∈ D' := fun g x hx => by
    show ((g * x * g⁻¹ : H) : Y) ∈ D
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN g g.2 x hx
  have h4' : ∀ d ∈ D', ∀ e ∈ D', orderOf (d * e) ≤ 4 := fun d hd e he => by
    rw [hord, Subgroup.coe_mul]
    exact h4 _ hd _ he
  have hK : ∀ a ∈ D', ∃ c ∈ D', orderOf (a * c) = 3 := by
    intro a ha
    by_contra hno
    push Not at hno
    have hpow : ∀ c ∈ D', (a * c) ^ 2 ^ 2 = 1 := by
      intro c hc
      refine orderOf_dvd_iff_pow_eq_one.1 ?_
      rcases hcases a ha c hc with h | h | h | h <;> rw [h]
      · exact one_dvd _
      · decide
      · exact absurd h (hno c hc)
      · decide
    have hmem : a ∈ CFSG.pCore 2 H := by
      rw [CFSG.BaerSuzuki.baer_suzuki_iff]
      intro g
      exact isPGroup_two_closure_pair (hroot.mul_self_eq_one ha)
        (hroot.mul_self_eq_one (hN' g a ha)) (hpow _ (hN' g a ha))
    have hnorm := CFSG.BaerSuzuki.Helpers.pCore_normal (G := H) 2
    have hP : (CFSG.pCore 2 H).map H.subtype = ⊥ := by
      refine hO2 _ (Subgroup.map_subtype_le _)
        ((CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2).map _) fun h hh => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hnorm.conj_mem n hn _, ?_⟩
        simp
      · rintro ⟨n, hn, hny⟩
        refine ⟨⟨h, hh⟩⁻¹ * n * ⟨h, hh⟩⁻¹⁻¹, hnorm.conj_mem n hn _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hny ⊢
        rw [hny]
        group
    have : (a : Y) ∈ (CFSG.pCore 2 H).map H.subtype := ⟨a, hmem, rfl⟩
    rw [hP, Subgroup.mem_bot] at this
    exact hroot.ne_one ha (Subtype.ext this)
  intro d hd e hde
  set d₀ : H := ⟨d, hDH hd⟩
  have hlift : ∃ e₀ : H, (e₀ : Y) = e ∧
      ReflTransGen (fun x y : H => x ∈ D' ∧ y ∈ D' ∧ x * y ≠ y * x) d₀ e₀ := by
    induction hde with
    | refl => exact ⟨d₀, rfl, .refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨b₀, hb₀, hpath⟩ := ih
      refine ⟨⟨c, hDH hbc.2.1⟩, rfl, hpath.tail ⟨?_, hbc.2.1, fun h => hbc.2.2 ?_⟩⟩
      · show (b₀ : Y) ∈ D
        rw [hb₀]
        exact hbc.1
      · have := congrArg Subtype.val h
        simpa [hb₀] using this
  obtain ⟨e₀, he₀, hpath⟩ := hlift
  have hodd' : ∀ f : H, ReflTransGen (fun x y : H => x ∈ D' ∧ y ∈ D' ∧ x * y ≠ y * x) d₀ f →
      ReflTransGen (OddRel D') d₀ f := by
    intro f hf
    induction hf with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      exact ih.trans (reflTransGen_of_not_commute hroot hN' h4' hK hbc.1 hbc.2.1 hbc.2.2)
  have hodd := hodd' e₀ hpath
  obtain ⟨g, hg, hge⟩ := exists_conj_of_reflTransGen hroot hodd
  refine ⟨(g : Y), ?_, by rw [← he₀, hge]; simp [d₀]⟩
  have hcomp : ∀ f : H, ReflTransGen (OddRel D') d₀ f →
      ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d (f : Y) := by
    intro f hf
    induction hf with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      refine ih.tail ⟨hbc.1, hbc.2.1, fun h => not_commute_of_oddRel hroot hbc ?_⟩
      exact Subtype.ext (by simpa using h)
  have hmap : (Subgroup.closure {f | ReflTransGen (OddRel D') d₀ f}).map H.subtype ≤
      Subgroup.closure
        {f | ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d f} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hcomp f hf
  exact hmap ⟨g, hg, rfl⟩


end CFSG.Timmesfeld

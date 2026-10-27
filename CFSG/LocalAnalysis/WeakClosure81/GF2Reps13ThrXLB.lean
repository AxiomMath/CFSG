module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXLA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_axis_of_nonorth (q y : Fin 3 → ZMod 3) (hq : ∀ i, q i ≠ 0)
    (hy : ∑ i, q i * y i ≠ 0) :
    ∃ α β : ZMod 3, ∃ i : Fin 3, α * q i + β * y i ≠ 0 ∧
      ∀ j, j ≠ i → α * q j + β * y j = 0 := by
  revert q y
  decide +kernel

private noncomputable def w16g_dot {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (u v : ↥X) : ZMod 3 :=
  ∑ᶠ U : ↥(s13IsoComps X), lam U (Additive.ofMul u) * lam U (Additive.ofMul v)

private theorem w16g_finite_subgroups : Finite (Subgroup W) :=
  Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective

private theorem w16g_dot_add_left {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (u v w : ↥X) :
    w16g_dot lam (u * v) w = w16g_dot lam u w + w16g_dot lam v w := by
  classical
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  simp only [w16g_dot, finsum_eq_sum_of_fintype]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun U _ => by rw [ofMul_mul, map_add, add_mul]

private theorem w16g_dot_add_right {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (u v w : ↥X) :
    w16g_dot lam u (v * w) = w16g_dot lam u v + w16g_dot lam u w := by
  classical
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  simp only [w16g_dot, finsum_eq_sum_of_fintype]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun U _ => by rw [ofMul_mul, map_add, mul_add]

private theorem w16g_dot_one_left {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (v : ↥X) :
    w16g_dot lam (1 : ↥X) v = 0 := by
  classical
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  simp [w16g_dot, ofMul_one]

private theorem w16g_dot_inv_left {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (u v : ↥X) :
    w16g_dot lam u⁻¹ v = -w16g_dot lam u v := by
  have h1 : w16g_dot lam u⁻¹ v + w16g_dot lam u v = 0 := by
    have h := (w16g_dot_add_left lam u⁻¹ u v).symm
    rwa [inv_mul_cancel, w16g_dot_one_left] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h1

private theorem w16g_dot_conj (h : HAb A X Q t 3)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) (u v : ↥X) :
    w16g_dot lam ⟨t * (u : MulAut W) * t⁻¹, h.hXA t h.htA _ u.2⟩
      ⟨t * (v : MulAut W) * t⁻¹, h.hXA t h.htA _ v.2⟩ = w16g_dot lam u v := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  obtain ⟨σ, c, -, hσcoord⟩ := exists_monomial h.hW hp3 hp32 h.hXe hl
    (fun x hx => h.hXA t h.htA x hx)
    (fun x hx => by simpa using h.hXA t⁻¹ (A.inv_mem h.htA) x hx)
  have hcu : ∀ c : (ZMod 3)ˣ, (c : ZMod 3) * (c : ZMod 3) = 1 := by decide
  simp only [w16g_dot, finsum_eq_sum_of_fintype]
  rw [← Equiv.sum_comp σ (fun U : s13IsoComps X =>
    lam U (Additive.ofMul ⟨t * (u : MulAut W) * t⁻¹, h.hXA t h.htA _ u.2⟩) *
      lam U (Additive.ofMul ⟨t * (v : MulAut W) * t⁻¹, h.hXA t h.htA _ v.2⟩))]
  apply Finset.sum_congr rfl
  intro U _
  have hu := hσcoord U u (h.hXA t h.htA _ u.2)
  have hv := hσcoord U v (h.hXA t h.htA _ v.2)
  have hc := hcu (c U)
  rw [hu, hv]
  calc ((c U : ZMod 3) * lam U (Additive.ofMul u)) *
        ((c U : ZMod 3) * lam U (Additive.ofMul v))
      = ((c U : ZMod 3) * (c U : ZMod 3)) *
          (lam U (Additive.ofMul u) * lam U (Additive.ofMul v)) := by ring
    _ = lam U (Additive.ofMul u) * lam U (Additive.ofMul v) := by rw [hc, one_mul]

private theorem w16g_mem_supp_zpowers_iff {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) (x : ↥X)
    (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (x : MulAut W)) ↔
      lam U (Additive.ofMul x) ≠ 0 := by
  simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  exact (coord_ne_zero_iff hl x U).symm

private theorem w16g_commSub_zpowers_eq_bot_iff {U : Subgroup W} {z : MulAut W} :
    commSub U (Subgroup.zpowers z) = ⊥ ↔ z ∈ centSub U := by
  rw [commSub_eq_bot_iff]
  constructor
  · intro h
    rw [mem_centSub]
    intro u hu
    exact (mem_fixV.mp (h hu)) z (Subgroup.mem_zpowers z)
  · intro h u hu
    rw [mem_fixV]
    intro w hw
    exact mem_centSub.mp (Subgroup.zpowers_le.mpr h hw) u hu

private theorem w16g_supp_zpowers_inv_le (h : HAb A X Q t 3)
    (he : (s13Supp X Q).ncard = 3) {y : ↥X}
    (hyinv : t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹) :
    s13Supp X (Subgroup.zpowers (y : MulAut W)) ⊆ s13Supp X Q := by
  classical
  haveI : Finite (Subgroup W) := w16g_finite_subgroups
  have hcost : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = 3 := by
    have h1 := (cost_commSub_Q h).1
    have h2 := w16g_three_rk_eq_six h he
    omega
  have hQmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    rw [show MulAut.conj (1 : MulAut W) = 1 from by ext w; simp [MulAut.conj_apply]]
    exact Subgroup.map_id Q
  have ht1 : (1 : MulAut W) * t * 1⁻¹ = t := by simp
  have hcost' : rk ↥(commSub (commSub ⊤ (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom))
      (Subgroup.zpowers ((1 : MulAut W) * t * 1⁻¹))) = 3 := by
    rw [hQmap1, ht1]; exact hcost
  have hsatU : ∀ U ∈ s13IsoComps X, U ∉ s13Supp X Q →
      commSub U (Subgroup.zpowers t) = ⊥ := by
    intro U hU hUe
    have hU' : U ∉ s13Supp X (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom) := by
      rw [hQmap1]; exact hUe
    have h1 := (saturation h (a := 1) A.one_mem hcost').1 U hU hU'
    simpa [ht1] using h1
  intro U hU
  by_contra hUne
  have hUX : U ∈ s13IsoComps X := hU.1
  have hcent : t ∈ centSub U :=
    (w16g_commSub_zpowers_eq_bot_iff (U := U) (z := t)).mp (hsatU U hUX hUne)
  have htinvcent : t⁻¹ ∈ centSub U := (centSub U).inv_mem hcent
  have ht_fix : ∀ a ∈ U, t a = a := fun a ha => mem_centSub.mp hcent a ha
  have htinv_fix : ∀ a ∈ U, t⁻¹ a = a := fun a ha => mem_centSub.mp htinvcent a ha
  have hstab : StableUnder X U := s13IsoComps_stable hUX
  have hyy : (y : MulAut W) * ((y : MulAut W) * (y : MulAut W)) = 1 := by
    rw [← mul_assoc, ← pow_two, ← pow_succ]
    exact h.hXe.2 (y : MulAut W) y.2
  have hyinv_eq : (y : MulAut W)⁻¹ = (y : MulAut W) * (y : MulAut W) :=
    (mul_eq_one_iff_eq_inv'.mp hyy).symm
  have hycent : (y : MulAut W) ∈ centSub U := by
    rw [mem_centSub]
    intro u hu
    have hyu : (y : MulAut W) u ∈ U := hstab (y : MulAut W) y.2 u hu
    have hLHS : (t * (y : MulAut W) * t⁻¹) u = (y : MulAut W) u := by
      show t ((y : MulAut W) (t⁻¹ u)) = (y : MulAut W) u
      rw [htinv_fix u hu, ht_fix ((y : MulAut W) u) hyu]
    have hRHS : (t * (y : MulAut W) * t⁻¹) u = (y : MulAut W)⁻¹ u := by rw [hyinv]
    have hyu_eq : (y : MulAut W) u = (y : MulAut W)⁻¹ u := hLHS.symm.trans hRHS
    rw [hyinv_eq, MulAut.mul_apply] at hyu_eq
    have h2 := congrArg (fun a : W => (y : MulAut W)⁻¹ a) hyu_eq
    simp only [MulAut.inv_apply_self] at h2
    exact h2.symm
  exact hU.2 ((w16g_commSub_zpowers_eq_bot_iff (U := U) (z := (y : MulAut W))).mpr hycent)

private theorem w16g_sum_eq_fin3_sum {α : Type*} [Fintype α] (e : Set α) [Fintype ↥e]
    (eu : ↥e ≃ Fin 3) (F : α → ZMod 3) (hF : ∀ a, a ∉ e → F a = 0) :
    (∑ a : α, F a) = ∑ i : Fin 3, F (eu.symm i).1 := by
  classical
  let s : Finset α := Finset.univ.filter (fun a => a ∈ e)
  have hs : ∀ a, a ∈ s ↔ a ∈ e := by
    intro a; simp [s]
  have h1 : (∑ a : α, F a) = ∑ a ∈ s, F a := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro a _ ha
    exact hF a (fun h => ha ((hs a).mpr h))
  have h2 : (∑ a ∈ s, F a) = ∑ a : ↥e, F a.1 :=
    Finset.sum_subtype s hs F
  have h3 : (∑ a : ↥e, F a.1) = ∑ i : Fin 3, F (eu.symm i).1 :=
    (Equiv.sum_comp eu.symm (fun a : ↥e => F a.1)).symm
  rw [h1, h2, h3]

private theorem w16g_three_dot_eq_zero_of_inv (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) :
    ∀ q : ↥X, (q : MulAut W) ∈ Q → q ≠ 1 → ∀ y : ↥X,
      t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹ → w16g_dot lam q y = 0 := by
  classical
  haveI : Finite (Subgroup W) := w16g_finite_subgroups
  haveI : Fintype ↥(s13IsoComps X) := Fintype.ofFinite _
  intro q hqQ hq1 y hyinv
  by_contra hdot
  have hzpeq : s13Supp X (Subgroup.zpowers (q : MulAut W)) = s13Supp X Q := by
    have hzple : Subgroup.zpowers (q : MulAut W) ≤ Q := Subgroup.zpowers_le.mpr hqQ
    have hcarddvd : Nat.card ↥(Subgroup.zpowers (q : MulAut W)) ∣ 3 := by
      rw [← hQ3]; exact Subgroup.card_dvd_of_le hzple
    have hcardne1 : Nat.card ↥(Subgroup.zpowers (q : MulAut W)) ≠ 1 := by
      intro h1
      have hbot : Subgroup.zpowers (q : MulAut W) = ⊥ := Subgroup.card_eq_one.mp h1
      refine hq1 (Subtype.ext ?_)
      exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers (q : MulAut W))
    have hcard3 : Nat.card ↥(Subgroup.zpowers (q : MulAut W)) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hcarddvd with h1 | h3
      · exact absurd h1 hcardne1
      · exact h3
    exact congrArg (s13Supp X)
      (Subgroup.eq_of_le_of_card_ge hzple (by rw [hQ3, hcard3]))
  let E : Set ↥(s13IsoComps X) := {U | (U : Subgroup W) ∈ s13Supp X Q}
  haveI : Fintype ↥E := Fintype.ofFinite _
  have hEimage : (Subtype.val : ↥(s13IsoComps X) → Subgroup W) '' E =
      s13Supp X Q := by
    ext U
    constructor
    · rintro ⟨V, hVE, rfl⟩
      exact hVE
    · intro hUe
      exact ⟨⟨U, hUe.1⟩, hUe, rfl⟩
  have hcardE : Fintype.card ↥E = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      ← Set.ncard_image_of_injective E (Subtype.val_injective :
        Function.Injective (Subtype.val : ↥(s13IsoComps X) → Subgroup W)), hEimage]
    exact he
  let eu : ↥E ≃ Fin 3 := Fintype.equivFinOfCardEq hcardE
  have hy_e : s13Supp X (Subgroup.zpowers (y : MulAut W)) ⊆ s13Supp X Q :=
    w16g_supp_zpowers_inv_le h he hyinv
  have hq'ne : ∀ i : Fin 3, lam ((eu.symm i).1) (Additive.ofMul q) ≠ 0 := by
    intro i
    have hmem : ((eu.symm i).1 : Subgroup W) ∈
        s13Supp X (Subgroup.zpowers (q : MulAut W)) := by
      rw [hzpeq]
      exact (eu.symm i).2
    exact (w16g_mem_supp_zpowers_iff hl q ((eu.symm i).1)).mp hmem
  have hF : ∀ U : ↥(s13IsoComps X), U ∉ E →
      lam U (Additive.ofMul q) * lam U (Additive.ofMul y) = 0 := by
    intro U hU
    have hUne : (U : Subgroup W) ∉ s13Supp X Q := hU
    have hq0 : lam U (Additive.ofMul q) = 0 := by
      by_contra hne
      exact hUne (hzpeq ▸ (w16g_mem_supp_zpowers_iff hl q U).mpr hne)
    have hy0 : lam U (Additive.ofMul y) = 0 := by
      by_contra hne
      exact hUne (hy_e ((w16g_mem_supp_zpowers_iff hl y U).mpr hne))
    rw [hq0, hy0, mul_zero]
  have hsum_eq : (∑ U : ↥(s13IsoComps X),
      lam U (Additive.ofMul q) * lam U (Additive.ofMul y)) =
      ∑ i : Fin 3, lam ((eu.symm i).1) (Additive.ofMul q) *
        lam ((eu.symm i).1) (Additive.ofMul y) :=
    w16g_sum_eq_fin3_sum E eu
      (fun U => lam U (Additive.ofMul q) * lam U (Additive.ofMul y)) hF
  have hdot' : (∑ᶠ U : ↥(s13IsoComps X),
      lam U (Additive.ofMul q) * lam U (Additive.ofMul y)) ≠ 0 := by
    simpa only [w16g_dot] using hdot
  rw [finsum_eq_sum_of_fintype] at hdot'
  rw [hsum_eq] at hdot'
  obtain ⟨α, β, i, hne, hzero⟩ := w16g_axis_of_nonorth
    (fun i => lam ((eu.symm i).1) (Additive.ofMul q))
    (fun i => lam ((eu.symm i).1) (Additive.ofMul y)) hq'ne hdot'
  let z : ↥X := q ^ α.val * y ^ β.val
  have hzcoord : ∀ U : ↥(s13IsoComps X),
      lam U (Additive.ofMul z) = (α : ZMod 3) * lam U (Additive.ofMul q) +
        (β : ZMod 3) * lam U (Additive.ofMul y) := by
    intro U
    show lam U (Additive.ofMul (q ^ α.val * y ^ β.val)) = _
    rw [ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hE_iff : ∀ U : ↥E, lam U.1 (Additive.ofMul z) ≠ 0 ↔ U = eu.symm i := by
    intro U
    have hj : eu.symm (eu U) = U := Equiv.symm_apply_apply eu U
    have hcoord : lam U.1 (Additive.ofMul z) =
        α * lam ((eu.symm (eu U)).1) (Additive.ofMul q) +
        β * lam ((eu.symm (eu U)).1) (Additive.ofMul y) := by
      rw [hzcoord U.1, hj]
    rw [hcoord]
    constructor
    · intro hne'
      by_contra hUne
      exact hne' (hzero (eu U) (fun h => hUne (by rw [← h, hj])))
    · intro hU
      have : eu U = i := by rw [hU, Equiv.apply_symm_apply]
      rw [this]
      exact hne
  have hsupp_z : s13Supp X (Subgroup.zpowers (z : MulAut W)) =
      {((eu.symm i).1 : Subgroup W)} := by
    ext U
    rw [Set.mem_singleton_iff]
    constructor
    · intro hU
      have hUX : U ∈ s13IsoComps X := hU.1
      have hzU : lam ⟨U, hUX⟩ (Additive.ofMul z) ≠ 0 :=
        (w16g_mem_supp_zpowers_iff hl z ⟨U, hUX⟩).mp hU
      have hUe : U ∈ s13Supp X Q := by
        by_contra hUne
        apply hzU
        rw [hzcoord ⟨U, hUX⟩]
        have hq0 : lam ⟨U, hUX⟩ (Additive.ofMul q) = 0 := by
          by_contra hne'
          exact hUne (hzpeq ▸ (w16g_mem_supp_zpowers_iff hl q ⟨U, hUX⟩).mpr hne')
        have hy0 : lam ⟨U, hUX⟩ (Additive.ofMul y) = 0 := by
          by_contra hne'
          exact hUne (hy_e ((w16g_mem_supp_zpowers_iff hl y ⟨U, hUX⟩).mpr hne'))
        rw [hq0, hy0, mul_zero, mul_zero, add_zero]
      have hEU : (⟨⟨U, hUX⟩, hUe⟩ : ↥E) = eu.symm i :=
        (hE_iff ⟨⟨U, hUX⟩, hUe⟩).mp hzU
      exact congrArg (fun V : ↥E => (V.1 : Subgroup W)) hEU
    · intro hU
      rw [hU]
      exact (w16g_mem_supp_zpowers_iff hl z (eu.symm i).1).mpr
        ((hE_iff (eu.symm i)).mpr rfl)
  have hz1 : (z : MulAut W) ≠ 1 := by
    intro hz1
    have hmem : ((eu.symm i).1 : Subgroup W) ∈
        s13Supp X (Subgroup.zpowers (z : MulAut W)) := by
      rw [hsupp_z]; exact Set.mem_singleton _
    have hne' : lam ((eu.symm i).1) (Additive.ofMul z) ≠ 0 :=
      (w16g_mem_supp_zpowers_iff hl z (eu.symm i).1).mp hmem
    apply hne'
    rw [show z = 1 from Subtype.ext hz1]
    simp [ofMul_one]
  exact hH0 (z : MulAut W) z.2 hz1 (by rw [hsupp_z, Set.ncard_singleton])

theorem w16g_three_orth_core (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) :
    ∀ q : ↥X, (q : MulAut W) ∈ Q → ∀ x : ↥X,
      ∑ᶠ U : ↥(s13IsoComps X), lam U (Additive.ofMul q) * lam U (Additive.ofMul x) = 0 := by
  classical
  haveI : Finite (Subgroup W) := w16g_finite_subgroups
  intro q hqQ x
  by_cases hq1 : q = 1
  · subst hq1
    change w16g_dot lam (1 : ↥X) x = 0
    exact w16g_dot_one_left lam x
  · have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
    have htinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    let y : ↥X := ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
      X.mul_mem (h.hXA t h.htA _ x.2) (X.inv_mem x.2)⟩
    have hyinv : t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹ := by
      have h1 : t * (y : MulAut W) * t⁻¹ =
          (x : MulAut W) * (t * (x : MulAut W)⁻¹ * t⁻¹) := by
        show t * (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹) * t⁻¹ =
          (x : MulAut W) * (t * (x : MulAut W)⁻¹ * t⁻¹)
        rw [htinvt]
        rw [show t * (t * (x : MulAut W) * t * (x : MulAut W)⁻¹) * t =
            (t * t) * (x : MulAut W) * (t * (x : MulAut W)⁻¹ * t) from by group]
        rw [htt, one_mul]
      have h2 : (y : MulAut W)⁻¹ =
          (x : MulAut W) * (t * (x : MulAut W)⁻¹ * t⁻¹) := by
        show (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)⁻¹ =
          (x : MulAut W) * (t * (x : MulAut W)⁻¹ * t⁻¹)
        group
      exact h1.trans h2.symm
    have hkey := w16g_three_dot_eq_zero_of_inv h hH0 hQ3 he hl q hqQ hq1 y hyinv
    have hconjdot : w16g_dot lam q ⟨t * (x : MulAut W) * t⁻¹, h.hXA t h.htA _ x.2⟩ =
        -w16g_dot lam q x := by
      have hu : t * (t * (q : MulAut W) * t⁻¹) * t⁻¹ = (q : MulAut W) := by
        rw [htinvt]
        rw [show t * (t * (q : MulAut W) * t) * t =
            (t * t) * (q : MulAut W) * (t * t) from by group]
        rw [htt, one_mul, mul_one]
      have hmain := w16g_dot_conj h hl
        ⟨t * (q : MulAut W) * t⁻¹, h.hXA t h.htA _ q.2⟩ x
      have h1 : (⟨t * (t * (q : MulAut W) * t⁻¹) * t⁻¹,
          h.hXA t h.htA _ (h.hXA t h.htA _ q.2)⟩ : ↥X) = q := Subtype.ext hu
      rw [h1] at hmain
      have h2 : (⟨t * (q : MulAut W) * t⁻¹, h.hXA t h.htA _ q.2⟩ : ↥X) = q⁻¹ :=
        Subtype.ext (h.hQinv (q : MulAut W) hqQ)
      rw [h2, w16g_dot_inv_left] at hmain
      exact hmain
    have hconjx_eq : w16g_dot lam q ⟨t * (x : MulAut W) * t⁻¹, h.hXA t h.htA _ x.2⟩ =
        w16g_dot lam q y + w16g_dot lam q x := by
      have hxy : (⟨t * (x : MulAut W) * t⁻¹, h.hXA t h.htA _ x.2⟩ : ↥X) = y * x := by
        apply Subtype.ext
        show t * (x : MulAut W) * t⁻¹ =
          (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹) * (x : MulAut W)
        group
      rw [hxy, w16g_dot_add_right]
    have hB : w16g_dot lam q x = 0 := by
      have h1 : w16g_dot lam q y + w16g_dot lam q x = -w16g_dot lam q x := by
        rw [← hconjx_eq, hconjdot]
      rw [hkey, zero_add] at h1
      have h2 : w16g_dot lam q x + w16g_dot lam q x = 0 := by
        have hh := congrArg (fun z => z + w16g_dot lam q x) h1
        simpa using hh
      have h3 : (2 : ZMod 3) * w16g_dot lam q x = 0 := by
        rw [two_mul]; exact h2
      exact (mul_eq_zero.mp h3).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
    change w16g_dot lam q x = 0
    exact hB

end CFSG.LocalAnalysis.WeakClosure81

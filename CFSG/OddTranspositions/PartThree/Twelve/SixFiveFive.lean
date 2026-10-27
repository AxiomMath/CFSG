module

public import CFSG.OddTranspositions.PartThree.Twelve.SixFiveEich
import CFSG.OddTranspositions.PartThree.Twelve.FiveChartBasic
import CFSG.OddTranspositions.PartThree.Twelve.SixFiveLocal
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.PartThree.CommSetConj

public section

namespace CFSG.OddTranspositions.PartThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
  PartFour.TableE1Five PartFour.FiveEichler

variable {G : Type} [Group G] {D : Set G}

namespace FiveChart

variable {hC : HypothesisC D} {n : ℕ}


private theorem act_eq_or_neg {m : ℕ} {g : GL (Fin m) (ZMod 5)} {x y : Fin m → ZMod 5}
    (h : x = y ∨ x = -y) : act g x = act g y ∨ act g x = -act g y := by
  rcases h with rfl | rfl
  · left; rfl
  · right; simp

private theorem eich_eq_or_neg {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {e β : Fin n → ZMod 5} {x y : Fin n → ZMod 5} (h : x = y ∨ x = -y) :
    eich b e β x = eich b e β y ∨ eich b e β x = -eich b e β y := by
  rcases h with rfl | rfl
  · left; rfl
  · right; rw [eich_neg]

private theorem conj_mem_inter (hC : HypothesisC D) {w x g : G} (hgd : Commute g hC.d)
    (hgw : Commute g w) (hx : x ∈ commSet D hC.d ∩ commSet D w) :
    g * x * g⁻¹ ∈ commSet D hC.d ∩ commSet D w :=
  ⟨conj_mem_commSet_of_commute hC.setup.normal hgd hx.1,
    conj_mem_commSet_of_commute hC.setup.normal hgw hx.2⟩

private theorem commute_of_mem_closure_L_d {w g : G}
    (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w)) : Commute g hC.d :=
  OddLocal.commute_of_mem_closure_commSet (Subgroup.closure_mono Set.inter_subset_left hg)

private theorem commute_of_mem_closure_L_w {w g : G}
    (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w)) : Commute g w :=
  OddLocal.commute_of_mem_closure_commSet (Subgroup.closure_mono Set.inter_subset_right hg)

private theorem d_not_mem_closure_L {w : G} (hwd : ¬ Commute w hC.d) :
    hC.d ∉ Subgroup.closure (commSet D hC.d ∩ commSet D w) := by
  intro hd
  exact hwd (commute_of_mem_closure_L_w hd).symm

private theorem mem_Halpha_of_mem_commSet (hα : hC.alpha = {hC.d}) {a : G}
    (ha : a ∈ commSet D hC.d) : a ∈ Halpha D hC.alpha := by
  change a ∈ Subgroup.closure (DalphaStar D hC.alpha)
  rw [Nine.DalphaStar_eq_commSet hC hα]
  exact Subgroup.subset_closure ha

private theorem mem_Halpha_of_mem_closure_L (hα : hC.alpha = {hC.d}) {w g : G}
    (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w)) : g ∈ Halpha D hC.alpha := by
  change g ∈ Subgroup.closure (DalphaStar D hC.alpha)
  rw [Nine.DalphaStar_eq_commSet hC hα]
  exact Subgroup.closure_mono Set.inter_subset_left hg

private theorem mem_center_Halpha_of_actsAsEich_zero (c : FiveChart hC n)
    (hα : hC.alpha = {hC.d}) {e : Fin n → ZMod 5} {g : G}
    (hg0 : c.ActsAsEich e 0 g) (hgd : Commute g hC.d)
    (hgH : g ∈ Halpha D hC.alpha) :
    (⟨g, hgH⟩ : Halpha D hC.alpha) ∈ Subgroup.center (Halpha D hC.alpha) := by
  rw [Subgroup.mem_center_iff]
  intro m
  have hmG : (m : G) ∈ Halpha D hC.alpha := m.2
  have hcomm : Commute g (m : G) := by
    change (m : G) ∈ Subgroup.closure (DalphaStar D hC.alpha) at hmG
    rw [Nine.DalphaStar_eq_commSet hC hα] at hmG
    refine commute_of_mem_closure (S := {g}) (T := commSet D hC.d) (fun x hx y hy => ?_)
      (Subgroup.subset_closure (Set.mem_singleton g)) hmG
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mul_inv_eq_iff_eq_mul.mp (ActsAsEich.conj_eq_of_zero hg0 hgd hy)
  refine Subtype.ext ?_
  exact hcomm.eq.symm

private theorem actsAsEich_zero_pow_five (c : FiveChart hC n) {e β : Fin n → ZMod 5} {g : G}
    (hg : c.ActsAsEich e β g) (hgd : Commute g hC.d) (he : c.b e e = 0)
    (hβ : c.b β e = 0) : c.ActsAsEich e 0 (g ^ 5) := by
  have h := ActsAsEich.pow hg hgd he hβ 5
  have h5 : (5 : ℕ) • β = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 5) 5 β]
    have h5c : ((5 : ℕ) : ZMod 5) = 0 := by decide
    rw [h5c, zero_smul]
  rwa [h5] at h

private theorem two_sq_mul_sq_ne_zero {c₀ μ : ZMod 5} (hc₀ : c₀ ≠ 0) (hμ : μ ≠ 0) :
    2 * c₀ ^ 2 * μ ^ 2 ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 2 hc₀)) (pow_ne_zero 2 hμ)

private theorem b_vec_ne_zero_of_ne (c : FiveChart hC n) {w v₀ x : G} {e : Fin n → ZMod 5}
    (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w) (hx : x ∈ commSet D hC.d ∩ commSet D w)
    (hev₀ : c.b e (c.vec v₀) = 0) (hxe : c.b (c.vec x) e ≠ 0)
    (hP : ∀ y ∈ commSet D hC.d ∩ commSet D v₀, (Commute y w ↔ c.b (c.vec y) e = 0)) :
    c.b (c.vec x) (c.vec v₀) ≠ 0 := by
  intro h0
  have hx_ne_v₀ : x ≠ v₀ := by
    intro hxv
    exact hxe (by rw [hxv, c.hsym]; exact hev₀)
  have hxv₀ : Commute x v₀ := (c.commute_iff x hx.1 v₀ hv₀.1 hx_ne_v₀).2 h0
  have hxP : x ∈ commSet D hC.d ∩ commSet D v₀ := ⟨hx.1, hx.1.1, hxv₀, hx_ne_v₀⟩
  exact hxe ((hP x hxP).1 hx.2.2.1)

private theorem vec_eq_or_neg_eich (c : FiveChart hC n) {x' y m x v₀ : G} {e β : Fin n → ZMod 5}
    (hvec_x' : c.vec x' = eich c.b e β (c.vec x) ∨ c.vec x' = -eich c.b e β (c.vec x))
    (hstep1 : c.vec y = act (refl c.b (c.vec x')) (c.vec m) ∨
      c.vec y = -act (refl c.b (c.vec x')) (c.vec m))
    (hvec_m : c.vec m = act (refl c.b (c.vec x)) (c.vec v₀) ∨
      c.vec m = -act (refl c.b (c.vec x)) (c.vec v₀)) :
    c.vec y = act (refl c.b (eich c.b e β (c.vec x))) (act (refl c.b (c.vec x)) (c.vec v₀)) ∨
      c.vec y =
        -act (refl c.b (eich c.b e β (c.vec x))) (act (refl c.b (c.vec x)) (c.vec v₀)) := by
  have hrefl : refl c.b (c.vec x') = refl c.b (eich c.b e β (c.vec x)) := by
    rcases hvec_x' with h | h
    · rw [h]
    · rw [h, refl_neg]
  have hstep1' : c.vec y = act (refl c.b (eich c.b e β (c.vec x))) (c.vec m) ∨
      c.vec y = -act (refl c.b (eich c.b e β (c.vec x))) (c.vec m) := by
    rcases hstep1 with h | h
    · left; rwa [hrefl] at h
    · right; rwa [hrefl] at h
  have hstep2 : act (refl c.b (eich c.b e β (c.vec x))) (c.vec m) =
        act (refl c.b (eich c.b e β (c.vec x))) (act (refl c.b (c.vec x)) (c.vec v₀)) ∨
      act (refl c.b (eich c.b e β (c.vec x))) (c.vec m) =
        -act (refl c.b (eich c.b e β (c.vec x))) (act (refl c.b (c.vec x)) (c.vec v₀)) :=
    act_eq_or_neg (g := refl c.b (eich c.b e β (c.vec x))) hvec_m
  exact eq_or_neg_of_eq_or_neg
    (Or.imp Eq.symm (fun h => by rw [h, neg_neg]) hstep1') hstep2

theorem perp_of_mem_five (c : FiveChart hC n) (hn : 5 ≤ n) {w v₀ : G} {e : Fin n → ZMod 5}
    (hwd : ¬ Commute w hC.d) (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w)
    (he : c.b e e = 0) (he0 : e ≠ 0) (hev₀ : c.b e (c.vec v₀) = 0)
    (hP : ∀ x ∈ commSet D hC.d ∩ commSet D v₀, (Commute x w ↔ c.b (c.vec x) e = 0)) :
    ∀ x ∈ commSet D hC.d ∩ commSet D w, c.b (c.vec x) e = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro x hx
  by_contra hxe
  have hxnorm : c.b (c.vec x) (c.vec x) = 1 := c.norm_vec x hx.1
  have hv₀norm : c.b (c.vec v₀) (c.vec v₀) = 1 := c.norm_vec v₀ hv₀.1
  have hc₀ : c.b (c.vec x) (c.vec v₀) ≠ 0 := b_vec_ne_zero_of_ne c hv₀ hx hev₀ hxe hP
  obtain ⟨β, hβv₀, hβe, hβ⟩ :=
    exists_norm_perp_of_singular c.hsym c.hnd hn hv₀norm he he0 hev₀
      (2 * c.b (c.vec x) (c.vec v₀) ^ 2 * c.b (c.vec x) e ^ 2)⁻¹
  obtain ⟨g, hgL, hgβ⟩ := exists_actsAsEich_of_local c hn hwd hv₀ he he0 hev₀ hP hβv₀ hβe
  have hgd : Commute g hC.d := commute_of_mem_closure_L_d hgL
  have hgw : Commute g w := commute_of_mem_closure_L_w hgL
  let x' : G := g * x * g⁻¹
  have hx' : x' ∈ commSet D hC.d ∩ commSet D w := conj_mem_inter hC hgd hgw hx
  have hvec_x' : c.vec x' = eich c.b e β (c.vec x) ∨
      c.vec x' = -eich c.b e β (c.vec x) := hgβ x hx.1
  let m : G := x * v₀ * x⁻¹
  have hm : m ∈ commSet D hC.d ∩ commSet D w := conj_mem_inter hC hx.1.2.1 hx.2.2.1 hv₀
  have hvec_m : c.vec m = act (refl c.b (c.vec x)) (c.vec v₀) ∨
      c.vec m = -act (refl c.b (c.vec x)) (c.vec v₀) := c.vec_conj_eq_act hx.1 hv₀.1
  let y : G := x' * m * x'⁻¹
  have hy : y ∈ commSet D hC.d ∩ commSet D w := conj_mem_inter hC hx'.1.2.1 hx'.2.2.1 hm
  have hstep1 : c.vec y = act (refl c.b (c.vec x')) (c.vec m) ∨
      c.vec y = -act (refl c.b (c.vec x')) (c.vec m) := c.vec_conj_eq_act hx'.1 hm.1
  have hvecy := vec_eq_or_neg_eich c hvec_x' hstep1 hvec_m
  have hβ' : 2 * c.b (c.vec x) (c.vec v₀) ^ 2 * c.b (c.vec x) e ^ 2 * c.b β β = 1 := by
    rw [hβ]
    exact mul_inv_cancel₀ (two_sq_mul_sq_ne_zero hc₀ hxe)
  obtain ⟨hzv₀, hze⟩ :=
    b_act_refl_eich_eq_zero_and_ne_zero c.hsym hv₀norm he hev₀ hxnorm hβv₀ hβe hβ'
  have hyv₀ : c.b (c.vec y) (c.vec v₀) = 0 := (c.b_vec_eq_zero_iff hvecy).2 hzv₀
  have hye : c.b (c.vec y) e ≠ 0 := mt (c.b_vec_eq_zero_iff hvecy).1 hze
  have hy_ne_v₀ : y ≠ v₀ := fun hyv => hye (by rw [hyv, c.hsym]; exact hev₀)
  have hyv₀' : y ∈ commSet D v₀ :=
    ⟨hy.1.1, (c.commute_iff y hy.1 v₀ hv₀.1 hy_ne_v₀).2 hyv₀, hy_ne_v₀⟩
  exact hye ((hP y ⟨hy.1, hyv₀'⟩).1 hy.2.2.1)

theorem local_eq_of_perp_five (c : FiveChart hC n) (hn : 5 ≤ n) {w u : G} {e : Fin n → ZMod 5}
    (hw : w ∈ D) (hwd : ¬ Commute w hC.d) (h5 : orderOf (hC.d * w) = 5)
    (he0 : e ≠ 0) (hΓe : ∀ x ∈ commSet D hC.d ∩ commSet D w, c.b (c.vec x) e = 0)
    (hu : u ∈ commSet D hC.d ∩ commSet D w) :
    ∀ x ∈ commSet D hC.d ∩ commSet D u, (Commute x w ↔ c.b (c.vec x) e = 0) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hz0, hzu, hznorm, hP⟩ := exists_local_hyperplane c hn hw hwd hu
  have hz : c.b z z = 0 := by
    rw [if_pos h5] at hznorm
    exact hznorm
  have heu : c.b e (c.vec u) = 0 := by
    rw [c.hsym]
    exact hΓe u hu
  have hforall : ∀ y, c.b y y = 1 → c.b y (c.vec u) = 0 → c.b y z = 0 → c.b y e = 0 := by
    intro y hy hyu hyz
    obtain ⟨a, ha, hva⟩ := c.exists_vec y hy
    have hay_u : c.b (c.vec a) (c.vec u) = 0 := (c.b_vec_eq_zero_iff hva).2 hyu
    have hay_z : c.b (c.vec a) z = 0 := (c.b_vec_eq_zero_iff hva).2 hyz
    have ha_ne_u : a ≠ u := by
      intro h
      rw [h, c.norm_vec u hu.1] at hay_u
      exact one_ne_zero hay_u
    have ha_u : a ∈ commSet D u :=
      ⟨ha.1, (c.commute_iff a ha u hu.1 ha_ne_u).2 hay_u, ha_ne_u⟩
    have haw : Commute a w := (hP a ⟨ha, ha_u⟩).2 hay_z
    have ha_w : a ∈ commSet D w :=
      ⟨ha.1, haw, by intro h; rw [h] at ha; exact hwd ha.2.1⟩
    have hae : c.b (c.vec a) e = 0 := hΓe a ⟨ha, ha_w⟩
    exact (c.b_vec_eq_zero_iff hva).1 hae
  obtain ⟨l, hl⟩ :=
    eq_smul_of_forall_perp_singular c.hsym c.hnd hn (c.norm_vec u hu.1) hz hz0 hzu heu hforall
  have hl0 : l ≠ 0 := by
    intro h
    apply he0
    rw [hl, h, zero_smul]
  intro x hx
  rw [hP x hx, hl, LinearMap.BilinForm.smul_right, mul_eq_zero_iff_left hl0]

private theorem act_refl_beta_perp (c : FiveChart hC n) {a : G} {e β : Fin n → ZMod 5}
    (ha : a ∈ commSet D hC.d) (hae : c.b (c.vec a) e = 0) (hβe : c.b β e = 0) :
    c.b (act (refl c.b (c.vec a)) β) e = 0 := by
  have hnorm := c.norm_vec a ha
  have hae' : act (refl c.b (c.vec a)) e = e :=
    act_refl_of_perp hnorm (by rw [c.hsym]; exact hae)
  have hisom : c.b (act (refl c.b (c.vec a)) β) (act (refl c.b (c.vec a)) e) = c.b β e :=
    (mem_isomGroup.mp (refl_mem_isomGroup c.hsym (c.vec a))) β e
  rw [hae', hβe] at hisom
  exact hisom

private theorem vec_conj_eich (c : FiveChart hC n) {a g y y' : G} {e β : Fin n → ZMod 5}
    (hnorm : c.b (c.vec a) (c.vec a) = 1) (hae : c.b (c.vec a) e = 0)
    (hy'vec : c.vec y' = act (refl c.b (c.vec a)) (c.vec y) ∨
      c.vec y' = -act (refl c.b (c.vec a)) (c.vec y))
    (hinner : c.vec (g * y' * g⁻¹) = eich c.b e β (c.vec y') ∨
      c.vec (g * y' * g⁻¹) = -eich c.b e β (c.vec y'))
    (h3 : c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        act (refl c.b (c.vec a)) (c.vec (g * y' * g⁻¹)) ∨
      c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        -act (refl c.b (c.vec a)) (c.vec (g * y' * g⁻¹))) :
    c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        eich c.b e (act (refl c.b (c.vec a)) β) (c.vec y) ∨
      c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        -eich c.b e (act (refl c.b (c.vec a)) β) (c.vec y) := by
  have hinner' : c.vec (g * y' * g⁻¹) =
        eich c.b e β (act (refl c.b (c.vec a)) (c.vec y)) ∨
      c.vec (g * y' * g⁻¹) =
        -eich c.b e β (act (refl c.b (c.vec a)) (c.vec y)) :=
    eq_or_neg_of_eq_or_neg
      (Or.imp Eq.symm (fun h => by rw [h, neg_neg]) hinner) (eich_eq_or_neg hy'vec)
  have h3' : c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        act (refl c.b (c.vec a))
          (eich c.b e β (act (refl c.b (c.vec a)) (c.vec y))) ∨
      c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        -act (refl c.b (c.vec a))
          (eich c.b e β (act (refl c.b (c.vec a)) (c.vec y))) :=
    eq_or_neg_of_eq_or_neg
      (Or.imp Eq.symm (fun h => by rw [h, neg_neg]) h3) (act_eq_or_neg hinner')
  have h4 : act (refl c.b (c.vec a))
        (eich c.b e β (act (refl c.b (c.vec a)) (c.vec y))) =
      eich c.b e (act (refl c.b (c.vec a)) β) (c.vec y) :=
    act_refl_eich c.hsym hnorm hae β (c.vec y)
  rwa [h4] at h3'

private theorem actsAsEich_conj_refl (c : FiveChart hC n) {a g : G} {e β : Fin n → ZMod 5}
    (hgd : Commute g hC.d) (ha : a ∈ commSet D hC.d) (hae : c.b (c.vec a) e = 0)
    (hgβ : c.ActsAsEich e β g) :
    c.ActsAsEich e (act (refl c.b (c.vec a)) β) (a * g * a⁻¹) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hC.setup.oddT.mul_self_eq_one ha.1)
  have hnorm := c.norm_vec a ha
  intro y hy
  set y' : G := a⁻¹ * y * a with hy'_def
  have hy' : y' ∈ commSet D hC.d := by
    rw [hy'_def, hai]
    have h := conj_mem_commSet_of_commute hC.setup.normal ha.2.1 hy
    rwa [hai] at h
  have hinner : c.vec (g * y' * g⁻¹) = eich c.b e β (c.vec y') ∨
      c.vec (g * y' * g⁻¹) = -eich c.b e β (c.vec y') := hgβ y' hy'
  have hy'vec : c.vec y' = act (refl c.b (c.vec a)) (c.vec y) ∨
      c.vec y' = -act (refl c.b (c.vec a)) (c.vec y) := by
    rw [hy'_def, hai]
    have h := c.vec_conj_eq_act ha hy
    rwa [hai] at h
  have h3 : c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        act (refl c.b (c.vec a)) (c.vec (g * y' * g⁻¹)) ∨
      c.vec (a * (g * y' * g⁻¹) * a⁻¹) =
        -act (refl c.b (c.vec a)) (c.vec (g * y' * g⁻¹)) :=
    c.vec_conj_eq_act ha (conj_mem_commSet_of_commute hC.setup.normal hgd hy')
  have hgroup : (a * g * a⁻¹) * y * (a * g * a⁻¹)⁻¹ = a * (g * y' * g⁻¹) * a⁻¹ := by
    rw [hy'_def]
    group
  rw [hgroup]
  exact vec_conj_eich c hnorm hae hy'vec hinner h3

private theorem pow_five_eq_one_of_actsAsEich (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) {w g : G} (hwd : ¬ Commute w hC.d) {e β : Fin n → ZMod 5}
    (he : c.b e e = 0) (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hgβ : c.ActsAsEich e β g) (hβe : c.b β e = 0) : g ^ 5 = 1 := by
  have hgd : Commute g hC.d := commute_of_mem_closure_L_d hg
  have hg5acts : c.ActsAsEich e 0 (g ^ 5) := actsAsEich_zero_pow_five c hgβ hgd he hβe
  have hg5H : g ^ 5 ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_closure_L hα (Subgroup.pow_mem _ hg 5)
  have hg5cent : (⟨g ^ 5, hg5H⟩ : Halpha D hC.alpha) ∈
      Subgroup.center (Halpha D hC.alpha) :=
    mem_center_Halpha_of_actsAsEich_zero c hα hg5acts (hgd.pow_left 5) hg5H
  rcases hcen ⟨g ^ 5, hg5H⟩ hg5cent with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ Subgroup.pow_mem _ hg 5) (d_not_mem_closure_L hwd)

private theorem d_pow_five (hC : HypothesisC D) : hC.d ^ 5 = hC.d := by
  have h2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have h4 : hC.d ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, h2, one_mul]
  rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_add, pow_one, h4, one_mul]

private theorem inv_mul_conj_ne_d (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) {w a g h : G} (hwd : ¬ Commute w hC.d) {e β β' : Fin n → ZMod 5}
    (he : c.b e e = 0) (hhd : Commute h hC.d)
    (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hgβ : c.ActsAsEich e β g) (hβe : c.b β e = 0)
    (hhL : h ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hhβ : c.ActsAsEich e β' h) (hβ'e : c.b β' e = 0) :
    h⁻¹ * (a * g * a⁻¹) ≠ hC.d := by
  intro hk_d
  have hg5 : g ^ 5 = 1 := pow_five_eq_one_of_actsAsEich hα hcen c hwd he hg hgβ hβe
  have hh5 : h ^ 5 = 1 := pow_five_eq_one_of_actsAsEich hα hcen c hwd he hhL hhβ hβ'e
  have hconj_eq : a * g * a⁻¹ = h * hC.d := by
    calc a * g * a⁻¹ = h * (h⁻¹ * (a * g * a⁻¹)) := by group
      _ = h * hC.d := by rw [hk_d]
  have h1 : (a * g * a⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hg5]
    group
  have h2 : (a * g * a⁻¹) ^ 5 = h ^ 5 * hC.d ^ 5 := by
    rw [hconj_eq]
    exact hhd.mul_pow 5
  have hd1 : hC.d = 1 := by
    have hcontra : h ^ 5 * hC.d ^ 5 = 1 := h2.symm.trans h1
    rwa [hh5, d_pow_five hC, one_mul] at hcontra
  exact hC.setup.oddT.ne_one hC.hd hd1

private theorem inv_mul_conj_eq_one (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) {w a g h : G} (hwd : ¬ Commute w hC.d) {e β β' : Fin n → ZMod 5}
    (he : c.b e e = 0) (ha : a ∈ commSet D hC.d)
    (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hgβ : c.ActsAsEich e β g) (hβe : c.b β e = 0)
    (hhL : h ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hhβ : c.ActsAsEich e β' h) (hβ'e : c.b β' e = 0)
    (hconjβ : c.ActsAsEich e β' (a * g * a⁻¹)) :
    h⁻¹ * (a * g * a⁻¹) = 1 := by
  have hhd : Commute h hC.d := commute_of_mem_closure_L_d hhL
  have hgd : Commute g hC.d := commute_of_mem_closure_L_d hg
  have hagad : Commute (a * g * a⁻¹) hC.d := by
    have h1 := hgd.conj a
    rwa [show a * hC.d * a⁻¹ = hC.d from by
      rw [ha.2.1.eq, mul_assoc, mul_inv_cancel, mul_one]] at h1
  set k : G := h⁻¹ * (a * g * a⁻¹) with hk_def
  have hk0 : c.ActsAsEich e 0 k := by
    rw [hk_def]
    have hinv : c.ActsAsEich e (-β') h⁻¹ := ActsAsEich.inv hhβ hhd he hβ'e
    have hmul := ActsAsEich.mul hinv hconjβ hagad he (by simp [hβ'e]) hβ'e
    simpa using hmul
  have haH : a ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hα ha
  have hgH : g ∈ Halpha D hC.alpha := mem_Halpha_of_mem_closure_L hα hg
  have hhH : h ∈ Halpha D hC.alpha := mem_Halpha_of_mem_closure_L hα hhL
  have hagH : a * g * a⁻¹ ∈ Halpha D hC.alpha :=
    (Halpha D hC.alpha).mul_mem ((Halpha D hC.alpha).mul_mem haH hgH)
      ((Halpha D hC.alpha).inv_mem haH)
  have hkH : k ∈ Halpha D hC.alpha := by
    rw [hk_def]
    exact (Halpha D hC.alpha).mul_mem ((Halpha D hC.alpha).inv_mem hhH) hagH
  have hkd : Commute k hC.d := by
    rw [hk_def]
    exact hhd.inv_left.mul_left hagad
  have hkcent : (⟨k, hkH⟩ : Halpha D hC.alpha) ∈ Subgroup.center (Halpha D hC.alpha) :=
    mem_center_Halpha_of_actsAsEich_zero c hα hk0 hkd hkH
  have hkne : k ≠ hC.d := inv_mul_conj_ne_d hα hcen c hwd he hhd hg hgβ hβe hhL hhβ hβ'e
  rcases hcen ⟨k, hkH⟩ hkcent with h1 | h1
  · simpa [hk_def] using h1
  · exfalso
    exact hkne (by simpa using h1)

theorem conj_mem_of_actsAsEich (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) {w : G} (hwd : ¬ Commute w hC.d) {e : Fin n → ZMod 5}
    (he : c.b e e = 0)
    (hreal : ∀ β, c.b β e = 0 →
      ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g)
    {a : G} (ha : a ∈ commSet D hC.d) (hae : c.b (c.vec a) e = 0) {g : G}
    {β : Fin n → ZMod 5} (hg : g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w))
    (hβe : c.b β e = 0) (hgβ : c.ActsAsEich e β g) :
    a * g * a⁻¹ ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w) ∧
      c.ActsAsEich e (act (refl c.b (c.vec a)) β) (a * g * a⁻¹) := by
  have hgd : Commute g hC.d := commute_of_mem_closure_L_d hg
  set β' : Fin n → ZMod 5 := act (refl c.b (c.vec a)) β with hβ'def
  have hβ'e : c.b β' e = 0 := by
    rw [hβ'def]
    exact act_refl_beta_perp c ha hae hβe
  obtain ⟨h, hhL, hhβ⟩ := hreal β' hβ'e
  have hgβ' : c.ActsAsEich e β' (a * g * a⁻¹) := by
    rw [hβ'def]
    exact actsAsEich_conj_refl c hgd ha hae hgβ
  have hk1 : h⁻¹ * (a * g * a⁻¹) = 1 :=
    inv_mul_conj_eq_one hα hcen c hwd he ha hg hgβ hβe hhL hhβ hβ'e hgβ'
  have hconj : a * g * a⁻¹ = h := by
    have h := congrArg (fun t => h * t) hk1
    simpa using h
  exact ⟨hconj.symm ▸ hhL, hconj ▸ hgβ'⟩

private def eichSubgroup (c : FiveChart hC n) {e : Fin n → ZMod 5} (he : c.b e e = 0) (w : G) :
    Subgroup G where
  carrier := {g | g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w) ∧
    ∃ β : Fin n → ZMod 5, c.b β e = 0 ∧ c.ActsAsEich e β g}
  one_mem' := ⟨Subgroup.one_mem _, 0, by simp, actsAsEich_one c e⟩
  mul_mem' := by
    rintro g h ⟨hgL, β, hβe, hgβ⟩ ⟨hhL, β', hβ'e, hhβ⟩
    refine ⟨Subgroup.mul_mem _ hgL hhL, β + β', ?_, ?_⟩
    · rw [LinearMap.BilinForm.add_left, hβe, hβ'e, add_zero]
    · exact ActsAsEich.mul hgβ hhβ (commute_of_mem_closure_L_d hhL) he hβe hβ'e
  inv_mem' := by
    rintro g ⟨hgL, β, hβe, hgβ⟩
    refine ⟨Subgroup.inv_mem _ hgL, -β, ?_, ?_⟩
    · rw [LinearMap.BilinForm.neg_left, hβe, neg_zero]
    · exact ActsAsEich.inv hgβ (commute_of_mem_closure_L_d hgL) he hβe

private theorem mem_normalizer_of_mul_self_eq_one {U : Subgroup G} {t : G} (ht : t * t = 1)
    (htU : ∀ g ∈ U, t * g * t⁻¹ ∈ U) : t ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact htU u hu
  · intro hu
    have htin : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have htt : t * (t * u * t⁻¹) * t⁻¹ = u := by
      rw [htin]
      calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
        _ = u := by rw [ht]; group
    rw [← htt]
    exact htU (t * u * t⁻¹) hu

private theorem conj_eq_self_of_mem_normalizer {U : Subgroup G} {a k w : G}
    (hN : k ∈ Subgroup.normalizer (U : Set G)) (hka : k * w * k⁻¹ = a)
    (hwU : ∀ u ∈ U, w * u * w⁻¹ = u) : ∀ u ∈ U, a * u * a⁻¹ = u := by
  intro u hu
  have hk_inv : k⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normalizer (U : Set G)).inv_mem hN
  have hu' : k⁻¹ * u * k ∈ U := by
    have h := (Subgroup.mem_normalizer_iff.mp hk_inv u).mp hu
    simpa using h
  have hwcentral : w * (k⁻¹ * u * k) * w⁻¹ = k⁻¹ * u * k := hwU (k⁻¹ * u * k) hu'
  have hident : a * u * a⁻¹ = k * (w * (k⁻¹ * u * k) * w⁻¹) * k⁻¹ := by
    rw [← hka]
    group
  rw [hident, hwcentral]
  group

private theorem exists_b_vec_ne_zero (c : FiveChart hC n) (hn : 5 ≤ n) {a : G}
    {e : Fin n → ZMod 5} (ha : a ∈ commSet D hC.d) (he0 : e ≠ 0)
    (hae : c.b (c.vec a) e = 0) : ∃ y ∈ commSet D hC.d, c.b (c.vec y) e ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply he0
  refine eq_zero_of_forall_norm_one_perp c.hsym c.hnd
    (le_trans (by norm_num : 3 ≤ 5) hn) (c.norm_vec a ha) ?_ ?_
  · rw [c.hsym]; exact hae
  · intro y hy hyv
    obtain ⟨z, hzD, hzv⟩ := c.exists_vec y hy
    have hz_e : c.b (c.vec z) e = 0 := hnone z hzD
    have hy_e : c.b y e = 0 := (c.b_vec_eq_zero_iff hzv).1 hz_e
    rw [c.hsym]
    exact hy_e

private theorem false_of_centralizes_eichSubgroup (c : FiveChart hC n) (hn : 5 ≤ n) {w a : G}
    {e : Fin n → ZMod 5} (he : c.b e e = 0) (he0 : e ≠ 0)
    (hreal : ∀ β, c.b β e = 0 →
      ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g)
    (ha : a ∈ commSet D hC.d) (hae : c.b (c.vec a) e = 0)
    (hacent : ∀ u ∈ eichSubgroup c he w, a * u * a⁻¹ = u) : False := by
  obtain ⟨g₀, hg₀L, hg₀β⟩ := hreal (c.vec a) hae
  have hg₀U : g₀ ∈ eichSubgroup c he w := ⟨hg₀L, c.vec a, hae, hg₀β⟩
  have hg₀neg : c.ActsAsEich e (-c.vec a) g₀ := by
    have h1 : c.ActsAsEich e (act (refl c.b (c.vec a)) (c.vec a)) (a * g₀ * a⁻¹) :=
      actsAsEich_conj_refl c (commute_of_mem_closure_L_d hg₀L) ha hae hg₀β
    rw [hacent g₀ hg₀U] at h1
    have h2 : act (refl c.b (c.vec a)) (c.vec a) = -c.vec a :=
      act_refl_self (c.norm_vec a ha)
    rwa [h2] at h1
  obtain ⟨y, hy, hye⟩ := exists_b_vec_ne_zero c hn ha he0 hae
  have h1 : c.vec (g₀ * y * g₀⁻¹) = eich c.b e (c.vec a) (c.vec y) ∨
      c.vec (g₀ * y * g₀⁻¹) = -eich c.b e (c.vec a) (c.vec y) := hg₀β y hy
  have h2 : c.vec (g₀ * y * g₀⁻¹) = eich c.b e (-c.vec a) (c.vec y) ∨
      c.vec (g₀ * y * g₀⁻¹) = -eich c.b e (-c.vec a) (c.vec y) := hg₀neg y hy
  have hcase := eq_or_neg_of_eq_or_neg h2 h1
  have hne := eich_neg_ne c.hsym he (c.norm_vec a ha) hae hye
  rcases hcase with hc | hc
  · exact hne.1 hc
  · exact hne.2 hc

theorem commute_of_perp_five (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) (hn : 5 ≤ n) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    {e : Fin n → ZMod 5} (he : c.b e e = 0) (he0 : e ≠ 0)
    (hreal : ∀ β, c.b β e = 0 →
      ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g)
    {a : G} (ha : a ∈ commSet D hC.d) (hae : c.b (c.vec a) e = 0) : Commute a w := by
  by_contra h
  have hwa : ¬ Commute w a := fun hc => h hc.symm
  obtain ⟨k, hk_mem, hk_conj⟩ := hC.setup.oddT.exists_conj hw ha.1 hwa
  have hw2 : w * w = 1 := hC.setup.oddT.mul_self_eq_one hw
  have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one ha.1
  have hwU : ∀ u ∈ eichSubgroup c he w, w * u * w⁻¹ = u := by
    intro u hu
    have hc := (commute_of_mem_closure_L_w hu.1).symm
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hwN : w ∈ Subgroup.normalizer (eichSubgroup c he w : Set G) :=
    mem_normalizer_of_mul_self_eq_one hw2 (fun u hu => by rw [hwU u hu]; exact hu)
  have haU : ∀ g ∈ eichSubgroup c he w, a * g * a⁻¹ ∈ eichSubgroup c he w := by
    rintro g ⟨hgL, β, hβe, hgβ⟩
    have hres := conj_mem_of_actsAsEich hα hcen c hwd he hreal ha hae hgL hβe hgβ
    exact ⟨hres.1, act (refl c.b (c.vec a)) β, act_refl_beta_perp c ha hae hβe, hres.2⟩
  have haN : a ∈ Subgroup.normalizer (eichSubgroup c he w : Set G) :=
    mem_normalizer_of_mul_self_eq_one ha2 haU
  have hN : k ∈ Subgroup.normalizer (eichSubgroup c he w : Set G) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (eichSubgroup c he w : Set G))).mpr ?_ hk_mem
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hwN
    · rw [hx]; exact haN
  have hacent : ∀ u ∈ eichSubgroup c he w, a * u * a⁻¹ = u :=
    conj_eq_self_of_mem_normalizer hN hk_conj hwU
  exact false_of_centralizes_eichSubgroup c hn he he0 hreal ha hae hacent

theorem isFiveHyperplane_five (hα : hC.alpha = {hC.d})
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC n) (hn : 5 ≤ n) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (h5 : orderOf (hC.d * w) = 5) (hΓ : (commSet D hC.d ∩ commSet D w).Nonempty) :
    ∃ z, IsFiveHyperplane c w z := by
  obtain ⟨v₀, hv₀⟩ := hΓ
  obtain ⟨e, he0, hev₀, hnorm, hP⟩ := exists_local_hyperplane c hn hw hwd hv₀
  have he : c.b e e = 0 := by
    rw [if_pos h5] at hnorm
    exact hnorm
  have hΓe : ∀ x ∈ commSet D hC.d ∩ commSet D w, c.b (c.vec x) e = 0 :=
    perp_of_mem_five c hn hwd hv₀ he he0 hev₀ hP
  have hPall : ∀ u ∈ commSet D hC.d ∩ commSet D w,
      ∀ x ∈ commSet D hC.d ∩ commSet D u, (Commute x w ↔ c.b (c.vec x) e = 0) :=
    fun u hu => local_eq_of_perp_five c hn hw hwd h5 he0 hΓe hu
  have hreal : ∀ β, c.b β e = 0 →
      ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g :=
    fun β hβe => exists_actsAsEich c hn hwd hv₀ he he0 hev₀ hPall hβe
  refine ⟨e, he0, ?_, ?_⟩
  · rw [if_pos h5]
    exact he
  · intro y hy
    constructor
    · intro hyw
      exact hΓe y ⟨hy, ⟨hy.1, hyw, by intro h; rw [h] at hy; exact hwd hy.2.1⟩⟩
    · intro hye
      exact commute_of_perp_five hα hcen c hn hw hwd he he0 hreal hy hye

end FiveChart

end CFSG.OddTranspositions.PartThree

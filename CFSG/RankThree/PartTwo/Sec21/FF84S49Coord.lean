module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84 IsoAux

variable {G : Type} [Group G] [Finite G]

theorem sg_mem_W {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1) {x : G}
    (hx : x ∈ ⁅S, Subgroup.zpowers c⁆) : c * x * c⁻¹ ∈ ⁅S, Subgroup.zpowers c⁆ := by
  have hrange := commutator_zpowers_eq_range hcm hsq hc hc3
  rw [hrange] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨⟨sg c y, sg_mem hc y.2⟩, ?_⟩
  rw [phiHom_apply, phiHom_apply]
  show (sg c y)⁻¹ * sg c (sg c y) = sg c ((y : G)⁻¹ * sg c y)
  simp only [sg]; group

theorem pim_W {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1) {x : G}
    (hx : x ∈ ⁅S, Subgroup.zpowers c⁆) : pim c x = 1 := by
  rw [commutator_zpowers_eq_range hcm hsq hc hc3] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [phiHom_apply]
  have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
  have e : pim c ((y : G)⁻¹ * sg c y) =
      (y : G)⁻¹ * ((c * c * c) * (y : G) * (c * c * c)⁻¹) := by
    simp only [pim, sg]; group
  rw [e, hc3']; group

theorem W_cen_eq_one {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1) {w : G}
    (hw : w ∈ ⁅S, Subgroup.zpowers c⁆) (h : Commute c w) : w = 1 := by
  have h1 := pim_of_fix hsq (W_le_S hcm hsq hc hc3 hw) (sg_of_commute h)
  rw [← h1]
  exact pim_W hcm hsq hc hc3 hw

theorem W_orbit {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1)
    (hW : Nat.card ↥⁅S, Subgroup.zpowers c⁆ = 4) {p q : G} (hp : p ∈ ⁅S, Subgroup.zpowers c⁆)
    (hq : q ∈ ⁅S, Subgroup.zpowers c⁆) (hp1 : p ≠ 1) (hq1 : q ≠ 1) :
    ∃ n : ℕ, c ^ n * p * (c ^ n)⁻¹ = q := by
  by_contra hne
  push Not at hne
  have hs : c * p * c⁻¹ ∈ ⁅S, Subgroup.zpowers c⁆ := sg_mem_W hcm hsq hc hc3 hp
  have ht : c * (c * p * c⁻¹) * c⁻¹ ∈ ⁅S, Subgroup.zpowers c⁆ := sg_mem_W hcm hsq hc hc3 hs
  set s := c * p * c⁻¹ with hsdef
  set t := c * s * c⁻¹ with htdef
  have hinj : ∀ x y : G, c * x * c⁻¹ = c * y * c⁻¹ → x = y := by
    intro x y h
    simpa using h
  have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
  have hps : p ≠ s := by
    intro h
    exact hp1 (W_cen_eq_one hcm hsq hc hc3 hp
      (commute_of_sg (show c * p * c⁻¹ = p from h.symm)))
  have hst : s ≠ t := fun h => hps (hinj _ _ h)
  have htp : t ≠ p := by
    intro h
    have e : c * t * c⁻¹ = p := by
      rw [htdef, hsdef]
      calc c * (c * (c * p * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * p * (c * c * c)⁻¹ := by group
        _ = p := by rw [hc3']; simp
    apply hps
    calc p = c * t * c⁻¹ := e.symm
      _ = c * p * c⁻¹ := by rw [h]
  have hs1 : s ≠ 1 := by
    intro h
    apply hp1
    apply hinj
    rw [← hsdef, h]; simp
  have ht1 : t ≠ 1 := by
    intro h
    apply hs1
    apply hinj
    rw [← htdef, h]; simp
  have hq0 : q ≠ p := fun h => hne 0 (by simpa using h.symm)
  have hq1' : q ≠ s := fun h => hne 1 (by simpa using h.symm)
  have hq2 : q ≠ t := fun h => hne 2 (by
    rw [h, htdef, hsdef]
    simp only [pow_two]
    group)
  let a1 : ↥⁅S, Subgroup.zpowers c⁆ := 1
  let a2 : ↥⁅S, Subgroup.zpowers c⁆ := ⟨p, hp⟩
  let a3 : ↥⁅S, Subgroup.zpowers c⁆ := ⟨s, hs⟩
  let a4 : ↥⁅S, Subgroup.zpowers c⁆ := ⟨t, ht⟩
  let a5 : ↥⁅S, Subgroup.zpowers c⁆ := ⟨q, hq⟩
  have hnd : [a1, a2, a3, a4, a5].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, a1, a2, a3, a4, a5,
      Subtype.ext_iff]
    simp only [OneMemClass.coe_one]
    exact ⟨⟨hp1.symm, hs1.symm, ht1.symm, hq1.symm⟩, ⟨hps, htp.symm, hq0.symm⟩,
      ⟨hst, hq1'.symm⟩, hq2.symm, not_false, List.nodup_nil⟩
  haveI := Fintype.ofFinite ↥⁅S, Subgroup.zpowers c⁆
  have hlen := hnd.length_le_card
  rw [← Nat.card_eq_fintype_card, hW] at hlen
  simp at hlen

private theorem commute_mul_left_iff {a x y : G} (hy : Commute a y) :
    Commute a (x * y) ↔ Commute a x :=
  ⟨fun h => by simpa using h.mul_right hy.inv_right, fun h => h.mul_right hy⟩

private theorem commute_mul_right_iff {a x y : G} (hx : Commute a x) :
    Commute a (x * y) ↔ Commute a y :=
  ⟨fun h => by simpa using hx.inv_right.mul_right h, fun h => hx.mul_right h⟩

private theorem commute_one_iff {W : Subgroup G} {b : G} (fx : ∀ w ∈ W, Commute b w → w = 1)
    (w : W) : Commute b (w : G) ↔ w = 1 :=
  ⟨fun h => Subtype.ext (fx _ w.2 h), fun h => by rw [h]; simp⟩

private theorem cen_iff {a x : G} : x ∈ Cen a ↔ Commute a x :=
  ⟨commute_of_mem_cen, fun h => Subgroup.mem_centralizer_singleton_iff.2 h.eq.symm⟩

private theorem conj_fix {a w : G} (h : Commute a w) : a * w * a⁻¹ = w := sg_of_commute h

private theorem orbit_step {W : Subgroup G} {b : G}
    (o : ∀ p ∈ W, ∀ q ∈ W, p ≠ 1 → q ≠ 1 → ∃ n : ℕ, b ^ n * p * (b ^ n)⁻¹ = q) {e : Prop}
    {p q : W} (hp : p = 1 ↔ e) (hq : q = 1 ↔ e) :
    ∃ n : ℕ, b ^ n * (p : G) * (b ^ n)⁻¹ = (q : G) := by
  by_cases hp1 : p = 1
  · have hq1 : q = 1 := hq.2 (hp.1 hp1)
    exact ⟨0, by rw [hp1, hq1]; simp⟩
  · have hq1 : q ≠ 1 := fun h => hp1 (hp.2 (hq.1 h))
    exact o p p.2 q q.2 (fun h => hp1 (Subtype.ext h)) (fun h => hq1 (Subtype.ext h))

open _root_.Classical in
private theorem card_pat {H : Type} [Group H] [Finite H] (hH : Nat.card H = 4) (e : Prop) :
    ({w : H | (w = 1 ↔ e)} : Set H).ncard = if e then 1 else 3 := by
  classical
  by_cases he : e
  · have : {w : H | (w = 1 ↔ e)} = {1} := by ext w; simp [he]
    rw [this, if_pos he, Set.ncard_singleton]
  · have : {w : H | (w = 1 ↔ e)} = ({1} : Set H)ᶜ := by ext w; simp [he]
    rw [this, if_neg he, Set.ncard_compl, Set.ncard_singleton, hH]

@[expose] def PatSet (S : Subgroup G) (b₀ b₁ b₂ : G) (e₀ e₁ e₂ : Prop) : Set G :=
  {x | x ∈ S ∧ (x ∈ Cen b₀ ↔ e₀) ∧ (x ∈ Cen b₁ ↔ e₁) ∧ (x ∈ Cen b₂ ↔ e₂)}

open _root_.Classical in
theorem coord_orbits_aux {S W₀ W₁ W₂ : Subgroup G} {b₀ b₁ b₂ : G}
    (hS : Nat.card S = 64) (c₀ : Nat.card W₀ = 4) (c₁ : Nat.card W₁ = 4)
    (c₂ : Nat.card W₂ = 4) (s₀ : W₀ ≤ S) (s₁ : W₁ ≤ S) (s₂ : W₂ ≤ S)
    (c01 : ∀ w ∈ W₁, Commute b₀ w) (c02 : ∀ w ∈ W₂, Commute b₀ w)
    (c10 : ∀ w ∈ W₀, Commute b₁ w) (c12 : ∀ w ∈ W₂, Commute b₁ w)
    (c20 : ∀ w ∈ W₀, Commute b₂ w) (c21 : ∀ w ∈ W₁, Commute b₂ w)
    (f₀ : ∀ w ∈ W₀, Commute b₀ w → w = 1) (f₁ : ∀ w ∈ W₁, Commute b₁ w → w = 1)
    (f₂ : ∀ w ∈ W₂, Commute b₂ w → w = 1)
    (o₀ : ∀ p ∈ W₀, ∀ q ∈ W₀, p ≠ 1 → q ≠ 1 → ∃ n : ℕ, b₀ ^ n * p * (b₀ ^ n)⁻¹ = q)
    (o₁ : ∀ p ∈ W₁, ∀ q ∈ W₁, p ≠ 1 → q ≠ 1 → ∃ n : ℕ, b₁ ^ n * p * (b₁ ^ n)⁻¹ = q)
    (o₂ : ∀ p ∈ W₂, ∀ q ∈ W₂, p ≠ 1 → q ≠ 1 → ∃ n : ℕ, b₂ ^ n * p * (b₂ ^ n)⁻¹ = q)
    (e₀ e₁ e₂ : Prop) :
    (PatSet S b₀ b₁ b₂ e₀ e₁ e₂).ncard =
        (if e₀ then 1 else 3) * (if e₁ then 1 else 3) * (if e₂ then 1 else 3) ∧
      ∀ x ∈ PatSet S b₀ b₁ b₂ e₀ e₁ e₂, ∀ y ∈ PatSet S b₀ b₁ b₂ e₀ e₁ e₂,
        ∃ β ∈ Subgroup.closure ({b₀, b₁, b₂} : Set G), β * x * β⁻¹ = y := by
  obtain ⟨f, hf⟩ : ∃ f : W₀ × W₁ × W₂ → G, ∀ p, f p = (p.1 : G) * p.2.1 * p.2.2 :=
    ⟨_, fun _ => rfl⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨p0, p1, p2⟩ ⟨q0, q1, q2⟩ h
    rw [hf, hf] at h
    simp only at h
    have e0 : (p0 : G) = q0 := by
      have h' : (p0 : G) * ((p1 : G) * (p2 : G)) = q0 * ((q1 : G) * (q2 : G)) := by simpa [mul_assoc] using h
      have h1 : (q0 : G)⁻¹ * p0 = ((q1 : G) * (q2 : G)) * ((p1 : G) * (p2 : G))⁻¹ := by
        calc (q0 : G)⁻¹ * p0 = (q0 : G)⁻¹ * (p0 * ((p1 : G) * (p2 : G))) * ((p1 : G) * (p2 : G))⁻¹ := by group
          _ = ((q1 : G) * (q2 : G)) * ((p1 : G) * (p2 : G))⁻¹ := by rw [h']; group
      have hc : Commute b₀ ((q0 : G)⁻¹ * p0) := by
        rw [h1]
        exact ((c01 _ q1.2).mul_right (c02 _ q2.2)).mul_right
          ((c01 _ p1.2).mul_right (c02 _ p2.2)).inv_right
      have := f₀ _ (mul_mem (inv_mem q0.2) p0.2) hc
      exact (inv_mul_eq_one.1 this).symm
    rw [e0] at h
    have h' : (q0 : G) * ((p1 : G) * (p2 : G)) = q0 * ((q1 : G) * (q2 : G)) := by simpa [mul_assoc] using h
    have h2 : (p1 : G) * p2 = q1 * q2 := mul_left_cancel h'
    have e1 : (p1 : G) = q1 := by
      have h1 : (q1 : G)⁻¹ * p1 = q2 * (p2 : G)⁻¹ := by
        calc (q1 : G)⁻¹ * p1 = (q1 : G)⁻¹ * ((p1 : G) * (p2 : G)) * (p2 : G)⁻¹ := by group
          _ = q2 * (p2 : G)⁻¹ := by rw [h2]; group
      have hc : Commute b₁ ((q1 : G)⁻¹ * p1) := by
        rw [h1]
        exact (c12 _ q2.2).mul_right (c12 _ p2.2).inv_right
      have := f₁ _ (mul_mem (inv_mem q1.2) p1.2) hc
      exact (inv_mul_eq_one.1 this).symm
    rw [e1] at h2
    have e2 : (p2 : G) = q2 := mul_left_cancel h2
    exact Prod.ext (Subtype.ext e0) (Prod.ext (Subtype.ext e1) (Subtype.ext e2))
  have hfS : ∀ p, f p ∈ S := fun p => by
    rw [hf]
    exact mul_mem (mul_mem (s₀ p.1.2) (s₁ p.2.1.2)) (s₂ p.2.2.2)
  have hsurj : ∀ x ∈ S, ∃ p, f p = x := by
    let g : W₀ × W₁ × W₂ → S := fun p => ⟨f p, hfS p⟩
    have hg_inj : Function.Injective g := fun p q h => hf_inj (congrArg Subtype.val h)
    have hg_bij : Function.Bijective g := by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨hg_inj, ?_⟩
      simp [Nat.card_prod, c₀, c₁, c₂, hS]
    intro x hx
    obtain ⟨p, hp⟩ := hg_bij.2 ⟨x, hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  have hcen0 : ∀ p, f p ∈ Cen b₀ ↔ p.1 = 1 := by
    intro p
    rw [← commute_one_iff f₀, cen_iff, hf, mul_assoc,
      commute_mul_left_iff ((c01 _ p.2.1.2).mul_right (c02 _ p.2.2.2))]
  have hcen1 : ∀ p, f p ∈ Cen b₁ ↔ p.2.1 = 1 := by
    intro p
    rw [← commute_one_iff f₁, cen_iff, hf, commute_mul_left_iff (c12 _ p.2.2.2),
      commute_mul_right_iff (c10 _ p.1.2)]
  have hcen2 : ∀ p, f p ∈ Cen b₂ ↔ p.2.2 = 1 := by
    intro p
    rw [← commute_one_iff f₂, cen_iff, hf,
      commute_mul_right_iff ((c20 _ p.1.2).mul_right (c21 _ p.2.1.2))]
  have hPat : PatSet S b₀ b₁ b₂ e₀ e₁ e₂ = f '' (({w : W₀ | (w = 1 ↔ e₀)} : Set W₀) ×ˢ
      (({w : W₁ | (w = 1 ↔ e₁)} : Set W₁) ×ˢ ({w : W₂ | (w = 1 ↔ e₂)} : Set W₂))) := by
    ext x
    constructor
    · rintro ⟨hxS, hx0, hx1, hx2⟩
      obtain ⟨p, rfl⟩ := hsurj x hxS
      exact ⟨p, ⟨(hcen0 p).symm.trans hx0, (hcen1 p).symm.trans hx1,
        (hcen2 p).symm.trans hx2⟩, rfl⟩
    · rintro ⟨p, ⟨h0, h1, h2⟩, rfl⟩
      exact ⟨hfS p, (hcen0 p).trans h0, (hcen1 p).trans h1, (hcen2 p).trans h2⟩
  refine ⟨?_, ?_⟩
  · rw [hPat, Set.ncard_image_of_injective _ hf_inj, Set.ncard_prod, Set.ncard_prod,
      card_pat c₀, card_pat c₁, card_pat c₂, mul_assoc]
  · intro x hx y hy
    rw [hPat] at hx hy
    obtain ⟨p, ⟨hp0, hp1, hp2⟩, rfl⟩ := hx
    obtain ⟨q, ⟨hq0, hq1, hq2⟩, rfl⟩ := hy
    obtain ⟨n0, hn0⟩ := orbit_step o₀ hp0 hq0
    obtain ⟨n1, hn1⟩ := orbit_step o₁ hp1 hq1
    obtain ⟨n2, hn2⟩ := orbit_step o₂ hp2 hq2
    refine ⟨b₀ ^ n0 * b₁ ^ n1 * b₂ ^ n2, ?_, ?_⟩
    · exact mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) n0)
        (pow_mem (Subgroup.subset_closure (by simp)) n1))
        (pow_mem (Subgroup.subset_closure (by simp)) n2)
    · rw [hf, hf]
      set β := b₀ ^ n0 * b₁ ^ n1 * b₂ ^ n2 with hβ
      have e0 : β * (p.1 : G) * β⁻¹ = q.1 := by
        calc β * (p.1 : G) * β⁻¹
            = b₀ ^ n0 * (b₁ ^ n1 * (b₂ ^ n2 * (p.1 : G) * (b₂ ^ n2)⁻¹) * (b₁ ^ n1)⁻¹) *
              (b₀ ^ n0)⁻¹ := by rw [hβ]; group
          _ = q.1 := by
            rw [conj_fix ((c20 _ p.1.2).pow_left n2), conj_fix ((c10 _ p.1.2).pow_left n1), hn0]
      have e1 : β * (p.2.1 : G) * β⁻¹ = q.2.1 := by
        calc β * (p.2.1 : G) * β⁻¹
            = b₀ ^ n0 * (b₁ ^ n1 * (b₂ ^ n2 * (p.2.1 : G) * (b₂ ^ n2)⁻¹) * (b₁ ^ n1)⁻¹) *
              (b₀ ^ n0)⁻¹ := by rw [hβ]; group
          _ = q.2.1 := by
            rw [conj_fix ((c21 _ p.2.1.2).pow_left n2), hn1,
              conj_fix ((c01 _ q.2.1.2).pow_left n0)]
      have e2 : β * (p.2.2 : G) * β⁻¹ = q.2.2 := by
        calc β * (p.2.2 : G) * β⁻¹
            = b₀ ^ n0 * (b₁ ^ n1 * (b₂ ^ n2 * (p.2.2 : G) * (b₂ ^ n2)⁻¹) * (b₁ ^ n1)⁻¹) *
              (b₀ ^ n0)⁻¹ := by rw [hβ]; group
          _ = q.2.2 := by
            rw [hn2, conj_fix ((c12 _ q.2.2.2).pow_left n1),
              conj_fix ((c02 _ q.2.2.2).pow_left n0)]
      calc β * ((p.1 : G) * p.2.1 * p.2.2) * β⁻¹
          = (β * (p.1 : G) * β⁻¹) * (β * (p.2.1 : G) * β⁻¹) * (β * (p.2.2 : G) * β⁻¹) := by
            group
        _ = (q.1 : G) * q.2.1 * q.2.2 := by rw [e0, e1, e2]

structure CoordHyp (S : Subgroup G) (b₀ b₁ b₂ : G) : Prop where
  ea : EA2 S
  card : Nat.card S = 64
  nor₀ : b₀ ∈ Nor S
  nor₁ : b₁ ∈ Nor S
  nor₂ : b₂ ∈ Nor S
  ord₀ : orderOf b₀ = 3
  ord₁ : orderOf b₁ = 3
  ord₂ : orderOf b₂ = 3
  c₀₁ : b₀ * b₁ = b₁ * b₀
  c₀₂ : b₀ * b₂ = b₂ * b₀
  c₁₂ : b₁ * b₂ = b₂ * b₁
  f₀ : Nat.card ↥(S ⊓ Cen b₀) = 16
  f₁ : Nat.card ↥(S ⊓ Cen b₁) = 16
  f₂ : Nat.card ↥(S ⊓ Cen b₂) = 16
  fix : S ⊓ CenS (Subgroup.closure ({b₀, b₁, b₂} : Set G)) = ⊥
  k₀ : Nat.card ↥⁅S, Subgroup.zpowers b₀⁆ = 4
  k₁ : Nat.card ↥⁅S, Subgroup.zpowers b₁⁆ = 4
  k₂ : Nat.card ↥⁅S, Subgroup.zpowers b₂⁆ = 4
  join : ⁅S, Subgroup.zpowers b₀⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ = S
  z₀ : ⁅S, Subgroup.zpowers b₀⁆ ≤ CenS (Subgroup.closure ({b₁, b₂} : Set G))
  z₁ : ⁅S, Subgroup.zpowers b₁⁆ ≤ CenS (Subgroup.closure ({b₀, b₂} : Set G))
  z₂ : ⁅S, Subgroup.zpowers b₂⁆ ≤ CenS (Subgroup.closure ({b₀, b₁} : Set G))

private theorem commute_of_z {W : Subgroup G} {x y : G}
    (hz : W ≤ CenS (Subgroup.closure ({x, y} : Set G))) {w : G} (hw : w ∈ W) :
    Commute x w ∧ Commute y w := by
  have h := Subgroup.mem_centralizer_iff.1 (hz hw)
  exact ⟨h x (Subgroup.subset_closure (by simp)), h y (Subgroup.subset_closure (by simp))⟩

open _root_.Classical in
theorem coord_orbits {S : Subgroup G} {b₀ b₁ b₂ : G} (h : CoordHyp S b₀ b₁ b₂)
    (e₀ e₁ e₂ : Prop) :
    (PatSet S b₀ b₁ b₂ e₀ e₁ e₂).ncard =
        (if e₀ then 1 else 3) * (if e₁ then 1 else 3) * (if e₂ then 1 else 3) ∧
      ∀ x ∈ PatSet S b₀ b₁ b₂ e₀ e₁ e₂, ∀ y ∈ PatSet S b₀ b₁ b₂ e₀ e₁ e₂,
        ∃ β ∈ Subgroup.closure ({b₀, b₁, b₂} : Set G), β * x * β⁻¹ = y := by
  have hcm := h.ea.1
  have hsq := h.ea.2
  have hb₀ : b₀ ^ 3 = 1 := by rw [← h.ord₀]; exact pow_orderOf_eq_one b₀
  have hb₁ : b₁ ^ 3 = 1 := by rw [← h.ord₁]; exact pow_orderOf_eq_one b₁
  have hb₂ : b₂ ^ 3 = 1 := by rw [← h.ord₂]; exact pow_orderOf_eq_one b₂
  exact coord_orbits_aux h.card h.k₀ h.k₁ h.k₂
    (W_le_S hcm hsq h.nor₀ hb₀) (W_le_S hcm hsq h.nor₁ hb₁) (W_le_S hcm hsq h.nor₂ hb₂)
    (fun w hw => (commute_of_z h.z₁ hw).1) (fun w hw => (commute_of_z h.z₂ hw).1)
    (fun w hw => (commute_of_z h.z₀ hw).1) (fun w hw => (commute_of_z h.z₂ hw).2)
    (fun w hw => (commute_of_z h.z₀ hw).2) (fun w hw => (commute_of_z h.z₁ hw).2)
    (fun w hw hc => W_cen_eq_one hcm hsq h.nor₀ hb₀ hw hc)
    (fun w hw hc => W_cen_eq_one hcm hsq h.nor₁ hb₁ hw hc)
    (fun w hw hc => W_cen_eq_one hcm hsq h.nor₂ hb₂ hw hc)
    (fun p hp q hq hp1 hq1 => W_orbit hcm hsq h.nor₀ hb₀ h.k₀ hp hq hp1 hq1)
    (fun p hp q hq hp1 hq1 => W_orbit hcm hsq h.nor₁ hb₁ h.k₁ hp hq hp1 hq1)
    (fun p hp q hq hp1 hq1 => W_orbit hcm hsq h.nor₂ hb₂ h.k₂ hp hq hp1 hq1) e₀ e₁ e₂

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

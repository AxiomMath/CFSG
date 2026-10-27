module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.Asc81cPfField

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] {G X Y : Subgroup (MulAut W)}

section Normal

theorem two_mul_add_one_lt_two_pow {b : ℕ} (hb : 3 ≤ b) : 2 * b + 1 < 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

theorem inv_apply_eq_of_apply_eq {x : MulAut W} {v : W} (h : x v = v) : x⁻¹ v = v := by
  calc x⁻¹ v = x⁻¹ (x v) := by rw [h]
    _ = v := by rw [MulAut.inv_apply_self]

theorem map_eq_of_fixes {x : MulAut W} {S : Subgroup W} (hx : ∀ v ∈ S, x v = v) :
    S.map x.toMonoidHom = S := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    show x u ∈ S
    rw [hx u hu]
    exact hu
  · intro hv
    exact ⟨v, hv, hx v hv⟩

theorem mem_normalizer_of_fixes (hY : Hyp101 G Y) {x : MulAut W} (hx : x ∈ G)
    (hfix : ∀ v ∈ fixV Y, x v = v) : x ∈ Subgroup.normalizer (Y : Set (MulAut W)) := by
  have hfix' : ∀ v ∈ fixV Y, x⁻¹ v = v := fun v hv => inv_apply_eq_of_apply_eq (hfix v hv)
  refine Subgroup.mem_normalizer_iff.2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · exact hY.2.2.2.2.2 x hx (map_eq_of_fixes hfix) z hz
  · have h1 := hY.2.2.2.2.2 x⁻¹ (G.inv_mem hx) (map_eq_of_fixes hfix') _ hz
    have h2 : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
    rwa [h2] at h1

theorem mem_normalizer_of_mapsTo [Finite W] (hY : Hyp101 G Y) {x : MulAut W} (hx : x ∈ G)
    (hmap : ∀ v ∈ fixV Y, x v ∈ fixV Y) : x ∈ Subgroup.normalizer (Y : Set (MulAut W)) := by
  have hmap' : (fixV Y).map x.toMonoidHom = fixV Y := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective x.injective).ge
    rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  have hle : Y.map (MulAut.conj x).toMonoidHom ≤ Y := by
    rintro _ ⟨z, hz, rfl⟩
    exact hY.2.2.2.2.2 x hx hmap' z hz
  have heq : Y.map (MulAut.conj x).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem fixV_stable_of_normalizer {y : MulAut W}
    (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) {c : W} (hc : c ∈ fixV X) :
    y c ∈ fixV X :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hy hc

end Normal

variable [Finite W]

theorem comm_of_fixes_commSub (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hfix : ∀ y ∈ Y, ∀ u ∈ commSub (⊤ : Subgroup W) X, y u = u) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  ext v
  have hv : v ∈ fixV X ⊔ commSub ⊤ X := by
    rw [fixV_sup_commSub_eq_top' hW hX.2.2.2.1]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.1 hv
  have hyc : y c ∈ fixV X := fixV_stable_of_normalizer (hYN hy) hc
  have hxu : x u ∈ commSub (⊤ : Subgroup W) X := commSub_stable' hx hu
  simp only [MulAut.mul_apply, map_mul]
  rw [hyc x hx, hc x hx, hfix y hy u hu, hfix y hy _ hxu]

theorem ten_six (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hnc : ∃ x ∈ X, ∃ y ∈ Y, x * y ≠ y * x) : Nat.card X = 7 ∧ Nat.card Y = 3 := by
  have hYU : ∀ y ∈ Y, ∀ u ∈ commSub (⊤ : Subgroup W) X, y u ∈ commSub (⊤ : Subgroup W) X :=
    fun y hy => normalizer_stable (hYN hy)
  obtain ⟨u, hu, y, hy, hyu⟩ : ∃ u ∈ commSub (⊤ : Subgroup W) X, ∃ y ∈ Y, y u ≠ u := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (comm_of_fixes_commSub hW hX hYN (fun y hy u hu => hall u hu y hy) x hx y hy)
  have hc0 : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
    (commSub ⊤ X).mul_mem (hYU y hy u hu) ((commSub ⊤ X).inv_mem hu)
  have hc0' : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
    Subgroup.subset_closure ⟨y, hy, u, Subgroup.mem_top u, rfl⟩
  have hc01 : y u * u⁻¹ ≠ 1 := fun h0 => hyu (mul_inv_eq_one.1 h0)
  have hU'U : commSub (⊤ : Subgroup W) Y ≤ commSub ⊤ X :=
    commSub_le_of_invariant' hY hYU hc0 hc0' hc01
  have hXodd := hX.2.2.2.1
  have hYodd := hY.2.2.2.1
  by_cases hUU : commSub (⊤ : Subgroup W) Y = commSub ⊤ X
  ·
    exfalso
    have hfixle : fixV X ≤ fixV Y := by
      intro c hc y' hy'
      have h1 : y' c * c⁻¹ ∈ fixV X ⊓ commSub ⊤ X := by
        refine ⟨(fixV X).mul_mem (fixV_stable_of_normalizer (hYN hy') hc)
          ((fixV X).inv_mem hc), ?_⟩
        rw [← hUU]
        exact Subgroup.subset_closure ⟨y', hy', c, Subgroup.mem_top c, rfl⟩
      rw [fixV_inf_commSub_eq_bot' hW hXodd] at h1
      exact mul_inv_eq_one.1 h1
    have hfixeq : fixV X = fixV Y := by
      refine Subgroup.eq_of_le_of_card_ge hfixle ?_
      have h1 := card_fixV_mul_card_commSub hW hXodd
      have h2 := card_fixV_mul_card_commSub hW hYodd
      rw [hUU] at h2
      have hpos : 0 < Nat.card (commSub (⊤ : Subgroup W) X) := Nat.card_pos
      have := Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
      omega
    have hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer (Y : Set (MulAut W)) := fun x hx =>
      mem_normalizer_of_fixes hY (hX.1 hx) fun v hv => (hfixeq ▸ hv : v ∈ fixV X) x hx
    obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hnc
    have hyN := hYN hy₀
    have hyX : ∃ x ∈ X, y₀ * x ≠ x * y₀ := ⟨x₀, hx₀, fun h => hxy₀ h.symm⟩
    have hsq := sq_card_centralizer_le hW hX hyN hyX
    have hcX : ∀ x : X, y₀ * (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ ∈ X := fun x =>
      X.mul_mem (conj_mem hyN x) (X.inv_mem x.2)
    let φ : X →* X :=
      { toFun := fun x => ⟨_, hcX x⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          show y₀ * ((a : MulAut W) * b) * y₀⁻¹ * ((a : MulAut W) * b)⁻¹ =
            y₀ * a * y₀⁻¹ * (a : MulAut W)⁻¹ * (y₀ * b * y₀⁻¹ * (b : MulAut W)⁻¹)
          have e1 : (a : MulAut W)⁻¹ * (y₀ * b * y₀⁻¹ * (b : MulAut W)⁻¹) =
              (y₀ * b * y₀⁻¹ * (b : MulAut W)⁻¹) * (a : MulAut W)⁻¹ :=
            mul_comm_of_isCyclic hX.2.2.1 (X.inv_mem a.2) (hcX b)
          calc y₀ * ((a : MulAut W) * b) * y₀⁻¹ * ((a : MulAut W) * b)⁻¹
              = y₀ * a * y₀⁻¹ * ((y₀ * b * y₀⁻¹ * (b : MulAut W)⁻¹) * (a : MulAut W)⁻¹) := by
                group
            _ = _ := by rw [← e1]; group) }
    have hker : ∀ x : X, x ∈ φ.ker ↔ (x : MulAut W) ∈ X ⊓ Subgroup.centralizer {y₀} := by
      intro x
      rw [MonoidHom.mem_ker]
      constructor
      · intro h1
        have h2 : y₀ * (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ = 1 := congrArg Subtype.val h1
        refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
        rw [Set.mem_singleton_iff.1 hg]
        have h3 := mul_inv_eq_one.1 h2
        calc y₀ * (x : MulAut W) = y₀ * x * y₀⁻¹ * y₀ := by group
          _ = x * y₀ := by rw [h3]
      · rintro ⟨-, hc⟩
        have h3 : y₀ * (x : MulAut W) = x * y₀ :=
          Subgroup.mem_centralizer_iff.1 hc y₀ (Set.mem_singleton y₀)
        apply Subtype.ext
        show y₀ * (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ = 1
        rw [h3]
        group
    have hrange : φ.range ≤ φ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [hker]
      refine ⟨hcX x, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      rw [Set.mem_singleton_iff.1 hg]
      have hmemY : y₀ * (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ ∈ Y := by
        have h1 : (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.1 (hXN x x.2) y₀⁻¹).1 (Y.inv_mem hy₀)
        have h2 := Y.mul_mem hy₀ h1
        have h3 : y₀ * ((x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹) =
            y₀ * (x : MulAut W) * y₀⁻¹ * (x : MulAut W)⁻¹ := by group
        rwa [h3] at h2
      exact mul_comm_of_isCyclic hY.2.2.1 hy₀ hmemY
    have hcardker : Nat.card φ.ker = Nat.card ↥(X ⊓ Subgroup.centralizer {y₀}) := by
      refine Nat.card_congr
        { toFun := fun k => ⟨k.1, (hker k.1).1 k.2⟩
          invFun := fun k => ⟨⟨k.1, k.2.1⟩, (hker ⟨k.1, k.2.1⟩).2 k.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 := Subgroup.card_le_of_le hrange
    have h3 := card_commSub hX
    have hpos : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer {y₀}) := Nat.card_pos
    rw [hcardker] at h1 h2
    have h4 : Nat.card X ≤ Nat.card ↥(X ⊓ Subgroup.centralizer {y₀}) ^ 2 := by
      rw [← h1, pow_two]
      exact Nat.mul_le_mul_left _ h2
    rw [h3] at hsq
    nlinarith
  ·
    have hYC : ∀ y ∈ Y, (∀ x ∈ X, y * x = x * y) → y = 1 := by
      intro y' hy' hc
      obtain ⟨x₀, hx₀, hx₀v⟩ := exists_eq_on_commSub hX (c := y') hc
      by_cases hx₀1 : x₀ = 1
      ·
        ext v
        have hv : v ∈ fixV X ⊔ commSub ⊤ X := by
          rw [fixV_sup_commSub_eq_top' hW hXodd]
          exact Subgroup.mem_top v
        obtain ⟨c, hc', w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
        have hyw : y' w = w := by rw [hx₀v w hw, hx₀1, MulAut.one_apply]
        have hyc : y' c = c := by
          have h1 : y' c * c⁻¹ ∈ fixV X ⊓ commSub ⊤ X := by
            refine ⟨(fixV X).mul_mem (fixV_stable_of_normalizer (hYN hy') hc')
              ((fixV X).inv_mem hc'), hU'U ?_⟩
            exact Subgroup.subset_closure ⟨y', hy', c, Subgroup.mem_top c, rfl⟩
          rw [fixV_inf_commSub_eq_bot' hW hXodd] at h1
          exact mul_inv_eq_one.1 h1
        rw [map_mul, hyc, hyw, MulAut.one_apply]
      ·
        exfalso
        apply hUU
        refine le_antisymm hU'U fun w hw => ?_
        let f : commSub (⊤ : Subgroup W) X → commSub (⊤ : Subgroup W) X := fun a =>
          ⟨y' a * (a : W)⁻¹, (commSub ⊤ X).mul_mem (hYU y' hy' a a.2) ((commSub ⊤ X).inv_mem a.2)⟩
        have hf : Function.Injective f := by
          intro a b hab
          have h1 : y' a * (a : W)⁻¹ = y' b * (b : W)⁻¹ := congrArg Subtype.val hab
          have h2 : y' ((a : W) * (b : W)⁻¹) = (a : W) * (b : W)⁻¹ := by
            have h3 : y' (a : W) = y' (b : W) * (b : W)⁻¹ * a := mul_inv_eq_iff_eq_mul.1 h1
            rw [map_mul, map_inv, h3, mul_inv_eq_iff_eq_mul]
            ac_rfl
          have hab' : (a : W) * (b : W)⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
            (commSub ⊤ X).mul_mem a.2 ((commSub ⊤ X).inv_mem b.2)
          by_contra hne
          have hne' : (a : W) * (b : W)⁻¹ ≠ 1 := fun h0 => hne (Subtype.ext (mul_inv_eq_one.1 h0))
          rw [hx₀v _ hab'] at h2
          exact hx₀1 (eq_one_of_apply_eq hX hx₀ hab' hne' h2)
        obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨w, hw⟩
        have h1 : y' a * (a : W)⁻¹ = w := congrArg Subtype.val ha
        rw [← h1]
        exact Subgroup.subset_closure ⟨y', hy', a, Subgroup.mem_top _, rfl⟩
    have hdvd := card_dvd_rk hW hX hYN hYC
    obtain ⟨hdec1, hdec2⟩ := B1.coprime_decomp hW hYodd (M := commSub ⊤ X) hYU
    have hceq : commSub (commSub ⊤ X) Y = commSub (⊤ : Subgroup W) Y := by
      refine le_antisymm (commSub_mono le_top le_rfl) ?_
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨y', hy', v, -, rfl⟩
      have hv : v ∈ fixV X ⊔ commSub ⊤ X := by
        rw [fixV_sup_commSub_eq_top' hW hXodd]
        exact Subgroup.mem_top v
      obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
      have hyc : y' c = c := by
        have h1 : y' c * c⁻¹ ∈ fixV X ⊓ commSub ⊤ X := by
          refine ⟨(fixV X).mul_mem (fixV_stable_of_normalizer (hYN hy') hc)
            ((fixV X).inv_mem hc), hU'U ?_⟩
          exact Subgroup.subset_closure ⟨y', hy', c, Subgroup.mem_top c, rfl⟩
        rw [fixV_inf_commSub_eq_bot' hW hXodd] at h1
        exact mul_inv_eq_one.1 h1
      have h1 : y' (c * w) * (c * w)⁻¹ = y' w * w⁻¹ := by
        rw [map_mul, hyc, mul_inv_rev, mul_comm c (y' w), mul_assoc, ← mul_assoc c,
          mul_comm c w⁻¹, mul_assoc, mul_inv_cancel, mul_one]
      rw [SetLike.mem_coe, h1]
      exact Subgroup.subset_closure ⟨y', hy', w, hw, rfl⟩
    set D := commSub (⊤ : Subgroup W) X ⊓ fixV Y with hDdef
    have hcardU : Nat.card (commSub (⊤ : Subgroup W) X) =
        Nat.card D * Nat.card (commSub (⊤ : Subgroup W) Y) := by
      have h := card_sup_mul_card_inf D (commSub (commSub ⊤ X) Y)
      rw [hdec1, hdec2, Subgroup.card_bot, mul_one, hceq] at h
      exact h
    have hD1 : D ≠ ⊥ := by
      intro hD
      apply hUU
      refine Subgroup.eq_of_le_of_card_ge hU'U ?_
      rw [hcardU, hD, Subgroup.card_bot, one_mul]
    obtain ⟨w₀, hw₀D, hw₀1⟩ : ∃ w ∈ D, w ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hD1 ((Subgroup.eq_bot_iff_forall D).2 hall)
    obtain ⟨w₁, hw₁, hw₁1⟩ := exists_ne_one hY
    let C := X ⊓ Subgroup.centralizer (Y : Set (MulAut W))
    have hCD : Nat.card C + 1 = Nat.card D := by
      have hmem : ∀ x : C, (x : MulAut W) w₀ ∈ ((D : Set W) \ {1}) := by
        intro x
        refine ⟨⟨commSub_stable' x.2.1 hw₀D.1, fun y' hy' => ?_⟩, fun h0 => hw₀1 ?_⟩
        · have hxy : y' * (x : MulAut W) = x * y' :=
            Subgroup.mem_centralizer_iff.1 x.2.2 y' hy'
          rw [← MulAut.mul_apply, hxy, MulAut.mul_apply, hw₀D.2 y' hy']
        · have h1 : (x : MulAut W) w₀ = (x : MulAut W) 1 := by
            rw [map_one]
            exact h0
          exact (x : MulAut W).injective h1
      let e : C → ↥((D : Set W) \ {1}) := fun x => ⟨_, hmem x⟩
      have he : Function.Bijective e := by
        constructor
        · intro a b hab
          have h1 : (a : MulAut W) w₀ = (b : MulAut W) w₀ := congrArg Subtype.val hab
          have h2 : ((b : MulAut W)⁻¹ * a) w₀ = w₀ := by
            rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
          have h3 := eq_one_of_apply_eq hX (X.mul_mem (X.inv_mem b.2.1) a.2.1) hw₀D.1 hw₀1 h2
          apply Subtype.ext
          have := congrArg (fun z => (b : MulAut W) * z) h3
          simpa using this
        · rintro ⟨w, ⟨hwU, hwY⟩, hw1⟩
          obtain ⟨x, hx, hxw⟩ := exists_apply_eq hX hw₀D.1 hw₀1 hwU hw1
          have hxC : x ∈ Subgroup.centralizer (Y : Set (MulAut W)) := by
            refine Subgroup.mem_centralizer_iff.2 fun y' hy' => ?_
            have hyN := hYN hy'
            have h1 : (y' * x * y'⁻¹) w₀ = x w₀ := by
              rw [MulAut.mul_apply, MulAut.mul_apply,
                inv_apply_eq_of_apply_eq (hw₀D.2 y' hy'),
                hxw, hwY y' hy']
            have h2 : (x⁻¹ * (y' * x * y'⁻¹)) w₀ = w₀ := by
              rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
            have hmem' : x⁻¹ * (y' * x * y'⁻¹) ∈ X :=
              X.mul_mem (X.inv_mem hx) (conj_mem hyN ⟨x, hx⟩)
            have h3 := eq_one_of_apply_eq hX hmem' hw₀D.1 hw₀1 h2
            have h4 : y' * x * y'⁻¹ = x := by
              have := congrArg (fun z => x * z) h3
              simpa using this
            calc y' * x = y' * x * y'⁻¹ * y' := by group
              _ = x * y' := by rw [h4]
          exact ⟨⟨x, hx, hxC⟩, Subtype.ext hxw⟩
      have h1 := Nat.card_congr (Equiv.ofBijective e he)
      rw [card_diff_one] at h1
      have h2 : 0 < Nat.card D := Nat.card_pos
      omega
    have hCY : Nat.card C + 1 ≤ Nat.card (commSub (⊤ : Subgroup W) Y) := by
      have hmem : ∀ x : C, (x : MulAut W) w₁ ∈ ((commSub (⊤ : Subgroup W) Y : Set W) \ {1}) := by
        intro x
        refine ⟨commSub_stable_of_commute (fun y' hy' =>
          (Subgroup.mem_centralizer_iff.1 x.2.2 y' hy').symm) hw₁, fun h0 => hw₁1 ?_⟩
        have h1 : (x : MulAut W) w₁ = (x : MulAut W) 1 := by
          rw [map_one]
          exact h0
        exact (x : MulAut W).injective h1
      let e : C → ↥((commSub (⊤ : Subgroup W) Y : Set W) \ {1}) := fun x => ⟨_, hmem x⟩
      have he : Function.Injective e := by
        intro a b hab
        have h1 : (a : MulAut W) w₁ = (b : MulAut W) w₁ := congrArg Subtype.val hab
        have h2 : ((b : MulAut W)⁻¹ * a) w₁ = w₁ := by
          rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
        have h3 := eq_one_of_apply_eq hX (X.mul_mem (X.inv_mem b.2.1) a.2.1) (hU'U hw₁) hw₁1 h2
        apply Subtype.ext
        have := congrArg (fun z => (b : MulAut W) * z) h3
        simpa using this
      have h1 := Nat.card_le_card_of_injective e he
      rw [card_diff_one] at h1
      have h2 : 0 < Nat.card (commSub (⊤ : Subgroup W) Y) := Nat.card_pos
      omega
    have hcY := card_commSub hY
    have hcX := card_commSub hX
    have ha := card_eq_two_pow hW (commSub (⊤ : Subgroup W) X)
    have hb := card_eq_two_pow hW (commSub (⊤ : Subgroup W) Y)
    set a := rk (commSub (⊤ : Subgroup W) X)
    set b := rk (commSub (⊤ : Subgroup W) Y)
    have hDle : Nat.card D ≤ 2 ^ b := by omega
    have hab : a ≤ 2 * b := by
      have h1 : 2 ^ a ≤ 2 ^ (2 * b) := by
        rw [← ha, hcardU, hb, pow_mul', pow_two]
        exact Nat.mul_le_mul_right _ hDle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have hY3 : 3 ≤ Nat.card Y := by
      have h1 : Nat.card Y ≠ 1 := fun h0 => hY.2.1 (Subgroup.eq_bot_of_card_eq Y h0)
      obtain ⟨k, hk⟩ := hYodd
      omega
    have hapos : 0 < a := by
      by_contra h0
      have : a = 0 := by omega
      rw [this, pow_zero] at ha
      have := Nat.card_pos (α := X)
      omega
    have hYa : Nat.card Y ≤ a := Nat.le_of_dvd hapos hdvd
    have hb2 : b ≤ 2 := by
      by_contra hb3
      have h1 := two_mul_add_one_lt_two_pow (b := b) (by omega)
      omega
    have hb2' : b = 2 := by
      by_contra hne
      interval_cases b <;> omega
    rw [hb2'] at hb
    have hY : Nat.card Y = 3 := by omega
    rw [hY] at hdvd
    have ha3 : a = 3 := by omega
    rw [ha3] at ha
    exact ⟨by omega, hY⟩

theorem eq_of_fixV_eq (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (h : fixV X = fixV Y) : X = Y := by
  have hXN : X ≤ Subgroup.normalizer (Y : Set (MulAut W)) := fun x hx =>
    mem_normalizer_of_mapsTo hY (hX.1 hx) fun v hv => by
      rw [← h] at hv ⊢
      rw [hv x hx]
      exact hv
  have hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) := fun y hy =>
    mem_normalizer_of_mapsTo hX (hY.1 hy) fun v hv => by
      rw [h] at hv ⊢
      rw [hv y hy]
      exact hv
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
    by_contra hnc
    push Not at hnc
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have h1 := ten_six hW hX hY hYN ⟨x, hx, y, hy, hxy⟩
    have h2 := ten_six hW hY hX hXN ⟨y, hy, x, hx, fun h => hxy h.symm⟩
    omega
  by_contra hXY
  have h1 := commSub_le_fixV_of_commute hW hX hY hXY hcomm
  rw [← h] at h1
  apply commSub_ne_bot hX
  rw [eq_bot_iff]
  intro w hw
  have h2 : w ∈ fixV X ⊓ commSub ⊤ X := ⟨h1 hw, hw⟩
  rwa [fixV_inf_commSub_eq_bot' hW hX.2.2.2.1] at h2

end Pf

end Asc81c

end CFSG.Quasithin

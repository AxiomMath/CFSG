module

public import CFSG.Sporadic.Recognition.CoverRecipeSq

public section

namespace CFSG.Sporadic.Recognition.CoverBootstrap

open Subgroup
open scoped commutatorElement

theorem injective_of_card_le {A X : Type*} [Group A] [Group X] [Finite A] (ψ : A →* X)
    (h : Nat.card A ≤ Nat.card ψ.range) : Function.Injective ψ := by
  have hb : Function.Bijective ψ.rangeRestrict :=
    ψ.rangeRestrict_surjective.bijective_of_nat_card_le h
  intro a b hab
  exact hb.1 (Subtype.ext hab)

theorem hom_trivial_of_perfect {H : Type*} [Group H] (hH : commutator H = ⊤) {B : Type*}
    [Group B] (f : H →* B) (hc : ∀ a b : H, f a * f b = f b * f a) : f = 1 := by
  have hle : commutator H ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (hc a b)]
  ext h
  have : h ∈ f.ker := hle (hH ▸ mem_top h)
  simpa using this

theorem conj_eq_of_perfect {P X : Type*} [Group P] [Group X] (π : P →* X) (H : Subgroup P)
    (hperf : commutator H = ⊤) (hinj : ∀ h ∈ H, ∀ h' ∈ H, π h = π h' → h = h')
    (G : Set P) (hG : Subgroup.closure G = H) (d : P)
    (hgen : ∀ s ∈ G, ∃ u ∈ H, π u = π d * π s * (π d)⁻¹ ∧
      d * s * d⁻¹ * u⁻¹ ∈ Subgroup.center P) :
    ∀ h ∈ H, ∀ u ∈ H, π u = π d * π h * (π d)⁻¹ → d * h * d⁻¹ = u := by
  classical
  have hnorm : ∀ h ∈ H, ∃ u ∈ H, π u = π d * π h * (π d)⁻¹ := by
    intro h hh
    rw [← hG] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, hu, hπ, -⟩ := hgen x hx
      exact ⟨u, hG ▸ hu, hπ⟩
    | one => exact ⟨1, hG ▸ (Subgroup.one_mem _), by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, hux⟩ := hx
      obtain ⟨v, hv, hvy⟩ := hy
      exact ⟨u * v, mul_mem hu hv, by rw [map_mul, hux, hvy, map_mul]; group⟩
    | inv x _ hx =>
      obtain ⟨u, hu, hux⟩ := hx
      exact ⟨u⁻¹, inv_mem hu, by rw [map_inv, hux, map_inv]; group⟩
  choose! f hfH hfπ using hnorm
  have hmul : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b := fun a ha b hb =>
    hinj _ (hfH _ (mul_mem ha hb)) _ (mul_mem (hfH a ha) (hfH b hb)) (by
      rw [hfπ _ (mul_mem ha hb), map_mul π a b, map_mul π (f a) (f b), hfπ a ha, hfπ b hb]
      group)
  have hone : f 1 = 1 := hinj _ (hfH _ (one_mem H)) _ (one_mem H) (by
    rw [hfπ _ (one_mem H)]; simp)
  have hinv : ∀ a ∈ H, f a⁻¹ = (f a)⁻¹ := fun a ha => by
    have h1 : f (a * a⁻¹) = f a * f a⁻¹ := hmul a ha a⁻¹ (inv_mem ha)
    rw [mul_inv_cancel, hone] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  set κ : P → P := fun h => d * h * d⁻¹ * (f h)⁻¹ with hκ
  have hκmul : ∀ a ∈ H, ∀ b ∈ H, κ b ∈ Subgroup.center P → κ (a * b) = κ b * κ a := by
    intro a ha b hb hcb
    have hz := Subgroup.mem_center_iff.mp hcb
    simp only [hκ, hmul a ha b hb]
    calc d * (a * b) * d⁻¹ * (f a * f b)⁻¹
        = (d * a * d⁻¹) * (d * b * d⁻¹ * (f b)⁻¹) * (f a)⁻¹ := by group
      _ = (d * b * d⁻¹ * (f b)⁻¹) * (d * a * d⁻¹) * (f a)⁻¹ := by rw [← hz (d * a * d⁻¹)]
      _ = _ := by group
  have hκc : ∀ h ∈ H, κ h ∈ Subgroup.center P := by
    intro h hh
    rw [← hG] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, hu, hπ, hc⟩ := hgen x hx
      have hxH : x ∈ H := hG ▸ Subgroup.subset_closure hx
      have hfx : f x = u := hinj _ (hfH x hxH) _ hu (by rw [hfπ x hxH, hπ])
      simpa [hκ, hfx] using hc
    | one => simp [hκ, hone]
    | mul x y hx' hy' hx hy =>
      have hxH : x ∈ H := hG ▸ hx'
      have hyH : y ∈ H := hG ▸ hy'
      rw [hκmul x hxH y hyH hy]
      exact mul_mem hy hx
    | inv x hx' hx =>
      have hxH : x ∈ H := hG ▸ hx'
      have e1 : d * x * d⁻¹ = κ x * f x := by simp only [hκ]; group
      have e2 : κ x⁻¹ = (κ x)⁻¹ := by
        have hzi := Subgroup.mem_center_iff.mp (inv_mem hx)
        show d * x⁻¹ * d⁻¹ * (f x⁻¹)⁻¹ = _
        rw [hinv x hxH, inv_inv]
        calc d * x⁻¹ * d⁻¹ * f x = (d * x * d⁻¹)⁻¹ * f x := by group
          _ = (f x)⁻¹ * (κ x)⁻¹ * f x := by rw [e1]; group
          _ = (κ x)⁻¹ * (f x)⁻¹ * f x := by rw [hzi (f x)⁻¹]
          _ = (κ x)⁻¹ := by group
      rw [e2]
      exact inv_mem hx
  let κ' : H →* Subgroup.center P :=
    { toFun := fun h => ⟨κ h.1, hκc h.1 h.2⟩
      map_one' := by
        apply Subtype.ext
        simp [hκ, hone]
      map_mul' := fun a b => by
        apply Subtype.ext
        change κ (a.1 * b.1) = κ a.1 * κ b.1
        rw [hκmul a.1 a.2 b.1 b.2 (hκc b.1 b.2)]
        exact (Subgroup.mem_center_iff.mp (hκc b.1 b.2) (κ a.1)).symm }
  have h1 : κ' = 1 := hom_trivial_of_perfect hperf κ' fun a b =>
    Subtype.ext (by
      show κ a.1 * κ b.1 = κ b.1 * κ a.1
      exact Subgroup.mem_center_iff.mp (hκc b.1 b.2) (κ a.1))
  intro h hh u hu hπ
  have hκ1 : κ h = 1 := by
    have := congrArg (fun z : H →* Subgroup.center P => (z ⟨h, hh⟩ : P)) h1
    simpa [κ'] using this
  have hfu : f h = u := hinj _ (hfH h hh) _ hu (by rw [hfπ h hh, hπ])
  have : d * h * d⁻¹ * (f h)⁻¹ = 1 := hκ1
  rw [hfu] at this
  exact mul_inv_eq_one.mp this

theorem conj_identities {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {a b c d e g : G}
    (h0 : d * d ∈ N) (h1 : a * d * a * d ∈ N) (h2 : b⁻¹ * d⁻¹ * b * d ∈ N)
    (h3 : e⁻¹ * d * c * d ∈ N) (h4 : g⁻¹ * c * b * c⁻¹ ∈ N) :
    d * b * d⁻¹ * b⁻¹ ∈ N ∧ d * a * d⁻¹ * a⁻¹⁻¹ ∈ N ∧
      d * c * d⁻¹ * e⁻¹ ∈ N ∧ d * e * d⁻¹ * c⁻¹ ∈ N ∧
      d * g * d⁻¹ * (e * b * e⁻¹)⁻¹ ∈ N := by
  simp only [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    at h0 h1 h2 h3 h4 ⊢
  generalize (a : G ⧸ N) = a' at *
  generalize (b : G ⧸ N) = b' at *
  generalize (c : G ⧸ N) = c' at *
  generalize (d : G ⧸ N) = d' at *
  generalize (e : G ⧸ N) = e' at *
  generalize (g : G ⧸ N) = g' at *
  have hd : d'⁻¹ = d' := inv_eq_of_mul_eq_one_right h0
  rw [hd] at h2 ⊢
  have hb : d' * b' * d' = b' := by
    calc d' * b' * d' = b' * (b'⁻¹ * d' * b' * d') := by group
      _ = b' := by rw [h2, mul_one]
  have ha : d' * a' * d' = a'⁻¹ := by
    calc d' * a' * d' = a'⁻¹ * (a' * d' * a' * d') := by group
      _ = a'⁻¹ := by rw [h1, mul_one]
  have hc : d' * c' * d' = e' := by
    calc d' * c' * d' = e' * (e'⁻¹ * d' * c' * d') := by group
      _ = e' := by rw [h3, mul_one]
  have he : d' * e' * d' = c' := by
    rw [← hc]
    calc d' * (d' * c' * d') * d' = (d' * d') * c' * (d' * d') := by group
      _ = c' := by rw [h0]; group
  have hg : g' = c' * b' * c'⁻¹ := by
    calc g' = g' * (g'⁻¹ * c' * b' * c'⁻¹) := by rw [h4, mul_one]
      _ = c' * b' * c'⁻¹ := by group
  have hci : d' * c'⁻¹ * d' = e'⁻¹ := by
    calc d' * c'⁻¹ * d' = (d' * c' * d')⁻¹ := by simp [mul_inv_rev, hd, mul_assoc]
      _ = e'⁻¹ := by rw [hc]
  have hgd : d' * g' * d' = e' * b' * e'⁻¹ := by
    rw [hg]
    calc d' * (c' * b' * c'⁻¹) * d'
        = (d' * c' * d') * (d' * d')⁻¹ * (d' * b' * d') * (d' * d')⁻¹ * (d' * c'⁻¹ * d') := by
          group
      _ = e' * b' * e'⁻¹ := by rw [hc, hb, hci, h0]; group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc d' * b' * d' * b'⁻¹ = b' * b'⁻¹ := by rw [hb]
      _ = 1 := mul_inv_cancel _
  · calc d' * a' * d' * a'⁻¹⁻¹ = a'⁻¹ * a'⁻¹⁻¹ := by rw [ha]
      _ = 1 := mul_inv_cancel _
  · calc d' * c' * d' * e'⁻¹ = e' * e'⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel _
  · calc d' * e' * d' * c'⁻¹ = c' * c'⁻¹ := by rw [he]
      _ = 1 := mul_inv_cancel _
  · rw [hgd]
    exact mul_inv_cancel _

theorem sq_eq_one_of_conj {G : Type*} [Group G] {d g u : G}
    (hc : g * d * g⁻¹ * u⁻¹ ∈ center G) (hc2 : (g * d * g⁻¹ * u⁻¹) * (g * d * g⁻¹ * u⁻¹) = 1)
    (hu : u * u = 1) : d * d = 1 := by
  set c := g * d * g⁻¹ * u⁻¹ with hcdef
  have hz := Subgroup.mem_center_iff.mp hc
  have h1 : g * d * g⁻¹ = c * u := by rw [hcdef]; group
  have h2 : g * (d * d) * g⁻¹ = 1 := by
    calc g * (d * d) * g⁻¹ = (g * d * g⁻¹) * (g * d * g⁻¹) := by group
      _ = (c * u) * (c * u) := by rw [h1]
      _ = c * c * (u * u) := by
        rw [mul_assoc c u (c * u), ← mul_assoc u c u, hz u]
        group
      _ = 1 := by rw [hc2, hu, mul_one]
  calc d * d = g⁻¹ * (g * (d * d) * g⁻¹) * g := by group
    _ = 1 := by rw [h2]; group


theorem map_mem_commutator {F G : Type*} [Group F] [Group G] (φ : F →* G) {z : F}
    (hz : z ∈ commutator F) : φ z ∈ commutator G := by
  have h1 : φ z ∈ (commutator F).map φ := Subgroup.mem_map_of_mem φ hz
  have h2 : (commutator F).map φ ≤ commutator G := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h2 h1

theorem commutator_eq_top_of_commutator_words {P : Type*} [Group P] {k : ℕ} (x : Fin k → P)
    (w : Fin k → FreeGroup (Fin k)) (hw : ∀ j, w j ∈ commutator (FreeGroup (Fin k)))
    (hx : ∀ j, FreeGroup.lift x (w j) = x j) :
    commutator ↥(Subgroup.closure (Set.range x)) = ⊤ := by
  set H := Subgroup.closure (Set.range x) with hH
  let x' : Fin k → H := fun j => ⟨x j, Subgroup.subset_closure ⟨j, rfl⟩⟩
  let F : FreeGroup (Fin k) →* H := FreeGroup.lift x'
  have hFx : ∀ z, ((F z : H) : P) = FreeGroup.lift x z := fun z => by
    have : H.subtype.comp F = FreeGroup.lift x := FreeGroup.ext_hom _ _ fun j => by simp [F, x']
    exact congrArg (fun φ : FreeGroup (Fin k) →* P => φ z) this
  have hFc : ∀ z ∈ commutator (FreeGroup (Fin k)), F z ∈ commutator H := by
    intro z hz
    have h1 : F z ∈ (commutator (FreeGroup (Fin k))).map F := Subgroup.mem_map_of_mem F hz
    have h2 : (commutator (FreeGroup (Fin k))).map F ≤ commutator H := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range x)]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro ⟨y, hy⟩ ⟨j, hj⟩
  have hyj : (⟨y, hy⟩ : H) = x' j := Subtype.ext hj.symm
  show (⟨y, hy⟩ : H) ∈ commutator H
  rw [hyj]
  have hFj : F (w j) = x' j := Subtype.ext (by rw [hFx, hx j])
  rw [← hFj]
  exact hFc _ (hw j)

section Cover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer

variable {m : ℕ} {R : List (List (Fin m × Bool))} {cw : Fin m → List (Fin m × Bool)}

theorem lift_cover₂_eq_one {X : Type*} [Group X] {g : Fin m → X}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) :
    ∀ w ∈ cover₂Words R cw, FreeGroup.lift g (FreeGroup.mk w) = 1 := by
  intro w hwm
  rw [mem_cover₂Words] at hwm
  simp only [coverWords, squareWords, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hwm
  rcases hwm with (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩) | ⟨r, hr, rfl⟩
  · rw [mk_commWord, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
      map_commutatorElement, FreeGroup.lift_apply_of, hR r hr]
    simp [commutatorElement_def]
  · rw [show FreeGroup.mk ((i, false) :: cw i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) from rfl,
      map_mul, map_inv, FreeGroup.lift_apply_of, hw i, inv_mul_cancel]
  · rw [← FreeGroup.mul_mk, map_mul, hR r hr, mul_one]

abbrev coverGen (R : List (List (Fin m × Bool))) (cw : Fin m → List (Fin m × Bool)) (i : Fin m) :
    PG m (cover₂Words R cw) := PresentedGroup.of i

theorem lift_coverGen_eq_one : ∀ w ∈ cover₂Words R cw,
    FreeGroup.lift (coverGen R cw) (FreeGroup.mk w) = 1 := fun w hw => by
  rw [← mk_eq_lift_of]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem lift_coverGen_commWord (i : Fin m) :
    FreeGroup.lift (coverGen R cw) (FreeGroup.mk (cw i)) = coverGen R cw i := by
  have h := lift_coverGen_eq_one (R := R) (cw := cw) ((i, false) :: cw i) (by
    rw [mem_cover₂Words]
    refine Or.inl ?_
    simp only [coverWords, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and]
    exact Or.inr ⟨i, rfl⟩)
  rw [show FreeGroup.mk ((i, false) :: cw i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) from rfl,
    map_mul, map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one] at h
  exact h.symm

theorem mem_center_of_comm_gens {ws : List (List (Fin m × Bool))} {z : PG m ws}
    (h : ∀ i : Fin m, PresentedGroup.of i * z = z * PresentedGroup.of i) :
    z ∈ center (PG m ws) := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin m → PG m ws)) := by
    rw [PresentedGroup.closure_range_of]; trivial
  induction hy using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    have : z * a = a * z := ha.symm
    calc a⁻¹ * z = a⁻¹ * z * a * a⁻¹ := by group
      _ = a⁻¹ * (z * a) * a⁻¹ := by rw [mul_assoc a⁻¹ z a]
      _ = z * a⁻¹ := by rw [this]; group

theorem lift_coverGen_rel_center {r : List (Fin m × Bool)} (hr : r ∈ R) :
    FreeGroup.lift (coverGen R cw) (FreeGroup.mk r) ∈ center (PG m (cover₂Words R cw)) := by
  refine mem_center_of_comm_gens fun i => ?_
  have h := lift_coverGen_eq_one (R := R) (cw := cw) (commWord [(i, true)] r) (by
    rw [mem_cover₂Words]
    refine Or.inl ?_
    simp only [coverWords, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and]
    exact Or.inl ⟨i, r, hr, rfl⟩)
  rw [mk_commWord, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
    map_commutatorElement, FreeGroup.lift_apply_of] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem lift_coverGen_rel_sq {r : List (Fin m × Bool)} (hr : r ∈ R) :
    FreeGroup.lift (coverGen R cw) (FreeGroup.mk r) *
      FreeGroup.lift (coverGen R cw) (FreeGroup.mk r) = 1 := by
  have h := lift_coverGen_eq_one (R := R) (cw := cw) (r ++ r) (by
    rw [mem_cover₂Words]
    refine Or.inr ?_
    simp only [squareWords, List.mem_map]
    exact ⟨r, hr, rfl⟩)
  rwa [← FreeGroup.mul_mk, map_mul] at h

end Cover

end CFSG.Sporadic.Recognition.CoverBootstrap

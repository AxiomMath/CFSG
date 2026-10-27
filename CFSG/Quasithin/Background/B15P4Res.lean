module

public import CFSG.Quasithin.Background.B15P4Comp
public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.Background.B1MoreSeven

public section

namespace CFSG.Quasithin.B15P4

open CFSG.Open
open scoped commutatorElement

section CommInv

variable {V : Type*} [CommGroup V]

theorem map_commSub_mem {W : Subgroup V} {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) (hW : ∀ w ∈ W, g w ∈ W) :
    ∀ c ∈ commSub W X, g c ∈ commSub W X := by
  have hle : commSub W X ≤ (commSub W X).comap g.toMonoidHom := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    show g (x w * w⁻¹) ∈ commSub W X
    have hx' : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have e : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hx', g w, hW w hw, rfl⟩
  intro c hc
  exact hle hc

theorem map_commV_mem {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) : ∀ c ∈ commV X, g c ∈ commV X := by
  rw [commV_eq_commSub]
  exact map_commSub_mem hg fun _ _ => Subgroup.mem_top _

theorem commSub_commV_of_perfect {X : Subgroup (MulAut V)} (hX : ⁅X, X⁆ = X) :
    commSub (commV X) X = commV X := by
  refine le_antisymm (commSub_le_of_invariant fun x hx v hv => ?_) ?_
  · exact map_commV_mem (Subgroup.le_normalizer hx) v hv
  · let U' := commSub (commV X) X
    let T : Subgroup (MulAut V) :=
      { carrier := {g | ∀ v, g v * v⁻¹ ∈ U'}
        one_mem' := fun v => by simp
        mul_mem' := by
          intro g h hg hh v
          have e : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
            rw [MulAut.mul_apply]
            group
          rw [e]
          exact U'.mul_mem (hg (h v)) (hh v)
        inv_mem' := by
          intro g hg v
          have e : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
            simp
          rw [e]
          exact U'.inv_mem (hg (g⁻¹ v)) }
    have hXT : X ≤ T := by
      calc X = ⁅X, X⁆ := hX.symm
        _ ≤ T := by
          rw [Subgroup.commutator_le]
          intro x hx y hy v
          set w : V := (y * x)⁻¹ v with hw
          have hv : v = (y * x) w := by simp [hw]
          have h1 : ⁅x, y⁆ v = (x * y) w := by
            have hc : ⁅x, y⁆ * (y * x) = x * y := by
              simp only [commutatorElement_def]
              group
            conv_lhs => rw [hv]
            rw [← MulAut.mul_apply, hc]
          have h2 : ⁅x, y⁆ v * v⁻¹ = (x (y w * w⁻¹) * (y w * w⁻¹)⁻¹) *
              (y (x w * w⁻¹) * (x w * w⁻¹)⁻¹)⁻¹ := by
            rw [h1]
            conv_lhs => rw [hv]
            simp only [MulAut.mul_apply, map_mul, map_inv, mul_inv_rev, inv_inv]
            apply Additive.ofMul.injective
            simp only [ofMul_mul, ofMul_inv]
            abel
          show ⁅x, y⁆ v * v⁻¹ ∈ U'
          rw [h2]
          have hdy : y w * w⁻¹ ∈ commV X := Subgroup.subset_closure ⟨y, hy, w, rfl⟩
          have hdx : x w * w⁻¹ ∈ commV X := Subgroup.subset_closure ⟨x, hx, w, rfl⟩
          have a1 : x (y w * w⁻¹) * (y w * w⁻¹)⁻¹ ∈ U' :=
            Subgroup.subset_closure ⟨x, hx, y w * w⁻¹, hdy, rfl⟩
          have a2 : y (x w * w⁻¹) * (x w * w⁻¹)⁻¹ ∈ U' :=
            Subgroup.subset_closure ⟨y, hy, x w * w⁻¹, hdx, rfl⟩
          exact U'.mul_mem a1 (U'.inv_mem a2)
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact hXT hx v

end CommInv

section Pull

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_eq_on_of_normalizes {A K : Subgroup (MulAut V)} {W : Subgroup V}
    (hAW : A ≤ stabSub W) (hKW : K ≤ stabSub W)
    (hnorm : autSub A W ≤ Subgroup.normalizer (autSub K W : Set (MulAut W)))
    {a k : MulAut V} (ha : a ∈ A) (hk : k ∈ K) :
    ∃ k' ∈ K, ∀ u ∈ W, (a * k * a⁻¹) u = k' u := by
  have habar : resHom W ⟨a, hAW ha⟩ ∈ autSub A W := mem_autSub.mpr ⟨⟨a, hAW ha⟩, ha, rfl⟩
  have hkbar : resHom W ⟨k, hKW hk⟩ ∈ autSub K W := mem_autSub.mpr ⟨⟨k, hKW hk⟩, hk, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm habar) _).mp hkbar
  obtain ⟨g', hg'K, hg'⟩ := mem_autSub.mp h1
  refine ⟨g'.1, hg'K, fun u hu => ?_⟩
  have h2 := congrArg (fun φ : MulAut W => ((φ ⟨u, hu⟩ : W) : V)) hg'
  have h3 : ∀ x : stabSub W, ((resHom W x ⟨u, hu⟩ : W) : V) = (x : MulAut V) u := fun x => rfl
  have e : resHom W ⟨a, hAW ha⟩ * resHom W ⟨k, hKW hk⟩ * (resHom W ⟨a, hAW ha⟩)⁻¹ =
      resHom W (⟨a, hAW ha⟩ * ⟨k, hKW hk⟩ * ⟨a, hAW ha⟩⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e, h3, h3] at h2
  exact h2.symm

theorem normalizer_of_autSub {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {W : Subgroup V} (hEW : Kspan A K ≤ stabSub W) (hAW : A ≤ stabSub W)
    (hKW : ¬ K ≤ centSub W)
    (hnorm : autSub A W ≤ Subgroup.normalizer (autSub K W : Set (MulAut W))) :
    A ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  intro a ha
  rw [mem_normalizer_iff_conjAut]
  have hKE : K ≤ Kspan A K := le_Kspan A K
  have hZ := Kspan_centSub_commutator hK hAG hEW
    (fun b hb => not_conjAut_le_centSub hAW hKW hb)
  have hcen : ∀ y ∈ Kspan A K ⊓ centSub W, ∀ e ∈ Kspan A K, y * e = e * y := by
    intro y hy e he
    have h1 := Subgroup.commutator_mem_commutator hy he
    rw [hZ, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hdecomp : ∀ x ∈ B1.conjAut a K, ∃ k' ∈ K, ∃ y ∈ Kspan A K ⊓ centSub W, x = y * k' := by
    intro x hx
    have hkx : a⁻¹ * x * a ∈ K := (B1.mem_conjAut).mp hx
    obtain ⟨k', hk'K, hk'⟩ := exists_eq_on_of_normalizes hAW (hKE.trans hEW) hnorm ha hkx
    refine ⟨k', hk'K, x * k'⁻¹, ⟨?_, ?_⟩, by simp⟩
    · exact (Kspan A K).mul_mem (conjAut_le_Kspan ha hx) ((Kspan A K).inv_mem (hKE hk'K))
    · refine mem_centSub.mpr fun u hu => ?_
      have hk'u : k'⁻¹ u ∈ W := (mem_stabSub.mp ((stabSub W).inv_mem (hKE.trans hEW hk'K)) u).mpr hu
      have h1 := hk' (k'⁻¹ u) hk'u
      have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      rw [e] at h1
      simp only [MulAut.mul_apply]
      rw [h1]
      exact MulAut.apply_inv_self _ k' u
  have hle : B1.conjAut a K ≤ K := by
    have hKa := isComponentOf_conjAut_of_mem hK hAG ha
    calc B1.conjAut a K = ⁅B1.conjAut a K, B1.conjAut a K⁆ :=
          (perfect_of_isComponentOf hKa).symm
      _ ≤ K := by
        rw [Subgroup.commutator_le]
        intro x₁ hx₁ x₂ hx₂
        obtain ⟨k₁, hk₁, y₁, hy₁, rfl⟩ := hdecomp x₁ hx₁
        obtain ⟨k₂, hk₂, y₂, hy₂, rfl⟩ := hdecomp x₂ hx₂
        rw [commutator_mul_central (hcen y₁ hy₁ y₂ hy₂.1) (hcen y₁ hy₁ k₁ (hKE hk₁))
          (hcen y₁ hy₁ k₂ (hKE hk₂)) (hcen y₂ hy₂ k₁ (hKE hk₁)) (hcen y₂ hy₂ k₂ (hKE hk₂))]
        exact Subgroup.commutator_mem_commutator hk₁ hk₂ |> fun h =>
          (Subgroup.commutator_le_self K) h
  have hcard : Nat.card K ≤ Nat.card (B1.conjAut a K) := by rw [B1.card_conjAut]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end Pull

section Pkg

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isFFStarOffender_sup {G A E : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    IsFFStarOffender (E ⊔ A) A :=
  ⟨le_sup_right, hA.2⟩

theorem isFFStarOffender_autSub_Kspan {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    {W : Subgroup V} (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥) :
    IsFFStarOffender (autSub (Kspan A K ⊔ A) W) (autSub A W) :=
  B1_5_1 (isFFStarOffender_sup hA) hAW hWA

omit [Finite V] in
theorem isComponentOf_autSub_Kspan {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {W : Subgroup V} (hEW : Kspan A K ≤ stabSub W) (hAW : A ≤ stabSub W)
    (hKW : ¬ K ≤ centSub W) :
    IsComponentOf (autSub K W) (autSub (Kspan A K ⊔ A) W) := by
  have hG' : Kspan A K ⊔ A ≤ G := sup_le (Kspan_le hK.1 hAG) hAG
  have hK' : IsComponentOf K (Kspan A K ⊔ A) :=
    isComponentOf_of_le hK ((le_Kspan A K).trans le_sup_left) hG'
  have hS : Kspan A K ⊔ A ≤ stabSub W := sup_le hEW hAW
  have h1 := isComponentOf_subgroupOf (stabSub W) hK' hS
  refine isComponentOf_map_hom (resHom W) h1 ?_
  intro hle
  apply hKW
  intro k hk
  have hkS : k ∈ stabSub W := hEW (le_Kspan A K hk)
  have h2 : (⟨k, hkS⟩ : stabSub W) ∈ K.subgroupOf (stabSub W) := hk
  have h3 := hle h2
  rw [ker_resHom, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem restrict_package {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hK : IsComponentOf K G) {W : Subgroup V} (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hEW : ∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) (hWA : commSub W A ≠ ⊥)
    (hKW : ¬ K ≤ centSub W) :
    IsFFStarOffender (autSub (Kspan A K ⊔ A) W) (autSub A W) ∧
      IsComponentOf (autSub K W) (autSub (Kspan A K ⊔ A) W) ∧
      (autSub A W ≤ Subgroup.normalizer (autSub K W : Set (MulAut W)) →
        A ≤ Subgroup.normalizer (K : Set (MulAut V))) := by
  have hAS := B1.le_stabSub_of_invariant hAW
  have hES := B1.le_stabSub_of_invariant hEW
  exact ⟨isFFStarOffender_autSub_Kspan hA hAW hWA,
    isComponentOf_autSub_Kspan hK hA.1 hES hAS hKW,
    normalizer_of_autSub hK hA.1 hES hAS hKW⟩

end Pkg

section CommE

variable {V : Type*} [CommGroup V]

theorem eq_bot_of_commV_eq_bot {X : Subgroup (MulAut V)} (h : commV X = ⊥) : X = ⊥ :=
  CFSG.Quasithin.FixVLat.eq_bot_of_commV_eq_bot h

theorem Kspan_invariant_commV (A K : Subgroup (MulAut V)) :
    ∀ e ∈ Kspan A K, ∀ c ∈ commV (Kspan A K), e c ∈ commV (Kspan A K) :=
  fun _ he => map_commV_mem (Subgroup.le_normalizer he)

theorem A_invariant_commV (A K : Subgroup (MulAut V)) :
    ∀ a ∈ A, ∀ c ∈ commV (Kspan A K), a c ∈ commV (Kspan A K) :=
  fun _ ha => map_commV_mem (le_normalizer_Kspan A K ha)

theorem Kspan_le_centSub_of_fixed {A K : Subgroup (MulAut V)} (hE : ⁅Kspan A K, A⁆ = Kspan A K)
    {W : Subgroup V} (hEW : ∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) (hWA : W ≤ fixV A) :
    Kspan A K ≤ centSub W := by
  calc Kspan A K = ⁅Kspan A K, A⁆ := hE.symm
    _ ≤ centSub W := by
      rw [Subgroup.commutator_le]
      intro e he a ha
      refine mem_centSub.mpr fun u hu => ?_
      have h1 : a⁻¹ u = u := hWA hu a⁻¹ (A.inv_mem ha)
      have h2 : e⁻¹ u ∈ W := hEW e⁻¹ ((Kspan A K).inv_mem he) u hu
      have h3 : a (e⁻¹ u) = e⁻¹ u := hWA h2 a ha
      show (e * a * e⁻¹ * a⁻¹) u = u
      simp only [MulAut.mul_apply]
      rw [h1, h3]
      exact MulAut.apply_inv_self _ e u

theorem Kspan_le_centSub_of_le {A K : Subgroup (MulAut V)} {W : Subgroup V} (hAW : A ≤ stabSub W)
    (hKW : K ≤ centSub W) : Kspan A K ≤ centSub W := by
  refine Kspan_le_iff.mpr fun a ha x hx => ?_
  have hx' : a⁻¹ * x * a ∈ K := B1.mem_conjAut.mp hx
  have hk := mem_centSub.mp (hKW hx')
  refine mem_centSub.mpr fun u hu => ?_
  have h1 : a⁻¹ u ∈ W := (mem_stabSub.mp ((stabSub W).inv_mem (hAW ha)) u).mpr hu
  have h2 := hk (a⁻¹ u) h1
  simp only [MulAut.mul_apply] at h2
  rw [MulAut.apply_inv_self] at h2
  exact a⁻¹.injective h2

theorem Kspan_le_stabSub_commV (A K : Subgroup (MulAut V)) :
    Kspan A K ≤ stabSub (commV (Kspan A K)) :=
  B1.le_stabSub_of_invariant (Kspan_invariant_commV A K)

theorem not_le_centSub_commV_Kspan {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G) :
    ¬ K ≤ centSub (commV (Kspan A K)) := by
  intro h
  have hperf := perfect_of_isComponentOf hK
  have h1 : commSub (commV K) K = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro u hu k hk
    have : u ∈ commV (Kspan A K) := G6.commV_mono (le_Kspan A K) hu
    exact mem_centSub.mp (h hk) u this
  have h2 := commSub_commV_of_perfect hperf
  rw [h1] at h2
  exact ne_bot_of_isComponentOf hK (eq_bot_of_commV_eq_bot h2.symm)

variable [Finite V]

theorem commSub_commV_Kspan_ne_bot {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {a₀ : MulAut V} (ha₀ : a₀ ∈ A)
    (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V))) :
    commSub (commV (Kspan A K)) A ≠ ⊥ := by
  intro hbot
  have hUA : commV (Kspan A K) ≤ fixV A := commSub_eq_bot_iff.mp hbot
  have hE := commutator_Kspan_eq hK hAG ha₀ hn
  have hEc := Kspan_le_centSub_of_fixed hE (Kspan_invariant_commV A K) hUA
  have h1 : commSub (commV (Kspan A K)) (Kspan A K) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro u hu e he
    exact mem_centSub.mp (hEc he) u hu
  have h2 := commSub_commV_of_perfect (Kspan_perfect hK hAG)
  rw [h1] at h2
  have h3 := eq_bot_of_commV_eq_bot h2.symm
  exact ne_bot_of_isComponentOf hK (eq_bot_iff.mpr ((le_Kspan A K).trans h3.le))

theorem restrict_commV {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hK : IsComponentOf K G) {a₀ : MulAut V} (ha₀ : a₀ ∈ A)
    (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V))) :
    IsFFStarOffender (autSub (Kspan A K ⊔ A) (commV (Kspan A K))) (autSub A (commV (Kspan A K))) ∧
      IsComponentOf (autSub K (commV (Kspan A K)))
        (autSub (Kspan A K ⊔ A) (commV (Kspan A K))) ∧
      (autSub A (commV (Kspan A K)) ≤
          Subgroup.normalizer (autSub K (commV (Kspan A K)) : Set (MulAut (commV (Kspan A K)))) →
        A ≤ Subgroup.normalizer (K : Set (MulAut V))) :=
  restrict_package hA hK (A_invariant_commV A K) (Kspan_invariant_commV A K)
    (commSub_commV_Kspan_ne_bot hK hA.1 ha₀ hn) (not_le_centSub_commV_Kspan hK)

theorem restrict_irrPlus {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hK : IsComponentOf K G) (hE : ⁅Kspan A K, A⁆ = Kspan A K) {I : Subgroup V}
    (hI : I ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V)) (hIA : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I) :
    IsFFStarOffender (autSub (Kspan A K ⊔ A) I) (autSub A I) ∧
      IsComponentOf (autSub K I) (autSub (Kspan A K ⊔ A) I) ∧
      (autSub A I ≤ Subgroup.normalizer (autSub K I : Set (MulAut I)) →
        A ≤ Subgroup.normalizer (K : Set (MulAut V))) := by
  obtain ⟨invI, commI, ltI, -⟩ := mem_irrPlus_top_iff.mp hI
  have hnot : ¬ I ≤ fixV (Kspan A K) := by
    intro h
    have h1 : I ⊓ fixV (Kspan A K) = I := inf_eq_left.mpr h
    rw [h1] at ltI
    exact lt_irrefl _ ltI
  have hbot : ¬ commSub I (Kspan A K) = ⊥ := fun h => hnot (commSub_eq_bot_iff.mp h)
  refine restrict_package hA hK hIA invI ?_ ?_
  · intro hbot'
    exact hbot (by
      have h1 := Kspan_le_centSub_of_fixed hE invI (commSub_eq_bot_iff.mp hbot')
      rw [commSub_eq_bot_iff]
      intro u hu e he
      exact mem_centSub.mp (h1 he) u hu)
  · intro hKI
    exact hbot (by
      have h1 := Kspan_le_centSub_of_le (B1.le_stabSub_of_invariant hIA) hKI
      rw [commSub_eq_bot_iff]
      intro u hu e he
      exact mem_centSub.mp (h1 he) u hu)

end CommE

section Induction

@[expose] def Part4Below (n : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V < n → (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ K : Subgroup (MulAut V), IsComponentOf K G →
        A ≤ Subgroup.normalizer (K : Set (MulAut V))

theorem false_of_proper {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (IH : Part4Below (Nat.card V)) {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hK : IsComponentOf K G) {a₀ : MulAut V} (ha₀ : a₀ ∈ A)
    (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V))) {W : Subgroup V} (hW : W ≠ ⊤)
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hEW : ∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hKW : ¬ K ≤ centSub W) : False := by
  obtain ⟨h1, h2, h3⟩ := restrict_package hA hK hAW hEW hWA hKW
  have hlt : Nat.card W < Nat.card V := by
    have h := Subgroup.card_mul_index W
    have hidx : W.index ≠ 1 := fun h1 => hW (Subgroup.index_eq_one.mp h1)
    have hidx0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hpos : 0 < Nat.card W := Nat.card_pos
    have h2 : 2 ≤ W.index := by omega
    nlinarith
  exact hn (h3 (IH W hlt (B1.sq_eq_one_sub hV W) _ _ h1 _ h2) ha₀)

theorem part4_of_key₂
    (key : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ A K : Subgroup (MulAut V), IsFFStarOffender (Kspan A K ⊔ A) A →
        IsComponentOf K (Kspan A K ⊔ A) → (∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut V))) →
        commV (Kspan A K) = ⊤ →
        (∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
          (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False) →
        (∀ B : Subgroup (MulAut V), B ≤ A → B ≠ A → IsFFStarOffender (Kspan A K ⊔ A) B →
          B ≤ Subgroup.normalizer (K : Set (MulAut V))) →
        Part4Below (Nat.card V) → False) :
    AsB15Part4 := by
  have main : ∀ n m : ℕ, ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V = n →
      (∀ v : V, v ^ 2 = 1) → ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
        Nat.card A = m → ∀ K : Subgroup (MulAut V), IsComponentOf K G →
          A ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IHn =>
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IHm =>
        intro V _ _ hVn hV G A hA hAm K hK
        by_contra hcon
        obtain ⟨a₀, ha₀, hn⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut V)) := by
          by_contra hnot
          exact hcon fun a ha => by_contra fun h => hnot ⟨a, ha, h⟩
        have IH : Part4Below (Nat.card V) := fun V' _ _ hlt hV' G' A' hA' K' hK' =>
          IHn (Nat.card V') (lt_of_lt_of_eq hlt hVn) (Nat.card A') V' rfl hV' G' A' hA' rfl K' hK'
        have hA' : IsFFStarOffender (Kspan A K ⊔ A) A := isFFStarOffender_sup hA
        have hK' : IsComponentOf K (Kspan A K ⊔ A) :=
          isComponentOf_of_le hK ((le_Kspan A K).trans le_sup_left)
            (sup_le (Kspan_le hK.1 hA.1) hA.1)
        have hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
            (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W →
              False :=
          fun W hW hAW hEW hWA hKW => false_of_proper hV IH hA hK ha₀ hn hW hAW hEW hWA hKW
        have hcomm : commV (Kspan A K) = ⊤ := by
          by_contra hne
          exact hmin (commV (Kspan A K)) hne (A_invariant_commV A K) (Kspan_invariant_commV A K)
            (commSub_commV_Kspan_ne_bot hK hA.1 ha₀ hn) (not_le_centSub_commV_Kspan hK)
        have hprop : ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ A →
            IsFFStarOffender (Kspan A K ⊔ A) B → B ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
          intro B hBA hBne hB
          have hcard : Nat.card B < Nat.card A :=
            lt_of_le_of_ne (Subgroup.card_le_of_le hBA)
              fun h => hBne (Subgroup.eq_of_le_of_card_ge hBA h.ge)
          exact IHm (Nat.card B) (lt_of_lt_of_eq hcard hAm) V hVn hV (Kspan A K ⊔ A) B hB rfl K hK'
        exact key V hV A K hA' hK' ⟨a₀, ha₀, hn⟩ hcomm hmin hprop IH
  intro V _ _ hV G A hA K hK
  exact main (Nat.card V) (Nat.card A) V rfl hV G A hA rfl K hK

theorem part4_of_key
    (key : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ A K : Subgroup (MulAut V), IsFFStarOffender (Kspan A K ⊔ A) A →
        IsComponentOf K (Kspan A K ⊔ A) → (∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut V))) →
        commV (Kspan A K) = ⊤ →
        (∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
          (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False) →
        Part4Below (Nat.card V) → False) :
    AsB15Part4 :=
  part4_of_key₂ fun V _ _ hV A K hA hK hex hcomm hmin _ IH =>
    key V hV A K hA hK hex hcomm hmin IH

end Induction

section Reduced

variable {V : Type*} [CommGroup V]

theorem le_fixV_of_not_restrictable {A K : Subgroup (MulAut V)}
    (hE : ⁅Kspan A K, A⁆ = Kspan A K) {W : Subgroup V}
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hEW : ∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W)
    (hmin : commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False) : W ≤ fixV (Kspan A K) := by
  by_cases h1 : commSub W A = ⊥
  · have h := Kspan_le_centSub_of_fixed hE hEW (commSub_eq_bot_iff.mp h1)
    intro w hw e he
    exact mem_centSub.mp (h he) w hw
  · by_cases h2 : K ≤ centSub W
    · have h := Kspan_le_centSub_of_le (B1.le_stabSub_of_invariant hAW) h2
      intro w hw e he
      exact mem_centSub.mp (h he) w hw
    · exact (hmin h1 h2).elim

theorem centralizer_Kspan_eq_bot (hV : ∀ v : V, v ^ 2 = 1) [Finite V] {A K : Subgroup (MulAut V)}
    (hAab : IsElemAbelian2 A) (hK1 : K ≠ ⊥) (hE : ⁅Kspan A K, A⁆ = Kspan A K)
    (hcomm : commV (Kspan A K) = ⊤)
    (hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False) :
    A ⊓ Subgroup.centralizer (Kspan A K : Set (MulAut V)) = ⊥ := by
  set B := A ⊓ Subgroup.centralizer (Kspan A K : Set (MulAut V)) with hB
  have hBA : B ≤ A := inf_le_left
  have hBE : ∀ b ∈ B, ∀ e ∈ Kspan A K, b * e = e * b := fun b hb e he =>
    ((Subgroup.mem_centralizer_iff.mp hb.2) e he).symm
  by_contra hB1
  have hnormB : ∀ g : MulAut V, (∀ b ∈ B, g * b * g⁻¹ ∈ B) →
      ∀ c ∈ commV B, g c ∈ commV B := fun g hg c hc => G6.apply_mem_commV hg hc
  have hAinv : ∀ a ∈ A, ∀ w ∈ commV B, a w ∈ commV B := by
    intro a ha w hw
    refine hnormB a (fun b hb => ?_) w hw
    have : a * b * a⁻¹ = b := by
      rw [hAab.1 a ha b (hBA hb), mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hb
  have hEinv : ∀ e ∈ Kspan A K, ∀ w ∈ commV B, e w ∈ commV B := by
    intro e he w hw
    refine hnormB e (fun b hb => ?_) w hw
    have : e * b * e⁻¹ = b := by
      rw [← hBE b hb e he, mul_inv_cancel_right]
    rw [this]
    exact hb
  have hVnt : Nontrivial V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hK1
    rw [Subgroup.eq_bot_iff_forall]
    intro k _
    ext v
    exact Subsingleton.elim _ _
  have hnotTop : commV B ≠ ⊤ := by
    refine G6.commV_ne_top_of_two_power hV (K := B) (N := ⊥) (fun k _ n hn => ?_)
      (fun k hk => ⟨1, ?_⟩) ?_
    · rw [Subgroup.mem_bot] at hn
      rw [hn]
      simp
    · simpa using hAab.2 k (hBA hk)
    · rw [commV_eq_commSub]
      intro h
      have h2 : commSub (⊤ : Subgroup V) (⊥ : Subgroup (MulAut V)) = ⊥ :=
        commSub_eq_bot_iff.mpr (by rw [B1.fixV_bot])
      rw [h2] at h
      exact bot_ne_top h
  have hfix : commV B ≤ fixV (Kspan A K) :=
    le_fixV_of_not_restrictable hE hAinv hEinv
      (fun h1 h2 => hmin (commV B) hnotTop hAinv hEinv h1 h2)
  apply hB1
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  have hgen : ∀ e ∈ Kspan A K, ∀ v : V, b (e v * v⁻¹) = e v * v⁻¹ := by
    intro e he v
    have hw : b v * v⁻¹ ∈ commV B := G6.mem_commV_of_mem hb v
    have h1 : e (b v * v⁻¹) = b v * v⁻¹ := hfix hw e he
    have h2 : b (e v) = e (b v) := by
      have := hBE b hb e he
      simpa [MulAut.mul_apply] using congrArg (fun g : MulAut V => g v) this
    have h3 : e (b v) = e v * (b v * v⁻¹) := by
      have : b v = v * (b v * v⁻¹) := by rw [mul_comm (b v) v⁻¹, mul_inv_cancel_left]
      conv_lhs => rw [this]
      rw [map_mul, h1]
    rw [map_mul, map_inv, h2, h3]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hle : commV (Kspan A K) ≤ MonoidHom.eqLocus b.toMonoidHom (MonoidHom.id V) :=
    G6.commV_le_iff.mpr fun x hx v => hgen x hx v
  rw [hcomm] at hle
  ext x
  exact hle (Subgroup.mem_top x)

end Reduced

end CFSG.Quasithin.B15P4

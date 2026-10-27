module

public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open CFSG.CosetTable CFSG.LieType.Multipliers Subgroup
open scoped commutatorElement

variable {m : ℕ}

@[expose] def squareWords (R : List (List (Fin m × Bool))) : List (List (Fin m × Bool)) :=
  R.map fun r => r ++ r

@[expose] def cover₂Words (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool)) :
    List (List (Fin m × Bool)) :=
  (coverWords R w ++ squareWords R).mergeSort fun a b => decide (a.length ≤ b.length)

theorem mem_cover₂Words {R : List (List (Fin m × Bool))} {w : Fin m → List (Fin m × Bool)}
    {x : List (Fin m × Bool)} :
    x ∈ cover₂Words R w ↔ x ∈ coverWords R w ∨ x ∈ squareWords R := by
  unfold cover₂Words
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_append]

theorem commutator_mul_center {Y : Type*} [Group Y] {a b z w : Y} (hz : z ∈ center Y)
    (hw : w ∈ center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
  have h2 : z * (b * w) * z⁻¹ = b * w := by rw [← hz' (b * w)]; group
  rw [h1, h2]
  have h3 : a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
  have h4 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← hw' a⁻¹]; group
  rw [h3, h4]

theorem eq_of_mem_commutator_of_central {G E S : Type*} [Group G] [Group E] [Group S]
    (q : E →* S) (hker : q.ker ≤ center E) (φ φ' : G →* E) (h : q.comp φ = q.comp φ') {x : G}
    (hx : x ∈ commutator G) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center E := fun y => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      inv_mul_cancel]
  have hle : commutator G ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, commutator_mul_center (hc a) (hc b)]
  exact hle hx


theorem center_eq_bot_of_sq {Q : Type*} [Group Q] [Finite Q] (hZ : IsPGroup 2 (center Q))
    (hsq : ∀ z ∈ center Q, ∃ b ∈ center Q, b * b = z) : center Q = ⊥ := by
  let f : center Q → center Q := fun b => ⟨b.1 * b.1, mul_mem b.2 b.2⟩
  have hsurj : Function.Surjective f := fun z => by
    obtain ⟨b, hb, hbz⟩ := hsq z.1 z.2
    exact ⟨⟨b, hb⟩, Subtype.ext hbz⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  by_contra hne
  have hcard : Nat.card (center Q) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have h2 : 2 ∣ Nat.card (center Q) := by
    rcases n with _ | n
    · exact absurd hn hcard
    · rw [hn]; exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hxx : f x = f 1 := by
    apply Subtype.ext
    have h1 : x.1 * x.1 = 1 := by
      have := congrArg Subtype.val hx2
      simpa [pow_two] using this
    simp [f, h1]
  have := hinj hxx
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)


theorem center_eq_bot_of_cover₂ {X : Type} [Group X] {g : Fin m → X}
    (hgen : Subgroup.closure (Set.range g) = ⊤) {R : List (List (Fin m × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) {cw : Fin m → List (Fin m × Bool)}
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i)
    (hfin : Finite (PG m (cover₂Words R cw)))
    (hcard : Nat.card (PG m (cover₂Words R cw)) ≤ Nat.card X) {Q : Type} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (hZ : IsPGroup 2 (center Q)) (e : Q ⧸ center Q ≃* X) :
    center Q = ⊥ := by
  classical
  have hXfin : Finite X := Finite.of_surjective _ e.surjective
  set q : Q →* X := centerQuotMap e with hq_def
  have hqs : Function.Surjective q := centerQuotMap_surjective e
  have hker : q.ker = center Q := ker_centerQuotMap e
  have hcomp : ∀ b : Fin m → Q, q.comp (FreeGroup.lift b) = FreeGroup.lift (fun i => q (b i)) :=
    fun b => FreeGroup.ext_hom _ _ fun i => by simp
  choose a ha using fun i => hqs (g i)
  set ee : Fin m → Q := fun i => FreeGroup.lift a (FreeGroup.mk (cw i)) with hee
  have hqa : (fun i => q (a i)) = g := funext ha
  have hqee : (fun i => q (ee i)) = g := by
    funext i
    simp only [hee]
    rw [← MonoidHom.comp_apply, hcomp, hqa, hwg]
  have hfix : ∀ i, FreeGroup.lift ee (FreeGroup.mk (cw i)) = ee i := fun i =>
    eq_of_mem_commutator_of_central q hker.le (FreeGroup.lift ee) (FreeGroup.lift a)
      (by rw [hcomp, hcomp, hqa, hqee]) (hw i)
  have hrc : ∀ r ∈ R, FreeGroup.lift ee (FreeGroup.mk r) ∈ center Q := fun r hr => by
    rw [← hker, MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp, hqee]
    exact hR r hr
  let N : Subgroup Q :=
    { carrier := {x | ∃ z ∈ center Q, x = z * z}
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨z, hz, rfl⟩ := hx
        obtain ⟨w, hw, rfl⟩ := hy
        refine ⟨z * w, mul_mem hz hw, ?_⟩
        have h1 : w * z = z * w := (mem_center_iff.mp hw z).symm
        calc z * z * (w * w) = z * (z * w) * w := by group
          _ = z * (w * z) * w := by rw [h1]
          _ = z * w * (z * w) := by group
      one_mem' := ⟨1, one_mem _, (one_mul 1).symm⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨z, hz, rfl⟩ := hx
        exact ⟨z⁻¹, inv_mem hz, (mul_inv_rev z z).symm ▸ rfl⟩ }
  have hNsq : ∀ z ∈ center Q, z * z ∈ N := fun z hz => ⟨z, hz, rfl⟩
  have hNle : N ≤ center Q := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem hz hz
  have hNn : N.Normal := Subgroup.normal_of_le_center hNle
  have hE0 : Subgroup.closure (Set.range ee) = ⊤ := by
    set E0 := Subgroup.closure (Set.range ee) with hE0def
    have hmap : E0.map q = ⊤ := by
      rw [hE0def, MonoidHom.map_closure, ← Set.range_comp]
      have : (q ∘ ee) = g := hqee
      rw [this]
      exact hgen
    have hsplit : ∀ x : Q, ∃ y ∈ E0, ∃ z ∈ center Q, x = y * z := fun x => by
      have : q x ∈ E0.map q := by rw [hmap]; trivial
      obtain ⟨y, hy, hyx⟩ := this
      refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hcom : commutator Q ≤ E0 := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨x1, hx1, z1, hz1, rfl⟩ := hsplit x
      obtain ⟨y1, hy1, z2, hz2, rfl⟩ := hsplit y
      rw [commutator_mul_center hz1 hz2, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx1 hy1) (inv_mem hx1)) (inv_mem hy1)
    exact eq_top_iff.2 ((Group.isPerfect_def.1 hQ) ▸ hcom)
  let ē : Fin m → Q ⧸ N := fun i => (ee i : Q ⧸ N)
  have hlift : FreeGroup.lift ē = (QuotientGroup.mk' N).comp (FreeGroup.lift ee) :=
    FreeGroup.ext_hom _ _ fun i => by simp [ē]
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (cover₂Words R cw).map FreeGroup.mk},
      FreeGroup.lift ē r = 1 := by
    intro r hr
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hr
    rw [hlift, MonoidHom.comp_apply]
    rw [mem_cover₂Words] at hwm
    simp only [coverWords, squareWords, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at hwm
    rcases hwm with (⟨i, r', hr', rfl⟩ | ⟨i, rfl⟩) | ⟨r', hr', rfl⟩
    · rw [mk_commWord, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
        map_commutatorElement, FreeGroup.lift_apply_of]
      have hc := mem_center_iff.mp (hrc r' hr') (ee i)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hc, map_one]
    · rw [show FreeGroup.mk ((i, false) :: cw i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) from
        rfl, map_mul, map_inv, FreeGroup.lift_apply_of, hfix i, inv_mul_cancel, map_one]
    · rw [← FreeGroup.mul_mk, map_mul]
      exact (QuotientGroup.eq_one_iff _).2 (hNsq _ (hrc r' hr'))
  let ψ : PG m (cover₂Words R cw) →* Q ⧸ N := PresentedGroup.toGroup (f := ē) hrel
  have hψs : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y ∈ Subgroup.closure (Set.range ee) := by rw [hE0]; trivial
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩
    | one => exact ⟨1, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨p', hp'⟩ := hy
      exact ⟨p * p', by rw [map_mul, hp, hp']; rfl⟩
    | inv x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨p⁻¹, by rw [map_inv, hp]; rfl⟩
  have hNker : N ≤ q.ker := hker ▸ hNle
  let qb : Q ⧸ N →* X := QuotientGroup.lift N q hNker
  have hqbs : Function.Surjective qb := fun x => by
    obtain ⟨y, rfl⟩ := hqs x
    exact ⟨(y : Q ⧸ N), rfl⟩
  have hle : Nat.card (Q ⧸ N) ≤ Nat.card X :=
    (Nat.card_le_card_of_surjective ψ hψs).trans hcard
  have hbij : Function.Bijective qb := hqbs.bijective_of_nat_card_le hle
  have hZN : ∀ z ∈ center Q, z ∈ N := fun z hz => by
    have h1 : qb (z : Q ⧸ N) = qb 1 := by
      rw [map_one]
      change q z = 1
      rw [← MonoidHom.mem_ker, hker]
      exact hz
    exact (QuotientGroup.eq_one_iff z).1 (hbij.1 h1)
  refine center_eq_bot_of_sq hZ fun z hz => ?_
  obtain ⟨b, hb, hbz⟩ := hZN z hz
  exact ⟨b, hb, hbz.symm⟩

end CFSG.Sporadic.Recognition.CoverRecipe

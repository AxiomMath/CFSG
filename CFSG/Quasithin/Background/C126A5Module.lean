module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.C126A5Delta
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.C126.A5

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.Quasithin

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

@[expose] def vec (β : ↥(commV L) ≃* Multiplicative (evenWeight 5)) (u : ↥(commV L)) :
    Fin 5 → ZMod 2 := ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)

theorem mem_commV_gen {x : MulAut W} (hx : x ∈ L) (v : W) : x v * v⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem act_mem_commV {h : MulAut W} (hh : h ∈ L) {u : W} (hu : u ∈ commV L) :
    h u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem hh hu

variable (θ : ↥L ≃* Perm (Fin 5)) (β : ↥(commV L) ≃* Multiplicative (evenWeight 5))
  (hβ : ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L) (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut W) (u : W), hu⟩) : evenWeight 5) :
        Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))

include hβ in
theorem vec_act (h : ↥L) (u : ↥(commV L)) :
    vec β ⟨(h : MulAut W) (u : W), act_mem_commV h.2 u.2⟩ = permAct (θ h) (vec β u) := by
  funext i
  exact hβ h u (act_mem_commV h.2 u.2) i

theorem vec_mem_delta5 (u : ↥(commV L)) : vec β u ∈ delta5 := by
  rw [mem_delta5]
  exact (Multiplicative.toAdd (β u) : evenWeight 5).2

theorem vec_injective : Function.Injective (vec β) := by
  intro u v h
  apply β.injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact h

theorem vec_mul (u v : ↥(commV L)) : vec β (u * v) = vec β u + vec β v := by
  unfold vec
  simp

theorem vec_surj {y : Fin 5 → ZMod 2} (hy : y ∈ delta5) : ∃ u, vec β u = y := by
  rw [mem_delta5] at hy
  refine ⟨β.symm (Multiplicative.ofAdd ⟨y, by simpa [evenWeight] using hy⟩), ?_⟩
  simp [vec]

theorem vec_one : vec β (1 : ↥(commV L)) = 0 := by
  unfold vec
  simp

theorem vec_eq_zero {u : ↥(commV L)} (h : vec β u = 0) : u = 1 :=
  vec_injective β (h.trans (vec_one β).symm)

@[expose] def CoversAlt (F : Subgroup (MulAut W)) : Prop :=
  ∀ g ∈ alts, ∃ h : ↥L, (h : MulAut W) ∈ F ∧ θ h = g

include hβ in
theorem irred_commV {F : Subgroup (MulAut W)} (hF : CoversAlt θ F) {U : Subgroup W}
    (hU : U ≤ commV L) (hinv : ∀ h ∈ F, ∀ u ∈ U, h u ∈ U) : U = ⊥ ∨ U = commV L := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hU
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  set x := vec β ⟨(u : W), hU u.2⟩ with hx
  have hx0 : x ≠ 0 := fun h => hu1 (Subtype.ext (by
    have := congrArg Subtype.val (vec_eq_zero β h)
    simpa using this))
  have key : ∀ c ∈ orb x, ∃ z : ↥(commV L), (z : W) ∈ U ∧ vec β z = c := by
    intro c hc
    rcases mem_orb.1 hc with rfl | ⟨g, hg, rfl⟩
    · exact ⟨1, U.one_mem, vec_one β⟩
    · obtain ⟨h, hhF, hθ⟩ := hF g hg
      refine ⟨⟨(h : MulAut W) (u : W), act_mem_commV h.2 (hU u.2)⟩, hinv _ hhF _ u.2, ?_⟩
      rw [vec_act θ β hβ h ⟨(u : W), hU u.2⟩, hθ]
  intro w hw
  obtain ⟨a, ha, b, hb, hab⟩ := ev5_irred x (vec_mem_delta5 β _) hx0
    (vec β ⟨w, hw⟩) (vec_mem_delta5 β _)
  obtain ⟨za, hza, rfl⟩ := key a ha
  obtain ⟨zb, hzb, rfl⟩ := key b hb
  have : (⟨w, hw⟩ : ↥(commV L)) = za * zb := vec_injective β (by rw [hab, vec_mul])
  have h2 := congrArg Subtype.val this
  simp only at h2
  rw [h2]
  exact U.mul_mem hza hzb

include hβ in
theorem fix_commV {F : Subgroup (MulAut W)} (hF : CoversAlt θ F) {u : W}
    (hu : u ∈ commV L) (hfix : ∀ h ∈ F, h u = u) : u = 1 := by
  have hx : vec β ⟨u, hu⟩ = 0 := by
    apply ev5_fix _ (vec_mem_delta5 β _)
    intro g hg
    obtain ⟨h, hhF, hθ⟩ := hF g hg
    rw [← hθ, ← vec_act θ β hβ h ⟨u, hu⟩]
    congr 1
    exact Subtype.ext (hfix _ hhF)
  exact congrArg Subtype.val (vec_eq_zero β hx)

theorem neg_vec (x : Fin 5 → ZMod 2) : -x = x := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

include hβ in
theorem four_commutators [Finite W] (π : Perm (Fin 5)) {h : ↥L} (hθ : θ h = cyc3 π) :
    4 ≤ (Set.range fun w : ↥(commV L) => ((h : MulAut W) (w : W)) * (w : W)⁻¹).ncard := by
  let Ψ : ↥(commV L) → ↥(commV L) := fun w =>
    ⟨(h : MulAut W) (w : W) * (w : W)⁻¹,
      (commV L).mul_mem (act_mem_commV h.2 w.2) ((commV L).inv_mem w.2)⟩
  have hvec : ∀ w, vec β (Ψ w) = permAct (cyc3 π) (vec β w) + vec β w := by
    intro w
    have h1 : Ψ w = ⟨(h : MulAut W) (w : W), act_mem_commV h.2 w.2⟩ * w⁻¹ := rfl
    have h2 : vec β w⁻¹ = vec β w := by
      have := vec_mul β w w⁻¹
      rw [mul_inv_cancel, vec_one] at this
      have h3 : vec β w⁻¹ = -vec β w := eq_neg_of_add_eq_zero_right this.symm
      rw [h3, neg_vec]
    rw [h1, vec_mul, vec_act θ β hβ h w, hθ, h2]
  have hrange : Set.range (fun w : ↥(commV L) => ((h : MulAut W) (w : W)) * (w : W)⁻¹) =
      Subtype.val '' Set.range Ψ := by
    ext y; constructor
    · rintro ⟨w, rfl⟩; exact ⟨Ψ w, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩
  rw [hrange, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hsub : ((delta5.image fun v => permAct (cyc3 π) v + v : Finset _) : Set (Fin 5 → ZMod 2)) ⊆
      vec β '' Set.range Ψ := by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨w, hw⟩ := vec_surj β hv
    exact ⟨Ψ w, ⟨w, rfl⟩, by rw [hvec, hw]⟩
  calc 4 ≤ (delta5.image fun v => permAct (cyc3 π) v + v).card := ev5_four π
    _ = ((delta5.image fun v => permAct (cyc3 π) v + v : Finset _) : Set (Fin 5 → ZMod 2)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (vec β '' Set.range Ψ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range Ψ).ncard := Set.ncard_image_le (Set.toFinite _)

end CFSG.Quasithin.C126.A5

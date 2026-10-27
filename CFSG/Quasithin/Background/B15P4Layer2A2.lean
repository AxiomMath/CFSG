module

public import CFSG.Quasithin.Background.B15P4Layer2Moved
public import CFSG.Quasithin.Background.B15P4Repl2

public section

namespace CFSG.Quasithin.B15P4

variable {V : Type*} [CommGroup V]

theorem fixV_inf_eq_sup [Finite V] {X A B₁ B₂ : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (h₁ : B₁ ≤ A) (h₂ : B₂ ≤ A) (e₁ : wt B₁ = wt A) (e₂ : wt B₂ = wt A) :
    fixV (B₁ ⊓ B₂) = fixV B₁ ⊔ fixV B₂ := by
  have hc := hA.2.2.1.1
  have e3 : fixV B₁ ⊔ fixV B₂ ≤ fixV (B₁ ⊓ B₂) :=
    sup_le (B1.fixV_le_fixV inf_le_left) (B1.fixV_le_fixV inf_le_right)
  by_contra hne
  have hlt : Nat.card ↥(fixV B₁ ⊔ fixV B₂) < Nat.card ↥(fixV (B₁ ⊓ B₂)) :=
    lt_of_le_of_ne (Subgroup.card_le_of_le e3)
      fun h => hne (Subgroup.eq_of_le_of_card_ge e3 h.ge).symm
  have e1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₂
    (fun x hx y hy => hc x (h₁ hx) y (h₂ hy))).1
  have e2 := card_sup_mul_card_inf (fixV B₁) (fixV B₂)
  rw [← fixV_sup] at e2
  have hpos : 0 < Nat.card ↥(fixV (B₁ ⊔ B₂)) := Nat.card_pos
  have hpos' : 0 < Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hstrict : wt B₁ * wt B₂ < wt (B₁ ⊓ B₂) * wt (B₁ ⊔ B₂) := by
    unfold wt
    calc Nat.card B₁ * Nat.card (fixV B₁) * (Nat.card B₂ * Nat.card (fixV B₂))
        = (Nat.card B₁ * Nat.card B₂) * (Nat.card (fixV B₁) * Nat.card (fixV B₂)) := by ring
      _ = (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂)) *
          (Nat.card ↥(fixV B₁ ⊔ fixV B₂) * Nat.card ↥(fixV (B₁ ⊔ B₂))) := by rw [e1, e2]
      _ < (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂)) *
          (Nat.card ↥(fixV (B₁ ⊓ B₂)) * Nat.card ↥(fixV (B₁ ⊔ B₂))) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hlt hpos) hpos'
      _ = Nat.card ↥(B₁ ⊓ B₂) * Nat.card ↥(fixV (B₁ ⊓ B₂)) *
          (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(fixV (B₁ ⊔ B₂))) := by ring
  have hle1 : wt (B₁ ⊓ B₂) ≤ wt A := wt_le_of_isFFStarOffender hA (inf_le_left.trans h₁)
  have hle2 : wt (B₁ ⊔ B₂) ≤ wt A := wt_le_of_isFFStarOffender hA (sup_le h₁ h₂)
  rw [e₁, e₂] at hstrict
  exact absurd hstrict (not_lt.2 (Nat.mul_le_mul hle1 hle2))

theorem fixV_Bv_le [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (v : V) :
    fixV (B1.Bv A v) ≤ commV A ⊔ fixV A := by
  intro w hw
  obtain ⟨a, ha, u, hu, rfl⟩ := exists_cv_mul_of_mem_fixV_Bv hA v hw
  rw [cv_eq]
  exact Subgroup.mul_mem_sup (G6.mem_commV_of_mem ha v) hu

theorem fixV_inf_Bv_finset_le [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (S : Finset V) : fixV (A ⊓ ⨅ v ∈ S, B1.Bv A v) ≤ commV A ⊔ fixV A := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hvS ih =>
    have hset : A ⊓ ⨅ w ∈ insert v S, B1.Bv A w = (A ⊓ ⨅ w ∈ S, B1.Bv A w) ⊓ B1.Bv A v := by
      rw [Finset.iInf_insert]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hset, fixV_inf_eq_sup hA inf_le_left (B1.Bv_le A v) (wt_inf_Bv_finset hA S)
      (wt_Bv hA v)]
    exact sup_le ih (fixV_Bv_le hA v)

theorem top_le_commV_sup_fixV [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (h : A2sub A = ⊥) : (⊤ : Subgroup V) ≤ commV A ⊔ fixV A := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have h1 := fixV_inf_Bv_finset_le hA Finset.univ
  have h2 : A ⊓ ⨅ v ∈ (Finset.univ : Finset V), B1.Bv A v = ⊥ := by
    have h3 : A2sub A = A ⊓ ⨅ v : V, B1.Bv A v := rfl
    rw [← h]
    simp [h3]
  rw [h2, B1.fixV_bot] at h1
  exact h1

section Nilpotent

open CFSG.Quasithin

theorem map_subtype_commV_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    (commV (autSub A U)).map U.subtype = commSub U A := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨φ, hφ, u, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    exact Subgroup.subset_closure ⟨g, hg, u, u.2, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact ⟨resHom U ⟨g, hA hg⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹,
      G6.mem_commV_of_mem (mem_autSub.2 ⟨⟨g, hA hg⟩, hg, rfl⟩) _, rfl⟩

theorem commSub_ne_self [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWne : W ≠ ⊥) : commSub W A ≠ W := by
  intro heq
  have hstab : A ≤ stabSub W := by
    intro a ha
    rw [mem_stabSub]
    intro u
    refine ⟨fun hu => ?_, fun hu => hW a ha u hu⟩
    have := hW a⁻¹ (A.inv_mem ha) _ hu
    simpa using this
  have hVW : ∀ u : ↥W, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u.1)
  have hnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hWne
  have hN : commV (⊥ : Subgroup (MulAut ↥W)) ≠ ⊤ := by
    have h0 : commV (⊥ : Subgroup (MulAut ↥W)) = ⊥ := by
      rw [commV, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨x, hx, v, rfl⟩
      rw [Subgroup.mem_bot] at hx
      simp [hx]
    rw [h0]
    exact bot_ne_top
  have key := G6.commV_ne_top_of_two_power (V := ↥W) hVW (K := autSub A W) (N := ⊥)
    (fun k _ n hn => by
      rw [Subgroup.mem_bot] at hn ⊢
      simp [hn])
    (fun k hk => by
      obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
      refine ⟨1, ?_⟩
      rw [Subgroup.mem_bot, pow_one, pow_two, ← map_mul]
      have : g * g = 1 := Subtype.ext (by simpa [pow_two] using hA2 _ hg)
      rw [this, map_one])
    hN
  apply key
  apply Subgroup.map_injective W.subtype_injective
  rw [map_subtype_commV_autSub hstab, heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Nilpotent

theorem A2sub_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : A2sub A ≠ ⊥ := by
  intro hbot
  have hc := hA.2.2.1.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have e1 : commV A ⊔ fixV A = ⊤ := top_le_iff.1 (top_le_commV_sup_fixV hA hbot)
  have e2 : commSub (commV A) A = commSub ⊤ A := by
    rw [← e1, commSub_sup_fixV le_rfl]
  have hcomm : commSub (commV A) A = commV A := by rw [e2, ← commV_eq_commSub]
  by_cases hU : commV A = ⊥
  · apply hA.2.1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    apply MulEquiv.ext
    intro v
    have : a v * v⁻¹ ∈ commV A := G6.mem_commV_of_mem ha v
    rw [hU, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · refine commSub_ne_self hV hA2 (fun a ha w hw => ?_) hU hcomm
    refine G6.apply_mem_commV (k := a) (fun x hx => ?_) hw
    rw [hc a ha x hx, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

theorem inf_centSub_commV_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : A ⊓ centSub (commV A) ≠ ⊥ := by
  rw [← A2sub_eq_inf_centSub hA.2.2.1.1]
  exact A2sub_ne_bot hV hA

end CFSG.Quasithin.B15P4

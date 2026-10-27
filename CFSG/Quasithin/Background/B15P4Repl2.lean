module

import all CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B15P4Repl

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem B1.cv_eq_apply_mul_inv (v : V) (a : MulAut V) : B1.cv v a = a v * v⁻¹ := by
  unfold B1.cv
  rfl

theorem Bv_ne_bot_of_offender [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (v : V) : B1.Bv A v ≠ ⊥ := by
  by_cases hv : v ∈ fixV A
  · rw [B1.Bv_eq_of_mem_fixV hv]
    exact hA.2.1
  · exact B1.Bv_ne_bot hV hA hv

theorem card_mul_card_fixV_Bv [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (v : V) : Nat.card (B1.Bv A v) * Nat.card (fixV (B1.Bv A v)) =
      Nat.card A * Nat.card (fixV A) := by
  rw [← card_fixV_Bv hA v]
  calc Nat.card (B1.Bv A v) * ((B1.Bv A v).relIndex A * Nat.card (fixV A))
      = ((B1.Bv A v).relIndex A * Nat.card (B1.Bv A v)) * Nat.card (fixV A) := by ring
    _ = Nat.card A * Nat.card (fixV A) := by rw [B1.relIndex_mul_card_Bv A v]

theorem ffLe_Bv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (v : V) : FFLe X (B1.Bv A v) A :=
  ⟨hA.isA2.mono (B1.Bv_le A v) (Bv_ne_bot_of_offender hV hA v), hA.isA2, B1.Bv_le A v,
    card_mul_card_fixV_Bv hA v⟩

theorem isFFStarOffender_Bv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (v : V) : IsFFStarOffender X (B1.Bv A v) :=
  B1_4_2 hA (ffLe_Bv hV hA v)

theorem exists_cv_mul_of_mem_fixV_Bv [Finite V] {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (v : V) {w : V} (hw : w ∈ fixV (B1.Bv A v)) :
    ∃ a ∈ A, ∃ u ∈ fixV A, w = B1.cv v a * u := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have hbij : Function.Bijective (B1.Fmap hc v) := by
    refine Function.Injective.bijective_of_nat_card_le (B1.Fmap_injective hc v) ?_
    rw [B1.card_Fmap_domain v, card_fixV_Bv hA v]
  obtain ⟨⟨q, u⟩, hqu⟩ := hbij.2 ⟨w, hw⟩
  have h1 : B1.cv v ((Quotient.out q : ↥A) : MulAut V) * (u : V) = w := congrArg Subtype.val hqu
  exact ⟨((Quotient.out q : ↥A) : MulAut V), (Quotient.out q : ↥A).2, u, u.2, h1.symm⟩

theorem Bv_eq_self_iff {A : Subgroup (MulAut V)} (v : V) :
    B1.Bv A v = A ↔ ∀ a ∈ A, B1.cv v a ∈ fixV A := by
  constructor
  · intro h a ha
    have : a ∈ B1.Bv A v := by rw [h]; exact ha
    exact (B1.mem_Bv.1 this).2
  · intro h
    exact le_antisymm (B1.Bv_le A v) fun a ha => B1.mem_Bv.2 ⟨ha, h a ha⟩

theorem isQuadratic_iff_forall_Bv_eq {A : Subgroup (MulAut V)} :
    IsQuadratic A ↔ ∀ v : V, B1.Bv A v = A := by
  constructor
  · intro h v
    refine (Bv_eq_self_iff v).2 fun a ha => ?_
    rw [B1.cv_eq_apply_mul_inv]
    exact h (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
  · intro h
    unfold IsQuadratic commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have := (Bv_eq_self_iff v).1 (h v) x hx
    rwa [B1.cv_eq_apply_mul_inv] at this

theorem Bv_lt_of_not_forall {A : Subgroup (MulAut V)} {v : V}
    (hv : ¬ ∀ a ∈ A, B1.cv v a ∈ fixV A) : B1.Bv A v < A :=
  lt_of_le_of_ne (B1.Bv_le A v) fun h => hv ((Bv_eq_self_iff v).1 h)

theorem Bv_le_of_forall_offender_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A N : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hN : ∀ B : Subgroup (MulAut V), B < A → IsFFStarOffender X B → B ≤ N) {v : V}
    (hv : ¬ ∀ a ∈ A, B1.cv v a ∈ fixV A) : B1.Bv A v ≤ N :=
  hN _ (Bv_lt_of_not_forall hv) (isFFStarOffender_Bv hV hA v)

theorem exists_Bv_le_of_not_quadratic [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A N : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (hq : ¬ IsQuadratic A)
    (hN : ∀ B : Subgroup (MulAut V), B < A → IsFFStarOffender X B → B ≤ N) :
    ∃ v : V, B1.Bv A v < A ∧ B1.Bv A v ≤ N ∧ FFLe X (B1.Bv A v) A ∧
      Nat.card (fixV (B1.Bv A v)) = (B1.Bv A v).relIndex A * Nat.card (fixV A) := by
  have : ∃ v : V, B1.Bv A v ≠ A := by
    by_contra hcon
    push Not at hcon
    exact hq (isQuadratic_iff_forall_Bv_eq.2 hcon)
  obtain ⟨v, hv⟩ := this
  have hlt : B1.Bv A v < A := lt_of_le_of_ne (B1.Bv_le A v) hv
  exact ⟨v, hlt, hN _ hlt (isFFStarOffender_Bv hV hA v), ffLe_Bv hV hA v,
    (card_fixV_Bv hA v).symm⟩

theorem card_fixV_lt_of_isFFStarMin [Finite V] {X F B : Subgroup (MulAut V)}
    (hF : IsFFStarMin X F) (hBF : B < F) (hB : B ≠ ⊥) :
    Nat.card (fixV B) < B.relIndex F * Nat.card (fixV F) := by
  have hle := hF.1.card_le hBF.le
  have h2 : B.relIndex F * Nat.card B = Nat.card F := by
    have := Subgroup.relIndex_mul_card B F
    rwa [inf_eq_left.2 hBF.le] at this
  by_contra hcon
  push Not at hcon
  have heq : Nat.card B * Nat.card (fixV B) = Nat.card F * Nat.card (fixV F) := by
    refine le_antisymm hle ?_
    calc Nat.card F * Nat.card (fixV F)
        = (B.relIndex F * Nat.card B) * Nat.card (fixV F) := by rw [h2]
      _ = Nat.card B * (B.relIndex F * Nat.card (fixV F)) := by ring
      _ ≤ Nat.card B * Nat.card (fixV B) := Nat.mul_le_mul_left _ hcon
  have hFF : FFLe X B F := ⟨hF.1.isA2.mono hBF.le hB, hF.1.isA2, hBF.le, heq⟩
  exact hBF.ne (hF.2 B (B1_4_2 hF.1 hFF) hFF)

theorem fixV_eq_of_isFFStarMin_of_relIndex_eq_two [Finite V] {X F B : Subgroup (MulAut V)}
    (hF : IsFFStarMin X F) (hBF : B ≤ F) (hB : B ≠ ⊥) (h2 : B.relIndex F = 2) :
    fixV B = fixV F := by
  have hlt : B < F := lt_of_le_of_ne hBF fun h => by
    rw [h, Subgroup.relIndex_self] at h2
    omega
  have h1 := card_fixV_lt_of_isFFStarMin hF hlt hB
  rw [h2] at h1
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (B1.fixV_le_fixV hBF)
  have hpos : 0 < Nat.card (fixV F) := Nat.card_pos
  have hm2 : m < 2 := by
    rw [hm, mul_comm 2] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  have hle : Nat.card (fixV B) ≤ Nat.card (fixV F) := by
    interval_cases m
    · have : 0 < Nat.card (fixV B) := Nat.card_pos
      omega
    · omega
  exact (Subgroup.eq_of_le_of_card_ge (B1.fixV_le_fixV hBF) hle).symm

theorem fixV_eq_of_isFFStarMin_of_card_eq_two_mul [Finite V] {X F B : Subgroup (MulAut V)}
    (hF : IsFFStarMin X F) (hBF : B ≤ F) (hB : B ≠ ⊥) (h2 : Nat.card F = 2 * Nat.card B) :
    fixV B = fixV F := by
  refine fixV_eq_of_isFFStarMin_of_relIndex_eq_two hF hBF hB ?_
  have h3 : B.relIndex F * Nat.card B = Nat.card F := by
    have := Subgroup.relIndex_mul_card B F
    rwa [inf_eq_left.2 hBF] at this
  have hpos : 0 < Nat.card B := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h3, h2]

theorem card_fixV_eq_relIndex_mul_of_ffLe [Finite V] {X A F : Subgroup (MulAut V)}
    (hFA : FFLe X F A) :
    Nat.card (fixV F) = F.relIndex A * Nat.card (fixV A) := by
  obtain ⟨-, -, hle, heq⟩ := hFA
  have h2 : F.relIndex A * Nat.card F = Nat.card A := by
    have := Subgroup.relIndex_mul_card F A
    rwa [inf_eq_left.2 hle] at this
  have hpos : 0 < Nat.card F := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card F * Nat.card (fixV F) = Nat.card A * Nat.card (fixV A) := heq
    _ = (F.relIndex A * Nat.card F) * Nat.card (fixV A) := by rw [h2]
    _ = Nat.card F * (F.relIndex A * Nat.card (fixV A)) := by ring

theorem relIndex_fixV_eq_of_ffLe [Finite V] {X A F : Subgroup (MulAut V)} (hFA : FFLe X F A) :
    (fixV A).relIndex (fixV F) = F.relIndex A := by
  have h1 : (fixV A).relIndex (fixV F) * Nat.card (fixV A) = Nat.card (fixV F) := by
    have := Subgroup.relIndex_mul_card (fixV A) (fixV F)
    rwa [inf_eq_left.2 (B1.fixV_le_fixV hFA.2.2.1)] at this
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, card_fixV_eq_relIndex_mul_of_ffLe hFA]

theorem fixV_lt_of_ffLe_of_lt [Finite V] {X A F : Subgroup (MulAut V)} (hFA : FFLe X F A)
    (hlt : F < A) : fixV A < fixV F := by
  refine lt_of_le_of_ne (B1.fixV_le_fixV hFA.2.2.1) fun h => ?_
  have h1 := card_fixV_eq_relIndex_mul_of_ffLe hFA
  rw [← h] at h1
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have h2 : F.relIndex A = 1 := by
    have : F.relIndex A * Nat.card (fixV A) = 1 * Nat.card (fixV A) := by rw [← h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  exact hlt.not_ge (Subgroup.relIndex_eq_one.1 h2)

theorem mem_of_forall_fixV_of_ffLe [Finite V] {X A F : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hFA : FFLe X F A) {x : MulAut V} (hx : x ∈ A)
    (hfix : ∀ u ∈ fixV F, x u = u) : x ∈ F := by
  set D : Subgroup (MulAut V) := F ⊔ Subgroup.zpowers x with hD
  have hDA : D ≤ A := sup_le hFA.2.2.1 (Subgroup.zpowers_le.2 hx)
  have hfixD : fixV D = fixV F := by
    refine le_antisymm (B1.fixV_le_fixV le_sup_left) fun u hu d hd => ?_
    have hxs : x ∈ MulAction.stabilizer (MulAut V) u := by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix u hu
    have hs : D ≤ MulAction.stabilizer (MulAut V) u := sup_le
      (fun a ha => by rw [MulAction.mem_stabilizer_iff]; exact hu a ha)
      (Subgroup.zpowers_le.2 hxs)
    have := hs hd
    rw [MulAction.mem_stabilizer_iff] at this
    exact this
  have h1 := hA.card_le hDA
  rw [hfixD, ← hFA.2.2.2] at h1
  have hpos : 0 < Nat.card (fixV F) := Nat.card_pos
  have h2 : Nat.card D ≤ Nat.card F := Nat.le_of_mul_le_mul_right h1 hpos
  have h3 : F = D := Subgroup.eq_of_le_of_card_ge le_sup_left h2
  rw [h3]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem inf_centSub_fixV_eq_of_ffLe [Finite V] {X A F : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hFA : FFLe X F A) : A ⊓ centSub (fixV F) = F :=
  le_antisymm
    (fun _ hx => mem_of_forall_fixV_of_ffLe hA hFA hx.1 (mem_centSub.1 hx.2))
    fun f hf => ⟨hFA.2.2.1 hf, mem_centSub.2 fun _ hu => hu f hf⟩

theorem relIndex_mul_card_fixV_le [Finite V] {X A F D : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hFA : FFLe X F A) (hFD : F ≤ D) (hDA : D ≤ A) :
    F.relIndex D * Nat.card (fixV D) ≤ Nat.card (fixV F) := by
  have h1 := hA.card_le hDA
  rw [← hFA.2.2.2] at h1
  have h2 : F.relIndex D * Nat.card F = Nat.card D := by
    have := Subgroup.relIndex_mul_card F D
    rwa [inf_eq_left.2 hFD] at this
  have hpos : 0 < Nat.card F := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card F * (F.relIndex D * Nat.card (fixV D))
      = (F.relIndex D * Nat.card F) * Nat.card (fixV D) := by ring
    _ = Nat.card D * Nat.card (fixV D) := by rw [h2]
    _ ≤ Nat.card F * Nat.card (fixV F) := h1

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace B1

theorem card_inf_fixV_aux [Finite V] {X A B : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hBA : B ≤ A) (W : Subgroup V) :
    Nat.card B * Nat.card ↥(W ⊓ fixV B) ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) ∧
      (Nat.card B * Nat.card ↥(W ⊓ fixV B) = Nat.card A * Nat.card ↥(W ⊓ fixV A) →
        Nat.card B * Nat.card (fixV B) = Nat.card A * Nat.card (fixV A) ∧
          (W ⊓ fixV B) ⊔ fixV A = fixV B) := by
  have hCle : fixV A ≤ fixV B := fixV_le_fixV hBA
  have hS : (W ⊓ fixV B) ⊔ fixV A ≤ fixV B := sup_le inf_le_right hCle
  have hinf : (W ⊓ fixV B) ⊓ fixV A = W ⊓ fixV A := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCle h.2⟩, h.2⟩⟩
  have hcard : Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card ↥(W ⊓ fixV B) * Nat.card (fixV A) := by
    have := card_sup_mul_card_inf (W ⊓ fixV B) (fixV A)
    rwa [hinf] at this
  have hSle : Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) ≤ Nat.card (fixV B) :=
    Subgroup.card_le_of_le hS
  have hstar := hA.card_le hBA
  have hCpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have hWApos : 0 < Nat.card ↥(W ⊓ fixV A) := Nat.card_pos
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hstep1 : Nat.card B * Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) ≤
      Nat.card B * Nat.card (fixV B) * Nat.card ↥(W ⊓ fixV A) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hSle)
  have hstep2 : Nat.card B * Nat.card (fixV B) * Nat.card ↥(W ⊓ fixV A) ≤
      Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) :=
    Nat.mul_le_mul_right _ hstar
  have hlhs : Nat.card B * Nat.card ↥(W ⊓ fixV B) * Nat.card (fixV A) =
      Nat.card B * Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) := by
    calc Nat.card B * Nat.card ↥(W ⊓ fixV B) * Nat.card (fixV A)
        = Nat.card B * (Nat.card ↥(W ⊓ fixV B) * Nat.card (fixV A)) := by ring
      _ = Nat.card B * (Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A)) := by
          rw [hcard]
      _ = _ := by ring
  have hrhs : Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card A * Nat.card ↥(W ⊓ fixV A) * Nat.card (fixV A) := by ring
  have hmain : Nat.card B * Nat.card ↥(W ⊓ fixV B) * Nat.card (fixV A) ≤
      Nat.card A * Nat.card ↥(W ⊓ fixV A) * Nat.card (fixV A) := by
    rw [hlhs, ← hrhs]
    exact hstep1.trans hstep2
  refine ⟨Nat.le_of_mul_le_mul_right hmain hCpos, fun heq => ?_⟩
  have h1 : Nat.card B * Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) := by
    rw [← hlhs, heq, hrhs]
  have h2 : Nat.card B * Nat.card (fixV B) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) := le_antisymm hstep2 (h1 ▸ hstep1)
  have h3 : Nat.card B * Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card B * Nat.card (fixV B) * Nat.card ↥(W ⊓ fixV A) := by rw [h1, h2]
  refine ⟨Nat.eq_of_mul_eq_mul_right hWApos h2, ?_⟩
  have h4 : Nat.card B * Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) =
      Nat.card B * Nat.card (fixV B) := Nat.eq_of_mul_eq_mul_right hWApos h3
  have h5 : Nat.card ↥((W ⊓ fixV B) ⊔ fixV A) = Nat.card (fixV B) :=
    Nat.eq_of_mul_eq_mul_left hBpos h4
  exact Subgroup.eq_of_le_of_card_ge hS h5.ge

theorem card_inf_fixV_le [Finite V] {X A B : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hBA : B ≤ A) (W : Subgroup V) :
    Nat.card B * Nat.card ↥(W ⊓ fixV B) ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) :=
  (card_inf_fixV_aux hA hBA W).1

theorem card_inf_fixV_eq [Finite V] {X A B : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hBA : B ≤ A) (W : Subgroup V)
    (heq : Nat.card B * Nat.card ↥(W ⊓ fixV B) = Nat.card A * Nat.card ↥(W ⊓ fixV A)) :
    Nat.card B * Nat.card (fixV B) = Nat.card A * Nat.card (fixV A) ∧
      (W ⊓ fixV B) ⊔ fixV A = fixV B :=
  (card_inf_fixV_aux hA hBA W).2 heq

theorem le_stabSub_of_invariant {A : Subgroup (MulAut V)} {W : Subgroup V}
    (h : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) : A ≤ stabSub W := by
  intro a ha u
  constructor
  · intro hu
    have := h a⁻¹ (A.inv_mem ha) (a u) hu
    simpa using this
  · exact fun hu => h a ha u hu

theorem sq_eq_one_sub (hV : ∀ v : V, v ^ 2 = 1) (W : Subgroup V) : ∀ w : W, w ^ 2 = 1 :=
  fun w => Subtype.ext (by simpa using hV w)

theorem autSub_bot (W : Subgroup V) : autSub (⊥ : Subgroup (MulAut V)) W = ⊥ := by
  unfold autSub
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem autSub_eq_bot_iff {A : Subgroup (MulAut V)} {W : Subgroup V} (hA : A ≤ stabSub W) :
    autSub A W = ⊥ ↔ W ≤ fixV A := by
  constructor
  · intro h u hu g hg
    have hmem : resHom W ⟨g, hA hg⟩ ∈ autSub A W := mem_autSub.mpr ⟨⟨g, hA hg⟩, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg (fun φ : MulAut W => ((φ ⟨u, hu⟩ : W) : V)) hmem
  · intro h
    refine (Subgroup.eq_bot_iff_forall _).mpr fun φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    ext u
    exact h u.2 g hg

theorem isA2_autSub {X A : Subgroup (MulAut V)} {W : Subgroup V} (h : IsA2 X A)
    (hA : A ≤ stabSub W) (hW : ¬ W ≤ fixV A) : IsA2 (autSub X W) (autSub A W) := by
  refine ⟨autSub_mono h.1 W, fun hbot => hW ((autSub_eq_bot_iff hA).mp hbot), ?_, ?_⟩
  · intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨k, hk, rfl⟩ := mem_autSub.mp hψ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.2.2.1 _ hg _ hk)
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (by simpa using h.2.2.2 _ hg)
    rw [this, map_one]

def preB (A : Subgroup (MulAut V)) (W : Subgroup V) (D : Subgroup (MulAut W)) :
    Subgroup (MulAut V) :=
  ((D.comap (resHom W)).map (stabSub W).subtype) ⊓ A

theorem mem_preB {A : Subgroup (MulAut V)} {W : Subgroup V} {D : Subgroup (MulAut W)}
    {g : MulAut V} :
    g ∈ preB A W D ↔ g ∈ A ∧ ∃ h : g ∈ stabSub W, resHom W ⟨g, h⟩ ∈ D := by
  unfold preB
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hA⟩
    exact ⟨hA, x.2, hx⟩
  · rintro ⟨hA, h, hD⟩
    exact ⟨⟨⟨g, h⟩, hD, rfl⟩, hA⟩

theorem preB_le (A : Subgroup (MulAut V)) (W : Subgroup V) (D : Subgroup (MulAut W)) :
    preB A W D ≤ A := fun _ h => (mem_preB.1 h).1

theorem inf_centSub_le_preB {A : Subgroup (MulAut V)} {W : Subgroup V} (hA : A ≤ stabSub W)
    (D : Subgroup (MulAut W)) : A ⊓ centSub W ≤ preB A W D := by
  intro g hg
  refine mem_preB.2 ⟨hg.1, hA hg.1, ?_⟩
  have : resHom W ⟨g, hA hg.1⟩ = 1 := by
    ext u
    exact hg.2 u u.2
  rw [this]
  exact D.one_mem

theorem preB_le_stabSub {A : Subgroup (MulAut V)} {W : Subgroup V} (hA : A ≤ stabSub W)
    (D : Subgroup (MulAut W)) : preB A W D ≤ stabSub W :=
  (preB_le A W D).trans hA

theorem autSub_preB {A : Subgroup (MulAut V)} {W : Subgroup V}
    {D : Subgroup (MulAut W)} (hD : D ≤ autSub A W) : autSub (preB A W D) W = D := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨-, h, hD'⟩ := mem_preB.1 hg
    exact hD'
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp (hD hφ)
    exact mem_autSub.2 ⟨g, mem_preB.2 ⟨hg, g.2, hφ⟩, rfl⟩

theorem preB_autSub {A : Subgroup (MulAut V)} {W : Subgroup V} (hA : A ≤ stabSub W) :
    preB A W (autSub A W) = A := by
  refine le_antisymm (preB_le A W _) fun g hg => ?_
  exact mem_preB.2 ⟨hg, hA hg, mem_autSub.2 ⟨⟨g, hA hg⟩, hg, rfl⟩⟩

theorem preB_ne_bot {A : Subgroup (MulAut V)} {W : Subgroup V}
    {D : Subgroup (MulAut W)} (hD : D ≤ autSub A W) (hne : D ≠ ⊥) : preB A W D ≠ ⊥ := by
  intro h
  apply hne
  rw [← autSub_preB hD, h, autSub_bot]

theorem card_transfer [Finite V] {A : Subgroup (MulAut V)} {W : Subgroup V} (hA : A ≤ stabSub W)
    {D : Subgroup (MulAut W)} (hD : D ≤ autSub A W) :
    Nat.card D * Nat.card (fixV D) * Nat.card ↥(A ⊓ centSub W) =
      Nat.card (preB A W D) * Nat.card ↥(W ⊓ fixV (preB A W D)) := by
  have hB := preB_le_stabSub hA D
  have h1 := card_autSub_mul hB
  rw [autSub_preB hD] at h1
  have h2 : preB A W D ⊓ centSub W = A ⊓ centSub W := by
    exact le_antisymm (inf_le_inf_right _ (preB_le A W D))
      (le_inf (inf_centSub_le_preB hA D) inf_le_right)
  rw [h2] at h1
  have h3 : Nat.card (fixV D) = Nat.card ↥(W ⊓ fixV (preB A W D)) := by
    have := map_subtype_fixV_autSub hB
    rw [autSub_preB hD] at this
    rw [← this, Subgroup.card_map_of_injective W.subtype_injective]
  rw [h3, ← h1]
  ring

end B1

theorem B7_1_1 [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥) :
    IsFFStarOffender (autSub X W) (autSub A W) := by
  have hst : A ≤ stabSub W := B1.le_stabSub_of_invariant hW
  have hne : ¬ W ≤ fixV A := fun h => hWA (commSub_eq_bot_iff.2 h)
  refine isFFStarOffender_iff.2 ⟨B1.isA2_autSub hA.isA2 hst hne, fun D hD => ?_⟩
  have h1 := B1.card_transfer hst hD
  have h2 := B1.card_transfer hst (le_refl (autSub A W))
  rw [B1.preB_autSub hst] at h2
  have h3 := B1.card_inf_fixV_le hA (B1.preB_le A W D) W
  have hpos : 0 < Nat.card ↥(A ⊓ centSub W) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [h1, h2]
  exact h3


theorem B1.ffLe_trans {X A B C : Subgroup (MulAut V)} (hCB : FFLe X C B) (hBA : FFLe X B A) :
    FFLe X C A :=
  ⟨hCB.1, hBA.2.1, hCB.2.2.1.trans hBA.2.2.1, hCB.2.2.2.trans hBA.2.2.2⟩

theorem B1.exists_isFFStarMin_le [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    ∃ A₀, FFLe X A₀ A ∧ IsFFStarMin X A₀ := by
  let S : Set (Subgroup (MulAut V)) := {B | IsFFStarOffender X B ∧ FFLe X B A}
  have hSne : S.Nonempty := ⟨A, hA, hA.isA2, hA.isA2, le_rfl, rfl⟩
  obtain ⟨A₀, hA₀, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) hSne
  refine ⟨A₀, hA₀.2, hA₀.1, fun B hB hBA₀ => ?_⟩
  have hBA : FFLe X B A := B1.ffLe_trans hBA₀ hA₀.2
  exact Subgroup.eq_of_le_of_card_ge hBA₀.2.2.1 (hmin B ⟨hB, hBA⟩)

theorem rAV_eq_one_of_one_le_qOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hq : (1 : WithTop ℚ) ≤ qOf X) (hA : IsFFStarOffender X A) : rAV A = 1 := by
  obtain ⟨A₀, hle, hmin⟩ := B1.exists_isFFStarMin_le hA
  have hquad : IsQuadratic A₀ := B1_4_3 hV hmin
  have hq' : ((1 : ℚ) : WithTop ℚ) ≤ kq X 2 := by
    rw [WithTop.coe_one]
    exact hq
  have h1 : (1 : ℚ) ≤ rAV A₀ :=
    le_kq_iff.1 hq' A₀ hmin.1.isA2 ((isQuadratic_iff_commSeries_two A₀).1 hquad)
  have h2 : rAV A₀ = 1 := le_antisymm (B1_4_1 hV hmin.1) h1
  have h3 := (rAV_eq_one_iff hV hmin.1.isA2).1 h2
  exact (rAV_eq_one_iff hV hA.isA2).2 (h3.trans hle.2.2.2)

namespace B1

theorem fixV_inf_centSub {A : Subgroup (MulAut V)} (W : Subgroup V) :
    W ≤ fixV (A ⊓ centSub W) := fun _ hu _ hg => hg.2 _ hu

theorem rk_eq_rkIdx_of_rAV_eq_one [Finite V] {X A : Subgroup (MulAut V)} (hA : IsA2 X A)
    (h : rAV A = 1) : rk A = rkIdx (fixV A) := by
  have hr : (rk A : ℚ) ≠ 0 := by exact_mod_cast hA.rk_pos.ne'
  unfold rAV at h
  rw [div_eq_one_iff_eq hr] at h
  exact_mod_cast h.symm

theorem rAV_eq_one_of_rk_eq_rkIdx [Finite V] {X A : Subgroup (MulAut V)} (hA : IsA2 X A)
    (h : rk A = rkIdx (fixV A)) : rAV A = 1 := by
  have hr : (rk A : ℚ) ≠ 0 := by exact_mod_cast hA.rk_pos.ne'
  unfold rAV
  rw [div_eq_one_iff_eq hr]
  exact_mod_cast h.symm

end B1

theorem B7_1_3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hm : rk (autSub A W) = rkIdx (fixV (autSub A W))) :
    (A ⊓ centSub W = ⊥ ∧ W ⊔ fixV A = ⊤) ∨
      (IsFFStarOffender X (A ⊓ centSub W) ∧ FFLe X (A ⊓ centSub W) A) := by
  have hst : A ≤ stabSub W := B1.le_stabSub_of_invariant hW
  have hAut := B7_1_1 hA hW hWA
  have hW2 := B1.sq_eq_one_sub hV W
  have hcardW : Nat.card W = Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) :=
    (B1.card_eq_iff hW2 hAut.isA2.2.2).2 hm.symm
  have htr := B1.card_transfer hst (le_refl (autSub A W))
  rw [B1.preB_autSub hst] at htr
  have hfix : W ⊓ fixV (A ⊓ centSub W) = W := inf_eq_left.2 (B1.fixV_inf_centSub W)
  have heq : Nat.card ↥(A ⊓ centSub W) * Nat.card ↥(W ⊓ fixV (A ⊓ centSub W)) =
      Nat.card A * Nat.card ↥(W ⊓ fixV A) := by
    rw [← htr, hfix, hcardW]
    ring
  obtain ⟨h1, h2⟩ := B1.card_inf_fixV_eq hA (inf_le_left : A ⊓ centSub W ≤ A) W heq
  by_cases hbot : A ⊓ centSub W = ⊥
  · left
    refine ⟨hbot, ?_⟩
    have hfT : fixV (A ⊓ centSub W) = ⊤ := by rw [hbot, B1.fixV_bot]
    rw [hfix, hfT] at h2
    exact h2
  · right
    have hB2 : IsA2 X (A ⊓ centSub W) := hA.isA2.mono inf_le_left hbot
    have hFF : FFLe X (A ⊓ centSub W) A := ⟨hB2, hA.isA2, inf_le_left, h1⟩
    exact ⟨B1_4_2 hA hFF, hFF⟩

theorem B7_1_2_min [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A) {W : Subgroup V}
    (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥) :
    IsFFStarMin (autSub X W) (autSub A W) := by
  have hst : A ≤ stabSub W := B1.le_stabSub_of_invariant hW
  refine ⟨B7_1_1 hA.1 hW hWA, fun E hE hEle => ?_⟩
  have hEA : E ≤ autSub A W := hEle.2.2.1
  have hB := B1.card_transfer hst hEA
  have hD := B1.card_transfer hst (le_refl (autSub A W))
  rw [B1.preB_autSub hst] at hD
  have heq : Nat.card (B1.preB A W E) * Nat.card ↥(W ⊓ fixV (B1.preB A W E)) =
      Nat.card A * Nat.card ↥(W ⊓ fixV A) := by
    rw [← hB, ← hD, hEle.2.2.2]
  obtain ⟨h1, -⟩ := B1.card_inf_fixV_eq hA.1 (B1.preB_le A W E) W heq
  have hBne : B1.preB A W E ≠ ⊥ := B1.preB_ne_bot hEA hEle.1.2.1
  have hB2 : IsA2 X (B1.preB A W E) := hA.1.isA2.mono (B1.preB_le A W E) hBne
  have hFF : FFLe X (B1.preB A W E) A := ⟨hB2, hA.1.isA2, B1.preB_le A W E, h1⟩
  have hBeq : B1.preB A W E = A := hA.2 _ (B1_4_2 hA.1 hFF) hFF
  calc E = autSub (B1.preB A W E) W := (B1.autSub_preB hEA).symm
    _ = autSub A W := by rw [hBeq]

theorem B7_1_2_faithful [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hm : rk (autSub A W) = rkIdx (fixV (autSub A W))) :
    A ⊓ centSub W = ⊥ ∧ W ⊔ fixV A = ⊤ := by
  rcases B7_1_3 hV hA.1 hW hWA hm with h | ⟨hB, hFF⟩
  · exact h
  · exfalso
    have hBeq : A ⊓ centSub W = A := hA.2 _ hB hFF
    apply hWA
    rw [commSub_eq_bot_iff]
    intro w hw g hg
    have hg' : g ∈ A ⊓ centSub W := by rw [hBeq]; exact hg
    exact hg'.2 w hw

theorem B7_1_2_of_not_strong [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥)
    (hns : ¬ IsStrongFFStarOffender (autSub X W) (autSub A W)) :
    A ⊓ centSub W = ⊥ ∧ W ⊔ fixV A = ⊤ := by
  have hAut := B7_1_1 hA.1 hW hWA
  have hW2 := B1.sq_eq_one_sub hV W
  have hr1 : rAV (autSub A W) ≤ 1 := B1_4_1 hW2 hAut
  have hr2 : ¬ rAV (autSub A W) < 1 := fun h => hns ⟨hAut, h⟩
  exact B7_1_2_faithful hV hA hW hWA
    (B1.rk_eq_rkIdx_of_rAV_eq_one hAut.isA2 (le_antisymm hr1 (not_lt.1 hr2)))

theorem B1_5_1 [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) {W : Subgroup V}
    (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥) :
    IsFFStarOffender (autSub X W) (autSub A W) :=
  B7_1_1 hA hW hWA

theorem B1_5_2 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥) :
    IsFFStarMin (autSub X W) (autSub A W) ∧
      (¬ IsStrongFFStarOffender (autSub X W) (autSub A W) →
        W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥) :=
  ⟨B7_1_2_min hA hW hWA, fun hns => (B7_1_2_of_not_strong hV hA hW hWA hns).symm⟩

theorem B1_5_6 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hm : rk (autSub A W) = rkIdx (fixV (autSub A W))) :
    A ⊓ centSub W = ⊥ ∨ IsFFStarOffender X (A ⊓ centSub W) := by
  rcases B7_1_3 hV hA hW hWA hm with h | ⟨hB, -⟩
  · exact Or.inl h.1
  · exact Or.inr hB

theorem B1_5_5 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : commSub W A ≠ ⊥)
    (hq : qOf (autSub X W) = 1) :
    IsFFStarMin (autSub X W) (autSub A W) ∧ W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ := by
  have hmin := B7_1_2_min hA hW hWA
  have hW2 := B1.sq_eq_one_sub hV W
  have hr := rAV_eq_one_of_one_le_qOf hW2 (hq ▸ le_rfl : (1 : WithTop ℚ) ≤ qOf (autSub X W))
    hmin.1
  obtain ⟨h1, h2⟩ := B7_1_2_faithful hV hA hW hWA
    (B1.rk_eq_rkIdx_of_rAV_eq_one hmin.1.isA2 hr)
  exact ⟨hmin, h2, h1⟩

theorem B1_5_7 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hfaith : A ⊓ centSub W = ⊥)
    (hq : qOf (autSub X W) = 1) : W ⊔ fixV A = ⊤ ∧ commV A ≤ W := by
  have hst : A ≤ stabSub W := B1.le_stabSub_of_invariant hW
  have hAut := B7_1_1 hA hW hWA
  have hW2 := B1.sq_eq_one_sub hV W
  have hr := rAV_eq_one_of_one_le_qOf hW2 (hq ▸ le_rfl : (1 : WithTop ℚ) ≤ qOf (autSub X W)) hAut
  have hcardW : Nat.card W = Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) :=
    (rAV_eq_one_iff hW2 hAut.isA2).1 hr
  have htr := B1.card_transfer hst (le_refl (autSub A W))
  rw [B1.preB_autSub hst, hfaith, Subgroup.card_bot, mul_one, ← hcardW] at htr
  have hsup := card_sup_mul_card_inf W (fixV A)
  have hle : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV] at this
  have hpos : 0 < Nat.card ↥(W ⊓ fixV A) := Nat.card_pos
  have hcardsup : Nat.card ↥(W ⊔ fixV A) = Nat.card A * Nat.card (fixV A) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hsup, htr]
    ring
  have htop : W ⊔ fixV A = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    refine le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective) ?_
    rw [hcardsup]
    exact hle
  refine ⟨htop, ?_⟩
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  have hv : v ∈ W ⊔ fixV A := by rw [htop]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
  have hxc : x c = c := hc x hx
  have : x (w * c) * (w * c)⁻¹ = x w * w⁻¹ := by
    rw [map_mul, hxc]
    group
  rw [this]
  exact W.mul_mem (hW x hx w hw) (W.inv_mem hw)

end CFSG.Quasithin

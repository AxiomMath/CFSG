module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2C

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_mem_sup_comm {U W : Subgroup G} (hc : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u)
    {x : G} (hx : x ∈ U ⊔ W) : ∃ u ∈ U, ∃ w ∈ W, x = u * w := by
  let T : Subgroup G :=
    { carrier := {x | ∃ u ∈ U, ∃ w ∈ W, x = u * w}
      one_mem' := ⟨1, U.one_mem, 1, W.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, w₁, hw₁, rfl⟩ ⟨u₂, hu₂, w₂, hw₂, rfl⟩
        refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, w₁ * w₂, W.mul_mem hw₁ hw₂, ?_⟩
        have h := hc u₂ hu₂ w₁ hw₁
        calc u₁ * w₁ * (u₂ * w₂) = u₁ * (w₁ * u₂) * w₂ := by group
          _ = u₁ * (u₂ * w₁) * w₂ := by rw [← h]
          _ = u₁ * u₂ * (w₁ * w₂) := by group
      inv_mem' := by
        rintro _ ⟨u, hu, w, hw, rfl⟩
        refine ⟨u⁻¹, U.inv_mem hu, w⁻¹, W.inv_mem hw, ?_⟩
        have h := hc u hu w hw
        calc (u * w)⁻¹ = (w * u)⁻¹ := by rw [h]
          _ = u⁻¹ * w⁻¹ := mul_inv_rev w u }
  have hle : U ⊔ W ≤ T := sup_le (fun u hu => ⟨u, hu, 1, W.one_mem, by simp⟩)
    (fun w hw => ⟨1, U.one_mem, w, hw, by simp⟩)
  exact hle hx

omit [Finite G] in
theorem inf_sup_le_of_card_two {Zt V C : Subgroup G} (hZ : Nat.card Zt = 2)
    (hc : ∀ z ∈ Zt, ∀ v ∈ V, z * v = v * z) (hVC : V ≤ C) (hZC : ¬ Zt ≤ C) :
    Zt ⊓ C = ⊥ ∧ C ⊓ (Zt ⊔ V) ≤ V := by
  have hbot : Zt ⊓ C = ⊥ := by
    have : Fact (Nat.Prime (Nat.card Zt)) := ⟨by rw [hZ]; exact Nat.prime_two⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Zt ⊓ C).subgroupOf Zt) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
      have : (⟨g, hg.1⟩ : Zt) ∈ (Zt ⊓ C).subgroupOf Zt := hg
      rw [h, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exact absurd (fun z hz => (show (⟨z, hz⟩ : Zt) ∈ (Zt ⊓ C).subgroupOf Zt by
        rw [h]; trivial).2) hZC
  refine ⟨hbot, fun w ⟨hwC, hw⟩ => ?_⟩
  obtain ⟨z, hz, v, hv, rfl⟩ := exists_mul_of_mem_sup_comm hc hw
  have hzC : z ∈ C := by
    have := C.mul_mem hwC (C.inv_mem (hVC hv))
    simpa using this
  have hz1 : z = 1 := by
    have : z ∈ Zt ⊓ C := ⟨hz, hzC⟩
    rw [hbot] at this
    exact this
  subst hz1
  simpa using hv

omit [Finite G] in
theorem le_normalizer_of_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : a * b * a⁻¹ = b := by rw [h a ha b hb]; group
    rwa [this]
  · intro hb
    have e : a * (a * b * a⁻¹) = a * b := by
      calc a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := h a ha _ hb
        _ = a * b := by group
    have e2 : a * b * a⁻¹ = b := mul_left_cancel e
    rwa [e2] at hb

open S35 S35.Std

theorem Wl_le_Wb (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) :
    Wl l ≤ Wb β := by
  rw [Wb_eq_iSup_Wl hS hβ]
  exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl le_rfl

omit [Finite G] in
theorem Vn_le_Wl_self {β l : Geo H M} (hl : l ∈ nbrs β) : Vn β ≤ Wl l :=
  Vn_le_Wl (mem_nbrs_symm.mpr hl)

theorem Wl_le_inf_stab (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) : Wl l ≤ stab β ⊓ stab l :=
  (Wl_le_Wb hS hβ hl).trans (le_inf ((Wb_le_Qv hS β).trans (pCoreOf_le 2 _))
    ((Wb_le_Ql hS hl).trans (pCoreOf_le 2 _)))

theorem not_mem_normalizer_Wl (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β)
    (hP : ∀ P : Subgroup G, stab β ⊓ stab l ≤ P → P ≤ stab β →
      P = stab β ∨ P ≤ Subgroup.normalizer (Zv l : Set G))
    {x : G} (hx : x ∈ stab β) (hxN : x ∉ Subgroup.normalizer (Zv l : Set G)) :
    x ∉ Subgroup.normalizer (Wl l : Set G) := by
  intro hxW
  have hle : stab β ⊓ stab l ⊔ Subgroup.zpowers x ≤ stab β :=
    sup_le inf_le_left ((Subgroup.zpowers_le).mpr hx)
  have hxP : x ∈ stab β ⊓ stab l ⊔ Subgroup.zpowers x :=
    (le_sup_right : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  rcases hP _ le_sup_left hle with h | h
  · have hPW : stab β ⊓ stab l ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (Wl l : Set G) :=
      sup_le (inf_le_right.trans (Wl_normal l)) ((Subgroup.zpowers_le).mpr hxW)
    rw [h] at hPW
    have hbot : Wl l = ⊥ :=
      eq_bot_of_normalizes_both hS.glob.amalg (show (graph (H ⊔ M) H M).Adj β l from hl)
        (Wl_le_inf_stab hS hβ hl) hPW (Wl_normal l)
    have h1 : Zv β = ⊥ :=
      le_bot_iff.mp (hbot ▸ (Zv_le_Vn_S5 hS hβ).trans (Vn_le_Wl_self hl))
    have h2 := hS.cardZ5 β hβ
    rw [h1, Subgroup.card_bot] at h2
    omega
  · exact hxN (h hxP)

omit [Finite G] in
theorem conj_mem_sup_of_comm {A Zt V : Subgroup G} {x : G} (hVA : V ≤ A)
    (hcomm : ∀ w ∈ A, ⁅w, x⁆ ∈ Zt ⊔ V) {b : G} (hb : b ∈ conjSub x A) : b ∈ A ⊔ Zt := by
  rw [mem_conjSub] at hb
  have hc := hcomm _ hb
  have e : b = (⁅x⁻¹ * b * x, x⁆)⁻¹ * (x⁻¹ * b * x) := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine mul_mem (inv_mem ?_) ((le_sup_left : A ≤ A ⊔ Zt) hb)
  exact (sup_le (le_sup_right : Zt ≤ A ⊔ Zt) (hVA.trans le_sup_left)) hc

theorem link_of_transv (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β)
    (hP : ∀ P : Subgroup G, stab β ⊓ stab l ≤ P → P ≤ stab β →
      P = stab β ∨ P ≤ Subgroup.normalizer (Zv l : Set G))
    (hWab : ∀ u ∈ Wb β, ∀ v ∈ Wb β, u * v = v * u)
    {Zt : Subgroup G} (hZ : Nat.card Zt = 2) (hZW : Zt ≤ Wb β) (hZV : ¬ Zt ≤ Vn β)
    {x : G} (hx : x ∈ stab β) (hxN : x ∉ Subgroup.normalizer (Zv l : Set G))
    (hcomm : ∀ w ∈ Wl l, ⁅w, x⁆ ∈ Zt ⊔ Vn β) :
    (Wl l ⊓ conjSub x (Wl l)).relIndex (Wl l) = 2 ∧
      ∀ h ∈ Wl l ⊓ conjSub x (Wl l), ⁅h, x⁆ ∈ Vn β := by
  set A := Wl l with hA
  set B := conjSub x A with hB
  have hVA : Vn β ≤ A := Vn_le_Wl_self hl
  have hAW : A ≤ Wb β := Wl_le_Wb hS hβ hl
  have hVW : Vn β ≤ Wb β := Vn_le_Wb_self hS hβ
  have hcardB : Nat.card B = Nat.card A := card_conjSub x A
  have hxA : x ∉ Subgroup.normalizer (A : Set G) := not_mem_normalizer_Wl hS hβ hl hP hx hxN
  have hBA : ¬ B ≤ A := fun h =>
    hxA (mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge h hcardB.ge))
  have hBsup : B ≤ A ⊔ Zt := fun b hb => conj_mem_sup_of_comm hVA hcomm hb
  have hZV' : ∀ z ∈ Zt, ∀ v ∈ Vn β, z * v = v * z := fun z hz v hv => hWab z (hZW hz) v (hVW hv)
  have hZA : ¬ Zt ≤ A := fun h => hBA (hBsup.trans (sup_le le_rfl h))
  obtain ⟨hZA0, -⟩ := inf_sup_le_of_card_two hZ hZV' hVA hZA
  have hZN : Zt ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_comm fun z hz a ha => hWab z (hZW hz) a (hAW ha)
  have hBW : B ≤ Wb β := by
    intro b hb
    rw [mem_conjSub] at hb
    have h2 := ((Subgroup.mem_normalizer_iff.mp (Wb_normal β hx)) (x⁻¹ * b * x)).mp (hAW hb)
    simpa [mul_assoc] using h2
  have hAN : A ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => hWab a (hAW ha) b (hBW hb)
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hcardZA : Nat.card (Zt ⊔ A : Subgroup G) = 2 * Nat.card A := by
    have h1 : (Zt ⊓ A).relIndex Zt = A.relIndex (Zt ⊔ A) := relIndex_inf_eq_relIndex_sup hZN
    rw [hZA0, Subgroup.relIndex_bot_left, hZ] at h1
    have h2 := Subgroup.relIndex_mul_card A (Zt ⊔ A)
    rw [inf_eq_left.mpr le_sup_right, ← h1] at h2
    exact h2.symm
  have hcardAB : Nat.card (A ⊔ B : Subgroup G) = 2 * Nat.card A := by
    have hd1 : Nat.card A ∣ Nat.card (A ⊔ B : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card (A ⊔ B : Subgroup G) ∣ Nat.card (Zt ⊔ A : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le (le_sup_right) (hBsup.trans (by rw [sup_comm])))
    obtain ⟨k, hk⟩ := hd1
    rw [hk, hcardZA, mul_comm 2] at hd2
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hpos hd2
    have hk12 : k = 1 ∨ k = 2 := (Nat.dvd_prime Nat.prime_two).mp hk2
    rcases hk12 with rfl | rfl
    · exfalso
      have hEq : A = A ⊔ B :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, mul_one])
      exact hBA (hEq ▸ le_sup_right)
    · rw [hk, mul_comm]
  have hrel : (A ⊓ B).relIndex A = 2 := by
    have h1 : (A ⊓ B).relIndex A = B.relIndex (A ⊔ B) := relIndex_inf_eq_relIndex_sup hAN
    have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
    rw [inf_eq_left.mpr le_sup_right, hcardB, hcardAB, ← h1] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  refine ⟨hrel, ?_⟩
  have hVinv : ∀ v ∈ Vn β, x⁻¹ * v * x ∈ Vn β := fun v hv => by
    have := ((Subgroup.mem_normalizer_iff.mp (Vn_normal β (inv_mem hx))) v).mp hv
    simpa using this
  have hVfwd : ∀ v ∈ Vn β, x * v * x⁻¹ ∈ Vn β := fun v hv =>
    ((Subgroup.mem_normalizer_iff.mp (Vn_normal β hx)) v).mp hv
  have hVB : Vn β ≤ B := fun v hv => mem_conjSub.mpr (hVA (hVinv v hv))
  have hZB : ¬ Zt ≤ B := by
    intro hZB
    obtain ⟨z, hz, hzV⟩ := IsConcreteLE.not_le_iff_exists.mp hZV
    have hzB := hZB hz
    rw [mem_conjSub] at hzB
    have hc := hcomm _ hzB
    have hw : x⁻¹ * z * x ∈ Zt ⊔ Vn β := by
      have : x⁻¹ * z * x = ⁅x⁻¹ * z * x, x⁆ * z := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hc ((le_sup_left : Zt ≤ Zt ⊔ Vn β) hz)
    have hwV := (inf_sup_le_of_card_two hZ hZV' hVA hZA).2 ⟨hzB, hw⟩
    exact hzV (by simpa [mul_assoc] using hVfwd _ hwV)
  have hBZ := (inf_sup_le_of_card_two hZ hZV' hVB hZB).2
  intro h hh
  have hc := hcomm h hh.1
  have hxh : x * h * x⁻¹ ∈ B := mem_conjSub.mpr (by simpa [mul_assoc] using hh.1)
  have e : ⁅h, x⁆ = h * (x * h * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  have : ⁅h, x⁆ ∈ B := by rw [e]; exact mul_mem hh.2 (inv_mem hxh)
  exact hBZ ⟨this, hc⟩

end S35.T2C

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.Recognition.St84.Sp44DC

import CFSG.Quasithin.Background.RonanF13SU
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_inj uElt_zero_eq_one)
open CFSG.QuasithinUnique.Fin257.Sp4
open CFSG.Quasithin.F112R.St84.Sp44 (B0 dTor rootXa rootXb T0B A1B A2B Z0B HB XaB XbB
  mem_dTor dSp_mem_dTor dSp_inj dTor_comm dTor_le rootXa_le_antiUnipotent
  rootXb_le_antiUnipotent rootXa_comm_dSp rootXb_comm_dSp_left A1_le_B0 A2_le_B0 Z0_le_B0
  Xa_le_B0 Xb_le_B0 XaB_le_T0B XbB_le_T0B map_Z0B frobAut_pow_dSp)
open CFSG.RankThree.PartOne.KCRootAxis (frobAut exists_sq_eq)
open CFSG.Quasithin.H13.F431.SpOut2 (frobAut_pow_uElt)
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem mul_eq_self_iff {x a : F} : x * a = a ↔ x = 1 ∨ a = 0 := by
  constructor
  · intro h
    have h' : (x - 1) * a = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with hx | ha
    · exact Or.inl (sub_eq_zero.mp hx)
    · exact Or.inr ha
  · rintro (rfl | rfl)
    · simp
    · simp

private theorem units_mul_eq_self_iff {x : Fˣ} {a : F} :
    (x : F) * a = a ↔ x = 1 ∨ a = 0 := by
  rw [mul_eq_self_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by rw [h, Units.val_one])
    · exact Or.inr h

private theorem unit_sq_eq_one_iff {u : Fˣ} : u ^ 2 = 1 ↔ u = 1 := by
  constructor
  · intro h
    by_contra hu
    have h2 : (u : F) ^ 2 = 1 := by
      have := congrArg (fun v : Fˣ => (v : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h2 with h1 | h1
    · exact hu (Units.ext h1)
    · rw [CharTwo.neg_eq] at h1
      exact hu (Units.ext h1)
  · rintro rfl
    simp

private theorem unit_sq_ne_one {u : Fˣ} (hu : u ≠ 1) : u ^ 2 ≠ 1 :=
  fun h => hu (unit_sq_eq_one_iff.mp h)

private theorem exists_unit_ne_one (hF : 4 ≤ Nat.card F) : ∃ lam : Fˣ, lam ≠ 1 := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcard : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    omega
  exact Fintype.exists_ne_of_one_lt_card hcard 1

private theorem ringEquiv_ne_zero_of_ne_zero (ρ : F ≃+* F) {x : F} (hx : x ≠ 0) :
    ρ x ≠ 0 := fun h => hx (ρ.injective (by rw [h, map_zero]))

private theorem eq_of_inv_eq_inv {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a⁻¹ = b⁻¹) : a = b := by
  have h1 : a * b⁻¹ = 1 := by
    rw [← h, mul_inv_cancel₀ ha]
  exact (mul_inv_eq_one₀ hb).mp h1

private theorem exists_unit_sq_eq (μ : Fˣ) : ∃ τ : Fˣ, τ ^ 2 = μ := by
  obtain ⟨τ, hτ⟩ := exists_sq_eq (μ : F)
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hτ
    exact Units.ne_zero μ hτ.symm
  refine ⟨Units.mk0 τ hτ0, Units.ext ?_⟩
  show τ ^ 2 = (μ : F)
  exact hτ

private theorem pow_two_pow (x : F) (k : ℕ) :
    (x ^ 2 ^ k) ^ 2 = (x ^ 2) ^ 2 ^ k := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem chi_inj {S T s t : Fˣ}
    (h1 : (S : F) * (T : F)⁻¹ = (s : F) * (t : F)⁻¹)
    (h2 : (T : F) ^ 2 = (t : F) ^ 2) : S = s ∧ T = t := by
  have ht : T = t := by
    apply Units.ext
    exact CharTwo.sq_inj.mp h2
  have h1' : (S : F) * (t : F)⁻¹ = (s : F) * (t : F)⁻¹ := by
    rwa [ht] at h1
  refine ⟨?_, ht⟩
  exact Units.ext (mul_right_cancel₀ (inv_ne_zero (Units.ne_zero t)) h1')

private theorem iff_of_map_eq {Y : Type*} [Group Y] (σ : MulAut Y) {S : Subgroup Y}
    (h : S.map σ.toMonoidHom = S) (b : Y) : b ∈ S ↔ σ b ∈ S := by
  constructor
  · intro hb
    rw [← h]
    exact Subgroup.mem_map_of_mem σ.toMonoidHom hb
  · intro hb
    rw [← h] at hb
    obtain ⟨b', hb', he⟩ := Subgroup.mem_map.mp hb
    have hbb : b' = b := σ.injective he
    rwa [hbb] at hb'

private theorem map_inv_of_map_eq {Y : Type*} [Group Y] {S : Subgroup Y} {σ : MulAut Y}
    (h : S.map σ.toMonoidHom = S) : S.map σ⁻¹.toMonoidHom = S := by
  have hcomp : (σ⁻¹.toMonoidHom).comp σ.toMonoidHom = MonoidHom.id Y := by
    ext y
    simp
  have h1 := congrArg (fun K : Subgroup Y => K.map σ⁻¹.toMonoidHom) h
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  exact h1.symm

theorem exists_addEquiv_of_map_mul {Γ : Type*} [Group Γ] {A : Type*} [AddGroup A] [Finite A]
    (f : A → Γ) (hf_add : ∀ a b : A, f (a + b) = f a * f b)
    (hf_inj : Function.Injective f) (τ : MulAut Γ) (hτ : ∀ a : A, ∃ b : A, τ (f a) = f b) :
    ∃ l : A ≃+ A, ∀ a : A, τ (f a) = f (l a) := by
  choose l hl using hτ
  have hadd : ∀ a b : A, l (a + b) = l a + l b := by
    intro a b
    apply hf_inj
    have e1 : f (l (a + b)) = f (l a) * f (l b) := by
      rw [← hl, ← hl, ← hl, hf_add, map_mul]
    rw [e1, hf_add]
  have hinj : Function.Injective l := by
    intro a b hab
    apply hf_inj
    apply τ.injective
    rw [hl, hl, hab]
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' l hadd)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hl⟩

theorem dSp_mul_uElt_comm_iff (s t : Fˣ) (a b c d : F) :
    dSp s t * uElt a b c d = uElt a b c d * dSp s t ↔
      (s = t ∨ a = 0) ∧ (s * t = 1 ∨ b = 0) ∧ (s = 1 ∨ c = 0) ∧ (t = 1 ∨ d = 0) := by
  constructor
  · intro h
    have hc : dSp s t * uElt a b c d * (dSp s t)⁻¹ = uElt a b c d := by
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [dSp_conj_uElt, Units.val_inv_eq_inv_val] at hc
    obtain ⟨h1, h2, h3, h4⟩ := uElt_inj hc
    have h1' : ((s * t⁻¹ : Fˣ) : F) * a = a := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact h1
    have h2' : ((s * t : Fˣ) : F) * b = b := by
      rw [Units.val_mul]
      exact h2
    have h3' : ((s ^ 2 : Fˣ) : F) * c = c := h3
    have h4' : ((t ^ 2 : Fˣ) : F) * d = d := h4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases units_mul_eq_self_iff.mp h1' with h | h
      · exact Or.inl (mul_inv_eq_one.mp h)
      · exact Or.inr h
    · exact units_mul_eq_self_iff.mp h2'
    · rcases units_mul_eq_self_iff.mp h3' with h | h
      · exact Or.inl (unit_sq_eq_one_iff.mp h)
      · exact Or.inr h
    · rcases units_mul_eq_self_iff.mp h4' with h | h
      · exact Or.inl (unit_sq_eq_one_iff.mp h)
      · exact Or.inr h
  · rintro ⟨h1, h2, h3, h4⟩
    have e1 : (s : F) * (t : F)⁻¹ * a = a := by
      rcases h1 with h | h
      · rw [h, mul_inv_cancel₀ (Units.ne_zero t), one_mul]
      · rw [h, mul_zero]
    have e2 : (s : F) * (t : F) * b = b := by
      rcases h2 with h | h
      · have hval : (s : F) * (t : F) = 1 := by
          rw [← Units.val_mul, h, Units.val_one]
        rw [hval, one_mul]
      · rw [h, mul_zero]
    have e3 : (s : F) ^ 2 * c = c := by
      rcases h3 with h | h
      · rw [h, Units.val_one, one_pow, one_mul]
      · rw [h, mul_zero]
    have e4 : (t : F) ^ 2 * d = d := by
      rcases h4 with h | h
      · rw [h, Units.val_one, one_pow, one_mul]
      · rw [h, mul_zero]
    have hc : dSp s t * uElt a b c d * (dSp s t)⁻¹ = uElt a b c d := by
      rw [dSp_conj_uElt, Units.val_inv_eq_inv_val, e1, e2, e3, e4]
    calc dSp s t * uElt a b c d
        = dSp s t * uElt a b c d * (dSp s t)⁻¹ * dSp s t := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = uElt a b c d * dSp s t := by rw [hc]

private def xaB (a : F) : ↥(B0 F) := ⟨uElt a 0 0 0, Xa_le_B0 ⟨a, rfl⟩⟩

private def xbB (d : F) : ↥(B0 F) := ⟨uElt 0 0 0 d, Xb_le_B0 ⟨d, rfl⟩⟩

private def torB (s t : Fˣ) : ↥(B0 F) := ⟨dSp s t, dTor_le (dSp_mem_dTor s t)⟩

private def zU1 : ↥(B0 F) := ⟨uElt 0 1 0 0, Z0_le_B0 ⟨1, 0, rfl⟩⟩

private def zU2 : ↥(B0 F) := ⟨uElt 0 0 1 0, Z0_le_B0 ⟨0, 1, rfl⟩⟩

private theorem torB_mem (s t : Fˣ) : torB s t ∈ HB F :=
  Subgroup.mem_subgroupOf.mpr (dSp_mem_dTor s t)

private theorem zU1_mem : zU1 (F := F) ∈ Z0B F := ⟨1, 0, rfl⟩

private theorem zU2_mem : zU2 (F := F) ∈ Z0B F := ⟨0, 1, rfl⟩

private theorem symm_maps_to_XbB (hF : 4 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hA2 : (A2B F).map σ.toMonoidHom = A2B F) :
    (XbB F).map σ⁻¹.toMonoidHom ≤ XbB F := by
  classical
  obtain ⟨lam, hlam⟩ := exists_unit_ne_one (F := F) hF
  let x : ↥(B0 F) := xbB 1
  have hxXb : x ∈ XbB F := ⟨1, rfl⟩
  have hxT : x ∈ T0B F := XbB_le_T0B hxXb
  have hx_notA2 : x ∉ A2B F := by
    intro h
    obtain ⟨a, b, c, h'⟩ := h
    have h2 := uElt_inj (show (uElt (0 : F) 0 0 1 : antiSp F) = uElt a b c 0 from h')
    exact one_ne_zero h2.2.2.2
  have hσxT : σ x ∈ T0B F := (iff_of_map_eq σ hT x).mp hxT
  obtain ⟨a, b, c, d, hσx⟩ := Subgroup.mem_subgroupOf.mp hσxT
  have hd : d ≠ 0 := by
    intro hd0
    have hmem : σ x ∈ A2B F := by
      show (σ x : antiSp F) ∈ radA2 F
      exact ⟨a, b, c, by rw [hσx, hd0]⟩
    exact hx_notA2 ((iff_of_map_eq σ hA2 x).mpr hmem)
  let hB : ↥(B0 F) := torB lam 1
  let k : ↥(B0 F) := σ hB
  have hkH : k ∈ HB F := (iff_of_map_eq σ hH hB).mp (torB_mem lam 1)
  obtain ⟨S, T, hkT⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hkH)
  have hcomm_x : hB * x = x * hB := by
    apply Subtype.ext
    show dSp lam 1 * uElt 0 0 0 1 = uElt 0 0 0 1 * dSp lam 1
    exact rootXb_comm_dSp_left lam hxXb
  have hcomm_kB : k * σ x = σ x * k := by
    have h := congrArg σ hcomm_x
    simpa [k, map_mul] using h
  have hcomm_k : (k : antiSp F) * (σ x : antiSp F) = (σ x : antiSp F) * (k : antiSp F) :=
    congrArg Subtype.val hcomm_kB
  have hcrit := (dSp_mul_uElt_comm_iff S T a b c d).mp (by
    rw [← hkT, ← hσx]
    exact hcomm_k)
  have hT1 : T = 1 := by
    rcases hcrit.2.2.2 with h | h
    · exact h
    · exact absurd h hd
  have hk_eq : (k : antiSp F) = dSp S 1 := by
    rw [hkT, hT1]
  rintro _ ⟨y, hy, rfl⟩
  have hyT : y ∈ T0B F := XbB_le_T0B hy
  have hσinv_T : σ⁻¹ y ∈ T0B F :=
    (iff_of_map_eq σ⁻¹ (map_inv_of_map_eq hT) y).mp hyT
  obtain ⟨a', b', c', d', hy'⟩ := Subgroup.mem_subgroupOf.mp hσinv_T
  have hcomm_y : (k : antiSp F) * (y : antiSp F) = (y : antiSp F) * (k : antiSp F) := by
    rw [hk_eq]
    exact rootXb_comm_dSp_left S hy
  have hcomm_inv : ((σ⁻¹ y : ↥(B0 F)) : antiSp F) * dSp lam 1 =
      dSp lam 1 * ((σ⁻¹ y : ↥(B0 F)) : antiSp F) := by
    have hB' : (σ⁻¹ y : ↥(B0 F)) * hB = hB * (σ⁻¹ y : ↥(B0 F)) := by
      have h1 : k * y = y * k := Subtype.ext hcomm_y
      have h2 : σ⁻¹ k * σ⁻¹ y = σ⁻¹ y * σ⁻¹ k := by
        rw [← map_mul, ← map_mul, h1]
      simpa [k, hB] using h2.symm
    exact congrArg Subtype.val hB'
  have hy'' : ((MulEquiv.toMonoidHom σ⁻¹) y) = uElt a' b' c' d' := hy'
  have hcrit' := (dSp_mul_uElt_comm_iff lam 1 a' b' c' d').mp (by
    rw [← hy'']
    exact hcomm_inv.symm)
  have ha' : a' = 0 := by
    rcases hcrit'.1 with h | h
    · exact absurd h hlam
    · exact h
  have hb' : b' = 0 := by
    rcases hcrit'.2.1 with h | h
    · exact absurd (by simpa using h) hlam
    · exact h
  have hc' : c' = 0 := by
    rcases hcrit'.2.2.1 with h | h
    · exact absurd h hlam
    · exact h
  exact Subgroup.mem_subgroupOf.mpr (by
    rw [hy'', ha', hb', hc']
    exact ⟨d', rfl⟩)

theorem map_XbB_eq (hF : 4 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hA2 : (A2B F).map σ.toMonoidHom = A2B F) :
    (XbB F).map σ.toMonoidHom = XbB F := by
  have hinv := symm_maps_to_XbB hF σ hT hH hA2
  have hfwd : (XbB F).map σ.toMonoidHom ≤ XbB F := by
    simpa using symm_maps_to_XbB hF σ⁻¹ (map_inv_of_map_eq hT) (map_inv_of_map_eq hH)
      (map_inv_of_map_eq hA2)
  refine le_antisymm hfwd ?_
  intro y hy
  exact ⟨σ⁻¹ y, hinv ⟨y, hy, rfl⟩, by simp⟩

private theorem symm_maps_to_XaB (hF : 4 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F) :
    (XaB F).map σ⁻¹.toMonoidHom ≤ XaB F := by
  classical
  obtain ⟨lam, hlam⟩ := exists_unit_ne_one (F := F) hF
  let x : ↥(B0 F) := xaB 1
  have hxXa : x ∈ XaB F := ⟨1, rfl⟩
  have hxT : x ∈ T0B F := XaB_le_T0B hxXa
  have hx_notA1 : x ∉ A1B F := by
    intro h
    obtain ⟨b, c, d, h'⟩ := h
    have h2 := uElt_inj (show (uElt (1 : F) 0 0 0 : antiSp F) = uElt 0 b c d from h')
    exact one_ne_zero h2.1
  have hσxT : σ x ∈ T0B F := (iff_of_map_eq σ hT x).mp hxT
  obtain ⟨a, b, c, d, hσx⟩ := Subgroup.mem_subgroupOf.mp hσxT
  have ha : a ≠ 0 := by
    intro ha0
    have hmem : σ x ∈ A1B F := by
      show (σ x : antiSp F) ∈ radA1 F
      exact ⟨b, c, d, by rw [hσx, ha0]⟩
    exact hx_notA1 ((iff_of_map_eq σ hA1 x).mpr hmem)
  let hB : ↥(B0 F) := torB lam lam
  let k : ↥(B0 F) := σ hB
  have hkH : k ∈ HB F := (iff_of_map_eq σ hH hB).mp (torB_mem lam lam)
  obtain ⟨S, T, hkT⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hkH)
  have hcomm_x : hB * x = x * hB := by
    apply Subtype.ext
    show dSp lam lam * uElt 1 0 0 0 = uElt 1 0 0 0 * dSp lam lam
    exact rootXa_comm_dSp lam hxXa
  have hcomm_kB : k * σ x = σ x * k := by
    have h := congrArg σ hcomm_x
    simpa [k, map_mul] using h
  have hcomm_k : (k : antiSp F) * (σ x : antiSp F) = (σ x : antiSp F) * (k : antiSp F) :=
    congrArg Subtype.val hcomm_kB
  have hcrit := (dSp_mul_uElt_comm_iff S T a b c d).mp (by
    rw [← hkT, ← hσx]
    exact hcomm_k)
  have hST : S = T := by
    rcases hcrit.1 with h | h
    · exact h
    · exact absurd h ha
  have hk_eq : (k : antiSp F) = dSp S S := by
    rw [hkT, hST]
  rintro _ ⟨y, hy, rfl⟩
  have hyT : y ∈ T0B F := XaB_le_T0B hy
  have hσinv_T : σ⁻¹ y ∈ T0B F :=
    (iff_of_map_eq σ⁻¹ (map_inv_of_map_eq hT) y).mp hyT
  obtain ⟨a', b', c', d', hy'⟩ := Subgroup.mem_subgroupOf.mp hσinv_T
  have hcomm_y : (k : antiSp F) * (y : antiSp F) = (y : antiSp F) * (k : antiSp F) := by
    rw [hk_eq]
    exact rootXa_comm_dSp S hy
  have hcomm_inv : ((σ⁻¹ y : ↥(B0 F)) : antiSp F) * dSp lam lam =
      dSp lam lam * ((σ⁻¹ y : ↥(B0 F)) : antiSp F) := by
    have hB' : (σ⁻¹ y : ↥(B0 F)) * hB = hB * (σ⁻¹ y : ↥(B0 F)) := by
      have h1 : k * y = y * k := Subtype.ext hcomm_y
      have h2 : σ⁻¹ k * σ⁻¹ y = σ⁻¹ y * σ⁻¹ k := by
        rw [← map_mul, ← map_mul, h1]
      simpa [k, hB] using h2.symm
    exact congrArg Subtype.val hB'
  have hy'' : ((MulEquiv.toMonoidHom σ⁻¹) y) = uElt a' b' c' d' := hy'
  have hcrit' := (dSp_mul_uElt_comm_iff lam lam a' b' c' d').mp (by
    rw [← hy'']
    exact hcomm_inv.symm)
  have hb' : b' = 0 := by
    rcases hcrit'.2.1 with h | h
    · have h2 : lam ^ 2 = 1 := by simpa [pow_two] using h
      exact absurd h2 (unit_sq_ne_one hlam)
    · exact h
  have hc' : c' = 0 := by
    rcases hcrit'.2.2.1 with h | h
    · exact absurd h hlam
    · exact h
  have hd' : d' = 0 := by
    rcases hcrit'.2.2.2 with h | h
    · exact absurd h hlam
    · exact h
  exact Subgroup.mem_subgroupOf.mpr (by
    rw [hy'', hb', hc', hd']
    exact ⟨a', rfl⟩)

theorem map_XaB_eq (hF : 4 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F) :
    (XaB F).map σ.toMonoidHom = XaB F := by
  have hinv := symm_maps_to_XaB hF σ hT hH hA1
  have hfwd : (XaB F).map σ.toMonoidHom ≤ XaB F := by
    simpa using symm_maps_to_XaB hF σ⁻¹ (map_inv_of_map_eq hT) (map_inv_of_map_eq hH)
      (map_inv_of_map_eq hA1)
  refine le_antisymm hfwd ?_
  intro y hy
  exact ⟨σ⁻¹ y, hinv ⟨y, hy, rfl⟩, by simp⟩

private def ActsOnXa (σ : MulAut ↥(B0 F)) (fa : F ≃+ F) : Prop :=
  ∀ a : F, ((σ (xaB a) : ↥(B0 F)) : antiSp F) = uElt (fa a) 0 0 0

private def ActsOnXb (σ : MulAut ↥(B0 F)) (fb : F ≃+ F) : Prop :=
  ∀ d : F, ((σ (xbB d) : ↥(B0 F)) : antiSp F) = uElt 0 0 0 (fb d)

private theorem sigmaCoords_exists (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) :
    ∃ p : Fˣ × Fˣ, ((σ (torB s t) : ↥(B0 F)) : antiSp F) = dSp p.1 p.2 := by
  have hmem : σ (torB s t) ∈ HB F := (iff_of_map_eq σ hH (torB s t)).mp (torB_mem s t)
  obtain ⟨S, T, hST⟩ := mem_dTor.mp (Subgroup.mem_subgroupOf.mp hmem)
  exact ⟨(S, T), hST⟩

private noncomputable def sigmaCoords (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) : Fˣ × Fˣ :=
  Classical.choose (sigmaCoords_exists σ hH s t)

private noncomputable def sigmaCoordsA (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) : Fˣ :=
  (sigmaCoords σ hH s t).1

private noncomputable def sigmaCoordsD (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) : Fˣ :=
  (sigmaCoords σ hH s t).2

private theorem sigmaCoords_spec (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) :
    ((σ (torB s t) : ↥(B0 F)) : antiSp F) =
      dSp (sigmaCoords σ hH s t).1 (sigmaCoords σ hH s t).2 :=
  Classical.choose_spec (sigmaCoords_exists σ hH s t)

private theorem sigmaCoordsA_spec (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) :
    ((σ (torB s t) : ↥(B0 F)) : antiSp F) =
      dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t) :=
  sigmaCoords_spec σ hH s t

private noncomputable def chiA (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) : Fˣ :=
  sigmaCoordsA σ hH s t * (sigmaCoordsD σ hH s t)⁻¹

private noncomputable def chiD (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) : Fˣ :=
  (sigmaCoordsD σ hH s t) ^ 2

private theorem chiA_apply (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) :
    (chiA σ hH s t : F) =
      (sigmaCoordsA σ hH s t : F) * (sigmaCoordsD σ hH s t : F)⁻¹ := by
  rw [chiA, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem chiD_apply (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) (s t : Fˣ) :
    (chiD σ hH s t : F) = (sigmaCoordsD σ hH s t : F) ^ 2 := by
  rw [chiD]
  rfl

private theorem semilinear_Xa (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) {fa : F ≃+ F} (hfa : ActsOnXa σ fa)
    (s t : Fˣ) (a : F) :
    fa (((s * t⁻¹ : Fˣ) : F) * a) = (chiA σ hH s t : F) * fa a := by
  let hB : ↥(B0 F) := torB s t
  let xB : ↥(B0 F) := xaB a
  let xB' : ↥(B0 F) := xaB (((s * t⁻¹ : Fˣ) : F) * a)
  have hconj : hB * xB * hB⁻¹ = xB' := by
    apply Subtype.ext
    show dSp s t * uElt a 0 0 0 * (dSp s t)⁻¹ =
      uElt (((s * t⁻¹ : Fˣ) : F) * a) 0 0 0
    rw [dSp_conj_uElt, Units.val_inv_eq_inv_val]
    congr 1
    · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    · ring
    · ring
    · ring
  have hmap : ((σ hB : ↥(B0 F)) : antiSp F) * ((σ xB : ↥(B0 F)) : antiSp F) *
      ((σ hB : ↥(B0 F)) : antiSp F)⁻¹ = ((σ xB' : ↥(B0 F)) : antiSp F) := by
    have h := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) (congrArg σ hconj)
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hσh : ((σ hB : ↥(B0 F)) : antiSp F) = dSp (sigmaCoordsA σ hH s t)
      (sigmaCoordsD σ hH s t) := sigmaCoordsA_spec σ hH s t
  have hσx : ((σ xB : ↥(B0 F)) : antiSp F) = uElt (fa a) 0 0 0 := hfa a
  have hσx' : ((σ xB' : ↥(B0 F)) : antiSp F) =
      uElt (fa (((s * t⁻¹ : Fˣ) : F) * a)) 0 0 0 := hfa _
  rw [hσh, hσx, hσx'] at hmap
  have hleft : dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t) * uElt (fa a) 0 0 0 *
      (dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t))⁻¹ =
      uElt (((sigmaCoordsA σ hH s t * (sigmaCoordsD σ hH s t)⁻¹ : Fˣ) : F) * fa a) 0 0 0 := by
    rw [dSp_conj_uElt, Units.val_inv_eq_inv_val]
    congr 1
    · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    · ring
    · ring
    · ring
  rw [hleft] at hmap
  have hcoord := (uElt_inj hmap).1
  exact hcoord.symm

private theorem semilinear_Xb (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) {fb : F ≃+ F} (hfb : ActsOnXb σ fb)
    (s t : Fˣ) (d : F) :
    fb (((t ^ 2 : Fˣ) : F) * d) = (chiD σ hH s t : F) * fb d := by
  let hB : ↥(B0 F) := torB s t
  let xB : ↥(B0 F) := xbB d
  let xB' : ↥(B0 F) := xbB (((t ^ 2 : Fˣ) : F) * d)
  have hconj : hB * xB * hB⁻¹ = xB' := by
    apply Subtype.ext
    show dSp s t * uElt 0 0 0 d * (dSp s t)⁻¹ =
      uElt 0 0 0 (((t ^ 2 : Fˣ) : F) * d)
    rw [dSp_conj_uElt]
    congr 1
    · ring
    · ring
    · ring
  have hmap : ((σ hB : ↥(B0 F)) : antiSp F) * ((σ xB : ↥(B0 F)) : antiSp F) *
      ((σ hB : ↥(B0 F)) : antiSp F)⁻¹ = ((σ xB' : ↥(B0 F)) : antiSp F) := by
    have h := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) (congrArg σ hconj)
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hσh : ((σ hB : ↥(B0 F)) : antiSp F) = dSp (sigmaCoordsA σ hH s t)
      (sigmaCoordsD σ hH s t) := sigmaCoordsA_spec σ hH s t
  have hσx : ((σ xB : ↥(B0 F)) : antiSp F) = uElt 0 0 0 (fb d) := hfb d
  have hσx' : ((σ xB' : ↥(B0 F)) : antiSp F) =
      uElt 0 0 0 (fb (((t ^ 2 : Fˣ) : F) * d)) := hfb _
  rw [hσh, hσx, hσx'] at hmap
  have hleft : dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t) * uElt 0 0 0 (fb d) *
      (dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t))⁻¹ =
      uElt 0 0 0 ((((sigmaCoordsD σ hH s t) ^ 2 : Fˣ) : F) * fb d) := by
    rw [dSp_conj_uElt, Units.val_inv_eq_inv_val]
    congr 1
    · ring
    · ring
    · ring
  rw [hleft] at hmap
  have hcoord := (uElt_inj hmap).2.2.2
  exact hcoord.symm

private theorem chiA_eq_ring (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) {fa : F ≃+ F} (hfa : ActsOnXa σ fa)
    {ρa : F ≃+* F} (hρa : ∀ x : F, fa x = fa 1 * ρa x) (s t : Fˣ) :
    (chiA σ hH s t : F) = ρa (((s * t⁻¹ : Fˣ) : F)) := by
  have h1 := semilinear_Xa σ hH hfa s t 1
  rw [mul_one] at h1
  have h2 := hρa (((s * t⁻¹ : Fˣ) : F))
  have hfa1 : fa 1 ≠ 0 := fun h => one_ne_zero (fa.injective (by rw [h, map_zero]))
  have h3 : (chiA σ hH s t : F) * fa 1 = fa 1 * ρa (((s * t⁻¹ : Fˣ) : F)) := by
    rw [← h1, h2]
  have h4 : (chiA σ hH s t : F) * fa 1 = ρa (((s * t⁻¹ : Fˣ) : F)) * fa 1 := by
    rw [h3, mul_comm (fa 1)]
  exact mul_right_cancel₀ hfa1 h4

private theorem chiD_eq_ring (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) {fb : F ≃+ F} (hfb : ActsOnXb σ fb)
    {ρb : F ≃+* F} (hρb : ∀ x : F, fb x = fb 1 * ρb x) (s t : Fˣ) :
    (chiD σ hH s t : F) = ρb (((t ^ 2 : Fˣ) : F)) := by
  have h1 := semilinear_Xb σ hH hfb s t 1
  rw [mul_one] at h1
  have h2 := hρb (((t ^ 2 : Fˣ) : F))
  have hfb1 : fb 1 ≠ 0 := fun h => one_ne_zero (fb.injective (by rw [h, map_zero]))
  have h3 : (chiD σ hH s t : F) * fb 1 = fb 1 * ρb (((t ^ 2 : Fˣ) : F)) := by
    rw [← h1, h2]
  have h4 : (chiD σ hH s t : F) * fb 1 = ρb (((t ^ 2 : Fˣ) : F)) * fb 1 := by
    rw [h3, mul_comm (fb 1)]
  exact mul_right_cancel₀ hfb1 h4

private theorem center_action_criteria (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F) {fa : F ≃+ F} (hfa : ActsOnXa σ fa)
    {fb : F ≃+ F} (hfb : ActsOnXb σ fb)
    {ρa ρb : F ≃+* F} (hρa : ∀ x : F, fa x = fa 1 * ρa x)
    (hρb : ∀ x : F, fb x = fb 1 * ρb x)
    {b₀ c₀ : F} (hbc₀ : ((σ (zU1 (F := F)) : ↥(B0 F)) : antiSp F) = uElt 0 b₀ c₀ 0)
    (lam : Fˣ) :
    (sigmaCoordsA σ hH lam lam⁻¹ * sigmaCoordsD σ hH lam lam⁻¹ = 1 ∨ b₀ = 0) ∧
      (sigmaCoordsA σ hH lam lam⁻¹ = 1 ∨ c₀ = 0) ∧
      ((sigmaCoordsA σ hH lam lam⁻¹ : F) * (sigmaCoordsD σ hH lam lam⁻¹ : F)⁻¹ =
        ρa ((lam : F) ^ 2)) ∧
      ((sigmaCoordsD σ hH lam lam⁻¹ : F) ^ 2 = (ρb ((lam : F) ^ 2))⁻¹) := by
  have hspec : ((σ (torB lam lam⁻¹) : ↥(B0 F)) : antiSp F) =
      dSp (sigmaCoordsA σ hH lam lam⁻¹) (sigmaCoordsD σ hH lam lam⁻¹) :=
    sigmaCoordsA_spec σ hH lam lam⁻¹
  have hcomm : torB lam lam⁻¹ * zU1 = zU1 * torB lam lam⁻¹ := by
    apply Subtype.ext
    show dSp lam lam⁻¹ * uElt 0 1 0 0 = uElt 0 1 0 0 * dSp lam lam⁻¹
    exact (dSp_mul_uElt_comm_iff lam lam⁻¹ 0 1 0 0).mpr
      ⟨Or.inr rfl, Or.inl (mul_inv_cancel lam), Or.inr rfl, Or.inr rfl⟩
  have hcommσ : ((σ (torB lam lam⁻¹) : ↥(B0 F)) : antiSp F) *
      ((σ (zU1 (F := F)) : ↥(B0 F)) : antiSp F) =
      ((σ (zU1 (F := F)) : ↥(B0 F)) : antiSp F) *
        ((σ (torB lam lam⁻¹) : ↥(B0 F)) : antiSp F) := by
    have h := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) (congrArg σ hcomm)
    simpa only [map_mul, Subgroup.coe_mul] using h
  have hcrit := (dSp_mul_uElt_comm_iff (sigmaCoordsA σ hH lam lam⁻¹) (sigmaCoordsD σ hH lam lam⁻¹)
    0 b₀ c₀ 0).mp (by
      rw [← hspec, ← hbc₀]
      exact hcommσ)
  refine ⟨hcrit.2.1, hcrit.2.2.1, ?_, ?_⟩
  · have h := chiA_eq_ring σ hH hfa hρa lam lam⁻¹
    rw [chiA_apply σ hH lam lam⁻¹] at h
    rw [h]
    show ρa (((lam * (lam⁻¹)⁻¹ : Fˣ) : F)) = ρa ((lam : F) ^ 2)
    congr 1
    rw [inv_inv, Units.val_mul, pow_two]
  · have h := chiD_eq_ring σ hH hfb hρb lam lam⁻¹
    rw [chiD_apply σ hH lam lam⁻¹] at h
    rw [h]
    rw [← map_inv₀ ρb ((lam : F) ^ 2)]
    congr 1
    show (((lam⁻¹ : Fˣ) : F) ^ 2) = ((lam : F) ^ 2)⁻¹
    rw [Units.val_inv_eq_inv_val, inv_pow]

private theorem rho_eq_of_center_action (hF : 8 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hZ : (Z0B F).map σ.toMonoidHom = Z0B F)
    {fa fb : F ≃+ F} (hfa : ActsOnXa σ fa) (hfb : ActsOnXb σ fb)
    {ρa ρb : F ≃+* F} (hρa : ∀ x : F, fa x = fa 1 * ρa x)
    (hρb : ∀ x : F, fb x = fb 1 * ρb x) :
    ∀ x : F, ρa x = ρb x := by
  classical
  have hz1 : zU1 (F := F) ∈ Z0B F := zU1_mem
  have hw1 : σ (zU1 (F := F)) ∈ Z0B F := (iff_of_map_eq σ hZ (zU1 (F := F))).mp hz1
  obtain ⟨b₀, c₀, hbc₀⟩ := Subgroup.mem_subgroupOf.mp hw1
  have hw1_ne : σ (zU1 (F := F)) ≠ 1 := by
    intro h
    have hz_ne : zU1 (F := F) ≠ 1 := by
      intro hz
      have h' : (uElt (0 : F) 1 0 0 : antiSp F) = 1 := congrArg Subtype.val hz
      have h2 := uElt_inj (h'.trans uElt_zero_eq_one.symm)
      exact one_ne_zero h2.2.1
    exact hz_ne (σ.injective (h.trans (map_one σ).symm))
  have hbc₀_ne : ¬(b₀ = 0 ∧ c₀ = 0) := by
    rintro ⟨hb, hc⟩
    apply hw1_ne
    apply Subtype.ext
    rw [hbc₀, hb, hc]
    exact uElt_zero_eq_one
  by_cases hb₀ : b₀ = 0
  · exfalso
    have hc₀ : c₀ ≠ 0 := fun hc => hbc₀_ne ⟨hb₀, hc⟩
    have hsq : ∀ lam : Fˣ, ρb ((lam : F) ^ 2) = (ρa ((lam : F) ^ 2)) ^ 2 := by
      intro lam
      obtain ⟨-, hS1, hchiA, hchiD⟩ :=
        center_action_criteria σ hH hfa hfb hρa hρb hbc₀ lam
      have hS1' : sigmaCoordsA σ hH lam lam⁻¹ = 1 := hS1.resolve_right hc₀
      have hchiA' : (sigmaCoordsD σ hH lam lam⁻¹ : F)⁻¹ = ρa ((lam : F) ^ 2) := by
        rw [← hchiA, hS1']
        simp
      have hchiD' : (sigmaCoordsD σ hH lam lam⁻¹ : F) = (ρa ((lam : F) ^ 2))⁻¹ := by
        rw [← hchiA', inv_inv]
      have hlam_sq : (ρa ((lam : F) ^ 2)) ^ 2 = ρb ((lam : F) ^ 2) := by
        have h := hchiD
        rw [hchiD', inv_pow] at h
        exact eq_of_inv_eq_inv
          (pow_ne_zero 2 (ringEquiv_ne_zero_of_ne_zero ρa (pow_ne_zero 2 (Units.ne_zero lam))))
          (ringEquiv_ne_zero_of_ne_zero ρb (pow_ne_zero 2 (Units.ne_zero lam))) h
      exact hlam_sq.symm
    have hcube : ∀ τ : Fˣ, τ ≠ 1 → (ρa (τ : F)) ^ 3 = 1 := by
      intro τ hτ
      have hz2 : zU2 (F := F) ∈ Z0B F := zU2_mem
      have hw2 : σ (zU2 (F := F)) ∈ Z0B F := (iff_of_map_eq σ hZ (zU2 (F := F))).mp hz2
      obtain ⟨b₁, c₁, hbc₁⟩ := Subgroup.mem_subgroupOf.mp hw2
      have hw2_ne : σ (zU2 (F := F)) ≠ 1 := by
        intro h
        have hz_ne : zU2 (F := F) ≠ 1 := by
          intro hz
          have h' : (uElt (0 : F) 0 1 0 : antiSp F) = 1 := congrArg Subtype.val hz
          have h2 := uElt_inj (h'.trans uElt_zero_eq_one.symm)
          exact one_ne_zero h2.2.2.1
        exact hz_ne (σ.injective (h.trans (map_one σ).symm))
      have hbc₁_ne : ¬(b₁ = 0 ∧ c₁ = 0) := by
        rintro ⟨hb, hc⟩
        apply hw2_ne
        apply Subtype.ext
        rw [hbc₁, hb, hc]
        exact uElt_zero_eq_one
      have hspec : ((σ (torB 1 τ) : ↥(B0 F)) : antiSp F) =
          dSp (sigmaCoordsA σ hH 1 τ) (sigmaCoordsD σ hH 1 τ) :=
        sigmaCoordsA_spec σ hH 1 τ
      have hcomm : torB 1 τ * zU2 = zU2 * torB 1 τ := by
        apply Subtype.ext
        show dSp 1 τ * uElt 0 0 1 0 = uElt 0 0 1 0 * dSp 1 τ
        exact (dSp_mul_uElt_comm_iff 1 τ 0 0 1 0).mpr
          ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl, Or.inr rfl⟩
      have hcommσ : ((σ (torB 1 τ) : ↥(B0 F)) : antiSp F) *
          ((σ (zU2 (F := F)) : ↥(B0 F)) : antiSp F) =
          ((σ (zU2 (F := F)) : ↥(B0 F)) : antiSp F) *
            ((σ (torB 1 τ) : ↥(B0 F)) : antiSp F) := by
        have h := congrArg (fun z : ↥(B0 F) => (z : antiSp F)) (congrArg σ hcomm)
        simpa only [map_mul, Subgroup.coe_mul] using h
      have hcrit := (dSp_mul_uElt_comm_iff (sigmaCoordsA σ hH 1 τ) (sigmaCoordsD σ hH 1 τ)
        0 b₁ c₁ 0).mp (by
          rw [← hspec, ← hbc₁]
          exact hcommσ)
      have hchiA : (sigmaCoordsA σ hH 1 τ : F) * (sigmaCoordsD σ hH 1 τ : F)⁻¹ =
          ρa ((τ : F)⁻¹) := by
        have h := chiA_eq_ring σ hH hfa hρa 1 τ
        rw [chiA_apply σ hH 1 τ] at h
        rw [h]
        show ρa (((1 * τ⁻¹ : Fˣ) : F)) = ρa ((τ : F)⁻¹)
        congr 1
        rw [one_mul, Units.val_inv_eq_inv_val]
      have hchiD : (sigmaCoordsD σ hH 1 τ : F) ^ 2 = (ρa ((τ : F) ^ 2)) ^ 2 := by
        have h := chiD_eq_ring σ hH hfb hρb 1 τ
        rw [chiD_apply σ hH 1 τ] at h
        rw [h]
        exact hsq τ
      have hP2 : (sigmaCoordsD σ hH 1 τ : F) = ρa ((τ : F) ^ 2) :=
        CharTwo.sq_inj.mp hchiD
      have hρτ2 : ρa ((τ : F) ^ 2) ≠ 0 :=
        ringEquiv_ne_zero_of_ne_zero ρa (pow_ne_zero 2 (Units.ne_zero τ))
      have hP1 : (sigmaCoordsA σ hH 1 τ : F) = ρa (τ : F) := by
        have h1 : (sigmaCoordsA σ hH 1 τ : F) =
            ρa ((τ : F)⁻¹) * ρa ((τ : F) ^ 2) := by
          have := congrArg (fun x : F => x * ρa ((τ : F) ^ 2)) hchiA
          rw [hP2] at this
          simpa [mul_assoc, inv_mul_cancel₀ hρτ2] using this
        rw [h1, ← map_mul]
        congr 1
        have hτ0 : (τ : F) ≠ 0 := Units.ne_zero τ
        field_simp
      have hP1ne : (sigmaCoordsA σ hH 1 τ : F) ≠ 1 := by
        intro h1
        have h2 : ρa (τ : F) = 1 := by
          rw [← hP1, h1]
        have h3 : ρa (τ : F) = ρa 1 := by
          rw [h2]
          exact (map_one ρa).symm
        exact hτ (Units.ext (ρa.injective h3))
      have hc1 : c₁ = 0 := by
        rcases hcrit.2.2.1 with h | h
        · exact absurd (congrArg (fun u : Fˣ => (u : F)) h) hP1ne
        · exact h
      have hb1 : b₁ ≠ 0 := fun hb => hbc₁_ne ⟨hb, hc1⟩
      have hprod : (sigmaCoordsA σ hH 1 τ : F) *
          (sigmaCoordsD σ hH 1 τ : F) = 1 := by
        have h := hcrit.2.1.resolve_right hb1
        simpa using congrArg (fun u : Fˣ => (u : F)) h
      calc (ρa (τ : F)) ^ 3 = (ρa (τ : F)) * (ρa (τ : F)) ^ 2 := by ring
        _ = ρa (τ : F) * ρa ((τ : F) ^ 2) := by rw [map_pow]
        _ = (sigmaCoordsA σ hH 1 τ : F) * (sigmaCoordsD σ hH 1 τ : F) := by
            rw [← hP1, hP2]
        _ = 1 := hprod
    have h3all : ∀ u : Fˣ, u ^ 3 = 1 := by
      intro u
      obtain ⟨x, hx⟩ := ρa.surjective (u : F)
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hx
        exact Units.ne_zero u hx.symm
      let τ : Fˣ := Units.mk0 x hx0
      have hτval : (τ : F) = x := rfl
      by_cases hτ1 : τ = 1
      · have hx1 : x = 1 := by rw [← hτval, hτ1, Units.val_one]
        have hxu : (u : F) = 1 := by
          rw [← hx, hx1]
          simpa using map_one ρa
        have hu1 : u = 1 := Units.ext hxu
        rw [hu1]
        exact one_pow 3
      · have h := hcube τ hτ1
        rw [hτval, hx] at h
        apply Units.ext
        simpa using h
    have hcard3 : Nat.card Fˣ ≤ 3 := by
      haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
      have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h3all g)
      have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
      rw [hord] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    have h7 : 7 ≤ Nat.card Fˣ := by
      rw [Nat.card_units]
      omega
    omega
  · have key : ∀ lam : Fˣ, ρa ((lam : F) ^ 2) = ρb ((lam : F) ^ 2) := by
      intro lam
      obtain ⟨hST, -, hchiA, hchiD⟩ :=
        center_action_criteria σ hH hfa hfb hρa hρb hbc₀ lam
      have hST1 : (sigmaCoordsA σ hH lam lam⁻¹ : F) *
          (sigmaCoordsD σ hH lam lam⁻¹ : F) = 1 := by
        have h := hST.resolve_right hb₀
        simpa using congrArg (fun u : Fˣ => (u : F)) h
      have hρbne : ρb ((lam : F) ^ 2) ≠ 0 :=
        ringEquiv_ne_zero_of_ne_zero ρb (pow_ne_zero 2 (Units.ne_zero lam))
      have hD0 : (sigmaCoordsD σ hH lam lam⁻¹ : F) ≠ 0 := Units.ne_zero _
      have hprod : (1 : F) = ρa ((lam : F) ^ 2) * (ρb ((lam : F) ^ 2))⁻¹ := by
        calc (1 : F) = (sigmaCoordsA σ hH lam lam⁻¹ : F) *
            (sigmaCoordsD σ hH lam lam⁻¹ : F) := hST1.symm
          _ = ((sigmaCoordsA σ hH lam lam⁻¹ : F) *
                (sigmaCoordsD σ hH lam lam⁻¹ : F)⁻¹) *
                ((sigmaCoordsD σ hH lam lam⁻¹ : F) ^ 2) := by
              field_simp
          _ = ρa ((lam : F) ^ 2) * (ρb ((lam : F) ^ 2))⁻¹ := by rw [hchiA, hchiD]
      have hba : ρb ((lam : F) ^ 2) = ρa ((lam : F) ^ 2) := by
        have := congrArg (fun x : F => x * ρb ((lam : F) ^ 2)) hprod
        simpa [mul_assoc, inv_mul_cancel₀ hρbne] using this
      exact hba.symm
    have hunits : ∀ μ : Fˣ, ρa (μ : F) = ρb (μ : F) := by
      intro μ
      obtain ⟨τ, hτ⟩ := exists_unit_sq_eq μ
      have hval : (μ : F) = (τ : F) ^ 2 := by
        rw [← hτ]
        rfl
      rw [hval]
      exact key τ
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact hunits (Units.mk0 x hx)

private theorem dSp_conj_eq_self {h x : antiSp F} (hh : h ∈ dTor F) (hx : x ∈ dTor F) :
    h * x * h⁻¹ = x := by
  have hcomm := dTor_comm hh hx
  rw [hcomm]
  group

theorem exists_eq_conj_frobAut_pow_of_eight_le (hF : 8 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hT : (T0B F).map σ.toMonoidHom = T0B F)
    (hH : (HB F).map σ.toMonoidHom = HB F)
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F)
    (hA2 : (A2B F).map σ.toMonoidHom = A2B F) :
    ∃ (s t : Fˣ) (k : ℕ), ∀ b : ↥(B0 F),
      ((b : antiSp F) ∈ rootXa F ∨ (b : antiSp F) ∈ rootXb F ∨
        (b : antiSp F) ∈ dTor F) →
        ((σ b : ↥(B0 F)) : antiSp F) =
          (MulAut.conj (dSp s t) * frobAut F ^ k) (b : antiSp F) := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have hXa : (XaB F).map σ.toMonoidHom = XaB F := map_XaB_eq h4 σ hT hH hA1
  have hXb : (XbB F).map σ.toMonoidHom = XbB F := map_XbB_eq h4 σ hT hH hA2
  obtain ⟨fa, hfa⟩ := exists_addEquiv_of_map_mul (A := F)
    (fun a : F => xaB a)
    (by
      intro a b
      apply Subtype.ext
      show uElt (a + b) 0 0 0 = uElt a 0 0 0 * uElt b 0 0 0
      rw [uElt_mul]
      congr 1 <;> ring)
    (by
      intro a b h
      exact (uElt_inj (congrArg (fun z : ↥(B0 F) => (z : antiSp F)) h)).1)
    σ (by
      intro a
      have hmem : σ (xaB a) ∈ XaB F := by
        rw [← hXa]
        exact Subgroup.mem_map_of_mem σ.toMonoidHom (show xaB a ∈ XaB F from ⟨a, rfl⟩)
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, Subtype.ext hb⟩)
  have hfa' : ActsOnXa σ fa := fun a => congrArg Subtype.val (hfa a)
  obtain ⟨fb, hfb⟩ := exists_addEquiv_of_map_mul (A := F)
    (fun d : F => xbB d)
    (by
      intro a b
      apply Subtype.ext
      show uElt 0 0 0 (a + b) = uElt 0 0 0 a * uElt 0 0 0 b
      rw [uElt_mul]
      congr 1 <;> ring)
    (by
      intro a b h
      exact (uElt_inj (congrArg (fun z : ↥(B0 F) => (z : antiSp F)) h)).2.2.2)
    σ (by
      intro d
      have hmem : σ (xbB d) ∈ XbB F := by
        rw [← hXb]
        exact Subgroup.mem_map_of_mem σ.toMonoidHom (show xbB d ∈ XbB F from ⟨d, rfl⟩)
      obtain ⟨e, he⟩ := hmem
      exact ⟨e, Subtype.ext he⟩)
  have hfb' : ActsOnXb σ fb := fun d => congrArg Subtype.val (hfb d)
  have hfa1 : fa 1 ≠ 0 := fun h => one_ne_zero (fa.injective (by rw [h, map_zero]))
  have hmul_a : ∀ x y : F, fa (x * y) * fa 1 = fa x * fa y := by
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · let x' : Fˣ := Units.mk0 x hx
      have hx' : (x' : F) = x := rfl
      have e1 := semilinear_Xa σ hH hfa' x' 1 y
      have e2 := semilinear_Xa σ hH hfa' x' 1 1
      simp only [inv_one, mul_one] at e1 e2
      rw [hx'] at e1 e2
      rw [e1, e2]
      ring
  obtain ⟨ρa, hρa, -, -⟩ := exists_ringEquiv_of_map_mul fa.toAddMonoidHom
    fa.toAddMonoidHom ((AddMonoidHom.mulLeft (fa 1)⁻¹).comp fa.toAddMonoidHom)
    fa.bijective (by
      intro y t
      change fa (y * t) = fa y * ((fa 1)⁻¹ * fa t)
      field_simp
      exact hmul_a y t)
  have hρa' : ∀ x : F, fa x = fa 1 * ρa x := fun x => hρa x
  have hfb1 : fb 1 ≠ 0 := fun h => one_ne_zero (fb.injective (by rw [h, map_zero]))
  have hmul_b : ∀ x y : F, fb (x * y) * fb 1 = fb x * fb y := by
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · let x' : Fˣ := Units.mk0 x hx
      obtain ⟨τ, hτ⟩ := exists_unit_sq_eq x'
      have hx' : (x' : F) = x := rfl
      have hτ' : ((τ ^ 2 : Fˣ) : F) = x := by
        rw [hτ]
        exact hx'
      have e1 := semilinear_Xb σ hH hfb' 1 τ y
      have e2 := semilinear_Xb σ hH hfb' 1 τ 1
      simp only [one_pow, mul_one] at e2
      rw [hτ'] at e1 e2
      rw [e1, e2]
      ring
  obtain ⟨ρb, hρb, -, -⟩ := exists_ringEquiv_of_map_mul fb.toAddMonoidHom
    fb.toAddMonoidHom ((AddMonoidHom.mulLeft (fb 1)⁻¹).comp fb.toAddMonoidHom)
    fb.bijective (by
      intro y t
      change fb (y * t) = fb y * ((fb 1)⁻¹ * fb t)
      field_simp
      exact hmul_b y t)
  have hρb' : ∀ x : F, fb x = fb 1 * ρb x := fun x => hρb x
  have hZ : (Z0B F).map σ.toMonoidHom = Z0B F := map_Z0B σ hA1 hA2
  have hρeq : ∀ x : F, ρa x = ρb x :=
    rho_eq_of_center_action hF σ hH hZ hfa' hfb' hρa' hρb'
  obtain ⟨k, hk⟩ := CFSG.Quasithin.RonanF13.ringEquiv_eq_frobenius ρa
  obtain ⟨t₀, ht₀⟩ := exists_unit_sq_eq (F := F) (Units.mk0 (fb 1) hfb1)
  have ht₀' : (t₀ : F) ^ 2 = fb 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) ht₀
    simpa using this
  let fa1 : Fˣ := Units.mk0 (fa 1) hfa1
  let s₀ : Fˣ := fa1 * t₀
  have hs₀ : (s₀ : F) = fa 1 * (t₀ : F) := rfl
  have hs₀t₀ : (s₀ : F) * (t₀ : F)⁻¹ = fa 1 := by
    rw [hs₀, mul_assoc, mul_inv_cancel₀ (Units.ne_zero t₀), mul_one]
  have hρa_pow : ∀ x : F, ρa x = x ^ 2 ^ k := hk
  have hρb_pow : ∀ x : F, ρb x = x ^ 2 ^ k := fun x => by rw [← hρeq x, hk x]
  refine ⟨s₀, t₀, k, ?_⟩
  intro b hb
  rcases hb with hb | hb | hb
  ·
    obtain ⟨a, ha⟩ := hb
    have hb_eq : b = xaB a := Subtype.ext ha
    have hσ : (σ b : antiSp F) = uElt (fa a) 0 0 0 := by
      rw [hb_eq]
      exact hfa' a
    rw [hσ, hb_eq]
    show uElt (fa a) 0 0 0 =
      (MulAut.conj (dSp s₀ t₀) * frobAut F ^ k) (uElt a 0 0 0)
    rw [MulAut.mul_apply, MulAut.conj_apply, frobAut_pow_uElt, dSp_conj_uElt,
      Units.val_inv_eq_inv_val]
    congr 1
    · rw [hs₀t₀, hρa' a, hρa_pow a]
    · ring
    · ring
    · ring
  ·
    obtain ⟨d, hd⟩ := hb
    have hb_eq : b = xbB d := Subtype.ext hd
    have hσ : (σ b : antiSp F) = uElt 0 0 0 (fb d) := by
      rw [hb_eq]
      exact hfb' d
    rw [hσ, hb_eq]
    show uElt 0 0 0 (fb d) =
      (MulAut.conj (dSp s₀ t₀) * frobAut F ^ k) (uElt 0 0 0 d)
    rw [MulAut.mul_apply, MulAut.conj_apply, frobAut_pow_uElt, dSp_conj_uElt,
      Units.val_inv_eq_inv_val]
    congr 1
    · ring
    · ring
    · ring
    · rw [ht₀', ← hρb_pow d]
      exact hρb' d
  ·
    obtain ⟨s, t, hst⟩ := mem_dTor.mp hb
    have hb_eq : b = torB s t := Subtype.ext hst
    have hσ : ((σ b : ↥(B0 F)) : antiSp F) =
        dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t) := by
      rw [hb_eq]
      exact sigmaCoordsA_spec σ hH s t
    rw [hσ, hb_eq]
    show dSp (sigmaCoordsA σ hH s t) (sigmaCoordsD σ hH s t) =
      (MulAut.conj (dSp s₀ t₀) * frobAut F ^ k) (dSp s t)
    rw [MulAut.mul_apply, MulAut.conj_apply, frobAut_pow_dSp]
    rw [dSp_conj_eq_self (dSp_mem_dTor s₀ t₀) (dSp_mem_dTor (s ^ 2 ^ k) (t ^ 2 ^ k))]
    have h1 : (sigmaCoordsA σ hH s t : F) * (sigmaCoordsD σ hH s t : F)⁻¹ =
        (s ^ 2 ^ k : F) * ((t ^ 2 ^ k : F))⁻¹ := by
      have h := chiA_eq_ring σ hH hfa' hρa' s t
      rw [chiA_apply σ hH s t] at h
      rw [h]
      show ρa (((s * t⁻¹ : Fˣ) : F)) =
        (s ^ 2 ^ k : F) * ((t ^ 2 ^ k : F))⁻¹
      rw [show ((s * t⁻¹ : Fˣ) : F) = (s : F) * (t : F)⁻¹ from by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]]
      rw [hρa_pow, mul_pow, inv_pow]
    have h2 : (sigmaCoordsD σ hH s t : F) ^ 2 = ((t ^ 2 ^ k : F)) ^ 2 := by
      have h := chiD_eq_ring σ hH hfb' hρb' s t
      rw [chiD_apply σ hH s t] at h
      rw [h]
      show ρb ((t : F) ^ 2) = ((t : F) ^ 2 ^ k) ^ 2
      rw [← hρeq ((t : F) ^ 2), hρa_pow]
      exact (pow_two_pow (t : F) k).symm
    have hP := chi_inj (S := sigmaCoordsA σ hH s t) (T := sigmaCoordsD σ hH s t)
      (s := s ^ 2 ^ k) (t := t ^ 2 ^ k) h1 h2
    rw [hP.1, hP.2]

end CFSG.Quasithin.F112R.St84

end

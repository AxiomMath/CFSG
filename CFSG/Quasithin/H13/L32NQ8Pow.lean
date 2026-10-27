module

public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

namespace Q8Pow

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {a x : G} (ha : orderOf a = 2)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem mem_cent_iff {g a : G} : g ∈ Subgroup.centralizer {a} ↔ ⁅g, a⁆ = 1 := by
  rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]

theorem closure_le_centralizer_closure {S T : Set G} (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro t ht
  have hle : Subgroup.closure T ≤ Subgroup.centralizer {s} := by
    rw [Subgroup.closure_le]
    intro t' ht'
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h s hs t' ht').symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ht)

structure CommPair (z : G) (C : Subgroup G) : Prop where
  z_mem : z ∈ C
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_comm : ∀ c ∈ C, c * z = z * c
  comm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z
  sq : ∀ c ∈ C, c * c = 1 ∨ c * c = z

structure SympPair (z : G) (C : Subgroup G) : Prop extends CommPair z C where
  center : ∀ c ∈ C, (∀ d ∈ C, c * d = d * c) → c = 1 ∨ c = z

namespace CommPair

variable {z : G} {C : Subgroup G} (S : CommPair z C)
include S

theorem orderOf_z : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact S.z_sq) S.z_ne

theorem central {w : G} (hw : w = 1 ∨ w = z) {c : G} (hc : c ∈ C) : c * w = w * c := by
  rcases hw with rfl | rfl
  · rw [mul_one, one_mul]
  · exact S.z_comm c hc

theorem comm_mul_left {a b c : G} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have h1 := S.central (S.comm b hb c hc)
    (C.mul_mem (C.mul_mem hc (C.inv_mem ha)) (C.inv_mem hc))
  calc ⁅a * b, c⁆ = a * (⁅b, c⁆ * (c * a⁻¹ * c⁻¹)) := by
        simp only [commutatorElement_def]; group
    _ = a * ((c * a⁻¹ * c⁻¹) * ⁅b, c⁆) := by rw [h1]
    _ = ⁅a, c⁆ * ⁅b, c⁆ := by simp only [commutatorElement_def]; group

theorem comm_mul_right {a b c : G} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h1 := S.central (S.comm a ha c hc) (C.inv_mem hb)
  calc ⁅a, b * c⁆ = a * b * a⁻¹ * (⁅a, c⁆ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = a * b * a⁻¹ * (b⁻¹ * ⁅a, c⁆) := by rw [h1]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by simp only [commutatorElement_def]; group

theorem comm_symm {a b : G} (ha : a ∈ C) (hb : b ∈ C) : ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv]
  rcases S.comm a ha b hb with h | h <;> rw [h]
  · exact inv_one
  · exact inv_eq_of_mul_eq_one_right S.z_sq

theorem decomp {a b : G} (ha : a ∈ C) (hb : b ∈ C) (hab : ⁅a, b⁆ = z) {c : G} (hc : c ∈ C) :
    ∃ e ∈ C ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b},
      c = e ∨ c = e * a⁻¹ ∨ c = e * b⁻¹ ∨ c = e * b⁻¹ * a⁻¹ := by
  have hba : ⁅b, a⁆ = z := by rw [S.comm_symm ha hb]; exact hab
  have haa : ⁅a, a⁆ = 1 := commutatorElement_self a
  have hbb : ⁅b, b⁆ = 1 := commutatorElement_self b
  have mem : ∀ e ∈ C, ⁅e, a⁆ = 1 → ⁅e, b⁆ = 1 →
      e ∈ C ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := fun e he h1 h2 =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨he, mem_cent_iff.mpr h1⟩, mem_cent_iff.mpr h2⟩
  rcases S.comm c hc a ha with h1 | h1 <;> rcases S.comm c hc b hb with h2 | h2
  · exact ⟨c, mem c hc h1 h2, Or.inl rfl⟩
  · refine ⟨c * a, mem _ (C.mul_mem hc ha) ?_ ?_, Or.inr (Or.inl (by group))⟩
    · rw [S.comm_mul_left hc ha ha, h1, haa, mul_one]
    · rw [S.comm_mul_left hc ha hb, h2, hab, S.z_sq]
  · refine ⟨c * b, mem _ (C.mul_mem hc hb) ?_ ?_, Or.inr (Or.inr (Or.inl (by group)))⟩
    · rw [S.comm_mul_left hc hb ha, h1, hba, S.z_sq]
    · rw [S.comm_mul_left hc hb hb, h2, hbb, mul_one]
  · refine ⟨c * a * b, mem _ (C.mul_mem (C.mul_mem hc ha) hb) ?_ ?_,
      Or.inr (Or.inr (Or.inr (by group)))⟩
    · rw [S.comm_mul_left (C.mul_mem hc ha) hb ha, S.comm_mul_left hc ha ha, h1, haa, hba,
        mul_one, S.z_sq]
    · rw [S.comm_mul_left (C.mul_mem hc ha) hb hb, S.comm_mul_left hc ha hb, h2, hab, hbb,
        S.z_sq, mul_one]

theorem card_eq_two_mul [Finite G] {D : Subgroup G} (hD : D ≤ C) {x y : G} (hx : x ∈ D)
    (hy : y ∈ C) (hxy : ⁅x, y⁆ = z) :
    Nat.card D = 2 * Nat.card ↥(D ⊓ Subgroup.centralizer {y}) := by
  have hidx : ((D ⊓ Subgroup.centralizer {y}).subgroupOf D).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hx⟩, fun d => ?_⟩
    have hd : (d : G) ∈ C := hD d.2
    have hmul : ((d * ⟨x, hx⟩ : ↥D) : G) = (d : G) * x := rfl
    rcases S.comm (d : G) hd y hy with h | h
    · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨d.2, mem_cent_iff.mpr h⟩), fun hm => ?_⟩
      have h2 := mem_cent_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hm)).2
      rw [hmul, S.comm_mul_left hd (hD hx) hy, h, hxy, one_mul] at h2
      exact S.z_ne h2
    · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨(d * ⟨x, hx⟩).2, mem_cent_iff.mpr ?_⟩), fun hm => ?_⟩
      · rw [hmul, S.comm_mul_left hd (hD hx) hy, h, hxy, S.z_sq]
      · have h2 := mem_cent_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hm)).2
        rw [h] at h2
        exact S.z_ne h2
  have h1 := Subgroup.card_mul_index ((D ⊓ Subgroup.centralizer {y}).subgroupOf D)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  omega

theorem card_peel [Finite G] {a b : G} (ha : a ∈ C) (hb : b ∈ C) (hab : ⁅a, b⁆ = z) :
    Nat.card C = 4 * Nat.card ↥(C ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := by
  have h1 := S.card_eq_two_mul le_rfl hb ha (by rw [S.comm_symm ha hb]; exact hab)
  have h2 := S.card_eq_two_mul (inf_le_left : C ⊓ Subgroup.centralizer {a} ≤ C)
    (Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) hb hab
  omega

theorem eq_zpowers [Finite G] (h : ∀ c ∈ C, c = 1 ∨ c = z) : C = Subgroup.zpowers z := by
  refine le_antisymm (fun c hc => ?_) (Subgroup.zpowers_le.mpr S.z_mem)
  rcases h c hc with rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

theorem exists_ne_of_two_lt [Finite G] {B : Subgroup G} (hB : 2 < Nat.card B) :
    ∃ a ∈ B, a ≠ 1 ∧ a ≠ z := by
  by_contra hne
  push Not at hne
  have hle : B ≤ Subgroup.zpowers z := fun b hb => by
    by_cases h1 : b = 1
    · rw [h1]
      exact one_mem _
    · rw [hne b hb h1]
      exact Subgroup.mem_zpowers z
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, S.orderOf_z] at this
  omega

omit S in
theorem mono (S : CommPair z C) {C₁ : Subgroup G} (hle : C₁ ≤ C) (hz : z ∈ C₁) :
    CommPair z C₁ where
  z_mem := hz
  z_ne := S.z_ne
  z_sq := S.z_sq
  z_comm c hc := S.z_comm c (hle hc)
  comm a ha b hb := S.comm a (hle ha) b (hle hb)
  sq c hc := S.sq c (hle hc)

end CommPair

namespace SympPair

variable {z : G} {C : Subgroup G} (S : SympPair z C)
include S

theorem exists_comm_eq {a : G} (ha : a ∈ C) (ha1 : a ≠ 1) (haz : a ≠ z) :
    ∃ b ∈ C, ⁅a, b⁆ = z := by
  by_contra hne
  push Not at hne
  refine (S.center a ha fun d hd => ?_).elim ha1 haz
  rw [← commutatorElement_eq_one_iff_mul_comm]
  exact (S.comm a ha d hd).resolve_right (hne d hd)

theorem exists_inv_partner {a : G} (ha : a ∈ C) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haa : a * a = 1) : ∃ b ∈ C, b * b = 1 ∧ ⁅a, b⁆ = z := by
  obtain ⟨b, hb, hab⟩ := S.exists_comm_eq ha ha1 haz
  rcases S.sq b hb with hbb | hbb
  · exact ⟨b, hb, hbb, hab⟩
  refine ⟨b * a, C.mul_mem hb ha, ?_, ?_⟩
  · have h1 : a * b = z * (b * a) := by
      rw [← hab]
      simp only [commutatorElement_def]
      group
    calc b * a * (b * a) = b * (a * b) * a := by group
      _ = b * (z * (b * a)) * a := by rw [h1]
      _ = (b * z) * (b * (a * a)) := by group
      _ = (z * b) * (b * (a * a)) := by rw [S.z_comm b hb]
      _ = z * (b * b) * (a * a) := by group
      _ = 1 := by rw [hbb, haa, S.z_sq, mul_one]
  · rw [S.comm_mul_right ha hb ha, hab, commutatorElement_self, mul_one]

theorem sympPair_inf {a b : G} (ha : a ∈ C) (hb : b ∈ C) (hab : ⁅a, b⁆ = z) :
    SympPair z (C ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) where
  z_mem := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨S.z_mem,
    Subgroup.mem_centralizer_singleton_iff.mpr (S.z_comm a ha).symm⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (S.z_comm b hb).symm⟩
  z_ne := S.z_ne
  z_sq := S.z_sq
  z_comm c hc := S.z_comm c (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1
  comm a' ha' b' hb' := S.comm a' (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha').1).1 b'
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb').1).1
  sq c hc := S.sq c (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1
  center c hc h := by
    obtain ⟨hc1, hcb⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hcC, hca⟩ := Subgroup.mem_inf.mp hc1
    refine S.center c hcC fun d hd => ?_
    obtain ⟨e, he, hde⟩ := S.decomp ha hb hab hd
    have hca' : Commute c a := Subgroup.mem_centralizer_singleton_iff.mp hca
    have hcb' : Commute c b := Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hce : Commute c e := h e he
    rcases hde with rfl | rfl | rfl | rfl
    · exact hce
    · exact hce.mul_right hca'.inv_right
    · exact hce.mul_right hcb'.inv_right
    · exact (hce.mul_right hcb'.inv_right).mul_right hca'.inv_right

end SympPair

theorem SympPair.card_eq_aux [Finite G] {z : G} :
    ∀ (n : ℕ) (C : Subgroup G), SympPair z C → Nat.card C ≤ n → ∃ k : ℕ, Nat.card C = 2 * 4 ^ k
  | 0, C, _, hn => absurd hn (by have := Nat.card_pos (α := C); omega)
  | n + 1, C, S, hn => by
    by_cases hall : ∀ c ∈ C, c = 1 ∨ c = z
    · refine ⟨0, ?_⟩
      rw [S.eq_zpowers hall, Nat.card_zpowers, S.orderOf_z]
      norm_num
    push Not at hall
    obtain ⟨a, ha, ha1, haz⟩ := hall
    obtain ⟨b, hb, hab⟩ := S.exists_comm_eq ha ha1 haz
    have hc := S.card_peel ha hb hab
    have hpos := Nat.card_pos (α := ↥(C ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}))
    obtain ⟨k, hk⟩ := SympPair.card_eq_aux n _ (S.sympPair_inf ha hb hab) (by omega)
    exact ⟨k + 1, by rw [hc, hk, pow_succ]; ring⟩

theorem SympPair.card_eq [Finite G] {z : G} {C : Subgroup G} (S : SympPair z C) :
    ∃ k : ℕ, Nat.card C = 2 * 4 ^ k :=
  SympPair.card_eq_aux _ C S le_rfl

section Quaternion

variable {x y : G}

theorem pow_mul_eq (hyx : y⁻¹ * x * y = x⁻¹) (k : ℕ) : x ^ k * y = y * x ^ (-(k : ℤ)) := by
  have h : y⁻¹ * x ^ k * y = (x ^ k)⁻¹ := by
    have := map_pow (MulAut.conj y⁻¹) x k
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hyx, inv_pow]
  calc x ^ k * y = y * (y⁻¹ * x ^ k * y) := by group
    _ = y * x ^ (-(k : ℤ)) := by rw [h, zpow_neg, zpow_natCast]

theorem pow_val_eq (h4 : x ^ 4 = 1) (i : ZMod 4) (m : ℤ) (hm : (m : ZMod 4) = i) :
    x ^ i.val = x ^ m := by
  have h4' : x ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, h4]
  rw [zpow_eq_zpow_emod m h4', ← hm, ← zpow_natCast]
  congr 1
  exact ZMod.val_intCast m

@[expose] def quatHom (h4 : x ^ 4 = 1) (hyy : y * y = x * x) (hyx : y⁻¹ * x * y = x⁻¹) :
    QuaternionGroup 2 →* G where
  toFun g := match g with
    | .a i => x ^ i.val
    | .xa i => y * x ^ i.val
  map_one' := by
    show x ^ (0 : ZMod (2 * 2)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · show x ^ (i + j).val = x ^ i.val * x ^ j.val
      rw [pow_val_eq h4 (i + j) ((i.val : ℤ) + j.val) (by push_cast [ZMod.natCast_zmod_val]; rfl),
        zpow_add, zpow_natCast, zpow_natCast]
    · show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      rw [pow_val_eq h4 (j - i) (-(i.val : ℤ) + j.val)
        (by push_cast [ZMod.natCast_zmod_val]; ring), ← mul_assoc, pow_mul_eq hyx]
      group
    · show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [pow_val_eq h4 (i + j) ((i.val : ℤ) + j.val) (by push_cast [ZMod.natCast_zmod_val]; rfl)]
      group
    · show x ^ ((2 : ℕ) + j - i : ZMod (2 * 2)).val = y * x ^ i.val * (y * x ^ j.val)
      rw [pow_val_eq h4 _ (2 + (j.val : ℤ) - i.val)
        (by push_cast [ZMod.natCast_zmod_val]; ring)]
      calc x ^ (2 + (j.val : ℤ) - i.val) = (x * x) * x ^ (-(i.val : ℤ)) * x ^ j.val := by
            group
        _ = (y * y) * x ^ (-(i.val : ℤ)) * x ^ j.val := by rw [hyy]
        _ = y * (y * x ^ (-(i.val : ℤ))) * x ^ j.val := by group
        _ = y * (x ^ i.val * y) * x ^ j.val := by rw [pow_mul_eq hyx]
        _ = y * x ^ i.val * (y * x ^ j.val) := by group

theorem quatHom_injective (h4 : x ^ 4 = 1) (hyy : y * y = x * x) (hyx : y⁻¹ * x * y = x⁻¹)
    (hx2 : x * x ≠ 1) : Function.Injective (quatHom h4 hyy hyx) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · change x ^ i.val = 1 at h
    have hlt := ZMod.val_lt i
    have hv : i.val = 0 := by
      rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3) with hv | hv | hv | hv
      · exact hv
      · exfalso
        rw [hv, pow_one] at h
        exact hx2 (by rw [h, one_mul])
      · exfalso
        rw [hv, pow_two] at h
        exact hx2 h
      · exfalso
        rw [hv] at h
        have hx1 : x = 1 := by
          calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
            _ = 1 := by rw [h4, h, inv_one, one_mul]
        exact hx2 (by rw [hx1, one_mul])
    rw [(ZMod.val_eq_zero i).mp hv]
    rfl
  · change y * x ^ i.val = 1 at h
    exfalso
    have hy : y = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hc : y⁻¹ * x * y = x := by
      rw [hy, inv_inv]
      group
    rw [hyx] at hc
    apply hx2
    calc x * x = x * x⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel x

theorem exists_quatHom {z : G} (hxx : x * x = z) (hyy : y * y = z) (hz : z ≠ 1)
    (hzz : z * z = 1) (hxy : ⁅x, y⁆ = z) :
    ∃ φ : QuaternionGroup 2 →* G, Function.Injective φ ∧ φ.range = Subgroup.closure {x, y} ∧
      φ (QuaternionGroup.a 1) = x ∧ φ (QuaternionGroup.xa 0) = y ∧
      φ (QuaternionGroup.a 2) = z := by
  have hzy : y * z = z * y := by rw [← hyy]; group
  have h4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hxx, hzz]
  have hyy' : y * y = x * x := by rw [hyy, hxx]
  have h1 : x * y = z * (y * x) := by
    rw [← hxy]
    simp only [commutatorElement_def]
    group
  have hyx : y⁻¹ * x * y = x⁻¹ := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (z * (y * x)) := by rw [h1]
      _ = y⁻¹ * (z * y) * x := by group
      _ = y⁻¹ * (y * z) * x := by rw [hzy]
      _ = (x * x) * x := by rw [← hxx]; group
      _ = x ^ 4 * x⁻¹ := by simp only [pow_succ, pow_zero, one_mul, mul_inv_cancel_right]
      _ = x⁻¹ := by rw [h4, one_mul]
  have hinj := quatHom_injective h4 hyy' hyx (by rw [hxx]; exact hz)
  have hφ1 : quatHom h4 hyy' hyx (QuaternionGroup.a 1) = x := by
    show x ^ (1 : ZMod (2 * 2)).val = x
    rw [show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  have hφ0 : quatHom h4 hyy' hyx (QuaternionGroup.xa 0) = y := by
    show y * x ^ (0 : ZMod (2 * 2)).val = y
    rw [ZMod.val_zero, pow_zero, mul_one]
  have hφ2 : quatHom h4 hyy' hyx (QuaternionGroup.a 2) = z := by
    show x ^ (2 : ZMod (2 * 2)).val = z
    rw [show (2 : ZMod (2 * 2)).val = 2 from rfl, pow_two, hxx]
  have hrange : (quatHom h4 hyy' hyx).range = Subgroup.closure {x, y} := by
    have hxm : x ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert x {y})
    have hym : y ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rcases g with i | i
      · exact Subgroup.pow_mem _ hxm _
      · exact Subgroup.mul_mem _ hym (Subgroup.pow_mem _ hxm _)
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨QuaternionGroup.a 1, hφ1⟩
      · rw [Set.mem_singleton_iff.mp hw]
        exact ⟨QuaternionGroup.xa 0, hφ0⟩
  exact ⟨quatHom h4 hyy' hyx, hinj, hrange, hφ1, hφ0, hφ2⟩

theorem nonempty_closure_mulEquiv_q8 {z : G} (hxx : x * x = z) (hyy : y * y = z) (hz : z ≠ 1)
    (hzz : z * z = 1) (hxy : ⁅x, y⁆ = z) :
    Nonempty (↥(Subgroup.closure {x, y}) ≃* QuaternionGroup 2) := by
  obtain ⟨φ, hinj, hrange, -⟩ := exists_quatHom hxx hyy hz hzz hxy
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

end Quaternion

theorem exists_q8_family [Finite G] {z : G} :
    ∀ (j : ℕ) (C A : Subgroup G), SympPair z C → z ∈ A → A ≤ C →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a * a = 1) →
      Nat.card A = 2 ^ (2 * j + 1) → Nat.card C = 2 ^ (4 * j + 1) →
      ∃ Q : Fin (2 * j) → Subgroup G, (∀ i, Q i ≤ C) ∧
        (∀ i i', i ≠ i' → Q i ≤ Subgroup.centralizer (Q i' : Set G)) ∧
        (∀ i, Nonempty (↥(Q i) ≃* QuaternionGroup 2)) ∧ (∀ i, z ∈ Q i) ∧
        C ≤ (⨆ i, Q i) ⊔ Subgroup.zpowers z
  | 0, C, A, S, _, _, _, _, _, hC => by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_⟩
    have heq : Subgroup.zpowers z = C := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr S.z_mem) (by rw [hC, Nat.card_zpowers, S.orderOf_z]; norm_num)
    rw [← heq]
    exact le_sup_right
  | j + 1, C, A, S, hzA, hAC, hAc, hA2, hA, hC => by
    have eA : 2 ^ (2 * (j + 1) + 1) = 4 * 2 ^ (2 * j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]
      ring
    have eC : 2 ^ (4 * (j + 1) + 1) = 16 * 2 ^ (4 * j + 1) := by
      rw [show 4 * (j + 1) + 1 = (4 * j + 1) + 4 by ring, pow_add]
      ring
    have hXA : 1 ≤ 2 ^ (2 * j + 1) := Nat.one_le_two_pow
    rw [eA] at hA
    rw [eC] at hC
    obtain ⟨a₁, ha₁A, ha₁1, ha₁z⟩ := S.exists_ne_of_two_lt (B := A) (by omega)
    have ha₁C := hAC ha₁A
    obtain ⟨b₁, hb₁C, hb₁b₁, hab₁⟩ := S.exists_inv_partner ha₁C ha₁1 ha₁z (hA2 a₁ ha₁A)
    have S₁ := S.sympPair_inf ha₁C hb₁C hab₁
    have hcard₁ := S.card_peel ha₁C hb₁C hab₁
    have hcardA₁ := S.card_eq_two_mul hAC ha₁A hb₁C hab₁
    have hA₁C₁ : A ⊓ Subgroup.centralizer {b₁} ≤
        C ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {b₁} := fun x hx =>
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hAC (Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_centralizer_singleton_iff.mpr (hAc x (Subgroup.mem_inf.mp hx).1 a₁ ha₁A)⟩,
        (Subgroup.mem_inf.mp hx).2⟩
    have hzA₁ : z ∈ A ⊓ Subgroup.centralizer {b₁} := Subgroup.mem_inf.mpr
      ⟨hzA, Subgroup.mem_centralizer_singleton_iff.mpr (S.z_comm b₁ hb₁C).symm⟩
    obtain ⟨a₂, ha₂A₁, ha₂1, ha₂z⟩ := S₁.exists_ne_of_two_lt (B := A ⊓ Subgroup.centralizer {b₁})
      (by omega)
    have ha₂C₁ := hA₁C₁ ha₂A₁
    have ha₂A : a₂ ∈ A := (Subgroup.mem_inf.mp ha₂A₁).1
    obtain ⟨b₂, hb₂C₁, hb₂b₂, hab₂⟩ := S₁.exists_inv_partner ha₂C₁ ha₂1 ha₂z (hA2 a₂ ha₂A)
    have S₂ := S₁.sympPair_inf ha₂C₁ hb₂C₁ hab₂
    have hcard₂ := S₁.card_peel ha₂C₁ hb₂C₁ hab₂
    have hcardA₂ := S₁.card_eq_two_mul hA₁C₁ ha₂A₁ hb₂C₁ hab₂
    have hA₂C₂ : A ⊓ Subgroup.centralizer {b₁} ⊓ Subgroup.centralizer {b₂} ≤
        C ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {b₁} ⊓ Subgroup.centralizer {a₂} ⊓
          Subgroup.centralizer {b₂} := fun x hx =>
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hA₁C₁ (Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (hAc x (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1 a₂ ha₂A)⟩,
        (Subgroup.mem_inf.mp hx).2⟩
    have hzA₂ : z ∈ A ⊓ Subgroup.centralizer {b₁} ⊓ Subgroup.centralizer {b₂} :=
      Subgroup.mem_inf.mpr ⟨hzA₁, Subgroup.mem_centralizer_singleton_iff.mpr
        (S₁.z_comm b₂ hb₂C₁).symm⟩
    obtain ⟨Q', hQ'C, hQ'c, hQ'i, hQ'z, hQ'g⟩ := exists_q8_family j _ _ S₂ hzA₂ hA₂C₂
      (fun a ha b hb => hAc a (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1 b
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).1)
      (fun a ha => hA2 a (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1)
      (by omega) (by omega)
    obtain ⟨⟨hb₂C, hb₂a₁⟩, hb₂b₁⟩ := Subgroup.mem_inf.mp hb₂C₁ |>.imp_left Subgroup.mem_inf.mp
    obtain ⟨⟨ha₂C, ha₂a₁⟩, ha₂b₁⟩ := Subgroup.mem_inf.mp ha₂C₁ |>.imp_left Subgroup.mem_inf.mp
    have ca₂a₁ : Commute a₂ a₁ := Subgroup.mem_centralizer_singleton_iff.mp ha₂a₁
    have ca₂b₁ : Commute a₂ b₁ := Subgroup.mem_centralizer_singleton_iff.mp ha₂b₁
    have cb₂a₁ : Commute b₂ a₁ := Subgroup.mem_centralizer_singleton_iff.mp hb₂a₁
    have cb₂b₁ : Commute b₂ b₁ := Subgroup.mem_centralizer_singleton_iff.mp hb₂b₁
    have ia₁ : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right (hA2 a₁ ha₁A)
    have ib₁ : b₁⁻¹ = b₁ := inv_eq_of_mul_eq_one_right hb₁b₁
    have ia₂ : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right (hA2 a₂ ha₂A)
    have ib₂ : b₂⁻¹ = b₂ := inv_eq_of_mul_eq_one_right hb₂b₂
    have hba₁ : ⁅b₁, a₁⁆ = z := by rw [S.comm_symm ha₁C hb₁C]; exact hab₁
    have hba₂ : ⁅b₂, a₂⁆ = z := by rw [S.comm_symm ha₂C hb₂C]; exact hab₂
    have cx₂a₁ : Commute (a₂ * b₂) a₁ := ca₂a₁.mul_left cb₂a₁
    have cx₂b₁ : Commute (a₂ * b₂) b₁ := ca₂b₁.mul_left cb₂b₁
    have cx₂x₁ : Commute (a₂ * b₂) (a₁ * b₁) := cx₂a₁.mul_right cx₂b₁
    have cx₁a₂ : Commute (a₁ * b₁) a₂ := (ca₂a₁.mul_right ca₂b₁).symm
    have hx₁C : a₁ * b₁ ∈ C := C.mul_mem ha₁C hb₁C
    have hx₂C : a₂ * b₂ ∈ C := C.mul_mem ha₂C hb₂C
    have hy₁C : a₁ * (a₂ * b₂) ∈ C := C.mul_mem ha₁C hx₂C
    have hy₂C : a₁ * b₁ * a₂ ∈ C := C.mul_mem hx₁C ha₂C
    have hx₁x₁ : a₁ * b₁ * (a₁ * b₁) = z := by
      rw [← hab₁, commutatorElement_def, ia₁, ib₁]
      group
    have hx₂x₂ : a₂ * b₂ * (a₂ * b₂) = z := by
      rw [← hab₂, commutatorElement_def, ia₂, ib₂]
      group
    have hy₁y₁ : a₁ * (a₂ * b₂) * (a₁ * (a₂ * b₂)) = z := by
      calc a₁ * (a₂ * b₂) * (a₁ * (a₂ * b₂)) = a₁ * ((a₂ * b₂) * a₁) * (a₂ * b₂) := by group
        _ = a₁ * (a₁ * (a₂ * b₂)) * (a₂ * b₂) := by rw [cx₂a₁.eq]
        _ = (a₁ * a₁) * ((a₂ * b₂) * (a₂ * b₂)) := by group
        _ = z := by rw [hA2 a₁ ha₁A, hx₂x₂, one_mul]
    have hy₂y₂ : a₁ * b₁ * a₂ * (a₁ * b₁ * a₂) = z := by
      calc a₁ * b₁ * a₂ * (a₁ * b₁ * a₂) = (a₁ * b₁) * (a₂ * (a₁ * b₁)) * a₂ := by group
        _ = (a₁ * b₁) * ((a₁ * b₁) * a₂) * a₂ := by rw [cx₁a₂.eq]
        _ = (a₁ * b₁) * (a₁ * b₁) * (a₂ * a₂) := by group
        _ = z := by rw [hA2 a₂ ha₂A, hx₁x₁, mul_one]
    have hcx₁y₁ : ⁅a₁ * b₁, a₁ * (a₂ * b₂)⁆ = z := by
      rw [S.comm_mul_right hx₁C ha₁C hx₂C, S.comm_mul_left ha₁C hb₁C ha₁C,
        commutatorElement_self, hba₁, one_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr cx₂x₁.eq.symm, mul_one]
    have hcx₂y₂ : ⁅a₂ * b₂, a₁ * b₁ * a₂⁆ = z := by
      rw [S.comm_mul_right hx₂C hx₁C ha₂C, S.comm_mul_left ha₂C hb₂C ha₂C,
        commutatorElement_self, hba₂, one_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr cx₂x₁.eq, one_mul]
    have hcy₁y₂ : ⁅a₁ * (a₂ * b₂), a₁ * b₁ * a₂⁆ = 1 := by
      rw [S.comm_mul_left ha₁C hx₂C hy₂C, S.comm_mul_right ha₁C hx₁C ha₂C,
        S.comm_mul_right hx₂C hx₁C ha₂C, S.comm_mul_right ha₁C ha₁C hb₁C,
        S.comm_mul_left ha₂C hb₂C ha₂C, commutatorElement_self, commutatorElement_self, hab₁,
        hba₂, commutatorElement_eq_one_iff_mul_comm.mpr ca₂a₁.eq.symm,
        commutatorElement_eq_one_iff_mul_comm.mpr cx₂x₁.eq]
      simp only [one_mul, mul_one]
      exact S.z_sq
    set Q₁ := Subgroup.closure ({a₁ * b₁, a₁ * (a₂ * b₂)} : Set G) with hQ₁
    set Q₂ := Subgroup.closure ({a₂ * b₂, a₁ * b₁ * a₂} : Set G) with hQ₂
    have hx₁Q₁ : a₁ * b₁ ∈ Q₁ := Subgroup.subset_closure (Set.mem_insert _ _)
    have hy₁Q₁ : a₁ * (a₂ * b₂) ∈ Q₁ :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hx₂Q₂ : a₂ * b₂ ∈ Q₂ := Subgroup.subset_closure (Set.mem_insert _ _)
    have hy₂Q₂ : a₁ * b₁ * a₂ ∈ Q₂ :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hQ₁C : Q₁ ≤ C := by
      rw [hQ₁, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hx₁C
      · exact hy₁C
    have hQ₂C : Q₂ ≤ C := by
      rw [hQ₂, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hx₂C
      · exact hy₂C
    have hQ₁Q₂ : Q₁ ≤ Subgroup.centralizer (Q₂ : Set G) := by
      refine closure_le_centralizer_closure ?_
      rintro s (rfl | rfl) t (rfl | rfl)
      · exact cx₂x₁.eq.symm
      · exact (Commute.refl (a₁ * b₁)).mul_right cx₁a₂
      · exact (cx₂a₁.symm.mul_left (Commute.refl (a₂ * b₂))).eq
      · exact (commutatorElement_eq_one_iff_mul_comm.mp hcy₁y₂)
    have hQ₂Q₁ : Q₂ ≤ Subgroup.centralizer (Q₁ : Set G) :=
      Subgroup.le_centralizer_iff.mp hQ₁Q₂
    have hC₂c : ∀ q ∈ C ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {b₁} ⊓
        Subgroup.centralizer {a₂} ⊓ Subgroup.centralizer {b₂},
        Commute q a₁ ∧ Commute q b₁ ∧ Commute q a₂ ∧ Commute q b₂ := by
      intro q hq
      obtain ⟨hq1, hqb₂⟩ := Subgroup.mem_inf.mp hq
      obtain ⟨hq2, hqa₂⟩ := Subgroup.mem_inf.mp hq1
      obtain ⟨hq3, hqb₁⟩ := Subgroup.mem_inf.mp hq2
      obtain ⟨-, hqa₁⟩ := Subgroup.mem_inf.mp hq3
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mp hqa₁,
        Subgroup.mem_centralizer_singleton_iff.mp hqb₁,
        Subgroup.mem_centralizer_singleton_iff.mp hqa₂,
        Subgroup.mem_centralizer_singleton_iff.mp hqb₂⟩
    have hQ₁Q' : ∀ k, Q₁ ≤ Subgroup.centralizer (Q' k : Set G) := by
      intro k
      rw [hQ₁, Subgroup.closure_le]
      rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
        intro q hq <;> obtain ⟨c₁, c₂, c₃, c₄⟩ := hC₂c q (hQ'C k hq)
      · exact (c₁.mul_right c₂).eq
      · exact (c₁.mul_right (c₃.mul_right c₄)).eq
    have hQ₂Q' : ∀ k, Q₂ ≤ Subgroup.centralizer (Q' k : Set G) := by
      intro k
      rw [hQ₂, Subgroup.closure_le]
      rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
        intro q hq <;> obtain ⟨c₁, c₂, c₃, c₄⟩ := hC₂c q (hQ'C k hq)
      · exact (c₃.mul_right c₄).eq
      · exact ((c₁.mul_right c₂).mul_right c₃).eq
    refine ⟨Fin.cons Q₁ (Fin.cons Q₂ Q'), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hQ₁C
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact hQ₂C
        · exact (hQ'C k).trans (le_trans inf_le_left (le_trans inf_le_left
            (le_trans inf_le_left inf_le_left)))
    · intro i i' hii'
      induction i using Fin.cases with
      | zero =>
        induction i' using Fin.cases with
        | zero => exact absurd rfl hii'
        | succ i' =>
          induction i' using Fin.cases with
          | zero => exact hQ₁Q₂
          | succ k => exact hQ₁Q' k
      | succ i =>
        induction i using Fin.cases with
        | zero =>
          induction i' using Fin.cases with
          | zero => exact hQ₂Q₁
          | succ i' =>
            induction i' using Fin.cases with
            | zero => exact absurd rfl hii'
            | succ k => exact hQ₂Q' k
        | succ k =>
          induction i' using Fin.cases with
          | zero => exact Subgroup.le_centralizer_iff.mp (hQ₁Q' k)
          | succ i' =>
            induction i' using Fin.cases with
            | zero => exact Subgroup.le_centralizer_iff.mp (hQ₂Q' k)
            | succ k' =>
              exact hQ'c k k' fun h => hii' (by rw [h])
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact nonempty_closure_mulEquiv_q8 hx₁x₁ hy₁y₁ S.z_ne S.z_sq hcx₁y₁
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact nonempty_closure_mulEquiv_q8 hx₂x₂ hy₂y₂ S.z_ne S.z_sq hcx₂y₂
        · exact hQ'i k
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · show z ∈ Q₁
        rw [← hx₁x₁]
        exact Q₁.mul_mem hx₁Q₁ hx₁Q₁
      · refine Fin.cases ?_ (fun k => ?_) i
        · show z ∈ Q₂
          rw [← hx₂x₂]
          exact Q₂.mul_mem hx₂Q₂ hx₂Q₂
        · exact hQ'z k
    · set Q : Fin (2 * j + 1 + 1) → Subgroup G := Fin.cons Q₁ (Fin.cons Q₂ Q') with hQ
      set K := (⨆ i, Q i) ⊔ Subgroup.zpowers z with hK
      have hQ₁K : Q₁ ≤ K := le_sup_left.trans' (le_iSup Q 0)
      have hQ₂K : Q₂ ≤ K := le_sup_left.trans' (le_iSup Q 1)
      have hQ'K : ∀ k, Q' k ≤ K := fun k => le_sup_left.trans' (le_iSup Q k.succ.succ)
      have ha₁K : a₁ ∈ K := by
        have : a₁ = a₁ * (a₂ * b₂) * (a₂ * b₂)⁻¹ := by group
        rw [this]
        exact K.mul_mem (hQ₁K hy₁Q₁) (K.inv_mem (hQ₂K hx₂Q₂))
      have hb₁K : b₁ ∈ K := by
        have : b₁ = a₁⁻¹ * (a₁ * b₁) := by group
        rw [this]
        exact K.mul_mem (K.inv_mem ha₁K) (hQ₁K hx₁Q₁)
      have ha₂K : a₂ ∈ K := by
        have : a₂ = (a₁ * b₁)⁻¹ * (a₁ * b₁ * a₂) := by group
        rw [this]
        exact K.mul_mem (K.inv_mem (hQ₁K hx₁Q₁)) (hQ₂K hy₂Q₂)
      have hb₂K : b₂ ∈ K := by
        have : b₂ = a₂⁻¹ * (a₂ * b₂) := by group
        rw [this]
        exact K.mul_mem (K.inv_mem ha₂K) (hQ₂K hx₂Q₂)
      have hC₂K : C ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {b₁} ⊓
          Subgroup.centralizer {a₂} ⊓ Subgroup.centralizer {b₂} ≤ K :=
        hQ'g.trans (sup_le (iSup_le fun k => hQ'K k) le_sup_right)
      intro c hc
      obtain ⟨e₁, he₁, hce⟩ := S.decomp ha₁C hb₁C hab₁ hc
      obtain ⟨e₂, he₂, hee⟩ := S₁.decomp ha₂C₁ hb₂C₁ hab₂ he₁
      have he₂K := hC₂K he₂
      have he₁K : e₁ ∈ K := by
        rcases hee with rfl | rfl | rfl | rfl
        · exact he₂K
        · exact K.mul_mem he₂K (K.inv_mem ha₂K)
        · exact K.mul_mem he₂K (K.inv_mem hb₂K)
        · exact K.mul_mem (K.mul_mem he₂K (K.inv_mem hb₂K)) (K.inv_mem ha₂K)
      rcases hce with rfl | rfl | rfl | rfl
      · exact he₁K
      · exact K.mul_mem he₁K (K.inv_mem ha₁K)
      · exact K.mul_mem he₁K (K.inv_mem hb₁K)
      · exact K.mul_mem (K.mul_mem he₁K (K.inv_mem hb₁K)) (K.inv_mem ha₁K)

theorem sympPair_of_extraspecial [Finite G] {U : Subgroup G}
    (hU : CFSG.IsExtraspecialPGroup 2 ↥U) : ∃ z : G, SympPair z U ∧ z ∈ centerOf U := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := hU
  have : Nontrivial (Subgroup.center ↥U) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨⟨z', hz'c⟩, hz'⟩ := exists_ne (1 : Subgroup.center ↥U)
  have hz'1 : z' ≠ 1 := fun h => hz' (Subtype.ext h)
  have hord : orderOf z' = 2 := by
    have hdvd : orderOf z' ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk z' hz'c]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'1
    · exact h
  have hzc : Subgroup.zpowers z' = Subgroup.center ↥U := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hz'c) (by rw [hcard, Nat.card_zpowers, hord])
  have hcen : ∀ w ∈ Subgroup.center ↥U, w = 1 ∨ w = z' := fun w hw =>
    eq_one_or_eq_of_mem_zpowers hord (hzc ▸ hw)
  have hcen' : ∀ w : ↥U, w ∈ Subgroup.center ↥U → (w : G) = 1 ∨ (w : G) = z' := by
    intro w hw
    rcases hcen w hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hpow := (CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hp).2.2.1
  refine ⟨z', ⟨⟨z'.2, fun h => hz'1 (Subtype.ext h), ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · have := pow_orderOf_eq_one z'
    rw [hord, pow_two] at this
    exact congrArg Subtype.val this
  · intro c hc
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨c, hc⟩)
  · intro a ha b hb
    have hm : ⁅(⟨a, ha⟩ : ↥U), ⟨b, hb⟩⁆ ∈ Subgroup.center ↥U := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have := hcen' _ hm
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · intro c hc
    have hm : (⟨c, hc⟩ : ↥U) ^ 2 ∈ Subgroup.center ↥U := by
      rw [← hfrat, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hpow _
    have := hcen' _ hm
    simpa only [pow_two, Subgroup.coe_mul] using this
  · intro c hc h
    refine hcen' ⟨c, hc⟩ (Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_)
    exact (h g g.2).symm
  · refine Subgroup.mem_inf.mpr ⟨z'.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨g, hg⟩)

theorem card_eq_of_extraspecial [Finite G] {U : Subgroup G}
    (hU : CFSG.IsExtraspecialPGroup 2 ↥U) : ∃ k : ℕ, Nat.card U = 2 ^ (2 * k + 1) := by
  obtain ⟨z, S, -⟩ := sympPair_of_extraspecial hU
  obtain ⟨k, hk⟩ := S.card_eq
  exact ⟨k, by rw [hk, pow_succ, pow_mul]; norm_num; ring⟩

theorem isQ8CentralPow_of_elemAbelian [Finite G] {U A : Subgroup G}
    (hU : CFSG.IsExtraspecialPGroup 2 ↥U) (hAU : A ≤ U) (hZA : centerOf U ≤ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1) {j : ℕ} (hj : 0 < j)
    (hA : Nat.card A = 2 ^ (2 * j + 1)) (hUc : Nat.card U = 2 ^ (4 * j + 1)) :
    IsQ8CentralPow (2 * j) ↥U := by
  obtain ⟨z, S, hzZ⟩ := sympPair_of_extraspecial hU
  obtain ⟨Q, hQU, hQc, hQi, hQz, hgen⟩ := exists_q8_family j U A S (hZA hzZ) hAU hAc hA2 hA hUc
  have hsup : (⨆ i, Q i) ⊔ Subgroup.zpowers z = ⨆ i, Q i := by
    refine sup_eq_left.mpr (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_iSup_of_mem ⟨0, by omega⟩ (hQz _)
  refine ⟨by rw [hUc]; ring_nf, fun i => (Q i).subgroupOf U, ?_, ?_, ?_⟩
  · intro i i' h u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hQc i i' h (Subgroup.mem_subgroupOf.mp hu))
      v (Subgroup.mem_subgroupOf.mp hv))
  · rw [eq_top_iff]
    intro u _
    have hu : (u : G) ∈ ⨆ i, Q i := hsup ▸ hgen u.2
    have hmap : (⨆ i, (Q i).subgroupOf U).map U.subtype = ⨆ i, Q i := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun i => ?_
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hQU i)]
    rw [← hmap] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    rwa [Subtype.ext hvu] at hv
  · intro i
    obtain ⟨e⟩ := hQi i
    exact ⟨(Subgroup.subgroupOfEquivOfLe (hQU i)).trans e⟩

end Q8Pow

end CFSG.Quasithin.H13

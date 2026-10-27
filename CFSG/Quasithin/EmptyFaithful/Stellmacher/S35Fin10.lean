module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def IsElemAb (A : Subgroup (Perm (Fin 5))) : Prop :=
  (∀ a ∈ A, a * a = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

@[expose] def invF : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => g ≠ 1 ∧ g * g = 1

theorem mem_invF {g : Perm (Fin 5)} : g ∈ invF ↔ g ≠ 1 ∧ g * g = 1 := by
  simp [invF]

@[expose] def sqF : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => g * g = 1

theorem mem_sqF {g : Perm (Fin 5)} : g ∈ sqF ↔ g * g = 1 := by
  simp [sqF]

@[expose] def kl (x y : Perm (Fin 5)) : Finset (Perm (Fin 5)) := {1, x, y, x * y}

theorem kl_mul' : ∀ x ∈ sqF, ∀ y ∈ sqF, x * y = y * x →
    ∀ a ∈ kl x y, ∀ b ∈ kl x y, a * b ∈ kl x y := by
  intro x hx y hy hc a ha b hb
  rw [mem_sqF] at hx hy
  have hc' : y * x = x * y := hc.symm
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hy' : ∀ z, y * (y * z) = z := fun z => by rw [← mul_assoc, hy, one_mul]
  have hc'' : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hc', mul_assoc]
  simp only [kl, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [mul_one, one_mul, mul_assoc, hx, hy, hc', hx', hy', hc'', eq_self_iff_true,
      true_or, or_true]

theorem kl_sq' : ∀ x ∈ sqF, ∀ y ∈ sqF, x * y = y * x → ∀ a ∈ kl x y, a * a = 1 := by
  intro x hx y hy hc a ha
  rw [mem_sqF] at hx hy
  have hc' : y * x = x * y := hc.symm
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hy' : ∀ z, y * (y * z) = z := fun z => by rw [← mul_assoc, hy, one_mul]
  have hc'' : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hc', mul_assoc]
  simp only [kl, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp only [mul_one, one_mul, mul_assoc, hx, hy, hc', hx', hy', hc'']

theorem kl_mul {x y : Perm (Fin 5)} (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x) :
    ∀ a ∈ kl x y, ∀ b ∈ kl x y, a * b ∈ kl x y :=
  kl_mul' x (mem_sqF.mpr hx) y (mem_sqF.mpr hy) hc

theorem kl_sq {x y : Perm (Fin 5)} (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x) :
    ∀ a ∈ kl x y, a * a = 1 :=
  kl_sq' x (mem_sqF.mpr hx) y (mem_sqF.mpr hy) hc

theorem no_third : ∀ x ∈ invF, ∀ y ∈ invF, ∀ a ∈ invF, x ≠ y → x * y = y * x → a * x = x * a →
    a * y = y * a → a ∈ kl x y := by
  unfold kl invF; decide +kernel

theorem mem_closure_pair {x y : Perm (Fin 5)} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) (a : Perm (Fin 5)) :
    a ∈ Subgroup.closure ({x, y} : Set (Perm (Fin 5))) ↔ a ∈ kl x y := by
  constructor
  · intro ha
    induction ha using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · simp [kl]
      · simp [kl]
    | one => simp [kl]
    | mul a b _ _ ha hb => exact kl_mul hx hy hc a ha b hb
    | inv a _ ha =>
      have := kl_sq hx hy hc a ha
      rw [inv_eq_of_mul_eq_one_right this]; exact ha
  · intro ha
    have hx' : x ∈ Subgroup.closure ({x, y} : Set (Perm (Fin 5))) :=
      Subgroup.subset_closure (by simp)
    have hy' : y ∈ Subgroup.closure ({x, y} : Set (Perm (Fin 5))) :=
      Subgroup.subset_closure (by simp)
    simp only [kl, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hx'
    · exact hy'
    · exact Subgroup.mul_mem _ hx' hy'

theorem elemAb_cases {A : Subgroup (Perm (Fin 5))} (hA : IsElemAb A) :
    A = ⊥ ∨ (∃ x, x ≠ 1 ∧ x * x = 1 ∧ A = Subgroup.zpowers x) ∨
      (∃ x y, x ≠ y ∧ x ≠ 1 ∧ y ≠ 1 ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧
        A = Subgroup.closure ({x, y} : Set (Perm (Fin 5)))) := by
  by_cases hbot : ∀ a ∈ A, a = 1
  · left; exact (Subgroup.eq_bot_iff_forall A).mpr hbot
  right
  push Not at hbot
  obtain ⟨x, hxA, hx1⟩ := hbot
  have hxx := hA.1 x hxA
  by_cases hcyc : ∀ a ∈ A, a ∈ Subgroup.zpowers x
  · left
    refine ⟨x, hx1, hxx, le_antisymm hcyc ?_⟩
    rw [Subgroup.zpowers_le]; exact hxA
  right
  push Not at hcyc
  obtain ⟨y, hyA, hyx⟩ := hcyc
  have hyy := hA.1 y hyA
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hc := hA.2 x hxA y hyA
  refine ⟨x, y, hxy, hx1, hy1, hxx, hyy, hc, ?_⟩
  apply le_antisymm
  · intro a ha
    rw [mem_closure_pair hxx hyy hc]
    by_cases ha1 : a = 1
    · simp [kl, ha1]
    · exact no_third x (mem_invF.mpr ⟨hx1, hxx⟩) y (mem_invF.mpr ⟨hy1, hyy⟩) a
        (mem_invF.mpr ⟨ha1, hA.1 a ha⟩) hxy hc (hA.2 a ha x hxA) (hA.2 a ha y hyA)
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxA
    · exact hyA

set_option synthInstance.maxSize 2000 in
theorem quadKl_iff : ∀ x ∈ invF, ∀ y ∈ invF, x ≠ y → x * y = y * x →
    ((∀ a ∈ kl x y, ∀ w ∈ spanF (commGensF orth (kl x y) Finset.univ), orth.act a w = w) ↔
      (Perm.sign x ≠ 1 ∨ Perm.sign y ≠ 1)) := by
  unfold kl invF; decide +kernel

theorem isQuad_closure_pair_iff {x y : Perm (Fin 5)} (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hxx : x * x = 1) (hyy : y * y = 1) (hc : x * y = y * x) :
    IsQuad (Subgroup.closure ({x, y} : Set (Perm (Fin 5)))) ↔
      (Perm.sign x ≠ 1 ∨ Perm.sign y ≠ 1) := by
  rw [← quadKl_iff x (mem_invF.mpr ⟨hx1, hxx⟩) y (mem_invF.mpr ⟨hy1, hyy⟩) hxy hc]
  have hB : ∀ σ, σ ∈ Subgroup.closure ({x, y} : Set (Perm (Fin 5))) ↔ σ ∈ kl x y :=
    mem_closure_pair hxx hyy hc
  unfold IsQuad
  constructor
  · intro h a ha w hw
    refine h a ((hB a).mpr ha) w ?_
    exact (mem_commW_iff orth hB (fun u => by simp) w).mpr hw
  · intro h a ha w hw
    refine h a ((hB a).mp ha) w ?_
    exact (mem_commW_iff orth hB (fun u => by simp) w).mp hw

theorem isQuad_bot : IsQuad ⊥ := by
  intro a ha w _
  rw [Subgroup.mem_bot.mp ha, map_one]; rfl

theorem isQuad_zpowers {x : Perm (Fin 5)} (hx : x * x = 1) : IsQuad (Subgroup.zpowers x) := by
  have key : ∀ x : Perm (Fin 5), x * x = 1 → ∀ w ∈ commF x, orth.act x w = w := by
    unfold commF; decide +kernel
  intro a ha w hw
  rw [mem_zpowers_iff_of_mul_self hx] at ha
  rw [mem_commW_zpowers_iff] at hw
  rcases ha with rfl | rfl
  · rw [map_one]; rfl
  · exact key _ hx w hw

theorem kl_eq_left : ∀ x ∈ sqF, ∀ y ∈ sqF, x * y = y * x → kl x y = kl x (x * y) := by
  unfold kl sqF; decide +kernel

theorem kl_eq_right : ∀ x ∈ sqF, ∀ y ∈ sqF, x * y = y * x → kl x y = kl y (x * y) := by
  unfold kl sqF; decide +kernel

theorem closure_pair_congr {x y s t : Perm (Fin 5)} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s)
    (h : kl x y = kl s t) :
    Subgroup.closure ({x, y} : Set (Perm (Fin 5))) =
      Subgroup.closure ({s, t} : Set (Perm (Fin 5))) := by
  ext a
  rw [mem_closure_pair hx hy hc, mem_closure_pair hs ht hst, h]

theorem isSwap_iff_mul_self {g : Perm (Fin 5)} :
    g.IsSwap ↔ g ≠ 1 ∧ g * g = 1 ∧ Perm.sign g ≠ 1 := by
  rw [isSwap_iff, pow_two]

theorem sign_ne_one_mul {x y : Perm (Fin 5)} (hx : Perm.sign x ≠ 1) (hy : Perm.sign y = 1) :
    Perm.sign (x * y) ≠ 1 := by
  rw [Perm.sign_mul, hy, mul_one]; exact hx

theorem sign_ne_one_mul' {x y : Perm (Fin 5)} (hx : Perm.sign x = 1) (hy : Perm.sign y ≠ 1) :
    Perm.sign (x * y) ≠ 1 := by
  rw [Perm.sign_mul, hx, one_mul]; exact hy

theorem exists_swaps_of_klein {x y : Perm (Fin 5)} (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hxx : x * x = 1) (hyy : y * y = 1) (hc : x * y = y * x)
    (hs : Perm.sign x ≠ 1 ∨ Perm.sign y ≠ 1) :
    ∃ s t : Perm (Fin 5), s ≠ t ∧ s * t = t * s ∧ s.IsSwap ∧ t.IsSwap ∧
      Subgroup.closure ({x, y} : Set (Perm (Fin 5))) =
      Subgroup.closure ({s, t} : Set (Perm (Fin 5))) := by
  have hxm := mem_sqF.mpr hxx
  have hym := mem_sqF.mpr hyy
  have hxy1 : x * y ≠ 1 := fun h => hxy (by
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [h, one_mul])
  have hxyx : x * y ≠ x := fun h => hy1 (by
    calc y = x * (x * y) := by rw [← mul_assoc, hxx, one_mul]
      _ = x * x := by rw [h]
      _ = 1 := hxx)
  have hxyy : x * y ≠ y := fun h => hx1 (by
    calc x = (x * y) * y := by rw [mul_assoc, hyy, mul_one]
      _ = y * y := by rw [h]
      _ = 1 := hyy)
  have hxyxy : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * (x * y)) := by rw [mul_assoc]
      _ = x * ((y * x) * y) := by rw [mul_assoc]
      _ = x * ((x * y) * y) := by rw [hc]
      _ = x * (x * (y * y)) := by rw [mul_assoc]
      _ = 1 := by rw [hyy, mul_one, hxx]
  by_cases hsx : Perm.sign x ≠ 1
  · by_cases hsy : Perm.sign y ≠ 1
    · exact ⟨x, y, hxy, hc, isSwap_iff_mul_self.mpr ⟨hx1, hxx, hsx⟩,
        isSwap_iff_mul_self.mpr ⟨hy1, hyy, hsy⟩, rfl⟩
    · have hsy' : Perm.sign y = 1 := not_not.mp hsy
      refine ⟨x, x * y, fun h => hxyx h.symm, ?_, isSwap_iff_mul_self.mpr ⟨hx1, hxx, hsx⟩,
        isSwap_iff_mul_self.mpr ⟨hxy1, hxyxy, sign_ne_one_mul hsx hsy'⟩, ?_⟩
      · calc x * (x * y) = (x * x) * y := by rw [mul_assoc]
          _ = y * (x * x) := by rw [hxx, one_mul, mul_one]
          _ = (y * x) * x := by rw [mul_assoc]
          _ = (x * y) * x := by rw [hc]
      · exact closure_pair_congr hxx hyy hc hxx hxyxy (by
          calc x * (x * y) = (x * x) * y := by rw [mul_assoc]
            _ = y * (x * x) := by rw [hxx, one_mul, mul_one]
            _ = (y * x) * x := by rw [mul_assoc]
            _ = (x * y) * x := by rw [hc]) (kl_eq_left x hxm y hym hc)
  · have hsx' : Perm.sign x = 1 := not_not.mp hsx
    have hsy : Perm.sign y ≠ 1 := hs.resolve_left hsx
    refine ⟨y, x * y, fun h => hxyy h.symm, ?_, isSwap_iff_mul_self.mpr ⟨hy1, hyy, hsy⟩,
      isSwap_iff_mul_self.mpr ⟨hxy1, hxyxy, sign_ne_one_mul' hsx' hsy⟩, ?_⟩
    · calc y * (x * y) = (y * x) * y := by rw [mul_assoc]
        _ = (x * y) * y := by rw [hc]
    · exact closure_pair_congr hxx hyy hc hyy hxyxy (by
        calc y * (x * y) = (y * x) * y := by rw [mul_assoc]
          _ = (x * y) * y := by rw [hc]) (kl_eq_right x hxm y hym hc)

theorem isQuad_elemAb_iff {A : Subgroup (Perm (Fin 5))} (hA : IsElemAb A) :
    IsQuad A ↔ A = ⊥ ∨ (∃ x, x ≠ 1 ∧ x * x = 1 ∧ A = Subgroup.zpowers x) ∨
      (∃ s t : Perm (Fin 5), s ≠ t ∧ s * t = t * s ∧ s.IsSwap ∧ t.IsSwap ∧
        A = Subgroup.closure ({s, t} : Set (Perm (Fin 5)))) := by
  constructor
  · intro hq
    rcases elemAb_cases hA with h | h | ⟨x, y, hxy, hx1, hy1, hxx, hyy, hc, hAeq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      rw [hAeq] at hq
      have hs := (isQuad_closure_pair_iff hx1 hy1 hxy hxx hyy hc).mp hq
      obtain ⟨s, t, hst, hc', hs1, ht1, hcl⟩ := exists_swaps_of_klein hx1 hy1 hxy hxx hyy hc hs
      exact ⟨s, t, hst, hc', hs1, ht1, hAeq.trans hcl⟩
  · rintro (h | ⟨x, -, hx, rfl⟩ | ⟨s, t, hst, hc, hs, ht, rfl⟩)
    · rw [h]; exact isQuad_bot
    · exact isQuad_zpowers hx
    · obtain ⟨hs1, hss, hs3⟩ := isSwap_iff_mul_self.mp hs
      obtain ⟨ht1, htt, -⟩ := isSwap_iff_mul_self.mp ht
      exact (isQuad_closure_pair_iff hs1 ht1 hst hss htt hc).mpr (Or.inl hs3)

end CFSG.Quasithin.F53.Stellmacher.S35.Fin

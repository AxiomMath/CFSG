module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3
public import CFSG.Permutation.FinPackDec

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

namespace QuadK

open CFSG.Permutation.FinPack

@[expose] def e5 : ℕ := 274960

theorem e5_enc : enc (1 : Perm (Fin 5)) = e5 := by
  unfold e5
  decide +kernel

theorem hn5 : 5 ≤ 16 := by norm_num

@[expose] def crd (w : orth.W) (i : Fin 5) : ZMod 2 :=
  Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 i

theorem crd_act (σ : Perm (Fin 5)) (w : orth.W) (i : Fin 5) :
    crd (orth.act σ w) i = crd w (σ⁻¹ i) := rfl

theorem crd_mul (v w : orth.W) (i : Fin 5) : crd (v * w) i = crd v i + crd w i := rfl

theorem crd_inv (w : orth.W) (i : Fin 5) : crd w⁻¹ i = -crd w i := rfl

@[expose] def epv (j m t : Fin 5) : ZMod 2 := (if t = j then 1 else 0) + (if t = m then 1 else 0)

theorem crd_ep (j m t : Fin 5) : crd (ep j m) t = epv j m t := rfl

theorem crd_ext {v w : orth.W} (h : ∀ i, crd v i = crd w i) : v = w := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  exact h i

abbrev pairUp (p q r s : Fin 5) : Prop := (p = q ∧ r = s) ∨ (p = r ∧ q = s) ∨ (p = s ∧ q = r)

theorem oddW : ∀ p q r s : Fin 5, ¬ pairUp p q r s →
    ∃ j m : Fin 5, epv j m p + -epv j m q ≠ epv j m r + -epv j m s := by
  decide +kernel

theorem zmod2_swap : ∀ x y : ZMod 2, x + -y = y + -x := by decide

theorem zmod2_cancel : ∀ x y : ZMod 2, x + -x = y + -y := by decide

theorem gens_iff_pairUp (a b : Perm (Fin 5)) :
    (∀ u : orth.W, orth.act a (orth.act b u * u⁻¹) = orth.act b u * u⁻¹) ↔
      ∀ i : Fin 5, pairUp (b⁻¹ (a⁻¹ i)) (a⁻¹ i) (b⁻¹ i) i := by
  constructor
  · intro h i
    by_contra hp
    obtain ⟨j, m, hne⟩ := oddW _ _ _ _ hp
    have h1 := congrArg (fun w => crd w i) (h (ep j m))
    simp only [crd_act, crd_mul, crd_inv, crd_ep] at h1
    exact hne h1
  · intro h u
    refine crd_ext fun i => ?_
    simp only [crd_act, crd_mul, crd_inv]
    rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact zmod2_cancel _ _
    · rw [h1, h2]
    · rw [h1, h2]
      exact zmod2_swap _ _

set_option synthInstance.maxSize 2000 in
theorem quad_iff_pairs (K : Finset (Perm (Fin 5))) :
    (∀ a ∈ K, ∀ w ∈ spanF (commGensF orth K Finset.univ), orth.act a w = w) ↔
      ∀ a ∈ K, ∀ b ∈ K, ∀ i : Fin 5, pairUp (b⁻¹ (a⁻¹ i)) (a⁻¹ i) (b⁻¹ i) i := by
  constructor
  · intro h a ha b hb
    refine (gens_iff_pairUp a b).1 fun u => h a ha _ (subset_spanF _ _ ?_)
    exact Finset.mem_image.2 ⟨(b, u), Finset.mem_product.2 ⟨hb, Finset.mem_univ _⟩, rfl⟩
  · intro h a ha w hw
    rw [← closure_eq_spanF orth.sq] at hw
    induction hw using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨⟨b, u⟩, hbu, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
      exact (gens_iff_pairUp a b).2 (h a ha b (Finset.mem_product.1 hbu).1) u
    | one => exact map_one _
    | mul v w _ _ hv hw => rw [map_mul, hv, hw]
    | inv v _ hv => rw [map_inv, hv]

@[expose] noncomputable def pairK (p q r s : ℕ) : Bool :=
  (Nat.beq p q && Nat.beq r s) || (Nat.beq p r && Nat.beq q s) || (Nat.beq p s && Nat.beq q r)

@[expose] noncomputable def pK (a b : ℕ) : Bool :=
  allLtK (fun i => pairK (rd (invCK 5 b) (rd (invCK 5 a) i)) (rd (invCK 5 a) i) (rd (invCK 5 b) i)
    i) 5

@[expose] noncomputable def klK (c d : ℕ) : List ℕ := [e5, c, d, mulK 5 c d]

@[expose] noncomputable def allP (c d : ℕ) : Bool :=
  allK (fun a => allK (fun b => pK a b) (klK c d)) (klK c d)

@[expose] def invL : List ℕ :=
  [213520, 271120, 144400, 274720, 213280, 266800, 136240, 78400, 74560, 274945, 213505, 271105,
    144385, 274450, 213010, 266290, 77890, 262675, 132115, 262435, 66115, 12820, 8980, 12580, 4660]

theorem inv_walk : walkK 5 (fun c => Nat.beq c e5 || !Nat.beq (mulK 5 c c) e5 || memK c invL) 5
    0 0 0 = true := by
  decide +kernel

theorem quad_walk : walkK 5 (fun c => Nat.beq c e5 || !Nat.beq (mulK 5 c c) e5 ||
    allK (fun d => Nat.beq c d || !Nat.beq (mulK 5 c d) (mulK 5 d c) ||
      (allP c d == (!evenK 5 c || !evenK 5 d))) invL) 5 0 0 0 = true := by
  decide +kernel

theorem pairK_iff (p q r s : Fin 5) : pairK p q r s = true ↔ pairUp p q r s := by
  simp only [pairK, pairUp, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Fin.val_inj, or_assoc]

theorem pK_iff (a b : Perm (Fin 5)) :
    pK (enc a) (enc b) = true ↔ ∀ i : Fin 5, pairUp (b⁻¹ (a⁻¹ i)) (a⁻¹ i) (b⁻¹ i) i := by
  rw [pK, allLtK_iff, invCK_enc hn5, invCK_enc hn5]
  refine Iff.trans ⟨fun h (i : Fin 5) => h i i.2, fun h i hi => h ⟨i, hi⟩⟩ ?_
  simp only [rd_enc hn5, pairK_iff]

theorem allP_iff (x y : Perm (Fin 5)) : allP (enc x) (enc y) = true ↔
    ∀ a ∈ kl x y, ∀ b ∈ kl x y, ∀ i : Fin 5, pairUp (b⁻¹ (a⁻¹ i)) (a⁻¹ i) (b⁻¹ i) i := by
  have hk : klK (enc x) (enc y) = [1, x, y, x * y].map enc := by
    rw [klK, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil, e5_enc,
      enc_mul hn5]
  have hm : ∀ a, a ∈ kl x y ↔ a ∈ [1, x, y, x * y] := fun a => by simp [kl]
  simp only [allP, hk, allK_iff, List.forall_mem_map, pK_iff, hm]

theorem mem_invL (y : Perm (Fin 5)) (hy : y ∈ invF) : memK (enc y) invL = true := by
  obtain ⟨hy1, hyy⟩ := mem_invF.1 hy
  have h := walkK_sound inv_walk y
  have h1 : Nat.beq (enc y) e5 = false := by
    rw [← e5_enc, beq_enc_eq_decide hn5]
    exact decide_eq_false hy1
  have h2 : Nat.beq (mulK 5 (enc y) (enc y)) e5 = true := by
    rw [← e5_enc, mulK_enc hn5, hyy, Nat.beq_refl]
  rw [h1, h2, Bool.not_true, Bool.false_or, Bool.false_or] at h
  exact h

end QuadK

set_option synthInstance.maxSize 2000 in
open CFSG.Permutation.FinPack QuadK in
theorem quadKl_iff : ∀ x ∈ invF, ∀ y ∈ invF, x ≠ y → x * y = y * x →
    ((∀ a ∈ kl x y, ∀ w ∈ spanF (commGensF orth (kl x y) Finset.univ), orth.act a w = w) ↔
      (Perm.sign x ≠ 1 ∨ Perm.sign y ≠ 1)) := by
  intro x hx y hy hxy hc
  rw [quad_iff_pairs, ← allP_iff]
  obtain ⟨hx1, hxx⟩ := mem_invF.1 hx
  have h := walkK_sound quad_walk x
  have h1 : Nat.beq (enc x) e5 = false := by
    rw [← e5_enc, beq_enc_eq_decide hn5]
    exact decide_eq_false hx1
  have h2 : Nat.beq (mulK 5 (enc x) (enc x)) e5 = true := by
    rw [← e5_enc, mulK_enc hn5, hxx, Nat.beq_refl]
  rw [h1, h2, Bool.not_true, Bool.false_or, Bool.false_or] at h
  have h3 := allK_iff.1 h _ (memK_iff.1 (mem_invL y hy))
  have h4 : Nat.beq (enc x) (enc y) = false := by
    rw [beq_enc_eq_decide hn5]
    exact decide_eq_false hxy
  have h5 : Nat.beq (mulK 5 (enc x) (enc y)) (mulK 5 (enc y) (enc x)) = true := by
    rw [mulK_enc hn5, mulK_enc hn5, hc, Nat.beq_refl]
  rw [h4, h5, Bool.not_true, Bool.false_or, Bool.false_or, beq_iff_eq] at h3
  rw [h3, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true', evenK_enc_eq_decide hn5,
    evenK_enc_eq_decide hn5, decide_eq_false_iff_not, decide_eq_false_iff_not]

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

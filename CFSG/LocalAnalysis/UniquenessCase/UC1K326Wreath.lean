module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemThompsonTransport
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open RegularWreathProduct

open scoped commutatorElement

variable {n : ℕ}

@[expose]
def el (n : ℕ) (a b c : ZMod (3 ^ n)) (e : ZMod 3) : ZWr n :=
  ⟨fun q => Multiplicative.ofAdd
      (if Multiplicative.toAdd q = 0 then a else if Multiplicative.toAdd q = 1 then b else c),
    Multiplicative.ofAdd e⟩

@[simp] theorem el_left_zero (a b c : ZMod (3 ^ n)) (e : ZMod 3) :
    (el n a b c e).left (Multiplicative.ofAdd 0) = Multiplicative.ofAdd a := by
  simp [el]

@[simp] theorem el_left_one (a b c : ZMod (3 ^ n)) (e : ZMod 3) :
    (el n a b c e).left (Multiplicative.ofAdd 1) = Multiplicative.ofAdd b := by
  simp +decide [el]

@[simp] theorem el_left_two (a b c : ZMod (3 ^ n)) (e : ZMod 3) :
    (el n a b c e).left (Multiplicative.ofAdd 2) = Multiplicative.ofAdd c := by
  simp +decide [el]

@[simp] theorem el_right (a b c : ZMod (3 ^ n)) (e : ZMod 3) :
    (el n a b c e).right = Multiplicative.ofAdd e := rfl

theorem ofAdd_cases (q : Multiplicative (ZMod 3)) :
    q = Multiplicative.ofAdd 0 ∨ q = Multiplicative.ofAdd 1 ∨ q = Multiplicative.ofAdd 2 := by
  have h : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide
  rcases h (Multiplicative.toAdd q) with h0 | h1 | h2
  · exact Or.inl (by rw [← ofAdd_toAdd q, h0])
  · exact Or.inr (Or.inl (by rw [← ofAdd_toAdd q, h1]))
  · exact Or.inr (Or.inr (by rw [← ofAdd_toAdd q, h2]))

theorem el_injective :
    Function.Injective (fun p : ZMod (3 ^ n) × ZMod (3 ^ n) × ZMod (3 ^ n) × ZMod 3 =>
      el n p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨a, b, c, e⟩ ⟨a', b', c', e'⟩ h
  have hright : e = e' := by
    have := congrArg (fun w : ZWr n => Multiplicative.toAdd w.right) h
    simpa only [el_right, toAdd_ofAdd] using this
  have h0 : a = a' := by
    have := congrArg (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
    simpa only [el_left_zero, toAdd_ofAdd] using this
  have h1 : b = b' := by
    have := congrArg (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) h
    simpa only [el_left_one, toAdd_ofAdd] using this
  have h2 : c = c' := by
    have := congrArg (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))) h
    simpa only [el_left_two, toAdd_ofAdd] using this
  simp [h0, h1, h2, hright]

@[simp] theorem el_zero_zero : el n 0 0 0 (0 : ZMod 3) = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    rcases ofAdd_cases q with rfl | rfl | rfl <;> simp +decide [el]
  · simp [el]

theorem el_mul_zero (a b c a' b' c' : ZMod (3 ^ n)) (t : ZMod 3) :
    el n a b c 0 * el n a' b' c' t = el n (a + a') (b + b') (c + c') t := by
  apply RegularWreathProduct.ext
  · funext q
    apply Multiplicative.toAdd.injective
    rcases ofAdd_cases q with rfl | rfl | rfl <;>
      simp +decide only [el, RegularWreathProduct.mul_def, Pi.mul_apply, toAdd_ofAdd,
        toAdd_mul, toAdd_inv, toAdd_one, inv_one, mul_one, one_mul, if_true, if_false,
        reduceIte, add_zero, zero_add]
  · simp [el]

theorem el_mul_one (a b c a' b' c' : ZMod (3 ^ n)) (t : ZMod 3) :
    el n a b c 1 * el n a' b' c' t = el n (a + c') (b + a') (c + b') (1 + t) := by
  apply RegularWreathProduct.ext
  · funext q
    apply Multiplicative.toAdd.injective
    rcases ofAdd_cases q with rfl | rfl | rfl <;>
      simp +decide only [el, RegularWreathProduct.mul_def, Pi.mul_apply, toAdd_ofAdd,
        toAdd_mul, toAdd_inv, toAdd_one, inv_one, mul_one, one_mul, if_true, if_false,
        reduceIte, add_zero, zero_add]
  · simp [el]

theorem el_mul_two (a b c a' b' c' : ZMod (3 ^ n)) (t : ZMod 3) :
    el n a b c 2 * el n a' b' c' t = el n (a + b') (b + c') (c + a') (2 + t) := by
  apply RegularWreathProduct.ext
  · funext q
    apply Multiplicative.toAdd.injective
    rcases ofAdd_cases q with rfl | rfl | rfl <;>
      simp +decide only [el, RegularWreathProduct.mul_def, Pi.mul_apply, toAdd_ofAdd,
        toAdd_mul, toAdd_inv, toAdd_one, inv_one, mul_one, one_mul, if_true, if_false,
        reduceIte, add_zero, zero_add]
  · simp [el]

theorem zmod3_cases (s : ZMod 3) : s = 0 ∨ s = 1 ∨ s = 2 := by
  have h := ofAdd_cases (Multiplicative.ofAdd s)
  simpa using h

theorem one_ne_zero_zmod (hn : 1 ≤ n) : (1 : ZMod (3 ^ n)) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod (3 ^ n)) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle : 3 ^ n ≤ 1 := Nat.le_of_dvd (by norm_num) h'
  have hge : 3 ≤ 3 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hn
  omega

theorem el_eta (w : ZWr n) :
    w = el n (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0)))
        (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1)))
        (Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2)))
        (Multiplicative.toAdd w.right) := by
  apply RegularWreathProduct.ext
  · funext q
    rcases ofAdd_cases q with rfl | rfl | rfl <;> simp +decide [el]
  · simp [el]

@[expose] def base (n : ℕ) : Subgroup (ZWr n) := RegularWreathProduct.rightHom.ker

@[simp] theorem el_mem_base_iff (a b c : ZMod (3 ^ n)) (s : ZMod 3) :
    el n a b c s ∈ base n ↔ s = 0 := by
  simp [base, el]

theorem base_normal (n : ℕ) : (base n).Normal := by
  rw [base]
  exact MonoidHom.normal_ker _

theorem el_mul_base (a b c d : ZMod (3 ^ n)) (s : ZMod 3) :
    el n a b c s * el n d d d 0 = el n (a + d) (b + d) (c + d) s := by
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [el_mul_zero]
  · rw [el_mul_one]
    congr 1 <;> simp [add_assoc, add_comm, add_left_comm]
  · rw [el_mul_two]
    congr 1 <;> simp [add_assoc, add_comm, add_left_comm]

@[expose] def diagHom (n : ℕ) : Multiplicative (ZMod (3 ^ n)) →* ZWr n where
  toFun d :=
    el n (Multiplicative.toAdd d) (Multiplicative.toAdd d) (Multiplicative.toAdd d) 0
  map_one' := by simp [el_zero_zero]
  map_mul' d e := by
    rw [el_mul_zero, toAdd_mul]

@[simp] theorem diagHom_apply (d : Multiplicative (ZMod (3 ^ n))) :
    diagHom n d =
      el n (Multiplicative.toAdd d) (Multiplicative.toAdd d) (Multiplicative.toAdd d) 0 := rfl

@[expose] def diagSub (n : ℕ) : Subgroup (ZWr n) := (diagHom n).range

theorem diagHom_injective : Function.Injective (diagHom n) := by
  intro d e h
  apply Multiplicative.toAdd.injective
  have h' := congrArg (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
  simpa only [diagHom_apply, el_left_zero, toAdd_ofAdd] using h'

theorem diag_le_center : diagSub n ≤ Subgroup.center (ZWr n) := by
  rintro w ⟨d, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  rw [el_eta g, diagHom_apply, el_mul_zero, el_mul_base]
  simp [add_comm]

theorem center_le_diag (hn : 1 ≤ n) : Subgroup.center (ZWr n) ≤ diagSub n := by
  intro w hw
  obtain ⟨a, b, c, s, rfl⟩ : ∃ a b c s, w = el n a b c s := ⟨_, _, _, _, el_eta w⟩
  have hmem := Subgroup.mem_center_iff.mp hw
  have hs0 : s = 0 := by
    rcases zmod3_cases s with hs | hs | hs
    · exact hs
    · exfalso
      have hc := hmem (el n 1 0 0 0)
      rw [hs, el_mul_one, el_mul_zero] at hc
      have hfirst := congrArg
        (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0))) hc
      simp only [el_left_zero, toAdd_ofAdd, zero_add, add_zero] at hfirst
      exact one_ne_zero_zmod hn (add_right_cancel (b := a) (by rw [zero_add]; exact hfirst))
    · exfalso
      have hc := hmem (el n 1 0 0 0)
      rw [hs, el_mul_two, el_mul_zero] at hc
      have hfirst := congrArg
        (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0))) hc
      simp only [el_left_zero, toAdd_ofAdd, zero_add, add_zero] at hfirst
      exact one_ne_zero_zmod hn (add_right_cancel (b := a) (by rw [zero_add]; exact hfirst))
  rw [hs0] at hw ⊢
  have hmem0 := Subgroup.mem_center_iff.mp hw
  have hc := hmem0 (el n 0 0 0 1)
  rw [el_mul_one, el_mul_zero] at hc
  have h0 := congrArg
    (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0))) hc
  have h1 := congrArg
    (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 1))) hc
  have h2 := congrArg
    (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 2))) hc
  simp only [el_left_zero, el_left_one, el_left_two, toAdd_ofAdd, zero_add, add_zero] at h0 h1 h2
  rw [diagSub, MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  rw [diagHom_apply, toAdd_ofAdd, h1, h2]

theorem center_eq_diag (hn : 1 ≤ n) : Subgroup.center (ZWr n) = diagSub n :=
  le_antisymm (center_le_diag hn) diag_le_center

theorem card_diagSub : Nat.card (diagSub n) = 3 ^ n := by
  rw [diagSub]
  rw [Nat.card_congr (MonoidHom.ofInjective (f := diagHom n) diagHom_injective).symm.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem isCyclic_diagSub : IsCyclic (diagSub n) := by
  rw [diagSub]
  exact ((MonoidHom.ofInjective (f := diagHom n) diagHom_injective).isCyclic).mp inferInstance

theorem isCyclic_center (hn : 1 ≤ n) : IsCyclic (Subgroup.center (ZWr n)) := by
  rw [center_eq_diag hn]
  exact isCyclic_diagSub

theorem card_center (hn : 1 ≤ n) : Nat.card (Subgroup.center (ZWr n)) = 3 ^ n := by
  rw [center_eq_diag hn, card_diagSub]

theorem zwr_card_center_Zwr (hn : 1 ≤ n) :
    Nat.card (ZWr n) = 3 ^ (3 * n + 1) ∧ IsCyclic (Subgroup.center (ZWr n)) ∧
      Nat.card (Subgroup.center (ZWr n)) = 3 ^ n := by
  refine ⟨?_, isCyclic_center hn, card_center hn⟩
  rw [RegularWreathProduct.card]
  simp only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [← pow_mul]
  ring_nf

theorem isPGroup_Zwr (hn : 1 ≤ n) : IsPGroup 3 (ZWr n) :=
  IsPGroup.of_card (n := 3 * n + 1) (zwr_card_center_Zwr hn).1

theorem center_omega_le_of_normal {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    (hG : IsPGroup 3 G) (hcyc : IsCyclic (Subgroup.center G))
    (hcard : Nat.card (Subgroup.center G) = 3 ^ n) {N : Subgroup G} (hN : N.Normal)
    (hN1 : N ≠ ⊥) : ∀ z ∈ Subgroup.center G, z ^ 3 = 1 → z ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : N.Normal := hN
  haveI : IsCyclic (Subgroup.center G) := hcyc
  have hnil : Group.IsNilpotent G := hG.isNilpotent
  have hinter : N ⊓ Subgroup.center G ≠ ⊥ := hnil.inf_center_ne_bot_of_normal hN1
  let K : Subgroup (Subgroup.center G) :=
    (N ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hinter
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxZ⟩ := hx
    have hmem : (⟨x, hxZ⟩ : Subgroup.center G) ∈ K := by
      change (⟨x, hxZ⟩ : Subgroup.center G) ∈
        (N ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)
      exact ⟨hxN, hxZ⟩
    rw [hK] at hmem
    have hx1 : x = 1 := by simpa using hmem
    simp [hx1]
  have hZpg : IsPGroup 3 (Subgroup.center G) := hG.to_subgroup (Subgroup.center G)
  obtain ⟨h3K, -⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card hZpg hKne
  have hctop : Subgroup.center (↥(Subgroup.center G)) = ⊤ := Subgroup.center_eq_top
  have hcenterK : K ⊓ Subgroup.center (Subgroup.center G) = K := by
    rw [hctop, inf_top_eq]
  rw [hcenterK] at h3K
  intro z hz hz3
  by_cases hz1 : z = 1
  · rw [hz1]; exact N.one_mem
  · have hz3' : (⟨z, hz⟩ : Subgroup.center G) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    have hz1' : (⟨z, hz⟩ : Subgroup.center G) ≠ 1 := by
      intro h; exact hz1 (Subtype.ext_iff.mp h)
    have hord : orderOf (⟨z, hz⟩ : Subgroup.center G) = 3 :=
      orderOf_eq_prime hz3' hz1'
    have hcard_z : Nat.card (Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center G)) = 3 := by
      rw [Nat.card_zpowers, hord]
    have hle : Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center G) ≤ K := by
      rw [IsCyclic.subgroup_le_iff_card_dvd (H := Subgroup.zpowers _) (K := K)]
      rw [hcard_z]
      exact h3K
    have hmem : (⟨z, hz⟩ : Subgroup.center G) ∈ K := hle (Subgroup.mem_zpowers _)
    have hmem' : (⟨z, hz⟩ : Subgroup.center G) ∈
        (N ⊓ Subgroup.center G).subgroupOf (Subgroup.center G) := hmem
    exact (Subgroup.mem_subgroupOf.mp hmem').1

theorem zwr_normal_contains_omega_center_Zwr (hn : 1 ≤ n) {N : Subgroup (ZWr n)}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : ∀ z ∈ Subgroup.center (ZWr n), z ^ 3 = 1 → z ∈ N :=
  center_omega_le_of_normal hn (isPGroup_Zwr hn) (isCyclic_center hn) (card_center hn) hN hN1

theorem base_mul_left (x y : ZWr n) (hx : x ∈ base n) (q : Multiplicative (ZMod 3)) :
    (x * y).left q = x.left q * y.left q := by
  have hxr : x.right = Multiplicative.ofAdd 0 := by
    have h : x.right = 1 := by simpa [base] using hx
    rw [h, ofAdd_zero]
  have hq : x.right⁻¹ * q = q := by
    rw [hxr, ← ofAdd_neg, show (-(0 : ZMod 3)) = 0 by decide, ofAdd_zero, one_mul]
  show x.left q * y.left (x.right⁻¹ * q) = x.left q * y.left q
  rw [hq]

theorem base_comm {x y : ZWr n} (hx : x ∈ base n) (hy : y ∈ base n) : x * y = y * x := by
  apply RegularWreathProduct.ext
  · funext q
    rw [base_mul_left x y hx q, base_mul_left y x hy q, mul_comm]
  · have hxr : x.right = 1 := by simpa [base] using hx
    have hyr : y.right = 1 := by simpa [base] using hy
    rw [RegularWreathProduct.mul_right, RegularWreathProduct.mul_right, hxr, hyr]

theorem base_pow_left (x : ZWr n) (hx : x ∈ base n) (k : ℕ)
    (q : Multiplicative (ZMod 3)) : (x ^ k).left q = (x.left q) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, base_mul_left _ _ ((base n).pow_mem hx k) q, ih, pow_succ]

theorem el_pow_base (a b c : ZMod (3 ^ n)) (k : ℕ) :
    el n a b c 0 ^ k = el n (k • a) (k • b) (k • c) 0 := by
  induction k with
  | zero => simp [el_zero_zero]
  | succ k ih =>
    rw [pow_succ, ih, el_mul_zero]
    congr 1 <;> ring

theorem three_dvd_pow (hn : 1 ≤ n) : 3 ∣ 3 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact dvd_mul_left 3 (3 ^ m)

@[expose] def omegaD (m : ℕ) : Subgroup (Multiplicative (ZMod m)) :=
  (powMonoidHom (α := Multiplicative (ZMod m)) 3).ker

@[simp] theorem mem_omegaD {m : ℕ} {x : Multiplicative (ZMod m)} :
    x ∈ omegaD m ↔ x ^ 3 = 1 := by
  simp [omegaD]

theorem card_omegaD (hn : 1 ≤ n) : Nat.card (omegaD (3 ^ n)) = 3 := by
  have h := IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (3 ^ n))) 3
  have hm : Nat.card (Multiplicative (ZMod (3 ^ n))) = 3 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hm] at h
  rw [omegaD, h, Nat.gcd_eq_right (three_dvd_pow hn)]

@[expose] def omegaBase (n : ℕ) : Subgroup (ZWr n) where
  carrier := {x | x ∈ base n ∧ x ^ 3 = 1}
  one_mem' := ⟨(base n).one_mem, one_pow 3⟩
  mul_mem' := by
    rintro x y ⟨hxb, hx3⟩ ⟨hyb, hy3⟩
    refine ⟨(base n).mul_mem hxb hyb, ?_⟩
    rw [Commute.mul_pow (by rw [Commute]; exact base_comm hxb hyb), hx3, hy3, one_mul]
  inv_mem' := by
    rintro x ⟨hxb, hx3⟩
    exact ⟨(base n).inv_mem hxb, by rw [inv_pow, hx3, inv_one]⟩

theorem omegaBase_le_base : omegaBase n ≤ base n := fun _ hx => hx.1

theorem omegaD_three_smul {d : Multiplicative (ZMod (3 ^ n))} (hd : d ∈ omegaD (3 ^ n)) :
    3 • Multiplicative.toAdd d = 0 := by
  have h : d ^ 3 = 1 := by simpa using hd
  simpa [toAdd_pow] using congrArg Multiplicative.toAdd h

@[expose] noncomputable def omegaBaseEquiv (n : ℕ) :
    omegaBase n ≃ (omegaD (3 ^ n) × omegaD (3 ^ n) × omegaD (3 ^ n)) where
  toFun x :=
    (⟨x.1.left (Multiplicative.ofAdd 0), by
        have h := base_pow_left x.1 x.2.1 3 (Multiplicative.ofAdd 0)
        rw [x.2.2] at h
        simpa using h.symm⟩,
     ⟨x.1.left (Multiplicative.ofAdd 1), by
        have h := base_pow_left x.1 x.2.1 3 (Multiplicative.ofAdd 1)
        rw [x.2.2] at h
        simpa using h.symm⟩,
     ⟨x.1.left (Multiplicative.ofAdd 2), by
        have h := base_pow_left x.1 x.2.1 3 (Multiplicative.ofAdd 2)
        rw [x.2.2] at h
        simpa using h.symm⟩)
  invFun p :=
    ⟨el n (Multiplicative.toAdd p.1.1) (Multiplicative.toAdd p.2.1.1)
        (Multiplicative.toAdd p.2.2.1) 0,
      ⟨by rw [el_mem_base_iff], by
        rw [el_pow_base]
        simp only [omegaD_three_smul p.1.2, omegaD_three_smul p.2.1.2,
          omegaD_three_smul p.2.2.2, el_zero_zero]⟩⟩
  left_inv x := by
    apply Subtype.ext
    rw [el_eta x.1]
    have hxr : Multiplicative.toAdd x.1.right = 0 := by
      have h := x.2.1
      simp [base] at h
      rw [h]; rfl
    rw [hxr]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; simp +decide [el]
    · apply Prod.ext
      · apply Subtype.ext; simp +decide [el]
      · apply Subtype.ext; simp +decide [el]

theorem card_omegaBase (hn : 1 ≤ n) : Nat.card (omegaBase n) = 27 := by
  simp only [Nat.card_congr (omegaBaseEquiv n), Nat.card_prod, card_omegaD hn]

theorem isElemAbelian_omegaBase : CFSG.Open.IsElemAbelian 3 (omegaBase n) :=
  ⟨⟨⟨fun a b => Subtype.ext (base_comm a.2.1 b.2.1)⟩⟩, fun _ hx => hx.2⟩

theorem el_comm_base_diag {A B C a b c : ZMod (3 ^ n)} {s : ZMod 3} (hs : s ≠ 0)
    (h : el n A B C s * el n a b c 0 = el n a b c 0 * el n A B C s) :
    a = b ∧ b = c := by
  rcases zmod3_cases s with h0 | h1 | h2
  · exact False.elim (absurd h0 hs)
  · rw [h1] at h
    rw [el_mul_one, el_mul_zero] at h
    have h0 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
    have h1' := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) h
    simp only [el_left_zero, el_left_one, toAdd_ofAdd, zero_add, add_zero] at h0 h1'
    have hca : c = a := add_right_cancel (b := A) (by simpa [add_comm] using h0)
    have hab : a = b := add_right_cancel (b := B) (by simpa [add_comm] using h1')
    exact ⟨hab, hab.symm.trans hca.symm⟩
  · rw [h2] at h
    rw [el_mul_two, el_mul_zero] at h
    have h0 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
    have h1' := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) h
    simp only [el_left_zero, el_left_one, toAdd_ofAdd, zero_add, add_zero] at h0 h1'
    have hba : b = a := add_right_cancel (b := A) (by simpa [add_comm] using h0)
    have hcb : c = b := add_right_cancel (b := B) (by simpa [add_comm] using h1')
    exact ⟨hba.symm, hcb.symm⟩

theorem centralizer_base_le_diag {y : ZWr n} (hy : y ∉ base n) :
    Subgroup.centralizer ({y} : Set (ZWr n)) ⊓ base n ≤ diagSub n := by
  intro x hx
  obtain ⟨hxcent, hxbase⟩ := hx
  set A := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 0)) with hA
  set B := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 1)) with hB
  set C := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 2)) with hC
  set s := Multiplicative.toAdd y.right with hs
  set a := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0)) with ha
  set b := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 1)) with hb
  set c := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 2)) with hc
  have hsne : s ≠ 0 := by
    intro h0
    apply hy
    rw [hs] at h0
    have : y.right = 1 := Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    simpa [base] using this
  have hx0 : Multiplicative.toAdd x.right = 0 := by
    have h : x.right = 1 := by simpa [base] using hxbase
    rw [h, toAdd_one]
  have hy_eq : y = el n A B C s := by
    rw [el_eta y, hA, hB, hC, hs]
  have hx_eq : x = el n a b c 0 := by
    rw [el_eta x, ha, hb, hc, hx0]
  have hcomm : el n A B C s * el n a b c 0 = el n a b c 0 * el n A B C s := by
    have h := Subgroup.mem_centralizer_iff.mp hxcent y (by simp)
    rwa [hy_eq, hx_eq] at h
  obtain ⟨hab, hbc⟩ := el_comm_base_diag hsne hcomm
  rw [hx_eq, diagSub, MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  rw [diagHom_apply, toAdd_ofAdd, hab, hbc]

theorem card_diag_inter_omegaBase_le (hn : 1 ≤ n) :
    Nat.card (diagSub n ⊓ omegaBase n : Subgroup (ZWr n)) ≤ 3 := by
  let ψ := MonoidHom.ofInjective (f := diagHom n) diagHom_injective
  have hinj : Function.Injective (fun x : (diagSub n ⊓ omegaBase n : Subgroup (ZWr n)) =>
      (⟨ψ.symm ⟨x.1, x.2.1⟩, by
        show (ψ.symm ⟨x.1, x.2.1⟩ : Multiplicative (ZMod (3 ^ n))) ^ 3 = 1
        apply ψ.injective
        rw [map_pow, MulEquiv.apply_symm_apply, map_one]
        exact Subtype.ext x.2.2.2⟩ : omegaD (3 ^ n))) := by
    intro x y h
    have h' : (⟨x.1, x.2.1⟩ : diagSub n) = ⟨y.1, y.2.1⟩ := ψ.symm.injective (Subtype.ext_iff.mp h)
    have h1 : ψ.symm ⟨x.1, x.2.1⟩ = ψ.symm ⟨y.1, y.2.1⟩ := congrArg Subtype.val h
    have h2 : (⟨x.1, x.2.1⟩ : diagSub n) = ⟨y.1, y.2.1⟩ := ψ.symm.injective h1
    have h3 : (x : ZWr n) = (y : ZWr n) := congrArg (fun z : diagSub n => (z : ZWr n)) h2
    exact Subtype.ext h3
  calc Nat.card (diagSub n ⊓ omegaBase n : Subgroup (ZWr n))
      ≤ Nat.card (omegaD (3 ^ n)) := Nat.card_le_card_of_injective _ hinj
    _ = 3 := card_omegaD hn

theorem card_le_nine_of_not_le_base (hn : 1 ≤ n) {E : Subgroup (ZWr n)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hbase : ¬ E ≤ base n) : Nat.card E ≤ 9 := by
    classical
    rw [SetLike.le_def] at hbase
    push Not at hbase
    let y := Classical.choose hbase
    have hyE : y ∈ E := (Classical.choose_spec hbase).1
    have hybase : y ∉ base n := (Classical.choose_spec hbase).2
    let K : Subgroup (ZWr n) := E ⊓ base n
    haveI : IsMulCommutative E := hE.1
    have hEcent : E ≤ Subgroup.centralizer ({y} : Set (ZWr n)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hc := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hyE⟩)
      simpa using hc.symm
    have hKdiag : K ≤ diagSub n := by
      intro x hx
      exact centralizer_base_le_diag hybase ⟨hEcent hx.1, hx.2⟩
    have hKomega : K ≤ omegaBase n := fun x hx => ⟨hx.2, hE.2 x hx.1⟩
    have hKcard : Nat.card K ≤ 3 :=
      (Subgroup.card_le_of_le (show K ≤ diagSub n ⊓ omegaBase n from
        fun x hx => ⟨hKdiag hx, hKomega hx⟩)).trans (card_diag_inter_omegaBase_le hn)
    let φ : E →* Multiplicative (ZMod 3) :=
      RegularWreathProduct.rightHom.comp E.subtype
    have hker : Nat.card φ.ker ≤ Nat.card K := by
      have hinj : Function.Injective (fun x : φ.ker =>
          (⟨x.1.1, ⟨x.1.2, by
            have hx2 : φ x.1 = 1 := MonoidHom.mem_ker.mp x.2
            have hx3 : rightHom x.1.1 = 1 := hx2
            simpa [base] using hx3⟩⟩ : K)) := by
        intro x y h
        have h1 : (x.1.1 : ZWr n) = (y.1.1 : ZWr n) :=
          congrArg (fun z : K => (z : ZWr n)) h
        exact Subtype.ext (Subtype.ext h1)
      exact Nat.card_le_card_of_injective _ hinj
    have hrange : Nat.card φ.range ≤ 3 := by
      calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 3)) :=
            Subgroup.card_le_card_group _
        _ = 3 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
      _ ≤ 3 * 3 := Nat.mul_le_mul (hker.trans hKcard) hrange
      _ = 9 := by norm_num

theorem card_elemAbelian_le (hn : 1 ≤ n) {E : Subgroup (ZWr n)}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  by_cases hbase : E ≤ base n
  · have hEomega : E ≤ omegaBase n := fun x hx => ⟨hbase hx, hE.2 x hx⟩
    calc Nat.card E ≤ Nat.card (omegaBase n) := Subgroup.card_le_of_le hEomega
      _ = 27 := card_omegaBase hn
  · exact (card_le_nine_of_not_le_base hn hE hbase).trans (by norm_num)

theorem unique_omegaBase (hn : 1 ≤ n) {E : Subgroup (ZWr n)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 27) : E = omegaBase n := by
  have hEbase : E ≤ base n := by
    by_contra h
    have h9 := card_le_nine_of_not_le_base hn hE h
    omega
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ⟨hEbase hx, hE.2 x hx⟩) ?_
  rw [card_omegaBase hn, hcard]

theorem zwr_pRank_Zwr (hn : 1 ≤ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (ZWr n)) = 3 := by
  refine le_antisymm ?_ ?_
  · refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    have h := card_elemAbelian_le hn hE
    simpa using h
  · refine SectionRank.le_pRank (by norm_num) (H := (⊤ : Subgroup (ZWr n)))
      (E := omegaBase n) le_top isElemAbelian_omegaBase (k := 3) ?_
    rw [card_omegaBase hn]
    norm_num

theorem zwr_elemThompson_Zwr (hn : 1 ≤ n) :
    CFSG.elemThompson (ZWr n) 3 = omegaBase n := by
  have hpr : CFSG.pRank 3 (ZWr n) = 3 := by
    rw [SectionRank.pRank_eq_open_pRank_top, zwr_pRank_Zwr hn]
  have hfam : CFSG.elemThompsonFamily (ZWr n) 3 = {omegaBase n} := by
    ext A
    rw [CFSG.elemThompsonFamily]
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hA, hcard⟩
      rw [hpr] at hcard
      exact unique_omegaBase hn (CFSG.Open.isElemAbelian_of_isElementaryAbelian) hcard
    · intro hA
      rw [hA]
      exact ⟨(CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp isElemAbelian_omegaBase),
        by rw [card_omegaBase hn, hpr]; norm_num⟩
  rw [CFSG.elemThompson, hfam, csSup_singleton]

theorem el_inv_base (a b c : ZMod (3 ^ n)) :
    (el n a b c 0)⁻¹ = el n (-a) (-b) (-c) 0 := by
  apply inv_eq_of_mul_eq_one_right
  rw [el_mul_zero]
  simp [el_zero_zero]

theorem el_inv_one (a b c : ZMod (3 ^ n)) :
    (el n a b c 1)⁻¹ = el n (-b) (-c) (-a) 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [el_mul_one, show (1 : ZMod 3) + 2 = 0 by decide]
  simp [el_zero_zero]

theorem el_inv_two (a b c : ZMod (3 ^ n)) :
    (el n a b c 2)⁻¹ = el n (-c) (-a) (-b) 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [el_mul_two, show (2 : ZMod 3) + 1 = 0 by decide]
  simp [el_zero_zero]

theorem commutator_base_one (a b c : ZMod (3 ^ n)) :
    el n 1 0 0 0 * el n a b c 1 * (el n 1 0 0 0)⁻¹ * (el n a b c 1)⁻¹ =
      el n 1 (-1) 0 0 := by
  rw [el_inv_base, el_inv_one]
  simp only [el_mul_zero, el_mul_one, add_zero, zero_add]
  congr 1 <;> first | abel | decide

theorem commutator_base_two (a b c : ZMod (3 ^ n)) :
    el n 1 0 0 0 * el n a b c 2 * (el n 1 0 0 0)⁻¹ * (el n a b c 2)⁻¹ =
      el n 1 0 (-1) 0 := by
  rw [el_inv_base, el_inv_two]
  simp only [el_mul_zero, el_mul_two, add_zero, zero_add]
  congr 1 <;> first | abel | decide

theorem two_ne_zero_zmod (hn : 1 ≤ n) : (2 : ZMod (3 ^ n)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (3 ^ n)) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle : 3 ^ n ≤ 2 := Nat.le_of_dvd (by norm_num) h'
  have hge : 3 ≤ 3 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hn
  omega

theorem one_ne_neg_one_zmod (hn : 1 ≤ n) : (1 : ZMod (3 ^ n)) ≠ -1 := by
  intro h
  apply two_ne_zero_zmod hn
  have h3 : (1 : ZMod (3 ^ n)) + 1 = 0 := by
    nth_rewrite 1 [h]
    exact neg_add_cancel 1
  exact (show (2 : ZMod (3 ^ n)) = 1 + 1 by ring).trans h3

theorem el_mem_diagSub_iff {a b c : ZMod (3 ^ n)} :
    el n a b c 0 ∈ diagSub n ↔ a = b ∧ b = c := by
  rw [diagSub, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    have h0 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) hd
    have h1 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) hd
    have h2 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))) hd
    simp only [diagHom_apply, el_left_zero, el_left_one, el_left_two, toAdd_ofAdd] at h0 h1 h2
    exact ⟨h0.symm.trans h1, h1.symm.trans h2⟩
  · rintro ⟨hab, hbc⟩
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    rw [diagHom_apply, toAdd_ofAdd, hab, hbc]

theorem normal_elemAbelian_le_omegaBase_Zwr (hn : 1 ≤ n) {E : Subgroup (ZWr n)}
    (hN : E.Normal) (hE : CFSG.Open.IsElemAbelian 3 E) : E ≤ omegaBase n := by
  by_cases hbase : E ≤ base n
  · exact fun x hx => ⟨hbase hx, hE.2 x hx⟩
  · exfalso
    rw [SetLike.le_def] at hbase
    push Not at hbase
    let y := Classical.choose hbase
    have hyE : y ∈ E := (Classical.choose_spec hbase).1
    have hybase : y ∉ base n := (Classical.choose_spec hbase).2
    haveI : IsMulCommutative E := hE.1
    haveI : (base n).Normal := base_normal n
    set a := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 0)) with ha
    set b := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 1)) with hb
    set c := Multiplicative.toAdd (y.left (Multiplicative.ofAdd 2)) with hc
    set s := Multiplicative.toAdd y.right with hs
    have hy_eq : y = el n a b c s := by rw [el_eta y, ha, hb, hc, hs]
    have hsne : s ≠ 0 := by
      intro h0
      apply hybase
      rw [hy_eq, h0]
      exact (el_mem_base_iff a b c 0).mpr rfl
    have hconjE : el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ ∈ E :=
      hN.conj_mem y hyE (el n 1 0 0 0)
    have hcommE : el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ * y⁻¹ ∈ E :=
      mul_mem hconjE (inv_mem hyE)
    have hcommcent : el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ * y⁻¹ ∈
        Subgroup.centralizer ({y} : Set (ZWr n)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val (mul_comm' (⟨y, hyE⟩ : E)
        (⟨el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ * y⁻¹, hcommE⟩ : E))
    have hb_base : el n 1 0 0 0 ∈ base n := (el_mem_base_iff 1 0 0 0).mpr rfl
    have hconjB : y * (el n 1 0 0 0)⁻¹ * y⁻¹ ∈ base n :=
      (base_normal n).conj_mem (el n 1 0 0 0)⁻¹ ((base n).inv_mem hb_base) y
    have hcommbase : el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ * y⁻¹ ∈ base n := by
      have h2 : el n 1 0 0 0 * (y * (el n 1 0 0 0)⁻¹ * y⁻¹) ∈ base n :=
        (base n).mul_mem hb_base hconjB
      simpa only [mul_assoc] using h2
    have hcommdiag : el n 1 0 0 0 * y * (el n 1 0 0 0)⁻¹ * y⁻¹ ∈ diagSub n :=
      centralizer_base_le_diag hybase ⟨hcommcent, hcommbase⟩
    rcases zmod3_cases s with h0 | h1 | h2
    · exact hsne h0
    · rw [hy_eq, h1, commutator_base_one] at hcommdiag
      rw [el_mem_diagSub_iff] at hcommdiag
      exact one_ne_neg_one_zmod hn hcommdiag.1
    · rw [hy_eq, h2, commutator_base_two] at hcommdiag
      rw [el_mem_diagSub_iff] at hcommdiag
      exact one_ne_zero_zmod hn hcommdiag.1

theorem zwr_unique_E27_Zwr (hn : 1 ≤ n) :
    ∃ A : Subgroup (ZWr n), CFSG.elemThompson (ZWr n) 3 = A ∧
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      (∀ E : Subgroup (ZWr n), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 → E = A) ∧
      (∀ E : Subgroup (ZWr n), E.Normal → CFSG.Open.IsElemAbelian 3 E → E ≤ A) :=
  ⟨omegaBase n, zwr_elemThompson_Zwr hn, isElemAbelian_omegaBase, card_omegaBase hn,
    fun E hE hc => unique_omegaBase hn hE hc,
    fun E hN hE => normal_elemAbelian_le_omegaBase_Zwr hn hN hE⟩

theorem conj_base_one (A B C a b c : ZMod (3 ^ n)) :
    el n A B C 1 * el n a b c 0 * (el n A B C 1)⁻¹ = el n c a b 0 := by
  rw [el_inv_one, el_mul_one, add_zero, el_mul_one]
  congr 1 <;> first | abel | decide

theorem conj_base_two (A B C a b c : ZMod (3 ^ n)) :
    el n A B C 2 * el n a b c 0 * (el n A B C 2)⁻¹ = el n b c a 0 := by
  rw [el_inv_two, el_mul_two, add_zero, el_mul_two]
  congr 1 <;> first | abel | decide

theorem el_one_neg_one_mem_commutator_Zwr :
    el n 1 (-1) 0 0 ∈ commutator (ZWr n) := by
  have h := Subgroup.commutator_mem_commutator
    (H₁ := (⊤ : Subgroup (ZWr n))) (H₂ := (⊤ : Subgroup (ZWr n)))
    (g₁ := el n 1 0 0 0) (g₂ := el n 0 0 0 1) trivial trivial
  rw [commutatorElement_def, commutator_base_one 0 0 0] at h
  exact h

theorem centralizer_commutator_le_base_Zwr (hn : 1 ≤ n) :
    Subgroup.centralizer (commutator (ZWr n) : Set (ZWr n)) ≤ base n := by
  intro g hg
  by_contra hgb
  have hc0_comm : el n 1 (-1) 0 0 * g = g * el n 1 (-1) 0 0 :=
    Subgroup.mem_centralizer_iff.mp hg _ el_one_neg_one_mem_commutator_Zwr
  have hgc : g * el n 1 (-1) 0 0 * g⁻¹ = el n 1 (-1) 0 0 := by
    rw [hc0_comm.symm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨A, B, C, s, hg_eq⟩ : ∃ A B C s, g = el n A B C s := ⟨_, _, _, _, el_eta g⟩
  have hs : s ≠ 0 := by
    intro h0
    apply hgb
    rw [hg_eq, h0]
    exact (el_mem_base_iff A B C 0).mpr rfl
  rcases zmod3_cases s with h0 | h1 | h2
  · exact hs h0
  · rw [hg_eq, h1, conj_base_one] at hgc
    have h0' := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) hgc
    simp only [el_left_zero, toAdd_ofAdd] at h0'
    exact (one_ne_zero_zmod hn) h0'.symm
  · rw [hg_eq, h2, conj_base_two] at hgc
    have h0' := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) hgc
    simp only [el_left_zero, toAdd_ofAdd] at h0'
    exact (one_ne_neg_one_zmod hn) h0'.symm

theorem base_index (n : ℕ) : (base n).index = 3 := by
  rw [base, Subgroup.index_ker]
  have hrange : (RegularWreathProduct.rightHom : ZWr n →* Multiplicative (ZMod 3)).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro q
    exact ⟨RegularWreathProduct.inl q, rfl⟩
  rw [hrange, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem commutator_le_of_normal_nonabelian_Zwr (hn : 1 ≤ n) {T : Subgroup (ZWr n)}
    (hT : T.Normal) (hnab : ¬ IsMulCommutative T) : commutator (ZWr n) ≤ T := by
  haveI := hT
  have hTnotbase : ¬ T ≤ base n := by
    intro h
    apply hnab
    exact ⟨⟨fun a b => Subtype.ext (base_comm (h a.2) (h b.2))⟩⟩
  have hlt : base n < T ⊔ base n := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro hEq
    exact hTnotbase (by rw [hEq]; exact le_sup_left)
  have h1 : (T ⊔ base n).index = 1 := by
    have hlt' : (T ⊔ base n).index < (base n).index := Subgroup.index_strictAnti hlt
    rw [base_index n] at hlt'
    have hdiv : (T ⊔ base n).index ∣ 3 := by
      have h := Subgroup.index_dvd_of_le (le_sup_right : base n ≤ T ⊔ base n)
      rwa [base_index n] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact h
    · omega
  have hsup : T ⊔ base n = ⊤ := Subgroup.index_eq_one.mp h1
  haveI hbasecomm : IsMulCommutative (base n) :=
    ⟨⟨fun a b => Subtype.ext (base_comm a.2 b.2)⟩⟩
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hbasecomm

theorem zwr_centralizer_nonabelian_normal_Zwr (hn : 1 ≤ n) {T : Subgroup (ZWr n)}
    (hT : T.Normal) (hnab : ¬ IsMulCommutative T) :
    Subgroup.centralizer (T : Set (ZWr n)) ≤ Subgroup.center (ZWr n) := by
  have hcomm : commutator (ZWr n) ≤ T := commutator_le_of_normal_nonabelian_Zwr hn hT hnab
  have hTnotbase : ¬ T ≤ base n := by
    intro h
    apply hnab
    exact ⟨⟨fun a b => Subtype.ext (base_comm (h a.2) (h b.2))⟩⟩
  rw [SetLike.le_def] at hTnotbase
  push Not at hTnotbase
  let y := Classical.choose hTnotbase
  have hyT : y ∈ T := (Classical.choose_spec hTnotbase).1
  have hybase : y ∉ base n := (Classical.choose_spec hTnotbase).2
  intro g hg
  have hgbase : g ∈ base n := by
    apply centralizer_commutator_le_base_Zwr hn
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_iff.mp hg c (hcomm hc)
  have hgy : g ∈ Subgroup.centralizer ({y} : Set (ZWr n)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subgroup.mem_centralizer_iff.mp hg y hyT
  rw [center_eq_diag hn]
  exact centralizer_base_le_diag hybase ⟨hgy, hgbase⟩

theorem exists_el_of_mem_base {x : ZWr n} (hx : x ∈ base n) :
    ∃ a b c, x = el n a b c 0 := by
  have hxr : Multiplicative.toAdd x.right = 0 := by
    have h : x.right = 1 := by simpa [base] using hx
    rw [h, toAdd_one]
  exact ⟨_, _, _, by rw [el_eta x, hxr]⟩

theorem el_mem_omegaBase_iff {u v w : ZMod (3 ^ n)} :
    el n u v w 0 ∈ omegaBase n ↔ 3 • u = 0 ∧ 3 • v = 0 ∧ 3 • w = 0 := by
  constructor
  · rintro ⟨-, h3⟩
    rw [el_pow_base, ← el_zero_zero] at h3
    have h0 := congrArg
      (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0))) h3
    have h1 := congrArg
      (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 1))) h3
    have h2 := congrArg
      (fun x : ZWr n => Multiplicative.toAdd (x.left (Multiplicative.ofAdd 2))) h3
    simp only [el_left_zero, el_left_one, el_left_two, toAdd_ofAdd] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨hu, hv, hw⟩
    refine ⟨(el_mem_base_iff u v w 0).mpr rfl, ?_⟩
    rw [el_pow_base, hu, hv, hw]
    exact el_zero_zero

def deltaZ (n : ℕ) (x : ZWr n) : ZWr n :=
  x⁻¹ * (el n 0 0 0 1 * x * (el n 0 0 0 1)⁻¹)

theorem delta_el (a b c : ZMod (3 ^ n)) :
    deltaZ n (el n a b c 0) = el n (c - a) (a - b) (b - c) 0 := by
  unfold deltaZ
  rw [conj_base_one 0 0 0, el_inv_base, el_mul_zero]
  congr 1 <;> abel

theorem deltaZ_mem_omegaBase {x : ZWr n} (hx : x ∈ omegaBase n) :
    deltaZ n x ∈ omegaBase n := by
  obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base hx.1
  rw [el_mem_omegaBase_iff] at hx
  rw [delta_el, el_mem_omegaBase_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [nsmul_sub, hx.1, hx.2.2, sub_zero]
  · rw [nsmul_sub, hx.2.1, hx.1, sub_zero]
  · rw [nsmul_sub, hx.2.2, hx.2.1, sub_zero]

theorem deltaZ_mul {x y : ZWr n} (hx : x ∈ base n) (hy : y ∈ base n) :
    deltaZ n (x * y) = deltaZ n x * deltaZ n y := by
  obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base hx
  obtain ⟨a', b', c', rfl⟩ := exists_el_of_mem_base hy
  rw [el_mul_zero, delta_el, delta_el, delta_el, el_mul_zero]
  congr 1 <;> abel

theorem deltaZ_one (n : ℕ) : deltaZ n 1 = 1 := by
  unfold deltaZ
  simp

@[expose] def deltaA (n : ℕ) : omegaBase n →* omegaBase n where
  toFun x := ⟨deltaZ n x.1, deltaZ_mem_omegaBase x.2⟩
  map_one' := by
    apply Subtype.ext
    exact deltaZ_one n
  map_mul' x y := by
    apply Subtype.ext
    exact deltaZ_mul x.2.1 y.2.1

def eps (n : ℕ) : ZMod (3 ^ n) := ((3 ^ (n - 1) : ℕ) : ZMod (3 ^ n))

theorem three_nsmul_eps (hn : 1 ≤ n) : 3 • eps n = 0 := by
  unfold eps
  rw [nsmul_eq_mul, ← Nat.cast_mul,
    show 3 * 3 ^ (n - 1) = 3 ^ n from by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [Nat.succ_sub_one, pow_succ]
      ring,
    ZMod.natCast_self]

theorem eps_ne_zero (hn : 1 ≤ n) : eps n ≠ 0 := by
  unfold eps
  intro h
  have h' : ((3 ^ (n - 1) : ℕ) : ZMod (3 ^ n)) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hpos : 0 < 3 ^ (n - 1) := pow_pos (by norm_num) _
  have hlt : 3 ^ (n - 1) < 3 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Nat.succ_sub_one, pow_succ]
    simpa using Nat.mul_lt_mul_of_pos_left (by norm_num : (1 : ℕ) < 3)
      (pow_pos (by norm_num : (0 : ℕ) < 3) m)
  exact absurd h' (Nat.not_dvd_of_pos_of_lt hpos hlt)

theorem el_eps_mem_diag (n : ℕ) : el n (eps n) (eps n) (eps n) 0 ∈ diagSub n := by
  refine ⟨Multiplicative.ofAdd (eps n), ?_⟩
  rw [diagHom_apply, toAdd_ofAdd]

theorem el_eps_mem_omegaBase (hn : 1 ≤ n) :
    el n (eps n) (eps n) (eps n) 0 ∈ omegaBase n := by
  rw [el_mem_omegaBase_iff]
  exact ⟨three_nsmul_eps hn, three_nsmul_eps hn, three_nsmul_eps hn⟩

theorem el_eps_ne_one (hn : 1 ≤ n) : el n (eps n) (eps n) (eps n) 0 ≠ 1 := by
  intro h
  have h0 := congrArg
    (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
  simp only [el_left_zero, toAdd_ofAdd, one_left, toAdd_one] at h0
  exact eps_ne_zero hn h0

@[expose] def omegaBaseOne (n : ℕ) : Subgroup (ZWr n) :=
  (deltaA n).ker.map (omegaBase n).subtype

@[expose] def omegaBaseTwo (n : ℕ) : Subgroup (ZWr n) :=
  (deltaA n).range.map (omegaBase n).subtype

theorem omegaBaseOne_eq_inf_diag : omegaBaseOne n = omegaBase n ⊓ diagSub n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change y.1 ∈ diagSub n
    obtain ⟨a, b, c, hx⟩ := exists_el_of_mem_base y.2.1
    rw [hx]
    have hdelta : deltaZ n y.1 = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      simpa [deltaA] using h
    rw [hx, delta_el, ← el_zero_zero] at hdelta
    have h0 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) hdelta
    have h1 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) hdelta
    have h2 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))) hdelta
    simp only [el_left_zero, el_left_one, el_left_two, toAdd_ofAdd] at h0 h1 h2
    exact el_mem_diagSub_iff.mpr ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨hxω, hxD⟩
    obtain ⟨a, b, c, hx⟩ := exists_el_of_mem_base hxω.1
    have hdiag := el_mem_diagSub_iff.mp (hx ▸ hxD)
    refine ⟨⟨x, hxω⟩, ?_, rfl⟩
    change deltaA n ⟨x, hxω⟩ = 1
    apply Subtype.ext
    show deltaZ n x = 1
    rw [hx, delta_el, hdiag.1, hdiag.2]
    simp [el_zero_zero]

theorem card_omegaBaseOne (hn : 1 ≤ n) : Nat.card (omegaBaseOne n) = 3 := by
  have hle : Nat.card (omegaBaseOne n) ≤ 3 := by
    rw [omegaBaseOne_eq_inf_diag, inf_comm]
    exact card_diag_inter_omegaBase_le hn
  have hge : 3 ≤ Nat.card (omegaBaseOne n) := by
    have hz : el n (eps n) (eps n) (eps n) 0 ∈ omegaBaseOne n := by
      rw [omegaBaseOne_eq_inf_diag]
      exact ⟨el_eps_mem_omegaBase hn, el_eps_mem_diag n⟩
    have hz3 : (el n (eps n) (eps n) (eps n) 0) ^ 3 = 1 := by
      rw [el_pow_base, three_nsmul_eps hn, el_zero_zero]
    have hz1 : el n (eps n) (eps n) (eps n) 0 ≠ 1 := el_eps_ne_one hn
    have hord : orderOf (el n (eps n) (eps n) (eps n) 0) = 3 :=
      orderOf_eq_prime hz3 hz1
    have hcard : Nat.card (Subgroup.zpowers (el n (eps n) (eps n) (eps n) 0)) = 3 := by
      rw [Nat.card_zpowers, hord]
    calc 3 = Nat.card (Subgroup.zpowers (el n (eps n) (eps n) (eps n) 0)) := hcard.symm
      _ ≤ Nat.card (omegaBaseOne n) := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hz)
  exact le_antisymm hle hge

theorem card_deltaA_ker (hn : 1 ≤ n) : Nat.card (deltaA n).ker = 3 := by
  have h : Nat.card (omegaBaseOne n) = Nat.card (deltaA n).ker := by
    rw [omegaBaseOne,
      Subgroup.card_map_of_injective (omegaBase n).subtype_injective]
  rw [← h]
  exact card_omegaBaseOne hn

theorem card_deltaA_range (hn : 1 ≤ n) : Nat.card (deltaA n).range = 9 := by
  have h := Subgroup.card_ker_mul_card_range (deltaA n)
  rw [card_deltaA_ker hn, card_omegaBase hn] at h
  omega

theorem card_omegaBaseTwo (hn : 1 ≤ n) : Nat.card (omegaBaseTwo n) = 9 := by
  have h : Nat.card (omegaBaseTwo n) = Nat.card (deltaA n).range := by
    rw [omegaBaseTwo,
      Subgroup.card_map_of_injective (omegaBase n).subtype_injective]
  rw [h, card_deltaA_range hn]

theorem commutator_el_base_zero (a b c A B C : ZMod (3 ^ n)) :
    ⁅el n a b c 0, el n A B C 0⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr
    (base_comm ((el_mem_base_iff a b c 0).mpr rfl) ((el_mem_base_iff A B C 0).mpr rfl))

theorem commutator_el_base_one (a b c A B C : ZMod (3 ^ n)) :
    ⁅el n a b c 0, el n A B C 1⁆ = el n (a - c) (b - a) (c - b) 0 := by
  rw [commutatorElement_def]
  have h : el n A B C 1 * el n a b c 0 * (el n A B C 1)⁻¹ = el n c a b 0 :=
    conj_base_one A B C a b c
  calc el n a b c 0 * el n A B C 1 * (el n a b c 0)⁻¹ * (el n A B C 1)⁻¹
      = el n a b c 0 * (el n A B C 1 * el n a b c 0 * (el n A B C 1)⁻¹)⁻¹ := by
        group
    _ = el n a b c 0 * (el n c a b 0)⁻¹ := by rw [h]
    _ = el n (a - c) (b - a) (c - b) 0 := by
        rw [el_inv_base, el_mul_zero]
        congr 1 <;> abel

theorem commutator_el_base_two (a b c A B C : ZMod (3 ^ n)) :
    ⁅el n a b c 0, el n A B C 2⁆ = el n (a - b) (b - c) (c - a) 0 := by
  rw [commutatorElement_def]
  have h : el n A B C 2 * el n a b c 0 * (el n A B C 2)⁻¹ = el n b c a 0 :=
    conj_base_two A B C a b c
  calc el n a b c 0 * el n A B C 2 * (el n a b c 0)⁻¹ * (el n A B C 2)⁻¹
      = el n a b c 0 * (el n A B C 2 * el n a b c 0 * (el n A B C 2)⁻¹)⁻¹ := by
        group
    _ = el n a b c 0 * (el n b c a 0)⁻¹ := by rw [h]
    _ = el n (a - b) (b - c) (c - a) 0 := by
        rw [el_inv_base, el_mul_zero]
        congr 1 <;> abel

theorem mem_upperCentralSeries_two_iff (hn : 1 ≤ n) {x : ZWr n} :
    x ∈ Subgroup.upperCentralSeries (ZWr n) 2 ↔ ∀ y : ZWr n, ⁅x, y⁆ ∈ diagSub n := by
  rw [Subgroup.mem_upperCentralSeries_succ_iff, Subgroup.upperCentralSeries_one,
    center_eq_diag hn]

theorem mem_Z2_omegaBase_iff (hn : 1 ≤ n) {a b c : ZMod (3 ^ n)}
    (ha : 3 • a = 0) (hb : 3 • b = 0) (hc : 3 • c = 0) :
    el n a b c 0 ∈ Subgroup.upperCentralSeries (ZWr n) 2 ↔ a + b + c = 0 := by
  have h3a : (3 : ZMod (3 ^ n)) * a = 0 := by rwa [nsmul_eq_mul] at ha
  have h3b : (3 : ZMod (3 ^ n)) * b = 0 := by rwa [nsmul_eq_mul] at hb
  have h3c : (3 : ZMod (3 ^ n)) * c = 0 := by rwa [nsmul_eq_mul] at hc
  rw [mem_upperCentralSeries_two_iff hn]
  constructor
  · intro h
    have h1 := h (el n 0 0 0 1)
    rw [commutator_el_base_one a b c 0 0 0, el_mem_diagSub_iff] at h1
    linear_combination h3a - h1.1
  · intro hsum y
    obtain ⟨A, B, C, s, hy⟩ : ∃ A B C s, y = el n A B C s := ⟨_, _, _, _, el_eta y⟩
    rw [hy]
    rcases zmod3_cases s with rfl | rfl | rfl
    · rw [commutator_el_base_zero]
      exact (diagSub n).one_mem
    · rw [commutator_el_base_one, el_mem_diagSub_iff]
      exact ⟨by linear_combination h3a - hsum, by linear_combination h3b - hsum⟩
    · rw [commutator_el_base_two, el_mem_diagSub_iff]
      exact ⟨by linear_combination hsum - h3b, by linear_combination hsum - h3c⟩

theorem mem_omegaBaseTwo_iff (hn : 1 ≤ n) {a b c : ZMod (3 ^ n)}
    (ha : 3 • a = 0) (hb : 3 • b = 0) (hc : 3 • c = 0) :
    el n a b c 0 ∈ omegaBaseTwo n ↔ a + b + c = 0 := by
  constructor
  · rintro ⟨y, hyK, hyx⟩
    obtain ⟨z, hz⟩ := hyK
    obtain ⟨u, v, w, hz_el⟩ := exists_el_of_mem_base z.2.1
    have hdelta : deltaZ n (el n u v w 0) = el n a b c 0 := by
      have h : deltaZ n z.1 = y.1 := congrArg Subtype.val hz
      rw [hz_el] at h
      have hyx' : y.1 = el n a b c 0 := hyx
      rw [hyx'] at h
      simpa [deltaA] using h
    rw [delta_el] at hdelta
    have h0 := congrArg
      (fun z : ZWr n => Multiplicative.toAdd (z.left (Multiplicative.ofAdd 0))) hdelta
    have h1 := congrArg
      (fun z : ZWr n => Multiplicative.toAdd (z.left (Multiplicative.ofAdd 1))) hdelta
    have h2 := congrArg
      (fun z : ZWr n => Multiplicative.toAdd (z.left (Multiplicative.ofAdd 2))) hdelta
    simp only [el_left_zero, el_left_one, el_left_two, toAdd_ofAdd] at h0 h1 h2
    linear_combination -h0 - h1 - h2
  · intro hsum
    have h3a : (3 : ZMod (3 ^ n)) * a = 0 := by rwa [nsmul_eq_mul] at ha
    have h3b : (3 : ZMod (3 ^ n)) * b = 0 := by rwa [nsmul_eq_mul] at hb
    have hy : el n b 0 (a + b) 0 ∈ omegaBase n := by
      rw [el_mem_omegaBase_iff]
      refine ⟨hb, by simp, ?_⟩
      rw [nsmul_add, ha, hb, add_zero]
    have hdelta : deltaZ n (el n b 0 (a + b) 0) = el n a b c 0 := by
      rw [delta_el]
      have hc' : c = -(a + b) := by linear_combination hsum
      rw [hc']
      congr 1 <;> abel
    exact ⟨deltaA n ⟨el n b 0 (a + b) 0, hy⟩,
      ⟨⟨⟨el n b 0 (a + b) 0, hy⟩, rfl⟩, hdelta⟩⟩

theorem omegaBaseTwo_eq_inf_upperCentralSeries (hn : 1 ≤ n) :
    omegaBaseTwo n = omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hx
    have hxω : x ∈ omegaBase n := by rw [← hyx]; exact y.2
    refine ⟨hxω, ?_⟩
    obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base hxω.1
    have hxω' : 3 • a = 0 ∧ 3 • b = 0 ∧ 3 • c = 0 := (el_mem_omegaBase_iff).mp hxω
    have hsum : a + b + c = 0 :=
      (mem_omegaBaseTwo_iff hn hxω'.1 hxω'.2.1 hxω'.2.2).mp hx
    exact (mem_Z2_omegaBase_iff hn hxω'.1 hxω'.2.1 hxω'.2.2).mpr hsum
  · rintro ⟨hxω, hxZ⟩
    obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base hxω.1
    have hxω' : 3 • a = 0 ∧ 3 • b = 0 ∧ 3 • c = 0 := (el_mem_omegaBase_iff).mp hxω
    have hsum : a + b + c = 0 :=
      (mem_Z2_omegaBase_iff hn hxω'.1 hxω'.2.1 hxω'.2.2).mp hxZ
    exact (mem_omegaBaseTwo_iff hn hxω'.1 hxω'.2.1 hxω'.2.2).mpr hsum

theorem deltaZ_mem_of_normal {U : Subgroup (ZWr n)} (hUn : U.Normal) {x : ZWr n}
    (hx : x ∈ U) : deltaZ n x ∈ U := by
  have h1 : el n 0 0 0 1 * x * (el n 0 0 0 1)⁻¹ ∈ U :=
    hUn.conj_mem x hx (el n 0 0 0 1)
  exact U.mul_mem (U.inv_mem hx) h1

theorem mem_omegaBaseOne_iff_deltaZ_eq_one (hn : 1 ≤ n) {x : ZWr n}
    (hx : x ∈ omegaBase n) : x ∈ omegaBaseOne n ↔ deltaZ n x = 1 := by
  obtain ⟨a, b, c, hx_eq⟩ := exists_el_of_mem_base hx.1
  rw [hx_eq] at hx ⊢
  rw [el_mem_omegaBase_iff] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  rw [omegaBaseOne_eq_inf_diag, delta_el]
  constructor
  · rintro ⟨-, hD⟩
    have hab := (el_mem_diagSub_iff.mp hD).1
    have hbc := (el_mem_diagSub_iff.mp hD).2
    rw [hab, hbc, sub_self]
    exact el_zero_zero
  · intro h
    refine ⟨(el_mem_omegaBase_iff).mpr ⟨ha, hb, hc⟩, ?_⟩
    refine el_mem_diagSub_iff.mpr ?_
    rw [← el_zero_zero] at h
    have h0 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
    have h1 := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))) h
    simp only [el_left_zero, el_left_one, toAdd_ofAdd] at h0 h1
    have hab : a = b := sub_eq_zero.mp h1
    have hca : c = a := sub_eq_zero.mp h0
    exact ⟨hab, hab.symm.trans hca.symm⟩

theorem deltaZ_mem_omegaBaseTwo {x : ZWr n} (hx : x ∈ omegaBase n) :
    deltaZ n x ∈ omegaBaseTwo n := by
  exact ⟨deltaA n ⟨x, hx⟩, ⟨⟨⟨x, hx⟩, rfl⟩, rfl⟩⟩

theorem mem_omegaBaseTwo_iff_deltaZ_mem_one (hn : 1 ≤ n) {x : ZWr n}
    (hx : x ∈ omegaBase n) : x ∈ omegaBaseTwo n ↔ deltaZ n x ∈ omegaBaseOne n := by
  obtain ⟨a, b, c, hx_eq⟩ := exists_el_of_mem_base hx.1
  rw [hx_eq] at hx ⊢
  rw [el_mem_omegaBase_iff] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  have h3a : (3 : ZMod (3 ^ n)) * a = 0 := by rwa [nsmul_eq_mul] at ha
  have h3b : (3 : ZMod (3 ^ n)) * b = 0 := by rwa [nsmul_eq_mul] at hb
  rw [mem_omegaBaseTwo_iff hn ha hb hc, omegaBaseOne_eq_inf_diag, delta_el]
  constructor
  · intro hsum
    refine ⟨?_, ?_⟩
    · exact (el_mem_omegaBase_iff).mpr
        ⟨by rw [nsmul_sub, hc, ha, sub_zero],
         by rw [nsmul_sub, ha, hb, sub_zero],
         by rw [nsmul_sub, hb, hc, sub_zero]⟩
    · exact el_mem_diagSub_iff.mpr
        ⟨by linear_combination hsum - h3a,
          by linear_combination hsum - h3b⟩
  · rintro ⟨-, hdiag⟩
    have hdiag' := el_mem_diagSub_iff.mp hdiag
    linear_combination hdiag'.1 + h3a

theorem omegaBaseOne_le_omegaBaseTwo (hn : 1 ≤ n) :
    omegaBaseOne n ≤ omegaBaseTwo n := by
  intro x hx
  rw [omegaBaseOne_eq_inf_diag] at hx
  have hxω : x ∈ omegaBase n := hx.1
  have hxD : x ∈ diagSub n := hx.2
  obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base (omegaBase_le_base hxω)
  have hxω' : 3 • a = 0 ∧ 3 • b = 0 ∧ 3 • c = 0 := (el_mem_omegaBase_iff).mp hxω
  have hdiag := el_mem_diagSub_iff.mp hxD
  exact (mem_omegaBaseTwo_iff hn hxω'.1 hxω'.2.1 hxω'.2.2).mpr (by
    rw [hdiag.1, hdiag.2]
    have hc3 : 3 • c = 0 := hxω'.2.2
    have h3c : (3 : ZMod (3 ^ n)) * c = 0 := by rwa [nsmul_eq_mul] at hc3
    linear_combination h3c)

theorem omegaBase_uniserial (hn : 1 ≤ n) {U : Subgroup (ZWr n)}
    (hU : U ≤ omegaBase n) (hUn : U.Normal) :
    U = ⊥ ∨ U = omegaBaseOne n ∨ U = omegaBaseTwo n ∨ U = omegaBase n := by
  have hdiv27 : Nat.card U ∣ 3 ^ 3 := by
    have h := Subgroup.card_dvd_of_le hU
    rw [card_omegaBase hn, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
    exact h
  by_cases hU2 : U ≤ omegaBaseTwo n
  · by_cases hU1 : U ≤ omegaBaseOne n
    · have hdiv3 : Nat.card U ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hU1
        rwa [card_omegaBaseOne hn] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h1 | h3
      · left; rw [Subgroup.eq_bot_iff_card]; exact h1
      · right; left
        exact Subgroup.eq_of_le_of_card_ge hU1 (by rw [card_omegaBaseOne hn, h3])
    · right; right; left
      have hnot : ∃ x : ZWr n, x ∈ U ∧ x ∉ omegaBaseOne n :=
        Set.not_subset.mp (show ¬ (U : Set (ZWr n)) ⊆ (omegaBaseOne n : Set (ZWr n)) from hU1)
      let x := Classical.choose hnot
      have hxU : x ∈ U := (Classical.choose_spec hnot).1
      have hxnot1 : x ∉ omegaBaseOne n := (Classical.choose_spec hnot).2
      have hxω : x ∈ omegaBase n := hU hxU
      have hx2 : x ∈ omegaBaseTwo n := hU2 hxU
      have hd1 : deltaZ n x ∈ omegaBaseOne n :=
        (mem_omegaBaseTwo_iff_deltaZ_mem_one hn hxω).mp hx2
      have hdU : deltaZ n x ∈ U := deltaZ_mem_of_normal hUn hxU
      have hne : deltaZ n x ≠ 1 := by
        intro h
        exact hxnot1 ((mem_omegaBaseOne_iff_deltaZ_eq_one hn hxω).mpr h)
      have hne_bot : U ⊓ omegaBaseOne n ≠ ⊥ := by
        intro hbot
        have hmem : deltaZ n x ∈ U ⊓ omegaBaseOne n := ⟨hdU, hd1⟩
        rw [hbot] at hmem
        exact hne (by simpa using hmem)
      have hcard1 : Nat.card (U ⊓ omegaBaseOne n : Subgroup (ZWr n)) = 3 := by
        have hdiv := Subgroup.card_dvd_of_le
          (inf_le_right : U ⊓ omegaBaseOne n ≤ omegaBaseOne n)
        rw [card_omegaBaseOne hn] at hdiv
        rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
        · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h1) hne_bot
        · exact h3
      have hlt : U ⊓ omegaBaseOne n < U := by
        rw [lt_iff_le_and_ne]
        exact ⟨inf_le_left, fun heq => hU1 (heq ▸ inf_le_right)⟩
      have hgt : 3 < Nat.card U := by
        have := Subgroup.card_lt_of_lt hlt
        rwa [hcard1] at this
      have hdiv9 : Nat.card U ∣ 3 ^ 2 := by
        have h := Subgroup.card_dvd_of_le hU2
        rw [card_omegaBaseTwo hn, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
        exact h
      have hcardU : Nat.card U = 9 := by
        obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv9
        have hj_eq : j = 2 := by
          rcases Nat.lt_or_ge j 2 with h | h
          · have hle : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          · omega
        rw [hj_eq] at hj
        norm_num at hj
        exact hj
      exact Subgroup.eq_of_le_of_card_ge hU2 (by rw [card_omegaBaseTwo hn, hcardU])
  · right; right; right
    have hnot : ∃ x : ZWr n, x ∈ U ∧ x ∉ omegaBaseTwo n :=
      Set.not_subset.mp (show ¬ (U : Set (ZWr n)) ⊆ (omegaBaseTwo n : Set (ZWr n)) from hU2)
    let x := Classical.choose hnot
    have hxU : x ∈ U := (Classical.choose_spec hnot).1
    have hxnot2 : x ∉ omegaBaseTwo n := (Classical.choose_spec hnot).2
    have hxω : x ∈ omegaBase n := hU hxU
    have hdxU : deltaZ n x ∈ U := deltaZ_mem_of_normal hUn hxU
    have hdxω : deltaZ n x ∈ omegaBase n := deltaZ_mem_omegaBase hxω
    have hdx2 : deltaZ n x ∈ omegaBaseTwo n := deltaZ_mem_omegaBaseTwo hxω
    have hdx_not1 : deltaZ n x ∉ omegaBaseOne n := by
      intro h
      exact hxnot2 ((mem_omegaBaseTwo_iff_deltaZ_mem_one hn hxω).mpr h)
    have hddx1 : deltaZ n (deltaZ n x) ∈ omegaBaseOne n :=
      (mem_omegaBaseTwo_iff_deltaZ_mem_one hn hdxω).mp hdx2
    have hddxU : deltaZ n (deltaZ n x) ∈ U := deltaZ_mem_of_normal hUn hdxU
    have hddx_not1 : deltaZ n (deltaZ n x) ≠ 1 := by
      intro h
      exact hdx_not1 ((mem_omegaBaseOne_iff_deltaZ_eq_one hn hdxω).mpr h)
    have hne_bot : U ⊓ omegaBaseOne n ≠ ⊥ := by
      intro hbot
      have hmem : deltaZ n (deltaZ n x) ∈ U ⊓ omegaBaseOne n := ⟨hddxU, hddx1⟩
      rw [hbot] at hmem
      exact hddx_not1 (by simpa using hmem)
    have hcard1 : Nat.card (U ⊓ omegaBaseOne n : Subgroup (ZWr n)) = 3 := by
      have hdiv := Subgroup.card_dvd_of_le
        (inf_le_right : U ⊓ omegaBaseOne n ≤ omegaBaseOne n)
      rw [card_omegaBaseOne hn] at hdiv
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
      · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h1) hne_bot
      · exact h3
    have hlt12 : U ⊓ omegaBaseOne n < U ⊓ omegaBaseTwo n := by
      rw [lt_iff_le_and_ne]
      refine ⟨fun y hy => ⟨hy.1, omegaBaseOne_le_omegaBaseTwo hn hy.2⟩, ?_⟩
      intro heq
      have hmem : deltaZ n x ∈ U ⊓ omegaBaseTwo n := ⟨hdxU, hdx2⟩
      rw [← heq] at hmem
      exact hdx_not1 hmem.2
    have hcard2 : Nat.card (U ⊓ omegaBaseTwo n : Subgroup (ZWr n)) = 9 := by
      have hdiv := Subgroup.card_dvd_of_le
        (inf_le_right : U ⊓ omegaBaseTwo n ≤ omegaBaseTwo n)
      rw [card_omegaBaseTwo hn, show (9 : ℕ) = 3 ^ 2 by norm_num] at hdiv
      have hgt : 3 < Nat.card (U ⊓ omegaBaseTwo n : Subgroup (ZWr n)) := by
        have := Subgroup.card_lt_of_lt hlt12
        rwa [hcard1] at this
      obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
      have hj_eq : j = 2 := by
        rcases Nat.lt_or_ge j 2 with h | h
        · have hle : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · omega
      rw [hj_eq] at hj
      norm_num at hj
      exact hj
    have hltU : U ⊓ omegaBaseTwo n < U := by
      rw [lt_iff_le_and_ne]
      exact ⟨inf_le_left, fun heq => hU2 (heq ▸ inf_le_right)⟩
    have hgt : 9 < Nat.card U := by
      have := Subgroup.card_lt_of_lt hltU
      rwa [hcard2] at this
    have hcardU : Nat.card U = 27 := by
      obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv27
      have hk_eq : k = 3 := by
        rcases Nat.lt_or_ge k 3 with h | h
        · have hle : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · omega
      rw [hk_eq] at hk
      norm_num at hk
      exact hk
    exact Subgroup.eq_of_le_of_card_ge hU (by rw [card_omegaBase hn, hcardU])

theorem zwr_A_uniserial_Zwr (hn : 1 ≤ n) :
    Nat.card (omegaBase n ⊓ Subgroup.center (ZWr n) : Subgroup (ZWr n)) = 3 ∧
    Nat.card (omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 : Subgroup (ZWr n)) = 9 ∧
    ∀ U : Subgroup (ZWr n), U ≤ omegaBase n → U.Normal →
      U = ⊥ ∨ U = (omegaBase n ⊓ Subgroup.center (ZWr n) : Subgroup (ZWr n)) ∨
        U = (omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 : Subgroup (ZWr n)) ∨
        U = omegaBase n := by
  have h1 : (omegaBase n ⊓ Subgroup.center (ZWr n) : Subgroup (ZWr n)) = omegaBaseOne n := by
    rw [center_eq_diag hn, ← omegaBaseOne_eq_inf_diag]
  have h2 : (omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 : Subgroup (ZWr n)) =
      omegaBaseTwo n := (omegaBaseTwo_eq_inf_upperCentralSeries hn).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, card_omegaBaseOne hn]
  · rw [h2, card_omegaBaseTwo hn]
  · intro U hU hUn
    rcases omegaBase_uniserial hn hU hUn with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (h.trans h1.symm))
    · exact Or.inr (Or.inr (Or.inl (h.trans h2.symm)))
    · exact Or.inr (Or.inr (Or.inr h))

variable {P : Type*} [Group P] [Finite P]

theorem zwr_card_center (hn : 1 ≤ n) (e : P ≃* ZWr n) :
    Nat.card P = 3 ^ (3 * n + 1) ∧ IsCyclic (Subgroup.center P) ∧
      Nat.card (Subgroup.center P) = 3 ^ n := by
  obtain ⟨hcard, hcyc, hcent⟩ := zwr_card_center_Zwr hn
  have hmap : (Subgroup.center P).map (e : P →* ZWr n) = Subgroup.center (ZWr n) :=
    Subgroup.map_center_eq e
  let φ : Subgroup.center P ≃* Subgroup.center (ZWr n) :=
    (e.subgroupMap (Subgroup.center P)).trans (MulEquiv.subgroupCongr hmap)
  haveI : IsCyclic (Subgroup.center (ZWr n)) := hcyc
  have hcycP : IsCyclic (Subgroup.center P) :=
    isCyclic_of_injective φ.toMonoidHom φ.injective
  have hcardP : Nat.card (Subgroup.center P) = Nat.card (Subgroup.center (ZWr n)) :=
    Nat.card_congr φ.toEquiv
  exact ⟨by rw [Nat.card_congr e.toEquiv]; exact hcard, hcycP, by rw [hcardP, hcent]⟩

theorem zwr_pRank (hn : 1 ≤ n) (e : P ≃* ZWr n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup P) = 3 := by
  rw [SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e, zwr_pRank_Zwr hn]

theorem zwr_normal_contains_omega_center (hn : 1 ≤ n) (e : P ≃* ZWr n) {N : Subgroup P}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : ∀ z ∈ Subgroup.center P, z ^ 3 = 1 → z ∈ N := by
  obtain ⟨hcard, hcyc, hcent⟩ := zwr_card_center hn e
  have hP : IsPGroup 3 P := IsPGroup.of_card (n := 3 * n + 1) hcard
  exact center_omega_le_of_normal hn hP hcyc hcent hN hN1

private theorem symm_comp_self_eq_id (e : P ≃* ZWr n) :
    e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id P := by
  ext x
  simp

theorem zwr_unique_E27 (hn : 1 ≤ n) (e : P ≃* ZWr n) :
    ∃ A : Subgroup P, CFSG.elemThompson P 3 = A ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      (∀ E : Subgroup P, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 → E = A) ∧
      (∀ E : Subgroup P, E.Normal → CFSG.Open.IsElemAbelian 3 E → E ≤ A) := by
  obtain ⟨Am, hET, hEA, hEc, huniq, hnorm⟩ := zwr_unique_E27_Zwr hn
  refine ⟨Am.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← CFSG.elemThompson_map_mulEquiv e.symm 3, hET]
  · exact hEA.map e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEc]
  · intro E hE hcard
    rw [← huniq (E.map e.toMonoidHom) (hE.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hcard])]
    rw [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id]
  · intro E hN hE
    have h1 : E.map e.toMonoidHom ≤ Am :=
      hnorm (E.map e.toMonoidHom) (hN.map e.toMonoidHom e.surjective)
        (hE.map e.toMonoidHom)
    have h2 : (E.map e.toMonoidHom).map e.symm.toMonoidHom ≤
        Am.map e.symm.toMonoidHom := Subgroup.map_mono h1
    rwa [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id] at h2

theorem zwr_centralizer_nonabelian_normal (hn : 1 ≤ n) (e : P ≃* ZWr n) {T : Subgroup P}
    (hT : T.Normal) (hnab : ¬ IsMulCommutative T) :
    Subgroup.centralizer (T : Set P) ≤ Subgroup.center P := by
  have hTmap : (T.map e.toMonoidHom).Normal := hT.map e.toMonoidHom e.surjective
  have hnabmap : ¬ IsMulCommutative (T.map e.toMonoidHom) := by
    intro h
    apply hnab
    refine ⟨⟨fun x y => Subtype.ext (e.injective ?_)⟩⟩
    have hc := congrArg Subtype.val (h.is_comm.comm
      ⟨e (x : P), Subgroup.mem_map_of_mem e.toMonoidHom x.2⟩
      ⟨e (y : P), Subgroup.mem_map_of_mem e.toMonoidHom y.2⟩)
    simpa only [map_mul, Subgroup.coe_mul] using hc
  intro g hg
  have hgmap : e g ∈ Subgroup.centralizer ((T.map e.toMonoidHom) : Set (ZWr n)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hc
    have h := Subgroup.mem_centralizer_iff.mp hg t ht
    simpa using congrArg e h
  have hcenter : e g ∈ Subgroup.center (ZWr n) :=
    zwr_centralizer_nonabelian_normal_Zwr hn hTmap hnabmap hgmap
  rw [← Subgroup.map_center_eq e] at hcenter
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp hcenter
  rwa [e.injective hgg'] at hg'

theorem zwr_A_uniserial (hn : 1 ≤ n) (e : P ≃* ZWr n) {A : Subgroup P}
    (hA : CFSG.elemThompson P 3 = A) :
    Nat.card (A ⊓ Subgroup.center P : Subgroup P) = 3 ∧
    Nat.card (A ⊓ Subgroup.upperCentralSeries P 2 : Subgroup P) = 9 ∧
    ∀ U : Subgroup P, U ≤ A → U.Normal →
      U = ⊥ ∨ U = A ⊓ Subgroup.center P ∨ U = A ⊓ Subgroup.upperCentralSeries P 2 ∨ U = A := by
  obtain ⟨hcard1, hcard2, huni⟩ := zwr_A_uniserial_Zwr hn
  have hAmap : A.map e.toMonoidHom = omegaBase n := by
    rw [← hA, CFSG.elemThompson_map_mulEquiv e 3, zwr_elemThompson_Zwr hn]
  have hupper : (Subgroup.upperCentralSeries P 2).map e.toMonoidHom =
      Subgroup.upperCentralSeries (ZWr n) 2 := by
    have hcomap := Subgroup.comap_upperCentralSeries e 2
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  have hcentermap : (A ⊓ Subgroup.center P : Subgroup P).map e.toMonoidHom =
      (omegaBase n ⊓ Subgroup.center (ZWr n) : Subgroup (ZWr n)) := by
    rw [Subgroup.map_inf A (Subgroup.center P) e.toMonoidHom e.injective, hAmap]
    exact congrArg (fun S : Subgroup (ZWr n) => omegaBase n ⊓ S)
      (Subgroup.map_center_eq e)
  have hZmap : (A ⊓ Subgroup.upperCentralSeries P 2 : Subgroup P).map e.toMonoidHom =
      (omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 : Subgroup (ZWr n)) := by
    rw [Subgroup.map_inf A (Subgroup.upperCentralSeries P 2) e.toMonoidHom e.injective,
      hAmap, hupper]
  have hAmap' : (omegaBase n).map e.symm.toMonoidHom = A := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hAmap
    rw [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id] at h
    exact h.symm
  have hcentermap' :
      (omegaBase n ⊓ Subgroup.center (ZWr n) : Subgroup (ZWr n)).map e.symm.toMonoidHom =
        (A ⊓ Subgroup.center P : Subgroup P) := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hcentermap
    rw [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id] at h
    exact h.symm
  have hZmap' :
      (omegaBase n ⊓ Subgroup.upperCentralSeries (ZWr n) 2 : Subgroup (ZWr n)).map
        e.symm.toMonoidHom = (A ⊓ Subgroup.upperCentralSeries P 2 : Subgroup P) := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hZmap
    rw [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id] at h
    exact h.symm
  refine ⟨?_, ?_, ?_⟩
  · have hc := Subgroup.card_map_of_injective (K := (A ⊓ Subgroup.center P : Subgroup P))
      (f := e.toMonoidHom) e.injective
    rw [hcentermap] at hc
    rw [← hc]
    exact hcard1
  · have hc := Subgroup.card_map_of_injective
      (K := (A ⊓ Subgroup.upperCentralSeries P 2 : Subgroup P))
      (f := e.toMonoidHom) e.injective
    rw [hZmap] at hc
    rw [← hc]
    exact hcard2
  · intro U hU hUn
    have hUmap : U.map e.toMonoidHom ≤ omegaBase n := by
      rw [← hAmap]
      exact Subgroup.map_mono hU
    have hUnmap : (U.map e.toMonoidHom).Normal := hUn.map e.toMonoidHom e.surjective
    have hback {V : Subgroup (ZWr n)} (hV : U.map e.toMonoidHom = V) :
        U = V.map e.symm.toMonoidHom := by
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) hV
      rwa [Subgroup.map_map, symm_comp_self_eq_id, Subgroup.map_id] at h
    rcases huni (U.map e.toMonoidHom) hUmap hUnmap with h | h | h | h
    · left
      rw [hback h, Subgroup.map_bot]
    · right; left
      exact (hback h).trans hcentermap'
    · right; right; left
      exact (hback h).trans hZmap'
    · right; right; right
      exact (hback h).trans hAmap'

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

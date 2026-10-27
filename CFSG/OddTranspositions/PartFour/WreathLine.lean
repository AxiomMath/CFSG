module

public import CFSG.OddTranspositions.PartFour.LineShort
public import CFSG.OddTranspositions.PartFour.SeventeenFourSp
public import CFSG.OddTranspositions.PartFour.SideConditions
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81

section Model

variable {L : Type} [Group L] {m : ℕ}

theorem wreathLine_act_apply (σ : Equiv.Perm (Fin m)) (h : Fin m → L) (i : Fin m) :
    wreathAct L m σ h i = h (σ⁻¹ i) := rfl

theorem wreathLine_act_symm_apply (σ : Equiv.Perm (Fin m)) (h : Fin m → L) (i : Fin m) :
    (wreathAct L m σ).symm h i = h (σ i) := rfl

theorem wreathLine_conj_inr_right (c : WreathSym L m) (s : Equiv.Perm (Fin m)) :
    (c * SemidirectProduct.inr s * c⁻¹).right = c.right * s * c.right⁻¹ := by
  simp

theorem wreathLine_conj_inr_left (c : WreathSym L m) (s : Equiv.Perm (Fin m)) (k : Fin m) :
    (c * SemidirectProduct.inr s * c⁻¹).left k =
      c.left k * (c.left ((c.right * s * c.right⁻¹)⁻¹ k))⁻¹ := by
  simp [wreathLine_act_apply, wreathLine_act_symm_apply, Equiv.Perm.mul_apply]

theorem wreathLine_isConj_inr_swap_iff {a b : Fin m} (hab : a ≠ b) (x : WreathSym L m) :
    IsConj (SemidirectProduct.inr (Equiv.swap a b)) x ↔ ∃ i j : Fin m, i ≠ j ∧
      x.right = Equiv.swap i j ∧ (∀ k, k ≠ i → k ≠ j → x.left k = 1) ∧
      x.left j = (x.left i)⁻¹ := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    have hr : c.right * Equiv.swap a b * c.right⁻¹ = Equiv.swap (c.right a) (c.right b) :=
      (Equiv.swap_apply_apply c.right a b).symm
    refine ⟨c.right a, c.right b, c.right.injective.ne hab,
      by rw [wreathLine_conj_inr_right, hr], ?_, ?_⟩
    · intro k hka hkb
      rw [wreathLine_conj_inr_left, hr, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hka hkb, mul_inv_cancel]
    · rw [wreathLine_conj_inr_left, wreathLine_conj_inr_left, hr, Equiv.swap_inv,
        Equiv.swap_apply_left, Equiv.swap_apply_right, mul_inv_rev, inv_inv]
  · rintro ⟨i, j, hij, hr, hsupp, hj⟩
    obtain ⟨σ, hσ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hij)
    refine isConj_iff.2 ⟨⟨Pi.mulSingle i (x.left i), σ⟩, SemidirectProduct.ext ?_ ?_⟩
    · funext k
      rw [wreathLine_conj_inr_left]
      simp only [hσ, Equiv.swap_inv]
      by_cases hki : k = i
      · rw [hki, Equiv.swap_apply_left, Pi.mulSingle_eq_same,
          Pi.mulSingle_eq_of_ne hij.symm, inv_one, mul_one]
      by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, Pi.mulSingle_eq_same,
          Pi.mulSingle_eq_of_ne hij.symm, one_mul, hj]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, mul_inv_cancel, hsupp k hki hkj]
    · rw [wreathLine_conj_inr_right]
      exact hσ.trans hr.symm

def wreathLine_sigma (k l : Fin m) (z : L) : WreathSym L m :=
  SemidirectProduct.inl (Pi.mulSingle k z) * SemidirectProduct.inr (Equiv.swap k l) *
    (SemidirectProduct.inl (Pi.mulSingle k z))⁻¹

theorem wreathLine_sigma_right (k l : Fin m) (z : L) :
    (wreathLine_sigma k l z).right = Equiv.swap k l := by
  rw [wreathLine_sigma, wreathLine_conj_inr_right]
  simp

theorem wreathLine_sigma_left_apply {k l : Fin m} (z : L) (p : Fin m) :
    (wreathLine_sigma k l z).left p =
      (Pi.mulSingle k z * (Pi.mulSingle k z ∘ Equiv.swap k l)⁻¹ : Fin m → L) p := by
  rw [wreathLine_sigma, wreathLine_conj_inr_left]
  simp [Equiv.swap_inv, Pi.mul_apply]

theorem wreathLine_sigma_left_self {k l : Fin m} (hkl : k ≠ l) (z : L) :
    (wreathLine_sigma k l z).left k = z := by
  rw [wreathLine_sigma_left_apply]
  simp [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hkl.symm,
    Equiv.swap_apply_left]

theorem wreathLine_sigma_left_right {k l : Fin m} (hkl : k ≠ l) (z : L) :
    (wreathLine_sigma k l z).left l = z⁻¹ := by
  rw [wreathLine_sigma_left_apply]
  simp [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hkl.symm,
    Equiv.swap_apply_right]

theorem wreathLine_sigma_left_ne {k l : Fin m} (hkl : k ≠ l) (z : L) {p : Fin m}
    (hpk : p ≠ k) (hpl : p ≠ l) : (wreathLine_sigma k l z).left p = 1 := by
  rw [wreathLine_sigma_left_apply]
  simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hpk, Pi.mulSingle_eq_of_ne hpl,
    Equiv.swap_apply_of_ne_of_ne hpk hpl]

theorem wreathLine_sigma_isConj {a b k l : Fin m} (hab : a ≠ b) (hkl : k ≠ l) (z : L) :
    IsConj (SemidirectProduct.inr (Equiv.swap a b)) (wreathLine_sigma k l z) := by
  have h1 : IsConj (SemidirectProduct.inr (Equiv.swap k l)) (wreathLine_sigma k l z) :=
    isConj_iff.2 ⟨SemidirectProduct.inl (Pi.mulSingle k z), by rw [wreathLine_sigma]⟩
  exact (MonoidHom.map_isConj SemidirectProduct.inr (Equiv.Perm.isConj_swap hab hkl)).trans h1

theorem wreathLine_sigma_swap {i j : Fin m} (hij : i ≠ j) (y : L) :
    wreathLine_sigma j i y = wreathLine_sigma i j y⁻¹ := by
  refine SemidirectProduct.ext (funext fun p => ?_) ?_
  · by_cases hpi : p = i
    · subst hpi
      rw [wreathLine_sigma_left_right (Ne.symm hij), wreathLine_sigma_left_self hij]
    · by_cases hpj : p = j
      · subst hpj
        rw [wreathLine_sigma_left_self (Ne.symm hij), wreathLine_sigma_left_right hij, inv_inv]
      · rw [wreathLine_sigma_left_ne (Ne.symm hij) y hpj hpi,
          wreathLine_sigma_left_ne hij y⁻¹ hpi hpj]
  · rw [wreathLine_sigma_right, wreathLine_sigma_right, Equiv.swap_comm]

theorem wreathLine_eq_sigma {x : WreathSym L m} {i j : Fin m} (hij : i ≠ j)
    (hr : x.right = Equiv.swap i j) (hsupp : ∀ k, k ≠ i → k ≠ j → x.left k = 1)
    (hj : x.left j = (x.left i)⁻¹) : x = wreathLine_sigma i j (x.left i) := by
  refine SemidirectProduct.ext (funext fun p => ?_) ?_
  · by_cases hpi : p = i
    · subst hpi
      rw [wreathLine_sigma_left_self hij]
    · by_cases hpj : p = j
      · subst hpj
        rw [wreathLine_sigma_left_right hij]
        exact hj
      · rw [hsupp p hpi hpj, wreathLine_sigma_left_ne hij (x.left i) hpi hpj]
  · rw [hr, wreathLine_sigma_right]

theorem wreathLine_commute_of_disjoint {x y : WreathSym L m} {i j k l : Fin m}
    (hx : x.right = Equiv.swap i j) (hxl : ∀ p, p ≠ i → p ≠ j → x.left p = 1)
    (hy : y.right = Equiv.swap k l) (hyl : ∀ p, p ≠ k → p ≠ l → y.left p = 1)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : Commute x y := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap i j) (Equiv.swap k l) := fun p => by
    by_cases hpi : p = i
    · exact Or.inr (hpi ▸ Equiv.swap_apply_of_ne_of_ne hik hil)
    by_cases hpj : p = j
    · exact Or.inr (hpj ▸ Equiv.swap_apply_of_ne_of_ne hjk hjl)
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hpi hpj)
  refine SemidirectProduct.ext (funext fun p => ?_) ?_
  · simp only [SemidirectProduct.mul_left, Pi.mul_apply, wreathLine_act_apply, hx, hy,
      Equiv.swap_inv]
    by_cases hpi : p = i
    · rw [hpi, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hik hil, hyl _ hjk hjl,
        hyl _ hik hil, mul_one, one_mul]
    by_cases hpj : p = j
    · rw [hpj, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hjk hjl, hyl _ hik hil,
        hyl _ hjk hjl, mul_one, one_mul]
    rw [Equiv.swap_apply_of_ne_of_ne hpi hpj, hxl p hpi hpj, one_mul]
    by_cases hpk : p = k
    · rw [hpk, Equiv.swap_apply_left, hxl _ (Ne.symm hil) (Ne.symm hjl), mul_one]
    by_cases hpl : p = l
    · rw [hpl, Equiv.swap_apply_right, hxl _ (Ne.symm hik) (Ne.symm hjk), mul_one]
    rw [Equiv.swap_apply_of_ne_of_ne hpk hpl, hxl p hpi hpj, mul_one]
  · simp only [SemidirectProduct.mul_right, hx, hy]
    exact hd.commute

theorem wreathLine_swap_commute_cases {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l)
    (h : Commute (Equiv.swap i j) (Equiv.swap k l)) :
    (k = i ∧ l = j) ∨ (k = j ∧ l = i) ∨
      (k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j) := by
  have hpt : ∀ p : Fin m, Equiv.swap i j (Equiv.swap k l p) =
      Equiv.swap k l (Equiv.swap i j p) := by
    intro p
    have hp := congrArg (fun e : Equiv.Perm (Fin m) => e p) h.eq
    simpa [Equiv.Perm.mul_apply] using hp
  by_cases hki : k = i
  · subst hki
    by_cases hlj : l = j
    · exact Or.inl ⟨rfl, hlj⟩
    · exfalso
      have h1 := hpt l
      simp only [Equiv.swap_apply_right, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hkl) hlj] at h1
      exact hij h1.symm
  by_cases hkj : k = j
  · subst hkj
    by_cases hli : l = i
    · exact Or.inr (Or.inl ⟨rfl, hli⟩)
    · exfalso
      have h1 := hpt l
      simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hli (Ne.symm hkl)] at h1
      exact hij h1
  · by_cases hli : l = i
    · subst hli
      exfalso
      have h1 := hpt k
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hki hkj] at h1
      exact hij h1.symm
    · by_cases hlj : l = j
      · subst hlj
        exfalso
        have h1 := hpt k
        simp only [Equiv.swap_apply_right, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hki hkj] at h1
        exact hij h1
      · exact Or.inr (Or.inr ⟨hki, hkj, hli, hlj⟩)

theorem wreathLine_sigma_mul_left_self {i j : Fin m} (hij : i ≠ j) (y z : L) :
    (wreathLine_sigma i j y * wreathLine_sigma i j z).left i = y * z⁻¹ := by
  rw [SemidirectProduct.mul_left, Pi.mul_apply, wreathLine_sigma_right,
    wreathLine_act_apply, Equiv.swap_inv, Equiv.swap_apply_left,
    wreathLine_sigma_left_self hij, wreathLine_sigma_left_right hij]

theorem wreathLine_commute_sigma_sigma {i j : Fin m} (hij : i ≠ j) (y z : L) :
    Commute (wreathLine_sigma i j y) (wreathLine_sigma i j z) ↔
      (y * z⁻¹) * (y * z⁻¹) = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : WreathSym L m => w.left i) h.eq
    rw [wreathLine_sigma_mul_left_self hij, wreathLine_sigma_mul_left_self hij z y] at h1
    have h3 : z * y⁻¹ = (y * z⁻¹)⁻¹ := by simp
    nth_rewrite 1 [h1]
    rw [h3, inv_mul_cancel]
  · intro h
    have hyz : y * z⁻¹ = z * y⁻¹ := by
      calc y * z⁻¹ = (y * z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = z * y⁻¹ := by simp
    have hyz' : y⁻¹ * z = z⁻¹ * y := by
      calc y⁻¹ * z = y⁻¹ * (z * y⁻¹) * y := by group
        _ = y⁻¹ * (y * z⁻¹) * y := by rw [← hyz]
        _ = z⁻¹ * y := by group
    refine SemidirectProduct.ext (funext fun p => ?_) ?_
    · by_cases hpi : p = i
      · subst hpi
        simp only [SemidirectProduct.mul_left, Pi.mul_apply, wreathLine_sigma_right,
          wreathLine_act_apply, Equiv.swap_inv, Equiv.swap_apply_left,
          wreathLine_sigma_left_self hij, wreathLine_sigma_left_right hij]
        exact hyz
      · by_cases hpj : p = j
        · subst hpj
          simp only [SemidirectProduct.mul_left, Pi.mul_apply, wreathLine_sigma_right,
            wreathLine_act_apply, Equiv.swap_inv, Equiv.swap_apply_right,
            wreathLine_sigma_left_self hij, wreathLine_sigma_left_right hij]
          exact hyz'
        · simp only [SemidirectProduct.mul_left, Pi.mul_apply, wreathLine_sigma_right,
            wreathLine_act_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hpi hpj,
            wreathLine_sigma_left_ne hij y hpi hpj, wreathLine_sigma_left_ne hij z hpi hpj]
    · simp only [SemidirectProduct.mul_right, wreathLine_sigma_right]

theorem wreathLine_sigma_one (i j : Fin m) :
    wreathLine_sigma i j (1 : L) = SemidirectProduct.inr (Equiv.swap i j) := by
  simp [wreathLine_sigma]

theorem wreathLine_sigma_eq_inr_of_commute
    (hL₁ : ∀ y : L, y * y = 1 → y ≠ 1 → ∃ z : L, z * z = 1 ∧ (y * z) * (y * z) ≠ 1)
    {a b i j p q : Fin m} (hij : i ≠ j)
    (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hclass : ∀ z : L, IsConj (SemidirectProduct.inr (Equiv.swap a b))
      (wreathLine_sigma i j z))
    {y : L}
    (hself : Commute (wreathLine_sigma i j y) (SemidirectProduct.inr (Equiv.swap i j)))
    (hother : Commute (wreathLine_sigma i j y) (SemidirectProduct.inr (Equiv.swap p q)))
    (hxsub : perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap i j)) ∩
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap p q)) ⊆
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (wreathLine_sigma i j y)) :
    wreathLine_sigma i j y = SemidirectProduct.inr (Equiv.swap i j) := by
  by_cases hy1 : y = 1
  · rw [hy1, wreathLine_sigma_one]
  · exfalso
    have hself' : Commute (wreathLine_sigma i j y) (wreathLine_sigma i j (1 : L)) := by
      rwa [wreathLine_sigma_one i j]
    have hsq : y * y = 1 := by
      have h := (wreathLine_commute_sigma_sigma hij (y := y) (z := 1)).1 hself'
      simpa using h
    obtain ⟨z, hz2, hyz⟩ := hL₁ y hsq hy1
    have hu_self : Commute (wreathLine_sigma i j z)
        (SemidirectProduct.inr (Equiv.swap i j)) := by
      rw [← wreathLine_sigma_one i j, wreathLine_commute_sigma_sigma hij]
      simpa using hz2
    have hu_other : Commute (wreathLine_sigma i j z)
        (SemidirectProduct.inr (Equiv.swap p q)) :=
      wreathLine_commute_of_disjoint (wreathLine_sigma_right i j z)
        (fun r hr1 hr2 => wreathLine_sigma_left_ne hij z hr1 hr2) rfl
        (fun _ _ _ => rfl) hip hiq hjp hjq
    have hnot : ¬ Commute (wreathLine_sigma i j z) (wreathLine_sigma i j y) := by
      intro hc
      have h := (wreathLine_commute_sigma_sigma hij (y := y) (z := z)).1 hc.symm
      have hz : z⁻¹ = z := (eq_inv_of_mul_eq_one_right hz2).symm
      rw [hz] at h
      exact hyz h
    exact hnot (hxsub ⟨⟨hclass z, hu_self⟩, ⟨hclass z, hu_other⟩⟩).2

theorem wreathLine_sigma_disjoint_false (hL₂ : ∃ t : L, t * t ≠ 1)
    {a b c d k l : Fin m} (hkl : k ≠ l)
    (hclass : ∀ z : L, IsConj (SemidirectProduct.inr (Equiv.swap a b))
      (wreathLine_sigma k l z))
    (hka : k ≠ a) (hkb : k ≠ b) (hla : l ≠ a) (hlb : l ≠ b)
    (hkc : k ≠ c) (hkd : k ≠ d) (hlc : l ≠ c) (hld : l ≠ d)
    {y : L}
    (hxsub : perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) ∩
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap c d)) ⊆
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (wreathLine_sigma k l y)) : False := by
  obtain ⟨t, ht⟩ := hL₂
  have huS : wreathLine_sigma k l (t * y) ∈
      {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x} := hclass (t * y)
  have hu_v : Commute (wreathLine_sigma k l (t * y))
      (SemidirectProduct.inr (Equiv.swap a b)) :=
    wreathLine_commute_of_disjoint (wreathLine_sigma_right k l (t * y))
      (fun r hr1 hr2 => wreathLine_sigma_left_ne hkl (t * y) hr1 hr2) rfl
      (fun _ _ _ => rfl) hka hkb hla hlb
  have hu_w : Commute (wreathLine_sigma k l (t * y))
      (SemidirectProduct.inr (Equiv.swap c d)) :=
    wreathLine_commute_of_disjoint (wreathLine_sigma_right k l (t * y))
      (fun r hr1 hr2 => wreathLine_sigma_left_ne hkl (t * y) hr1 hr2) rfl
      (fun _ _ _ => rfl) hkc hkd hlc hld
  have hnot : ¬ Commute (wreathLine_sigma k l (t * y)) (wreathLine_sigma k l y) := by
    intro hc
    have h := (wreathLine_commute_sigma_sigma hkl (y := t * y) (z := y)).1 hc
    exact ht (by simpa [mul_assoc] using h)
  exact hnot (hxsub ⟨⟨huS, hu_v⟩, ⟨huS, hu_w⟩⟩).2

theorem isConj_inr_swap_and_commute {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    IsConj (SemidirectProduct.inr (Equiv.swap a b) : WreathSym L m)
        (SemidirectProduct.inr (Equiv.swap c d)) ∧
      Commute (SemidirectProduct.inr (Equiv.swap a b) : WreathSym L m)
        (SemidirectProduct.inr (Equiv.swap c d)) := by
  refine ⟨MonoidHom.map_isConj SemidirectProduct.inr (Equiv.Perm.isConj_swap hab hcd), ?_⟩
  exact wreathLine_commute_of_disjoint rfl (fun _ _ _ => rfl) rfl (fun _ _ _ => rfl)
    hac had hbc hbd

theorem perpMem_inr_swap_ne (hL : ∃ t : L, t * t ≠ 1) {a b c d : Fin m} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) ≠
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap c d)) := by
  obtain ⟨t, ht⟩ := hL
  have huS : wreathLine_sigma c d t ∈
      {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x} :=
    wreathLine_sigma_isConj hab hcd t
  have hu_v : Commute (wreathLine_sigma c d t)
      (SemidirectProduct.inr (Equiv.swap a b)) :=
    wreathLine_commute_of_disjoint (wreathLine_sigma_right c d t)
      (fun p hp1 hp2 => wreathLine_sigma_left_ne hcd t hp1 hp2) rfl
      (fun _ _ _ => rfl) (Ne.symm hac) (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd)
  have hu_not : ¬ Commute (wreathLine_sigma c d t)
      (SemidirectProduct.inr (Equiv.swap c d)) := by
    intro hc
    have h' : Commute (wreathLine_sigma c d t) (wreathLine_sigma c d (1 : L)) := by
      rwa [wreathLine_sigma_one c d]
    have h := (wreathLine_commute_sigma_sigma hcd (y := t) (z := 1)).1 h'
    exact ht (by simpa using h)
  intro heq
  have hu_mem : wreathLine_sigma c d t ∈
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) := ⟨huS, hu_v⟩
  rw [heq] at hu_mem
  exact hu_not hu_mem.2

theorem wreathLine_lineMem_data {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {x : WreathSym L m}
    (hx : x ∈ lineMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) (SemidirectProduct.inr (Equiv.swap c d))) :
    ∃ (k l : Fin m) (y : L), k ≠ l ∧ x = wreathLine_sigma k l y ∧
      Commute x (SemidirectProduct.inr (Equiv.swap a b)) ∧
      Commute x (SemidirectProduct.inr (Equiv.swap c d)) ∧
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap a b)) ∩
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap c d)) ⊆
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (wreathLine_sigma k l y) := by
  rw [mem_lineMem] at hx
  obtain ⟨hxS, hxsub⟩ := hx
  have hvS : SemidirectProduct.inr (Equiv.swap a b) ∈
      {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x} :=
    IsConj.refl (SemidirectProduct.inr (Equiv.swap a b) : WreathSym L m)
  have hwS : SemidirectProduct.inr (Equiv.swap c d) ∈
      {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x} :=
    (isConj_inr_swap_and_commute (L := L) (m := m) hab hac had hbc hbd hcd).1
  have hvw : Commute (SemidirectProduct.inr (Equiv.swap a b))
      (SemidirectProduct.inr (Equiv.swap c d)) :=
    (isConj_inr_swap_and_commute (L := L) (m := m) hab hac had hbc hbd hcd).2
  have hv_mem : SemidirectProduct.inr (Equiv.swap a b) ∈
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap a b)) ∩
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap c d)) :=
    ⟨⟨hvS, Commute.refl (SemidirectProduct.inr (Equiv.swap a b) : WreathSym L m)⟩,
      ⟨hvS, hvw⟩⟩
  have hw_mem : SemidirectProduct.inr (Equiv.swap c d) ∈
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap a b)) ∩
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap c d)) :=
    ⟨⟨hwS, hvw.symm⟩,
      ⟨hwS, Commute.refl (SemidirectProduct.inr (Equiv.swap c d) : WreathSym L m)⟩⟩
  have hxv : Commute x (SemidirectProduct.inr (Equiv.swap a b)) := (hxsub hv_mem).2.symm
  have hxw : Commute x (SemidirectProduct.inr (Equiv.swap c d)) := (hxsub hw_mem).2.symm
  obtain ⟨k, l, hkl, hr, hsupp, hj⟩ := (wreathLine_isConj_inr_swap_iff hab x).1 hxS
  set y : L := x.left k with hy
  have hxeq : x = wreathLine_sigma k l y := by
    rw [hy]
    exact wreathLine_eq_sigma hkl hr hsupp hj
  rw [hxeq] at hxsub
  exact ⟨k, l, y, hkl, hxeq, hxv, hxw, hxsub⟩

theorem wreathLine_lineMem_case_ab
    (hL₁ : ∀ y : L, y * y = 1 → y ≠ 1 → ∃ z : L, z * z = 1 ∧ (y * z) * (y * z) ≠ 1)
    {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {y : L}
    (hxv : Commute (wreathLine_sigma a b y) (SemidirectProduct.inr (Equiv.swap a b)))
    (hxw : Commute (wreathLine_sigma a b y) (SemidirectProduct.inr (Equiv.swap c d)))
    (hxsub : perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap a b)) ∩
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap c d)) ⊆
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (wreathLine_sigma a b y)) :
    wreathLine_sigma a b y ∈ ({SemidirectProduct.inr (Equiv.swap a b),
      SemidirectProduct.inr (Equiv.swap c d)} : Set (WreathSym L m)) := by
  have h : wreathLine_sigma a b y = SemidirectProduct.inr (Equiv.swap a b) :=
    wreathLine_sigma_eq_inr_of_commute (L := L) (m := m) hL₁ hab hac had hbc hbd
      (fun z => wreathLine_sigma_isConj (L := L) (m := m) hab hab z) hxv hxw hxsub
  rw [h]
  simp

theorem wreathLine_lineMem_case_cd
    (hL₁ : ∀ y : L, y * y = 1 → y ≠ 1 → ∃ z : L, z * z = 1 ∧ (y * z) * (y * z) ≠ 1)
    {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {y : L}
    (hxv : Commute (wreathLine_sigma c d y) (SemidirectProduct.inr (Equiv.swap a b)))
    (hxw : Commute (wreathLine_sigma c d y) (SemidirectProduct.inr (Equiv.swap c d)))
    (hxsub : perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap a b)) ∩
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (SemidirectProduct.inr (Equiv.swap c d)) ⊆
        perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
          (wreathLine_sigma c d y)) :
    wreathLine_sigma c d y ∈ ({SemidirectProduct.inr (Equiv.swap a b),
      SemidirectProduct.inr (Equiv.swap c d)} : Set (WreathSym L m)) := by
  have hxsub' : perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap c d)) ∩
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) ⊆
      perpMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (wreathLine_sigma c d y) := by
    rw [Set.inter_comm]
    exact hxsub
  have h : wreathLine_sigma c d y = SemidirectProduct.inr (Equiv.swap c d) :=
    wreathLine_sigma_eq_inr_of_commute (L := L) (m := m) hL₁ hcd (Ne.symm hac)
      (Ne.symm hbc) (Ne.symm had) (Ne.symm hbd)
      (fun z => wreathLine_sigma_isConj (L := L) (m := m) hab hcd z) hxw hxv hxsub'
  rw [h]
  simp

theorem lineMem_inr_swap_subset
    (hL₁ : ∀ y : L, y * y = 1 → y ≠ 1 → ∃ z : L, z * z = 1 ∧ (y * z) * (y * z) ≠ 1)
    (hL₂ : ∃ t : L, t * t ≠ 1) {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    lineMem {x : WreathSym L m | IsConj (SemidirectProduct.inr (Equiv.swap a b)) x}
        (SemidirectProduct.inr (Equiv.swap a b)) (SemidirectProduct.inr (Equiv.swap c d)) ⊆
      {SemidirectProduct.inr (Equiv.swap a b), SemidirectProduct.inr (Equiv.swap c d)} := by
  intro x hx
  obtain ⟨k, l, y, hkl, rfl, hxv, hxw, hxsub⟩ :=
    wreathLine_lineMem_data hab hac had hbc hbd hcd hx
  have hcomm_v : Commute (Equiv.swap k l) (Equiv.swap a b) := by
    simpa [wreathLine_sigma_right] using hxv.map SemidirectProduct.rightHom
  have hcomm_w : Commute (Equiv.swap k l) (Equiv.swap c d) := by
    simpa [wreathLine_sigma_right] using hxw.map SemidirectProduct.rightHom
  rcases wreathLine_swap_commute_cases hab hkl hcomm_v.symm with
    ⟨hk, hl⟩ | ⟨hk, hl⟩ | ⟨hka, hkb, hla, hlb⟩
  · rw [hk, hl] at hxv hxw hxsub ⊢
    exact wreathLine_lineMem_case_ab hL₁ hab hac had hbc hbd hcd hxv hxw hxsub
  · rw [hk, hl] at hxv hxw hxsub ⊢
    rw [wreathLine_sigma_swap hab] at hxv hxw hxsub ⊢
    exact wreathLine_lineMem_case_ab hL₁ hab hac had hbc hbd hcd hxv hxw hxsub
  · rcases wreathLine_swap_commute_cases hcd hkl hcomm_w.symm with
      ⟨hk, hl⟩ | ⟨hk, hl⟩ | ⟨hkc, hkd, hlc, hld⟩
    · rw [hk, hl] at hxv hxw hxsub ⊢
      exact wreathLine_lineMem_case_cd hL₁ hab hac had hbc hbd hcd hxv hxw hxsub
    · rw [hk, hl] at hxv hxw hxsub ⊢
      rw [wreathLine_sigma_swap hcd] at hxv hxw hxsub ⊢
      exact wreathLine_lineMem_case_cd hL₁ hab hac had hbc hbd hcd hxv hxw hxsub
    · exfalso
      exact wreathLine_sigma_disjoint_false hL₂ hkl (fun z => wreathLine_sigma_isConj hab hkl z)
        hka hkb hla hlb hkc hkd hlc hld hxsub

end Model

section SL2

variable {F : Type} [Field F] [CharP F 2]

theorem exists_mul_self_ne_one_sl2 :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F, t * t ≠ 1 := by
  let t : Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.CGT.Timmesfeld75.sl2Mk 0 1 1 1 (by simpa using (CharTwo.neg_eq (1 : F)))
  have ht00 : t 0 0 = 0 := by simp [t, CFSG.CGT.Timmesfeld75.sl2Mk]
  have ht01 : t 0 1 = 1 := by simp [t, CFSG.CGT.Timmesfeld75.sl2Mk]
  have ht11 : t 1 1 = 1 := by simp [t, CFSG.CGT.Timmesfeld75.sl2Mk]
  refine ⟨t, ?_⟩
  intro h
  have h01 : (t * t) 0 1 = (1 : Matrix.SpecialLinearGroup (Fin 2) F) 0 1 :=
    congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 0 1) h
  simp [CFSG.CGT.Timmesfeld75.mul_apply_01, CFSG.CGT.Timmesfeld75.one_apply_01,
    ht00, ht01, ht11] at h01

theorem wreathLine_sl2_entry_facts (y : Matrix.SpecialLinearGroup (Fin 2) F) (hy : y * y = 1) :
    y 0 0 * y 0 0 + y 0 1 * y 1 0 = 1 ∧
    y 0 0 * y 0 1 + y 0 1 * y 1 1 = 0 ∧
    y 1 0 * y 0 0 + y 1 1 * y 1 0 = 0 ∧
    y 1 0 * y 0 1 + y 1 1 * y 1 1 = 1 ∧
    y 0 1 * (y 0 0 + y 1 1) = 0 ∧ y 1 0 * (y 0 0 + y 1 1) = 0 := by
  have h00 : y 0 0 * y 0 0 + y 0 1 * y 1 0 = 1 := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 0 0) hy
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.one_apply_00] using h
  have h01 : y 0 0 * y 0 1 + y 0 1 * y 1 1 = 0 := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 0 1) hy
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_01, CFSG.CGT.Timmesfeld75.one_apply_01] using h
  have h10 : y 1 0 * y 0 0 + y 1 1 * y 1 0 = 0 := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 1 0) hy
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_10, CFSG.CGT.Timmesfeld75.one_apply_10] using h
  have h11 : y 1 0 * y 0 1 + y 1 1 * y 1 1 = 1 := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 1 1) hy
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_11, CFSG.CGT.Timmesfeld75.one_apply_11] using h
  refine ⟨h00, h01, h10, h11, ?_, ?_⟩
  · rw [mul_add, mul_comm (y 0 1) (y 0 0)]
    exact h01
  · rw [mul_add, mul_comm (y 1 0) (y 1 1)]
    exact h10

theorem wreathLine_sl2_eq_one_of_entries (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : y 0 1 = 0) (hr : y 1 0 = 0) (h00 : y 0 0 * y 0 0 + y 0 1 * y 1 0 = 1)
    (h11 : y 1 0 * y 0 1 + y 1 1 * y 1 1 = 1) : y = 1 := by
  have hp : y 0 0 * y 0 0 = 1 := by simpa [hq, hr] using h00
  have hs : y 1 1 * y 1 1 = 1 := by simpa [hq, hr] using h11
  have hp1 : y 0 0 = 1 := CharTwo.sq_inj.mp (by rw [sq, one_pow]; exact hp)
  have hs1 : y 1 1 = 1 := CharTwo.sq_inj.mp (by rw [sq, one_pow]; exact hs)
  apply CFSG.CGT.Timmesfeld75.sl2_ext <;>
    simp [hp1, hs1, hq, hr, CFSG.CGT.Timmesfeld75.one_apply_00,
      CFSG.CGT.Timmesfeld75.one_apply_01, CFSG.CGT.Timmesfeld75.one_apply_10,
      CFSG.CGT.Timmesfeld75.one_apply_11]

theorem wreathLine_sl2_exists_of_q_eq_zero (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : y 0 1 = 0) (hr : y 1 0 ≠ 0) (hrs : y 1 0 * (y 0 0 + y 1 1) = 0) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) F, z * z = 1 ∧ (y * z) * (y * z) ≠ 1 := by
  let z : Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.CGT.Timmesfeld75.sl2Mk 1 1 0 1 (by norm_num)
  have hz00 : z 0 0 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz01 : z 0 1 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz10 : z 1 0 = 0 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz11 : z 1 1 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz : z * z = 1 := by
    apply CFSG.CGT.Timmesfeld75.mul_self_eq_one_of_trace_eq_zero
    simp [z, CFSG.CGT.Timmesfeld75.sl2Mk, CFSG.CGT.Timmesfeld75.one_apply_00,
      CFSG.CGT.Timmesfeld75.one_apply_11, CharTwo.add_self_eq_zero]
  refine ⟨z, hz, ?_⟩
  intro h
  have hen : y 1 0 * y 0 0 + (y 1 0 + y 1 1) * y 1 0 = 0 := by
    have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 1 0) h
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_10,
      CFSG.CGT.Timmesfeld75.mul_apply_11, CFSG.CGT.Timmesfeld75.one_apply_10,
      hz00, hz01, hz10, hz11] using h'
  have hr0 : y 1 0 * y 1 0 = 0 := by linear_combination hen - hrs
  exact hr (mul_self_eq_zero.mp hr0)

theorem wreathLine_sl2_exists_of_q_ne_zero (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : y 0 1 ≠ 0) (hqs : y 0 1 * (y 0 0 + y 1 1) = 0) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) F, z * z = 1 ∧ (y * z) * (y * z) ≠ 1 := by
  let z : Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.CGT.Timmesfeld75.sl2Mk 1 0 1 1 (by norm_num)
  have hz00 : z 0 0 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz01 : z 0 1 = 0 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz10 : z 1 0 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz11 : z 1 1 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have hz : z * z = 1 := by
    apply CFSG.CGT.Timmesfeld75.mul_self_eq_one_of_trace_eq_zero
    simp [z, CFSG.CGT.Timmesfeld75.sl2Mk, CFSG.CGT.Timmesfeld75.one_apply_00,
      CFSG.CGT.Timmesfeld75.one_apply_11, CharTwo.add_self_eq_zero]
  refine ⟨z, hz, ?_⟩
  intro h
  have hen : (y 0 0 + y 0 1) * y 0 1 + y 0 1 * y 1 1 = 0 := by
    have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 0 1) h
    simpa [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_01,
      CFSG.CGT.Timmesfeld75.mul_apply_11, CFSG.CGT.Timmesfeld75.one_apply_01,
      hz00, hz01, hz10, hz11] using h'
  have hq0 : y 0 1 * y 0 1 = 0 := by linear_combination hen - hqs
  exact hq (mul_self_eq_zero.mp hq0)

theorem exists_involution_mul_mul_self_ne_one_sl2 (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) F, z * z = 1 ∧ (y * z) * (y * z) ≠ 1 := by
  obtain ⟨h00, -, -, h11, hqs, hrs⟩ := wreathLine_sl2_entry_facts y hy
  by_cases hq : y 0 1 = 0
  · by_cases hr : y 1 0 = 0
    · exact absurd (wreathLine_sl2_eq_one_of_entries y hq hr h00 h11) hy1
    · exact wreathLine_sl2_exists_of_q_eq_zero y hq hr hrs
  · exact wreathLine_sl2_exists_of_q_ne_zero y hq hqs

theorem exists_pow_ne_one_sl2 {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) F, ∀ k : ℕ, 0 < k → k ≤ 3 → z ^ k ≠ 1 := by
  let z : Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.CGT.Timmesfeld75.sl2Mk a 1 1 0 (by simpa using (CharTwo.neg_eq (1 : F)))
  have h00 : z 0 0 = a := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have h01 : z 0 1 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have h10 : z 1 0 = 1 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  have h11 : z 1 1 = 0 := by simp [z, CFSG.CGT.Timmesfeld75.sl2Mk]
  refine ⟨z, fun k hk0 hk3 hk => ?_⟩
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g 0 1) hk
  interval_cases k
  · simp [CFSG.CGT.Timmesfeld75.one_apply_01, h01] at h
  · rw [pow_two] at h
    simp [CFSG.CGT.Timmesfeld75.mul_apply_01, CFSG.CGT.Timmesfeld75.one_apply_01, h00, h01,
      h11] at h
    exact ha0 h
  · rw [pow_succ, pow_two] at h
    simp [CFSG.CGT.Timmesfeld75.mul_apply_01, CFSG.CGT.Timmesfeld75.mul_apply_00,
      CFSG.CGT.Timmesfeld75.one_apply_01, h00, h01, h10, h11] at h
    have hsq : (a + 1) * (a + 1) = 0 := by
      linear_combination h + a * (CharTwo.two_eq_zero (R := F))
    have ha : a = -1 := eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp hsq)
    exact ha1 (by rw [ha, CharTwo.neg_eq])

end SL2

theorem wreathLine_exists_pow_ne_one {F : Type} [Field F] [CharP F 2] {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ v w : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m,
      IsConj (SemidirectProduct.inr (Equiv.swap i j)) v ∧
        IsConj (SemidirectProduct.inr (Equiv.swap i j)) w ∧
          ∀ k : ℕ, 0 < k → k ≤ 3 → (v * w) ^ k ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_pow_ne_one_sl2 ha0 ha1
  refine ⟨wreathLine_sigma i j z, wreathLine_sigma i j 1, wreathLine_sigma_isConj hij hij z,
    wreathLine_sigma_isConj hij hij 1, fun k hk0 hk3 hk => hz k hk0 hk3 ?_⟩
  set x := wreathLine_sigma i j z * wreathLine_sigma i j 1 with hx
  have hright : x.right = 1 := by
    rw [hx, SemidirectProduct.mul_right, wreathLine_sigma_right, wreathLine_sigma_right,
      Equiv.swap_mul_self]
  have hxe : x = SemidirectProduct.inl x.left :=
    SemidirectProduct.ext (SemidirectProduct.left_inl _).symm
      (by rw [hright, SemidirectProduct.right_inl])
  have hleft : x.left i = z := by
    rw [hx, wreathLine_sigma_mul_left_self hij, inv_one, mul_one]
  have h := congrArg (fun y : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m => y.left i) hk
  rw [hxe, ← map_pow, SemidirectProduct.left_inl, Pi.pow_apply, hleft] at h
  simpa using h

theorem wreathLine_exists_fin_pair {m : ℕ} (hm : 4 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ∃ c d : Fin m, c ≠ d ∧ c ≠ i ∧ c ≠ j ∧ d ≠ i ∧ d ≠ j := by
  have hcard : 1 < (Finset.univ \ ({i, j} : Finset (Fin m))).card := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
      Finset.card_pair hij]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hc hd
  exact ⟨c, d, hcd, hc.1, hc.2, hd.1, hd.2⟩

theorem wreathLine_ncard_le_two_of_lineMem_subset {X : Type} [Group X] {S : Set X} {v w : X}
    (h : lineMem S v w ⊆ {v, w}) : (perpMem S '' lineMem S v w).ncard ≤ 2 := by
  have himg : perpMem S '' lineMem S v w ⊆ perpMem S '' ({v, w} : Set X) := Set.image_mono h
  refine (Set.ncard_le_ncard himg ?_).trans ?_
  · rw [Set.image_pair]
    exact Set.finite_insert.mpr (Set.finite_singleton _)
  · rw [Set.image_pair]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem wreathLine_wreath_sl2_exists {F : Type} [Field F] [CharP F 2] {m : ℕ} (hm : 4 ≤ m)
    {i j : Fin m} (hij : i ≠ j) {t : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m}
    (hclass : {x | IsConj t x} =
      {x : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m |
        IsConj (SemidirectProduct.inr (Equiv.swap i j)) x}) :
    ∃ v ∈ {x | IsConj t x}, ∃ w ∈ {x | IsConj t x}, Commute v w ∧
      perpMem {x | IsConj t x} v ≠ perpMem {x | IsConj t x} w ∧
      (perpMem {x | IsConj t x} '' lineMem {x | IsConj t x} v w).ncard ≤ 2 := by
  obtain ⟨c, d, hcd, hci, hcj, hdi, hdj⟩ := wreathLine_exists_fin_pair hm hij
  have hac : i ≠ c := Ne.symm hci
  have had : i ≠ d := Ne.symm hdi
  have hbc : j ≠ c := Ne.symm hcj
  have hbd : j ≠ d := Ne.symm hdj
  let v' : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m :=
    SemidirectProduct.inr (Equiv.swap i j)
  let w' : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m :=
    SemidirectProduct.inr (Equiv.swap c d)
  have hv' : v' ∈ {x | IsConj t x} := by
    rw [hclass]
    exact IsConj.refl v'
  have hw' : w' ∈ {x | IsConj t x} := by
    rw [hclass]
    exact (isConj_inr_swap_and_commute (L := Matrix.SpecialLinearGroup (Fin 2) F)
      hij hac had hbc hbd hcd).1
  have hvw' : Commute v' w' :=
    (isConj_inr_swap_and_commute (L := Matrix.SpecialLinearGroup (Fin 2) F)
      hij hac had hbc hbd hcd).2
  have hne' : perpMem {x | IsConj t x} v' ≠ perpMem {x | IsConj t x} w' := by
    rw [hclass]
    exact perpMem_inr_swap_ne (L := Matrix.SpecialLinearGroup (Fin 2) F)
      (show ∃ u : Matrix.SpecialLinearGroup (Fin 2) F, u * u ≠ 1 from
        exists_mul_self_ne_one_sl2) hij hac had hbc hbd hcd
  have hline' : lineMem {x | IsConj t x} v' w' ⊆ {v', w'} := by
    rw [hclass]
    exact lineMem_inr_swap_subset (L := Matrix.SpecialLinearGroup (Fin 2) F)
      (fun y hy hy1 => exists_involution_mul_mul_self_ne_one_sl2 y hy hy1)
      exists_mul_self_ne_one_sl2 hij hac had hbc hbd hcd
  exact ⟨v', hv', w', hw', hvw', hne', wreathLine_ncard_le_two_of_lineMem_subset hline'⟩

theorem wreathLine_exists_pullback {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) {s : X}
    {v' w' : Y} (hv' : v' ∈ {y | IsConj (φ s) y}) (hw' : w' ∈ {y | IsConj (φ s) y})
    (hvw' : Commute v' w')
    (hne' : perpMem {y | IsConj (φ s) y} v' ≠ perpMem {y | IsConj (φ s) y} w')
    (hcount' : (perpMem {y | IsConj (φ s) y} '' lineMem {y | IsConj (φ s) y} v' w').ncard ≤ 2) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 := by
  let v : X := φ.symm v'
  let w : X := φ.symm w'
  have hφv : φ v = v' := φ.apply_symm_apply v'
  have hφw : φ w = w' := φ.apply_symm_apply w'
  have hclass : φ '' {x | IsConj s x} = {y | IsConj (φ s) y} :=
    CFSG.Fischer.image_setOf_isConj φ s
  have hclass' : φ.symm '' {y | IsConj (φ s) y} = {x | IsConj s x} := by
    simpa using CFSG.Fischer.image_setOf_isConj φ.symm (φ s)
  have hv : v ∈ {x | IsConj s x} := by
    obtain ⟨u, hu, rfl⟩ := hclass.symm ▸ hv'
    simpa [v] using hu
  have hw : w ∈ {x | IsConj s x} := by
    obtain ⟨u, hu, rfl⟩ := hclass.symm ▸ hw'
    simpa [w] using hu
  have hvw : Commute v w := by simpa [v, w] using hvw'.map φ.symm.toMonoidHom
  have hne : perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w := by
    intro h
    apply hne'
    have hV : perpMem {x | IsConj s x} v = φ.symm '' perpMem {y | IsConj (φ s) y} v' := by
      rw [← hφv, ← hclass, perpMem_image_mulEquiv]
      exact (CFSG.Fischer.image_symm_image φ (perpMem {x | IsConj s x} v)).symm
    have hW : perpMem {x | IsConj s x} w = φ.symm '' perpMem {y | IsConj (φ s) y} w' := by
      rw [← hφw, ← hclass, perpMem_image_mulEquiv]
      exact (CFSG.Fischer.image_symm_image φ (perpMem {x | IsConj s x} w)).symm
    exact (Set.image_injective.mpr φ.symm.injective) (by rw [← hV, ← hW]; exact h)
  have hcount : (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 := by
    have hEq := ncard_perpMem_image_lineMem_mulEquiv φ.symm {y | IsConj (φ s) y} v' w'
    rw [hclass'] at hEq
    calc (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard
        = (perpMem {y | IsConj (φ s) y} '' lineMem {y | IsConj (φ s) y} v' w').ncard := hEq
      _ ≤ 2 := hcount'
  exact ⟨v, hv, w, hw, hvw, hne, hcount⟩

theorem exists_lineMem_ncard_le_two_of_isWreathTransposition {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {f m : ℕ} (hm : 4 ≤ m)
    (hs : IsWreathTransposition X f m s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 := by
  obtain ⟨-, F, hF, hFin, hFcard, e, i, j, hij, hconj⟩ := hs
  letI := hF
  letI := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : X, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  have hclass : {x : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m | IsConj (φ s) x} =
      {x : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m |
        IsConj (SemidirectProduct.inr (Equiv.swap i j)) x} := by
    rw [hφ]
    ext x
    constructor
    · intro hx
      exact hconj.symm.trans hx
    · intro hx
      exact hconj.trans hx
  obtain ⟨v', hv', w', hw', hvw', hne', hcount'⟩ :=
    wreathLine_wreath_sl2_exists (F := F) hm hij hclass
  exact wreathLine_exists_pullback φ hv' hw' hvw' hne' hcount'

theorem exists_pow_ne_one_of_isWreathTransposition {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {f m : ℕ} (hs : IsWreathTransposition X f m s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, ∀ k : ℕ, 0 < k → k ≤ 3 → (v * w) ^ k ≠ 1 := by
  obtain ⟨hf, F, hF, hFin, hFcard, e, i, j, hij, hconj⟩ := hs
  letI := hF
  letI := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  obtain ⟨a, -, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := ({0, 1} : Set F))
    (t := Set.univ) (by
      rw [Set.ncard_univ, hFcard]
      calc ({0, 1} : Set F).ncard ≤ 2 :=
            (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
        _ < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : X, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  obtain ⟨v, w, hv, hw, hk⟩ := wreathLine_exists_pow_ne_one (F := F) hij ha.1 ha.2
  have hconj' : ∀ y, IsConj (SemidirectProduct.inr (Equiv.swap i j)) y →
      IsConj s (φ.symm y) := by
    intro y hy
    have h1 : IsConj (φ s) y := by
      rw [hφ]
      exact hconj.trans hy
    simpa using MonoidHom.map_isConj φ.symm.toMonoidHom h1
  refine ⟨φ.symm v, hconj' v hv, φ.symm w, hconj' w hw, fun k hk0 hk3 h => hk k hk0 hk3 ?_⟩
  simpa using congrArg φ h

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_isWreathTransposition (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {f m : ℕ} (hm : 4 ≤ m)
    (hsw : IsWreathTransposition
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) f m s) : False := by
  have hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
    obtain ⟨v, hv, w, hw, hk⟩ :=
      exists_pow_ne_one_of_isWreathTransposition (center_eq_bot_quotient_H hC) hsw
    rw [← imageClass_eq_setOf_isConj hC hs] at hv hw
    exact not_threeTransp_of_pow_ne_one hC hv hw hk
  obtain ⟨v, hv, w, hw, hvw, hne, h2⟩ :=
    exists_lineMem_ncard_le_two_of_isWreathTransposition (center_eq_bot_quotient_H hC) hm hsw
  rw [← imageClass_eq_setOf_isConj hC hs] at hv hw hne h2
  exact false_of_ncard_perpMem_lineMem_le_two h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne h2

end CFSG.OddTranspositions.PartFour

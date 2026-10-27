module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNum
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType.FrameRoute

open CFSG SpCoord Multiplicative

variable {k : ℕ}

@[expose] def signedPermSet (k : ℕ) : Set (MulAut (Fin k → Multiplicative (ZMod 3))) :=
  {u | IsSignedPerm ⇑u}

@[expose] def negSwapAut (a b : Fin k) : MulAut (Fin k → Multiplicative (ZMod 3)) :=
  sgnAut a * sgnAut b * permAut (Equiv.swap a b)

section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem frameMB_negSwapAut_apply {a b : Fin k} (hab : a ≠ b)
    (f : Fin k → Multiplicative (ZMod 3)) (j : Fin k) :
    negSwapAut a b f j = if j = a then (f b)⁻¹ else if j = b then (f a)⁻¹ else f j := by
  rw [negSwapAut, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply, sgnAut_apply,
    permAut_apply]
  simp only [Function.comp_apply, Equiv.swap_inv, Function.update_apply]
  by_cases hja : j = a
  · subst hja
    simp [hab]
  · by_cases hjb : j = b
    · subst hjb
      simp [hja, Ne.symm hab]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
      simp [hja, hjb]

private lemma frameMB_card_ker_mul_three {M : Type*} [Group M] [Finite M]
    (f : M →* Multiplicative (ZMod 3)) (hf : Function.Surjective f) :
    Nat.card f.ker * 3 = Nat.card M := by
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h := Subgroup.card_ker_mul_card_range f
  rwa [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, h3] at h

private def frameMB_delta (i b : Fin k) (c : ZMod 3) :
    (Fin k → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3) where
  toFun f := ofAdd (toAdd (f b) - c * toAdd (f i))
  map_one' := by simp
  map_mul' f g := by
    simp only [Pi.mul_apply, toAdd_mul]
    rw [← ofAdd_add]
    congr 1
    ring

private theorem frameMB_delta_apply (i b : Fin k) (c : ZMod 3)
    (f : Fin k → Multiplicative (ZMod 3)) :
    frameMB_delta i b c f = ofAdd (toAdd (f b) - c * toAdd (f i)) :=
  rfl

private lemma frameMB_delta_surjective {i b : Fin k} (c : ZMod 3) (hib : i ≠ b) :
    Function.Surjective (frameMB_delta i b c) := by
  intro y
  refine ⟨Pi.mulSingle b y, ?_⟩
  rw [frameMB_delta_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hib]
  simp

private theorem frameMB_isSignedPerm_negSwapAut {a b : Fin k} (hab : a ≠ b) :
    IsSignedPerm (⇑(negSwapAut a b : MulAut (Fin k → Multiplicative (ZMod 3)))) := by
  refine ⟨Equiv.swap a b, fun i => if i = a ∨ i = b then -1 else 1, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = a ∨ i = b
    · rw [if_pos h]
      exact Or.inr rfl
    · rw [if_neg h]
      exact Or.inl rfl
  · intro f i
    dsimp only
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, frameMB_negSwapAut_apply hab]
      rw [if_neg (Ne.symm hab), if_pos rfl, if_pos (Or.inl rfl), toAdd_inv, neg_one_mul]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, frameMB_negSwapAut_apply hab]
        rw [if_pos rfl, if_pos (Or.inr rfl), toAdd_inv, neg_one_mul]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib, frameMB_negSwapAut_apply hab]
        rw [if_neg hia, if_neg hib, if_neg (by tauto), one_mul]

private theorem frameMB_negSwapAut_sq {a b : Fin k} (hab : a ≠ b) :
    (negSwapAut a b : MulAut (Fin k → Multiplicative (ZMod 3))) ^ 2 = 1 := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
  rw [sq, MulAut.mul_apply]
  simp only [frameMB_negSwapAut_apply hab]
  by_cases hja : j = a
  · subst hja
    simp [Ne.symm hab, toAdd_inv]
  · by_cases hjb : j = b
    · subst hjb
      simp [hja, toAdd_inv]
    · simp [hja, hjb]

private theorem frameMB_card_fix_negSwapAut {a b : Fin k} (hab : a ≠ b) :
    Nat.card {f : Fin k → Multiplicative (ZMod 3) // negSwapAut a b f = f} * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3)) := by
  have hsurj := frameMB_delta_surjective (i := a) (b := b) (-1) hab
  have hcard := frameMB_card_ker_mul_three (frameMB_delta a b (-1)) hsurj
  have hker : Nat.card {f : Fin k → Multiplicative (ZMod 3) // negSwapAut a b f = f} =
      Nat.card (frameMB_delta a b (-1)).ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    rw [MonoidHom.mem_ker, frameMB_delta_apply]
    constructor
    · intro h
      have h1 := congrArg (fun g => toAdd (g a)) h
      rw [frameMB_negSwapAut_apply hab] at h1
      simp only [if_pos rfl, toAdd_inv, if_true] at h1
      have h2 : toAdd (f b) - (-1) * toAdd (f a) = 0 := by linear_combination -h1
      rw [h2, ofAdd_zero]
    · intro h
      have h1 : toAdd (f b) - (-1) * toAdd (f a) = 0 := by
        have := congrArg toAdd h
        simpa using this
      refine eq_of_toAdd_eq fun j => ?_
      rw [frameMB_negSwapAut_apply hab]
      by_cases hja : j = a
      · subst hja
        rw [if_pos rfl, toAdd_inv]
        linear_combination -h1
      · by_cases hjb : j = b
        · subst hjb
          rw [if_neg (Ne.symm hab), if_pos rfl, toAdd_inv]
          linear_combination -h1
        · rw [if_neg hja, if_neg hjb]
  rw [hker]
  exact hcard

private def frameMB_fixedSubgroup (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    Subgroup (Fin k → Multiplicative (ZMod 3)) where
  carrier := {f | u f = f}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [map_mul, hf, hg]
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [map_inv, hf]

private lemma frameMB_card_ker_eval (i : Fin k) :
    Nat.card (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 3)) i).ker * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3)) := by
  refine frameMB_card_ker_mul_three _ ?_
  intro y
  refine ⟨Function.update 1 i y, ?_⟩
  simp [Pi.evalMonoidHom, Function.update_self]

private lemma frameMB_forward_pi_one {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    {ε : Fin k → ZMod 3} (hall : ∀ i, ε i = 1)
    (hu : ∀ f i, toAdd (u f i) = ε i * toAdd (f i))
    (hcard : Nat.card (frameMB_fixedSubgroup u) * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3))) : False := by
  have hu1 : u = 1 := by
    refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
    rw [hu f i, hall i, one_mul]
    rfl
  have htop : frameMB_fixedSubgroup u = ⊤ := by
    ext f
    simp [frameMB_fixedSubgroup, hu1]
  rw [htop, Subgroup.card_top] at hcard
  have hpos : 0 < Nat.card (Fin k → Multiplicative (ZMod 3)) := Nat.card_pos
  omega

private lemma frameMB_forward_pi_one_eq {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    {ε : Fin k → ZMod 3} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f i) = ε i * toAdd (f i))
    (hcard : Nat.card (frameMB_fixedSubgroup u) * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3)))
    {i : Fin k} (hi : ε i = -1) : u = sgnAut i := by
  let H : Subgroup (Fin k → Multiplicative (ZMod 3)) :=
    (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 3)) i).ker
  have hle : frameMB_fixedSubgroup u ≤ H := by
    intro f hf
    change f i = 1
    change u f = f at hf
    have h1 : toAdd (f i) = -toAdd (f i) := by
      calc toAdd (f i) = toAdd (u f i) := by rw [hf]
        _ = ε i * toAdd (f i) := hu f i
        _ = -toAdd (f i) := by rw [hi]; ring
    have h0 : toAdd (f i) = 0 :=
      coord_eq_zero_of_eq_neg (p := 3) Nat.prime_three (by decide) h1
    exact toAdd.injective (by simpa using h0)
  have hHcard : Nat.card H * 3 = Nat.card (Fin k → Multiplicative (ZMod 3)) :=
    frameMB_card_ker_eval i
  have heqcard : Nat.card (frameMB_fixedSubgroup u) = Nat.card H := by
    apply Nat.mul_right_cancel (by norm_num : 0 < 3)
    rw [hcard, hHcard]
  have hH : frameMB_fixedSubgroup u = H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq heqcard.symm)
  have hε_one : ∀ j, j ≠ i → ε j = 1 := by
    intro j hj
    have he : (Pi.mulSingle j (ofAdd 1) : Fin k → Multiplicative (ZMod 3)) ∈ H := by
      change (Pi.mulSingle j (ofAdd 1) : Fin k → Multiplicative (ZMod 3)) i = 1
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hj)]
    have he' : (Pi.mulSingle j (ofAdd 1) : Fin k → Multiplicative (ZMod 3)) ∈
        frameMB_fixedSubgroup u := hH ▸ he
    change u (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) at he'
    have happ := IsSignedPerm.apply_mulSingle (π := 1) (ε := ε) hu j 1
    rw [he'] at happ
    have h2 := congrArg (fun g => toAdd (g j)) happ
    simp only [toAdd_mulSingle, Equiv.Perm.one_apply, if_true, mul_one] at h2
    exact h2.symm
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
  by_cases hji : j = i
  · subst hji
    rw [hu f j, hi, sgnAut_apply, Function.update_self, toAdd_inv]
    ring
  · rw [hu f j, hε_one j hji, one_mul, sgnAut_apply, Function.update_of_ne hji]

private structure frameMB_SignedData (u : MulAut (Fin k → Multiplicative (ZMod 3))) where
  π : Equiv.Perm (Fin k)
  ε : Fin k → ZMod 3
  hε : ∀ i, ε i = 1 ∨ ε i = -1
  hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)

private lemma frameMB_fixedSubgroup_le_ker {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) {i : Fin k} (hi : D.π i ≠ i) :
    frameMB_fixedSubgroup u ≤ (frameMB_delta i (D.π i) (D.ε i)).ker := by
  intro f hf
  rw [MonoidHom.mem_ker, frameMB_delta_apply]
  change u f = f at hf
  have h1 : toAdd (f (D.π i)) = D.ε i * toAdd (f i) := by
    calc toAdd (f (D.π i)) = toAdd (u f (D.π i)) := by rw [hf]
      _ = D.ε i * toAdd (f i) := D.hu f i
  rw [h1, sub_self, ofAdd_zero]

private lemma frameMB_fixedSubgroup_eq_ker {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) {i : Fin k} (hi : D.π i ≠ i)
    (hcard : Nat.card (frameMB_fixedSubgroup u) * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3))) :
    frameMB_fixedSubgroup u = (frameMB_delta i (D.π i) (D.ε i)).ker := by
  have hle := frameMB_fixedSubgroup_le_ker D hi
  have hsurj := frameMB_delta_surjective (i := i) (b := D.π i) (D.ε i) (Ne.symm hi)
  have hHcard : Nat.card (frameMB_delta i (D.π i) (D.ε i)).ker * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3)) :=
    frameMB_card_ker_mul_three _ hsurj
  have heqcard : Nat.card (frameMB_fixedSubgroup u) =
      Nat.card (frameMB_delta i (D.π i) (D.ε i)).ker := by
    apply Nat.mul_right_cancel (by norm_num : 0 < 3)
    rw [hcard, hHcard]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq heqcard.symm)

private lemma frameMB_forward_ne_one_shape {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) {i : Fin k} (hi : D.π i ≠ i)
    (hcard : Nat.card (frameMB_fixedSubgroup u) * 3 =
      Nat.card (Fin k → Multiplicative (ZMod 3))) :
    (∀ j, j ≠ i → j ≠ D.π i → D.π j = j ∧ D.ε j = 1) ∧
      D.π = Equiv.swap i (D.π i) ∧ D.ε (D.π i) = D.ε i := by
  have hH := frameMB_fixedSubgroup_eq_ker D hi hcard
  have hout : ∀ j, j ≠ i → j ≠ D.π i → D.π j = j ∧ D.ε j = 1 := by
    intro j hji hjb
    have he : (Pi.mulSingle j (ofAdd 1) : Fin k → Multiplicative (ZMod 3)) ∈
        (frameMB_delta i (D.π i) (D.ε i)).ker := by
      rw [MonoidHom.mem_ker, frameMB_delta_apply]
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hjb), Pi.mulSingle_eq_of_ne (Ne.symm hji)]
      simp
    have he' : (Pi.mulSingle j (ofAdd 1) : Fin k → Multiplicative (ZMod 3)) ∈
        frameMB_fixedSubgroup u := hH.symm ▸ he
    change u (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) at he'
    have happ := IsSignedPerm.apply_mulSingle (π := D.π) (ε := D.ε) D.hu j 1
    rw [he'] at happ
    obtain ⟨hπj, hεj⟩ := mulSingle_ofAdd_eq_iff (p := 3)
      (coord_zero_ne_one (p := 3) Nat.prime_three).symm happ
    exact ⟨hπj.symm, by simpa using hεj.symm⟩
  have hπb : D.π (D.π i) = i := by
    by_contra hne
    have hbne : D.π (D.π i) ≠ D.π i := fun h => hi (D.π.injective h)
    exact hbne (D.π.injective (hout (D.π (D.π i)) hne hbne).1)
  have hπeq : D.π = Equiv.swap i (D.π i) := by
    refine Equiv.ext fun j => ?_
    by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_left]
    · by_cases hjb : j = D.π i
      · subst hjb
        rw [Equiv.swap_apply_right, hπb]
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjb]
        exact (hout j hji hjb).1
  have hεb : D.ε (D.π i) = D.ε i := by
    let v : Fin k → Multiplicative (ZMod 3) :=
      Pi.mulSingle i (ofAdd 1) * Pi.mulSingle (D.π i) (ofAdd (D.ε i))
    have hvb : v (D.π i) = ofAdd (D.ε i) := by
      simp [v, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi]
    have hvi : v i = ofAdd 1 := by
      simp [v, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hi)]
    have hv : v ∈ (frameMB_delta i (D.π i) (D.ε i)).ker := by
      rw [MonoidHom.mem_ker, frameMB_delta_apply, hvb, hvi, toAdd_ofAdd, toAdd_ofAdd,
        mul_one, sub_self, ofAdd_zero]
    have hv' : v ∈ frameMB_fixedSubgroup u := hH.symm ▸ hv
    change u v = v at hv'
    have h := D.hu v (D.π i)
    rw [hπb, hv'] at h
    rw [hvi, hvb, toAdd_ofAdd, toAdd_ofAdd] at h
    calc D.ε (D.π i) = D.ε (D.π i) * 1 := (mul_one _).symm
      _ = D.ε (D.π i) * (D.ε i * D.ε i) := by rw [coord_sign_mul_self (D.hε i)]
      _ = (D.ε (D.π i) * D.ε i) * D.ε i := by ring
      _ = 1 * D.ε i := by rw [← h]
      _ = D.ε i := one_mul _
  exact ⟨hout, hπeq, hεb⟩

private lemma frameMB_signedData_apply_inv {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) (f : Fin k → Multiplicative (ZMod 3)) (j : Fin k) :
    toAdd (u f j) = D.ε (D.π⁻¹ j) * toAdd (f (D.π⁻¹ j)) := by
  have h1 : D.π (D.π⁻¹ j) = j := by
    simpa using (Equiv.apply_symm_apply D.π j)
  calc toAdd (u f j) = toAdd (u f (D.π (D.π⁻¹ j))) := by rw [h1]
    _ = D.ε (D.π⁻¹ j) * toAdd (f (D.π⁻¹ j)) := D.hu f (D.π⁻¹ j)

private lemma frameMB_forward_ne_one_eps_one {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) {i : Fin k} (hi : D.π i ≠ i)
    (hout : ∀ j, j ≠ i → j ≠ D.π i → D.π j = j ∧ D.ε j = 1)
    (hπeq : D.π = Equiv.swap i (D.π i))
    (hεb : D.ε (D.π i) = D.ε i) (hεi : D.ε i = 1) :
    u = permAut (Equiv.swap i (D.π i)) := by
  have hεall : ∀ l, D.ε l = 1 := by
    intro l
    by_cases hli : l = i
    · subst hli
      exact hεi
    · by_cases hlb : l = D.π i
      · subst hlb
        rw [hεb]
        exact hεi
      · exact (hout l hli hlb).2
  have hπinv : D.π⁻¹ = (Equiv.swap i (D.π i))⁻¹ := by
    conv_lhs => rw [hπeq]
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
  rw [frameMB_signedData_apply_inv D f j, hεall (D.π⁻¹ j), one_mul, hπinv,
    permAut_apply, Function.comp_apply, Equiv.swap_inv]

private lemma frameMB_forward_ne_one_eps_neg {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (D : frameMB_SignedData u) {i : Fin k} (hi : D.π i ≠ i)
    (hout : ∀ j, j ≠ i → j ≠ D.π i → D.π j = j ∧ D.ε j = 1)
    (hπeq : D.π = Equiv.swap i (D.π i))
    (hεb : D.ε (D.π i) = D.ε i) (hεi : D.ε i = -1) :
    u = negSwapAut i (D.π i) := by
  have hεb' : D.ε (D.π i) = -1 := by rw [hεb, hεi]
  have hπinv : D.π⁻¹ = (Equiv.swap i (D.π i))⁻¹ := by
    conv_lhs => rw [hπeq]
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
  rw [frameMB_signedData_apply_inv D f j, frameMB_negSwapAut_apply (Ne.symm hi)]
  by_cases hji : j = i
  · rw [hji]
    have hπj : D.π⁻¹ i = D.π i := by
      rw [hπinv, Equiv.swap_inv]
      exact Equiv.swap_apply_left i (D.π i)
    rw [hπj, hεb', if_pos rfl, toAdd_inv, neg_one_mul]
  · by_cases hjb : j = D.π i
    · rw [hjb]
      have hπj : D.π⁻¹ (D.π i) = i := by
        rw [hπinv, Equiv.swap_inv]
        exact Equiv.swap_apply_right i (D.π i)
      rw [hπj, hεi, if_neg hi, if_pos rfl, toAdd_inv, neg_one_mul]
    · have hπj : D.π⁻¹ j = j := by
        rw [hπinv, Equiv.swap_inv]
        exact Equiv.swap_apply_of_ne_of_ne hji hjb
      rw [hπj, (hout j hji hjb).2, one_mul, if_neg hji, if_neg hjb]

end

theorem mem_modelReflSet_signedPermSet_iff (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    u ∈ modelReflSet (signedPermSet k) ↔
      (∃ i, u = sgnAut i) ∨
        ∃ a b : Fin k, a ≠ b ∧ (u = permAut (Equiv.swap a b) ∨ u = negSwapAut a b) := by
  constructor
  · rintro ⟨hu, -, hcard⟩
    obtain ⟨π, ε, hε, hu⟩ := hu
    let D : frameMB_SignedData u := ⟨π, ε, hε, hu⟩
    have hcard' : Nat.card (frameMB_fixedSubgroup u) * 3 =
        Nat.card (Fin k → Multiplicative (ZMod 3)) := hcard
    by_cases hπ : D.π = 1
    · have hu1 : ∀ f i, toAdd (u f i) = D.ε i * toAdd (f i) := by
        intro f i
        simpa [hπ] using D.hu f i
      by_cases hall : ∀ i, D.ε i = 1
      · exfalso
        exact frameMB_forward_pi_one hall hu1 hcard'
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        rcases D.hε i with h | h
        · exact absurd h hi
        · exact Or.inl ⟨i, frameMB_forward_pi_one_eq D.hε hu1 hcard' h⟩
    · obtain ⟨i, hi⟩ : ∃ i, D.π i ≠ i := by
        by_contra h
        push Not at h
        exact hπ (Equiv.ext fun j => by simpa using h j)
      obtain ⟨hout, hπeq, hεb⟩ := frameMB_forward_ne_one_shape D hi hcard'
      rcases D.hε i with hsign | hsign
      · exact Or.inr ⟨i, D.π i, Ne.symm hi,
          Or.inl (frameMB_forward_ne_one_eps_one D hi hout hπeq hεb hsign)⟩
      · exact Or.inr ⟨i, D.π i, Ne.symm hi,
          Or.inr (frameMB_forward_ne_one_eps_neg D hi hout hπeq hεb hsign)⟩
  · rintro (⟨i, rfl⟩ | ⟨a, b, hab, rfl | rfl⟩)
    · exact ⟨isSignedPerm_sgnAut i, sgnAut_sq i,
        card_fix_sgnAut (p := 3) Nat.prime_three (by decide) i⟩
    · exact ⟨isSignedPerm_permAut (Equiv.swap a b), permAut_swap_sq a b,
        card_fix_permAut_swap (p := 3) Nat.prime_three (by decide) hab⟩
    · exact ⟨frameMB_isSignedPerm_negSwapAut hab, frameMB_negSwapAut_sq hab,
        frameMB_card_fix_negSwapAut hab⟩

end CFSG.StandardType.FrameRoute

end

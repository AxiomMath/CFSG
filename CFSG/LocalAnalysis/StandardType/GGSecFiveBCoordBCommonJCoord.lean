module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJ

open Multiplicative

variable {p k : ℕ}

private theorem pow_injective_of_not_dvd {p : ℕ} (hp : p.Prime) {c : ℕ} (hc : ¬ p ∣ c) :
    ∀ x y : Multiplicative (ZMod p), x ^ c = y ^ c → x = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hc0 : (c : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hc
  intro x y h
  have h' := congrArg toAdd h
  simp only [toAdd_pow, nsmul_eq_mul] at h'
  exact toAdd.injective (mul_left_cancel₀ hc0 h')

private theorem eq_zero_of_sign_mul_eq_zero {p : ℕ} {ε a : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (h : ε * a = 0) : a = 0 := by
  rcases hε with rfl | rfl
  · simpa using h
  · simpa using h

private theorem eq_or_neg_of_sign_mul {p : ℕ} {ε δ a b : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (h : ε * a = δ * b ∨ ε * a = -(δ * b)) : a = b ∨ a = -b := by
  rcases h with h | h
  · have h' : a = (ε * δ) * b := by
      calc a = (ε * ε) * a := by rw [SpCoord.coord_sign_mul_self hε, one_mul]
        _ = ε * (ε * a) := by rw [mul_assoc]
        _ = ε * (δ * b) := by rw [h]
        _ = (ε * δ) * b := by rw [mul_assoc]
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp_all
  · have h' : a = -((ε * δ) * b) := by
      calc a = (ε * ε) * a := by rw [SpCoord.coord_sign_mul_self hε, one_mul]
        _ = ε * (ε * a) := by rw [mul_assoc]
        _ = ε * (-(δ * b)) := by rw [h]
        _ = -((ε * δ) * b) := by ring
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp_all

private theorem sign_mul_eq_or_neg_of_eq_or_neg {p : ℕ} {ε δ a b : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (h : a = b ∨ a = -b) : ε * a = δ * b ∨ ε * a = -(δ * b) := by
  rcases h with h | h
  · rw [h]
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp [mul_neg]
  · rw [h]
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp [mul_neg]

private theorem isSignedPerm_apply_one_iff {p k : ℕ}
    {u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (f : Fin k → Multiplicative (ZMod p)) (i : Fin k) :
    u f (π i) = 1 ↔ f i = 1 := by
  constructor
  · intro h
    have h0 : ε i * toAdd (f i) = 0 := by
      rw [← hu f i, h, toAdd_one]
    have hz : toAdd (f i) = 0 := eq_zero_of_sign_mul_eq_zero (hε i) h0
    exact toAdd.injective (by simpa using hz)
  · intro h
    apply toAdd.injective
    rw [hu f i, h, toAdd_one, mul_zero]

private theorem isSignedPerm_coord_iff {p k : ℕ}
    {u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (f : Fin k → Multiplicative (ZMod p)) (i j : Fin k) :
    u f (π j) = u f (π i) ∨ u f (π j) = (u f (π i))⁻¹ ↔
      f j = f i ∨ f j = (f i)⁻¹ := by
  constructor
  · rintro (h | h)
    · have h1 : ε j * toAdd (f j) = ε i * toAdd (f i) := by
        rw [← hu f j, ← hu f i, h]
      rcases eq_or_neg_of_sign_mul (hε j) (hε i) (Or.inl h1) with h2 | h2
      · exact Or.inl (toAdd.injective h2)
      · exact Or.inr (toAdd.injective (by simpa [toAdd_inv] using h2))
    · have h1 : ε j * toAdd (f j) = -(ε i * toAdd (f i)) := by
        rw [← hu f j, ← hu f i, h, toAdd_inv]
      rcases eq_or_neg_of_sign_mul (hε j) (hε i) (Or.inr h1) with h2 | h2
      · exact Or.inl (toAdd.injective h2)
      · exact Or.inr (toAdd.injective (by simpa [toAdd_inv] using h2))
  · rintro (h | h)
    · have h1 : toAdd (f j) = toAdd (f i) := by rw [h]
      rcases sign_mul_eq_or_neg_of_eq_or_neg (hε j) (hε i) (Or.inl h1) with h2 | h2
      · left
        apply toAdd.injective
        rw [hu f j, hu f i]
        exact h2
      · right
        apply toAdd.injective
        rw [hu f j, toAdd_inv, hu f i]
        exact h2
    · have h1 : toAdd (f j) = -toAdd (f i) := by
        rw [h, toAdd_inv]
      rcases sign_mul_eq_or_neg_of_eq_or_neg (hε j) (hε i) (Or.inr h1) with h2 | h2
      · left
        apply toAdd.injective
        rw [hu f j, hu f i]
        exact h2
      · right
        apply toAdd.injective
        rw [hu f j, toAdd_inv, hu f i]
        exact h2

theorem ggCoordDense_pow (hp : p.Prime) {f : Fin k → Multiplicative (ZMod p)} {c : ℕ}
    (hc : ¬ p ∣ c) : GGCoordDense (f ^ c) ↔ GGCoordDense f := by
  have hpow := pow_injective_of_not_dvd hp hc
  constructor
  · intro h i
    refine ⟨?_, fun j => ?_⟩
    · intro hfi
      exact (h i).1 (by rw [Pi.pow_apply, hfi, one_pow])
    · rcases (h i).2 j with hji | hji
      · left
        rw [Pi.pow_apply, Pi.pow_apply] at hji
        exact hpow _ _ hji
      · right
        rw [Pi.pow_apply, Pi.pow_apply] at hji
        exact hpow _ _ (by rw [hji, ← inv_pow])
  · intro h i
    refine ⟨?_, fun j => ?_⟩
    · intro hi
      have hfi : f i ^ c = 1 := by simpa [Pi.pow_apply] using hi
      exact (h i).1 (hpow _ _ (by rw [hfi, one_pow]))
    · rcases (h i).2 j with hji | hji <;> rw [Pi.pow_apply, Pi.pow_apply, hji]
      · left
        rfl
      · right
        rw [inv_pow]

theorem ggCoordSparse_pow (hp : p.Prime) {f : Fin k → Multiplicative (ZMod p)} {c : ℕ}
    (hc : ¬ p ∣ c) : GGCoordSparse (f ^ c) ↔ GGCoordSparse f := by
  have hpow := pow_injective_of_not_dvd hp hc
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj => ?_⟩
    have h1 : f j ^ c = (1 : Multiplicative (ZMod p)) ^ c := by
      rw [← Pi.pow_apply, hi j hj, one_pow]
    exact hpow _ _ h1
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj => ?_⟩
    rw [Pi.pow_apply, hi j hj, one_pow]

theorem ggCoordDense_iff_of_isSignedPerm
    {u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))}
    (hu : SpCoord.IsSignedPerm u) (f : Fin k → Multiplicative (ZMod p)) :
    GGCoordDense (u f) ↔ GGCoordDense f := by
  obtain ⟨π, ε, hε, hu'⟩ := hu
  constructor
  · intro h i
    refine ⟨?_, fun j => (isSignedPerm_coord_iff hε hu' f i j).1 ((h (π i)).2 (π j))⟩
    intro hfi
    exact (h (π i)).1 ((isSignedPerm_apply_one_iff hε hu' f i).2 hfi)
  · intro h i
    refine ⟨?_, fun j => ?_⟩
    · intro hi
      have h1 : f (π.symm i) = 1 :=
        (isSignedPerm_apply_one_iff hε hu' f (π.symm i)).1 (by simpa using hi)
      exact (h (π.symm i)).1 h1
    · have h1 := (isSignedPerm_coord_iff hε hu' f (π.symm i) (π.symm j)).2
        ((h (π.symm i)).2 (π.symm j))
      simpa using h1

theorem ggCoordSparse_iff_of_isSignedPerm
    {u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))}
    (hu : SpCoord.IsSignedPerm u) (f : Fin k → Multiplicative (ZMod p)) :
    GGCoordSparse (u f) ↔ GGCoordSparse f := by
  obtain ⟨π, ε, hε, hu'⟩ := hu
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨π.symm i, fun j hj => ?_⟩
    have hπj : π j ≠ i := by
      intro h
      apply hj
      calc j = π.symm (π j) := (Equiv.symm_apply_apply π j).symm
        _ = π.symm i := by rw [h]
    exact (isSignedPerm_apply_one_iff hε hu' f j).1 (hi (π j) hπj)
  · rintro ⟨i, hi⟩
    refine ⟨π i, fun j hj => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, π m = j := ⟨π.symm j, Equiv.apply_symm_apply π j⟩
    have hm : m ≠ i := by
      intro h
      exact hj (by rw [h])
    exact (isSignedPerm_apply_one_iff hε hu' f m).2 (hi m hm)

theorem ggCoord_iff_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k)
    {φ : MulAut (Fin k → Multiplicative (ZMod p))}
    (hφ : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), SpCoord.IsSignedPerm ⇑u →
      SpCoord.IsSignedPerm ⇑(φ * u * φ⁻¹))
    (f : Fin k → Multiplicative (ZMod p)) :
    (GGCoordDense (φ f) ↔ GGCoordDense f) ∧ (GGCoordSparse (φ f) ↔ GGCoordSparse f) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hφ' : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)),
      SpCoord.IsSignedPerm ⇑u → SpCoord.IsSignedPerm ⇑(φ⁻¹ * u * φ) := by
    intro v hv
    let S := SignedPermCount.signedPermSubgroup p k
    haveI : Finite (MulAut (Fin k → Multiplicative (ZMod p))) :=
      Finite.of_injective (fun f : MulAut _ => (f : _ → _)) DFunLike.coe_injective
    haveI : Finite S :=
      Finite.of_injective (fun s : S => (s : MulAut (Fin k → Multiplicative (ZMod p))))
        Subtype.val_injective
    let T : S → S := fun u => ⟨φ * (u : MulAut (Fin k → Multiplicative (ZMod p))) * φ⁻¹,
      hφ (u : MulAut (Fin k → Multiplicative (ZMod p))) u.2⟩
    have hTinj : Function.Injective T := by
      rintro ⟨u, hu⟩ ⟨w, hw⟩ h
      have h' : φ * u * φ⁻¹ = φ * w * φ⁻¹ := congrArg Subtype.val h
      have h'' := congrArg (fun x => φ⁻¹ * x * φ) h'
      simpa [mul_assoc] using h''
    have hTsurj : Function.Surjective T := Finite.surjective_of_injective hTinj
    obtain ⟨⟨u, hu⟩, hu_eq⟩ := hTsurj ⟨v, hv⟩
    have h1 : φ * u * φ⁻¹ = v := congrArg Subtype.val hu_eq
    have h2 : φ⁻¹ * v * φ = u := by
      rw [← h1]
      group
    rw [h2]
    exact hu
  obtain ⟨w, hw, c, hcφ⟩ := SpCoord.exists_isSignedPerm_pow hp hp2 hk hφ hφ'
  have hcp : ¬ p ∣ c := by
    intro hpc
    obtain ⟨d, rfl⟩ := hpc
    have hfix : ∀ f : Fin k → Multiplicative (ZMod p), φ f = 1 := by
      intro f
      have hwp : (w f) ^ p = 1 := by
        funext i
        apply toAdd.injective
        rw [Pi.pow_apply, Pi.one_apply, toAdd_pow, toAdd_one, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul]
      rw [hcφ f, pow_mul, hwp, one_pow]
    let i0 : Fin k := ⟨0, by omega⟩
    have hδ1 : φ (Pi.mulSingle i0 (ofAdd 1)) = 1 := hfix _
    have hδ : (Pi.mulSingle i0 (ofAdd 1) : Fin k → Multiplicative (ZMod p)) = 1 :=
      φ.injective (by simpa using hδ1)
    have hδne : (Pi.mulSingle i0 (ofAdd 1) : Fin k → Multiplicative (ZMod p)) ≠ 1 := by
      intro h
      have h10 : (1 : ZMod p) = 0 := by
        have := congrArg (fun f => toAdd (f i0)) h
        simpa using this
      exact SpCoord.coord_zero_ne_one hp h10.symm
    exact hδne hδ
  constructor
  · calc GGCoordDense (φ f) ↔ GGCoordDense ((w f) ^ c) := by rw [hcφ f]
      _ ↔ GGCoordDense (w f) := ggCoordDense_pow hp hcp
      _ ↔ GGCoordDense f := ggCoordDense_iff_of_isSignedPerm hw f
  · calc GGCoordSparse (φ f) ↔ GGCoordSparse ((w f) ^ c) := by rw [hcφ f]
      _ ↔ GGCoordSparse (w f) := ggCoordSparse_pow hp hcp
      _ ↔ GGCoordSparse f := ggCoordSparse_iff_of_isSignedPerm hw f

theorem ggSecFiveBCoordDense_iff {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1)) (D : Subgroup G) :
    GGSecFiveBCoordDense eta i0 D ↔
      ∀ z : ↥Bs, (z : G) ∈ D → z ≠ 1 → eta z i0 = 1 →
        GGCoordDense fun j => eta z (i0.succAbove j) := by
  constructor
  · intro h z hzD hz1 hzi i
    have H := h z hzD hz1 hzi (i0.succAbove i) (Fin.succAbove_ne i0 i)
    exact ⟨H.1, fun j => H.2 (i0.succAbove j) (Fin.succAbove_ne i0 j)⟩
  · intro h z hzD hz1 hzi i hi
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
    refine ⟨(h z hzD hz1 hzi i').1, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact (h z hzD hz1 hzi i').2 j'

theorem ggSecFiveBCoordSparse_iff {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1)) (D : Subgroup G) :
    GGSecFiveBCoordSparse eta i0 D ↔
      ∀ z : ↥Bs, (z : G) ∈ D → z ≠ 1 → eta z i0 = 1 →
        GGCoordSparse fun j => eta z (i0.succAbove j) := by
  constructor
  · intro h z hzD hz1 hzi
    obtain ⟨i, hi0, hi⟩ := h z hzD hz1 hzi
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi0
    refine ⟨i', fun j hj => ?_⟩
    have hji : i0.succAbove j ≠ i0.succAbove i' := fun hh =>
      hj (Fin.succAbove_right_injective hh)
    exact hi (i0.succAbove j) (Fin.succAbove_ne i0 j) hji
  · intro h z hzD hz1 hzi
    obtain ⟨i', hi'⟩ := h z hzD hz1 hzi
    refine ⟨i0.succAbove i', Fin.succAbove_ne i0 i', ?_⟩
    intro j hj0 hj
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj0
    have hj' : j' ≠ i' := by
      intro h
      exact hj (by rw [h])
    exact hi' j' hj'

theorem bCoordinateBlock_apply_self {n : ℕ} {i0 : Fin n}
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ bCoordinateBlock n p i0) (F : Fin n → Multiplicative (ZMod p)) : u F i0 = F i0 := by
  have hP : ∀ F : Fin n → Multiplicative (ZMod p), u F i0 = F i0 := by
    induction hu using Subgroup.closure_induction with
    | mem r hr =>
      intro F
      rcases hr with ⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩
      · rw [SpCoord.sgnAut_apply, Function.update_of_ne (Ne.symm hi)]
      · rw [SpCoord.permAut_apply]
        change F (Equiv.swap a b i0) = F i0
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
    | one => intro F; rfl
    | mul u v hu hv ihu ihv =>
      intro F
      rw [MulAut.mul_apply, ihu (v F), ihv F]
    | inv u hu ihu =>
      intro F
      have h := ihu (u⁻¹ F)
      rw [MulAut.apply_inv_self] at h
      exact h.symm
  exact hP F

theorem exists_bCoordinateBlock_restrict {m : ℕ} (i0 : Fin (m + 1))
    {w : MulAut (Fin m → Multiplicative (ZMod p))} (hw : SpCoord.IsSignedPerm ⇑w) :
    ∃ u ∈ bCoordinateBlock (m + 1) p i0, ∀ F : Fin (m + 1) → Multiplicative (ZMod p),
      (fun j => u F (i0.succAbove j)) = w fun j => F (i0.succAbove j) := by
  let H : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
    { carrier := {w | ∃ u ∈ bCoordinateBlock (m + 1) p i0,
        ∀ F : Fin (m + 1) → Multiplicative (ZMod p),
          (fun j => u F (i0.succAbove j)) = w fun j => F (i0.succAbove j)}
      one_mem' := ⟨1, (bCoordinateBlock (m + 1) p i0).one_mem, fun F => rfl⟩
      mul_mem' := by
        rintro w₁ w₂ ⟨u₁, hu₁, hr₁⟩ ⟨u₂, hu₂, hr₂⟩
        refine ⟨u₁ * u₂, (bCoordinateBlock (m + 1) p i0).mul_mem hu₁ hu₂, fun F => ?_⟩
        funext j
        calc (u₁ * u₂) F (i0.succAbove j) = u₁ (u₂ F) (i0.succAbove j) := rfl
          _ = w₁ (fun k => u₂ F (i0.succAbove k)) j := congrFun (hr₁ (u₂ F)) j
          _ = w₁ (w₂ (fun k => F (i0.succAbove k))) j := by rw [hr₂ F]
          _ = (w₁ * w₂) (fun k => F (i0.succAbove k)) j := rfl
      inv_mem' := by
        rintro w ⟨u, hu, hru⟩
        refine ⟨u⁻¹, (bCoordinateBlock (m + 1) p i0).inv_mem hu, fun F => ?_⟩
        funext j
        have h := hru (u⁻¹ F)
        rw [MulAut.apply_inv_self] at h
        calc u⁻¹ F (i0.succAbove j) =
              w⁻¹ (w (fun k => u⁻¹ F (i0.succAbove k))) j := by
                rw [MulAut.inv_apply_self]
          _ = w⁻¹ (fun k => F (i0.succAbove k)) j := by rw [← h] }
  have hs : ∀ i : Fin m, SpCoord.sgnAut i ∈ H := by
    intro i
    refine ⟨SpCoord.sgnAut (i0.succAbove i),
      Subgroup.subset_closure (Or.inl ⟨i0.succAbove i, Fin.succAbove_ne i0 i, rfl⟩),
      fun F => ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp [SpCoord.sgnAut_apply]
    · rw [SpCoord.sgnAut_apply, SpCoord.sgnAut_apply,
        Function.update_of_ne (fun h => hj (Fin.succAbove_right_injective h)),
        Function.update_of_ne hj]
  have ht : ∀ a b : Fin m, a ≠ b → SpCoord.permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    have hσ : ∀ j, Equiv.swap (i0.succAbove a) (i0.succAbove b) (i0.succAbove j) =
        i0.succAbove (Equiv.swap a b j) := by
      intro j
      by_cases hja : j = a
      · rw [hja, Equiv.swap_apply_left, Equiv.swap_apply_left]
      · by_cases hjb : j = b
        · rw [hjb, Equiv.swap_apply_right, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne
              (fun h => hja (Fin.succAbove_right_injective h))
              (fun h => hjb (Fin.succAbove_right_injective h)),
            Equiv.swap_apply_of_ne_of_ne hja hjb]
    refine ⟨SpCoord.permAut (Equiv.swap (i0.succAbove a) (i0.succAbove b)),
      Subgroup.subset_closure (Or.inr ⟨i0.succAbove a, i0.succAbove b,
        fun h => hab (Fin.succAbove_right_injective h), Fin.succAbove_ne i0 a,
        Fin.succAbove_ne i0 b, rfl⟩), fun F => ?_⟩
    funext j
    rw [SpCoord.permAut_apply, SpCoord.permAut_apply, Function.comp_apply,
      Function.comp_apply, Equiv.swap_inv, Equiv.swap_inv, hσ j]
  exact SpCoord.mem_of_isSignedPerm (H := H) hs ht hw

theorem eq_one_of_bCoordinateBlock_fix (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {i0 : Fin n}
    {F : Fin n → Multiplicative (ZMod p)} (hF : ∀ u ∈ bCoordinateBlock n p i0, u F = F)
    {i : Fin n} (hi : i ≠ i0) : F i = 1 := by
  have h := congrFun (hF (SpCoord.sgnAut i)
    (Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩))) i
  rw [SpCoord.sgnAut_apply, Function.update_self] at h
  have h' := congrArg toAdd h
  rw [toAdd_inv] at h'
  have hz := SpCoord.coord_eq_zero_of_eq_neg hp hp2 h'.symm
  exact toAdd.injective (by simpa using hz)

theorem card_scalar_param {p r : ℕ} (P Q : Fin r → Prop) [DecidablePred P]
    [DecidablePred Q] (hdisj : ∀ i, P i → Q i → False) (hne : ∃ i, P i ∨ Q i) :
    Nat.card {g : Fin r → Multiplicative (ZMod p) //
      ∃ c, ∀ i, (P i → g i = c) ∧ (Q i → g i = c⁻¹)} =
      p * p ^ (r - Nat.card {i : Fin r // P i ∨ Q i}) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  let e : {g : Fin r → Multiplicative (ZMod p) //
      ∃ c, ∀ i, (P i → g i = c) ∧ (Q i → g i = c⁻¹)} ≃
      Multiplicative (ZMod p) × ({i : Fin r // ¬ (P i ∨ Q i)} → Multiplicative (ZMod p)) :=
    { toFun := fun g =>
        (if h : P i₀ then g.1 i₀ else (g.1 i₀)⁻¹, fun i => g.1 i.1)
      invFun := fun x =>
        ⟨fun i => if hi : P i then x.1
          else if hi' : Q i then x.1⁻¹ else x.2 ⟨i, by simp [hi, hi']⟩,
         ⟨x.1, fun i => ⟨fun hi => by simp [hi], fun hi => by
           have hiP : ¬ P i := fun h => hdisj i h hi
           simp [hiP, hi]⟩⟩⟩
      left_inv := by
        intro g
        obtain ⟨c, hc⟩ := g.2
        have hc₀ : (if h : P i₀ then g.1 i₀ else (g.1 i₀)⁻¹) = c := by
          rcases hi₀ with h | h
          · rw [dif_pos h, (hc i₀).1 h]
          · have hP : ¬ P i₀ := fun hp => hdisj i₀ hp h
            rw [dif_neg hP, (hc i₀).2 h, inv_inv]
        apply Subtype.ext
        funext i
        by_cases hi : P i
        · simp [hi, (hc i).1 hi, hc₀]
        · by_cases hi' : Q i
          · have hiP : ¬ P i := fun h => hdisj i h hi'
            simp [hi, hi', hiP, (hc i).2 hi', hc₀]
          · simp [hi, hi']
      right_inv := by
        intro x
        apply Prod.ext
        · rcases hi₀ with h | h
          · simp [h]
          · have hP : ¬ P i₀ := fun hp => hdisj i₀ hp h
            simp [hP, h]
        · funext i
          have hiP : ¬ P i := fun h => i.2 (Or.inl h)
          have hiQ : ¬ Q i := fun h => i.2 (Or.inr h)
          simp only [dif_neg hiP, dif_neg hiQ] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun]
  have hp : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  rw [hp]
  congr 1
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_fin]

end CommonJ

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.B15P4Layer2A2

public section

namespace CFSG.Quasithin.H13.L8211

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem mem_stabSub_commV {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) : g ∈ stabSub (commV X) :=
  CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer hg

theorem mem_stabSub_of {U : Subgroup V} {g : MulAut V} (h1 : ∀ u ∈ U, g u ∈ U)
    (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U :=
  CFSG.Quasithin.mem_stabSub_of_invariant h1 h2

theorem apply_mem_of_stabSub {U : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub U) {u : V}
    (hu : u ∈ U) : g u ∈ U := (hg u).2 hu

theorem inv_apply_mem_of_stabSub {U : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub U) {u : V}
    (hu : u ∈ U) : g⁻¹ u ∈ U :=
  apply_mem_of_stabSub (Subgroup.inv_mem _ hg) hu

theorem sup_mem_stabSub {A B : Subgroup V} {g : MulAut V} (hA : g ∈ stabSub A)
    (hB : g ∈ stabSub B) : g ∈ stabSub (A ⊔ B) := by
  have key : ∀ k : MulAut V, k ∈ stabSub A → k ∈ stabSub B → ∀ u ∈ A ⊔ B, k u ∈ A ⊔ B := by
    intro k hkA hkB u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (apply_mem_of_stabSub hkA ha) (apply_mem_of_stabSub hkB hb)
  exact mem_stabSub_of (key g hA hB)
    (key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB))

theorem commSub_mem_stabSub {W : Subgroup V} {Q : Subgroup (MulAut V)} {g : MulAut V}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set (MulAut V))) (hgW : g ∈ stabSub W) :
    g ∈ stabSub (commSub W Q) :=
  CFSG.Quasithin.StabLat.mem_stabSub_commSub hgW hgQ

theorem commSub_le_self {W : Subgroup V} {Q : Subgroup (MulAut V)} (hQW : Q ≤ stabSub W) :
    commSub W Q ≤ W :=
  commSub_le_of_invariant fun _ hx _ hw => apply_mem_of_stabSub (hQW hx) hw

theorem commSub_sup_le (A B : Subgroup V) (Q : Subgroup (MulAut V)) :
    commSub (A ⊔ B) Q ≤ commSub A Q ⊔ commSub B Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, u, hu, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  have e : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
    (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)

theorem commSub_ne_self [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    (hQ : IsPGroup 2 ↥Q) {U : Subgroup V} (hQU : Q ≤ stabSub U) (hU : U ≠ ⊥) :
    commSub U Q ≠ U := by
  intro heq
  have hVU : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u.1)
  have hnt : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).2 hU
  have hN : commV (⊥ : Subgroup (MulAut ↥U)) ≠ ⊤ := by
    have h0 : commV (⊥ : Subgroup (MulAut ↥U)) = ⊥ := by
      rw [commV, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨x, hx, v, rfl⟩
      rw [Subgroup.mem_bot] at hx
      simp [hx]
    rw [h0]
    exact bot_ne_top
  have key := G6.commV_ne_top_of_two_power (V := ↥U) hVU (K := autSub Q U) (N := ⊥)
    (fun k _ n hn => by
      rw [Subgroup.mem_bot] at hn ⊢
      simp [hn])
    (fun k hk => by
      obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
      obtain ⟨m, hm⟩ := hQ ⟨g, hg⟩
      refine ⟨m, ?_⟩
      have hg1 : g ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
      rw [Subgroup.mem_bot, ← map_pow, hg1, map_one])
    hN
  apply key
  apply Subgroup.map_injective U.subtype_injective
  rw [B15P4.map_subtype_commV_autSub hQU, heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_commIter_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    (hQ : IsPGroup 2 ↥Q) {U : Subgroup V} (hQU : Q ≤ stabSub U) :
    ∃ m, commIter U Q m = ⊥ := by
  have hstab : ∀ k, Q ≤ stabSub (commIter U Q k) := by
    intro k
    induction k with
    | zero => exact hQU
    | succ k ih => exact fun g hg => commSub_mem_stabSub (Subgroup.le_normalizer hg) (ih hg)
  have hstep : ∀ k, commIter U Q k = ⊥ ∨
      Nat.card ↥(commIter U Q (k + 1)) < Nat.card ↥(commIter U Q k) := by
    intro k
    by_cases hk : commIter U Q k = ⊥
    · exact Or.inl hk
    · right
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne (commSub_le_self (hstab k)) ?_)
      exact commSub_ne_self hV hQ (hstab k) hk
  have hbound : ∀ k, commIter U Q k = ⊥ ∨ Nat.card ↥(commIter U Q k) + k ≤ Nat.card U := by
    intro k
    induction k with
    | zero => exact Or.inr (by simp [commIter])
    | succ k ih =>
      rcases ih with h | h
      · left
        show commSub (commIter U Q k) Q = ⊥
        rw [h, commSub_eq_bot_iff]
        exact bot_le
      · rcases hstep k with h' | h'
        · left
          show commSub (commIter U Q k) Q = ⊥
          rw [h', commSub_eq_bot_iff]
          exact bot_le
        · right
          omega
  refine ⟨Nat.card U, ?_⟩
  rcases hbound (Nat.card U) with h | h
  · exact h
  · have := (commIter U Q (Nat.card U)).one_lt_card_iff_ne_bot
    by_contra hne
    have h1 := this.mpr hne
    omega

theorem eq_one_or_eq_of_mem_zpowers {z x : V} (hz : z ^ 2 = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hz' : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hz', one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hz', one_zpow, one_mul, zpow_one]

theorem commSub_le_of_irr [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {P Q : Subgroup (MulAut V)}
    {W Z : Subgroup V} (hZW : Z ≤ W) (hZ : Nat.card Z = 2) (hW : 4 ≤ Nat.card W)
    (hQ : IsPGroup 2 ↥Q) (hQW : Q ≤ stabSub W) (hQZ : Q ≤ centSub Z)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut V))) (hPW : P ≤ stabSub W)
    (hPZ : P ≤ stabSub Z)
    (hirr : ∀ Y : Subgroup V, Z < Y → Y ≤ W → P ≤ stabSub Y → Y = W) :
    commSub W Q ≤ Z := by
  by_contra hXZ
  set X := commSub W Q with hXdef
  have hXW : X ≤ W := commSub_le_self hQW
  have hPX : P ≤ stabSub X := fun p hp => commSub_mem_stabSub (hPQ hp) (hPW hp)
  have hQX : Q ≤ stabSub X := fun q hq => commSub_mem_stabSub (Subgroup.le_normalizer hq) (hQW hq)
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW
    omega
  have hXne : X ≠ W := commSub_ne_self hV hQ hQW hWne
  have hXZW : X ⊔ Z = W := by
    refine hirr _ (lt_of_le_of_ne le_sup_right fun h => hXZ (h ▸ le_sup_left)) (sup_le hXW hZW)
      fun p hp => sup_mem_stabSub (hPX hp) (hPZ hp)
  have hcard := card_sup_mul_card_inf X Z
  rw [hXZW, hZ] at hcard
  have hXlt : Nat.card X < Nat.card W := Subgroup.card_lt_of_lt (lt_of_le_of_ne hXW hXne)
  have hXZ1 : Nat.card ↥(X ⊓ Z) = 1 := by
    have hd : Nat.card ↥(X ⊓ Z) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le inf_le_right
    have hpos : 0 < Nat.card ↥(X ⊓ Z) := Nat.card_pos
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hcard
      omega
  rw [hXZ1, mul_one] at hcard
  have hXbot : X ⊓ Z = ⊥ := Subgroup.eq_bot_of_card_eq _ hXZ1
  have hX2 : commSub X Q ≤ Z := by
    by_contra hX2Z
    have hX2X : commSub X Q ≤ X := commSub_le_self hQX
    have hX2ne : commSub X Q ≠ X := by
      refine commSub_ne_self hV hQ hQX fun h => ?_
      rw [h, Subgroup.card_bot] at hcard
      omega
    have h1 : commSub X Q ⊔ Z = W := by
      refine hirr _ (lt_of_le_of_ne le_sup_right fun h => hX2Z (h ▸ le_sup_left))
        (sup_le (hX2X.trans hXW) hZW) fun p hp =>
          sup_mem_stabSub (commSub_mem_stabSub (hPQ hp) (hPX hp)) (hPZ hp)
    have h2 := card_sup_mul_card_inf (commSub X Q) Z
    rw [h1, hZ] at h2
    have h3 : Nat.card ↥(commSub X Q) < Nat.card X :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hX2X hX2ne)
    have h4 : 1 ≤ Nat.card ↥(commSub X Q ⊓ Z) := Nat.card_pos
    have h5 : Nat.card W ≤ Nat.card ↥(commSub X Q) * 2 := by
      calc Nat.card W ≤ Nat.card W * Nat.card ↥(commSub X Q ⊓ Z) := Nat.le_mul_of_pos_right _ h4
        _ = _ := h2
    omega
  have hX2bot : commSub X Q = ⊥ := by
    rw [eq_bot_iff, ← hXbot]
    exact le_inf (commSub_le_self hQX) hX2
  have hWfix : W ≤ fixV Q := by
    rw [← hXZW]
    refine sup_le (commSub_eq_bot_iff.mp hX2bot) fun u hu q hq => (hQZ hq) u hu
  have hX1 : X = ⊥ := commSub_eq_bot_iff.mpr hWfix
  rw [hX1, bot_sup_eq] at hXZW
  rw [← hXZW, hZ] at hW
  omega

theorem commV_le_of_irr [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {P Q : Subgroup (MulAut V)}
    {W : Subgroup V} (hWtop : W ≠ ⊤) (hQ : IsPGroup 2 ↥Q) (hQW : Q ≤ stabSub W)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut V))) (hPW : P ≤ stabSub W)
    (hirr : ∀ Y : Subgroup V, W < Y → P ≤ stabSub Y → Y = ⊤) : commV Q ≤ W := by
  by_contra hQW'
  have hstab : ∀ k, P ≤ stabSub (commIter ⊤ Q k) := by
    intro k
    induction k with
    | zero => exact fun p _ u => Iff.intro (fun _ => trivial) (fun _ => trivial)
    | succ k ih => exact fun p hp => commSub_mem_stabSub (hPQ hp) (ih hp)
  have hall : ∀ k, commIter ⊤ Q k ⊔ W = ⊤ := by
    intro k
    induction k with
    | zero => exact top_sup_eq W
    | succ k ih =>
      have h0 : commV Q = commSub (commIter ⊤ Q k ⊔ W) Q := by rw [ih, ← commV_eq_commSub]
      have h1 : commV Q ≤ commIter ⊤ Q (k + 1) ⊔ W := by
        rw [h0]
        exact (commSub_sup_le _ _ Q).trans (sup_le_sup_left (commSub_le_self hQW) _)
      refine hirr _ (lt_of_le_of_ne le_sup_right fun h => hQW' (h ▸ h1))
        fun p hp => sup_mem_stabSub (hstab (k + 1) hp) (hPW hp)
  obtain ⟨m, hm⟩ := exists_commIter_eq_bot hV hQ (U := ⊤) fun q _ u =>
    Iff.intro (fun _ => trivial) (fun _ => trivial)
  have := hall m
  rw [hm, bot_sup_eq] at this
  exact hWtop this

end CFSG.Quasithin.H13.L8211

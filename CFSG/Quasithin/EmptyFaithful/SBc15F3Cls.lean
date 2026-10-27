module

public import CFSG.Quasithin.EmptyFaithful.SBc15F3Model
public import CFSG.Quasithin.EmptyFaithful.SBc15F3Prod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc15

namespace L3

theorem odd_dvd_two_pow {n k : ℕ} (hn : Odd n) (h : n ∣ 2 ^ k) : n = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)).symm h

theorem isSylowTwoOf_R0 : IsSylowTwoOf R0 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [cards_std.1]; norm_num), ?_⟩
  have hidx : R0.index * Nat.card R0 = Nat.card SL32 := Subgroup.index_mul_card R0
  rw [cards_std.1, card_SL32] at hidx
  have h21 : R0.index = 21 := by omega
  have e : (R0.subgroupOf ⊤).index = R0.index := Subgroup.relIndex_top_right (H := R0)
  rw [e, h21]
  omega

theorem no_ord7 {Y : Subgroup SL32} (h7 : ¬ 7 ∣ Nat.card Y) {z : SL32} (hz : z ∈ Y) :
    ¬ Ord7 z := by
  rintro ⟨hz7, hz1⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho : orderOf z = 7 := orderOf_eq_prime hz7 hz1
  apply h7
  have := orderOf_dvd_natCard (⟨z, hz⟩ : Y)
  rwa [Subgroup.orderOf_mk, ho] at this

theorem odd_cases {Y : Subgroup SL32} (h7 : ¬ 7 ∣ Nat.card Y) {x : SL32} (hx : x ∈ Y)
    (hodd : Odd (orderOf x)) : x = 1 ∨ (x ^ 3 = 1 ∧ x ≠ 1) := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  refine Or.inr ?_
  rcases exp_cases x with h | h | h | h
  · exact absurd (orderOf_eq_one_iff.mp (odd_dvd_two_pow (k := 1) hodd
      (by simpa using orderOf_dvd_of_pow_eq_one h))) hx1
  · exact ⟨h, hx1⟩
  · exact absurd (orderOf_eq_one_iff.mp (odd_dvd_two_pow (k := 2) hodd
      (by simpa using orderOf_dvd_of_pow_eq_one h))) hx1
  · exact absurd ⟨h, hx1⟩ (no_ord7 h7 hx)

theorem eq_of_mem_aux (A B : Subgroup SL32)
    (hE1 : ∀ x : SL32, x ^ 3 = 1 → x ≠ 1 → x ∈ A ∨ x ∈ B ∨ ∃ r₂ ∈ R0, ∃ r₃ ∈ R0,
      Ord7 (x * (r₂ * x * r₂⁻¹) * (r₃ * x * r₃⁻¹)))
    (hE2A : ∀ a ∈ A, a ^ 3 = 1 → a ≠ 1 → ∀ x ∈ A, ∃ r₁ ∈ R0, ∃ r₂ ∈ R0,
      x = (r₁ * a * r₁⁻¹) * (r₂ * a * r₂⁻¹))
    (hE2B : ∀ a ∈ B, a ^ 3 = 1 → a ≠ 1 → ∀ x ∈ B, ∃ r₁ ∈ R0, ∃ r₂ ∈ R0,
      x = (r₁ * a * r₁⁻¹) * (r₂ * a * r₂⁻¹))
    (hE3 : ∃ a ∈ A, ∃ b ∈ B, Ord7 (a * b))
    {Y : Subgroup SL32} (hN : R0 ≤ Subgroup.normalizer (Y : Set SL32)) (hO : oTwoUpper Y = Y)
    (h7 : ¬ 7 ∣ Nat.card Y) {a : SL32} (haY : a ∈ Y) (haA : a ∈ A) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) : Y = A := by
  have hconj : ∀ r ∈ R0, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hN hr) y).mp hy
  have hAY : A ≤ Y := by
    intro x hx
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hE2A a haA ha3 ha1 x hx
    exact Y.mul_mem (hconj r₁ hr₁ a haY) (hconj r₂ hr₂ a haY)
  have hYA : Y ≤ A := by
    calc Y = oTwoUpper Y := hO.symm
      _ ≤ A := by
        refine (Subgroup.closure_le A).mpr fun x hx => ?_
        obtain ⟨hxY, hxodd⟩ := hx
        rcases odd_cases h7 hxY hxodd with rfl | ⟨hx3, hx1⟩
        · exact A.one_mem
        rcases hE1 x hx3 hx1 with hxA | hxB | ⟨r₂, hr₂, r₃, hr₃, h7'⟩
        · exact hxA
        · exfalso
          have hBY : B ≤ Y := by
            intro y hy
            obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hE2B x hxB hx3 hx1 y hy
            exact Y.mul_mem (hconj r₁ hr₁ x hxY) (hconj r₂ hr₂ x hxY)
          obtain ⟨a₀, ha₀, b₀, hb₀, h70⟩ := hE3
          exact no_ord7 h7 (Y.mul_mem (hAY ha₀) (hBY hb₀)) h70
        · exact absurd h7' (no_ord7 h7 (Y.mul_mem (Y.mul_mem hxY (hconj r₂ hr₂ x hxY))
            (hconj r₃ hr₃ x hxY)))
  exact le_antisymm hYA hAY

theorem classify {Y : Subgroup SL32} (hN : R0 ≤ Subgroup.normalizer (Y : Set SL32))
    (hO : oTwoUpper Y = Y) (hY : Y ≠ ⊥) (h7 : ¬ 7 ∣ Nat.card Y) : Y = A4a ∨ Y = A4b := by
  obtain ⟨a, haY, haodd, ha1⟩ : ∃ a ∈ Y, Odd (orderOf a) ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : oTwoUpper Y ≤ ⊥ := (Subgroup.closure_le _).mpr fun x hx => by
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      exact hcon x hx.1 hx.2
    rw [hO] at hle
    exact hY (le_bot_iff.mp hle)
  have ha3 : a ^ 3 = 1 := ((odd_cases h7 haY haodd).resolve_left ha1).1
  rcases e1_L a ha3 ha1 with haA | haB | ⟨r₂, hr₂, r₃, hr₃, h7'⟩
  · exact Or.inl (eq_of_mem_aux A4a A4b e1_L (fun a ha h3 h1 x hx => e2a_L ha h3 h1 hx)
      (fun a ha h3 h1 x hx => e2b_L ha h3 h1 hx) e3ab_L hN hO h7 haY haA ha3 ha1)
  · refine Or.inr (eq_of_mem_aux A4b A4a (fun x h3 h1 => ?_)
      (fun a ha h3 h1 x hx => e2b_L ha h3 h1 hx) (fun a ha h3 h1 x hx => e2a_L ha h3 h1 hx)
      e3ba_L hN hO h7 haY haB ha3 ha1)
    rcases e1_L x h3 h1 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exfalso
    have hconj : ∀ r ∈ R0, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y := fun r hr y hy =>
      (Subgroup.mem_normalizer_iff.mp (hN hr) y).mp hy
    exact no_ord7 h7 (Y.mul_mem (Y.mul_mem haY (hconj r₂ hr₂ a haY)) (hconj r₃ hr₃ a haY)) h7'

theorem localData_a : LocalData R0 A4a V4a where
  le_R := V4a_le_R0
  R_le := le_normalizer_of_forall_conj fun _ hk _ hv => R0_conj_V4a hk hv
  Y_le := le_normalizer_of_forall_conj fun _ hk _ hv => A4a_conj_V4a hk hv
  card_V := cards_std.2.2.2.1
  card_Y := cards_std.2.1
  comm := fun y hy hy1 hodd w hw =>
    comma_L hy hy1 ((odd_cases (Y := A4a) (by rw [cards_std.2.1]; norm_num) hy hodd).resolve_left
      hy1).1 hw
  weak := weaka_L

theorem localData_b : LocalData R0 A4b V4b where
  le_R := V4b_le_R0
  R_le := le_normalizer_of_forall_conj fun _ hk _ hv => R0_conj_V4b hk hv
  Y_le := le_normalizer_of_forall_conj fun _ hk _ hv => A4b_conj_V4b hk hv
  card_V := cards_std.2.2.2.2
  card_Y := cards_std.2.2.1
  comm := fun y hy hy1 hodd w hw =>
    commb_L hy hy1 ((odd_cases (Y := A4b) (by rw [cards_std.2.2.1]; norm_num) hy hodd).resolve_left
      hy1).1 hw
  weak := weakb_L

theorem map_symm_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem local_good_SL32 : ∀ R Y : Subgroup SL32, IsSylowTwoOf R ⊤ →
    R ≤ Subgroup.normalizer (Y : Set SL32) → oTwoUpper Y = Y → Y ≠ ⊥ → ¬ 7 ∣ Nat.card Y →
      ∃ V : Subgroup SL32, LocalData R Y V := by
  intro R Y hR hRY hO hY0 h7
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_R0 hR
  let e : SL32 ≃* SL32 := MulAut.conj g⁻¹
  have hRmap : R.map e.toMonoidHom = R0 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have := (hg r).mp hr
      simpa [e, MulAut.conj_apply] using this
    · intro hx
      refine ⟨g * x * g⁻¹, (hg _).mpr (by simpa [mul_assoc] using hx), ?_⟩
      simp [e, mul_assoc]
  have hN' : R0 ≤ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup SL32) : Set SL32) := by
    rw [← hRmap]
    exact map_le_normalizer_map _ hRY
  have hO' : oTwoUpper (Y.map e.toMonoidHom) = Y.map e.toMonoidHom := by
    rw [oTwoUpper_map, hO]
  have hY0' : Y.map e.toMonoidHom ≠ ⊥ := fun h =>
    hY0 ((Subgroup.map_eq_bot_iff_of_injective Y e.injective).mp h)
  have h7' : ¬ 7 ∣ Nat.card (Y.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hR : R = R0.map e.symm.toMonoidHom := by
    rw [← hRmap, map_symm_map]
  rcases classify hN' hO' hY0' h7' with h | h
  · refine ⟨V4a.map e.symm.toMonoidHom, ?_⟩
    have := localData_a.map e.symm
    rw [← h, map_symm_map, ← hR] at this
    exact this
  · refine ⟨V4b.map e.symm.toMonoidHom, ?_⟩
    have := localData_b.map e.symm
    rw [← h, map_symm_map, ← hR] at this
    exact this

end L3

end SBc15

end CFSG.Quasithin

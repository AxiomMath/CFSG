module

public import CFSG.Walter.Bender1970.S38.Action

public section

namespace CFSG.Walter

variable {A Y : Type*} [CommGroup A] [Group Y]

theorem exists_mem_ne_one_ne {M : Type*} [Group M] {Q : Subgroup M} [Finite Q]
    (h3 : 3 ≤ Nat.card Q) (u : M) : ∃ x ∈ Q, x ≠ 1 ∧ x ≠ u := by
  classical
  have := Fintype.ofFinite Q
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset Q).map (Function.Embedding.subtype _) ⊆
      ({1, u} : Finset M) := by
    intro y hy
    obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hy
    by_cases hy1 : (y' : M) = 1
    · rw [Finset.mem_insert]
      exact Or.inl hy1
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hcon y' y'.2 hy1)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_le_two (a := (1 : M)) (b := u)
  omega

namespace Bender38Action

variable {ρ : Y →* MulAut A} {W Q : Subgroup A} {X R : Subgroup Y}
  (hD : Bender38Action ρ W Q X R)
include hD

theorem le_Q_of_inf_eq_bot [Finite A] {C : Subgroup A} (hCR : ∀ r ∈ R, ∀ c ∈ C, ρ r c ∈ C)
    (hCW : ∀ w ∈ W, w ∈ C → w = 1) : C ≤ Q := by
  intro c hc
  obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul c
  by_cases hv1 : v = 1
  · rw [hv1, mul_one] at hc ⊢
    rw [hCW w hw hc]
    exact Q.one_mem
  have hQC : ∀ u ∈ Q, u ∈ C := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact C.one_mem
    obtain ⟨u₁, hu₁, hu₁1, hu₁u⟩ :=
      exists_mem_ne_one_ne (Q := Q) (by have := hD.four_le_card; omega) u
    set u₂ := u₁ * u with hu₂
    have hu₂Q : u₂ ∈ Q := Q.mul_mem hu₁ hu
    have hu₂1 : u₂ ≠ 1 := by
      intro h
      apply hu₁u
      have h1 : u₁ = u⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h1, inv_eq_of_mul_eq_one_left (by rw [← sq, hD.sq_eq_one])]
    obtain ⟨r₁, hr₁, hr₁v⟩ := hD.trans v hv hv1 u₁ hu₁ hu₁1
    obtain ⟨r₂, hr₂, hr₂v⟩ := hD.trans v hv hv1 u₂ hu₂Q hu₂1
    have h1 := C.mul_mem (hCR r₁ hr₁ _ hc) (hCR r₂ hr₂ _ hc)
    rw [hD.map_mul_of_mem_R hr₁ hw, hD.map_mul_of_mem_R hr₂ hw, hr₁v, hr₂v] at h1
    have h2 : w * u₁ * (w * u₂) = u := by
      rw [hu₂, mul_mul_mul_comm, ← sq, hD.sq_eq_one, one_mul, ← mul_assoc, ← sq, hD.sq_eq_one,
        one_mul]
    rwa [h2] at h1
  have hwC : w ∈ C := by simpa using C.mul_mem hc (C.inv_mem (hQC v hv))
  rw [hCW w hw hwC, one_mul]
  exact hv

theorem card_eq_of_abelian_normal [Finite A] [Finite Y] {N : Subgroup Y} (hN1 : N ≠ ⊥)
    (hNab : IsMulCommutative N) (hNn : N.Normal) (hNX : N ⊓ X = ⊥) :
    Nat.card W = 2 ∧ Nat.card Q = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemNX : ∀ n ∈ N, n ∈ X → n = 1 := fun n hn hnX => by
    have : n ∈ N ⊓ X := ⟨hn, hnX⟩
    rwa [hNX, Subgroup.mem_bot] at this
  have hNodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat hD.odd_card (Subgroup.card_subgroup_dvd_card N)
  have hfpf : ∀ x ∈ R, x ≠ 1 → ∀ n ∈ N, x * n * x⁻¹ = n → n = 1 := by
    intro x hx hx1 n hn h
    apply hmemNX n hn
    refine hD.mem_X_of_conj_mem hx hx1 ?_
    have : n * x * n⁻¹ = x := by
      calc n * x * n⁻¹ = (x * n * x⁻¹) * x * n⁻¹ := by rw [h]
        _ = x := by group
    rw [this]
    exact hx
  set C := fixOf ρ N with hC
  have hCW : ∀ w ∈ W, w ∈ C → w = 1 := by
    intro w hw hwC
    by_contra hw1
    apply hN1
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact hmemNX n hn (hD.mem_X_of_fix hw hw1 (hwC n hn))
  have hNinv : ∀ y : Y, ∀ c ∈ C, ρ y c ∈ C := by
    intro y c hc n hn
    exact map_mem_fixOf_conj hc y (by have := hNn.conj_mem _ hn y⁻¹; simpa using this)
  have hCQ : C ≤ Q := hD.le_Q_of_inf_eq_bot (fun r _ c hc => hNinv r c hc) hCW
  by_cases hC1 : C = ⊥
  ·
    have hfixR : fixOf ρ R = W := by
      obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
      ext a
      constructor
      · intro ha
        exact (hD.fix_iff hr hr1 a).mp (ha r hr)
      · intro ha s hs
        exact hD.fix_W s hs a ha
    have hcard := card_eq_card_fixOf_pow hD.sq_eq_one ρ hNab
      (fun r _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hNn]; exact Subgroup.mem_top r)
      hfpf hNodd
      (fun a ha => by
        have : a ∈ C := ha
        rwa [hC1, Subgroup.mem_bot] at this)
    rw [hfixR, hD.card_eq_mul] at hcard
    have hR := hD.card_R_add_one
    rw [show Nat.card R = Nat.card Q - 1 by omega] at hcard
    obtain ⟨a, ha⟩ := (hD.isPGroup_two W).exists_card_eq
    obtain ⟨b, hb⟩ := (hD.isPGroup_two Q).exists_card_eq
    have hW2 : 2 ≤ Nat.card W := by
      have := (Subgroup.one_lt_card_iff_ne_bot W).mpr hD.ne_bot
      omega
    exact eq_two_and_eq_four_of_mul_eq_pow ⟨a, ha⟩ ⟨b, hb⟩ hW2 hD.four_le_card hcard
  · exfalso
    obtain ⟨⟨c, hcC⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC1
    have hQC : ∀ u ∈ Q, u ∈ C := by
      intro u hu
      by_cases hu1 : u = 1
      · rw [hu1]
        exact C.one_mem
      obtain ⟨r, -, hru⟩ := hD.trans c (hCQ hcC) (fun h => hc1 (Subtype.ext h)) u hu hu1
      rw [← hru]
      exact hNinv r c hcC
    set D := Subgroup.closure {a : A | ∃ n ∈ N, ∃ b : A, ρ n b * b⁻¹ = a} with hDdef
    have hDinv : ∀ y : Y, ∀ d ∈ D, ρ y d ∈ D := by
      intro y d hd
      induction hd using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨n, hn, b, rfl⟩ := ha
        refine Subgroup.subset_closure ⟨y * n * y⁻¹, hNn.conj_mem n hn y, ρ y b, ?_⟩
        rw [map_mul ρ, map_mul ρ, MulAut.mul_apply, MulAut.mul_apply, map_inv,
          MulAut.inv_apply_self, map_mul (ρ y), map_inv]
      | one => rw [map_one]; exact D.one_mem
      | mul a b _ _ ha hb => rw [map_mul]; exact D.mul_mem ha hb
      | inv a _ ha => rw [map_inv]; exact D.inv_mem ha
    have := Fintype.ofFinite N
    let av : A →* A :=
      { toFun := fun a => ∏ n : N, ρ n a
        map_one' := by simp
        map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
    have hav_gen : ∀ n₀ ∈ N, ∀ b : A, av (ρ n₀ b * b⁻¹) = 1 := by
      intro n₀ hn₀ b
      rw [map_mul, map_inv, mul_inv_eq_one]
      change ∏ n : N, ρ n (ρ n₀ b) = ∏ n : N, ρ n b
      rw [← Fintype.prod_equiv (Equiv.mulRight (⟨n₀, hn₀⟩ : N))
        (fun n : N => ρ ((n * (⟨n₀, hn₀⟩ : N) : N) : Y) b) (fun n : N => ρ n b) (fun _ => rfl)]
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]
    have hDker : ∀ d ∈ D, av d = 1 := by
      intro d hd
      induction hd using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨n, hn, b, rfl⟩ := ha
        exact hav_gen n hn b
      | one => exact map_one av
      | mul a b _ _ ha hb => rw [map_mul, ha, hb, mul_one]
      | inv a _ ha => rw [map_inv, ha, inv_one]
    have hav_fix : ∀ a ∈ C, av a = a := by
      intro a ha
      change ∏ n : N, ρ n a = a
      rw [Finset.prod_congr rfl (fun (n : N) _ => ha n n.2), Finset.prod_const,
        Finset.card_univ, ← Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := hNodd
      rw [hk, pow_succ, pow_mul, hD.sq_eq_one, one_pow, one_mul]
    have hDQ : ∀ d ∈ D, d ∈ Q → d = 1 := fun d hd hdQ =>
      (hav_fix d (hQC d hdQ)).symm.trans (hDker d hd)
    obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
    have hDW : ∀ d ∈ D, d ∈ W := by
      intro d hd
      obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul d
      have h1 : ρ r (w * v) * (w * v)⁻¹ ∈ D := D.mul_mem (hDinv r _ hd) (D.inv_mem hd)
      rw [hD.map_mul_of_mem_R hr hw] at h1
      have h2 : w * ρ r v * (w * v)⁻¹ = ρ r v * v⁻¹ :=
        calc w * ρ r v * (w * v)⁻¹ = w * ρ r v * (w⁻¹ * v⁻¹) := by
              rw [mul_inv_rev, mul_comm v⁻¹]
          _ = ρ r v * v⁻¹ := by
              rw [mul_comm w (ρ r v), mul_assoc, ← mul_assoc w, mul_inv_cancel, one_mul]
      rw [h2] at h1
      have hrvQ : ρ r v * v⁻¹ ∈ Q := Q.mul_mem (hD.map_mem_Q r (hD.le_X hr) v hv) (Q.inv_mem hv)
      have h3 : ρ r v = v := mul_inv_eq_one.mp (hDQ _ h1 hrvQ)
      by_cases hv1 : v = 1
      · rw [hv1, mul_one]
        exact hw
      · exact absurd (hD.free r hr v hv h3 hv1) hr1
    obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hρn : ρ n ≠ 1 := fun h => hn1' (hD.injective (h.trans (map_one ρ).symm))
    obtain ⟨b, hb⟩ : ∃ b : A, ρ n b ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hρn (MulEquiv.ext hcon)
    have hd : ρ n b * b⁻¹ ∈ D := Subgroup.subset_closure ⟨n, hn, b, rfl⟩
    have hd1 : ρ n b * b⁻¹ ≠ 1 := fun h => hb (mul_inv_eq_one.mp h)
    have hdW := hDW _ hd
    apply hN1
    rw [eq_bot_iff]
    intro n' hn'
    rw [Subgroup.mem_bot]
    exact hmemNX n' hn' (hD.mem_X n' _ hdW hd1 (hDW _ (hDinv n' _ hd)))

end Bender38Action

end CFSG.Walter

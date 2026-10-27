module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XVCard
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TPtAct

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative
open CFSG.Quasithin.H13.L828T

section Generic

variable {G : Type} [Group G]

theorem ob5_index_two {V B : Subgroup G} (hBV : B ≤ V) {v : G} (hv : v ∈ V) (hvB : v ∉ B)
    (hV2 : ∀ x ∈ V, x * x = 1) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hcov : ∀ w ∈ V, w ∈ B ∨ ∃ b ∈ B, w = v * b) :
    (B.subgroupOf V).index = 2 := by
  classical
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨v, hv⟩, fun b => ?_⟩
  obtain ⟨b, hbV⟩ := b
  by_cases hb : b ∈ B
  · have hbv : b * v ∉ B := fun hbv => hvB (by
      have := B.mul_mem (B.inv_mem hb) hbv
      simpa using this)
    simp [Subgroup.mem_subgroupOf, hb, hbv]
  · rcases hcov b hbV with hb' | ⟨b', hb', rfl⟩
    · exact absurd hb' hb
    · have hcomm : v * b' = b' * v := hVc v hv b' (hBV hb')
      have hbv : v * b' * v = b' := by
        rw [hcomm, mul_assoc, hV2 v hv, mul_one]
      have hbv' : v * b' * v ∈ B := by rw [hbv]; exact hb'
      simp [Subgroup.mem_subgroupOf, hb, hbv']

theorem ob5_card_quot {W : Type} [CommGroup W] {B U : Subgroup W} (hUB : U ≤ B) :
    Nat.card (QMod B U) * Nat.card U = Nat.card B := by
  have h1 : Nat.card (U.subgroupOf B) * (U.subgroupOf B).index = Nat.card B :=
    Subgroup.card_mul_index (U.subgroupOf B)
  have h2 : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  have h3 : Nat.card (QMod B U) = (U.subgroupOf B).index := rfl
  rw [h2] at h1
  rw [h3, mul_comm]
  exact h1

theorem ob5_card_U_sixteen {U : Type} [Group U] [Finite U] (hU : IsPGroup 2 U) (hrk : rk U = 4) :
    Nat.card U = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := U)).mp hU
  have hrk' : rk U = n := by
    unfold rk
    rw [hn, padicValNat.prime_pow]
  rw [hrk'] at hrk
  subst hrk
  rw [hn]
  norm_num

end Generic

section Ctx

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

theorem ob5_card_V (c : S828Ctx T L I H h k) (hrow : ∃ n : ℕ, Row711L3Nine T L I n) :
    Nat.card ↥(fsuV T I) = 512 := by
  obtain ⟨n, hn⟩ := hrow
  have hn1 : n = 1 := c.hC5.2.2.1 n hn
  subst hn1
  have := CFSG.Quasithin.H13.L827X.card_of_binaryNineTensor (le_refl 1) hn.2
  simpa using this

theorem ob5_card_B (c : S828Ctx T L I H h k) (hV512 : Nat.card ↥(fsuV T I) = 512)
    {v : G} (hv : v ∈ fsuV T I) (hvB : v ∉ ch82B (fsuV T I) h)
    (hcov : ∀ w ∈ fsuV T I, w ∈ ch82B (fsuV T I) h ∨ ∃ b ∈ ch82B (fsuV T I) h, w = v * b) :
    Nat.card ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)) = 256 := by
  have hBV : ch82B (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hV2 : ∀ x ∈ fsuV T I, x * x = 1 := fun x hx => by
    have := c.hV.2 x hx
    rwa [pow_two] at this
  have hVc : ∀ x ∈ fsuV T I, ∀ y ∈ fsuV T I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuV T I)) ⟨y, hy⟩)
  have hidx := ob5_index_two hBV hv hvB hV2 hVc hcov
  have hmul := Subgroup.card_mul_index ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
  rw [hidx, hV512] at hmul
  omega

theorem ob5_card_QB (c : S828Ctx T L I H h k) (hB256 : Nat.card ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)) = 256)
    (hU16 : Nat.card ↥(ch82U (fsuV T I) h) = 16) :
    Nat.card (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 16 := by
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hUB : ch82U (fsuV T I) h ≤ ch82B (fsuV T I) h := c.hUB
  have hUB' : (ch82U (fsuV T I) h).subgroupOf (fsuV T I) ≤
      (ch82B (fsuV T I) h).subgroupOf (fsuV T I) := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hUB hx
  have h1 := ob5_card_quot hUB'
  have h2 : Nat.card ↥((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) = 16 := by
    rw [← hU16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  show Nat.card (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
    ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))) = 16
  rw [h2, hB256] at h1
  omega

theorem ob5_card_M (c : S828Ctx T L I H h k) (hQB16 : Nat.card (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 16) :
    Nat.card (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 2 ^ 8 := by
  rw [Nat.card_prod, hQB16]
  norm_num

end Ctx

end CFSG.Quasithin.H13

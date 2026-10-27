module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Odd
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Z
public import CFSG.Quasithin.EmptyFaithful.S1421QA15R
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.exists_z (c : Core3Ctx T M H K1 L M₁) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ (∀ t ∈ T, t * z = z * t) ∧
      Lemma115Hyp (g0Of T M H K1) (sOf T K1) (mcOf T) z ∧ oddCoreIn (g0Of T M H K1) = ⊥ := by
  obtain ⟨z, hz, hz1, hz2, hzc, hZ⟩ := exists_generator c.st
  have h115 := lemma115Hyp_g0 c.st c.pCore_ne c.inM c.sylow hz hz1 hz2 hzc hZ
  have hYG0 : yOfL22 T M ≤ g0Of T M H K1 := yOfL22_le_g0Of T M H K1
  exact ⟨z, hz, hz1, hz2, hzc, h115,
    oddCoreIn_g0_eq_bot c.st hYG0 hz hz1 h115.inverts_oddCoreIn⟩

@[expose] def oddCentralOf (L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ L ∧ (∀ l ∈ L, g * l = l * g) ∧ ∃ m : ℕ, Odd m ∧ g ^ m = 1}
  one_mem' := ⟨L.one_mem, fun l _ => by simp, 1, odd_one, one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨haL, hac, m, hm, ham⟩ ⟨hbL, hbc, k, hk, hbk⟩
    refine ⟨L.mul_mem haL hbL, fun l hl => ?_, m * k, hm.mul hk, ?_⟩
    · rw [mul_assoc, hbc l hl, ← mul_assoc, hac l hl, mul_assoc]
    · have hcomm : Commute a b := hac b hbL
      rw [hcomm.mul_pow, pow_mul, ham, one_pow, mul_comm m k, pow_mul, hbk, one_pow, one_mul]
  inv_mem' := by
    rintro a ⟨haL, hac, m, hm, ham⟩
    refine ⟨L.inv_mem haL, fun l hl => ?_, m, hm, by rw [inv_pow, ham, inv_one]⟩
    have := hac l hl
    calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * l) * a⁻¹ := by rw [← this]
      _ = l * a⁻¹ := by group

omit [Finite G] in
theorem le_oddCoreIn_of_normalizes {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem Core3Ctx.oddCentralOf_eq_bot (c : Core3Ctx T M H K1 L M₁)
    (hodd : oddCoreIn (g0Of T M H K1) = ⊥) : oddCentralOf L = ⊥ := by
  have hL := c.g0Of_le_normalizer
  have hle : oddCentralOf L ≤ g0Of T M H K1 := fun g hg => c.le_g0Of hg.1
  have hnorm : g0Of T M H K1 ≤ Subgroup.normalizer ((oddCentralOf L : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ g0Of T M H K1, ∀ g ∈ oddCentralOf L, h * g * h⁻¹ ∈ oddCentralOf L := by
      rintro h hh g ⟨hgL, hgc, m, hm, hgm⟩
      have hl : ∀ x ∈ L, h * x * h⁻¹ ∈ L := fun x hx =>
        (Subgroup.mem_normalizer_iff.mp (hL hh) x).mp hx
      have hl' : ∀ x ∈ L, h⁻¹ * x * h ∈ L := fun x hx => by
        have := (Subgroup.mem_normalizer_iff.mp (hL ((g0Of T M H K1).inv_mem hh)) x).mp hx
        simpa using this
      refine ⟨hl g hgL, fun l hl0 => ?_, m, hm, ?_⟩
      · have h1 := hgc (h⁻¹ * l * h) (hl' l hl0)
        calc h * g * h⁻¹ * l = h * (g * (h⁻¹ * l * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * l * h) * g) * h⁻¹ := by rw [h1]
          _ = l * (h * g * h⁻¹) := by group
      · calc (h * g * h⁻¹) ^ m = h * g ^ m * h⁻¹ := by
              rw [conj_pow]
          _ = 1 := by rw [hgm]; group
    intro g
    refine ⟨fun hg => key h hh g hg, fun hg => ?_⟩
    have := key h⁻¹ ((g0Of T M H K1).inv_mem hh) _ hg
    simpa [mul_assoc] using this
  have hoddcard : Odd (Nat.card (oddCentralOf L)) := by
    by_contra hcon
    have h2 : 2 ∣ Nat.card (oddCentralOf L) := by
      rcases Nat.even_or_odd (Nat.card (oddCentralOf L)) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨-, -, m, hm, hxm⟩ := x.2
    have h1 : orderOf (x : G) ∣ m := orderOf_dvd_of_pow_eq_one hxm
    have h3 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    rw [h3] at h1
    obtain ⟨k, hk⟩ := h1
    have : Even m := ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hm) this
  have := le_oddCoreIn_of_normalizes hle hnorm hoddcard
  rw [hodd] at this
  exact eq_bot_iff.mpr this

theorem Core3Ctx.center_eq_pCore (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hodd : oddCoreIn (g0Of T M H K1) = ⊥) : Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
  have hbot := c.oddCentralOf_eq_bot hodd
  apply le_antisymm
  · have hp : IsPGroup 2 (Subgroup.center ↥L) := by
      intro x
      have hx : orderOf (x : ↥L) ≠ 0 := (orderOf_pos _).ne'
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hx
      have hy : (((x : ↥L) ^ 2 ^ k : ↥L) : G) ∈ oddCentralOf L := by
        refine ⟨(((x : ↥L) ^ 2 ^ k : ↥L)).2, fun l hl => ?_, m, hm, ?_⟩
        · have hc := Subgroup.mem_center_iff.mp
            (Subgroup.pow_mem _ x.2 (2 ^ k)) ⟨l, hl⟩
          have := congrArg Subtype.val hc
          simpa using this.symm
        · have : ((x : ↥L) ^ 2 ^ k) ^ m = 1 := by
            rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
          simpa using congrArg Subtype.val this
      rw [hbot] at hy
      have h1 : (x : ↥L) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        simpa using hy
      exact ⟨k, Subtype.ext (by simpa using h1)⟩
    exact le_sSup ⟨inferInstance, hp⟩
  · exact normal_isPGroup_le_center_of_isQuasisimple hq _ (CFSG.pCore_isPGroup (p := 2) (G := ↥L))

theorem Core3Ctx.isSimpleGroup_quot (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hodd : oddCoreIn (g0Of T M H K1) = ⊥) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have h := c.center_eq_pCore hq hodd
  have e : (↥L ⧸ Subgroup.center ↥L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.quotientMulEquivOfEq h
  exact e.isSimpleGroup_congr.mp hq.2.1

end S1421

end CFSG.Quasithin

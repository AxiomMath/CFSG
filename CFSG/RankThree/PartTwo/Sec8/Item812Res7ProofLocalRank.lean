module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Item812Res7

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {P : Subgroup G} {g : G}
    (h : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem inv_pow_mul_pow_mem {N : Subgroup G} {y u : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hu : y⁻¹ * u ∈ N) :
    ∀ k : ℕ, (y ^ k)⁻¹ * u ^ k ∈ N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hconj : y⁻¹ * ((y ^ k)⁻¹ * u ^ k) * y ∈ N := by
      have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyN) _).mp ih
      simpa using h
    have e : (y ^ (k + 1))⁻¹ * u ^ (k + 1) =
        (y⁻¹ * ((y ^ k)⁻¹ * u ^ k) * y) * (y⁻¹ * u) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem hconj hu

theorem four_le_localRank_of_trivial_mod {F N D : Subgroup G} {y : G}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hN3 : ¬ 3 ∣ Nat.card N) (hFN : F ≤ Subgroup.normalizer (N : Set G))
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hy3 : y ^ 3 ∈ N)
    (hFy : ∀ f ∈ F, y⁻¹ * (f * y * f⁻¹) ∈ N) (hyF : ∀ f ∈ F, ∀ n ∈ N, y ≠ f * n)
    (hND : N ≤ D) (hD3 : ¬ 3 ∣ Nat.card D) (hD2 : 2 ∣ Nat.card D)
    (hFD : F ≤ Subgroup.normalizer (D : Set G)) (hyD : y ∈ Subgroup.normalizer (D : Set G)) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hact : ∀ f ∈ F, ∀ g : G, y⁻¹ * g ∈ N → y⁻¹ * (f * g * f⁻¹) ∈ N := by
    intro f hf g hg
    have e : y⁻¹ * (f * g * f⁻¹) = (y⁻¹ * (f * y * f⁻¹)) * (f * (y⁻¹ * g) * f⁻¹) := by group
    rw [e]
    exact N.mul_mem (hFy f hf) ((Subgroup.mem_normalizer_iff.mp (hFN hf) _).mp hg)
  let α := {g : G // y⁻¹ * g ∈ N}
  let _ : MulAction F α :=
    { smul := fun f g => ⟨(f : G) * g * (f : G)⁻¹, hact f f.2 g g.2⟩
      one_smul := fun g => Subtype.ext (by
        change ((1 : F) : G) * g * ((1 : F) : G)⁻¹ = g
        simp)
      mul_smul := fun f₁ f₂ g => Subtype.ext (by
        change ((f₁ : G) * f₂) * g * ((f₁ : G) * f₂)⁻¹ = f₁ * (f₂ * g * (f₂ : G)⁻¹) * (f₁ : G)⁻¹
        group) }
  have hαN : Nat.card α = Nat.card N := by
    refine Nat.card_congr ⟨fun g => ⟨y⁻¹ * g, g.2⟩, fun n => ⟨y * n, by simp⟩,
      fun g => Subtype.ext (by simp), fun n => Subtype.ext (by simp)⟩
  have hFp : IsPGroup 3 F := fun f => ⟨1, Subtype.ext (by simpa using hF.2 f f.2)⟩
  obtain ⟨g₀, hg₀⟩ := hFp.nonempty_fixed_point_of_prime_not_dvd_card α (by rwa [hαN])
  set u : G := (g₀ : G) with hudef
  have hun : y⁻¹ * u ∈ N := g₀.2
  have hfix : ∀ f ∈ F, f * u * f⁻¹ = u := fun f hf =>
    congrArg Subtype.val (hg₀ ⟨f, hf⟩)
  have hfu : ∀ f ∈ F, f * u = u * f := fun f hf => by
    calc f * u = f * u * f⁻¹ * f := by group
      _ = u * f := by rw [hfix f hf]
  have hpow := inv_pow_mul_pow_mem hyN hun
  have hw : u ^ 3 ∈ N := by
    have h := N.mul_mem hy3 (hpow 3)
    simpa using h
  set r := orderOf (u ^ 3) with hr
  have hr3 : ¬ 3 ∣ r := fun h => hN3 (h.trans (Subgroup.orderOf_dvd_natCard N hw))
  have hrsq : r ^ 2 % 3 = 1 := by
    have h := Nat.mod_lt r (show 0 < 3 by norm_num)
    have h0 : r % 3 ≠ 0 := fun h0 => hr3 (Nat.dvd_of_mod_eq_zero h0)
    rw [Nat.pow_mod]
    interval_cases hrm : r % 3 <;> simp_all
  obtain ⟨k, hk⟩ : ∃ k, r ^ 2 = 3 * k + 1 := ⟨r ^ 2 / 3, by
    have h := (Nat.div_add_mod (r ^ 2) 3).symm
    rwa [hrsq] at h⟩
  set y'' := u ^ (r ^ 2) with hy''
  have hy''3 : y'' ^ 3 = 1 := by
    rw [hy'', ← pow_mul, mul_comm, pow_mul, sq, pow_mul, pow_orderOf_eq_one, one_pow]
  have hy''F : ∀ f ∈ F, f * y'' = y'' * f := fun f hf =>
    ((Commute.pow_right (show Commute f u from hfu f hf) (r ^ 2))).eq
  have hy''notF : y'' ∉ F := by
    intro hmem
    apply hyF y'' hmem (((u ^ 3) ^ k)⁻¹ * (u⁻¹ * y))
    · refine N.mul_mem (N.inv_mem (N.pow_mem hw k)) ?_
      have := N.inv_mem hun
      simpa using this
    · have e : u ^ (r ^ 2) = u ^ (3 * k) * u := by rw [hk, pow_succ]
      rw [hy'', e, ← pow_mul]
      group
  have huD : u ∈ Subgroup.normalizer (D : Set G) := by
    have e : u = y * (y⁻¹ * u) := by group
    rw [e]
    exact Subgroup.mul_mem _ hyD (Subgroup.le_normalizer (hND hun))
  have hy''D : y'' ∈ Subgroup.normalizer (D : Set G) := Subgroup.pow_mem _ huD _
  obtain ⟨hSab, hScard⟩ := Sec5.isElemAbelian_sup_zpowers hF hy''notF hy''3 hy''F
  have hSD : F ⊔ Subgroup.zpowers y'' ≤ Subgroup.normalizer (D : Set G) :=
    sup_le hFD ((Subgroup.zpowers_le).mpr hy''D)
  exact CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three hSD hSab
    (by rw [hScard, hF27]; norm_num)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3) hD2

end Item812Res7

end CFSG.RankThree.PartTwo.Sec8

module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Rep
import CFSG.Models.PGLOrders
import CFSG.Models.PGLSimple
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26GL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26Klein
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26Lin
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3L26U34

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.PGLModel (projSU)
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
open Module

theorem isSimpleGroup_projSU_three_four : IsSimpleGroup (projSU 3 2 2) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩

theorem isPerfect_projSU_three_four : Group.IsPerfect (projSU 3 2 2) := by
  haveI := isSimpleGroup_projSU_three_four
  refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => ?_
  have hp := (Group.is_simple_iff_prime_card (α := projSU 3 2 2)).mp inferInstance
  rw [CFSG.PGLModel.card_projSU_three_four] at hp
  norm_num at hp

theorem exists_two_element_fixed_of_klein {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ : X →* (V →ₗ[ZMod p] V))
    (hK : ∃ a b : X ⧸ ρ.ker, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hdim : 7 ≤ finrank (ZMod p) V) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := hK
  let ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod p] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
  have hinj : Function.Injective ρbar := liftKer_injective ρ
  have hK2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hρa : ρbar a * ρbar a = 1 := by rw [← map_mul, ha, map_one]
  have hρb : ρbar b * ρbar b = 1 := by rw [← map_mul, hb, map_one]
  have hρab : ρbar a * ρbar b = ρbar b * ρbar a := by rw [← map_mul, ← map_mul, hab]
  have hsum := finrank_le_add_ker hK2 hρa hρb hρab
  obtain ⟨g, hg2, hg1, hgdim⟩ : ∃ g : X ⧸ ρ.ker, g * g = 1 ∧ g ≠ 1 ∧
      3 ≤ finrank (ZMod p) (LinearMap.ker (ρbar g - 1)) := by
    by_cases h1 : 3 ≤ finrank (ZMod p) (LinearMap.ker (ρbar a - 1))
    · exact ⟨a, ha, ha1, h1⟩
    by_cases h2 : 3 ≤ finrank (ZMod p) (LinearMap.ker (ρbar b - 1))
    · exact ⟨b, hb, hb1, h2⟩
    refine ⟨a * b, ?_, ?_, ?_⟩
    · calc a * b * (a * b) = a * b * (b * a) := by rw [hab]
        _ = 1 := by rw [mul_assoc, ← mul_assoc b b a, hb, one_mul, ha]
    · intro h1'
      apply hne
      calc a = a * (a * b) := by rw [h1', mul_one]
        _ = b := by rw [← mul_assoc, ha, one_mul]
    · rw [map_mul]
      omega
  obtain ⟨t, htg, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' ρ.ker)
    (QuotientGroup.mk'_surjective ρ.ker) hg2
  have hρt : ρ t = ρbar g := by
    rw [← htg, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
  · rw [hρt]
    intro h1
    exact hg1 (hinj (h1.trans (map_one ρbar).symm))
  · rw [hρt]
    exact hgdim

private theorem exists_surjective_projSU_of_ker {X : Type*} [Group X] [Group.IsPerfect X]
    {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N) (e : X ⧸ N ≃* projSU 3 2 2)
    {M : Type*} [Monoid M] (ρ : X →* M) (hρ : ∃ x, ρ x ≠ 1) :
    ∃ π : X ⧸ ρ.ker →* projSU 3 2 2, Function.Surjective π := by
  haveI := isSimpleGroup_projSU_three_four
  have hKN : ρ.ker ≤ N := ker_le_of_perfect hN (MulEquiv.isSimpleGroup e) ρ hρ
  refine ⟨e.toMonoidHom.comp
    (QuotientGroup.map ρ.ker N (MonoidHom.id X) (by rw [Subgroup.comap_id]; exact hKN)), ?_⟩
  refine e.surjective.comp ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  refine ⟨QuotientGroup.mk' ρ.ker x, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply, QuotientGroup.mk'_apply]

theorem eight_le_finrank_of_u34 {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N) (e : X ⧸ N ≃* projSU 3 2 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod 5) V] [Module.Finite (ZMod 5) V]
    (σ : X →* (V →ₗ[ZMod 5] V)) (hσ : ∃ x, σ x ≠ 1) : 8 ≤ finrank (ZMod 5) V := by
  by_contra hlt
  have hdim : finrank (ZMod 5) V ≤ 7 := by omega
  let σbar : X ⧸ σ.ker →* (V →ₗ[ZMod 5] V) := QuotientGroup.lift σ.ker σ (fun _ hx => hx)
  have hinj : Function.Injective σbar := liftKer_injective σ
  obtain ⟨π, hπ⟩ := exists_surjective_projSU_of_ker hN e σ hσ
  obtain ⟨g, x, hg, hxg⟩ := exists_orderOf_thirteen_conj_cube_projSU
  obtain ⟨g', y, hg', hyg'⟩ := exists_orderOf_thirteen_conj_cube_of_surjective π hπ
    (not_sq_thirteen_dvd_card_quotient_ker hdim σ) hg hxg
  refine false_of_pow_thirteen_conj_cube hdim (γ := σbar g') (ξ := σbar y) ?_ ?_
    ((Group.isUnit y).map σbar) ?_
  · rw [← map_pow, ← hg', pow_orderOf_eq_one, map_one]
  · intro h1
    have h2 : g' = 1 := hinj (h1.trans (map_one σbar).symm)
    rw [h2, orderOf_one] at hg'
    omega
  · rw [← map_pow, ← map_mul, ← map_mul]
    congr 1
    calc y * g' = y * g' * y⁻¹ * y := by group
      _ = g' ^ 3 * y := by rw [hyg']

theorem exists_two_element_fixed_of_seven_u34 {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N)
    (e : X ⧸ N ≃* projSU 3 2 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V))
    (hρ : ∃ x, ρ x ≠ 1) (hdim : 7 ≤ finrank (ZMod p) V) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  obtain ⟨π, hπ⟩ := exists_surjective_projSU_of_ker hN e ρ hρ
  refine exists_two_element_fixed_of_klein hp2 ρ ?_ hdim
  exact exists_klein_four_of_surjective_of_pow_eight π hπ
    (by rw [CFSG.PGLModel.card_projSU_three_four]; norm_num) pow_four_eq_one_of_pow_eight_projSU

theorem false_of_perfect_cover_act_u34 {G : Type} [Group G] [Finite G]
    (hloc : CFSG.Assembly.RankThreeEven.localRank 5 G < 3) {Pi S : Subgroup G}
    [Group.IsPerfect Pi] {N : Subgroup Pi} [N.Normal] (hN : Group.IsSolvable N)
    (e : Pi ⧸ N ≃* projSU 3 2 2) (hS : IsPGroup 5 S)
    (hPS : Pi ≤ Subgroup.normalizer (S : Set G)) (hact : ∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨X₂, hX₂, h3⟩ := exists_twoLocal_three_le_pRank (by norm_num) hS hPS hact
    fun V _ _ _ ρ hρ => exists_two_element_fixed_of_seven_u34 hN e (by norm_num) ρ hρ
      (le_trans (by norm_num) (eight_le_finrank_of_u34 hN e ρ hρ))
  have h1 := CFSG.RankThree.Classical.pRank_le_localRank (Fact.out : (5 : ℕ).Prime).one_lt hX₂
  omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

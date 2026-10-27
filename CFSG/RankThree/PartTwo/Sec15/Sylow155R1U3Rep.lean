module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3No3
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartOne.S11c.CentralWitness

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
open CFSG.RankThree.PartOne.FixedRank36 (fixedSub frattiniRep)
open Module
open scoped IsMulCommutative

theorem exists_two_element_fixed_of_seven {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N) {f : ℕ} (hf : 3 ≤ f)
    (e : X ⧸ N ≃* projSL 2 (GaloisField 2 f)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V))
    (hρ : ∃ x, ρ x ≠ 1) (hdim : 7 ≤ finrank (ZMod p) V) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  have hKN : ρ.ker ≤ N := ker_le_of_perfect hN hsimple ρ hρ
  let ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod p] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
  have hinj : Function.Injective ρbar := liftKer_injective ρ
  let π : X ⧸ ρ.ker →* projSL 2 (GaloisField 2 f) :=
    e.toMonoidHom.comp
      (QuotientGroup.map ρ.ker N (MonoidHom.id X) (by rw [Subgroup.comap_id]; exact hKN))
  have hπs : Function.Surjective π := by
    refine e.surjective.comp ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨QuotientGroup.mk' ρ.ker x, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply, QuotientGroup.mk'_apply]
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_klein_four hf π hπs
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

theorem exists_twoLocal_three_le_pRank {G : Type} [Group G] [Finite G] {Pi S : Subgroup G}
    [Group.IsPerfect Pi] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hS : IsPGroup p S)
    (hPS : Pi ≤ Subgroup.normalizer (S : Set G)) (hact : ∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s)
    (hfix : ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
      (ρ : Pi →* (V →ₗ[ZMod p] V)), (∃ x, ρ x ≠ 1) →
        ∃ t : Pi, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ finrank (ZMod p) (LinearMap.ker (ρ t - 1))) :
    ∃ X₂ : Subgroup G, CFSG.Assembly.IsTwoLocal X₂ ∧ 3 ≤ CFSG.Assembly.pRank p X₂ := by
  classical
  have hp : p.Prime := Fact.out
  set ρ : Pi →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hPS) with hρ
  have hρapp : ∀ (x : Pi) (s : S), ((ρ x s : S) : G) = x * s * x⁻¹ := fun _ _ => rfl
  have hρ1 : ∃ x, ρ x ≠ 1 := by
    obtain ⟨x, hx, s, hs, hxs⟩ := hact
    refine ⟨⟨x, hx⟩, fun h1 => hxs ?_⟩
    have h2 := hρapp ⟨x, hx⟩ ⟨s, hs⟩
    rw [h1] at h2
    exact h2.symm
  obtain ⟨D, hDchar, hDp, hDexp, hDclass, hel, xD, hxD⟩ :=
    TwoStarProof.exists_critical_rep_ne_one hp2 hS ρ hρ1
  set ρD : Pi →* MulAut D := (Sec3.restrictCharacteristic D).comp ρ with hρD
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  obtain ⟨t, hρt, ⟨k, htk⟩, hdim⟩ :=
    hfix (Additive (D ⧸ frattini D)) (frattiniRep p ρD) ⟨xD, hxD⟩
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    apply hρt
    rw [show t = 1 from Subtype.ext h1, map_one]
  have htk' : (t : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val htk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hrank := TwoStarProof.three_le_pRank_fixed hp2 hDp hDexp hDclass ρD htk hdim
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_isElementaryAbelian_card_pRank (p := p) hp.one_lt
      (H := fixedSub (ρD t))
  let ι : fixedSub (ρD t) →* G := S.subtype.comp (D.subtype.comp (fixedSub (ρD t)).subtype)
  have hιinj : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hEe : CFSG.Assembly.IsElemAbelian p (E.map ι) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩
      apply Subtype.ext
      change ι u * ι v = ι v * ι u
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian u hu, map_one]
  have hEt : E.map ι ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    have hy : ρD t y.1 = y.1 := y.2
    have h1 : (t : G) * ι y * (t : G)⁻¹ = ι y := congrArg (fun u : D => ((u : S) : G)) hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ι y * t = (t : G) * ι y * (t : G)⁻¹ * t := by rw [h1]
      _ = t * ι y := by group
  refine ⟨Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G),
    ⟨_, ?_, TwoStarProof.isPGroup_zpowers_of_pow htk', rfl⟩, ?_⟩
  · intro h1
    apply ht1
    have : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
    rwa [h1, Subgroup.mem_bot] at this
  · have h1 := Sec5.le_pRank_of_elemAbelian hp
      (hEt.trans (TwoStarProof.centralizer_le_normalizer_zpowers _)) hEe
      (by rw [Subgroup.card_map_of_injective hιinj, hEcard])
    omega

theorem false_of_perfect_cover_act_of_minDegree {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {Pi S : Subgroup G} [Group.IsPerfect Pi] {N : Subgroup Pi} [N.Normal]
    (hN : Group.IsSolvable N) {f : ℕ} (hf : 3 ≤ f) (e : Pi ⧸ N ≃* projSL 2 (GaloisField 2 f))
    (hdeg : ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
      (ρ : Pi →* (V →ₗ[ZMod p] V)), (∃ x, ρ x ≠ 1) → 7 ≤ finrank (ZMod p) V)
    (hS : IsPGroup p S) (hPS : Pi ≤ Subgroup.normalizer (S : Set G))
    (hact : ∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s) : False := by
  obtain ⟨X₂, hX₂, h3⟩ := exists_twoLocal_three_le_pRank hp2 hS hPS hact
    fun V _ _ _ ρ hρ => exists_two_element_fixed_of_seven hN hf e hp2 ρ hρ (hdeg V ρ hρ)
  have h1 := CFSG.RankThree.Classical.pRank_le_localRank (Fact.out : p.Prime).one_lt hX₂
  omega

theorem false_of_perfect_cover_act
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {Pi S : Subgroup G}
    [hPi : Group.IsPerfect Pi] {N : Subgroup Pi} [N.Normal] (hN : Group.IsSolvable N) {f : ℕ}
    (hf : 6 ≤ f) (e : Pi ⧸ N ≃* projSL 2 (GaloisField 2 f)) (hS : IsPGroup p S)
    (hPS : Pi ≤ Subgroup.normalizer (S : Set G)) (hact : ∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s) :
    False :=
  false_of_perfect_cover_act_of_minDegree (by omega) hloc hN (by omega) e
    (fun V _ _ _ ρ hρ => l2EvenSolvableMinDegree_no3 f hf p hp5 Pi hPi N hN ⟨e⟩ V ρ hρ) hS hPS hact

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

module

public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.RankThree.Chevalley.OddExceptionalRealRootElement
public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.TitsCover

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank Subgroup CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem exists_prime_gt_three_dvd_of_mod {n : ℕ} (h1 : n ≠ 1) (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ n := by
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  refine ⟨r, hr, ?_, hrd⟩
  have hr2 : r ≠ 2 := fun h => by
    subst h
    omega
  have hr3 : r ≠ 3 := fun h => by
    subst h
    omega
  have := hr.two_le
  omega

theorem exists_quotient_witness_of_suzukiModel {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : SuzukiModel S p f) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  obtain ⟨-, hUcard, -⟩ := suzuki_unipotent_structure (a := a) hK
  obtain ⟨-, -, hTcard, hTN, -⟩ := suzuki_borel_structure (a := a) hK
  have h4 : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; simp
  have hq : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by rw [pow_succ, pow_mul]; norm_num; ring
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_of_mod (n := 2 ^ (2 * a + 1) - 1)
    (by omega) (by omega) (by omega)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r (show r ∣ Nat.card (suzukiT a K) by
    rw [hTcard]
    exact hrd)
  have hU2 : IsPGroup 2 (suzukiU a K) :=
    IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [hUcard, ← pow_mul, mul_comm])
  have hUne : suzukiU a K ≠ ⊥ := fun hb => by
    rw [hb, card_bot] at hUcard
    have : 1 < (2 ^ (2 * a + 1)) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  refine quotient_witness_of_mulEquiv e ⟨suzukiU a K, hUne, hU2, Or.inl ⟨r, hr, hr3, ?_⟩⟩
  have hd := orderOf_dvd_natCard (⟨(y : suzukiGroup a K), hTN y.2⟩ :
    normalizer ((suzukiU a K : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)))
  rwa [orderOf_mk, orderOf_coe, hy] at hd

theorem exists_quotient_witness_of_smallReeModel {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨-, -, rfl, ⟨b, hb, heb⟩, hiso⟩ := small_Ree_model_Schreier S p f h
  obtain ⟨-, b', heb', K, _, _, hK, hw⟩ := h
  have hb' : 1 ≤ b' := by omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso b' K heb' hK hw
  have hK' : Nat.card K = 3 ^ (2 * b' + 1) := by rw [hK, heb']
  obtain ⟨⟨φ, -⟩, -⟩ := small_Ree_positive_torus_action b' K hK'
  have hle : ReeTag.G2.reeFixedTorus K b' ≤ ReeTag.G2.reeGamma K b' := inf_le_right
  let ι : Kˣ →* ReeTag.G2.reeGamma K b' := (Subgroup.inclusion hle).comp φ.toMonoidHom
  have hι : Function.Injective ι := (Subgroup.inclusion_injective hle).comp φ.injective
  have h3 : ringChar K = 3 := ringChar.eq K 3
  have hneg : orderOf (-1 : Kˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, h3]
    rfl
  have ht : orderOf (ι (-1)) = 2 := by rw [orderOf_injective ι hι, hneg]
  obtain ⟨hVne, hV2⟩ := zpowers_ne_bot_and_isPGroup_two ht
  have h9 : 9 ^ b' % 4 = 1 := by rw [Nat.pow_mod]; simp
  have h9' : 9 ≤ 9 ^ b' := Nat.le_self_pow (by omega) 9
  have hq : 3 ^ (2 * b' + 1) = 3 * 9 ^ b' := by rw [pow_succ, pow_mul]; norm_num; ring
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_of_mod
    (n := (3 ^ (2 * b' + 1) - 1) / 2) (by omega) (by omega) (by omega)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r (show r ∣ Nat.card Kˣ by
    rw [Nat.card_units, hK']
    exact hrd.trans (Nat.div_dvd_of_dvd (by omega)))
  have hyN : ι y ∈
      normalizer ((zpowers (ι (-1)) : Subgroup _) : Set (ReeTag.G2.reeGamma K b')) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    rw [← map_zpow, ← map_mul, ← map_mul, mul_comm]
  refine quotient_witness_of_mulEquiv e ⟨_, hVne, hV2, Or.inl ⟨r, hr, hr3, ?_⟩⟩
  have hd := orderOf_dvd_natCard (⟨ι y, hyN⟩ :
    normalizer ((zpowers (ι (-1)) : Subgroup _) : Set (ReeTag.G2.reeGamma K b')))
  rwa [orderOf_mk, orderOf_injective ι hι, hy] at hd

theorem center_eq_bot_of_largeReeTitsModel {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (center L))) {t : StatedLieTag} (ht : t = .twistedF4 ∨ t = .Tits)
    {p f : ℕ} (h : ReeTitsModel (L ⧸ center L) t p f) : center L = ⊥ := by
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
    have hker := ker_comp_mk'_center e
    have h1 := CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
      CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hodd)
    rwa [hker] at h1
  · obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
    have hker := ker_comp_mk'_center e
    have h1 := CFSG.SectionRank.Tits_perfect_odd_cover_trivial (K := K) hK
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hodd)
    rwa [hker] at h1

theorem exists_quotient_witness_of_real {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x z b : S} (hx : orderOf x = p) (hz : orderOf z = 2) (hxz : x * z = z * x)
    (hb : b * x * b⁻¹ = x⁻¹) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨hVne, hV2⟩ := zpowers_ne_bot_and_isPGroup_two hz
  have hxN : x ∈ normalizer ((zpowers z : Subgroup S) : Set S) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_left (show Commute z x from hxz.symm) k).eq
  refine ⟨zpowers z, hVne, hV2, ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact Or.inr ⟨x, hxN, hx, isConj_iff.2 ⟨b, hb⟩⟩
  · refine Or.inl ⟨p, hp, ?_, ?_⟩
    · have := hp.two_le
      omega
    · have h := orderOf_dvd_natCard (⟨x, hxN⟩ : normalizer ((zpowers z : Subgroup S) : Set S))
      rwa [orderOf_mk, hx] at h

theorem exists_quotient_witness_of_oddChevalley {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : ChevalleyExceptionalModel S t p f) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨x, z, b, hx, hz, hxz, hb, -⟩ :=
    odd_Chevalley_exceptional_real_root_element_centralizing_involution S hp hp2 f t h
  exact exists_quotient_witness_of_real hp hp2 hx hz hxz hb

theorem exists_quotient_witness_of_evenChevalley {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} {f : ℕ} (h : ChevalleyExceptionalModel S t 2 f) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨x, z, b, hx, hz, hxz, hb, -⟩ :=
    even_Chevalley_exceptional_real_three_element_centralizing_involution S t f h
  exact exists_quotient_witness_of_real Nat.prime_three (by norm_num) hx hz hxz hb

variable {G : Type} [Group G] [Finite G]

theorem theta_free_Suzuki_small_Ree_component_normalization_at_three
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      (SuzukiModel (L ⧸ center L) p f ∨ ReeTitsModel (L ⧸ center L) .twistedG2 p f) →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ p f : ℕ,
      (SuzukiModel (L ⧸ center L) p f ∨ ReeTitsModel (L ⧸ center L) .twistedG2 p f) →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      (SuzukiModel (L ⧸ center L) p f ∨ ReeTitsModel (L ⧸ center L) .twistedG2 p f) →
      A ≤ normalizer (L : Set G) := by
    intro L hL p f hmodel
    refine normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ => ?_
    rcases hmodel with h | h
    · exact exists_quotient_witness_of_suzukiModel h
    · exact exists_quotient_witness_of_smallReeModel h
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

theorem theta_free_large_Ree_Tits_component_normalization_at_three
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (p f : ℕ), (t = .twistedF4 ∨ t = .Tits) →
      ReeTitsModel (L ⧸ center L) t p f → A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ (t : StatedLieTag) (p f : ℕ),
      (t = .twistedF4 ∨ t = .Tits) → ReeTitsModel (L ⧸ center L) t p f →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (p f : ℕ),
      (t = .twistedF4 ∨ t = .Tits) → ReeTitsModel (L ⧸ center L) t p f →
      A ≤ normalizer (L : Set G) := by
    intro L hL t p f ht hmodel
    have : Group.IsPerfect L := hL.1
    refine normalizes_of_center_eq_bot hθ he hq h3 hA hL fun hZ3 => ?_
    obtain ⟨n, hn⟩ := hZ3.exists_card_eq
    exact center_eq_bot_of_largeReeTitsModel (by rw [hn]; exact Odd.pow (by decide)) ht hmodel
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

theorem theta_free_odd_Chevalley_exceptional_component_normalization_at_three
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (p f : ℕ), p.Prime → p ≠ 2 →
      ChevalleyExceptionalModel (L ⧸ center L) t p f → A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ (t : StatedLieTag) (p f : ℕ), p.Prime → p ≠ 2 →
      ChevalleyExceptionalModel (L ⧸ center L) t p f → A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (p f : ℕ), p.Prime → p ≠ 2 →
      ChevalleyExceptionalModel (L ⧸ center L) t p f → A ≤ normalizer (L : Set G) :=
    fun L hL t p f hp hp2 hmodel => normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ =>
      exists_quotient_witness_of_oddChevalley hp hp2 hmodel
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

theorem theta_free_even_Chevalley_exceptional_component_normalization_at_three
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (f : ℕ),
      ChevalleyExceptionalModel (L ⧸ center L) t 2 f → A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ (t : StatedLieTag) (f : ℕ),
      ChevalleyExceptionalModel (L ⧸ center L) t 2 f → A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ (t : StatedLieTag) (f : ℕ),
      ChevalleyExceptionalModel (L ⧸ center L) t 2 f → A ≤ normalizer (L : Set G) :=
    fun L hL t f hmodel => normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ =>
      exists_quotient_witness_of_evenChevalley hmodel
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

end CFSG.RankThree.Chevalley

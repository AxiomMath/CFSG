module

public import CFSG.RankThree.PartTwo.KFacts.KS44Sz
public import CFSG.Open.SignalizerFunctorDefs
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22K108FieldSz
import CFSG.RankThree.S4Free.Stellmacher24Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

section Automorphisms

variable {a : ℕ} {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem fixed_sup_sylow_eq_top_of_pow_three_of_suzuki [Finite X]
    (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) (ψ : X ≃* CFSG.Blueprint.suzukiGroup a F)
    (h3 : ¬ 3 ∣ Nat.card X) {α : MulAut X} (hα : α ^ 3 = 1) (T : Sylow 2 X) :
    CFSG.Open.signalizerFixedSubgroup α ⊔ (T : Subgroup X) = ⊤ := by
  by_cases hα1 : α = 1
  · subst hα1
    exact eq_top_iff.2 fun x _ => mem_sup_left (show (1 : MulAut X) x = x from rfl)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf α = 3 := orderOf_eq_prime hα hα1
    refine UC22.k108FieldSz_fixed_sup_sylow_eq_top_of_mulEquiv ha hF ψ Nat.prime_three
      (by norm_num) ⟨hord, fun g hg => h3 ?_⟩ T
    have hdvd := orderOf_map_dvd (MulAut.conj : X →* MulAut X) g
    rw [← hg, hord] at hdvd
    exact hdvd.trans (orderOf_dvd_natCard g)

end Automorphisms

section Involutions

variable {a : ℕ} {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] {K V : Subgroup Y}

private theorem r1sz_sq_eq_one (hZ : center ↥K = ⊥) (hVN : V ≤ normalizer (K : Set Y))
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) {g : ↥K}
    (hg : MulAut.conj g ∈ (K.normalizerMonoidHom.comp (inclusion hVN)).range) : g ^ 2 = 1 := by
  obtain ⟨v, hv⟩ := hg
  have hv2 : v ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hV2 v v.2)
  have h1 : MulAut.conj (g ^ 2) = 1 := by rw [map_pow, ← hv, ← map_pow, hv2, map_one]
  have h2 : g ^ 2 ∈ center ↥K := mem_center_iff.2 fun y => by
    have h3 := congrArg (fun σ : MulAut ↥K => σ y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * g ^ 2 = g ^ 2 * y * (g ^ 2)⁻¹ * g ^ 2 := by rw [h3]
      _ = g ^ 2 * y := by group
  rwa [hZ, mem_bot] at h2

theorem exists_sylow_commute_of_suzuki (ha : 1 ≤ a)
    (hF : Nat.card F = 2 ^ (2 * a + 1)) (ψ : ↥K ≃* CFSG.Blueprint.suzukiGroup a F)
    (hZ : center ↥K = ⊥) (hVN : V ≤ normalizer (K : Set Y)) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ T : Sylow 2 ↥K, ∀ t ∈ (T : Subgroup ↥K), ∀ v ∈ V, v * (t : Y) = t * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥V →* MulAut ↥K := K.normalizerMonoidHom.comp (inclusion hVN)
  let V₀ : Subgroup ↥K := ρ.range.comap (MulAut.conj : ↥K →* MulAut ↥K)
  have hV₀2 : IsPGroup 2 V₀ := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact r1sz_sq_eq_one hZ hVN hV2 g.2)⟩
  obtain ⟨T, hT⟩ := hV₀2.exists_le_sylow
  refine ⟨T, fun t ht v hv => ?_⟩
  have hρ2 : ρ ⟨v, hv⟩ ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← map_pow,
      show (⟨v, hv⟩ : ↥V) ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hV2 v hv),
      map_one]
  obtain ⟨g, hg⟩ := CFSG.RankThree.S4Free.Suzuki.exists_conj_of_pow_eq_one ha hF ψ hρ2
  have hgV₀ : g ∈ V₀ := ⟨⟨v, hv⟩, hg⟩
  have hgc := CFSG.RankThree.S4Free.Suzuki.mem_centralizer_of_sq_eq_one hF ψ T (hT hgV₀)
    (r1sz_sq_eq_one hZ hVN hV2 hgV₀)
  have htg : t * g = g * t := mem_centralizer_iff.1 hgc t ht
  have h1 : ρ ⟨v, hv⟩ t = t := by rw [hg, MulAut.conj_apply, ← htg, mul_inv_cancel_right]
  have h2 : (v * t * v⁻¹ : Y) = t := congrArg Subtype.val h1
  calc v * (t : Y) = v * t * v⁻¹ * v := by group
    _ = t * v := by rw [h2]

end Involutions

section Main


theorem center_eq_bot_and_suzukiModel_of_not_three_dvd {K : Type} [Group K] [Finite K]
    (hKq : CFSG.Open.IsQuasisimple K) (hKK : CFSG.Open.IsKGroup K)
    (hZ : Odd (Nat.card (center K))) (h3 : ¬ 3 ∣ Nat.card K) :
    center K = ⊥ ∧ ∃ f : ℕ, CFSG.Blueprint.SuzukiModel K 2 f := by
  have : Group.IsPerfect K := ⟨hKq.1⟩
  have : IsSimpleGroup (K ⧸ center K) := hKq.2
  have hnab : ∃ x y : K ⧸ center K, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (K ⧸ center K) ⟨⟨h⟩⟩
  obtain ⟨f, -, a, ha, F, _, _, rfl, hF, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.KFacts.kpSz (K ⧸ center K) hnab
      ((hKK.quotient (center K)).isCatalogGroup_of_surjective ⊤ hnab
        (Subgroup.topEquiv (G := K ⧸ center K)).toMonoidHom Subgroup.topEquiv.surjective)
      (fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card _)))
  let φ' := φ.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hF)
  let π := φ'.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : π.ker = center K := CFSG.SectionRank.center_eq_ker_of_mulEquiv φ'
  have hbot := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π
    (φ'.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (hker ▸ hZ)
  rw [hker] at hbot
  exact ⟨hbot, 2 * a + 1, rfl, a, ha, F, inferInstance, inferInstance, rfl, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans φ⟩⟩

theorem k_19_26_rankOne_of_not_three_dvd {Y : Type} [Group Y] [Finite Y] (K V : Subgroup Y) (e : Y)
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKK : CFSG.Open.IsKGroup ↥K)
    (hZ : Odd (Nat.card (Subgroup.center ↥K))) (hV2 : CFSG.Open.IsElemAbelian 2 V)
    (hVN : V ≤ normalizer (K : Set Y)) (he : orderOf e = 3) (heN : e ∈ normalizer (K : Set Y))
    (h3 : ¬ 3 ∣ Nat.card K) :
    K ≤ (K ⊓ centralizer ({e} : Set Y)) ⊔ (K ⊓ centralizer (V : Set Y)) := by
  obtain ⟨hZ1, f, -, a, ha, F, _, _, rfl, hF, ⟨ψ⟩⟩ :=
    center_eq_bot_and_suzukiModel_of_not_three_dvd hKq hKK hZ h3
  obtain ⟨T, hT⟩ := exists_sylow_commute_of_suzuki ha hF ψ hZ1 hVN hV2.2
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨e, heN⟩ with hα
  have he3 : (⟨e, heN⟩ : normalizer (K : Set Y)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact he ▸ pow_orderOf_eq_one e)
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, he3, map_one]
  have hgen := fixed_sup_sylow_eq_top_of_pow_three_of_suzuki ha hF ψ h3 hα3 T
  have hA : (CFSG.Open.signalizerFixedSubgroup α).map K.subtype ≤
      K ⊓ centralizer ({e} : Set Y) := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (e * k * e⁻¹ : Y) = k := congrArg Subtype.val hk
    calc (k : Y) * e = e * k * e⁻¹ * e := by rw [h1]
      _ = e * k := by group
  have hB : (T : Subgroup ↥K).map K.subtype ≤ K ⊓ centralizer (V : Set Y) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t.2, mem_centralizer_iff.2 fun v hv => hT t ht v hv⟩
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥K) ∈ CFSG.Open.signalizerFixedSubgroup α ⊔ (T : Subgroup ↥K) :=
    hgen ▸ mem_top _
  have hmap := mem_map_of_mem K.subtype hx'
  rw [Subgroup.map_sup] at hmap
  exact sup_le_sup hA hB hmap

end Main

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

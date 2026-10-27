module

public import CFSG.RankThree.PartTwo.Sec8.Standing
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Tools
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

open CFSG.Goldschmidt.G310 in
theorem not_three_dvd_card_sylow_two {R : Type*} [Group R] [Finite R] (Θ : Subgroup R)
    [Θ.Normal] (hΘ : ¬ 3 ∣ Nat.card Θ)
    (hc : ∀ s r : R, (∃ j : ℕ, s ^ 3 ^ j = 1) → s * r * s⁻¹ * r⁻¹ ∈ Θ) :
    ¬ 3 ∣ Nat.card (Sylow 2 R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 R := Classical.arbitrary _
  let P₀ : Sylow 2 R := Classical.arbitrary _
  set W : Subgroup R := (P₀ : Subgroup R) ⊔ Θ with hW
  have hW3 : ¬ 3 ∣ Nat.card W :=
    Sec6.not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) P₀.isPGroup'
      Subgroup.le_normalizer_of_normal hΘ
  have hSW : (S : Subgroup R) ≤ Subgroup.normalizer (W : Set R) := by
    refine Sec6.le_normalizer_sup_of_conj (fun a ha x hx => ?_) (fun a ha x hx => ?_)
    · have h1 : a * x * a⁻¹ * x⁻¹ ∈ Θ := by
        rw [show a * x * a⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ from rfl]
        refine hc a x ?_
        obtain ⟨j, hj⟩ := S.isPGroup' ⟨a, ha⟩
        exact ⟨j, by simpa using congrArg Subtype.val hj⟩
      have h2 : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right (Subgroup.Normal.conj_mem inferInstance x hx a)
  obtain ⟨P', hfus, -, hSP'⟩ := exists_invariant_sylow_containing Nat.prime_three Nat.prime_two
    S.isPGroup' hW3 hSW bot_le IsPGroup.of_bot Subgroup.le_normalizer_of_normal
  obtain ⟨hP'W, hP'2, -⟩ := id hfus
  obtain ⟨Q, hQ⟩ := exists_sylow_of_fusionIsSylowIn hfus
  have h1 : ¬ 2 ∣ P'.relIndex W := by
    have h := Q.not_dvd_index
    have : P'.subgroupOf W = (Q : Subgroup W) := by
      rw [← hQ]
      exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
    rwa [Subgroup.relIndex, this]
  have h2 : ¬ 2 ∣ W.index := fun h =>
    P₀.not_dvd_index (h.trans (Subgroup.index_dvd_of_le (le_sup_left : (P₀ : Subgroup R) ≤ W)))
  have h3 : ¬ 2 ∣ P'.index := by
    rw [← Subgroup.relIndex_mul_index hP'W]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    exacts [h1 h, h2 h]
  let P'' : Sylow 2 R := hP'2.toSylow h3
  have hle : (S : Subgroup R) ≤ Subgroup.normalizer ((P'' : Subgroup R) : Set R) := hSP'
  rw [Sylow.card_eq_index_normalizer P'']
  intro hdvd
  exact S.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))

theorem u38_two_elt_mem (hloc : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3)
    {A Y I : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : Nat.card A = 81)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hAI : A ≤ Subgroup.normalizer (I : Set G))
    (hIY : I ≤ Subgroup.normalizer (Y : Set G))
    (hI : I ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)
    (hS3 : ∀ i ∈ I, (∃ j : ℕ, i ^ 3 ^ j ∈ Y) → i ∈ Y)
    {t : G} (htI : t ∈ I) (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) : t ∈ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra htY
  obtain ⟨k, hk⟩ := ht2
  set Θ : Subgroup G := inSubgroup (aschbacherSolvableCore 3) Y with hΘ
  set Cy : Subgroup G := Sec4.thetaQuotCentralizer Y with hCy
  have hCyN : Cy ≤ Subgroup.normalizer (Y : Set G) := Sec6.thetaQuotCentralizer_le_normalizer Y
  have hNΘ : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (Θ : Set G) :=
    Sec6.normalizer_le_normalizer_theta Y
  have hΘY : Θ ≤ Y := Sec6.theta_le Y
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore Y
  have ht' : t ∈ (Y : Set G) * (Cy : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y Cy hCyN]
    exact hI htI
  obtain ⟨y, hy, c, hc, hyc⟩ := ht'
  have hcdef : c = y⁻¹ * t := by rw [← hyc]; group
  set R : Subgroup G := Cy ⊓ (I ⊔ Y) with hR
  have hcR : c ∈ R := Subgroup.mem_inf.mpr ⟨hc, by
    rw [hcdef]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Y.inv_mem hy)) (Subgroup.mem_sup_left htI)⟩
  have hRCy : R ≤ Cy := inf_le_left
  have hRN : R ≤ Subgroup.normalizer (Y : Set G) := hRCy.trans hCyN
  have hΘR : Θ ≤ R := le_inf (Sec6.theta_le_thetaQuotCentralizer Y) (hΘY.trans le_sup_right)
  have hAsup : A ≤ Subgroup.normalizer ((I ⊔ Y : Subgroup G) : Set G) :=
    Sec6.le_normalizer_sup_of_conj
      (fun a ha z hz => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hAI ha) z).mp hz))
      (fun a ha z hz => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hAY ha) z).mp hz))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    refine HeringU38.le_normalizer_of_conj_mem fun g hg x hx => ?_
    obtain ⟨hxC, hxIY⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨Sec6.conj_mem_thetaQuotCentralizer hxC (hAY hg),
      (Subgroup.mem_normalizer_iff.mp (hAsup hg) x).mp hxIY⟩
  have h3R : ∀ r ∈ R, (∃ j : ℕ, r ^ 3 ^ j = 1) → r ∈ Y := by
    rintro r hr ⟨j, hj⟩
    have hrIY : r ∈ (I : Set G) * (Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right I Y hIY]
      exact (Subgroup.mem_inf.mp hr).2
    obtain ⟨i, hi, y', hy', hry⟩ := hrIY
    have hrN : r ∈ Subgroup.normalizer (Y : Set G) := hRN hr
    have hiY : i ∈ Y := by
      refine hS3 i hi ⟨j, ?_⟩
      have hn : r * y'⁻¹ * r⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hrN _).mp (Y.inv_mem hy')
      obtain ⟨n', hn', h⟩ := HeringU38.pow_mul_mem Y hrN hn (3 ^ j)
      have hi' : i = (r * y'⁻¹ * r⁻¹) * r := by rw [← hry]; group
      rw [hi', h, hj, mul_one]
      exact hn'
    rw [← hry]
    exact Subgroup.mul_mem _ hiY hy'
  have hc3 : ∀ s r : R, (∃ j : ℕ, s ^ 3 ^ j = 1) → s * r * s⁻¹ * r⁻¹ ∈ Θ.subgroupOf R := by
    rintro s r ⟨j, hj⟩
    have hsY : (s : G) ∈ Y := h3R s s.2 ⟨j, by simpa using congrArg Subtype.val hj⟩
    have hrC : (r : G) ∈ Cy := hRCy r.2
    have := (Sec6.mem_thetaQuotCentralizer_iff.mp hrC).2 ((s : G)⁻¹) (Y.inv_mem hsY)
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using this
  haveI : (Θ.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΘR).mpr (hRN.trans hNΘ)
  have hΘ3' : ¬ 3 ∣ Nat.card (Θ.subgroupOf R) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘR).toEquiv]
  have hcard := not_three_dvd_card_sylow_two (R := ↥R) (Θ.subgroupOf R) hΘ3' hc3
  let φ : A →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hAR)
  let _ : MulDistribMulAction A R := MulDistribMulAction.compHom R φ
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  obtain ⟨P, hP⟩ := hAp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 R) hcard
  have hPinv : ∀ e : A, ∀ s ∈ (P : Subgroup R), e • s ∈ (P : Subgroup R) := by
    intro e s hs
    have hmem : e • s ∈ ((e • P : Sylow 2 R) : Subgroup R) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hP e] at hmem
  set PG : Subgroup G := (P : Subgroup R).map R.subtype with hPG
  have hconjPG : ∀ e ∈ A, ∀ z ∈ PG, e * z * e⁻¹ ∈ PG := by
    rintro e he _ ⟨s, hs, rfl⟩
    exact ⟨_, hPinv ⟨e, he⟩ s hs, rfl⟩
  have hPG2 : IsPGroup 2 PG := P.isPGroup'.map R.subtype
  have hPGΘ : PG ≤ Subgroup.normalizer (Θ : Set G) :=
    (Subgroup.map_subtype_le _).trans (hRN.trans hNΘ)
  have hX3 : ¬ 3 ∣ Nat.card (PG ⊔ Θ : Subgroup G) :=
    Sec6.not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hPG2 hPGΘ hΘ3
  have hAX : A ≤ Subgroup.normalizer ((PG ⊔ Θ : Subgroup G) : Set G) :=
    Sec6.le_normalizer_sup_of_conj
      (fun a ha z hz => Subgroup.mem_sup_left (hconjPG a ha z hz))
      (fun a ha z hz => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hNΘ (hAY ha)) z).mp hz))
  have hodd := odd_card_of_le_normalizer hloc hAe hA81 hX3 hAX
  have hPGodd : Odd (Nat.card PG) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le le_sup_left)
  have hc2k : c ^ 2 ^ k ∈ Y := by
    obtain ⟨n', hn', h⟩ := HeringU38.pow_mul_mem Y (hIY htI) (Y.inv_mem hy) (2 ^ k)
    rw [hcdef, h, hk, mul_one]
    exact hn'
  have hcY : c ∉ Y := fun hcY => htY (by rw [← hyc]; exact Subgroup.mul_mem _ hy hcY)
  have hceven : ¬ Odd (orderOf c) := by
    intro hodd'
    have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
      Nat.Coprime.pow_left k hodd'.coprime_two_right.symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    apply hcY
    rw [← hm]
    exact Subgroup.pow_mem _ hc2k m
  have h2R : 2 ∣ Nat.card R := by
    have h1 : orderOf c ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨c, hcR⟩ : R)
      rwa [← Subgroup.orderOf_coe] at this
    have h2 : 2 ∣ orderOf c := by
      rcases Nat.even_or_odd (orderOf c) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hceven
    exact h2.trans h1
  have hfac : 0 < (Nat.card R).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2R
  have hPcard : Nat.card P = 2 ^ (Nat.card R).factorization 2 := Sylow.card_eq_multiplicity P
  have hPGcard : Nat.card PG = Nat.card P := by
    rw [hPG, Subgroup.card_map_of_injective R.subtype_injective]
  rw [hPGcard, hPcard] at hPGodd
  exact (Nat.not_even_iff_odd.mpr hPGodd) (Nat.even_pow.mpr ⟨even_two, hfac.ne'⟩)

end CFSG.RankThree.PartTwo.Sec8

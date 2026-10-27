module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Odd
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4cProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type} [Group G] [Finite G]

theorem faithful (hbig : NoBig3 G) {A L' Q : Subgroup G} {y d : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : 27 < Nat.card A)
    (hAL : A ≤ Subgroup.normalizer (L' : Set G)) (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (L' : Set G)) (hyQ : ∀ q ∈ Q, y * q = q * y)
    (hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hyA : y ∈ A) (hdA : d ∈ A)
    (hdec : A ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ (A ⊓ L')) :
    ∀ q ∈ Q, ∀ hq : q ∈ Subgroup.normalizer (L' : Set G),
      Sec12.thetaBarAct L' ⟨q, hq⟩ = 1 → q = 1 := by
  intro q hqQ hq hact
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L'
  set CL : Subgroup G := Sec4.thetaQuotCentralizer L'
  set Q₀ : Subgroup G := Q ⊓ CL
  set M : Subgroup G := Q₀ ⊔ T
  have hNT : Subgroup.normalizer (L' : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Sec6.normalizer_le_normalizer_theta L'
  have hQ₀2 : IsPGroup 2 Q₀ :=
    hQ2.of_injective (Subgroup.inclusion (inf_le_left : Q₀ ≤ Q)) (Subgroup.inclusion_injective _)
  have hQ₀N : Q₀ ≤ Subgroup.normalizer (T : Set G) :=
    (inf_le_left : Q₀ ≤ Q).trans (hQN.trans hNT)
  have hM3 : ¬ 3 ∣ Nat.card M :=
    Sec6.not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hQ₀2 hQ₀N
      (Sec11.not_three_dvd_card_inSubgroup_theta L')
  have hconj : ∀ g : G, (∀ x ∈ Q₀, g * x * g⁻¹ ∈ M) → (∀ t ∈ T, g * t * g⁻¹ ∈ M) →
      g ∈ Subgroup.normalizer (M : Set G) := by
    intro g hQg hTg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hmap : (Q₀ ⊔ T).map (MulAut.conj g).toMonoidHom ≤ Q₀ ⊔ T := by
      rw [Subgroup.map_sup, sup_le_iff]
      constructor
      · rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        exact hQg x hx
      · rw [Subgroup.map_le_iff_le_comap]
        intro t ht
        exact hTg t ht
    exact hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (show n ∈ M from hn))
  have hyM : y ∈ Subgroup.normalizer (M : Set G) := by
    refine hconj y (fun x hx => ?_) (fun t ht => ?_)
    · have hyx : y * x * y⁻¹ = x := by
        rw [hyQ x (Subgroup.mem_inf.mp hx).1, mul_inv_cancel_right]
      rw [hyx]
      exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNT (hAL hyA)) t).mp ht)
  have hdM : d ∈ Subgroup.normalizer (M : Set G) := by
    refine hconj d (fun x hx => ?_) (fun t ht => ?_)
    · have hdx : d * x * d⁻¹ ∈ Q₀ :=
        Subgroup.mem_inf.mpr ⟨hdQ x (Subgroup.mem_inf.mp hx).1,
          Sec12.conj_mem_thetaQuotCentralizer (hAL hdA) (Subgroup.mem_inf.mp hx).2⟩
      exact Subgroup.mem_sup_left hdx
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNT (hAL hdA)) t).mp ht)
  have hℓM : ∀ ℓ ∈ L', ℓ ∈ Subgroup.normalizer (M : Set G) := by
    intro ℓ hℓ
    refine hconj ℓ (fun x hx => ?_) (fun t ht => ?_)
    · have hcrit := (Sec6.mem_thetaQuotCentralizer_iff.mp (Subgroup.mem_inf.mp hx).2).2 ℓ⁻¹
        (L'.inv_mem hℓ)
      rw [inv_inv] at hcrit
      have hfac : ℓ * x * ℓ⁻¹ = (ℓ * (x * ℓ⁻¹ * x⁻¹)) * x := by group
      rw [hfac]
      exact mul_mem (Subgroup.mem_sup_right hcrit) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L' hℓ) t).mp ht)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := by
    refine hdec.trans (sup_le (sup_le (Subgroup.zpowers_le.mpr hyM)
      (Subgroup.zpowers_le.mpr hdM)) ?_)
    intro a ha
    exact hℓM a (Subgroup.mem_inf.mp ha).2
  have hQ₀bot : Q₀ = ⊥ :=
    eq_bot_of_two_subgroup_of_normalized hbig hA hA81 hM3 hAM (le_sup_left : Q₀ ≤ M) hQ₀2
  have hqQ₀ : q ∈ Q₀ :=
    Subgroup.mem_inf.mpr ⟨hqQ, (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hq).mpr hact⟩
  rw [hQ₀bot, Subgroup.mem_bot] at hqQ₀
  exact hqQ₀

end CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4cProof

end

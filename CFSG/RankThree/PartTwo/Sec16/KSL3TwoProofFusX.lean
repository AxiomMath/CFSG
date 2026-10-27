module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFusX
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

namespace ProofKSL3Two

theorem eq_sup_zpowers_of_card_nine {X : Type*} [Group X] {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {e₁ e₂ : X} (he₁E : e₁ ∈ E)
    (he₁1 : e₁ ≠ 1) (he₂E : e₂ ∈ E) (he₂ : e₂ ∉ Subgroup.zpowers e₁) :
    E = Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  set H := Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ with hH
  have hHE : H ≤ E := sup_le (Subgroup.zpowers_le.mpr he₁E) (Subgroup.zpowers_le.mpr he₂E)
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHE)
  have h3 : Nat.card (Subgroup.zpowers e₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE.2 e₁ he₁E) he₁1
  have hdvd : Nat.card H ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hHE
  have h1H : Subgroup.zpowers e₁ ≤ H := le_sup_left
  have hgt : 3 < Nat.card H := by
    by_contra hle
    push Not at hle
    have heq : Subgroup.zpowers e₁ = H := Subgroup.eq_of_le_of_card_ge h1H (by rw [h3]; exact hle)
    exact he₂ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e₂))
  have h9 : Nat.card H = 9 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card H ∣ 3 ^ 2 from hdvd)
    interval_cases k <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [h9, hE9])).symm

end ProofKSL3Two

open ProofKSL3Two ProofHess in
theorem kS1617FusX : KS1617FusX := by
  intro X _ _ n hn hn3 hiso D hD hD9 y hy hy1 z hz hz1
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hn hiso
  have h9K := not_nine_dvd_card_sub_one hK (not_two_pow_mod_nine hn3)
  obtain ⟨e₁, he₁D, he₁1, e₂, he₂D, he₂⟩ := exists_two_of_card_nine hD hD9
  have hDeq := eq_sup_zpowers_of_card_nine hD hD9 he₁D he₁1 he₂D he₂
  set ψ : X →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (2 ^ n) K)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  obtain ⟨y₁, hy₁S, hy₁⟩ := (φ e₁).2
  obtain ⟨y₂, hy₂S, hy₂⟩ := (φ e₂).2
  have hψ₁ : ψ e₁ = ProjGenLinGroup.mk y₁ := hy₁.symm
  have hψ₂ : ψ e₂ = ProjGenLinGroup.mk y₂ := hy₂.symm
  have h₁3 : ProjGenLinGroup.mk y₁ ^ 3 = 1 := by rw [← hψ₁, ← map_pow, hD.2 e₁ he₁D, map_one]
  have h₂3 : ProjGenLinGroup.mk y₂ ^ 3 = 1 := by rw [← hψ₂, ← map_pow, hD.2 e₂ he₂D, map_one]
  have h₁1 : ProjGenLinGroup.mk y₁ ≠ 1 := by
    rw [← hψ₁]
    exact fun h => he₁1 (hψinj (by rw [h, map_one]))
  have hcomm : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨e₁, he₁D⟩ ⟨e₂, he₂D⟩)
  have hcomm_bar : ProjGenLinGroup.mk y₁ * ProjGenLinGroup.mk y₂ =
      ProjGenLinGroup.mk y₂ * ProjGenLinGroup.mk y₁ := by
    rw [← hψ₁, ← hψ₂, ← map_mul, ← map_mul, hcomm]
  have he₂' : ProjGenLinGroup.mk y₂ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₁) := by
    rintro ⟨k, hk⟩
    apply he₂
    refine ⟨k, hψinj ?_⟩
    simp only at hk ⊢
    rw [map_zpow, hψ₁, hψ₂, hk]
  have h1 := type1_of_lift hK hq h9K hy₁S h₁3 h₁1
  obtain ⟨ζ, hζ1, hζ⟩ := exists_heis_scalar hK hq h9K hy₁S hy₂S h₁3 h₂3 h₁1 hcomm_bar he₂'
  set e : (⊤ : Subgroup X) ≃* projImage (slPi π 3 (2 ^ n) K) := Subgroup.topEquiv.trans φ with he
  have key := transitive_of_heis_pair hK hq e (x₁ := e₁) (x₂ := e₂) (Subgroup.mem_top _)
    (Subgroup.mem_top _) (y₁ := y₁) (y₂ := y₂) hy₁.symm hy₂.symm h1 hy₂S hζ1 hζ
  rw [← hDeq] at key
  obtain ⟨m, hm, hmyz⟩ := key y hy hy1 z hz hz1
  exact ⟨m, hm.2, hmyz⟩

theorem ks1617Fus_proved : KS1617Fus :=
  ks1617Fus_of kS1617FusX

end CFSG.RankThree.PartTwo.Sec16

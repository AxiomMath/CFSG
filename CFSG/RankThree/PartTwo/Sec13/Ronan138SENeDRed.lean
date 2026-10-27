module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SENeD
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SInnerRes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def Step138ENeDTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → Subgroup.zpowers ⁅x, y⁆ ∈ omegaA E →
    ∀ K : Subgroup G, K ∈ lA E ⁅x, y⁆ → ⁅x, y⁆ ∉ K → E ⊓ K = Subgroup.zpowers c →
      F ≤ Subgroup.normalizer (K : Set G) → t ∈ Subgroup.normalizer (K : Set G) →
      Sec8.IsZ3PGLThreePi (lBarA ⁅x, y⁆ K E) →
      Nonempty (Sec4.autIn K E ≃* Multiplicative (ZMod 3)) →
      (∃ x₀ ∈ E, Sec4.InducesTypeOn K x₀ 3) → False

@[expose] def Step138ENeDSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → Subgroup.zpowers ⁅x, y⁆ ∈ omegaA E →
    ∀ K : Subgroup G, K ∈ lA E ⁅x, y⁆ → ⁅x, y⁆ ∈ K →
      (Sec4.IsSLThreePiTwo (lBarA ⁅x, y⁆ K E) ∨
        (Sec4.IsHeisCentral (lBarA ⁅x, y⁆ K E) (K ⧸ aschbacherSolvableCore 3 K) ∧
          Subgroup.normalizer (E : Set G) ≤
            Subgroup.normalizer (Subgroup.zpowers ⁅x, y⁆ : Set G))) → False

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem autIn_eq_bot_of_inf_eq_bot {E K : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (K : Set G)) (h : E ⊓ K = ⊥) : Sec4.autIn K E = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  obtain ⟨k, hkN, hkK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun e => Subtype.ext ?_
  rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
  have h1 : (e : G) * k * (e : G)⁻¹ * k⁻¹ ∈ E ⊓ K := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hkN (e : G)⁻¹).mp (inv_mem e.2)
      rw [show (e : G) * k * (e : G)⁻¹ * k⁻¹ = e * (k * (e : G)⁻¹ * k⁻¹) by group]
      exact mul_mem e.2 this
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hEN e.2) k).mp hkK) (inv_mem hkK)
  rw [h, Subgroup.mem_bot] at h1
  calc k * (e : G) * k⁻¹ = ((e : G) * k * (e : G)⁻¹ * k⁻¹)⁻¹ * e := by group
    _ = e := by rw [h1, inv_one, one_mul]

theorem inf_ne_bot_of_autIn {E K : Subgroup G} (hEN : E ≤ Subgroup.normalizer (K : Set G))
    (hAut : Nonempty (Sec4.autIn K E ≃* Multiplicative (ZMod 3))) : E ⊓ K ≠ ⊥ := by
  intro h0
  obtain ⟨φ⟩ := hAut
  have hc := Nat.card_congr φ.toEquiv
  rw [autIn_eq_bot_of_inf_eq_bot hEN h0, Subgroup.card_bot, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] at hc
  norm_num at hc

theorem false_of_card_inf_nine {A L E F : Subgroup G} {c x y t : G}
    (hfr : Frame138Base A L E F c x y t) {K : Subgroup G} (hK : K ∈ lA E ⁅x, y⁆)
    (hdK : ⁅x, y⁆ ∉ K) (h9 : Nat.card (E ⊓ K : Subgroup G) = 9) : False := by
  have hne : E ⊓ K ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h9
    norm_num at h9
  rw [inf_eq_zpowers_of_not_mem hfr hK hne hdK, card_zpowers_of_pow_three hfr.hc3 hfr.hc1] at h9
  norm_num at h9

theorem step138ENeDBase_of (h131 : Item131) (hspor : SporadicModels131)
    (hsetAt : Item13SetupAt) (hTwo : Step138ENeDTwo) (hSeven : Step138ENeDSeven) :
    Step138ENeDBase := by
  intro G _ _ A c L E F x y t hfr hΩ
  have h := hfr.hH.1
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  obtain ⟨K, hK⟩ := hsetAt G h.toPartTwoStanding h.partTwoS_eq E hXF.1 hXF.2 _ hΩ
  have hD : Sec13Data G E ⁅x, y⁆ K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := hΩ
      mem_lA := hK }
  rcases cases131 h131 hspor slTwoCenter hD with
    ⟨hdK, h9, -, -⟩ | ⟨hdK, h9, -, -⟩ | ⟨hdK, hPGLK, hAut, hx₀⟩ | ⟨hdK, h7⟩
  · exact false_of_card_inf_nine hfr hK hdK h9
  · exact false_of_card_inf_nine hfr hK hdK h9
  · have hne := inf_ne_bot_of_autIn hK.2.1 hAut
    have hEKc := inf_eq_zpowers_of_not_mem hfr hK hne hdK
    have hEKd : ¬ E ⊓ K ≤ Subgroup.zpowers ⁅x, y⁆ := by
      intro hle
      apply hne
      rw [eq_bot_iff, ← zpowers_inf_eq_bot hfr.hd3 hdK]
      exact le_inf hle inf_le_right
    obtain ⟨hFK, htK⟩ := normalizer_of_mem_lA_d hfr hK hEKd
    exact hTwo G A c L E F x y t hfr hΩ K hK hdK hEKc hFK htK hPGLK hAut hx₀
  · exact hSeven G A c L E F x y t hfr hΩ K hK hdK h7

theorem step138ENeD_of (h131 : Item131) (hspor : SporadicModels131) (hsetAt : Item13SetupAt)
    (hTwo : Step138ENeDTwo) (hSeven : Step138ENeDSeven) : Step138ENeD := by
  intro G _ _ A c L E hH hPGL hΩ
  obtain ⟨F, hF⟩ := item138ExistsN G A c L E hH
  obtain ⟨x, y, t, hfr⟩ := exists_frame138_t hH hF hPGL
  rw [hfr.hEL] at hΩ
  exact step138ENeDBase_of h131 hspor hsetAt hTwo hSeven G A c L E F x y t hfr.toBase hΩ

end CFSG.RankThree.PartTwo.Sec13.Ronan138S

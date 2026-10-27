module

public import CFSG.Quasithin.Background.C48SporSetup
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem commutator_eq_of_isComponentOf {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    ⁅K, K⁆ = K := by
  have h := hK.2.2.1
  rw [_root_.commutator_def] at h
  have := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

theorem isSimpleGroup_kStar {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    IsSimpleGroup ↥(img (sporN H K) K) :=
  have := hK.2.2.2
  MulEquiv.isSimpleGroup (kStarEquiv (K_le_sporX hK.1)).symm

theorem commutator_kStar {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    commutator ↥(img (sporN H K) K) = ⊤ := by
  have hKX := K_le_sporX (H := H) hK.1
  have himg : ⁅img (sporN H K) K, img (sporN H K) K⁆ = img (sporN H K) K := by
    rw [← img_commutator hKX hKX, commutator_eq_of_isComponentOf hK]
  rw [_root_.commutator_def]
  apply Subgroup.map_injective (img (sporN H K) K).subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, himg]

theorem eq_bot_of_normal_of_isPGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) {P : Subgroup S} (hP : P.Normal) (hP2 : IsPGroup 2 ↥P) :
    P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    have hS : IsPGroup 2 S := by
      rw [h] at hP2
      exact hP2.of_equiv Subgroup.topEquiv
    have hnt : Nontrivial S := IsSimpleGroup.toNontrivial
    have hZ := hS.center_nontrivial
    have hZtop : Subgroup.center S = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
      · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hZ
        rw [h', Subgroup.mem_bot] at ha hb
        exact absurd (Subtype.ext (ha.trans hb.symm)) hab
      · exact h'
    have hcomm : commutator S = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (hZtop ▸ Subgroup.mem_top x) y
    obtain ⟨a, b, hab⟩ := hnt
    apply hab
    have h1 : (⊤ : Subgroup S) = ⊥ := hperf.symm.trans hcomm
    have ha : a ∈ (⊥ : Subgroup S) := h1 ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup S) := h1 ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem not_isC134Case_two {A : Type} [Group A] [Finite A] {S R' : Subgroup A} (hSn : S.Normal)
    [IsSimpleGroup ↥S] (hperf : commutator ↥S = ⊤) : ¬ IsC134Case 2 (S ⊔ R') R' S := by
  rintro ⟨⟨n, F, hF, hFt, α, -, -, hsum⟩, -⟩
  obtain ⟨-, -, β, hβ, -, -⟩ := hsum
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (S ⊔ R') with hP
  have hSP : S ≤ Subgroup.normalizer (P : Set A) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (S ⊔ R'))
  have h1 : ⁅P, S⁆ ≤ S := Subgroup.commutator_le_right P S
  have h2 : ⁅P, S⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp s hs
    rw [commutatorElement_def]
    have : s * p⁻¹ * s⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hSP hs) _).mp (P.inv_mem hp)
    have := P.mul_mem hp this
    simpa [mul_assoc] using this
  have hPS : (P ⊓ S).subgroupOf S = ⊥ := by
    refine eq_bot_of_normal_of_isPGroup hperf ⟨fun x hx g => ?_⟩ ?_
    · rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hSP g.2) _).mp hx.1, ?_⟩
      exact S.mul_mem (S.mul_mem g.2 hx.2) (S.inv_mem g.2)
    · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (S ⊔ R')).to_le
        inf_le_left).comap_of_injective S.subtype S.subtype_injective
  have hQ : c134Q (S ⊔ R') S = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hq' : (⟨q, h1 hq⟩ : ↥S) ∈ (P ⊓ S).subgroupOf S := ⟨h2 hq, h1 hq⟩
    rw [hPS, Subgroup.mem_bot] at hq'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hq'
  obtain ⟨q, hq⟩ := hβ (Multiplicative.ofAdd (fun _ _ => (1 : F)))
  have hq1 : q = 1 := by
    apply Subtype.ext
    have := hQ.le q.2
    rw [Subgroup.mem_bot] at this
    exact this
  rw [hq1, map_one] at hq
  have := congrFun (congrFun (congrArg Multiplicative.toAdd hq) 0) 0
  simp at this

end CFSG.Quasithin.C48Spor

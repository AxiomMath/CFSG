module

public import CFSG.Sporadic.Co2Smith.GlClosure
public import CFSG.Sporadic.Co2Smith.GlEmbed
public import CFSG.Sporadic.Co2Smith.CGlobal
public import CFSG.RankThree.Co2.CentGold
public import CFSG.RankThree.Co2.C4

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3


theorem eq_top_of_centralizer_le {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz) {Gs : Subgroup G}
    (hH : centralizer ({z} : Set G) ≤ Gs) (hGs : Nonempty (Gs ≃* K)) : Gs = ⊤ := by
  have : IsSimpleGroup Gs :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 hGs.some
  have hcen : ∃ S : Sylow 2 K, z0 ∈ (S : Subgroup K) ∧
      ∀ s ∈ (S : Subgroup K), z0 * s = s * z0 := by
    obtain ⟨S, hS, hc⟩ := exists_sylow_two_z0
    exact ⟨S, hS, fun s hs => (hc s hs).symm⟩
  let z' : Gs := ⟨z, hH (mem_centralizer_singleton_iff.2 rfl)⟩
  have hz' : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz
  let hA : CFSG.RankThree.Co2.Co2CentHyp G :=
    CFSG.RankThree.Co2.Co2CentHyp.ofTwoCentral z hz z0 z0_ne_one hcen φ
  let hB : CFSG.RankThree.Co2.Co2CentHyp Gs :=
    CFSG.RankThree.Co2.Co2CentHyp.ofTwoCentral z' hz' z0 z0_ne_one hcen
      ((centralizerEquivOfLe (t := z') hH).trans φ)
  have hrG : ∀ c, ((hB.rG c : Gs) : G) = hA.rG c := fun c => rfl
  have hC : ∀ c, Nat.card (centralizer ({hB.rG c} : Set Gs)) =
      Nat.card (centralizer ({hA.rG c} : Set G)) → centralizer ({hA.rG c} : Set G) ≤ Gs := by
    intro c hc
    rw [← hrG]
    exact centralizer_le_of_natCard_eq (by rw [hrG]; exact hc)
  have h1 : centralizer ({hA.rG 1} : Set G) ≤ Gs := hC 1 (hB.card_IG.trans hA.card_IG.symm)
  have h8 : centralizer ({hA.rG 8} : Set G) ≤ Gs :=
    hC 8 (hB.card_centralizer_eight.trans hA.card_centralizer_eight.symm)
  have hcls : ∀ t ∈ Gs, orderOf t = 2 → (∃ h ∈ Gs, h * z * h⁻¹ = t) ∨
      (∃ h ∈ Gs, h * hA.rG 1 * h⁻¹ = t) ∨ ∃ h ∈ Gs, h * hA.rG 8 * h⁻¹ = t := by
    intro t ht ht2
    have hsq : (⟨t, ht⟩ : Gs) * ⟨t, ht⟩ = 1 := by
      apply Subtype.ext
      change t * t = 1
      rw [← sq, ← ht2, pow_orderOf_eq_one]
    have hne : (⟨t, ht⟩ : Gs) ≠ 1 := by
      intro e
      have e' : t = 1 := congrArg Subtype.val e
      rw [e', orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have key : ∀ a : Gs, IsConj a ⟨t, ht⟩ → ∃ h ∈ Gs, h * (a : G) * h⁻¹ = t := by
      intro a ha
      obtain ⟨c, hc⟩ := isConj_iff.1 ha
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    rcases hB.three_classes hsq hne with e | e | e
    · exact Or.inl (key _ e)
    · exact Or.inr (Or.inl (key _ e))
    · exact Or.inr (Or.inr (key _ e))
  have ho1 : orderOf (hA.rG 1) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hA.aG_mul_self) (hA.rG_ne_one (by norm_num))
  exact eq_top_of_three_classes (w₁ := z) (w₂ := hA.rG 1) (w₃ := hA.rG 8) hz ho1
    hA.three_classes_distinct.1 hH h1 h8 hcls

theorem smithGlobalResidual_of_G1 (h : SmithG1Input) :
    SmithGlobalResidual := by
  intro G _ _ z hsimple hG φ h22 h245 h27
  obtain ⟨G₁, ψ, u, v, hu, hun, hv, hvn, hX, hvc, hH⟩ := h G z hsimple hG φ ⟨h22, h245, h27⟩
  have hcard := natCard_closure_eq ψ hu hun hv hvn hX hvc
  set Gs := closure ((G₁ : Set G) ∪ {u}) with hGs
  have hG₁ : G₁ ≤ Gs := fun a ha => subset_closure (Or.inl ha)
  have huGs : u ∈ Gs := subset_closure (Or.inr rfl)
  have hnorm : ∀ {w : G} (hw : w ∈ Gs), w ∉ normalizer (G₁ : Set G) →
      (⟨w, hw⟩ : Gs) ∉ normalizer ((G₁.subgroupOf Gs : Subgroup Gs) : Set Gs) := by
    intro w hw hwn hn
    obtain ⟨k, hk⟩ := exists_not_mem_of_not_mem_normalizer hwn
    exact hk (mem_subgroupOf.1 ((mem_normalizer_iff.1 hn ⟨k, hG₁ k.2⟩).1
      (mem_subgroupOf.2 k.2)))
  have hiso : Nonempty (Gs ≃* K) :=
    nonempty_mulEquiv_co2_of_le ((subgroupOfEquivOfLe hG₁).trans ψ) (u := ⟨u, huGs⟩)
      (v := ⟨v, hvc⟩) hcard (fun k hk => mem_subgroupOf.2 (hu (subgroupOfEquivOfLe hG₁ k) hk))
      (hnorm huGs hun) (fun k hk => mem_subgroupOf.2 (hv (subgroupOfEquivOfLe hG₁ k) hk))
      (hnorm hvc hvn)
  have := hsimple
  have htop : Gs = ⊤ := eq_top_of_centralizer_le hG.orderOf_eq φ hH hiso
  refine ⟨?_, G₁, ψ, u, v, hu, hun, hv, hvn⟩
  rw [← Subgroup.card_top (G := G), ← htop, hcard]

end CFSG.Sporadic.Co2Smith

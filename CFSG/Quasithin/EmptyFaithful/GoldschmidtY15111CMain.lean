module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CCase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Defs

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open F6 CFSG.LieType.BorelTits

section Abstract

variable {K : Type} [Group K] [Finite K]

theorem sixtyFour_le_card_inf {P H V E : Subgroup K} (hG : IsGoldschmidtTriple P H)
    (hVP : V ≤ P) (hPV : P ≤ Subgroup.normalizer (V : Set K)) (hV16 : Nat.card V = 16)
    (hVH : ¬ V ≤ pCoreOf 2 H) (hEH : E ≤ H) (hHE : H ≤ Subgroup.normalizer (E : Set K))
    (hE32 : Nat.card E = 32) : 64 ≤ Nat.card ↥(P ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEle : E ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hEH hHE
    (IsPGroup.of_card (n := 5) (by rw [hE32]; norm_num))
  have hET : E ≤ P ⊓ H := hEle.trans (pCoreOf_le_inf_right hG)
  have hVle : V ≤ pCoreOf 2 P := le_pCoreOf_of_le_normalizer 2 hVP hPV
    (IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num))
  have hVT : V ≤ P ⊓ H := hVle.trans (pCoreOf_le_inf_left hG)
  obtain ⟨a, ha⟩ := exists_card_inf_eq hG
  have h32 : 32 ≤ Nat.card ↥(P ⊓ H) := hE32 ▸ Subgroup.card_le_of_le hET
  have hne : Nat.card ↥(P ⊓ H) ≠ 32 := by
    intro h
    have hEeq : E = P ⊓ H := Subgroup.eq_of_le_of_card_ge hET (by rw [h, hE32])
    exact hVH (hVT.trans (hEeq ▸ hEle))
  have ha5 : 5 ≤ a := by
    by_contra hlt
    have : 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha6 : 6 ≤ a := by
    rcases Nat.eq_or_lt_of_le ha5 with h | h
    · exact absurd (by rw [ha, ← h]; norm_num) hne
    · omega
  calc 64 = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha6
    _ = _ := ha.symm

theorem core_false (hlist : GoldschmidtS3ListCat.{0}) (hG22 : G22AmalgamShapeFact)
    (hM12 : M12AmalgamShapeFact) (hAut : AutM12AmalgamShapeFact) {P H V E : Subgroup K} {c : K}
    (hA : IsGoldschmidtAmalgam P H) (hVP : V ≤ P) (hPV : P ≤ Subgroup.normalizer (V : Set K))
    (hV16 : Nat.card V = 16) (hVe : IsElemAbelian 2 V) (hVH : ¬ V ≤ pCoreOf 2 H) (hcP : c ∈ P)
    (hc3 : c ^ 3 = 1) (hfree : ∀ v ∈ V, c * v * c⁻¹ = v → v = 1) (hEH : E ≤ H)
    (hHE : H ≤ Subgroup.normalizer (E : Set K)) (hE32 : Nat.card E = 32) : False := by
  have hG : IsGoldschmidtTriple P H := hA.toIsGoldschmidtTriple
  have hT := sixtyFour_le_card_inf hG hVP hPV hV16 hVH hEH hHE hE32
  have hPn : NoVc ↥P := by
    rcases hlist K P H hA with ho | ho
    · exact (noVc_of_oriented hG22 hM12 hAut hG hT ho).1
    · rw [inf_comm] at hT
      exact (noVc_of_oriented hG22 hM12 hAut hG.symm hT ho).2
  have hVn : (V.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mpr hPV
  refine hPn (V.subgroupOf P) ⟨c, hcP⟩ hVn ?_ ?_ (Subtype.ext (by simpa using hc3)) ?_
  · rw [← hV16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have := hVe.1.is_comm.comm (⟨a.1, a.2⟩ : ↥V) ⟨b.1, b.2⟩
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))
    · exact Subtype.ext (by simpa using hVe.2 (x : K) hx)
  · intro v hv hcv
    have := hfree (v : K) hv (by simpa using congrArg Subtype.val hcv)
    exact Subtype.ext this

end Abstract

theorem input15111YCoreFree_of_list (hlist : GoldschmidtS3ListCat.{0})
    (hG22 : G22AmalgamShapeFact) (hM12 : M12AmalgamShapeFact)
    (hAut : AutM12AmalgamShapeFact) : Input15111YCoreFree := by
  intro G _ _ I P H V E c hT hbot hVP hPV hV16 hVe hVH hcP hc3 hfree hEH hHE hE
  have hgen := hT.1
  have hPI : P ≤ I := hgen ▸ le_sup_left
  have hHI : H ≤ I := hgen ▸ le_sup_right
  have hVI : V ≤ I := hVP.trans hPI
  have hEI : E ≤ I := hEH.trans hHI
  have hcI : c ∈ I := hPI hcP
  have hbot' : Open.pCore 2 ↥I = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (Open.pCore 2 ↥I) I.subtype_injective).mp hbot
  have hA : IsGoldschmidtAmalgam (P.subgroupOf I) (H.subgroupOf I) := ⟨hT.subgroupOf, hbot'⟩
  have hsub : ∀ {A B : Subgroup G}, A ≤ B → A.subgroupOf I ≤ B.subgroupOf I :=
    fun h y hy => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hy))
  have hE32 : Nat.card E = 32 := by simpa using hE.2.1
  refine core_false hlist hG22 hM12 hAut (V := V.subgroupOf I) (E := E.subgroupOf I)
    (c := ⟨c, hcI⟩) hA (hsub hVP) ?_ ?_ ?_ ?_ (Subgroup.mem_subgroupOf.mpr hcP)
    (Subtype.ext (by simpa using hc3)) ?_ (hsub hEH) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgN := Subgroup.mem_normalizer_iff.mp (hPV (Subgroup.mem_subgroupOf.mp hg)) (y : G)
    simpa [Subgroup.mem_subgroupOf] using hgN
  · rw [← hV16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have := hVe.1.is_comm.comm (⟨a.1, a.2⟩ : ↥V) ⟨b.1, b.2⟩
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))
    · exact Subtype.ext (by simpa using hVe.2 (x : G) hx)
  · intro hle
    apply hVH
    intro v hv
    have h1 : (⟨v, hVI hv⟩ : ↥I) ∈ pCoreOf 2 (H.subgroupOf I) :=
      hle (Subgroup.mem_subgroupOf.mpr hv)
    have h2 := map_pCoreOf_le (r := 2) I.subtype (H.subgroupOf I)
    rw [Subgroup.map_subgroupOf_eq_of_le hHI] at h2
    exact h2 ⟨_, h1, rfl⟩
  · intro v hv hcv
    have := hfree (v : G) hv (by simpa using congrArg Subtype.val hcv)
    exact Subtype.ext this
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgN := Subgroup.mem_normalizer_iff.mp (hHE (Subgroup.mem_subgroupOf.mp hg)) (y : G)
    simpa [Subgroup.mem_subgroupOf] using hgN
  · rw [← hE32]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv

end Y15111

end CFSG.Quasithin

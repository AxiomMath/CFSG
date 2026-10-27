module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section AuxGroup

theorem sixEmb_e5_conj_mem {G : Type} [Group G] {g : G} (hg : g * g = 1) (A : Subgroup G)
    (x : G) : x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g ∈ A := by
  rw [FullCenterWeyl.mem_map_conj_inv, inv_eq_of_mul_eq_one_right hg]

theorem sixEmb_e5_conj_conj {G : Type} [Group G] {g : G} (hg : g * g = 1) (x : G) :
    g * (g * x * g) * g = x := by
  calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
    _ = x := by rw [hg, one_mul, mul_one]

end AuxGroup

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixEmb_e5_inf (hH : SixHConclusion φ t i) :
    Mhat φ t i i ⊓ Mhat φ t i i.swap = Mc φ t i := by
  cases i
  · exact hH.inf_Mhat
  · exact (inf_comm _ _).trans hH.inf_Mhat

theorem sixEmb_e5_embVw_le_Mw : embVw φ t i ≤ Mw φ t i i.swap :=
  Subgroup.map_mono (show Vtor φ t i i ≤ Mc φ t i from inf_le_left)

theorem sixEmb_e5_embVw_le_Mhat : embVw φ t i ≤ Mhat φ t i i.swap :=
  sixEmb_e5_embVw_le_Mw.trans (le_sup_right : Mw φ t i i.swap ≤ Mhat φ t i i.swap)

theorem sixEmb_e6_mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixEmb_e5_VV (hS : SCSetting L K n φ t i) :
    Vtor φ t i i ⊓ Vtor φ t i i.swap = ⊥ := by
  have h1 : Vtor φ t i i.swap = Wk φ t i.swap :=
    RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot
  have h2 : Vtor φ t i i ⊓ Wk φ t i.swap = ⊥ :=
    RootStandard.V_inf_W_swap hS.fc i hS.ne_bot hS.eq_bot
  rw [h1]
  exact h2

theorem sixEmb_e5_MM (hS : SCSetting L K n φ t i) :
    Mc φ t i ⊓ Mw φ t i i.swap = Vtor φ t i i.swap :=
  (SixF.weylProductConclusion_both hS.fc i hS.ne_bot hS.eq_bot).2.1.2.2.1

theorem sixEmb_e6_norm (hH : SixHConclusion φ t i) :
    embVw φ t i ≤ normalizer (Mhat φ t i i : Set G) := by
  have hST : S φ t i ≤ Tplus φ t i :=
    (le_sup_left : S φ t i ≤ S φ t i ⊔ zpowers t).trans_eq hH.sup_t
  have hB1 : embVw φ t i ≤ Mhat φ t i i.swap := sixEmb_e5_embVw_le_Mhat
  have hB : embVw φ t i ≤ Tplus φ t i := hB1.trans ((sixEmb_e6_mhat_le_S i.swap).trans hST)
  obtain ⟨hX, hnorm, -⟩ := hH.normal_Mhat i
  exact hB.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hX).mp hnorm)

theorem sixEmb_e5
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) : EmbE5Concl φ t i := by
  have hVV : Vtor φ t i i ⊓ Vtor φ t i i.swap = ⊥ := sixEmb_e5_VV hS
  have hMM : Mc φ t i ⊓ Mw φ t i i.swap = Vtor φ t i i.swap := sixEmb_e5_MM hS
  have hMh : Mhat φ t i i ⊓ Mhat φ t i i.swap = Mc φ t i := sixEmb_e5_inf hH
  have hg : w φ i.swap * w φ i.swap = 1 := FullCenterWeyl.w_mul_self (φ := φ) i.swap
  show Mhat φ t i i ⊓ embVw φ t i = ⊥
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  have hxMh : x ∈ Mhat φ t i i.swap := sixEmb_e5_embVw_le_Mhat hxB
  have hxMw : x ∈ Mw φ t i i.swap := sixEmb_e5_embVw_le_Mw hxB
  have hxMc : x ∈ Mc φ t i := by
    have h1 : x ∈ Mhat φ t i i ⊓ Mhat φ t i i.swap := Subgroup.mem_inf.mpr ⟨hxA, hxMh⟩
    rw [hMh] at h1
    exact h1
  have hv1 : w φ i.swap * x * w φ i.swap ∈ Vtor φ t i i :=
    (sixEmb_e5_conj_mem hg (Vtor φ t i i) x).mp hxB
  have hv2 : w φ i.swap * x * w φ i.swap ∈ Mc φ t i :=
    (sixEmb_e5_conj_mem hg (Mc φ t i) x).mp hxMw
  have hv3 : w φ i.swap * (w φ i.swap * x * w φ i.swap) * w φ i.swap ∈ Mc φ t i := by
    rw [sixEmb_e5_conj_conj hg x]
    exact hxMc
  have hv4 : w φ i.swap * x * w φ i.swap ∈ Mw φ t i i.swap :=
    (sixEmb_e5_conj_mem hg (Mc φ t i) (w φ i.swap * x * w φ i.swap)).mpr hv3
  have hv5 : w φ i.swap * x * w φ i.swap ∈ Vtor φ t i i.swap := by
    have h1 : w φ i.swap * x * w φ i.swap ∈ Mc φ t i ⊓ Mw φ t i i.swap :=
      Subgroup.mem_inf.mpr ⟨hv2, hv4⟩
    rw [hMM] at h1
    exact h1
  have hv6 : w φ i.swap * x * w φ i.swap = 1 := by
    have h1 : w φ i.swap * x * w φ i.swap ∈ Vtor φ t i i ⊓ Vtor φ t i i.swap :=
      Subgroup.mem_inf.mpr ⟨hv1, hv5⟩
    rw [hVV, Subgroup.mem_bot] at h1
    exact h1
  rw [Subgroup.mem_bot]
  calc x = w φ i.swap * (w φ i.swap * x * w φ i.swap) * w φ i.swap :=
        (sixEmb_e5_conj_conj hg x).symm
    _ = 1 := by rw [hv6, mul_one, hg]

theorem sixEmb_e6
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) (he5 : EmbE5Concl φ t i) :
    Mhat φ t i i ⊔ embVw φ t i = S φ t i := by
  have he5' : Mhat φ t i i ⊓ embVw φ t i = ⊥ := he5
  have hle : Mhat φ t i i ⊔ embVw φ t i ≤ S φ t i :=
    sup_le (sixEmb_e6_mhat_le_S i) (sixEmb_e5_embVw_le_Mhat.trans (sixEmb_e6_mhat_le_S i.swap))
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := Mhat φ t i i) (B := embVw φ t i) (sixEmb_e6_norm hH)
  rw [he5', Subgroup.card_bot, mul_one] at hprod
  have hA : Nat.card (Mhat φ t i i : Subgroup G) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hV : Nat.card (Vtor φ t i i : Subgroup G) = Nat.card K ^ 3 :=
    RootStandard.card_V hS.fc i hS.ne_bot hS.eq_bot
  have hinj : Function.Injective (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom :=
    (MulAut.conj (w φ i.swap)⁻¹).injective
  have hBc : Nat.card (embVw φ t i : Subgroup G) = Nat.card K ^ 3 :=
    (Subgroup.card_map_of_injective hinj).trans hV
  have hsum : Nat.card (Mhat φ t i i ⊔ embVw φ t i : Subgroup G) = Nat.card K ^ 10 := by
    rw [hprod, hA, hBc]
    ring
  have hSc : Nat.card (S φ t i : Subgroup G) = Nat.card K ^ 10 := hH.card_S
  exact Subgroup.eq_of_le_of_card_ge hle (hSc.trans hsum.symm).le

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

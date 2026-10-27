module

public import CFSG.Quasithin.H13.A6S13816b
public import CFSG.Quasithin.Background.A3Structure318Star
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem reduce13821 (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    H ≤ Subgroup.normalizer (K : Set G) ∧ K ⊔ (S.L1 ⊔ T) ∈ S.Hz ∧ K ⊔ (S.L1 ⊔ T) ≤ H ∧
      K ∈ cComp (K ⊔ (S.L1 ⊔ T)) ∧ K ⊔ (S.L1 ⊔ T) ≤ Subgroup.normalizer (K : Set G) ∧
      HypF918 T V L (fsuV1 T V) S.V3 (K ⊔ (S.L1 ⊔ T)) K := by
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  obtain ⟨hH₀z, hH₀H, hF⟩ := S.hypF918_K0 h36c h37 h38 h139 h1334 h13 hS hH hK
  have e : (K ⊔ T) ⊔ S.L1 = K ⊔ (S.L1 ⊔ T) := by
    rw [sup_assoc, sup_comm T S.L1]
  rw [e] at hH₀z hH₀H hF
  exact ⟨hKN, hH₀z, hH₀H, hF.K_cComp, hH₀H.trans hKN, hF⟩

theorem center_modO2_cases (h36 : A36ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKN : H ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨
      Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3 := by
  have hSQ : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hA := h36 _ (SQTKHyp.of_sqtkGroup ↥H hSQ)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  obtain ⟨e₁⟩ := Vol2.Ch11.SecA.quotPCore_subgroupOf_equiv (L := K) hKH
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm hq
  obtain ⟨-, hcases⟩ := A318.lBar_structure hA (subgroupOf_mem_cComp hK) hq'
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hc : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (Subgroup.center ↥(modO2Image H K)) := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  rcases hcases with ⟨hb, -⟩ | ⟨h3, -⟩
  · left
    apply Subgroup.eq_bot_of_card_eq
    rw [hc]
    exact (Subgroup.card_eq_one.mpr hb)
  · exact Or.inr (hc.trans h3)

theorem lem13817 (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      FourList ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨
        Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) ∧
      ¬ ∃ e, IsSz e (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨hKN, hH₀z, -, -, hKN₀, hF⟩ :=
    S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  have hq := S.isQuasisimple_modO2 h36c h139 h1334 h13 hS hH hK
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    ((le_sup_right : T ≤ S.L1 ⊔ T).trans le_sup_right).trans hKN₀
  have hTK : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hTN ht) k).mp hk) (le_conjClosure K T)
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4' hF (S.sqtkGroup_of_mem_Hz hH₀z) hTK hV₁I hIU W hW hirrU hD310 hD391
    hI4).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have ec : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
      (↥(autIH (fsuV1 T V) S.V3 (K ⊔ (S.L1 ⊔ T)) K) ⧸
        Subgroup.center ↥(autIH (fsuV1 T V) S.V3 (K ⊔ (S.L1 ⊔ T)) K)) :=
    QuotientGroup.congr _ _ eA (Subgroup.map_center_eq eA)
  refine ⟨hq, fourList_congr ec.symm h4, S.center_modO2_cases h36 hH hK hKN hq, ?_⟩
  rintro ⟨e, he⟩
  obtain ⟨E⟩ := S.kst_equiv hS hH hK
  exact (h16 G T L V S hS H hH K hK).2 ⟨e, isSz_congr E he⟩

end Setting4

end CFSG.Quasithin.H13.A6

module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovS7

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z RegularWreathProduct

theorem cover_dichotomy_of_good (hB69 : B69Struct) (hB1 : B69One) (hgood : Lemma319SixGood) :
    ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
      ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
        qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
        Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V →
        ∀ L N : Subgroup G, ∀ hstep : IsChiefStep H (conjClosure V H) L N, ¬ IsCentralStep H L N →
          ((∃ _ : (L.subgroupOf N).Normal,
              QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
                NaturalSn 5 H L N) ∨
            (∃ _ : (L.subgroupOf N).Normal,
              QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))
                (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) ∧ NaturalSnPair 5 H L N)) →
          (∀ g : ↥H, chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g = 1 ↔
            (g : G) ∈ centralizerMod L H N) ∧
          ((∃ θ : ↥H →* Equiv.Perm (Fin 5), Function.Surjective θ ∧
              (∀ g : ↥H, θ g = 1 ↔ (g : G) ∈ centralizerMod L H N) ∧
              ∃ d : ↥H, (d : G) ∈ H ⊓ M ∧ (d : G) ∈ Subgroup.centralizer (V : Set G) ∧
                orderOf (θ d) = 3) ∨
          (∃ d t : ↥H, (d : G) ∈ H ⊓ M ∧ (d : G) ∈ Subgroup.centralizer (V : Set G) ∧ (t : G) ∈ T ∧
              orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d) = 3 ∧
              Commute (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d)
                (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) (t * d * t⁻¹)) ∧
              chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) (t * d * t⁻¹) ∉
                Subgroup.zpowers (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d))) := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii L N
    hstep hnc hshape
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := hconcl.elemAbelian
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hRT := h.pCoreOf_le hT
  obtain ⟨A, hA⟩ := hconcl.exists_A
  have hset : Setting H T (H ⊓ M) (conjClosure V H) A :=
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N' hs' hnc' => hconcl.count_four A hA L' N' hs' hnc'⟩
  obtain ⟨L₀, N₀, hstep₀, hnc₀, χ₀, hχC, a, haA, haH, hχa⟩ :=
    hgood G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
  have hg5 : ∃ g : ↥H, orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g) = 5 := by
    rcases hshape with ⟨hnorm, ⟨φ, hφs, hφk, -⟩, -⟩ | ⟨hnorm, ⟨φ, hφs, hφk, -⟩, -⟩
    · exact exists_psi_orderOf_five hset hstep φ hφs hφk orderOf_finRotate_five
    · exact exists_psi_orderOf_five hset hstep φ hφs hφk orderOf_wrI₁_finRotate_five
  have key := Setting.cover_dichotomy_cv hB69 hB1 hset hstep₀ hnc₀ hχC haA haH hχa hstep hnc
    (IsMinOffender.le_centralizer hT h hA) (fun g hg => hII hg) hg5
  exact key

end CFSG.Quasithin.H13.L319

module

public import CFSG.Quasithin.EmptyFaithful.S1421QA16Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Z
public import CFSG.Quasithin.EmptyFaithful.S1421STC2
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Mod
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Surv
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA27

variable {G : Type} [Group G]

theorem exists_embedding_of_survivor4 {T M H K1 : Subgroup G}
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) :
    ∃ (Y : Type) (_ : Group Y) (ψ : ↥K1 →* Y), IsLieOverTwo .trialityD4 0 1 Y ∧
      Function.Injective ψ := by
  obtain ⟨Y, iY, ψ, hY, hψ⟩ := exists_emb_of_isAmalgamOfGroup hsurv.1
  refine ⟨Y, iY, ψ.comp (Subgroup.inclusion le_sup_left), hY, ?_⟩
  exact hψ.comp (Subgroup.inclusion_injective _)

variable [Finite G]

theorem lemma14216QIrred4_holds_legacyBare :
    Lemma14216QIrred4LegacyBare := by
  intro G _ _ T M H K1 st _ hsurv W hZW hWQ hW
  have hsurv' := hsurv
  obtain ⟨-, hq1, hsp, -, -⟩ := hsurv'
  obtain ⟨z, hz2, hz1, -, hzZ, -, -, hzC, hZ⟩ := S1421QA18.exists_z st.hyp
  have hZeq := omegaOneCenter_eq_zpowers hzZ hZ
  rw [hZeq] at hZW ⊢
  have hzW : z ∈ W := hZW (Subgroup.mem_zpowers z)
  have hQK : pCoreOf 2 K1 ≤ K1 := pCoreOf_le 2 K1
  obtain ⟨Y, _, ψ, hY, hψ⟩ := exists_embedding_of_survivor4 hsurv
  have hIrr := irredModel_of_lieModel (Y := Y) hY
  refine irred_of_embedding hIrr hψ (orderOf_eq_prime (by simpa [sq] using hz2) hz1)
    (card_K1_of_survivor4 hq1 hsp) (fun k hk => ?_) hQK
    (fun k hk q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K1 hk) q).mp hq)
    (card_pCoreOf_of_survivor4 hsp) hzW hWQ hW
  have hkc : k ∈ Subgroup.centralizer ({z} : Set G) := hzC ▸ S1421.K1_le_mcOf st hk
  exact Subgroup.mem_centralizer_singleton_iff.mp hkc

end S1421QA27

end CFSG.Quasithin

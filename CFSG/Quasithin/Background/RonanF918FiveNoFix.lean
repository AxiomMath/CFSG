module

public import CFSG.Quasithin.Background.RonanF918FiveK
public import CFSG.Quasithin.Background.RonanF918FiveHatEq

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement

section NoFix

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem five_iii_cases_nofix (hO2 : CFSG.Quasithin.H13.T326.D321O2)
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I) (hirr : IsIrrPlusTildeT h hIU) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hsq : t * t ∈ Subgroup.normalizer (K : Set G))
    (hG : F918Good h hIU ht) :
    HatDSumU V₁ Vp H K T (conjClosure I H) ⁅conjClosure I H, K⁆ t ∧
      tildeOf V₁ ⁅conjClosure I H, K⁆ ≤ tildeOf V₁ (conjClosure I H) ⊓
        Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) ∧
      ((hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ =
            hat' V₁ Vp H K T (conjClosure I H) ⊓
              Subgroup.centralizer (hat' V₁ Vp H K T (conjSub t⁻¹ K) :
                Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) ∧
          hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ = hat' V₁ Vp H K T I ∧
          (F918NatChoice5U V₁ Vp H K T I ∨
            ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), Even n ∧
              Nat.card F = 2 ^ n ∧ σ ≠ RingHom.id F ∧ (∀ x, σ (σ x) = x) ∧
              Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 2 F)) ∧
              ModelOnU (orthModelU F σ) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I))) ∨
        (tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ (conjClosure I H) ⊓
            Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) ∧
          LieModel ↥(autIH V₁ Vp H K) .PSL 3 2 1 ∧
          (∃ s : G, s ∈ T ∧ s ∈ Subgroup.normalizer (K : Set G) ∧
            s ∉ Subgroup.normalizer (I : Set G)) ∧
          ∀ s : G, s ∈ T → s ∈ Subgroup.normalizer (K : Set G) → s ∉ Subgroup.normalizer (I : Set G) →
            (tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ I ⊔ tildeOf V₁ (conjSub s⁻¹ I) ∧
              tildeOf V₁ I ⊓ tildeOf V₁ (conjSub s⁻¹ I) = ⊥) ∧
            Nat.card ↥(tildeOf V₁ I) = 2 ^ 3) ∨
        (tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ (conjClosure I H) ⊓
            Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) ∧
          LieModel ↥(autIH V₁ Vp H K) .PSL 3 2 1 ∧
          (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
            ModelOnU (multiNatModelU 3 4 F) (tildeOf V₁ K) (tildeOf V₁ ⁅conjClosure I H, K⁆)) ∧
          (Nonempty (↥(oTwoRes (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
              (tildeOf V₁ (conjClosure I H)))) ≃* Multiplicative (ZMod 5)) ∨
            Nonempty (↥(oTwoRes (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
              (tildeOf V₁ (conjClosure I H)))) ≃*
                (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))))) ∨
        F918IiiD h hIU) := by
  haveI := factElem h hIU
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have htH : t ∈ H := h.T_le_H ht
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  have hAV := autIH_le_stabSub_subM h hIU hV₁I (le_conjClosure I H) hKI
  have hLV : autIH V₁ I H K ≤ stabSub (subM V₁ (conjClosure I H) I) :=
    (CFSG.Quasithin.AutOn.autOn_mono (V := tildeOf V₁ (conjClosure I H))
      (secImg_mono (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (le_conjClosure K T))).trans hAV
  have hGeq : GoodIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩) := hG
  obtain ⟨hsum, hincl, hcases⟩ := id hGeq
  refine ⟨hatDSumU_of_isSumMod_commutator h hIU htH hsum,
    tilde_commutator_le_centralizer h hIU htH hincl, ?_⟩
  rcases hcases with ⟨hA, hshape⟩ | hB | ⟨hC, htop⟩ | hD
  · obtain ⟨hdhat, hrest⟩ := five_iii_a_of_modFiveA h hH hA37 hA38 hK hV₁I hIU hnt hKI hA
    exact Or.inl ⟨hat_eq_of_modFiveA h hH hA37 hA38 hK hIU ht htK hirr hA.1 hsum hincl, hdhat, hrest⟩
  · exact Or.inr (Or.inl ⟨five_iii_eq_of_inf h hH hA37 hA38 hK hIU hIrr hnt ht htK hsq hGeq
      (modFiveB_commV_inf_fixV hB hLV), five_iii_b_of_modFiveB h hH hA37 hA38 hK hV₁I hIU hnt hB⟩)
  · obtain ⟨hL, hmod⟩ := five_iii_c_model h hH hA37 hA38 hK hIU hnt hC
    exact Or.inr (Or.inr (Or.inl ⟨five_iii_eq_of_inf h hH hA37 hA38 hK hIU hIrr hnt ht htK hsq hGeq
      (d321Two_commV_inf_fixV hC), hL, hmod,
      five_iii_c_O2 hO2 h hH hA37 hA38 hK hV₁I hIU hirr ht htK hC.1 htop⟩))
  · exact Or.inr (Or.inr (Or.inr hD))

end NoFix

end CFSG.Quasithin.RonanF918

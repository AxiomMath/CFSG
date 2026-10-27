module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isE_of_isEP {H T A K : Subgroup G} {j : ℕ} (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP j H T A K) : E1.IsE j H T A K := by
  obtain ⟨hKH, hτ, hSyl, h1 | ⟨h2, hc⟩⟩ := h
  · exact ⟨hKH, hτ, hSyl, Or.inl h1⟩
  · refine ⟨hKH, hτ, hSyl, Or.inr ⟨?_, hc⟩⟩
    have hAK : A ≤ K := (le_sup_left.trans (E1.le_tauOf hT hAT hA)).trans (hτ.trans inf_le_right)
    have hOK : pCoreOf 2 H ≤ K :=
      (le_sup_right.trans (E1.le_tauOf hT hAT hA)).trans (hτ.trans inf_le_right)
    have hOO : pCoreOf 2 H ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOK
        (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
        (hT.isPGroup.to_le (E1.pCoreOf_two_le_of_isSylowIn hT))
    have hTa : (E1.tauOf H T A).subgroupOf K ≤
        E1.tauOf (⊤ : Subgroup ↥K) ((T ⊓ K).subgroupOf K) (A.subgroupOf K) := by
      rw [E1.tauOf_top_subgroupOf (inf_le_right : T ⊓ K ≤ K) hAK]
      intro t ht
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      have ht' := (E1.mem_tauOf_of_le hT.le).mp ht
      exact (E1.mem_tauOf_of_le (inf_le_right : T ⊓ K ≤ K)).mpr
        ⟨Subgroup.mem_inf.mpr ⟨ht'.1, t.2⟩, fun a ha => hOO (ht'.2 a ha)⟩
    obtain ⟨h21, h22, h23, L, hL, hlay, hdisj⟩ := h2
    refine ⟨h21, h22, h23, L, hL, ?_, hdisj⟩
    have hnorm : (CFSG.layer (↥K ⧸ CFSG.solvableRadical ↥K)).Normal := by
      have : (CFSG.layer (↥K ⧸ CFSG.solvableRadical ↥K)).Characteristic :=
        CFSG.LocalCores.layer_characteristic
      infer_instance
    apply le_antisymm
    · rw [hlay]
      refine iSup₂_le fun t ht => ?_
      exact le_iSup₂_of_le t (Subgroup.map_mono hTa ht) le_rfl
    · refine iSup₂_le fun t _ => ?_
      rintro x ⟨y, hy, rfl⟩
      exact hnorm.conj_mem y (CFSG.LocalCores.component_le_layer hL hy) t

end CFSG.LocalAnalysis.WeakClosure81

end

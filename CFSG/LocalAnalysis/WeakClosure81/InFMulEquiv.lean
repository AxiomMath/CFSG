module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
public import CFSG.Quasithin.Background.E1ElevenIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F12

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open scoped Pointwise

theorem eGenP_map_mulEquiv {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (e : G₁ ≃* G₂) (i : ℕ) (H T : Subgroup G₁) (Ω : Set (Subgroup G₁)) :
    eGenP i (H.map e.toMonoidHom) (T.map e.toMonoidHom)
        (Subgroup.map e.toMonoidHom '' Ω) =
      (eGenP i H T Ω).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨K, rfl⟩ : ∃ K : Subgroup G₁, K.map e.toMonoidHom = K' :=
      ⟨K'.comap e.toMonoidHom, Subgroup.map_comap_eq_self_of_surjective e.surjective K'⟩
    have hK : IsEP i H T A K := (CFSG.LocalAnalysis.WeakClosure81.isEP_map_mulEquiv e).mp hK'
    exact Subgroup.map_mono (le_iSup₂_of_le A hA (le_iSup_of_le
      ((CFSG.Quasithin.E1.map_le_map_iff_mulEquiv e).mp hA'T)
      (le_iSup₂_of_le K hK le_rfl)))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map e.toMonoidHom) ⟨A, hA, rfl⟩ (le_iSup_of_le
      (Subgroup.map_mono hAT) (le_iSup₂_of_le (K.map e.toMonoidHom)
        ((CFSG.LocalAnalysis.WeakClosure81.isEP_map_mulEquiv e).mpr hK) le_rfl))

theorem inF_map_mulEquiv {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (e : G₁ ≃* G₂) (j : ℕ) (H : Subgroup G₁) :
    InF j (H.map e.toMonoidHom) ↔ InF j H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (f : A ≃* B) (j : ℕ)
      (K : Subgroup A), InF j K → InF j (K.map f.toMonoidHom) := by
    intro A B _ _ _ _ f j K hf T' hT' Ω' hΩ' hne' hbot'
    set T : Subgroup A := T'.comap f.toMonoidHom with hTdef
    set Ω : Set (Subgroup A) := Subgroup.map f.symm.toMonoidHom '' Ω' with hΩdef
    have hmapT : T.map f.toMonoidHom = T' :=
      Subgroup.map_comap_eq_self_of_surjective f.surjective T'
    have hTin : IsSylowIn 2 T K := by
      refine (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv f).mp ?_
      rw [hmapT]
      exact CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
    have hT : CFSG.ABGLocalTools.IsSylowOf 2 T K :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr hTin
    have hΩ : CFSG.Quasithin.E1.IsInvColl K Ω := by
      have h := CFSG.Quasithin.E1.Eleven.isInvColl_map_mulEquiv f.symm hΩ'
      rwa [CFSG.Quasithin.E1.Eleven.map_map_symm] at h
    have hne : Ω.Nonempty := by
      obtain ⟨A, hA⟩ := hne'
      exact ⟨A.map f.symm.toMonoidHom, A, hA, rfl⟩
    have hbot : ∀ A ∈ Ω, A ≠ ⊥ := by
      rintro A ⟨B, hB, rfl⟩ hA
      refine hbot' B hB ?_
      have hBmap : (B.map f.symm.toMonoidHom).map f.toMonoidHom = B := by
        have h := CFSG.Quasithin.E1.Eleven.map_map_symm f.symm B
        rwa [MulEquiv.symm_symm] at h
      rw [← hBmap, hA, Subgroup.map_bot]
    have hprod := hf T hT Ω hΩ hne hbot
    have hmapΩ : Subgroup.map f.toMonoidHom '' Ω = Ω' := by
      have h := CFSG.Quasithin.E1.Eleven.image_map_symm f.symm Ω'
      rwa [MulEquiv.symm_symm] at h
    have himg := congrArg (fun s : Set A => f.toMonoidHom '' s) hprod
    rw [Set.image_mul, ← Subgroup.coe_map f.toMonoidHom (eGenP j K T Ω),
      ← Subgroup.coe_map f.toMonoidHom T, ← Subgroup.coe_map f.toMonoidHom K,
      ← eGenP_map_mulEquiv f j K T Ω, hmapΩ, hmapT] at himg
    exact himg
  constructor
  · intro h'
    have h := key e.symm j (H.map e.toMonoidHom) h'
    rwa [CFSG.Quasithin.E1.Eleven.map_map_symm] at h
  · exact key e j H

end CFSG.LocalAnalysis.UniquenessCase.UC22.F12

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem inFSq_iff_bar2_inF_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {H : Subgroup G} {H' : Subgroup G'}
    (e : CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H ≃*
      CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H') (j : ℕ) :
    InFSq j H ↔ InFSq j H' := by
  simpa only [InFSq, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using
    (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.inF_map_mulEquiv e j ⊤).symm

end CFSG.LocalAnalysis.WeakClosure81

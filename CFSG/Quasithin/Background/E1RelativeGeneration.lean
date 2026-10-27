module

public import CFSG.Quasithin.Background.E1Sec7Two
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem relative_generation {T A K : Subgroup G} {Γ : Type*} [Group Γ] {n : ℕ}
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hτ : tauOf ⊤ T A ≤ T ⊓ K)
    (hS : IsSylowIn 2 (T ⊓ K) K)
    (π : ↥K →* Γ) (hπ : Function.Surjective π) (hker2 : IsPGroup 2 π.ker)
    (hgen : ((T ⊓ K).subgroupOf K).map π ⊔
      (⨆ I ∈ {I : Subgroup Γ | IsE n ⊤ (((T ⊓ K).subgroupOf K).map π)
        ((A.subgroupOf K).map π) I}, I) = ⊤) :
    K ≤ T ⊔ ⨆ J ∈ {J : Subgroup G | IsE n ⊤ T A J}, J := by
  haveI : Finite Γ := Finite.of_surjective π hπ
  have hAK : A ≤ K := (le_sup_left.trans (le_tauOf hT hA hAab)).trans (hτ.trans inf_le_right)
  let S0 : Subgroup ↥K := (T ⊓ K).subgroupOf K
  let A0 : Subgroup ↥K := A.subgroupOf K
  let q : ↥K →* (↥K ⧸ π.ker) := QuotientGroup.mk' π.ker
  let e : (↥K ⧸ π.ker) ≃* Γ := QuotientGroup.liftEquiv π.ker hπ rfl
  have hSbar : S0.map π = Subgroup.map e.toMonoidHom (S0.map q) := by
    rw [Subgroup.map_map]
    congr 1
  have hAbar : A0.map π = Subgroup.map e.toMonoidHom (A0.map q) := by
    rw [Subgroup.map_map]
    congr 1
  have hSq : Subgroup.map e.symm.toMonoidHom (S0.map π) = S0.map q := by
    rw [hSbar, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  have hAq : Subgroup.map e.symm.toMonoidHom (A0.map π) = A0.map q := by
    rw [hAbar, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  have hS0 : IsSylowIn 2 S0 ⊤ := by
    have := (isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ K) (K := K) (H := K)
      inf_le_right le_rfl).mpr hS
    simpa [S0, Subgroup.subgroupOf_self] using this
  have hA0S0 : A0 ≤ S0 := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr ⟨hA (Subgroup.mem_subgroupOf.mp ha), a.2⟩
  have hA0ab : IsElemAbelian 2 A0 := CFSG.Open.IsElemAbelian.subgroupOf hAab K
  let M : Subgroup G := T ⊔ ⨆ J : Subgroup G, ⨆ (_ : IsE n ⊤ T A J), J
  let D : Subgroup G := M ⊓ K
  have hDle : D ≤ K := inf_le_right
  have hSD : T ⊓ K ≤ D := le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hS0D : S0 ≤ D.subgroupOf K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hSD (Subgroup.mem_subgroupOf.mp hx))
  have hIle : ∀ I : Subgroup Γ, IsE n ⊤ (S0.map π) (A0.map π) I →
      I ≤ (D.subgroupOf K).map π := by
    intro I hI
    have hI'E : IsE n ⊤ (S0.map q) (A0.map q) (I.map e.symm) := by
      have h := (isE_map_mulEquiv e.symm).mpr hI
      rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective, hSq, hAq] at h
      exact h
    obtain ⟨J0, hJ0, hres⟩ := ten_seven (G := ↥K) (Y := π.ker) hS0 hA0S0 hA0ab
      (I := Subgroup.map e.symm.toMonoidHom I) hI'E
    have hJ0K : IsE n K (T ⊓ K) A (J0.map K.subtype) := by
      have h := (isE_map_subtype K (i := n) (T' := S0) (A' := A0) (K' := J0)).mpr hJ0
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right,
        Subgroup.map_subgroupOf_eq_of_le hAK] at h
    have hJ0G : IsE n ⊤ T A (J0.map K.subtype) :=
      eight_two hT hA hAab le_top hτ hS hJ0K
    have hJ0M : J0.map K.subtype ≤ M := by
      refine (le_iSup_of_le (J0.map K.subtype) ?_).trans le_sup_right
      exact le_iSup_of_le hJ0G le_rfl
    have hJ0D : J0.map K.subtype ≤ D := le_inf hJ0M (Subgroup.map_subtype_le J0)
    have hJ0D' : J0 ≤ D.subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hJ0D (Subgroup.mem_map_of_mem K.subtype hx))
    have hJ0res : (twoResidual J0).map q ≤ (D.subgroupOf K).map q :=
      Subgroup.map_mono (f := q) ((twoResidual_le J0).trans hJ0D')
    have hresD : twoResidual I ≤ (D.subgroupOf K).map π := by
      have h2 : Subgroup.map e.symm.toMonoidHom (twoResidual I) ≤ (D.subgroupOf K).map q := by
        rw [map_twoResidual e.symm.toMonoidHom I, hres]
        exact hJ0res
      have h4 : twoResidual I ≤ Subgroup.map e.toMonoidHom ((D.subgroupOf K).map q) := by
        have hmap := Subgroup.map_mono (f := e.toMonoidHom) h2
        rwa [Subgroup.map_map,
          show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ by
            ext x; simp,
          Subgroup.map_id] at hmap
      have hDbar :
          (D.subgroupOf K).map π = Subgroup.map e.toMonoidHom ((D.subgroupOf K).map q) := by
        rw [Subgroup.map_map]
        congr 1
      simpa [hDbar] using h4
    calc I ≤ twoResidual I ⊔ (S0.map π ⊓ I) := le_twoResidual_sup_of_isSylowIn hI.2.2.1
      _ ≤ (D.subgroupOf K).map π :=
        sup_le hresD (inf_le_left.trans (Subgroup.map_mono hS0D))
  have htop : (⊤ : Subgroup Γ) ≤ (D.subgroupOf K).map π := by
    rw [← hgen]
    refine sup_le ?_ ?_
    · exact Subgroup.map_mono hS0D
    · exact iSup₂_le fun I hI => hIle I hI
  have hDmap : (D.subgroupOf K).map π = ⊤ := top_le_iff.mp htop
  have hkerS0 : π.ker ≤ S0 := by
    have h1 : π.ker ≤ pCoreOf 2 (⊤ : Subgroup ↥K) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
        (le_of_eq (Subgroup.normalizer_eq_top π.ker).symm) hker2
    exact h1.trans (pCoreOf_two_le_of_isSylowIn hS0)
  have hkerD : π.ker ≤ D.subgroupOf K := hkerS0.trans hS0D
  have hDtop : D.subgroupOf K = ⊤ := by
    have h := Subgroup.comap_map_eq_self (f := π) hkerD
    rw [hDmap, Subgroup.comap_top] at h
    exact h.symm
  have hDK : D = K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDle, hDtop, Subgroup.map_top,
      Subgroup.range_subtype]
  change K ≤ T ⊔ ⨆ J : Subgroup G, ⨆ (_ : IsE n ⊤ T A J), J
  exact hDK ▸ (inf_le_left : D ≤ M)

theorem relative_generation_le_eGen_sup_normalizer {T A K : Subgroup G} {Γ : Type*} [Group Γ]
    {n : ℕ} (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hτ : tauOf ⊤ T A ≤ T ⊓ K)
    (hS : IsSylowIn 2 (T ⊓ K) K)
    (π : ↥K →* Γ) (hπ : Function.Surjective π) (hker2 : IsPGroup 2 π.ker)
    (hgen : ((T ⊓ K).subgroupOf K).map π ⊔
      (⨆ I ∈ {I : Subgroup Γ | IsE n ⊤ (((T ⊓ K).subgroupOf K).map π)
        ((A.subgroupOf K).map π) I}, I) = ⊤)
    {Ω : Set (Subgroup G)} (hΩ : IsInvColl ⊤ Ω) (hAΩ : A ∈ Ω) :
    K ≤ eGen n ⊤ T Ω ⊔ Subgroup.normalizer (weakClosure T Ω : Set G) := by
  have hmain : K ≤ T ⊔ ⨆ J ∈ {J : Subgroup G | IsE n ⊤ T A J}, J :=
    relative_generation (T := T) (A := A) (K := K) (Γ := Γ) (n := n)
      hT hA hAab hτ hS π hπ hker2 hgen
  refine hmain.trans (sup_le ?_ ?_)
  · exact (le_normalizer_weakClosure hΩ).trans le_sup_right
  · exact iSup₂_le fun J hJ => (le_eGen hAΩ hA hJ).trans le_sup_left

end E1

end CFSG.Quasithin

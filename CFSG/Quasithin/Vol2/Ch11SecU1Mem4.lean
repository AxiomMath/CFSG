module

public import CFSG.Quasithin.Vol2.Ch11SecU1Mem2
public import CFSG.Quasithin.Background.E3ClosedTwo

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem isE_one_self_of_almostSimple_image {Y : Type} [Group Y] [Finite Y]
    {H T A : Subgroup G} (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (φ : ↥H →* Y) (hφ : Function.Surjective φ) (hker : IsPGroup 2 ↥φ.ker)
    (K : Subgroup Y) [hKn : K.Normal] [IsSimpleGroup ↥K] (hnab : ∃ a b : ↥K, a * b ≠ b * a)
    (htwo : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ K)
    (hAc : ¬ (A.subgroupOf H).map φ ≤ Subgroup.centralizer (K : Set Y))
    (hA2 : Nat.card ↥((A.subgroupOf H).map φ) ≤ 2) :
    E1.IsE 1 H T A H := by
  classical
  have hTH : T ≤ H := hT.1
  have hSyl : IsSylowIn 2 (T ⊓ H) H := by rwa [inf_eq_left.mpr hTH]
  refine ⟨le_rfl, le_inf (E1.tauOf_le _ _ _) ((E1.tauOf_le _ _ _).trans hTH), hSyl, Or.inr ?_⟩
  set C : Subgroup Y := Subgroup.centralizer (K : Set Y) with hCdef
  have hZ := SecE3.center_eq_bot_of_simple hnab
  have hKC : K ⊓ C = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
    have hc : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hc)
  have hcent : ∀ q : Y, (∀ l ∈ K, l * q = q * l) → q ∈ C := fun q h =>
    Subgroup.mem_centralizer_iff.mpr h
  have hAS := Comp.almostSimple_map hnab hKC hcent htwo
  have hC2 : IsPGroup 2 C := Comp.isPGroup_two hKC htwo
  set ψ : ↥H →* Y ⧸ C := (QuotientGroup.mk' C).comp φ with hψdef
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective C).comp hφ
  have hkerψ : ψ.ker = C.comap φ := by
    ext x
    simp [hψdef, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hkerψ2 : IsPGroup 2 ↥ψ.ker := by
    rw [hkerψ]
    exact IsPGroup.comap_of_ker_isPGroup hC2 φ hker
  have hO2 : CFSG.Open.pCore 2 (Y ⧸ C) = ⊥ :=
    le_bot_iff.mp (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le)
  have hZC : E1.IsTwoClosed ((CFSG.Open.pCore 2 (Y ⧸ C)).comap ψ) := by
    rw [hO2, MonoidHom.comap_bot]
    exact ⟨ψ.ker, ⟨le_rfl, hkerψ2, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hSylQ : IsSylowIn 2 ((T ⊓ H).subgroupOf H) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (H := H) inf_le_right le_rfl).mpr hSyl
    rwa [Subgroup.subgroupOf_self] at h
  have hBS : A.subgroupOf H ≤ (T ⊓ H).subgroupOf H := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hAT hx, x.2⟩
  have hB : (A.subgroupOf H).map ψ ≠ ⊥ := by
    intro h
    apply hAc
    rintro _ ⟨a, ha, rfl⟩
    have h1 : ψ a = 1 := by
      have : ψ a ∈ (A.subgroupOf H).map ψ := Subgroup.mem_map_of_mem ψ ha
      rw [h, Subgroup.mem_bot] at this
      exact this
    have h2 : a ∈ ψ.ker := h1
    rw [hkerψ, Subgroup.mem_comap] at h2
    exact h2
  have hkerS : ψ.ker ≤ (T ⊓ H).subgroupOf H := by
    have h2 := B6.pCoreOf_two_le_of_isSylowTwoOf hSylQ
    rw [E1.pCoreOf_top_eq] at h2
    exact (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hkerψ2).trans h2
  have hres : twoResidual (⊤ : Subgroup ↥H) = perfectCore (⊤ : Subgroup ↥H) :=
    E1.twoResidual_eq_perfectCore_of_surjective ψ hψ hSylQ
      (fun M hSM hM => by rwa [sup_eq_left.mpr (hkerS.trans hSM)] at hM)
      (by rw [hAS.twoResidual_eq, hAS.perfectCore_eq])
  refine ⟨E1.eTwo_of_surjective ψ hψ hZC hSylQ.2.1 hBS hres (hAS.eTwo hB), ?_⟩
  rw [← E1.card_barRad_eq_of_surjective ψ hψ (E1.isSolvable_ker_of_isTwoClosed ψ hZC)]
  unfold E1.barRad
  rw [Subgroup.card_map_of_injective (by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hAS.solvableRadical_eq_bot])]
  have hmap : (A.subgroupOf H).map ψ = ((A.subgroupOf H).map φ).map (QuotientGroup.mk' C) := by
    rw [hψdef, Subgroup.map_map]
  rw [hmap]
  exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans (hA2.trans (by norm_num))

end CFSG.Quasithin.Vol2.Ch11.SecU1

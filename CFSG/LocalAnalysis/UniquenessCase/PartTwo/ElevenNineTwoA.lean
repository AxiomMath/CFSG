module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

variable {M V₀ V : Subgroup G} [hN : ((F11.CTilde M V₀ V).subgroupOf M).Normal]

theorem barImage11_hinf_inf_barPreimage11 {Y : Subgroup G} {Lbar : Subgroup (F11.MBar11 M V₀ V)}
    (hLY : Lbar ≤ F11.barImage11 M V₀ V Y) (hYM : Y ≤ M) (hLperf : ⁅Lbar, Lbar⁆ = Lbar) :
    F11.barImage11 M V₀ V (Hinf (Y ⊓ F11.barPreimage11 M V₀ V Lbar)) = Lbar := by
  set P := F11.barPreimage11 M V₀ V Lbar
  set H := Y ⊓ P
  have hHM : H ≤ M := by
    show Y ⊓ P ≤ M
    exact inf_le_left.trans hYM
  let f : ↥H →* ↥Lbar :=
    ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)).comp
      (Subgroup.inclusion hHM)).codRestrict Lbar fun h => by
        obtain ⟨h', hh'⟩ := uc22p22u_mem_barPreimage11.1 h.2.2
        have hh : Subgroup.inclusion hHM h = (⟨(h : G), h'⟩ : ↥M) := Subtype.ext rfl
        change (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M))
          (Subgroup.inclusion hHM h) ∈ Lbar
        rw [hh]
        exact hh'
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨m, hm, hmq⟩ := uc22p22u_mem_barImage11.1 (hLY hq)
    have hmP : (m : G) ∈ P :=
      uc22p22u_mem_barPreimage11.2 ⟨m.2, by
        show (QuotientGroup.mk m : F11.MBar11 M V₀ V) ∈ Lbar
        rw [hmq]
        exact hq⟩
    refine ⟨⟨(m : G), ⟨hm, hmP⟩⟩, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk m : F11.MBar11 M V₀ V) = q
    exact hmq
  have hLbarTop : CFSG.perfectResidual ↥Lbar = ⊤ := by
    refine eq_top_iff.2 (uc22p21c_le_perfectResidual ⊤ ?_)
    have h2 : ⁅(⊤ : Subgroup ↥Lbar), (⊤ : Subgroup ↥Lbar)⁆ = ⊤ := by
      apply Subgroup.map_injective (Subgroup.subtype_injective Lbar)
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact hLperf
    exact h2
  have hres : (CFSG.perfectResidual ↥H).map f = ⊤ := by
    rw [uc22p21c_map_perfectResidual f hf, hLbarTop]
  apply le_antisymm
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
    have hmH : (m : G) ∈ H := uc22p21c_Hinf_le H hm
    obtain ⟨h', hh'⟩ := uc22p22u_mem_barPreimage11.1 hmH.2
    have hm' : (⟨(m : G), h'⟩ : ↥M) = m := Subtype.ext rfl
    rwa [hm'] at hh'
  · intro q hq
    have h1 : (⟨q, hq⟩ : ↥Lbar) ∈ (CFSG.perfectResidual ↥H).map f := by
      rw [hres]
      trivial
    obtain ⟨w, hw, hwq⟩ := h1
    refine uc22p22u_mem_barImage11.2 ⟨Subgroup.inclusion hHM w,
      uc22p21c_mem_Hinf.2 ⟨w, hw, rfl⟩, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hHM w) : F11.MBar11 M V₀ V) = q
    exact congrArg Subtype.val hwq

theorem isSubnormal_hinf_inf_barPreimage11 {Y : Subgroup G} {Lbar : Subgroup (F11.MBar11 M V₀ V)}
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hL : IsSubnormal Lbar ⊤) :
    IsSubnormal (Hinf (Y ⊓ F11.barPreimage11 M V₀ V Lbar)) M := by
  have hPsub : IsSubnormal (F11.barPreimage11 M V₀ V Lbar) M := by
    have h1 : IsSubnormal (Lbar.comap (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)))
        ((⊤ : Subgroup (F11.MBar11 M V₀ V)).comap
          (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M))) :=
      IsSubnormal.comap (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)) hL
    rw [Subgroup.comap_top] at h1
    have h2 := h1.map M.subtype
    rw [Subgroup.map_top, Subgroup.range_subtype] at h2
    exact h2
  have hYsub : IsSubnormal Y M :=
    IsSubnormal.step hYM ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hMY)
      (IsSubnormal.refl M)
  have hPY : IsSubnormal (F11.barPreimage11 M V₀ V Lbar ⊓ Y) M := by
    have h1 : IsSubnormal (F11.barPreimage11 M V₀ V Lbar ⊓ Y) (M ⊓ Y) := hPsub.inf Y
    rw [inf_eq_right.2 hYM] at h1
    exact h1.trans hYsub
  have hHinfNorm : ((Hinf (Y ⊓ F11.barPreimage11 M V₀ V Lbar)).subgroupOf
      (Y ⊓ F11.barPreimage11 M V₀ V Lbar)).Normal := by
    have heq : (Hinf (Y ⊓ F11.barPreimage11 M V₀ V Lbar)).subgroupOf
        (Y ⊓ F11.barPreimage11 M V₀ V Lbar) =
        CFSG.perfectResidual ↥(Y ⊓ F11.barPreimage11 M V₀ V Lbar) :=
      Subgroup.comap_map_eq_self_of_injective
        (Subgroup.subtype_injective (Y ⊓ F11.barPreimage11 M V₀ V Lbar)) _
    rw [heq]
    infer_instance
  exact (IsSubnormal.step (uc22p21c_Hinf_le _) hHinfNorm (IsSubnormal.refl _)).trans
    (by rw [inf_comm]; exact hPY)

theorem barImage11_conjClosure {K : Subgroup G} (hKM : K ≤ M) :
    F11.barImage11 M V₀ V (conjClosure M K) =
      ⨆ g : F11.MBar11 M V₀ V, (F11.barImage11 M V₀ V K).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · have hle : conjClosure M K ≤
        F11.barPreimage11 M V₀ V
          (⨆ ĝ : F11.MBar11 M V₀ V,
            (F11.barImage11 M V₀ V K).map (MulAut.conj ĝ).toMonoidHom) := by
      refine iSup₂_le fun A hA => ?_
      obtain ⟨g, hg, rfl⟩ := hA
      intro a ha
      obtain ⟨k, hk, hkga⟩ := Subgroup.mem_map.1 ha
      rw [← hkga, uc22p22u_mem_barPreimage11]
      have hM : (MulAut.conj g).toMonoidHom k ∈ M :=
        M.mul_mem (M.mul_mem hg (hKM hk)) (M.inv_mem hg)
      refine ⟨hM, ?_⟩
      have hmemK : (QuotientGroup.mk (⟨k, hKM hk⟩ : ↥M) : F11.MBar11 M V₀ V) ∈
          F11.barImage11 M V₀ V K :=
        uc22p22u_mem_barImage11.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩
      have hle' : (F11.barImage11 M V₀ V K).map
          (MulAut.conj ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M))
            (⟨g, hg⟩ : ↥M))).toMonoidHom ≤
          ⨆ ĝ : F11.MBar11 M V₀ V,
            (F11.barImage11 M V₀ V K).map (MulAut.conj ĝ).toMonoidHom :=
        le_iSup (fun ĝ : F11.MBar11 M V₀ V =>
          (F11.barImage11 M V₀ V K).map (MulAut.conj ĝ).toMonoidHom) _
      refine hle' (Subgroup.mem_map.2 ⟨_, hmemK, ?_⟩)
      change (MulAut.conj ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M))
            (⟨g, hg⟩ : ↥M))).toMonoidHom
            ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)) (⟨k, hKM hk⟩ : ↥M)) =
          (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M))
            (⟨(MulAut.conj g).toMonoidHom k, hM⟩ : ↥M)
      have hsub : (⟨(MulAut.conj g).toMonoidHom k, hM⟩ : ↥M) =
          (⟨g, hg⟩ : ↥M) * (⟨k, hKM hk⟩ : ↥M) * (⟨g, hg⟩ : ↥M)⁻¹ :=
        Subtype.ext rfl
      rw [hsub]
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
    obtain ⟨h', hh'⟩ := uc22p22u_mem_barPreimage11.1 (hle hm)
    have hm' : (⟨(m : G), h'⟩ : ↥M) = m := Subtype.ext rfl
    rwa [hm'] at hh'
  · refine iSup_le fun g => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨k, hk, hky⟩ := uc22p22u_mem_barImage11.1 hy
    rw [← hky]
    have hmem : ((m * k * m⁻¹ : ↥M) : G) ∈ conjClosure M K := by
      have hle' : K.map (MulAut.conj (m : G)).toMonoidHom ≤ conjClosure M K :=
        le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) _
          ⟨(m : G), m.2, rfl⟩ le_rfl
      refine hle' (Subgroup.mem_map.2 ⟨(k : G), hk, ?_⟩)
      rfl
    refine uc22p22u_mem_barImage11.2 ⟨m * k * m⁻¹, hmem, ?_⟩
    change (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M) (m * k * m⁻¹) :
        F11.MBar11 M V₀ V) =
      (MulAut.conj ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)) m)).toMonoidHom
        ((QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)) k)
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

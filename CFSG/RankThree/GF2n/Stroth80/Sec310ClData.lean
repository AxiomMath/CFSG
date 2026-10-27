module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClElation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.theoremX_data (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    (hdim : 4 ≤ Module.finrank K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) :
    ∃ P : Set ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), (∀ e ∈ P, e ≠ 0) ∧
      Submodule.span K P = ⊤ ∧
      (∀ e ∈ P, Classify.ElationFull D.F ((D.ρ.range : Set _) ∩ Classify.pointRad D.F e) e) ∧
      D.ρ.range = Subgroup.closure (⋃ e ∈ P, (D.ρ.range : Set _) ∩ Classify.pointRad D.F e) := by
  classical
  have hex : ∀ (m : G) (hm : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
      ∃ e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), e ≠ 0 ∧
        (∀ v : M₀.E, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • (e : M₀.E)) ∧
        ((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
          Classify.pointRadSubgroup D.F e ∧
        Classify.ElationFull D.F
          ((((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ :
            Subgroup _) : Set _) e := fun m hm ht => D.elation_data h34 hs h hdim hm ht
  choose e he0 heB hepr heful using hex
  refine ⟨{x | ∃ (m : G) (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)), x = e m hm ht},
    ?_, ?_, ?_, ?_⟩
  · rintro x ⟨m, hm, ht, rfl⟩
    exact he0 m hm ht
  · rw [eq_top_iff]
    intro w _
    have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) := mem_imgSub.mp w.2
    rw [hc.img_Vt_eq t M₀] at hw
    have key : (⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
        M₀.img (conjSubgroup m B)) ≤ (Submodule.span K ((Subtype.val : ↥(imgSub M₀
          (Vt M (LB M Q B) B Z t) hS) → M₀.E) ''
          {x | ∃ (m : G) (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)),
            x = e m hm ht})).toAddSubgroup := by
      refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
      intro v hv
      obtain ⟨s, rfl⟩ := (heB m hm ht v).mp hv
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨e m hm ht, ⟨m, hm, ht, rfl⟩, rfl⟩)
    exact (Submodule.apply_mem_span_image_iff_mem_span (f := (imgSub M₀
      (Vt M (LB M Q B) B Z t) hS).subtype) Subtype.val_injective).mp (key hw)
  · rintro x ⟨m, hm, ht, rfl⟩
    intro φ hφ
    obtain ⟨g, hg, hgφ⟩ := heful m hm ht φ hφ
    exact ⟨g, ⟨(Subgroup.map_le_range D.ρ _) hg, hepr m hm ht hg⟩, hgφ⟩
  · apply le_antisymm
    · set T : Set (↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) ≃ₗ[K]
        ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) :=
        ⋃ x ∈ {x | ∃ (m : G) (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)),
          x = e m hm ht}, (D.ρ.range : Set _) ∩ Classify.pointRad D.F x with hT
      have hAC : ∀ (m : G) (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)),
          ((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
            Subgroup.closure T := by
        intro m hm ht g hg
        apply Subgroup.subset_closure
        simp only [hT, Set.mem_iUnion]
        exact ⟨e m hm ht, ⟨m, hm, ht, rfl⟩, (Subgroup.map_le_range D.ρ _) hg, hepr m hm ht hg⟩
      have hRle : Rt M (LB M Q B) t ≤
          ((Subgroup.closure T).comap D.ρ).map (Rt M (LB M Q B) t).subtype := by
        unfold Rt
        refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
        intro x hx
        have hxR : x ∈ Rt M (LB M Q B) t :=
          hc.LB_conj_le_Rt hm ht (by rw [hc.LB_conj hm]; exact hx)
        refine ⟨⟨x, hxR⟩, ?_, rfl⟩
        exact hAC m hm ht ⟨⟨x, hxR⟩, hx, rfl⟩
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr', hrr⟩ := hRle r.2
      have : r' = r := Subtype.ext hrr
      rw [this] at hr'
      exact hr'
    · refine (Subgroup.closure_le _).mpr fun g hg => ?_
      simp only [Set.mem_iUnion] at hg
      obtain ⟨x, -, hg1, -⟩ := hg
      exact hg1

end CFSG.RankThree.GF2n.Stroth80

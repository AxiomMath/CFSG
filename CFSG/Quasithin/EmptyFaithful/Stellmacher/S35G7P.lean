module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7P4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7P3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7

open S35.Fin S35.G7.P

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conj_mem_Wb {γ : Geo H M} {g w : G} (hg : g ∈ stab γ) (hw : w ∈ Wb γ) :
    g * w * g⁻¹ ∈ Wb γ :=
  (Subgroup.mem_normalizer_iff.mp (Std.Wb_normal γ hg) w).mp hw

theorem pm (hS : Sit H M S) (hI : CaseI H M) (hZ : HypZ H M) (hR : HypR H M)
    (h5b : Claim5b H M) (h6b : Claim6b H M) (hA : AbstractPlaneLemma) (hB : Lem81 H M S)
    (hK : KernelStruct H M S) (hW : WModuleExists H M S) : PM H M := by
  intro γ hγ hsec y hy hyQ hyidx u hu hu1 hu2 hpl ⟨μ₀, hμ₀, hμ₀u⟩ w hw
  have hC : Ch.Ctx H M S := ⟨hS, hI, hZ, hR⟩
  obtain ⟨E, hEn, hVE, hEW, hEL, hEo, hy1, hy2⟩ := hB hS hI h5b h6b γ hγ hsec y hy hyQ hyidx
  obtain ⟨K, hKn, hVK, hKE, hKl, hKQ⟩ := hK hS γ hγ E hEn hVE hEW hEo y hy hyQ hy1 hy2
  obtain ⟨l₀, hl₀⟩ := exists_adj γ
  have hl₀' : l₀ ∈ nbrs γ := hl₀
  obtain ⟨c, hc⟩ := hC.exists_chart_normalized hγ (sylow_stab_inf_left hS.glob.amalg hl₀')
  have hD : c.Dl l₀ = S5Syl := hc
  obtain ⟨wm⟩ := hW hS hI hZ hR h6b γ hγ hsec c l₀ hl₀' hc E K hEn hVE hEW hEL hEo y hy hyQ
    hyidx hy1 hy2 hKn hVK hKE hKl hKQ
  have hu1' : ∀ v ∈ Vn γ, ⁅u, v⁆ = 1 := hu1
  have hker : ∀ x : ↥(Wb γ), wm.proj x = 1 → f0 hS c u hu2 x = 1 := by
    intro x hx
    have hxK : (x : G) ∈ K := (wm.proj_eq_one x).mp hx
    refine eq_one_of_mem_all_img hC hγ c hl₀' hD fun l hl => ?_
    obtain ⟨h, hmem⟩ := f0_mem_img hC hγ c hu1' hu2 hpl hl ((hKl l hl).1 hxK)
    exact hmem
  obtain ⟨f, hf⟩ := exists_lift wm (f0 hS c u hu2) hker
  have hf1 : f = 1 := by
    refine hA wm.mod wm.faithful wm.t wm.idx_t wm.π wm.π_surj wm.π_act wm.U wm.inv wm.π_inj
      wm.card_U wm.gen f ?_ ?_
    · intro σ u' hu'
      rw [wm.U_eq] at hu'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu'
      obtain ⟨g, rfl⟩ := c.surj σ
      have hxl : (x : G) ∈ Wl l₀ := hx
      have hcj : (g : G) * (x : G) * (g : G)⁻¹ ∈ Wb γ := conj_mem_Wb g.2 x.2
      rw [wm.proj_conj g x hcj, hf]
      have hgl : sm g • l₀ ∈ nbrs γ := Std.smul_mem_nbrs_of_stab (g := sm g) g.2 hl₀'
      obtain ⟨h, hmem⟩ := f0_mem_img hC hγ c hu1' hu2 hpl hgl (conj_mem_Wl (g := sm g) hxl)
      rw [img_Rl_smul hC hγ c g hl₀', mem_mp] at hmem
      rw [img_Rl_eq_map hC hγ hl₀' hD wm] at hmem
      obtain ⟨u'', hu'', hπ⟩ := Subgroup.mem_map.mp hmem
      refine ⟨u'', hu'', ?_⟩
      rw [hπ]
      exact (act_act_inv orth _ _).symm
    · obtain ⟨g₀, hg₀, hgl⟩ := stab_transitive_on_nbrs hl₀' hμ₀
      refine ⟨c.θ ⟨g₀, hg₀⟩, fun u' hu' => ?_⟩
      rw [wm.U_eq] at hu'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu'
      have hxl : (x : G) ∈ Wl l₀ := hx
      have hcj : (g₀ : G) * (x : G) * (g₀ : G)⁻¹ ∈ Wb γ := conj_mem_Wb hg₀ x.2
      rw [wm.proj_conj ⟨g₀, hg₀⟩ x hcj, hf, f0_apply]
      have h1 := conj_mem_Wl (g := g₀) hxl
      rw [hgl] at h1
      have h2 : (⟨⁅(g₀ : G) * (x : G) * (g₀ : G)⁻¹, u⁆, hu2 _ hcj⟩ : ↥(Vn γ)) = 1 :=
        Subtype.ext (hμ₀u _ h1)
      show c.π ⟨⁅(g₀ : G) * (x : G) * (g₀ : G)⁻¹, u⁆, hu2 _ hcj⟩ = 1
      rw [h2, map_one]
  have h3 : f0 hS c u hu2 ⟨w, hw⟩ = 1 := by rw [← hf, hf1]; rfl
  exact (c.π_eq_one _).mp h3

end S35.G7

end F53.Stellmacher

end CFSG.Quasithin

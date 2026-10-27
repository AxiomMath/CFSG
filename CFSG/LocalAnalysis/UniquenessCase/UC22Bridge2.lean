module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem cTilde_bot (M V : Subgroup G) :
    F11.CTilde M ⊥ V = M ⊓ centralizer (V : Set G) := by
  ext m
  simp only [F11.CTilde, Subgroup.mem_iInf, F11.CElt, Subgroup.mem_mk, Set.mem_setOf_eq,
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    refine ⟨(h 1 V.one_mem).1, fun g hg => ?_⟩
    have h2 : m * g * m⁻¹ * g⁻¹ = 1 := (h g hg).2.2
    have h3 : m * g * m⁻¹ = g := mul_inv_eq_one.1 h2
    have h4 : m * g = g * m := mul_inv_eq_iff_eq_mul.1 h3
    exact h4.symm
  · rintro ⟨hm, hc⟩ i hi
    have hN : m ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp only [SetLike.mem_coe, Subgroup.mem_bot]
      constructor
      · rintro rfl; simp
      · intro hh
        calc h = m⁻¹ * (m * h * m⁻¹) * m := by group
          _ = 1 := by rw [hh]; group
    refine ⟨hm, hN, ?_⟩
    have h1 : i * m = m * i := hc i hi
    have h3 : m * i * m⁻¹ = i := by rw [← h1]; group
    rw [h3]; group

theorem kerAct_normal (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G)) :
    (kerAct M V).Normal := by
  refine ⟨fun x hx m => ?_⟩
  rw [kerAct, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hv' : (m : G)⁻¹ * v * (m : G) ∈ V := by
    have := (mem_normalizer_iff.1 (hV (inv_mem m.2)) v).1 hv
    simpa using this
  have hxv : ((m : G)⁻¹ * v * (m : G)) * (x : G) = (x : G) * ((m : G)⁻¹ * v * (m : G)) := hx _ hv'
  show v * ((m : G) * (x : G) * (m : G)⁻¹) = ((m : G) * (x : G) * (m : G)⁻¹) * v
  calc v * ((m : G) * (x : G) * (m : G)⁻¹)
      = (m : G) * (((m : G)⁻¹ * v * (m : G)) * (x : G)) * (m : G)⁻¹ := by group
    _ = (m : G) * ((x : G) * ((m : G)⁻¹ * v * (m : G))) * (m : G)⁻¹ := by rw [hxv]
    _ = ((m : G) * (x : G) * (m : G)⁻¹) * v := by group

theorem subgroupOf_cTilde_bot (M V : Subgroup G) :
    (F11.CTilde M ⊥ V).subgroupOf M = kerAct M V := by
  rw [cTilde_bot]
  ext m
  simp only [kerAct, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨m.2, h⟩⟩

theorem cTilde_bot_normal (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G)) :
    ((F11.CTilde M ⊥ V).subgroupOf M).Normal := by
  rw [subgroupOf_cTilde_bot]
  exact kerAct_normal M V hV

noncomputable def mbarEquiv (M V : Subgroup G) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] :
    MBar M V ≃* F11.MBar11 M ⊥ V := by
  have h1 : (kerAct M V).Normal := by rw [← subgroupOf_cTilde_bot]; exact hN
  have h2 : (kerAct M V).normalCore = (F11.CTilde M ⊥ V).subgroupOf M := by
    rw [Subgroup.normalCore_eq_self, subgroupOf_cTilde_bot]
  exact QuotientGroup.quotientMulEquivOfEq h2

theorem map_mbarImage (M V X : Subgroup G) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] :
    (mbarImage M V X).map (mbarEquiv M V).toMonoidHom = F11.barImage11 M ⊥ V X := by
  unfold mbarImage F11.barImage11
  rw [Subgroup.map_map]
  congr 1

theorem pRank_mbar (M V : Subgroup G) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] (p : ℕ) :
    CFSG.pRank p (MBar M V) = CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 M ⊥ V)) := by
  rw [CFSG.pRank_congr_of_mulEquiv (mbarEquiv M V) p]
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (F11.MBar11 M ⊥ V))]
  exact (CFSG.pRank_congr_of_mulEquiv (Subgroup.topEquiv (G := F11.MBar11 M ⊥ V)) p).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22

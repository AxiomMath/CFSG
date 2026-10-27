module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2PcA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem conj_z_mem_K0 (h : Ctx T M g A t d x) : x * (d * d) * x⁻¹ ∈ K0 T d x := by
  obtain ⟨a, ha, haV, -⟩ := three_cycle_x h.c h.hD h.hd4 h.hx h.hx3
  have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
  have hd1 := d1_mem_Xgen h.c h.hx hd
  have haX : x * (d * d) * x⁻¹ ∈ Xgen T M := by
    have : x * (d * d) * x⁻¹ = (x * d * x⁻¹) * (x * d * x⁻¹) := by group
    rw [this]
    exact (Xgen T M).mul_mem hd1 hd1
  have haU : x * (d * d) * x⁻¹ ∈ uOfL22 T M := ha ▸ Hyp1281Two.VZ_le_uOfL22 T M haV
  exact ⟨uOfL22_le_oTwoUpper h.c haU, Subgroup.mem_centralizer_singleton_iff.mpr
    (Xgen_comm h.c h.hD h.hd4 _ haX _ (wOfX_mem_Xgen h.c h.hD h.hx))⟩

theorem x_mem_Gw (h : Ctx T M g A t d x) : x ∈ Gw d x :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (x_comm_wOfX h.c h.hD h.hd4 h.hx h.hx3))

theorem exists_noncomm_conj (h : Ctx T M g A t d x) :
    ∃ y ∈ K0 T d x, (x * (d * d) * x⁻¹) * (y * (x * (d * d) * x⁻¹) * y⁻¹) ≠
      (y * (x * (d * d) * x⁻¹) * y⁻¹) * (x * (d * d) * x⁻¹) := by
  obtain ⟨a, ha, -, haZ, -, haa, -⟩ := three_cycle_x h.c h.hD h.hd4 h.hx h.hx3
  have hdd := dd_facts h.hd4
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hzK := sq_mem_K0 h
  have haK : a ∈ K0 T d x := ha ▸ conj_z_mem_K0 h
  obtain ⟨ι, -, -, -, hι, -⟩ := z4StarSL23_struct h.hO
  have hzc : ∀ k : ↥(K0 T d x), k * (⟨d * d, hzK⟩ : ↥(K0 T d x)) = ⟨d * d, hzK⟩ * k := fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ k.2.1) (d * d) hzZ).symm
  have hzι : (⟨d * d, hzK⟩ : ↥(K0 T d x)) = ι := by
    rcases (hι _ hzc).2 (Subtype.ext hdd.1) with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hdd.2
    · exact h1
  have hac : ¬ ∀ k : ↥(K0 T d x), k * (⟨a, haK⟩ : ↥(K0 T d x)) = ⟨a, haK⟩ * k := by
    intro hc
    rcases (hι _ hc).2 (Subtype.ext haa) with h1 | h1
    · exact haZ (by rw [show a = 1 from congrArg Subtype.val h1]; exact Subgroup.one_mem _)
    · exact haZ (by rw [← hzι] at h1; rw [show a = d * d from congrArg Subtype.val h1]; exact hzZ)
  obtain ⟨y, hy⟩ := z4StarSL23_noncomm h.hO (a := ⟨a, haK⟩) (Subtype.ext haa) hac
  exact ⟨y, y.2, ha ▸ fun heq => hy (Subtype.ext heq)⟩

theorem pCore_Gw_le_T (h : Ctx T M g A t d x) : pCoreOf 2 (Gw d x) ≤ T :=
  (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.hSyl).trans inf_le_left

theorem z_not_mem_pCore_Gw (h : Ctx T M g A t d x) : d * d ∉ pCoreOf 2 (Gw d x) := by
  intro hz
  obtain ⟨y, hyK, hy⟩ := exists_noncomm_conj h
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hnorm := le_normalizer_pCoreOf 2 (Gw d x)
  have hzc : ∀ p ∈ pCoreOf 2 (Gw d x), (d * d) * p = p * (d * d) := fun p hp =>
    (Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hzZ).2.1 p
      (pCore_Gw_le_T h hp)).symm
  have hxG := x_mem_Gw h
  have hyxG : y * x ∈ Gw d x := Subgroup.mul_mem _ hyK.2 hxG
  have hcP : ∀ c ∈ Gw d x, c * (d * d) * c⁻¹ ∈ pCoreOf 2 (Gw d x) := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hc) _).mp hz
  have hb : ∀ p ∈ pCoreOf 2 (Gw d x), (y * x) * (d * d) * (y * x)⁻¹ * p =
      p * ((y * x) * (d * d) * (y * x)⁻¹) := by
    intro p hp
    have hp' : (y * x)⁻¹ * p * (y * x) ∈ pCoreOf 2 (Gw d x) := by
      have := (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.inv_mem _ hyxG)) p).mp hp
      rwa [inv_inv] at this
    calc (y * x) * (d * d) * (y * x)⁻¹ * p
        = (y * x) * ((d * d) * ((y * x)⁻¹ * p * (y * x))) * (y * x)⁻¹ := by group
      _ = (y * x) * (((y * x)⁻¹ * p * (y * x)) * (d * d)) * (y * x)⁻¹ := by rw [hzc _ hp']
      _ = p * ((y * x) * (d * d) * (y * x)⁻¹) := by group
  apply hy
  have e : y * (x * (d * d) * x⁻¹) * y⁻¹ = (y * x) * (d * d) * (y * x)⁻¹ := by group
  rw [e]
  exact (hb _ (hcP x hxG)).symm

end InspW2

end S143

end CFSG.Quasithin

module

public import CFSG.Quasithin.H13.A5S136a
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem v12_mem_V2 : S.v12 ∈ S.V2 :=
  S.mem_pre.2 ⟨S.v12_mem_V, by rw [S.psi_v12]; exact mem_W2.2 e01_props.1⟩

theorem lemma_13_6_4 :
    baum (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) = baum T ∧
      thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) = thompsonJ T := by
  have hsub : Subgroup.centralizer (S.V2 : Set G) ≤ Subgroup.centralizer ({S.v12} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v12_mem_V2)
  have hbT : baum T ≤ T ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    le_inf inf_le_left (S.baum_le_centralizer_V2.trans hsub)
  have hJT : thompsonJ T ≤ T ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    le_inf (B6.thompsonJ_le T) (S.thompsonJ_le_centralizer_V2.trans hsub)
  exact ⟨(baum_eq_of_le hbT inf_le_left).symm, B6.thompsonJ_eq_of_le hJT inf_le_left⟩

theorem lemma_13_6_5 (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) :
    Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (baum T : Set G) ≤
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({S.v12} : Set G) := by
  intro x hx
  obtain ⟨hxv, hxS⟩ := Subgroup.mem_inf.mp hx
  have hxM := S.normalizer_baum_le h517 hxS
  refine ⟨?_, hxv⟩
  have hne : Subgroup.zpowers S.v12 ≠ ⊥ := by
    intro h
    have : S.v12 = 1 := (Subgroup.zpowers_eq_bot).mp h
    have h1 : S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ = 1 := by
      have : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = 1 := Subtype.ext this
      rw [this, map_one]
    rw [S.psi_v12] at h1
    exact E12_ne_one h1
  have hle : Subgroup.zpowers S.v12 ≤ V := Subgroup.zpowers_le.mpr S.v12_mem_V
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hxv
      exact ((Commute.zpow_left hc.symm k).eq))
  exact S.mem_normalizer_V_of h1222 hxM hne hle hxN

end Setting

end CFSG.Quasithin.H13.A5

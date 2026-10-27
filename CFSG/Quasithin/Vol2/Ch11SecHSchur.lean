module

public import CFSG.Quasithin.Vol2.Ch11SecHP2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_K_le_pCoreOf_H (H : Subgroup G) : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H :=
  F7.pCoreOf_mono_of_le_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem comm_Q_mem_P (i : Inp32) {x : G} (hx : x ∈ pCoreOf 2 (oTwoUpper H)) {z : G}
    (hz : z ∈ fsuV T I ⊔ conjSubgroup (fsuV T I) h) : x * z * x⁻¹ * z⁻¹ ∈ pOf T I H h := by
  have hxO := pCoreOf_K_le_pCoreOf_H H hx
  have hxN : x ∈ Subgroup.normalizer (pOf T I H h : Set G) :=
    d.K_le_normalizer_P i (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
  let S : Subgroup G :=
    { carrier := {z | z ∈ Subgroup.normalizer (pOf T I H h : Set G) ∧
        x * z * x⁻¹ * z⁻¹ ∈ pOf T I H h}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
        have : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha ((Subgroup.mem_normalizer_iff.mp haN _).mp hb)
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, ?_⟩
        have : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [this]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp
          (Subgroup.inv_mem _ ha) }
  have hVS : fsuV T I ≤ S := by
    intro v hv
    refine ⟨d.fsuV_le_normalizer_P i hv, Subgroup.mem_sup_left ?_⟩
    rw [d.bOf_eq i]
    refine ⟨?_, ?_⟩
    · exact (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (d.pCoreOf_le_normalizer_V hxO) v).mp hv) ((fsuV T I).inv_mem hv)
    · have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (d.c.V_le_H hv)) x⁻¹).mp
        ((pCoreOf 2 H).inv_mem hxO)
      have h2 : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
      rw [h2]
      exact (pCoreOf 2 H).mul_mem hxO this
  have hVhS : conjSubgroup (fsuV T I) h ≤ S := by
    intro v hv
    refine ⟨d.Vh_le_normalizer_P i hv, Subgroup.mem_sup_right ?_⟩
    rw [d.Bh_eq i]
    refine ⟨?_, ?_⟩
    · exact (conjSubgroup (fsuV T I) h).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (d.pCoreOf_le_normalizer_Vh hxO) v).mp hv) ((conjSubgroup (fsuV T I) h).inv_mem hv)
    · have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (d.Vh_le_H hv)) x⁻¹).mp
        ((pCoreOf 2 H).inv_mem hxO)
      have h2 : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
      rw [h2]
      exact (pCoreOf 2 H).mul_mem hxO this
  exact (sup_le hVS hVhS hz).2

theorem inf_P_le (i : Inp32) : oTwoUpper H ⊓ pOf T I H h ≤ pCoreOf 2 (oTwoUpper H) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _ hk => mem_normalizer_inf (Subgroup.le_normalizer hk) (d.K_le_normalizer_P i hk))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
      (inf_le_right.trans (d.P_le_pCoreOf i)))

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH

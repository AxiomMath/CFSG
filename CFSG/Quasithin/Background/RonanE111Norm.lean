module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.EmptyFaithful.E111RMemA

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_conj_diagHom {J Z : Subgroup G} [Fintype ↥Z] (hC : DiagComm J Z) {v : G}
    (hvN : v ∈ Subgroup.normalizer (J : Set G)) (hvC : ∀ c ∈ Z, v * c = c * v) (y : ↥J) :
    ∃ z : ↥J, (z : G) = v⁻¹ * (y : G) * v ∧
      v⁻¹ * diagHom J Z hC y * v = diagHom J Z hC z := by
  have hvinv : v⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hvN
  have hz : v⁻¹ * (y : G) * v ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp hvinv (y : G)).mp y.2
    simpa using this
  refine ⟨⟨v⁻¹ * (y : G) * v, hz⟩, rfl, ?_⟩
  have h1 := conj_diagHom_of_comm hC ⟨v⁻¹ * (y : G) * v, hz⟩ hvN hvC
  have h3 : v * (v⁻¹ * (y : G) * v) * v⁻¹ = (y : G) := by group
  have h4 : diagHom J Z hC ⟨v * (v⁻¹ * (y : G) * v) * v⁻¹, by rw [h3]; exact y.2⟩ =
      diagHom J Z hC y :=
    congrArg (diagHom J Z hC) (Subtype.ext h3)
  have h5 : v * diagHom J Z hC ⟨v⁻¹ * (y : G) * v, hz⟩ * v⁻¹ = diagHom J Z hC y :=
    h1.trans h4
  rw [← h5]
  group

theorem norm_trick {X T A J Z : Subgroup G} [Fintype ↥Z] (h : DiagSetting X T A J Z)
    (hZV : Z ⊔ (A ⊓ Subgroup.normalizer (J : Set G)) = A) {j : G} (hj : j ∈ J)
    (hjS : ∀ v ∈ A ⊓ Subgroup.normalizer (J : Set G), j * v * j⁻¹ ∈ T) :
    ∃ x : G, x ∈ X ∧ conjSub x A ≤ T ∧
      conjSub j (A ⊓ Subgroup.normalizer (J : Set G)) ⊔
          (T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G)) =
        conjSub x (A ⊓ Subgroup.normalizer (J : Set G)) ⊔
          (T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G)) := by
  obtain ⟨x, hx⟩ : ∃ x : G, x = diagHom J Z h.diagComm ⟨j, hj⟩ := ⟨_, rfl⟩
  have hxX : x ∈ X := by
    have hmem : diagHom J Z h.diagComm ⟨j, hj⟩ ∈ diagSub J Z h.diagComm := ⟨⟨j, hj⟩, rfl⟩
    rw [hx]
    exact h.diag_le hmem
  have hZx : ∀ z ∈ Z, z * x * z⁻¹ = x := fun z hz => by
    rw [hx]
    exact conj_diagHom_of_mem h.diagComm _ hz
  have hVx : ∀ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ w : ↥J,
      (w : G) = v⁻¹ * j * v * j⁻¹ ∧ x * v * x⁻¹ = v * diagHom J Z h.diagComm w := by
    intro v hv
    obtain ⟨z, hzv, hzd⟩ := exists_inv_conj_diagHom h.diagComm hv.2
      (fun c hc => h.comm hv.1 (h.CA hc)) ⟨j, hj⟩
    rw [← hx] at hzd
    refine ⟨z * (⟨j, hj⟩ : ↥J)⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzv]
    · rw [map_mul, map_inv, ← hx, ← hzd]
      group
  have hkey : ∀ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ c ∈
      T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G),
        x * v * x⁻¹ = j * v * j⁻¹ * c := by
    intro v hv
    obtain ⟨w, hwG, hxv⟩ := hVx v hv
    have hwT : (w : G) ∈ T := by
      rw [hwG]
      have e : v⁻¹ * j * v * j⁻¹ = v⁻¹ * (j * v * j⁻¹) := by group
      rw [e]
      exact T.mul_mem (T.inv_mem (h.AT hv.1)) (hjS v hv)
    have hdT : diagHom J Z h.diagComm w ∈ T := by
      apply diagHom_mem_of h.diagComm w
      intro c hc
      exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) hwT) (T.inv_mem (h.AT (h.CA hc)))
    have hcC : (w : G)⁻¹ * diagHom J Z h.diagComm w ∈ Subgroup.centralizer (J : Set G) :=
      inv_mul_diagHom_mem h.diagComm w
    refine ⟨(w : G)⁻¹ * diagHom J Z h.diagComm w,
      ⟨⟨T.mul_mem (T.inv_mem hwT) hdT, Subgroup.centralizer_le_normalizer _ hcC⟩, hcC⟩, ?_⟩
    have hjv : j * v * j⁻¹ = v * (w : G) := by
      rw [hwG]
      group
    rw [hxv, hjv]
    group
  have hconj : A1b.conjSub x A ≤ T := by
    unfold A1b.conjSub
    rw [Subgroup.map_le_iff_le_comap, ← hZV]
    refine sup_le (fun z hz => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_comap]
      show x * z * x⁻¹ ∈ T
      have hxz : x * z * x⁻¹ = z := by
        have e := mul_inv_eq_iff_eq_mul.mp (hZx z hz)
        rw [← e, mul_inv_cancel_right]
      rw [hxz]
      exact h.AT (h.CA hz)
    · rw [Subgroup.mem_comap]
      show x * v * x⁻¹ ∈ T
      obtain ⟨c, hc, hEq⟩ := hkey v hv
      rw [hEq]
      exact T.mul_mem (hjS v hv) (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1
  have hjoin : A1b.conjSub j (A ⊓ Subgroup.normalizer (J : Set G)) ⊔
      (T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G)) =
      A1b.conjSub x (A ⊓ Subgroup.normalizer (J : Set G)) ⊔
      (T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G)) := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨c, hc, hEq⟩ := hkey v hv
      show j * v * j⁻¹ ∈ _
      have e : j * v * j⁻¹ = x * v * x⁻¹ * c⁻¹ := by
        rw [hEq, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem_sup (A1b.mem_conjSub_of_mem hv) (Subgroup.inv_mem _ hc)
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨c, hc, hEq⟩ := hkey v hv
      show x * v * x⁻¹ ∈ _
      rw [hEq]
      exact Subgroup.mul_mem_sup (A1b.mem_conjSub_of_mem hv) hc
  exact ⟨x, hxX, hconj, hjoin⟩

end CFSG.Quasithin.RonanE111

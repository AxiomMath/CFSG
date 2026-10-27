module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsLie

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

universe u v

section Map

variable {Mb : Type u} [Group Mb] {Mb' : Type v} [Group Mb'] (θ : Mb ≃* Mb')
  {T M1 M2 : Subgroup Mb} {z t : Mb}

theorem isConj_map_iff {a b : Mb} : IsConj (θ a) (θ b) ↔ IsConj a b := by
  rw [isConj_iff, isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨θ.symm c, θ.injective (by simpa using hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨θ c, by simpa using congrArg θ hc⟩

theorem InvStep.map {i j : Mb} (h : InvStep T M1 M2 i j) :
    InvStep (T.map θ.toMonoidHom) (M1.map θ.toMonoidHom) (M2.map θ.toMonoidHom) (θ i) (θ j) := by
  obtain ⟨hi, hj, c, hc, rfl⟩ := h
  refine ⟨Subgroup.mem_map_of_mem _ hi, Subgroup.mem_map_of_mem _ hj, θ c, ?_, by simp⟩
  rcases hc with hc | hc
  · exact Or.inl (Subgroup.mem_map_of_mem _ hc)
  · exact Or.inr (Subgroup.mem_map_of_mem _ hc)

theorem reflTransGen_invStep_map {i j : Mb} (h : Relation.ReflTransGen (InvStep T M1 M2) i j) :
    Relation.ReflTransGen (InvStep (T.map θ.toMonoidHom) (M1.map θ.toMonoidHom)
      (M2.map θ.toMonoidHom)) (θ i) (θ j) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.map θ)

theorem map_centralizer_singleton (a : Mb) :
    Subgroup.centralizer ({θ a} : Set Mb') =
      (Subgroup.centralizer ({a} : Set Mb)).map θ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨θ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply θ.injective
    simpa using hx
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simpa using congrArg θ hy

theorem F431LieI.map (D : F431LieI T M1 M2 z t) :
    F431LieI (T.map θ.toMonoidHom) (M1.map θ.toMonoidHom) (M2.map θ.toMonoidHom) (θ z) (θ t) where
  sylow := by
    obtain ⟨-, hp, hi⟩ := D.sylow
    refine ⟨le_top, hp.of_equiv (T.equivMapOfInjective θ.toMonoidHom θ.injective), ?_⟩
    have e1 : ((T.map θ.toMonoidHom).subgroupOf ⊤).index = (T.map θ.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have e2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
    have e3 : (T.map θ.toMonoidHom).index = T.index := Subgroup.index_map_equiv (H := T) θ
    rw [e1, e3]
    rwa [e2] at hi
  T_le₁ := Subgroup.map_mono D.T_le₁
  T_le₂ := Subgroup.map_mono D.T_le₂
  z_mem := Subgroup.mem_map_of_mem _ D.z_mem
  t_mem := Subgroup.mem_map_of_mem _ D.t_mem
  hz := (orderOf_injective θ.toMonoidHom θ.injective z).trans D.hz
  ht := (orderOf_injective θ.toMonoidHom θ.injective t).trans D.ht
  not_conj h := D.not_conj ((isConj_map_iff θ).1 h)
  classes x hx := by
    have hx' : orderOf (θ.symm x) = 2 := by
      rw [← hx]
      exact (orderOf_injective θ.symm.toMonoidHom θ.symm.injective x).symm.symm
    rcases D.classes _ hx' with h | h
    · left
      simpa using (isConj_map_iff θ).2 h
    · right
      simpa using (isConj_map_iff θ).2 h
  cent_z := by
    rw [map_centralizer_singleton, D.cent_z]
  cent_t := by
    rw [map_centralizer_singleton]
    exact Subgroup.map_mono D.cent_t
  center_T w hw hc hne := by
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨m, hm, hmz⟩ := D.center_T w₀ hw₀ (fun y hy => by
      apply θ.injective
      simpa using hc (θ y) (Subgroup.mem_map_of_mem _ hy)) (fun h => hne (by simp [h]))
    refine ⟨θ m, ?_, by simpa using congrArg θ hmz⟩
    obtain ⟨hm1, hm2⟩ := Subgroup.mem_inf.1 hm
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hm1, Subgroup.mem_map_of_mem _ hm2⟩
  inv_chain i hi ho := by
    have hi' : θ.symm i ∈ T := by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hi
      simpa using hy
    have ho' : orderOf (θ.symm i) = 2 := by
      rw [← ho]
      exact (orderOf_injective θ.symm.toMonoidHom θ.symm.injective i)
    rcases D.inv_chain _ hi' ho' with h | h
    · left
      simpa using reflTransGen_invStep_map θ h
    · right
      simpa using reflTransGen_invStep_map θ h

end Map

end CFSG.Quasithin

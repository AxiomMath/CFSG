module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSOutDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructOdd

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint
open CFSG.QuasithinUnique.Setup.Layer (isSylowTwoOf_map_mulEquiv)

universe u v

section Aux

variable {Mb : Type u} [Group Mb] {Mb' : Type v} [Group Mb'] (θ : Mb ≃* Mb')

theorem centerOf_map_eq (X : Subgroup Mb) :
    centerOf (X.map θ.toMonoidHom) = (centerOf X).map θ.toMonoidHom := by
  unfold centerOf
  rw [centralizer_map_equiv, Subgroup.map_inf_eq _ _ _ θ.injective]

theorem spTf_map (T : Subgroup Mb) (f : Mb) :
    spTf (T.map θ.toMonoidHom) (θ f) = (spTf T f).map θ.toMonoidHom := by
  unfold spTf
  rw [Subgroup.map_inf_eq _ _ _ θ.injective, map_centralizer_singleton θ f]

theorem spWf_map (T : Subgroup Mb) (f : Mb) :
    spWf (T.map θ.toMonoidHom) (θ f) = (spWf T f).map θ.toMonoidHom := by
  unfold spWf
  rw [spTf_map, centerOf_map_eq, ← Subgroup.map_commutator,
    Subgroup.map_inf_eq _ _ _ θ.injective]

theorem card_map_eq (X : Subgroup Mb) : Nat.card (X.map θ.toMonoidHom) = Nat.card X :=
  (Nat.card_congr (X.equivMapOfInjective θ.toMonoidHom θ.injective).toEquiv).symm

end Aux

variable {Mb : Type u} [Group Mb] [Finite Mb] {Mb' : Type v} [Group Mb'] [Finite Mb']
  (θ : Mb ≃* Mb') {T S N N' : Subgroup Mb} {f z : Mb} {I : Finset Mb}

theorem F431TwoOut.map (D : F431TwoOut T S f N N' z I) :
    F431TwoOut (T.map θ.toMonoidHom) (S.map θ.toMonoidHom) (θ f) (N.map θ.toMonoidHom)
      (N'.map θ.toMonoidHom) (θ z) (I.map θ.toEquiv.toEmbedding) where
  sylow := by
    have h := (isSylowTwoOf_map_mulEquiv θ).2 D.sylow
    rwa [Subgroup.map_top_of_surjective _ θ.surjective] at h
  T_le := Subgroup.map_mono D.T_le
  T_le' := Subgroup.map_mono D.T_le'
  S_le := Subgroup.map_mono D.S_le
  S_norm := by
    rw [← Subgroup.map_equiv_normalizer_eq S θ]
    exact Subgroup.map_mono D.S_norm
  cyc := by
    obtain ⟨t₀, ht₀⟩ := D.cyc
    refine ⟨θ t₀, ?_⟩
    rw [ht₀, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  z_mem := Subgroup.mem_map_of_mem _ D.z_mem
  z_two := (orderOf_injective θ.toMonoidHom θ.injective z).trans D.z_two
  z_ZN := by
    rw [← map_perfectCore θ.toMonoidHom N, centerOf_map_eq]
    exact Subgroup.mem_map_of_mem _ D.z_ZN
  center_T w hw hc hne := by
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨m, hm, hmz⟩ := D.center_T w₀ hw₀ (fun y hy => by
      apply θ.injective
      simpa using hc (θ y) (Subgroup.mem_map_of_mem _ hy)) (fun h => hne (by simp [h]))
    exact ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ hmz⟩
  I_le i hi := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨h1, h2⟩ := D.I_le j hj
    exact ⟨Subgroup.mem_map_of_mem _ h1,
      (orderOf_injective θ.toMonoidHom θ.injective j).trans h2⟩
  fusion x hx hx2 := by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy2 : orderOf y = 2 := by
      rw [← hx2]
      exact (orderOf_injective θ.toMonoidHom θ.injective y).symm
    obtain ⟨i, hi, h | h⟩ := D.fusion y hy hy2
    · obtain ⟨m, hm, hmi⟩ := h
      exact ⟨θ i, Finset.mem_map_of_mem _ hi,
        Or.inl ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ hmi⟩⟩
    · obtain ⟨m, hm, hmi⟩ := h
      exact ⟨θ i, Finset.mem_map_of_mem _ hi,
        Or.inr ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ hmi⟩⟩
  f_mem := Subgroup.mem_map_of_mem _ D.f_mem
  f_not := fun h => D.f_not (by simpa using (Subgroup.mem_map_iff_mem θ.injective).1 h)
  f_sq := by rw [← map_pow, D.f_sq, map_one]
  Tf_lt i hi := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    have e : θ.toEquiv.toEmbedding j = θ j := rfl
    rw [e, spTf_map, map_centralizer_singleton θ j, ← Subgroup.map_inf_eq _ _ _ θ.injective,
      card_map_eq, card_map_eq]
    exact D.Tf_lt j hj
  Sylow_Tf := by
    rw [spTf_map, map_centralizer_singleton θ f, ← Subgroup.map_inf_eq _ _ _ θ.injective]
    exact (isSylowTwoOf_map_mulEquiv θ).2 D.Sylow_Tf
  Z_sq x hx := by
    rw [← map_perfectCore θ.toMonoidHom N, centerOf_map_eq] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, D.Z_sq y hy, map_one]
  Z_S := by
    rw [centerOf_map_eq, ← map_perfectCore θ.toMonoidHom N, centerOf_map_eq]
    exact Subgroup.map_mono D.Z_S
  W_le := by
    rw [spWf_map, centerOf_map_eq]
    exact Subgroup.map_mono D.W_le
  W_ne := by
    obtain ⟨x, hx, hxZ, hx1⟩ := D.W_ne
    refine ⟨θ x, ?_, ?_, fun h => hx1 (θ.injective (by simpa using h))⟩
    · rw [spWf_map]
      exact Subgroup.mem_map_of_mem _ hx
    · rw [← map_perfectCore θ.toMonoidHom N, centerOf_map_eq]
      exact Subgroup.mem_map_of_mem _ hxZ

end CFSG.Quasithin.H13.F431.D4q.Struct

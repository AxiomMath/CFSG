module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieIso
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutDatum

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.D4q.Struct
open CFSG.QuasithinUnique.Setup.Layer (isSylowTwoOf_map_mulEquiv)

universe u v

variable {Mb : Type u} [Group Mb] {Mb' : Type v} [Group Mb']
  (θ : Mb ≃* Mb') {T S N N' V : Subgroup Mb} {f z t : Mb}

theorem F431UnOut.map (D : F431UnOut T S f N N' z t V) :
    F431UnOut (T.map θ.toMonoidHom) (S.map θ.toMonoidHom) (θ f) (N.map θ.toMonoidHom)
      (N'.map θ.toMonoidHom) (θ z) (θ t) (V.map θ.toMonoidHom) where
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
  t_mem := Subgroup.mem_map_of_mem _ D.t_mem
  t_two := (orderOf_injective θ.toMonoidHom θ.injective t).trans D.t_two
  zt_not_conj := fun h => D.zt_not_conj ((isConj_map_iff θ).1 h)
  z_ZN := by
    rw [unOut_centerOf_perfectCore_map]
    exact Subgroup.mem_map_of_mem _ D.z_ZN
  Z_sq x hx := by
    rw [unOut_centerOf_perfectCore_map] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, D.Z_sq y hy, map_one]
  ZN_trans x hx hx1 := by
    rw [unOut_centerOf_perfectCore_map] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨m, hm, e⟩ := D.ZN_trans y hy (fun h1 => hx1 (by rw [h1, map_one]))
    exact ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩
  center_T w hw hc hne := by
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨m, hm, e⟩ := D.center_T w₀ hw₀ (fun y hy => by
      apply θ.injective
      simpa using hc (θ y) (Subgroup.mem_map_of_mem _ hy)) (fun h => hne (by simp [h]))
    exact ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩
  fusion x hx hx2 := by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy2 : orderOf y = 2 := by
      rw [← hx2]
      exact (orderOf_injective θ.toMonoidHom θ.injective y).symm
    obtain ⟨i, hi, hch⟩ := D.fusion y hy hy2
    refine ⟨θ i, ?_, unOut_chain_map θ hch⟩
    rcases hi with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  V_le := Subgroup.map_mono D.V_le
  V_ab a ha b hb := by
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    simp only [← map_mul, D.V_ab a₀ ha₀ b₀ hb₀]
  V_sq a ha := by
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow]
    simp [D.V_sq a₀ ha₀]
  V_zt := ⟨Subgroup.mem_map_of_mem _ D.V_zt.1, Subgroup.mem_map_of_mem _ D.V_zt.2⟩
  V_eq := by
    rw [unOut_centerOf_pCoreOf_map, ← D.V_eq]
  V_unique E hE hab hsq hcard := by
    set E₀ := E.comap θ.toMonoidHom with hE₀
    have hmem : ∀ x : Mb, x ∈ E₀ ↔ θ x ∈ E := fun x => Iff.rfl
    have hE₀T : E₀ ≤ T := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hE ((hmem x).1 hx))
      rwa [← θ.injective hyx]
    have hcE : Nat.card ↥E = Nat.card ↥E₀ := by
      conv_lhs => rw [← unOut_map_comap θ E]
      exact card_map_eq θ E₀
    have hcard₀ : Nat.card ↥E₀ = Nat.card ↥V := by
      rw [← hcE, hcard, card_map_eq]
    have hE₀V := D.V_unique E₀ hE₀T (fun a ha b hb => θ.injective (by
        rw [map_mul, map_mul]
        exact hab _ ((hmem a).1 ha) _ ((hmem b).1 hb))) (fun a ha => θ.injective (by
        rw [map_pow, map_one]
        exact hsq _ ((hmem a).1 ha))) hcard₀
    rw [← unOut_map_comap θ E]
    exact congrArg (Subgroup.map θ.toMonoidHom) hE₀V
  f_mem := Subgroup.mem_map_of_mem _ D.f_mem
  f_not := fun h => D.f_not (by simpa using (Subgroup.mem_map_iff_mem θ.injective).1 h)
  f_sq := by rw [← map_pow, D.f_sq, map_one]
  Tf_lt_z := by
    rw [spTf_map, map_centralizer_singleton θ z, ← Subgroup.map_inf_eq _ _ _ θ.injective,
      card_map_eq, card_map_eq]
    exact D.Tf_lt_z
  Tf_lt_t := by
    rw [spTf_map, map_centralizer_singleton θ t, ← Subgroup.map_inf_eq _ _ _ θ.injective,
      card_map_eq, card_map_eq]
    exact D.Tf_lt_t
  Sylow_Tf := by
    rw [spTf_map, map_centralizer_singleton θ f, ← Subgroup.map_inf_eq _ _ _ θ.injective]
    exact (isSylowTwoOf_map_mulEquiv θ).2 D.Sylow_Tf
  W_le := by
    rw [spWf_map]
    exact Subgroup.map_mono D.W_le
  W_ne := by
    obtain ⟨x, hx, hxZ, hx1⟩ := D.W_ne
    refine ⟨θ x, ?_, ?_, fun h => hx1 (θ.injective (by simpa using h))⟩
    · rw [spWf_map]
      exact Subgroup.mem_map_of_mem _ hx
    · rw [unOut_centerOf_perfectCore_map]
      exact Subgroup.mem_map_of_mem _ hxZ
  W_cls y hy hc := by
    rw [spWf_map] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
    rw [unOut_centerOf_perfectCore_map]
    exact Subgroup.mem_map_of_mem _ (D.W_cls y₀ hy₀ ((isConj_map_iff θ).1 hc))

end CFSG.Quasithin.H13.F431.Un

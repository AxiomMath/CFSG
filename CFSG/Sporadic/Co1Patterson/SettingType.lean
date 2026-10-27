module

public import CFSG.Sporadic.Co1Patterson.Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GroupTheory.WeirSylow

theorem q₀_apply (v : Fin 8 → ZMod 2) :
    q₀ v = ∑ i : Fin 4, v (Fin.castAdd 4 i) * v (Fin.natAdd 4 i) := by
  simp [q₀, QuadraticMap.linMulLin_apply]

@[expose] noncomputable def plusCoords :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv

theorem quadPlus_plusCoords (v : Fin 8 → ZMod 2) :
    CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) (plusCoords v) = q₀ v := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply, q₀_apply]
  simp only [plusCoords, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Fin.sum_univ_four]
  rfl

@[expose] noncomputable def q₀IsometryQuadPlus :
    q₀.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) where
  toLinearEquiv := plusCoords
  map_app' := quadPlus_plusCoords

theorem isPlusType_q₀ : IsPlusType q₀ :=
  (isPlusType_congr q₀IsometryQuadPlus).2 (isPlusType_quadPlus (ZMod 2) 4)

theorem nondegenerate_q₀ : q₀.polarBilin.Nondegenerate := by
  rw [Bridge.polarBilin_nondegenerate_iff]
  exact Bridge.nondegenerate_of_map q₀IsometryQuadPlus.symm.toLinearEquiv
    (fun v => q₀IsometryQuadPlus.symm.map_app v)
    ((Bridge.polarBilin_nondegenerate_iff _).1
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)))

theorem finrank_V₀ : finrank (ZMod 2) (Fin 8 → ZMod 2) = 2 * 4 := by
  rw [Module.finrank_fin_fun]

theorem L₀_eq_omegaGroup :
    L₀ = CFSG.RankThree.OrthogonalInvolutions.omegaGroup q₀ nondegenerate_q₀ :=
  s12_timmesfeldOmega_eq q₀ nondegenerate_q₀

theorem card_L₀ : Nat.card L₀ = 174182400 := by
  rw [L₀_eq_omegaGroup]
  have h2 := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_eq nondegenerate_q₀
  rcases natCard_orthogonalGroup_of_finrank_eight nondegenerate_q₀ (by rw [Module.finrank_fin_fun])
    with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · exact absurd isPlusType_q₀ h

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

@[expose] noncomputable def isometryV₀ (hw : S.width = 4) (hp : IsPlusType S.q) :
    S.q.IsometryEquiv q₀ :=
  Classical.choice (nonempty_isometry_of_isPlusType_iff S.q_nondegenerate nondegenerate_q₀
    (by rw [S.finrank_Qt_eq_two_mul_width, hw]) finrank_V₀ (iff_of_true hp isPlusType_q₀))

theorem conj_ρ_mem_L₀ (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) :
    Bridge.conjLinearEquiv ι.toLinearEquiv ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ L₀ := by
  have hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ timmesfeldOmega S.q := by
    rw [← hΩ]
    exact ⟨S.ρ m, ⟨m, rfl⟩, rfl⟩
  rw [L₀, ← Bridge.omega_map ι.toLinearEquiv (fun v => ι.map_app v)]
  exact ⟨_, hm, rfl⟩

@[expose] noncomputable def phiV₀ (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) : S.M →* L₀ :=
  ((Bridge.conjLinearEquiv ι.toLinearEquiv).toMonoidHom.comp (S.O.subtype.comp S.ρ)).codRestrict
    L₀ (conj_ρ_mem_L₀ S ι hΩ)

theorem coe_phiV₀_apply (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) (v : Fin 8 → ZMod 2) :
    ((phiV₀ S ι hΩ m : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) v =
      ι (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (ι.symm v)) := rfl

theorem phiV₀_eq_one_iff (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) :
    phiV₀ S ι hΩ m = 1 ↔ (m : G) ∈ S.QG := by
  rw [← S.ρ_eq_one_iff]
  constructor
  · intro h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have h1 := congrArg (fun l : L₀ =>
      ((l : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (ι v)) h
    simp only [coe_phiV₀_apply, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h1
    rw [show ι.symm (ι v) = v from ι.symm_apply_apply v] at h1
    exact ι.injective h1
  · intro h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [coe_phiV₀_apply, h]
    simp

theorem phiV₀_surjective (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) :
    Function.Surjective (phiV₀ S ι hΩ) := by
  rintro ⟨l, hl⟩
  rw [L₀, ← Bridge.omega_map ι.toLinearEquiv (fun v => ι.map_app v), ← hΩ] at hl
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩ := hl
  exact ⟨m, rfl⟩

theorem card_Mbar_of_card (hM : Nat.card S.M = 89181388800) (hQ : Nat.card S.Q = 2 ^ 9) :
    Nat.card S.Mbar = 174182400 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S.Q
  rw [Nat.card_congr S.quotientEquivMbar.toEquiv, hM, hQ] at h1
  omega

theorem nonempty_Mbar_equiv_omegaPlus (hw : S.width = 4) (hM : Nat.card S.Mbar = 174182400) :
    Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 4) := by
  obtain ⟨hp, hΩ⟩ := isPlusType_and_map_eq_omegaGroup_of_card S.q_nondegenerate
    (finrank_Qt_of_width_four S hw) S.Mbar hM
  obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus S.q_nondegenerate
    (by rw [S.finrank_Qt_eq_two_mul_width, hw]) (by norm_num) hp
  exact ⟨((Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hΩ)).trans e⟩

@[expose] noncomputable def typeSystemOf (ι : S.q.IsometryEquiv q₀)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ S.M where
  φ := phiV₀ S ι hΩ
  φ_surj := phiV₀_surjective S ι hΩ
  z := S.zM
  vec m := ι (S.cl (m : G))
  z_mul_self := Subtype.ext S.z_mul_z
  z_ne_one h := S.z_ne_one (congrArg Subtype.val h)
  z_comm c := Subtype.ext (S.z_comm c.2)
  φ_z := (phiV₀_eq_one_iff S ι hΩ _).2 S.z_mem_QG
  vec_mul p q hp hq := by
    rw [Subgroup.coe_mul, S.cl_mul ((phiV₀_eq_one_iff S ι hΩ p).1 hp)
      ((phiV₀_eq_one_iff S ι hΩ q).1 hq), map_add]
  vec_eq_zero q hq := by
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    have h0 : ι (S.cl (q : G)) = 0 ↔ S.cl (q : G) = 0 :=
      ⟨fun h => ι.injective (h.trans (map_zero ι).symm), fun h => by rw [h, map_zero]⟩
    rw [h0, S.cl_eq_zero_iff hq', Subtype.ext_iff, Subtype.ext_iff]
    rfl
  vec_conj c q hq := by
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    change ι (S.cl ((c : G) * q * (c : G)⁻¹)) =
      ((phiV₀ S ι hΩ c : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (ι (S.cl (q : G)))
    rw [coe_phiV₀_apply, ι.symm_apply_apply, S.ρ_cl c hq']
  vec_surj w := by
    obtain ⟨x, hx, hxw⟩ := S.exists_cl (ι.symm w)
    refine ⟨⟨x, S.QG_le_M hx⟩, (phiV₀_eq_one_iff S ι hΩ _).2 hx, ?_⟩
    change ι (S.cl x) = w
    rw [hxw, ι.apply_symm_apply]
  mul_self_eq_one_iff q hq := by
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    rw [ι.map_app, S.q_cl_eq_zero_iff hq', Subtype.ext_iff, _root_.sq]
    rfl
  mul_self_eq_z_iff q hq := by
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    rw [ι.map_app, S.q_cl_eq_one_iff hq', Subtype.ext_iff]
    change (q : G) * q = S.z ↔ (q : G) ^ 2 ≠ 1
    rw [← _root_.sq]
    rcases S.sq_eq_one_or_z hq' with h | h <;> rw [h]
    · exact ⟨fun h1 => absurd h1.symm S.z_ne_one, fun h1 => absurd rfl h1⟩
    · exact ⟨fun _ => S.z_ne_one, fun _ => rfl⟩
  comm_eq_one_iff p q hp hq := by
    have hp' := (phiV₀_eq_one_iff S ι hΩ p).1 hp
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    change _ ↔ QuadraticMap.polar q₀ (ι.toLinearEquiv (S.cl (p : G)))
      (ι.toLinearEquiv (S.cl (q : G))) = 0
    rw [Bridge.polar_map ι.toLinearEquiv (fun v => ι.map_app v), S.polar_cl_eq_zero_iff hp' hq',
      ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm, Subtype.ext_iff]
    rfl
  comm_eq_z_iff p q hp hq := by
    have hp' := (phiV₀_eq_one_iff S ι hΩ p).1 hp
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    change _ ↔ QuadraticMap.polar q₀ (ι.toLinearEquiv (S.cl (p : G)))
      (ι.toLinearEquiv (S.cl (q : G))) = 1
    rw [Bridge.polar_map ι.toLinearEquiv (fun v => ι.map_app v), S.polar_cl_eq_one_iff hp' hq',
      Subtype.ext_iff]
    change (p : G) * q * (p : G)⁻¹ * (q : G)⁻¹ = S.z ↔ _
    rcases S.commutator_eq_one_or_z hp' hq' with h | h <;> rw [h]
    · refine ⟨fun h1 => absurd h1.symm S.z_ne_one, fun h1 => absurd ?_ h1⟩
      calc (p : G) * q = (p : G) * q * (p : G)⁻¹ * (q : G)⁻¹ * (q * p) := by group
        _ = q * p := by rw [h, one_mul]
    · refine ⟨fun _ h1 => S.z_ne_one ?_, fun _ => rfl⟩
      calc S.z = (p : G) * q * (p : G)⁻¹ * (q : G)⁻¹ := h.symm
        _ = 1 := by rw [h1]; group
  center_eq q hq hcomm := by
    have hq' := (phiV₀_eq_one_iff S ι hΩ q).1 hq
    have h := S.eq_one_or_z_of_commute hq' fun y hy =>
      (congrArg Subtype.val (hcomm ⟨y, S.QG_le_M hy⟩ ((phiV₀_eq_one_iff S ι hΩ _).2 hy))).symm
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h

@[expose] noncomputable def typeSystem (hw : S.width = 4)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (hp : IsPlusType S.q) :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ S.M :=
  typeSystemOf S (isometryV₀ S hw hp) hΩ

end Setting

@[expose] noncomputable def typeSystemOfHyp {X : Type} [Group X] [Finite X] {t : X}
    (h : PattersonCo1Hyp X t) :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ (centralizer ({t} : Set X)) :=
  Setting.typeSystem (setting h) (width_setting h) (Mbar_map_eq_omega h) (isPlusType h)

end CFSG.Sporadic.Co1Patterson

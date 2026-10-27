module

public import CFSG.Sporadic.SuzRecog.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.LargeExtraspecial.BridgeForms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial
  CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.GroupTheory.WeirSylow

theorem not_isPlusType_qMinusForm : ¬ IsPlusType qMinusForm := by
  rintro ⟨W, hW, hWs⟩
  rw [finrank_fin_six] at hW
  obtain ⟨u, hu, hu0⟩ := SuzB0.exists_qMinusForm_ne_zero SuzB0.b0_parts.2.2.2.2.2.2 W (by omega)
  exact hu0 (hWs u hu)

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

theorem not_isPlusType (hw : S.width = 3)
    (hE : ¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) :
    ¬ IsPlusType S.q := by
  rintro ⟨W, hW, hWs⟩
  rw [S.finrank_Qt_eq_two_mul_width, hw] at hW
  refine hE ⟨S.clPre W, S.clPre_le_QG W, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨ha, haW⟩ := S.mem_clPre.mp a.2
    obtain ⟨hb, hbW⟩ := S.mem_clPre.mp b.2
    refine (S.polar_cl_eq_zero_iff ha hb).mp ?_
    rw [polar, hWs _ (W.add_mem haW hbW), hWs _ haW, hWs _ hbW, sub_zero, sub_zero]
  · obtain ⟨hxQ, hxW⟩ := S.mem_clPre.mp hx
    exact (S.q_cl_eq_zero_iff hxQ).mp (hWs _ hxW)
  · rw [S.card_clPre, S.card_submodule]
    have : finrank (ZMod 2) W = 3 := by omega
    rw [this]
    norm_num

@[expose] noncomputable def isometryM (hw : S.width = 3)
    (hp : ¬ IsPlusType S.q) : S.q.IsometryEquiv qMinusForm :=
  Classical.choice (nonempty_isometry_of_isPlusType_iff S.q_nondegenerate
    qMinusForm_nondegenerate (n := 3) (by rw [S.finrank_Qt_eq_two_mul_width, hw])
    (by rw [finrank_fin_six]) (iff_of_false hp not_isPlusType_qMinusForm))

theorem conj_ρ_mem_Lm (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) :
    Bridge.conjLinearEquiv ι.toLinearEquiv ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Lm := by
  have hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ timmesfeldOmega S.q := by
    rw [← hΩ]
    exact ⟨S.ρ m, ⟨m, rfl⟩, rfl⟩
  rw [Lm, ← coe_qMinusForm, ← Bridge.omega_map ι.toLinearEquiv (fun v => ι.map_app v)]
  exact ⟨_, hm, rfl⟩

@[expose] noncomputable def phiM (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) : S.M →* Lm :=
  ((Bridge.conjLinearEquiv ι.toLinearEquiv).toMonoidHom.comp (S.O.subtype.comp S.ρ)).codRestrict
    Lm (conj_ρ_mem_Lm S ι hΩ)

theorem coe_phiM_apply (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) (v : Fin 6 → ZMod 2) :
    ((phiM S ι hΩ m : Lm) : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) v =
      ι (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (ι.symm v)) := rfl

theorem phiM_eq_one_iff (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) (m : S.M) :
    phiM S ι hΩ m = 1 ↔ (m : G) ∈ S.QG := by
  rw [← S.ρ_eq_one_iff]
  constructor
  · intro h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have h1 := congrArg (fun l : Lm =>
      ((l : Lm) : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) (ι v)) h
    simp only [coe_phiM_apply, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h1
    rw [show ι.symm (ι v) = v from ι.symm_apply_apply v] at h1
    exact ι.injective h1
  · intro h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [coe_phiM_apply, h]
    simp

theorem phiM_surjective (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) :
    Function.Surjective (phiM S ι hΩ) := by
  rintro ⟨l, hl⟩
  rw [Lm, ← coe_qMinusForm, ← Bridge.omega_map ι.toLinearEquiv (fun v => ι.map_app v), ← hΩ]
    at hl
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩ := hl
  exact ⟨m, rfl⟩

theorem qMinus_isometry (ι : S.q.IsometryEquiv qMinusForm) (x : S.Qt) : qMinus (ι x) = S.q x := by
  rw [← qMinusForm_apply, ι.map_app]

@[expose] noncomputable def typeSystemOf (ι : S.q.IsometryEquiv qMinusForm)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) : SuzType S.M where
  φ := phiM S ι hΩ
  φ_surj := phiM_surjective S ι hΩ
  z := S.zM
  vec m := ι (S.cl (m : G))
  z_mul_self := Subtype.ext S.z_mul_z
  z_ne_one h := S.z_ne_one (congrArg Subtype.val h)
  z_comm c := Subtype.ext (S.z_comm c.2)
  φ_z := (phiM_eq_one_iff S ι hΩ _).2 S.z_mem_QG
  vec_mul p q hp hq := by
    rw [Subgroup.coe_mul, S.cl_mul ((phiM_eq_one_iff S ι hΩ p).1 hp)
      ((phiM_eq_one_iff S ι hΩ q).1 hq), map_add]
  vec_eq_zero q hq := by
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    have h0 : ι (S.cl (q : G)) = 0 ↔ S.cl (q : G) = 0 :=
      ⟨fun h => ι.injective (h.trans (map_zero ι).symm), fun h => by rw [h, map_zero]⟩
    rw [h0, S.cl_eq_zero_iff hq', Subtype.ext_iff, Subtype.ext_iff]
    rfl
  vec_conj c q hq := by
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    change ι (S.cl ((c : G) * q * (c : G)⁻¹)) =
      ((phiM S ι hΩ c : Lm) : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) (ι (S.cl (q : G)))
    rw [coe_phiM_apply, ι.symm_apply_apply, S.ρ_cl c hq']
  vec_surj w := by
    obtain ⟨x, hx, hxw⟩ := S.exists_cl (ι.symm w)
    refine ⟨⟨x, S.QG_le_M hx⟩, (phiM_eq_one_iff S ι hΩ _).2 hx, ?_⟩
    change ι (S.cl x) = w
    rw [hxw, ι.apply_symm_apply]
  mul_self_eq_one_iff q hq := by
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    rw [qMinus_isometry, S.q_cl_eq_zero_iff hq', Subtype.ext_iff, _root_.sq]
    rfl
  mul_self_eq_z_iff q hq := by
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    rw [qMinus_isometry, S.q_cl_eq_one_iff hq', Subtype.ext_iff]
    change (q : G) * q = S.z ↔ (q : G) ^ 2 ≠ 1
    rw [← _root_.sq]
    rcases S.sq_eq_one_or_z hq' with h | h <;> rw [h]
    · exact ⟨fun h1 => absurd h1.symm S.z_ne_one, fun h1 => absurd rfl h1⟩
    · exact ⟨fun _ => S.z_ne_one, fun _ => rfl⟩
  comm_eq_one_iff p q hp hq := by
    have hp' := (phiM_eq_one_iff S ι hΩ p).1 hp
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    change _ ↔ QuadraticMap.polar qMinusForm (ι.toLinearEquiv (S.cl (p : G)))
      (ι.toLinearEquiv (S.cl (q : G))) = 0
    rw [Bridge.polar_map ι.toLinearEquiv (fun v => ι.map_app v), S.polar_cl_eq_zero_iff hp' hq',
      ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm, Subtype.ext_iff]
    rfl
  comm_eq_z_iff p q hp hq := by
    have hp' := (phiM_eq_one_iff S ι hΩ p).1 hp
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    change _ ↔ QuadraticMap.polar qMinusForm (ι.toLinearEquiv (S.cl (p : G)))
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
    have hq' := (phiM_eq_one_iff S ι hΩ q).1 hq
    have h := S.eq_one_or_z_of_commute hq' fun y hy =>
      (congrArg Subtype.val (hcomm ⟨y, S.QG_le_M hy⟩ ((phiM_eq_one_iff S ι hΩ _).2 hy))).symm
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h

@[expose] noncomputable def typeSystem (hw : S.width = 3)
    (hE : ¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q) : SuzType S.M :=
  typeSystemOf S (isometryM S hw (not_isPlusType S hw hE)) hΩ

end Setting

end CFSG.Sporadic.SuzRecog

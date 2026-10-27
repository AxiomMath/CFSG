module

public import CFSG.Quasithin.Vol2.Ch11SecB414I
public import CFSG.Quasithin.Vol2.Ch11SecB414L
public import CFSG.Quasithin.Vol2.Ch11SecB414MP
public import CFSG.Quasithin.Vol2.Ch11SecB414Defs
public import CFSG.Quasithin.Vol2.Ch11SecB414G

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open Subgroup CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {Γ V Z L X : Subgroup G} {F : Type} [Field F]
  [Fintype F] {α : ↥Γ →* GL (Fin 3) F ⧸ center (GL (Fin 3) F)}
  {P : Subgroup (GL (Fin 3) F ⧸ center (GL (Fin 3) F))}

omit [Finite G] in
theorem Hyp.isElem (hyp : Hyp Γ V Z L X F α P) : IsElem V Z :=
  ⟨hyp.lt.le, hyp.sq_mem, hyp.comm_mem⟩

omit [Finite G] in
theorem Hyp.hker (hyp : Hyp Γ V Z L X F α P) :
    ∀ γ : ↥Γ, α γ = 1 → ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z :=
  fun γ h => (hyp.ker_iff γ).mp h

omit [Finite G] in
theorem Hyp.charP (hyp : Hyp Γ V Z L X F α P) : CharP F 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := 2) (by norm_num) (by rw [Nat.card_eq_fintype_card, hyp.card]; norm_num)

omit [Finite G] in
theorem Hyp.natCard (hyp : Hyp Γ V Z L X F α P) : Nat.card F = 4 := by
  rw [Nat.card_eq_fintype_card, hyp.card]

omit [Fintype F] in
theorem dTMat_eq_diagonal (r t : Fˣ) :
    (dTMat r t : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(r : F), (t : F), (((r * t)⁻¹ : Fˣ) : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dTMat]

omit [Fintype F] in
theorem mk_dT_mem_Ptheta (j : Fin 2) (r t : Fˣ) :
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (dT r t)) ∈ Ptheta F j := by
  have hT : dT r t ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1)) :=
    upperTriangular_le_stabilizer_flagSpace _ fun i k hki => by
      rw [dT_coe]
      fin_cases i <;> fin_cases k <;> simp [dTMat] at hki ⊢
  exact ⟨proj 3 F (dT r t), ⟨dT r t, hT, rfl⟩, thetaP_proj (dT r t)⟩

omit [Fintype F] in
theorem dGL_commute {ω : F} (h0 : ω ≠ 0) (t : Fˣ) :
    Commute (dGL ω h0) (Matrix.SpecialLinearGroup.toGL (dT 1 t)) := by
  apply Units.ext
  show Matrix.diagonal ![ω, 1, 1] * (dT 1 t : Matrix (Fin 3) (Fin 3) F) =
    (dT 1 t : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![ω, 1, 1]
  rw [dT_coe, dTMat_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

omit [Finite G] in
theorem Hyp.exists_sl (hyp : Hyp Γ V Z L X F α P) {γ : ↥Γ} (hγ : (γ : G) ∈ L) :
    ∃ s : SL(3, F), QuotientGroup.mk' (center (GL (Fin 3) F))
      (Matrix.SpecialLinearGroup.toGL s) = α γ := by
  have := hyp.charP
  have h1 : α γ ∈ perfectCore P := by
    rw [← hyp.map_L]
    exact ⟨γ, hγ, rfl⟩
  have h2 : perfectCore P ≤ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ :=
    (perfectCore_le_derivedSeriesOf P 1).trans (commutator_mono le_top le_top)
  rw [← range_thetaP_eq hyp.natCard] at h2
  obtain ⟨x, hx⟩ := h2 h1
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  exact ⟨s, (thetaP_proj s).symm.trans hx⟩

omit [Finite G] in
theorem Hyp.exists_conj_t₃ (hyp : Hyp Γ V Z L X F α P) (ω : Fˣ) :
    ∃ γ : ↥Γ, (γ : G) ∈ L ∧ ∃ s : SL(3, F), QuotientGroup.mk' (center (GL (Fin 3) F))
      (Matrix.SpecialLinearGroup.toGL (s⁻¹ * dT 1 ω * s)) = α γ := by
  have := hyp.charP
  obtain ⟨c, j, hc⟩ := M.exists_conj_perfectCore hyp.natCard hyp.maxParabolic
  have h1 := mk_dT_mem_Ptheta (F := F) j 1 ω
  rw [← hc] at h1
  obtain ⟨p, hp, hpc⟩ := h1
  have hp' : p ∈ (L.subgroupOf Γ).map α := by
    rw [hyp.map_L]
    exact hp
  obtain ⟨γ, hγL, rfl⟩ := hp'
  refine ⟨γ, hγL, ?_⟩
  obtain ⟨c', rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective c
  obtain ⟨ω', h0, h1⟩ := exists_ne_zero_ne_one hyp.card
  have hdet0 : (c' : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det c').ne_zero
  obtain ⟨i, -, hci⟩ := exists_pow_eq hyp.card h0 h1 hdet0
  set d := dGL ω' h0 with hd
  have hs : (((d ^ i)⁻¹ * c' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hci, ← Matrix.GeneralLinearGroup.val_det_apply,
      map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, hd,
      det_dGL_pow]
    exact inv_mul_cancel₀ (pow_ne_zero i h0)
  let s : SL(3, F) := ⟨_, hs⟩
  have hsc : Matrix.SpecialLinearGroup.toGL s = (d ^ i)⁻¹ * c' := Units.ext rfl
  refine ⟨s, ?_⟩
  have hcd : c' = d ^ i * Matrix.SpecialLinearGroup.toGL s := by
    rw [hsc, mul_inv_cancel_left]
  have hcomm : Commute (d ^ i) (Matrix.SpecialLinearGroup.toGL (dT 1 ω)) :=
    (dGL_commute h0 ω).pow_left i
  have hkey : c'⁻¹ * Matrix.SpecialLinearGroup.toGL (dT 1 ω) * c' =
      Matrix.SpecialLinearGroup.toGL (s⁻¹ * dT 1 ω * s) := by
    have h3 : (d ^ i)⁻¹ * Matrix.SpecialLinearGroup.toGL (dT 1 ω) * d ^ i =
        Matrix.SpecialLinearGroup.toGL (dT 1 ω) := by
      rw [mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [map_mul, map_mul, map_inv, hcd, mul_inv_rev]
    calc (Matrix.SpecialLinearGroup.toGL s)⁻¹ * (d ^ i)⁻¹ *
          Matrix.SpecialLinearGroup.toGL (dT 1 ω) * (d ^ i * Matrix.SpecialLinearGroup.toGL s) =
        (Matrix.SpecialLinearGroup.toGL s)⁻¹ * ((d ^ i)⁻¹ *
          Matrix.SpecialLinearGroup.toGL (dT 1 ω) * d ^ i) *
          Matrix.SpecialLinearGroup.toGL s := by simp only [mul_assoc]
      _ = _ := by rw [h3]
  have hαγ : α γ = QuotientGroup.mk' (center (GL (Fin 3) F))
      (c'⁻¹ * Matrix.SpecialLinearGroup.toGL (dT 1 ω) * c') := by
    have h : QuotientGroup.mk' (center (GL (Fin 3) F)) c' * α γ *
        (QuotientGroup.mk' (center (GL (Fin 3) F)) c')⁻¹ =
        QuotientGroup.mk' (center (GL (Fin 3) F)) (Matrix.SpecialLinearGroup.toGL (dT 1 ω)) :=
      hpc
    rw [map_mul, map_mul, map_inv, ← h]
    group
  rw [hkey] at hαγ
  exact hαγ.symm

omit [Fintype F] in
theorem dT_one_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) : (dT 1 ω : SL(3, F)) ^ 3 = 1 := by
  have h : ω * ω * ω = 1 := by rw [← pow_two, ← pow_succ, hω3]
  rw [pow_succ, pow_two, dT_mul, dT_mul, one_mul, one_mul, h, dT_one]

theorem Hyp.exists_card_eq_fix (hyp : Hyp Γ V Z L X F α P) [Fact (IsElem V Z)] {ω : Fˣ}
    (hω3 : ω ^ 3 = 1) (W : Submodule (ZMod 2) (SecU V Z))
    (hW : ∀ s : SL(3, F), ∀ u ∈ W,
      slRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker s u ∈ W) :
    ∃ m, Nat.card W = Nat.card {u : W //
      slRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker (dT 1 ω) u = u} *
        16 ^ m := by
  set ρ := slRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker with hρ
  set σ := secRep V Z Γ hyp.le_normalizer_V hyp.le_normalizer_Z with hσ
  obtain ⟨γ, hγL, s, hs⟩ := hyp.exists_conj_t₃ ω
  have hγρ : σ γ = ρ (s⁻¹ * dT 1 ω * s) :=
    (glRep_eq hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hs).symm
  have hγ3 : σ (γ ^ 3) = 1 := by
    have hc : (s⁻¹ * dT 1 ω * s) ^ 3 = s⁻¹ * dT 1 ω ^ 3 * s := by
      have h := conj_pow (a := s⁻¹) (b := dT 1 ω) (i := 3)
      rw [inv_inv] at h
      exact h
    rw [map_pow, hγρ, ← map_pow, hc, dT_one_pow_three hω3, mul_one, inv_mul_cancel, map_one]
  have ht : ∀ u, (σ γ).toAddMonoidHom ((σ γ).toAddMonoidHom ((σ γ).toAddMonoidHom u)) = u := by
    intro u
    have h := congrArg (fun f => f u) hγ3
    simpa [map_pow, pow_succ, Module.End.mul_apply] using h
  have hL : ∀ l : ↥Γ, (l : G) ∈ L → ∀ u ∈ W.toAddSubgroup, σ l u ∈ W.toAddSubgroup := by
    intro l hl u hu
    obtain ⟨s', hs'⟩ := hyp.exists_sl hl
    rw [show σ l = ρ s' from
      (glRep_eq hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hs').symm]
    exact hW s' u hu
  obtain ⟨m, hm⟩ := exists_card_eq_mul_pow (σ γ).toAddMonoidHom ht
    (fun A => ∀ l : ↥Γ, (l : G) ∈ L → ∀ u ∈ A, σ l u ∈ A)
    (fun A hA a ha => hA γ hγL a ha) (fun l _ u hu => by
      rw [(AddSubgroup.mem_bot).mp hu, map_zero]
      exact AddSubgroup.zero_mem _)
    (fun A B hA hB hBA hch => card_chief hyp.le_normalizer_V hyp.le_normalizer_Z hyp.le_L
      hyp.card hyp.natural hγL hγ3 hA hB hBA hch) W.toAddSubgroup hL
  refine ⟨m, ?_⟩
  have e : Nat.card (fixRel (σ γ).toAddMonoidHom ⊥ W.toAddSubgroup) =
      Nat.card {u : W // ρ (dT 1 ω) u = u} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨ρ s x, hW s x x.2.1⟩, ?_⟩
        invFun := fun y => ⟨ρ s⁻¹ (y : W), hW s⁻¹ _ (y : W).2, ?_⟩
        left_inv := fun x => ?_
        right_inv := fun y => ?_ }
    · have h1 : ρ (s⁻¹ * dT 1 ω * s) (x : SecU V Z) = x := by
        rw [← hγρ]
        exact sub_eq_zero.mp ((AddSubgroup.mem_bot).mp x.2.2)
      show ρ (dT 1 ω) (ρ s x) = ρ s x
      rw [← Module.End.mul_apply, ← map_mul,
        show dT 1 ω * s = s * (s⁻¹ * dT 1 ω * s) by group, map_mul, Module.End.mul_apply, h1]
    · refine (AddSubgroup.mem_bot).mpr (sub_eq_zero.mpr ?_)
      show σ γ (ρ s⁻¹ (y : W)) = ρ s⁻¹ (y : W)
      rw [hγρ, ← Module.End.mul_apply, ← map_mul,
        show s⁻¹ * dT 1 ω * s * s⁻¹ = s⁻¹ * dT 1 ω by group, map_mul, Module.End.mul_apply, y.2]
    · apply Subtype.ext
      show ρ s⁻¹ (ρ s x) = x
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · apply Subtype.ext
      apply Subtype.ext
      show ρ s (ρ s⁻¹ (y : W)) = (y : W)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← e]
  exact hm

end CFSG.Quasithin.H13.Ch4.B414

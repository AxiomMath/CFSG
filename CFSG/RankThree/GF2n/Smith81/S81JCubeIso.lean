module

public import CFSG.RankThree.GF2n.Smith81.S81JZero

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def twist (σ : K ≃+* K) : GL (Fin 6) K →* GL (Fin 6) K :=
  Units.map (σ.mapMatrix : Matrix (Fin 6) (Fin 6) K ≃+* Matrix (Fin 6) (Fin 6) K).toRingHom.toMonoidHom

theorem twist_val (σ : K ≃+* K) (h : GL (Fin 6) K) :
    ((twist σ h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (h : Matrix (Fin 6) (Fin 6) K).map σ := by
  rw [twist, Units.coe_map]
  rfl

theorem det_twist (σ : K ≃+* K) (h : GL (Fin 6) K) :
    ((twist σ h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det =
      σ ((h : Matrix (Fin 6) (Fin 6) K).det) := by
  rw [twist_val]
  exact (RingEquiv.map_det σ _).symm

theorem twist_tr (σ : K ≃+* K) {a b : Fin 6} (hab : a ≠ b) (t : K) :
    twist σ (transvGL K a b hab t) = transvGL K a b hab (σ t) := by
  apply Units.ext
  rw [twist_val, transvGL_val, transvGL_val]
  ext i j
  simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem S0_eq_Wc : S0 K = Wc K ({0, 2, 4} : Finset (Fin 6)) := by
  have hiff : ∀ i : Fin 6, i ∉ ({0, 2, 4} : Finset (Fin 6)) ↔ i.val % 2 = 1 := by decide
  refine Submodule.ext fun v => ?_
  rw [s81A12_mem_S0, mem_Wc]
  exact ⟨fun h i hi => h i ((hiff i).1 hi), fun h j hj => h j ((hiff j).2 hj)⟩

private theorem cbA_span_basis {W : Submodule K (Fin 6 → K)} {n : ℕ}
    (b : Module.Basis (Fin n) K W) :
    W = Submodule.span K (Set.range fun i => (b i : Fin 6 → K)) := by
  refine Eq.symm ?_
  have h1 : Submodule.map W.subtype (Submodule.span K (Set.range b)) = W := by
    rw [b.span_eq, Submodule.map_subtype_top]
  rw [Submodule.map_span] at h1
  refine Eq.trans ?_ h1
  congr 1
  rw [← Set.range_comp]
  rfl

private theorem cbA_det_conj (g₀ g : GL (Fin 6) K)
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) :
    ((g₀ * g * g₀⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  have h : (g₀ : Matrix (Fin 6) (Fin 6) K).det *
      ((g₀⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hg]
  linear_combination h

theorem exists_sl_map_eq [Finite K] {W W' : Submodule K (Fin 6 → K)} (hW : finrank K W = 3)
    (hW' : finrank K W' = 3) : ∃ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      W.map (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K)) = W' := by
  let bW := Module.finBasisOfFinrankEq K W hW
  let bW' := Module.finBasisOfFinrankEq K W' hW'
  have hv : LinearIndependent K (fun i => (bW i : Fin 6 → K)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hw : LinearIndependent K (fun i => (bW' i : Fin 6 → K)) :=
    bW'.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  obtain ⟨g, hdet, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6) hv hw
  have hg0 : g.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0, hdet, ?_⟩
  have hGval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0 : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = g := rfl
  have hcomp : (⇑(Matrix.mulVecLin g) ∘ fun i => (bW i : Fin 6 → K)) =
      fun i => (bW' i : Fin 6 → K) := funext fun i => hgv i
  rw [hGval, cbA_span_basis bW, cbA_span_basis bW', Submodule.map_span, ← Set.range_comp, hcomp]

namespace SLAct

variable [CharP K 2] (A : SLAct K V)

def conj (g₀ : GL (Fin 6) K) : SLAct K V where
  act h := A.act (g₀ * h * g₀⁻¹)
  act_one := by
    show A.act (g₀ * 1 * g₀⁻¹) = 1
    rw [mul_one, mul_inv_cancel, A.act_one]
  act_mul := by
    intro g h hg hh
    show A.act (g₀ * (g * h) * g₀⁻¹) = A.act (g₀ * g * g₀⁻¹) * A.act (g₀ * h * g₀⁻¹)
    rw [show g₀ * (g * h) * g₀⁻¹ = g₀ * g * g₀⁻¹ * (g₀ * h * g₀⁻¹) by group,
      A.act_mul _ _ (cbA_det_conj g₀ g hg) (cbA_det_conj g₀ h hh)]

theorem Fix_conj {g₀ : GL (Fin 6) K} (hg₀ : (g₀ : Matrix (Fin 6) (Fin 6) K).det = 1)
    (W : Submodule K (Fin 6 → K)) :
    (A.conj g₀).Fix W = A.Fix (W.map (Matrix.mulVecLin (g₀ : Matrix (Fin 6) (Fin 6) K))) := by
  ext v
  rw [(A.conj g₀).mem_Fix, A.mem_Fix]
  constructor
  · intro hv u' hu'
    have key : A.act (g₀ * (g₀⁻¹ * u' * g₀) * g₀⁻¹) v = v :=
      hv (g₀⁻¹ * u' * g₀) (s81A12_conj_mem_inv g₀ W hu')
    rwa [show g₀ * (g₀⁻¹ * u' * g₀) * g₀⁻¹ = u' by group] at key
  · intro hv u hu
    exact hv (g₀ * u * g₀⁻¹) (s81A12_conj_mem g₀ W hu)

structure RankOneRel (v₀ : V) (g : K ≃+* K) : Prop where
  hX : ∀ t, A.X t (A.act (pm K (Equiv.swap 0 3)) v₀) = A.act (pm K (Equiv.swap 0 3)) v₀ + g t • v₀
  hY : ∀ t, A.Y t v₀ = v₀ + g t • A.act (pm K (Equiv.swap 0 3)) v₀

theorem act_tr_vI_fix {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) {a b : Fin 6} (hab : a ≠ b)
    (t : K) {I : Finset (Fin 6)} (hI : I.card = 3) (h : b ∈ I → a ∈ I) :
    A.act (transvGL K a b hab t) (A.vI v₀ I) = A.vI v₀ I := by
  have hW : finrank K (A.Fix (Wc K I)) = 1 := A.finrank_Fix_Wc S.h0 hI
  have hpW : ∀ w ∈ Wc K I,
      ((transvGL K a b hab t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ Wc K I :=
    fun w hw => tr_Wc_stable hab t h hw
  exact A.act_invol_fix (det_tr hab t) (tr_sq hab t) hpW hW _ (A.vI_mem S.h0 S.hv₀ hI)

theorem act_tr_vI_move {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) {g : K ≃+* K}
    (R : A.RankOneRel v₀ g) {a b : Fin 6} (hab : a ≠ b) (t : K) {I : Finset (Fin 6)}
    (hI : I.card = 3) (hb : b ∈ I) (ha : a ∉ I) :
    A.act (transvGL K a b hab t) (A.vI v₀ I) =
      A.vI v₀ I + g t • A.vI v₀ (insert a (I.erase b)) := by
  obtain ⟨σ, hσI, hb0, ha3⟩ := exists_perm_pair I hI hb ha
  subst hb0
  subst ha3
  subst hσI
  have h30 : (3 : Fin 6) ≠ 0 := by decide
  have hset : insert (σ 3) ((I0.image σ).erase (σ 0)) =
      I0.image (σ * Equiv.swap (0 : Fin 6) 3) := by
    have h01 : σ 1 ≠ σ 0 := σ.injective.ne (show (1 : Fin 6) ≠ 0 by decide)
    have h02 : σ 2 ≠ σ 0 := σ.injective.ne (show (2 : Fin 6) ≠ 0 by decide)
    have e1 : I0.image σ = insert (σ 0) (insert (σ 1) {σ 2}) := by
      rw [I0, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    have s0 : (σ * Equiv.swap (0 : Fin 6) 3) 0 = σ 3 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have s1 : (σ * Equiv.swap (0 : Fin 6) 3) 1 = σ 1 := by
      rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 6) ≠ 0 by decide)
          (show (1 : Fin 6) ≠ 3 by decide)]
    have s2 : (σ * Equiv.swap (0 : Fin 6) 3) 2 = σ 2 := by
      rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 6) ≠ 0 by decide)
          (show (2 : Fin 6) ≠ 3 by decide)]
    have e2 : I0.image (σ * Equiv.swap (0 : Fin 6) 3) = insert (σ 3) (insert (σ 1) {σ 2}) := by
      rw [I0, Finset.image_insert, Finset.image_insert, Finset.image_singleton, s0, s1, s2]
    have hn : σ 0 ∉ (insert (σ 1) {σ 2} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => h01 h.symm, fun h => h02 h.symm⟩
    rw [e1, e2, Finset.erase_insert hn]
  have hvI : A.vI v₀ (I0.image σ) = A.act (pm K σ) v₀ := (vI_eq A S.h0 S.hv₀ σ).symm
  have hconj : transvGL K (σ 3) (σ 0) hab t = pm K σ * transvGL K 3 0 h30 t * (pm K σ)⁻¹ :=
    (pm_conj_tr σ h30 t).symm
  have hτ : A.act (pm K (σ * Equiv.swap (0 : Fin 6) 3)) v₀ =
      A.act (pm K σ) (A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀) := by
    rw [map_mul, A.act_mul (pm K σ) (pm K (Equiv.swap (0 : Fin 6) 3)) (det_pm σ) (det_pm _),
      Module.End.mul_apply]
  have hY : A.act (transvGL K 3 0 h30 t) v₀ =
      v₀ + g t • A.act (pm K (Equiv.swap (0 : Fin 6) 3)) v₀ := R.hY t
  rw [hvI, hset, ← vI_eq A S.h0 S.hv₀ (σ * Equiv.swap (0 : Fin 6) 3), hτ, hconj,
    A.actA_conj_apply (det_pm σ) (det_tr h30 t) v₀, hY, map_add, map_smul]

noncomputable def Phi (v₀ : V) : Cube K →ₗ[K] V :=
  (cubeBasis K).constr K (fun I => A.vI v₀ I.1)

theorem Phi_cubeBasis (v₀ : V) (I : Set.powersetCard (Fin 6) 3) :
    A.Phi v₀ (cubeBasis K I) = A.vI v₀ I.1 := by
  unfold Phi
  rw [Module.Basis.constr_basis]

theorem Phi_rho_adj {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) {g : K ≃+* K}
    (R : A.RankOneRel v₀ g) {a b : Fin 6} (hne : a ≠ b)
    (hadj : a.val + 1 = b.val ∨ b.val + 1 = a.val) (c : K) (x : Cube K) :
    A.Phi v₀ (rho K (transvGL K a b hne c) x) =
      A.act (transvGL K a b hne (g.symm c)) (A.Phi v₀ x) := by
  have key : (A.Phi v₀).comp (rho K (transvGL K a b hne c)) =
      (A.act (transvGL K a b hne (g.symm c))).comp (A.Phi v₀) := by
    refine (cubeBasis K).ext fun I => ?_
    simp only [LinearMap.comp_apply]
    rw [rho_transvGL_cubeBasis hadj hne c I]
    by_cases h : b ∈ I.1 ∧ a ∉ I.1
    · have hI : I.1.card = 3 := I.2
      rw [dif_pos h]
      simp only [map_add, map_smul, Phi_cubeBasis]
      rw [A.act_tr_vI_move S R hne (g.symm c) hI h.1 h.2, RingEquiv.apply_symm_apply]
      rfl
    · have hI : I.1.card = 3 := I.2
      have hfix : b ∈ I.1 → a ∈ I.1 := fun hb => by
        by_contra ha
        exact h ⟨hb, ha⟩
      rw [dif_neg h]
      simp only [Phi_cubeBasis]
      rw [A.act_tr_vI_fix S hne (g.symm c) hI hfix]
  exact LinearMap.congr_fun key x

theorem Phi_rho {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) {g : K ≃+* K}
    (R : A.RankOneRel v₀ g) (h : GL (Fin 6) K)
    (hh : (h : Matrix (Fin 6) (Fin 6) K).det = 1) (x : Cube K) :
    A.Phi v₀ (rho K h x) = A.act (twist g.symm h) (A.Phi v₀ x) := by
  have hr1 : rho K (1 : GL (Fin 6) K) = 1 := map_one (TauCeti.extPowerRep K 6 3)
  have hdet : ∀ k : GL (Fin 6) K, (k : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ((twist g.symm k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    intro k hk
    rw [det_twist, hk, map_one]
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 6) K → Prop, ∀ k : GL (Fin 6) K, P k ↔
      ((k : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        ∀ y : Cube K, A.Phi v₀ (rho K k y) = A.act (twist g.symm k) (A.Phi v₀ y)) :=
    ⟨_, fun k => Iff.rfl⟩
  obtain ⟨H, hHmem⟩ : ∃ H : Subgroup (GL (Fin 6) K), ∀ k : GL (Fin 6) K, k ∈ H ↔ P k := by
    refine ⟨{ carrier := {k | P k}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ },
      fun k => Iff.rfl⟩
    · intro p q hp hq
      obtain ⟨hp1, hp2⟩ := (hP p).1 hp
      obtain ⟨hq1, hq2⟩ := (hP q).1 hq
      refine (hP (p * q)).2 ⟨by rw [Units.val_mul, Matrix.det_mul, hp1, hq1, one_mul], fun y => ?_⟩
      rw [rho_mul, Module.End.mul_apply, hp2, hq2, map_mul,
        A.act_mul _ _ (hdet p hp1) (hdet q hq1), Module.End.mul_apply]
    · refine (hP 1).2 ⟨by rw [Units.val_one, Matrix.det_one], fun y => ?_⟩
      rw [hr1, Module.End.one_apply, map_one, A.act_one, Module.End.one_apply]
    · intro p hp
      obtain ⟨hp1, hp2⟩ := (hP p).1 hp
      refine (hP p⁻¹).2 ⟨det_inv_eq_one hp1, fun y => ?_⟩
      have hrr : rho K p (rho K p⁻¹ y) = y := by
        rw [← Module.End.mul_apply, ← rho_mul, mul_inv_cancel, hr1, Module.End.one_apply]
      have h1 := hp2 (rho K p⁻¹ y)
      rw [hrr] at h1
      rw [h1, map_inv, A.act_inv_act (hdet p hp1)]
  have hH : ∀ (a b : Fin 6) (hne : a ≠ b), (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      ∀ t : K, transvGL K a b hne t ∈ H := by
    intro a b hne hadj t
    refine (hHmem _).2 ((hP (transvGL K a b hne t)).2 ⟨det_tr hne t, fun y => ?_⟩)
    rw [twist_tr, A.Phi_rho_adj S R hne hadj t y]
  exact ((hP h).1 ((hHmem h).1 (sl_le_of_adjacent_transvections H hH h hh))).2 x

private theorem cbC_surj {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) :
    Function.Surjective (A.Phi v₀) := by
  have hspan := A.span_vI S.hV S.h0 S.hv₀ S.hv0 S.hξ S.hξ1
  refine LinearMap.range_eq_top.1 ?_
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact LinearMap.mem_range.2 ⟨cubeBasis K ⟨I.1, I.2⟩, A.Phi_cubeBasis v₀ ⟨I.1, I.2⟩⟩

theorem Phi_injective {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) :
    Function.Injective (A.Phi v₀) := by
  have hC : finrank K (Cube K) = 20 := by
    rw [Module.finrank_eq_nat_card_basis (cubeBasis K)]
    exact card_J3
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by rw [S.hV]; norm_num)
  haveI : FiniteDimensional K (Cube K) := Module.finite_of_finrank_pos (by rw [hC]; norm_num)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hC.trans S.hV.symm)).2
    (cbC_surj A S)

theorem Phi_surjective {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) :
    Function.Surjective (A.Phi v₀) := by
  exact cbC_surj A S

theorem core_cube_iso [Finite K] {ξ : Kˣ →* Kˣ} {v₀ : V} (S : Setup A v₀ ξ) :
    ∃ (σ : K ≃+* K) (Φ : Cube K ≃ₗ[K] V),
      (∀ h : GL (Fin 6) K, (h : Matrix (Fin 6) (Fin 6) K).det = 1 → ∀ x : Cube K,
        Φ (rho K h x) = A.act (twist σ h) (Φ x)) ∧
      Φ (p0 K) = A.vI v₀ ({0, 2, 4} : Finset (Fin 6)) := by
  obtain ⟨g, -, hX, hY⟩ := rank_one_normalized A S
  have R : A.RankOneRel v₀ g := ⟨hX, hY⟩
  refine ⟨g.symm, LinearEquiv.ofBijective (A.Phi v₀) ⟨Phi_injective A S, Phi_surjective A S⟩,
    ?_, ?_⟩
  · intro h hh x
    exact Phi_rho A S R h hh x
  · exact (Phi_cubeBasis A v₀ S024).trans rfl

theorem core_main [Finite K] (hq : 4 ≤ Nat.card K) (hV : finrank K V = 20)
    {W : Submodule K (Fin 6 → K)} (hW : finrank K W = 3) (hline : finrank K (A.Fix W) = 1)
    (hspan : ⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
      (A.Fix W).map (A.act g.1) = ⊤) :
    ∃ (σ : K ≃+* K) (g₀ : GL (Fin 6) K) (Φ : Cube K ≃ₗ[K] V),
      (g₀ : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (∀ h : GL (Fin 6) K, (h : Matrix (Fin 6) (Fin 6) K).det = 1 → ∀ x : Cube K,
        Φ (rho K h x) = A.act (g₀ * twist σ h * g₀⁻¹) (Φ x)) ∧
      Φ (p0 K) ∈ A.Fix ((S0 K).map (Matrix.mulVecLin (g₀ : Matrix (Fin 6) (Fin 6) K))) := by
  have hWc : finrank K (Wc K I0) = 3 := by
    rw [finrank_Wc]
    decide
  obtain ⟨g₀, hg₀, hmap⟩ := exists_sl_map_eq hWc hW
  have hFix : (A.conj g₀).Fix (Wc K I0) = A.Fix W := by
    rw [A.Fix_conj hg₀ (Wc K I0), hmap]
  have h0 : finrank K ((A.conj g₀).Fix (Wc K I0)) = 1 := by
    rw [hFix, hline]
  obtain ⟨⟨v₀, hv₀⟩, hne0, -⟩ := finrank_eq_one_iff'.1 h0
  have hv0 : v₀ ≠ 0 := fun h => hne0 (Subtype.ext h)
  obtain ⟨ξ, hξ⟩ := exists_xi (A.conj g₀) h0
  by_cases hξ1 : ∃ c, ξ c ≠ 1
  · have hS : Setup (A.conj g₀) v₀ ξ := ⟨hV, h0, hv₀, hv0, hξ, hξ1⟩
    obtain ⟨σ, Φ, hΦ, hp0⟩ := core_cube_iso (A.conj g₀) hS
    refine ⟨σ, g₀, Φ, hg₀, fun h hh x => hΦ h hh x, ?_⟩
    have hI : ({0, 2, 4} : Finset (Fin 6)).card = 3 := by decide
    have hmem : (A.conj g₀).vI v₀ ({0, 2, 4} : Finset (Fin 6)) ∈ (A.conj g₀).Fix (S0 K) := by
      rw [S0_eq_Wc]
      exact vI_mem (A.conj g₀) h0 hv₀ hI
    rw [hp0, ← A.Fix_conj hg₀ (S0 K)]
    exact hmem
  · simp only [not_exists, ne_eq, not_not] at hξ1
    have hid : ∀ c : Kˣ, ∀ v ∈ (A.conj g₀).Fix (Wc K I0),
        (A.conj g₀).act (dg (cOn 0 3 c)) v = v := by
      intro c v hv
      rw [hξ c v hv, hξ1 c, Units.val_one, one_smul]
    have hspan' : ⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
        ((A.conj g₀).Fix (Wc K I0)).map ((A.conj g₀).act g.1) = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← hspan]
      refine iSup_le fun g => ?_
      have hdet : ((g₀⁻¹ * g.1 * g₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          det_inv_eq_one hg₀, g.2, hg₀, mul_one, mul_one]
      have hc : (A.conj g₀).act (g₀⁻¹ * g.1 * g₀) = A.act g.1 := by
        have e : g₀ * (g₀⁻¹ * g.1 * g₀) * g₀⁻¹ = g.1 := by group
        show A.act (g₀ * (g₀⁻¹ * g.1 * g₀) * g₀⁻¹) = A.act g.1
        rw [e]
      have key : ((A.conj g₀).Fix (Wc K I0)).map ((A.conj g₀).act (g₀⁻¹ * g.1 * g₀)) =
          (A.Fix W).map (A.act g.1) := by
        rw [hFix, hc]
      exact le_iSup_of_le
        (⟨g₀⁻¹ * g.1 * g₀, hdet⟩ : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1})
        key.ge
    have S0' : Setup0 (A.conj g₀) v₀ := ⟨hq, hV, h0, hv₀, hv0, hid, hspan'⟩
    exact (SLAct.xi_trivial_false (A.conj g₀) S0').elim

end SLAct

end CFSG.RankThree.GF2n.Smith81.S81J

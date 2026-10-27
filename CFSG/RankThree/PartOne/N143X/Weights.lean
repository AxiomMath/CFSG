module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian


public section

namespace CFSG.RankThree.PartOne.N143X

open Matrix Module Module.End

section Setup

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L]

@[expose] def mapL (g : GL ι K) : Matrix ι ι L := (g : Matrix ι ι K).map (algebraMap K L)

theorem mapL_mul (g h : GL ι K) : mapL L (g * h) = mapL L g * mapL L h := by
  simp only [mapL, Units.val_mul]
  exact Matrix.map_mul (f := algebraMap K L)

theorem mapL_one : mapL L (1 : GL ι K) = 1 := by
  simp [mapL]

theorem mapL_injective : Function.Injective (mapL L : GL ι K → Matrix ι ι L) := by
  intro g h hgh
  exact Units.ext (Matrix.map_injective (algebraMap K L).injective hgh)

@[expose] def mapLHom : GL ι K →* Matrix ι ι L where
  toFun := mapL L
  map_one' := mapL_one L
  map_mul' := mapL_mul L

theorem mapLHom_apply (g : GL ι K) : mapLHom L g = mapL L g := rfl

@[expose] def linL (g : GL ι K) : Module.End L (ι → L) := Matrix.toLinAlgEquiv' (mapL L g)

theorem linL_apply (g : GL ι K) (v : ι → L) : linL L g v = mapL L g *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ _

theorem linL_mul (g h : GL ι K) : linL L (g * h) = linL L g * linL L h := by
  simp only [linL, mapL_mul, map_mul]

theorem linL_one : linL L (1 : GL ι K) = 1 := by
  simp only [linL, mapL_one, map_one]

theorem linL_pow (g : GL ι K) (n : ℕ) : linL L (g ^ n) = linL L g ^ n := by
  induction n with
  | zero => simp [linL_one]
  | succ n ih => rw [pow_succ, linL_mul, ih, pow_succ]

variable (E : Subgroup (GL ι K))

@[expose] def joint (χ : E → L) : Submodule L (ι → L) :=
  ⨅ e : E, (linL L (e : GL ι K)).eigenspace (χ e)

theorem mem_joint {χ : E → L} {v : ι → L} :
    v ∈ joint L E χ ↔ ∀ e : E, mapL L (e : GL ι K) *ᵥ v = χ e • v := by
  simp [joint, Submodule.mem_iInf, linL_apply]

end Setup

section Decomposition

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

theorem linL_commute (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e) (e e' : E) :
    Commute (linL L (e : GL ι K)) (linL L (e' : GL ι K)) := by
  unfold Commute SemiconjBy
  rw [← linL_mul, ← linL_mul, hcomm e' e]

theorem isSemisimple_linL {p : ℕ} (hp : (p : L) ≠ 0) (e : E) (he : (e : GL ι K) ^ p = 1) :
    (linL L (e : GL ι K)).IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X ^ p - Polynomial.C 1 : Polynomial L)) ?_ ?_
  · exact (Polynomial.separable_X_pow_sub_C (1 : L) hp one_ne_zero).squarefree
  · simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    rw [← linL_pow, he, linL_one, sub_self]

theorem iSup_joint_eq_top [IsAlgClosed L] {p : ℕ} (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1)
    (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e) : ⨆ χ : E → L, joint L E χ = ⊤ := by
  have hss := fun e : E => isSemisimple_linL L E hp e (hexp e)
  have hmax : ∀ (e : E) (μ : L), (linL L (e : GL ι K)).maxGenEigenspace μ =
      (linL L (e : GL ι K)).eigenspace μ := fun e μ =>
    (hss e).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun e : E => linL L (e : GL ι K)) (fun e e' _ => linL_commute L E hcomm e e')
    (fun e => Module.End.iSup_maxGenEigenspace_eq_top _)
  refine Eq.trans ?_ h
  refine iSup_congr fun χ => ?_
  simp only [joint, hmax]

theorem iSupIndep_joint {p : ℕ} (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (hp : (p : L) ≠ 0) (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) :
    iSupIndep (joint L E) := by
  have hss := fun e : E => isSemisimple_linL L E hp e (hexp e)
  have hmax : ∀ (e : E) (μ : L), (linL L (e : GL ι K)).maxGenEigenspace μ =
      (linL L (e : GL ι K)).eigenspace μ := fun e μ =>
    (hss e).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun e : E => linL L (e : GL ι K)) (fun i j φ =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (linL_commute L E hcomm j i) φ)
  have : (fun χ : E → L => ⨅ e : E, (linL L (e : GL ι K)).maxGenEigenspace (χ e)) =
      joint L E := by
    funext χ
    simp only [joint, hmax]
  rwa [this] at h

end Decomposition


section Weights

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

abbrev Wts : Type := {χ : E → L // joint L E χ ≠ ⊥}

theorem pow_mulVec_eigen {A : Matrix ι ι L} {v : ι → L} {c : L} (h : A *ᵥ v = c • v) (n : ℕ) :
    (A ^ n) *ᵥ v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

theorem weight_pow_eq_one {p : ℕ} (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) {χ : E → L}
    (h : joint L E χ ≠ ⊥) (e : E) : χ e ^ p = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : (χ e ^ p) • v = (1 : L) • v := by
    rw [← pow_mulVec_eigen L ((mem_joint L E).1 hv e) p, ← mapLHom_apply, ← map_pow, hexp e]
    simp [mapLHom_apply, mapL_one]
  exact smul_left_injective L hv0 h1

theorem eq_of_forall_weight_eq [IsAlgClosed L] {p : ℕ} (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    {a b : E} (h : ∀ χ : E → L, joint L E χ ≠ ⊥ → χ a = χ b) : a = b := by
  have htop := iSup_joint_eq_top L E hp hexp hcomm
  have key : ∀ v : ι → L, mapL L (a : GL ι K) *ᵥ v = mapL L (b : GL ι K) *ᵥ v := by
    intro v
    have hv : v ∈ ⨆ χ : E → L, joint L E χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun v => mapL L (a : GL ι K) *ᵥ v = mapL L (b : GL ι K) *ᵥ v) hv ?_ ?_ ?_
    · intro χ w hw
      by_cases hχ : joint L E χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hw
        subst hw
        simp
      · rw [(mem_joint L E).1 hw a, (mem_joint L E).1 hw b, h χ hχ]
    · simp
    · intro x y hx hy
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
  have hmat : mapL L (a : GL ι K) = mapL L (b : GL ι K) :=
    Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using key v)
  exact Subtype.ext (mapL_injective L hmat)

theorem nat_card_wts_le {p : ℕ} (hp : (p : L) ≠ 0) (hexp : ∀ e : E, (e : GL ι K) ^ p = 1)
    (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e) :
    Finite (Wts L E) ∧ Nat.card (Wts L E) ≤ Fintype.card ι := by
  have hind := iSupIndep_joint L E hcomm hp hexp
  have : Fintype (Wts L E) := hind.fintypeNeBotOfFiniteDimensional
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card]
  have := hind.subtype_ne_bot_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at this

theorem joint_conj_ne_bot (n : Subgroup.normalizer (E : Set (GL ι K))) {χ : E → L}
    (h : joint L E χ ≠ ⊥) :
    joint L E (fun e => χ ((E.normalizerMonoidHom n)⁻¹ e)) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have hinv : ∀ e : E, (((E.normalizerMonoidHom n)⁻¹ e : E) : GL ι K) =
      ((n : GL ι K))⁻¹ * (e : GL ι K) * (n : GL ι K) := by
    intro e
    rw [← map_inv]
    simp
  refine (Submodule.ne_bot_iff _).2 ⟨mapL L (n : GL ι K) *ᵥ v, ?_, ?_⟩
  · rw [mem_joint]
    intro e
    have h1 := (mem_joint L E).1 hv ((E.normalizerMonoidHom n)⁻¹ e)
    rw [Matrix.mulVec_mulVec, ← mapL_mul]
    have h2 : (e : GL ι K) * (n : GL ι K) = (n : GL ι K) * ((n : GL ι K)⁻¹ * (e : GL ι K) *
        (n : GL ι K)) := by group
    rw [h2, mapL_mul, ← Matrix.mulVec_mulVec, ← hinv e, h1, Matrix.mulVec_smul]
  · intro h0
    apply hv0
    have h3 : mapL L ((n : GL ι K)⁻¹) *ᵥ (mapL L (n : GL ι K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← mapL_mul, inv_mul_cancel, mapL_one, Matrix.one_mulVec]
    rw [← h3, h0, Matrix.mulVec_zero]

end Weights


section Action

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

@[expose] def actFun (β : MulAut E) (χ : E → L) : E → L := fun e => χ (β.symm e)

variable {L E}

theorem joint_actFun_ne_bot (β : E.normalizerMonoidHom.range) {χ : E → L}
    (h : joint L E χ ≠ ⊥) : joint L E (actFun L E (β : MulAut E) χ) ≠ ⊥ := by
  obtain ⟨n, hn⟩ := β.2
  have := joint_conj_ne_bot L E n h
  rw [hn] at this
  exact this

@[expose] def actPerm (β : E.normalizerMonoidHom.range) : Equiv.Perm (Wts L E) where
  toFun χ := ⟨actFun L E (β : MulAut E) χ.1, joint_actFun_ne_bot β χ.2⟩
  invFun χ := ⟨actFun L E ((β⁻¹ : E.normalizerMonoidHom.range) : MulAut E) χ.1,
    joint_actFun_ne_bot β⁻¹ χ.2⟩
  left_inv χ := Subtype.ext (funext fun e => by
    change χ.1 ((β : MulAut E).symm (((β⁻¹ : E.normalizerMonoidHom.range) : MulAut E).symm e)) = _
    simp [MulAut.inv_def])
  right_inv χ := Subtype.ext (funext fun e => by
    change χ.1 (((β⁻¹ : E.normalizerMonoidHom.range) : MulAut E).symm ((β : MulAut E).symm e)) = _
    simp [MulAut.inv_def])

@[expose] def weightAction : E.normalizerMonoidHom.range →* Equiv.Perm (Wts L E) :=
  MonoidHom.mk' actPerm fun β₁ β₂ => by
    refine Equiv.ext fun χ => Subtype.ext (funext fun e => ?_)
    rfl

theorem weightAction_apply (β : E.normalizerMonoidHom.range) (χ : Wts L E) (e : E) :
    (weightAction β χ).1 e = χ.1 ((β : MulAut E).symm e) := rfl

theorem weightAction_injective [IsAlgClosed L] {p : ℕ} (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e) :
    Function.Injective (weightAction (L := L) (E := E)) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  have h1 : ∀ (χ : Wts L E) (e : E), χ.1 ((β : MulAut E).symm e) = χ.1 e := fun χ e =>
    congrFun (congrArg Subtype.val (Equiv.congr_fun hβ χ)) e
  have h2 : ∀ e : E, (β : MulAut E).symm e = e := fun e =>
    eq_of_forall_weight_eq L E hp hexp hcomm (fun χ hχ => h1 ⟨χ, hχ⟩ e)
  refine Subtype.ext (MulEquiv.ext fun e => ?_)
  have := h2 ((β : MulAut E) e)
  rw [MulEquiv.symm_apply_apply] at this
  exact this.symm

end Action


section Sym

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

theorem joint_inv_ne_bot [IsAlgClosed L] {p : ℕ} (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hEJ : ∀ e : E, ((e : GL ι K) : Matrix ι ι K)ᵀ * J * ((e : GL ι K) : Matrix ι ι K) = J)
    {χ : E → L} (h : joint L E χ ≠ ⊥) : joint L E (fun e => (χ e)⁻¹) ≠ ⊥ := by
  by_contra hbot
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  set JL : Matrix ι ι L := J.map (algebraMap K L) with hJLdef
  have hJL : IsUnit JL.det := by
    refine isUnit_iff_ne_zero.2 ?_
    have : JL.det = algebraMap K L J.det := by
      rw [hJLdef, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [this]
    exact (map_ne_zero (algebraMap K L)).2 hJ
  have hinv : ∀ e : E, (mapL L (e : GL ι K))ᵀ * JL * mapL L (e : GL ι K) = JL := by
    intro e
    have := congrArg (fun M : Matrix ι ι K => M.map (algebraMap K L)) (hEJ e)
    simpa [mapL, hJLdef, Matrix.map_mul, Matrix.transpose_map] using this
  have hpair : ∀ (e : E) (v w : ι → L), (mapL L (e : GL ι K) *ᵥ v) ⬝ᵥ
      (JL *ᵥ (mapL L (e : GL ι K) *ᵥ w)) = v ⬝ᵥ (JL *ᵥ w) := by
    intro e v w
    set A := mapL L (e : GL ι K)
    calc (A *ᵥ v) ⬝ᵥ (JL *ᵥ (A *ᵥ w)) = v ⬝ᵥ (Aᵀ *ᵥ (JL *ᵥ (A *ᵥ w))) := by
          rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
            dotProduct_comm]
      _ = v ⬝ᵥ ((Aᵀ * JL * A) *ᵥ w) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
      _ = v ⬝ᵥ (JL *ᵥ w) := by rw [hinv e]
  have hvanish : ∀ (ψ : E → L), ∀ w ∈ joint L E ψ, v ⬝ᵥ (JL *ᵥ w) = 0 := by
    intro ψ w hw
    by_cases hψ : ψ = fun e => (χ e)⁻¹
    · subst hψ
      rw [hbot, Submodule.mem_bot] at hw
      subst hw
      simp
    · obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ
      have h1 := hpair g v w
      rw [(mem_joint L E).1 hv g, (mem_joint L E).1 hw g] at h1
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      have hne : χ g * ψ g ≠ 1 := fun h1' => hg (eq_inv_of_mul_eq_one_right h1')
      have h2 : (χ g * ψ g - 1) * (v ⬝ᵥ (JL *ᵥ w)) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hne
      · exact h0
  have htop := iSup_joint_eq_top L E hp hexp hcomm
  have hall : ∀ w : ι → L, v ⬝ᵥ (JL *ᵥ w) = 0 := by
    intro w
    have hw : w ∈ ⨆ χ : E → L, joint L E χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun w => v ⬝ᵥ (JL *ᵥ w) = 0) hw
      (fun ψ w hw => hvanish ψ w hw) (by simp) fun x y hx hy => ?_
    rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
  have hzero : v ᵥ* JL = 0 := by
    funext i
    have := hall (Pi.single i 1)
    rw [Matrix.dotProduct_mulVec] at this
    simpa using this
  apply hv0
  calc v = (v ᵥ* JL) ᵥ* JL⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJL, Matrix.vecMul_one]
    _ = 0 := by rw [hzero]; simp

variable {L E}

variable (L E) in
@[expose] def NuStable : Prop :=
  ∀ χ : E → L, joint L E χ ≠ ⊥ → joint L E (fun e => (χ e)⁻¹) ≠ ⊥

@[expose] def nuPerm
    (hν : NuStable L E) : Equiv.Perm (Wts L E) where
  toFun χ := ⟨fun e => (χ.1 e)⁻¹, hν χ.1 χ.2⟩
  invFun χ := ⟨fun e => (χ.1 e)⁻¹, hν χ.1 χ.2⟩
  left_inv _ := Subtype.ext (funext fun _ => inv_inv _)
  right_inv _ := Subtype.ext (funext fun _ => inv_inv _)

theorem nuPerm_sq
    (hν : NuStable L E) :
    nuPerm hν ^ 2 = 1 :=
  Equiv.ext fun _ => Subtype.ext (funext fun _ => inv_inv _)

theorem weightAction_comm_nuPerm
    (hν : NuStable L E)
    (β : E.normalizerMonoidHom.range) :
    weightAction β * nuPerm hν = nuPerm hν * weightAction β :=
  Equiv.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem nuPerm_fixed {p : ℕ} (hp2 : p % 2 = 1) (hexp : ∀ e : E, (e : GL ι K) ^ p = 1)
    (hν : NuStable L E)
    (x y : Wts L E) (hx : nuPerm hν x = x) (hy : nuPerm hν y = y) : x = y := by
  have key : ∀ z : Wts L E, nuPerm hν z = z → ∀ e, z.1 e = 1 := by
    intro z hz e
    have h1 : (z.1 e)⁻¹ = z.1 e := congrFun (congrArg Subtype.val hz) e
    have h2 : z.1 e ^ p = 1 := weight_pow_eq_one L E hexp z.2 e
    have hp0 : p ≠ 0 := by omega
    have h3 : z.1 e ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp0] at h2
      exact zero_ne_one h2
    have h4 : z.1 e * z.1 e = 1 := by
      calc z.1 e * z.1 e = z.1 e * (z.1 e)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ h3
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    rw [hk, pow_succ, pow_mul, sq, h4, one_pow, one_mul] at h2
    exact h2
  exact Subtype.ext (funext fun e => (key x hx e).trans (key y hy e).symm)

end Sym


section Final

@[expose] def FaithfulSmall (H : Type) [Group H] (d : ℕ) : Prop :=
  ∃ (S : Type) (_ : Finite S) (φ : H →* Equiv.Perm S), Nat.card S ≤ d ∧ Function.Injective φ

@[expose] def FaithfulSmallSym (H : Type) [Group H] (d : ℕ) : Prop :=
  ∃ (S : Type) (_ : Finite S) (φ : H →* Equiv.Perm S), Nat.card S ≤ d ∧ Function.Injective φ ∧
    ∃ ν : Equiv.Perm S, ν ^ 2 = 1 ∧ (∀ x y, ν x = x → ν y = y → x = y) ∧ ∀ h, φ h * ν = ν * φ h

theorem FaithfulSmall.card_dvd_factorial {H : Type} [Group H] {d : ℕ} (h : FaithfulSmall H d) :
    Nat.card H ∣ d.factorial := by
  obtain ⟨S, hS, φ, hd, hφ⟩ := h
  have : Fintype S := Fintype.ofFinite S
  classical
  have h1 := Subgroup.card_dvd_of_injective φ hφ
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm S), Fintype.card_perm,
    ← Nat.card_eq_fintype_card] at h1
  exact h1.trans (Nat.factorial_dvd_factorial hd)

theorem card_centralizer_involution_dvd {S : Type} [Fintype S] [DecidableEq S] (ν : Equiv.Perm S)
    (h2 : ν ^ 2 = 1) (hfix : ∀ x y, ν x = x → ν y = y → x = y) (hS : Fintype.card S ≤ 8) :
    Nat.card (Subgroup.centralizer {ν}) ∣ 384 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (σ := ν) (p := 2) h2
  obtain ⟨m, hm⟩ : ∃ m, ν.cycleType = Multiset.replicate m 2 := ⟨_, hct⟩
  have hsum : ν.support.card = 2 * m := by
    rw [← Equiv.Perm.sum_cycleType, hm, Multiset.sum_replicate]
    simp [mul_comm]
  have hfixcard : (Finset.univ.filter fun x => ν x = x).card ≤ 1 :=
    Finset.card_le_one.2 fun x hx y hy => hfix x y (by simpa using hx) (by simpa using hy)
  have hcomp : ν.support.card + (Finset.univ.filter fun x => ν x = x).card = Fintype.card S := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
      (fun x => ν x ≠ x)
    simpa [Equiv.Perm.support, add_comm] using this
  have hm4 : m ≤ 4 := by
    have := Finset.card_le_univ ν.support
    omega
  have hfact : (Fintype.card S - ν.cycleType.sum).factorial = 1 := by
    rw [Nat.factorial_eq_one, Equiv.Perm.sum_cycleType]
    omega
  rw [Equiv.Perm.nat_card_centralizer, hfact, hm, Multiset.prod_replicate, one_mul]
  interval_cases m <;> simp <;> decide

theorem FaithfulSmallSym.card_dvd_384 {H : Type} [Group H] {d : ℕ} (h : FaithfulSmallSym H d)
    (hd : d ≤ 8) : Nat.card H ∣ 384 := by
  obtain ⟨S, hS, φ, hdS, hφ, ν, hν2, hνfix, hcomm⟩ := h
  have : Fintype S := Fintype.ofFinite S
  classical
  let φ' : H →* Subgroup.centralizer {ν} := φ.codRestrict _ fun x =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x)
  have hφ' : Function.Injective φ' := fun a b hab => hφ (congrArg Subtype.val hab)
  have h1 := Subgroup.card_dvd_of_injective φ' hφ'
  have h2 := card_centralizer_involution_dvd ν hν2 hνfix (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  exact h1.trans h2

theorem factorization_three_le_of_dvd_120 {n : ℕ} (h : n ∣ 120) : n.factorization 3 ≤ 1 := by
  have hn : n ≠ 0 := by
    rintro rfl
    norm_num at h
  have := (Nat.factorization_le_iff_dvd hn (by norm_num : (120 : ℕ) ≠ 0)).2 h 3
  have h120 : (120 : ℕ).factorization 3 = 1 := by
    have : (120 : ℕ) = 3 * 40 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]
  omega

theorem factorization_three_le_of_dvd_384 {n : ℕ} (h : n ∣ 384) : n.factorization 3 ≤ 1 := by
  have hn : n ≠ 0 := by
    rintro rfl
    norm_num at h
  have := (Nat.factorization_le_iff_dvd hn (by norm_num : (384 : ℕ) ≠ 0)).2 h 3
  have h384 : (384 : ℕ).factorization 3 = 1 := by
    have : (384 : ℕ) = 3 * 128 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 128)]
  omega

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (E : Subgroup (GL ι K))

theorem faithfulSmall_normalizer_range {p : ℕ} (hp : (p : K) ≠ 0) [IsElementaryAbelian p E] :
    FaithfulSmall E.normalizerMonoidHom.range (Fintype.card ι) := by
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := by
    intro h0
    apply hp
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  exact ⟨Wts L E, hfin, weightAction, hcard, weightAction_injective hpL hexp hcomm⟩

theorem faithfulSmallSym_normalizer_range {p : ℕ} (hp : (p : K) ≠ 0) (hp2 : p % 2 = 1)
    [IsElementaryAbelian p E] (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hEJ : ∀ e ∈ E, ((e : GL ι K) : Matrix ι ι K)ᵀ * J * ((e : GL ι K) : Matrix ι ι K) = J) :
    FaithfulSmallSym E.normalizerMonoidHom.range (Fintype.card ι) := by
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := by
    intro h0
    apply hp
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  have hν : NuStable L E := fun χ h =>
    joint_inv_ne_bot L E hpL hexp hcomm J hJ (fun e => hEJ e e.2) h
  exact ⟨Wts L E, hfin, weightAction, hcard, weightAction_injective hpL hexp hcomm, nuPerm hν,
    nuPerm_sq hν, fun x y hx hy => nuPerm_fixed hp2 hexp hν x y hx hy,
    fun β => weightAction_comm_nuPerm hν β⟩

theorem card_normalizer_range_dvd_120 {p : ℕ} (hp : (p : K) ≠ 0) [IsElementaryAbelian p E]
    (hd : Fintype.card ι ≤ 5) : Nat.card E.normalizerMonoidHom.range ∣ 120 := by
  obtain ⟨S, hS, φ, hcard, hinj⟩ := faithfulSmall_normalizer_range E hp
  have h := FaithfulSmall.card_dvd_factorial (⟨S, hS, φ, hcard.trans hd, hinj⟩ :
    FaithfulSmall E.normalizerMonoidHom.range 5)
  simpa [Nat.factorial] using h

theorem card_normalizer_range_dvd_384 {p : ℕ} (hp : (p : K) ≠ 0) (hp2 : p % 2 = 1)
    [IsElementaryAbelian p E] (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hEJ : ∀ e ∈ E, ((e : GL ι K) : Matrix ι ι K)ᵀ * J * ((e : GL ι K) : Matrix ι ι K) = J)
    (hd : Fintype.card ι ≤ 8) : Nat.card E.normalizerMonoidHom.range ∣ 384 :=
  FaithfulSmallSym.card_dvd_384 (faithfulSmallSym_normalizer_range E hp hp2 J hJ hEJ) hd

end Final

end CFSG.RankThree.PartOne.N143X

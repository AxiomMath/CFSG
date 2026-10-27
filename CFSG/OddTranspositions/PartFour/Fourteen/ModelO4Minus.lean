module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.Quasithin.Vol2.Ch11SecBK10H
import CFSG.ClassicalInvolution.Sp62Rec.I1.IndexTwo
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.LocalAnalysis.WeakClosure81

section Herm

open Matrix

structure HermInvol (K : Type) [Field K] where
  σ : K ≃+* K
  σσ : ∀ x, σ (σ x) = x
  ξ : K
  hξ : σ ξ ≠ ξ

namespace HermInvol

variable {K : Type} [Field K] [CharP K 2] (D : HermInvol K)

def F : Subfield K := RingHom.eqLocusField D.σ.toRingHom (RingHom.id K)

omit [CharP K 2] in
theorem σ_coe (x : D.F) : D.σ (x : K) = x := x.2

def bK : K := D.ξ + D.σ D.ξ

def cK : K := D.ξ * D.σ D.ξ

omit [CharP K 2] in
theorem σ_bK : D.σ D.bK = D.bK := by
  rw [bK, map_add, D.σσ, add_comm]

omit [CharP K 2] in
theorem σ_cK : D.σ D.cK = D.cK := by
  rw [cK, map_mul, D.σσ, mul_comm]

def b : D.F := ⟨D.bK, D.σ_bK⟩

def c : D.F := ⟨D.cK, D.σ_cK⟩

theorem bK_ne_zero : D.bK ≠ 0 := by
  intro h
  simp only [bK] at h
  apply D.hξ
  have : D.σ D.ξ = - D.ξ := by linear_combination h
  rw [this, CharTwo.neg_eq]

theorem irreducible (t : D.F) : t ^ 2 + D.b * t + D.c ≠ 0 := by
  intro h
  have h1 : (t : K) ^ 2 + D.bK * t + D.cK = 0 := by
    have := congrArg (fun x : D.F => (x : K)) h
    simpa [b, c] using this
  have h2 : ((t : K) - D.ξ) * ((t : K) - D.σ D.ξ) = 0 := by
    have e : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [bK, cK] at h1
    linear_combination h1 - ((t : K) * (D.ξ + D.σ D.ξ)) * e
  rcases mul_eq_zero.mp h2 with h3 | h3
  · apply D.hξ
    have : (t : K) = D.ξ := sub_eq_zero.mp h3
    rw [← this]
    exact D.σ_coe t
  · apply D.hξ
    have h4 : (t : K) = D.σ D.ξ := sub_eq_zero.mp h3
    calc D.σ D.ξ = (t : K) := h4.symm
      _ = D.σ (t : K) := (D.σ_coe t).symm
      _ = D.σ (D.σ D.ξ) := by rw [h4]
      _ = D.ξ := D.σσ _

theorem exists_coord (β : K) : ∃ u w : D.F, β = (u : K) + (w : K) * D.ξ := by
  have e : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb := D.bK_ne_zero
  set w : K := (β + D.σ β) / D.bK with hw
  have hwb : w * D.bK = β + D.σ β := by rw [hw]; field_simp
  have hwF : D.σ w = w := by
    rw [hw, map_div₀, map_add, D.σσ, D.σ_bK, add_comm]
  set u : K := β + w * D.ξ with hu
  have huF : D.σ u = u := by
    rw [hu, map_add, map_mul, hwF]
    simp only [bK] at hwb
    linear_combination hwb + (D.σ β - w * D.ξ) * e
  refine ⟨⟨u, huF⟩, ⟨w, hwF⟩, ?_⟩
  show β = u + w * D.ξ
  rw [hu]
  linear_combination (-(w * D.ξ)) * e

abbrev Ix : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 2

def beta (v : Ix → D.F) : K :=
  ((v (Sum.inr (Sum.inr 0)) : D.F) : K) + ((v (Sum.inr (Sum.inr 1)) : D.F) : K) * D.ξ

def toHerm (v : Ix → D.F) : Matrix (Fin 2) (Fin 2) K :=
  !![((v (Sum.inl 0) : D.F) : K), D.beta v; D.σ (D.beta v), ((v (Sum.inr (Sum.inl 0)) : D.F) : K)]

def IsHerm (A : Matrix (Fin 2) (Fin 2) K) : Prop := Aᵀ = A.map D.σ

omit [CharP K 2] in
theorem isHerm_toHerm (v : Ix → D.F) : D.IsHerm (D.toHerm v) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, D.σ_coe, D.σσ]

omit [CharP K 2] in
theorem toHerm_add (v w : Ix → D.F) : D.toHerm (v + w) = D.toHerm v + D.toHerm w := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, beta] <;> ring

omit [CharP K 2] in
theorem toHerm_smul (r : D.F) (v : Ix → D.F) :
    D.toHerm (r • v) = (r : K) • D.toHerm v := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, beta, D.σ_coe] <;> ring

def mk4 (a d u w : D.F) : Ix → D.F :=
  Sum.elim (fun _ => a) (Sum.elim (fun _ => d) ![u, w])

omit [CharP K 2] in
private theorem toHerm_mk4 (a d u w : D.F) :
    D.toHerm (D.mk4 a d u w) = !![(a : K), (u : K) + (w : K) * D.ξ;
      D.σ ((u : K) + (w : K) * D.ξ), (d : K)] := rfl

theorem herm_exists {A : Matrix (Fin 2) (Fin 2) K} (hA : D.IsHerm A) :
    ∃ v, D.toHerm v = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  simp only [transpose_apply, map_apply] at h00 h11 h01
  obtain ⟨u, w, hβ⟩ := D.exists_coord (A 0 1)
  refine ⟨D.mk4 ⟨A 0 0, h00.symm⟩ ⟨A 1 1, h11.symm⟩ u w, ?_⟩
  rw [toHerm_mk4, ← hβ]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h01]

omit [CharP K 2] in
theorem coord_unique {u w u' w' : D.F} (h : (u : K) + (w : K) * D.ξ = (u' : K) + (w' : K) * D.ξ) :
    u = u' ∧ w = w' := by
  have h2 := congrArg D.σ h
  simp only [map_add, map_mul, D.σ_coe] at h2
  have hw : (w : K) = w' := by
    have h3 : ((w : K) - w') * (D.σ D.ξ - D.ξ) = 0 := by linear_combination h2 - h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd (sub_eq_zero.mp h4) D.hξ
  have hu : (u : K) = u' := by rw [hw] at h; linear_combination h
  exact ⟨Subtype.ext hu, Subtype.ext hw⟩

omit [CharP K 2] in
theorem toHerm_injective : Function.Injective D.toHerm := by
  intro v v' h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  simp only [toHerm, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h00 h11 h01
  obtain ⟨hu, hw⟩ := D.coord_unique h01
  funext i
  rcases i with ⟨i⟩ | ⟨i⟩ | ⟨i⟩
  · fin_cases i; exact Subtype.ext h00
  · fin_cases i; exact Subtype.ext h11
  · fin_cases i
    · exact hu
    · exact hw

omit [CharP K 2] in
theorem mk4_eta (v : Ix → D.F) :
    v = D.mk4 (v (Sum.inl 0)) (v (Sum.inr (Sum.inl 0))) (v (Sum.inr (Sum.inr 0)))
      (v (Sum.inr (Sum.inr 1))) := by
  funext i
  rcases i with ⟨i⟩ | ⟨i⟩ | ⟨i⟩
  · fin_cases i; rfl
  · fin_cases i; rfl
  · fin_cases i <;> rfl

open Classical in
noncomputable def coords (A : Matrix (Fin 2) (Fin 2) K) : Ix → D.F :=
  if h : D.IsHerm A then Classical.choose (D.herm_exists h) else 0

theorem toHerm_coords {A : Matrix (Fin 2) (Fin 2) K} (hA : D.IsHerm A) :
    D.toHerm (D.coords A) = A := by
  rw [coords, dif_pos hA]
  exact Classical.choose_spec (D.herm_exists hA)

theorem det_toHerm (v : Ix → D.F) :
    (D.toHerm v).det = ((CFSG.PGLModel.minusQuadForm 1 D.b D.c v : D.F) : K) := by
  have e : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ : CFSG.PGLModel.minusQuadForm 1 D.b D.c v =
      v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
      D.b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      D.c * v (Sum.inr (Sum.inr 1)) ^ 2 := by
    simp [CFSG.PGLModel.minusQuadForm]
  rw [hQ, Matrix.det_fin_two]
  simp only [toHerm, beta, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, map_add, map_mul, D.σ_coe]
  push_cast
  simp only [b, c, bK, cK]
  linear_combination (-(((v (Sum.inr (Sum.inr 0)) : D.F) : K) ^ 2 +
    ((v (Sum.inr (Sum.inr 0)) : D.F) : K) * ((v (Sum.inr (Sum.inr 1)) : D.F) : K) *
      (D.ξ + D.σ D.ξ) + ((v (Sum.inr (Sum.inr 1)) : D.F) : K) ^ 2 * (D.ξ * D.σ D.ξ))) * e

def Phi (g A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K := g * A * (g.map D.σ)ᵀ

omit [CharP K 2] in
theorem map_σ_σ (g : Matrix (Fin 2) (Fin 2) K) : (g.map D.σ).map D.σ = g :=
  Matrix.ext fun i j => by simp [D.σσ]

omit [CharP K 2] in
theorem map_σ_one : (1 : Matrix (Fin 2) (Fin 2) K).map D.σ = 1 :=
  Matrix.map_one D.σ (map_zero D.σ) (map_one D.σ)

omit [CharP K 2] in
theorem Phi_one (A : Matrix (Fin 2) (Fin 2) K) : D.Phi 1 A = A := by
  simp [Phi, D.map_σ_one]

omit [CharP K 2] in
theorem Phi_mul (g h A : Matrix (Fin 2) (Fin 2) K) : D.Phi (g * h) A = D.Phi g (D.Phi h A) := by
  simp only [Phi, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

omit [CharP K 2] in
theorem Phi_add (g A B : Matrix (Fin 2) (Fin 2) K) : D.Phi g (A + B) = D.Phi g A + D.Phi g B := by
  simp [Phi, Matrix.mul_add, Matrix.add_mul]

omit [CharP K 2] in
theorem Phi_smul (g : Matrix (Fin 2) (Fin 2) K) (r : K) (A : Matrix (Fin 2) (Fin 2) K) :
    D.Phi g (r • A) = r • D.Phi g A := by
  simp [Phi]

omit [CharP K 2] in
theorem isHerm_Phi {A : Matrix (Fin 2) (Fin 2) K} (hA : D.IsHerm A)
    (g : Matrix (Fin 2) (Fin 2) K) : D.IsHerm (D.Phi g A) := by
  have hX : ((g.map D.σ)ᵀ).map D.σ = gᵀ := by rw [← Matrix.transpose_map, D.map_σ_σ]
  unfold IsHerm Phi at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
    Matrix.map_mul, Matrix.map_mul, hX, Matrix.mul_assoc]

noncomputable def liftL (T : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hadd : ∀ A B, T (A + B) = T A + T B)
    (hsmul : ∀ (r : D.F) A, T ((r : K) • A) = (r : K) • T A)
    (hH : ∀ A, D.IsHerm A → D.IsHerm (T A)) : (Ix → D.F) →ₗ[D.F] (Ix → D.F) where
  toFun v := D.coords (T (D.toHerm v))
  map_add' v w := by
    apply D.toHerm_injective
    have hv := D.toHerm_coords (hH _ (D.isHerm_toHerm v))
    have hw := D.toHerm_coords (hH _ (D.isHerm_toHerm w))
    have hvw := D.toHerm_coords (hH _ (D.isHerm_toHerm (v + w)))
    show D.toHerm (D.coords (T (D.toHerm (v + w)))) =
      D.toHerm (D.coords (T (D.toHerm v)) + D.coords (T (D.toHerm w)))
    rw [hvw, D.toHerm_add v w, D.toHerm_add (D.coords _) (D.coords _), hv, hw, hadd]
  map_smul' r v := by
    apply D.toHerm_injective
    have hv := D.toHerm_coords (hH _ (D.isHerm_toHerm v))
    have hrv := D.toHerm_coords (hH _ (D.isHerm_toHerm (r • v)))
    show D.toHerm (D.coords (T (D.toHerm (r • v)))) =
      D.toHerm (r • D.coords (T (D.toHerm v)))
    rw [hrv, D.toHerm_smul, D.toHerm_smul, hv, hsmul]

theorem toHerm_liftL (T : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K) {hadd hsmul hH}
    (v : Ix → D.F) : D.toHerm (D.liftL T hadd hsmul hH v) = T (D.toHerm v) :=
  D.toHerm_coords (hH _ (D.isHerm_toHerm _))

noncomputable def actL (g : Matrix (Fin 2) (Fin 2) K) : (Ix → D.F) →ₗ[D.F] (Ix → D.F) :=
  D.liftL (D.Phi g) (D.Phi_add g) (fun r A => D.Phi_smul g r A) (fun _ hA => D.isHerm_Phi hA g)

theorem toHerm_actL (g : Matrix (Fin 2) (Fin 2) K) (v : Ix → D.F) :
    D.toHerm (D.actL g v) = D.Phi g (D.toHerm v) := D.toHerm_liftL _ v

theorem actL_one : D.actL 1 = LinearMap.id :=
  LinearMap.ext fun v => D.toHerm_injective (by rw [D.toHerm_actL, D.Phi_one]; rfl)

theorem actL_mul (g h : Matrix (Fin 2) (Fin 2) K) : D.actL (g * h) = D.actL g * D.actL h := by
  refine LinearMap.ext fun v => D.toHerm_injective ?_
  rw [Module.End.mul_apply, D.toHerm_actL, D.toHerm_actL, D.toHerm_actL, D.Phi_mul]

noncomputable def RL : (Ix → D.F) →ₗ[D.F] (Ix → D.F) :=
  D.liftL (fun A => A.map D.σ) (fun A B => Matrix.map_add _ (map_add D.σ) A B)
    (fun r A => by
      refine Matrix.ext fun i j => ?_
      simp [D.σ_coe])
    (fun A hA => by
      unfold IsHerm at *
      rw [← Matrix.transpose_map, hA])

theorem toHerm_RL (v : Ix → D.F) : D.toHerm (D.RL v) = (D.toHerm v).map D.σ :=
  D.toHerm_liftL _ v

theorem RL_mul_self : D.RL * D.RL = 1 := by
  refine LinearMap.ext fun v => D.toHerm_injective ?_
  rw [Module.End.mul_apply, D.toHerm_RL, D.toHerm_RL, D.map_σ_σ]
  rfl

omit [CharP K 2] in
theorem Phi_map_σ (A M : Matrix (Fin 2) (Fin 2) K) :
    (D.Phi A (M.map D.σ)).map D.σ = D.Phi (A.map D.σ) M := by
  have hX : ((A.map D.σ)ᵀ).map D.σ = Aᵀ := by rw [← Matrix.transpose_map, D.map_σ_σ]
  simp only [Phi, Matrix.map_mul, hX, D.map_σ_σ]

theorem actL_map_σ (A : Matrix (Fin 2) (Fin 2) K) :
    D.actL (A.map D.σ) = D.RL * D.actL A * D.RL := by
  refine LinearMap.ext fun v => D.toHerm_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, D.toHerm_actL, D.toHerm_RL, D.toHerm_actL,
    D.toHerm_RL, Phi_map_σ]

abbrev Qf : (Ix → D.F) → D.F := CFSG.PGLModel.minusQuadForm 1 D.b D.c

theorem Q_actL (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det = 1) (v : Ix → D.F) :
    D.Qf (D.actL g v) = D.Qf v := by
  apply Subtype.ext
  rw [← D.det_toHerm, ← D.det_toHerm, D.toHerm_actL, Phi, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have h := RingHom.map_det D.σ.toRingHom g
  rw [RingHom.mapMatrix_apply, hg, map_one] at h
  have h' : (g.map D.σ).det = 1 := h.symm
  rw [h', hg, one_mul, mul_one]

theorem Q_RL (v : Ix → D.F) : D.Qf (D.RL v) = D.Qf v := by
  apply Subtype.ext
  rw [← D.det_toHerm, ← D.det_toHerm, D.toHerm_RL]
  have h : D.σ (D.toHerm v).det = ((D.toHerm v).map D.σ).det :=
    RingHom.map_det D.σ.toRingHom (D.toHerm v)
  rw [← h, D.det_toHerm]
  exact D.σ_coe _

noncomputable def matOf (g : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix D.F :=
  LinearMap.toMatrix' (D.actL g)

theorem matOf_mulVec (g : Matrix (Fin 2) (Fin 2) K) (v : Ix → D.F) :
    D.matOf g *ᵥ v = D.actL g v := by
  rw [matOf, LinearMap.toMatrix'_mulVec]

theorem matOf_one : D.matOf 1 = 1 := by
  rw [matOf, D.actL_one, LinearMap.toMatrix'_id]

theorem matOf_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    D.matOf (g * h) = D.matOf g * D.matOf h := by
  rw [matOf, matOf, matOf, D.actL_mul, LinearMap.toMatrix'_mul]

noncomputable def slHom : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix Ix Ix D.F where
  toFun A := D.matOf (A : Matrix (Fin 2) (Fin 2) K)
  map_one' := by simpa using D.matOf_one
  map_mul' A B := by simpa using D.matOf_mul (A : Matrix (Fin 2) (Fin 2) K) B

noncomputable def slGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL Ix D.F :=
  D.slHom.toHomUnits

private theorem slGL_coe (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((D.slGL A : GL Ix D.F) : Matrix Ix Ix D.F) = D.matOf (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem slGL_center (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : D.slGL A = 1 := by
  rw [CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.center_sl_eq_bot, Subgroup.mem_bot] at hA
  rw [hA, map_one]

noncomputable def psiN : CFSG.GorensteinWalter.PSL2 K →* GL Ix D.F :=
  QuotientGroup.lift (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) D.slGL
    (fun A hA => (MonoidHom.mem_ker).mpr (D.slGL_center A hA))

private theorem psiN_mk (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    D.psiN (QuotientGroup.mk A) = D.slGL A := rfl

noncomputable def matR : Matrix Ix Ix D.F := LinearMap.toMatrix' D.RL

theorem matR_mulVec (v : Ix → D.F) : D.matR *ᵥ v = D.RL v := by
  rw [matR, LinearMap.toMatrix'_mulVec]

theorem matR_mul_self : D.matR * D.matR = 1 := by
  rw [matR, ← LinearMap.toMatrix'_mul, D.RL_mul_self, Module.End.one_eq_id, LinearMap.toMatrix'_id]

noncomputable def Rg : GL Ix D.F := ⟨D.matR, D.matR, D.matR_mul_self, D.matR_mul_self⟩

private theorem Rg_coe : ((D.Rg : GL Ix D.F) : Matrix Ix Ix D.F) = D.matR := rfl

theorem Rg_mul_self : D.Rg * D.Rg = 1 := Units.ext D.matR_mul_self

theorem Rg_inv : D.Rg⁻¹ = D.Rg := inv_eq_of_mul_eq_one_right D.Rg_mul_self

theorem matOf_map_σ (A : Matrix (Fin 2) (Fin 2) K) :
    D.matOf (A.map D.σ) = D.matR * D.matOf A * D.matR := by
  rw [matOf, matOf, matR, D.actL_map_σ, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul]

omit [CharP K 2] in
private theorem psl2FieldAut_mk' (e : K ≃+* K) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    CFSG.GorensteinWalter.psl2FieldAut K e (QuotientGroup.mk A) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map e.toRingHom A) := by
  show CFSG.GorensteinWalter.psl2RingEquiv e
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) = _
  rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
  rfl

theorem psiN_compat (y : CFSG.GorensteinWalter.PSL2 K) :
    D.psiN (CFSG.GorensteinWalter.psl2FieldAut K D.σ y) = D.Rg * D.psiN y * D.Rg⁻¹ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  rw [psl2FieldAut_mk', D.psiN_mk, D.psiN_mk, D.Rg_inv]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, D.slGL_coe, D.slGL_coe, D.Rg_coe]
  have hA : ((Matrix.SpecialLinearGroup.map D.σ.toRingHom A :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K).map D.σ := rfl
  rw [hA, D.matOf_map_σ]

theorem psiN_ne_one : ∃ y : CFSG.GorensteinWalter.PSL2 K, D.psiN y ≠ 1 := by
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨QuotientGroup.mk A, ?_⟩
  intro h
  rw [D.psiN_mk] at h
  have hm : D.matOf (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun g : GL Ix D.F => (g : Matrix Ix Ix D.F)) h
    simpa [D.slGL_coe] using this
  have h1 : D.matOf (A : Matrix (Fin 2) (Fin 2) K) *ᵥ D.mk4 0 1 0 0 = D.mk4 0 1 0 0 := by
    rw [hm, Matrix.one_mulVec]
  rw [D.matOf_mulVec] at h1
  have h2 := congrArg D.toHerm h1
  rw [D.toHerm_actL] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp [Phi, toHerm_mk4, A, Matrix.mul_apply, Fin.sum_univ_two] at h3

theorem psiN_injective (h4 : 4 ≤ Nat.card K) : Function.Injective D.psiN := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D.psiN.ker with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy⟩ := D.psiN_ne_one
    have : y ∈ D.psiN.ker := by rw [h]; trivial
    exact hy this

omit [CharP K 2] in
theorem mem_orth {g : GL Ix D.F}
    (h : ∀ v, D.Qf ((g : Matrix Ix Ix D.F) *ᵥ v) = D.Qf v) :
    g ∈ CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c :=
  Subgroup.subset_closure h

theorem slGL_mem_orth (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    D.slGL A ∈ CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c :=
  D.mem_orth fun v => by
    rw [D.slGL_coe, D.matOf_mulVec]
    exact D.Q_actL _ A.det_coe v

theorem Rg_mem_orth : D.Rg ∈ CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c :=
  D.mem_orth fun v => by
    rw [D.Rg_coe, D.matR_mulVec]
    exact D.Q_RL v

theorem RL_mk4 (a d u w : D.F) : D.RL (D.mk4 a d u w) = D.mk4 a d (u + D.b * w) w := by
  have e : (2 : K) = 0 := CharTwo.two_eq_zero
  apply D.toHerm_injective
  rw [D.toHerm_RL, D.toHerm_mk4, D.toHerm_mk4]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [D.σ_coe, D.σσ, b, bK]
  · linear_combination (-((w : K) * D.ξ)) * e
  · linear_combination (-((w : K) * D.σ D.ξ)) * e

omit [CharP K 2] in
theorem mk4_zero_zero (t : D.F) :
    D.mk4 0 0 t 0 = t • (Pi.single (Sum.inr (Sum.inr 0)) 1 : Ix → D.F) := by
  funext i
  rcases i with ⟨i⟩ | ⟨i⟩ | ⟨i⟩
  · fin_cases i; simp [mk4]
  · fin_cases i; simp [mk4]
  · fin_cases i <;> simp [mk4]

theorem matR_sub_one_mulVec (v : Ix → D.F) :
    (D.matR - 1) *ᵥ v =
      (D.b * v (Sum.inr (Sum.inr 1))) • (Pi.single (Sum.inr (Sum.inr 0)) 1 : Ix → D.F) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, D.matR_mulVec]
  conv_lhs => rw [D.mk4_eta v]
  obtain ⟨a, d, u, w, hv⟩ : ∃ a d u w, v = D.mk4 a d u w := ⟨_, _, _, _, D.mk4_eta v⟩
  subst hv
  rw [D.RL_mk4, ← D.mk4_zero_zero]
  funext i
  rcases i with ⟨i⟩ | ⟨i⟩ | ⟨i⟩
  · fin_cases i; simp [mk4]
  · fin_cases i; simp [mk4]
  · fin_cases i <;> simp [mk4]

theorem rank_matR_sub_one : Matrix.rank (D.matR - 1) = 1 := by
  set e : Ix → D.F := Pi.single (Sum.inr (Sum.inr 0)) 1 with he
  have hb : D.b ≠ 0 := fun h => D.bK_ne_zero (congrArg Subtype.val h)
  have hrange : LinearMap.range (D.matR - 1).mulVecLin = Submodule.span D.F {e} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, D.matR_sub_one_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨D.b⁻¹ • Pi.single (Sum.inr (Sum.inr 1)) 1, ?_⟩
      rw [Matrix.mulVecLin_apply, D.matR_sub_one_mulVec]
      simp [hb, he]
  rw [Matrix.rank, hrange]
  exact finrank_span_singleton (by simp [he])

theorem natCard_K [Finite K] : Nat.card K = Nat.card D.F ^ 2 := by
  have hbij : Function.Bijective (fun p : D.F × D.F => ((p.1 : K) + (p.2 : K) * D.ξ)) := by
    constructor
    · rintro ⟨u, w⟩ ⟨u', w'⟩ h
      obtain ⟨hu, hw⟩ := D.coord_unique h
      exact Prod.ext hu hw
    · intro β
      obtain ⟨u, w, h⟩ := D.exists_coord β
      exact ⟨(u, w), h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

theorem natCard_orth [Finite K] :
    (Nat.card ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) : ℤ) =
      2 * (Nat.card D.F : ℤ) ^ 2 *
        (((Nat.card D.F : ℤ) ^ 2 + 1) * ((Nat.card D.F : ℤ) ^ 2 - 1)) := by
  have hirr := D.irreducible
  have h1 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
  have hcomap : CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c =
      (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) D.F D.b D.c)).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Ix D.F).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadMinus (1 + 1) D.F D.b D.c)
  have hc : Nat.card ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) =
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) D.F D.b D.c)) := by
    let Φ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv Ix D.F
    let Oq := TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) D.F D.b D.c)
    have key : Oq.comap Φ.toMonoidHom = Oq.map Φ.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm Φ Oq
    rw [hcomap, key]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  rw [hc, h1]
  simp [Finset.Icc_self]
  ring

end HermInvol

section GroupSide

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_involution_fieldAut_of_commutator_psl2 {X : Type} [Group X] {E : Set X}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hS : Setup X E)
    (hcen : Subgroup.centralizer (commutator X : Set X) = ⊥)
    (e : ↥(commutator X) ≃* PSL2 K) (hidx : (commutator X).index = 2) :
    ∃ s₀ ∈ E, s₀ ∉ commutator X ∧ ∃ σ : K ≃+* K, (∀ x, σ (σ x) = x) ∧ σ ≠ 1 ∧
      ∀ n : ↥(commutator X),
        e ⟨s₀ * n * s₀⁻¹, (inferInstance : (commutator X).Normal).conj_mem n n.2 s₀⟩ =
          psl2FieldAut K σ (e n) := by
  classical
  let N : Subgroup X := commutator X
  let φ : X →* MulAut (PSL2 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hφ : ∀ (x : X) (n : N), φ x (e n) =
      e ⟨x * n * x⁻¹, (inferInstance : N.Normal).conj_mem n n.2 x⟩ := by
    intro x n
    simp [φ]
    exact Subtype.ext (MulAut.conjNormal_apply x n)
  have hφinj : ∀ x, φ x = 1 → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := hφ x ⟨n, hn⟩
      rw [hx] at h1
      have h2 := e.injective h1
      have h3 := congrArg Subtype.val h2
      simp at h3
      calc n * x = x * n * x⁻¹ * x := by rw [← h3]
        _ = x * n := by group
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  have hφinj' : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hφinj
  have hinner : ∀ n : N, φ (n : X) = MulAut.conj (e n) := by
    intro n
    ext z
    obtain ⟨m, rfl⟩ := e.surjective z
    rw [hφ (n : X) m, MulAut.conj_apply]
    show e (n * m * n⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hidx' : N.index = 2 := hidx
  have hsN : ∀ s ∈ E, s ∉ N := by
    intro s hs hsN
    rcases hS.subset_or_disjoint N with h | h
    · have : N = ⊤ := hS.eq_top_of_subset N h
      rw [this, Subgroup.index_top] at hidx'
      omega
    · exact h s hs hsN
  obtain ⟨s, hs⟩ := hS.nonempty
  have hs1 : s * s = 1 := hS.oddT.mul_self_eq_one hs
  have hs_ne : s ≠ 1 := hS.oddT.ne_one hs
  have hα2 : (φ s) ^ 2 = 1 := by rw [← map_pow, pow_two, hs1, map_one]
  have hα1 : φ s ≠ 1 := fun h => hs_ne (hφinj s h)
  have hαord : orderOf (φ s) = 2 := orderOf_eq_prime hα2 hα1
  have hD : φ s ∉ (pglAction K).range := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy⟩ := CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.pglAction_mem_inner g
    have h1 : φ s = φ ((e.symm y : N) : X) := by
      rw [hinner, e.apply_symm_apply, hy, hg]
    exact hsN s hs (by rw [hφinj' h1]; exact (e.symm y).2)
  obtain ⟨σ, hσ, g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent
    Nat.prime_two (φ s) hαord hD
  obtain ⟨y₁, hy₁⟩ := CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.pglAction_mem_inner g
  rw [← hy₁] at hg
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ, pow_two] at this
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  set n₁ : N := e.symm y₁ with hn₁
  have hσ₀E : ((n₁ : X)⁻¹ * s * (n₁ : X)) ∈ E := by
    have := hS.conj_mem (n₁ : X)⁻¹ hs
    simpa using this
  have hφσ₀ : φ ((n₁ : X)⁻¹ * s * (n₁ : X)) = psl2FieldAut K σ := by
    rw [map_mul, map_mul, map_inv, hinner n₁, hn₁, e.apply_symm_apply, hg]
    group
  refine ⟨_, hσ₀E, hsN _ hσ₀E, σ, fun x => ?_, hσ1, fun n => ?_⟩
  · have := congrArg (fun τ : K ≃+* K => τ x) hσσ
    simpa using this
  · rw [← hφσ₀]
    exact (hφ _ n).symm

theorem exists_orthMinus_model_of_commutator_psl2 {X : Type} [Group X] [Finite X]
    {E : Set X} {K : Type} [Field K] [Finite K] [CharP K 2] (hS : Setup X E)
    (hcen : Subgroup.centralizer (commutator X : Set X) = ⊥)
    (e : ↥(commutator X) ≃* PSL2 K) (hidx : (commutator X).index = 2)
    (h4 : 4 ≤ Nat.card K) (hPSL : Nat.card (PSL2 K) = Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ s ∈ E, ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card K = Nat.card F ^ 2 ∧
      ∃ b c : F, (∀ t : F, t ^ 2 + b * t + c ≠ 0) ∧
        ∃ e' : (X ⧸ Subgroup.center X) ≃* ↥(CFSG.PGLModel.orthogonalMinus 1 F b c),
          IsRankOneIn ((e' (QuotientGroup.mk s) : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) F)) := by
  classical
  obtain ⟨s₀, hs₀, hs₀N, σ, hσσ, hσ1, hσ⟩ :=
    exists_involution_fieldAut_of_commutator_psl2 hS hcen e hidx
  obtain ⟨ξ, hξ⟩ : ∃ ξ : K, σ ξ ≠ ξ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  let D : HermInvol K := ⟨σ, hσσ, ξ, hξ⟩
  let f : ↥(commutator X) →* GL HermInvol.Ix D.F := D.psiN.comp e.toMonoidHom
  have hf_inj : Function.Injective f := (D.psiN_injective h4).comp e.injective
  have hf_orth : ∀ n : ↥(commutator X),
      f n ∈ CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c := by
    intro n
    obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e n)
    show D.psiN (e n) ∈ _
    rw [← hA, D.psiN_mk]
    exact D.slGL_mem_orth A
  have hconj : ∀ n : ↥(commutator X), D.Rg * f n * D.Rg⁻¹ =
      f ⟨s₀ * n * s₀⁻¹, (inferInstance : (commutator X).Normal).conj_mem n n.2 s₀⟩ := by
    intro n
    show _ = D.psiN (e ⟨_, _⟩)
    rw [hσ n, D.psiN_compat]
    rfl
  have hΓ : ∀ g : X, g ∈ commutator X ∨ g * s₀⁻¹ ∈ commutator X := fun g =>
    or_iff_not_imp_left.mpr fun hg => (Subgroup.mul_mem_iff_of_index_two hidx).mpr
      (iff_of_false hg fun h => hs₀N (inv_mem_iff.mp h))
  obtain ⟨ψ, hψN, hψσ, -⟩ := CFSG.ClassicalInvolution.Sp62Rec.I1.exists_hom_of_index_two
    (commutator X) s₀ (hS.oddT.mul_self_eq_one hs₀) hs₀N hΓ f D.Rg D.Rg_mul_self
    fun x hx => (hconj ⟨x, hx⟩).symm
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ Subgroup.centralizer ((commutator X : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 : ψ (x * n * x⁻¹) = ψ n := by
        rw [map_mul, map_mul, hx, map_inv, hx]; simp
      have hxn : x * n * x⁻¹ ∈ commutator X :=
        (inferInstance : (commutator X).Normal).conj_mem n hn x
      have h2 : f ⟨x * n * x⁻¹, hxn⟩ = f ⟨n, hn⟩ := by
        rw [← hψN (x * n * x⁻¹) hxn, ← hψN n hn]
        exact h1
      have h6 : x * n * x⁻¹ = n := congrArg Subtype.val (hf_inj h2)
      calc n * x = x * n * x⁻¹ * x := by rw [h6]
        _ = x * n := by group
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  have hψO : ∀ x, ψ x ∈ CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c := by
    intro x
    by_cases hx : x ∈ commutator X
    · have := hf_orth ⟨x, hx⟩
      rwa [← hψN x hx] at this
    · have hxs : x * s₀ ∈ commutator X :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hx hs₀N)
      have h1 : ψ (x * s₀) = ψ x * D.Rg := by rw [map_mul, hψσ]
      have h2 : ψ (x * s₀) = f ⟨x * s₀, hxs⟩ := hψN (x * s₀) hxs
      have h3 : ψ x = f ⟨x * s₀, hxs⟩ * D.Rg⁻¹ := by rw [← h2, h1]; group
      rw [h3]
      exact mul_mem (hf_orth _) (inv_mem D.Rg_mem_orth)
  let O := CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c
  let ψ' : X →* ↥O := ψ.codRestrict O hψO
  have hψ'inj : Function.Injective ψ' := fun a b h => hψinj (congrArg Subtype.val h)
  have hq : Nat.card K = Nat.card D.F ^ 2 := D.natCard_K
  have hcardX : Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) * 2 := by
    have h1 := Subgroup.card_mul_index (commutator X)
    rw [hidx, Nat.card_congr e.toEquiv, hPSL] at h1
    exact h1.symm
  have hcardO : Nat.card ↥O = Nat.card X := by
    have h1 := D.natCard_orth
    have h2 : 1 ≤ Nat.card D.F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h3 : 1 ≤ (Nat.card D.F ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
    rw [hcardX, hq]
    zify [h3]
    rw [h1]
    ring
  have hbij : Function.Bijective ψ' := hψ'inj.bijective_of_nat_card_le hcardO.le
  let eX : X ≃* ↥O := MulEquiv.ofBijective ψ' hbij
  have hcenter : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ Subgroup.centralizer ((commutator X : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact ((Subgroup.mem_center_iff.mp hz) h)
    rw [hcen] at this
    exact this
  let e' : (X ⧸ Subgroup.center X) ≃* ↥O :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans eX)
  refine ⟨s₀, hs₀, D.F, inferInstance, inferInstance, hq, D.b, D.c, D.irreducible, e', ?_⟩
  have hcoe : ((e' (QuotientGroup.mk s₀) : ↥O) : GL HermInvol.Ix D.F) = D.Rg := hψσ
  show Matrix.rank ((((e' (QuotientGroup.mk s₀) : ↥O) : GL HermInvol.Ix D.F) :
    Matrix HermInvol.Ix HermInvol.Ix D.F) - 1) = 1
  rw [hcoe, D.Rg_coe]
  exact D.rank_matR_sub_one

end GroupSide

end Herm

variable {X : Type} [Group X]

theorem exists_isOrthReflection_of_commutator_psl2Model [Finite X] {E : Set X} (hS : Setup X E)
    (hcen : Subgroup.centralizer (commutator X : Set X) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (e : ↥(commutator X) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f))
    (hidx : (commutator X).index = 2) : ∃ s ∈ E, IsOrthReflection X 4 f s := by
  have hf0 : 2 * f ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) := GaloisField.card 2 (2 * f) hf0
  have h4 : 4 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPSL : Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField 2 (2 * f))) =
      Nat.card (GaloisField 2 (2 * f)) * (Nat.card (GaloisField 2 (2 * f)) ^ 2 - 1) := by
    rw [hKcard]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even hf0
  obtain ⟨s, hs, F, hF, hFin, hq, b, c, hirr, e', hrank⟩ :=
    exists_orthMinus_model_of_commutator_psl2 hS hcen e hidx h4 hPSL
  refine ⟨s, hs, Or.inr ⟨1, le_rfl, rfl, F, hF, hFin, ?_, b, c, hirr, e', hrank⟩⟩
  have h2 : (Nat.card F) ^ 2 = (2 ^ f) ^ 2 := by
    rw [← hq, hKcard, ← pow_mul, mul_comm]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2


end CFSG.OddTranspositions.PartFour

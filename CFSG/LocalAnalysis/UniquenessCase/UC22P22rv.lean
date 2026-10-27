module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.Milestones.ASVolI.K3Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open CFSG.Quasithin.JonesParshall (uMat uMat_coe uMat_zero)
open CFSG.Quasithin.B45L2 (rootSub mem_rootSub rootSub_sq)
open scoped Matrix

section Model

variable {F : Type} [Field F]

theorem uc22p22r_op_omega_eq_range [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    StatedOmega (StatedQuadPlus 2 F) = (jProd (F := F)).range := by
  apply le_antisymm
  · have hidx : ((jProd (F := F)).range.subgroupOf
        (CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 F))).index = 2 := relIndex_jProd_range
    haveI hN : ((jProd (F := F)).range.subgroupOf
        (CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 F))).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    exact Subgroup.mem_subgroupOf.1 (uc22p22d_comm_mem_of_index_two hidx ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [jProd_apply]
    exact mul_mem (j1_mem_omega h4 a) (j2_mem_omega h4 b)

def uc22p22r_op_low (x : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

theorem uc22p22r_op_act_u1 [CharP F 2] (t : F) (v : Fin 2 ⊕ Fin 2 → F) :
    ((jProd (uMat t, 1) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      v + Pi.single (Sum.inl 0) (t * v (Sum.inl 1)) + Pi.single (Sum.inr 1) (t * v (Sum.inr 0)) := by
  rw [jProd_apply, map_one, mul_one, coe_j1, j1Mat_entries]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.fromBlocks_mulVec, uMat_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.single_apply, CharTwo.neg_eq] <;> ring

theorem uc22p22r_op_act_l1 [CharP F 2] (t : F) (v : Fin 2 ⊕ Fin 2 → F) :
    ((jProd (uc22p22r_op_low t, 1) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      v + Pi.single (Sum.inl 1) (t * v (Sum.inl 0)) + Pi.single (Sum.inr 0) (t * v (Sum.inr 1)) := by
  rw [jProd_apply, map_one, mul_one, coe_j1, j1Mat_entries]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [uc22p22r_op_low, Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.single_apply, CharTwo.neg_eq] <;> ring

theorem uc22p22r_op_act_u2 [CharP F 2] (t : F) (v : Fin 2 ⊕ Fin 2 → F) :
    ((jProd (1, uMat t) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      v + Pi.single (Sum.inl 0) (t * v (Sum.inr 1)) + Pi.single (Sum.inl 1) (t * v (Sum.inr 0)) := by
  rw [jProd_apply, map_one, one_mul, coe_j2, j1Mat_entries]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [uMat_coe, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Pi.single_apply, CharTwo.neg_eq, tauPerm_symm, tauPerm, Equiv.swap_apply_of_ne_of_ne] <;> ring

theorem uc22p22r_op_act_l2 [CharP F 2] (t : F) (v : Fin 2 ⊕ Fin 2 → F) :
    ((jProd (1, uc22p22r_op_low t) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      v + Pi.single (Sum.inr 1) (t * v (Sum.inl 0)) + Pi.single (Sum.inr 0) (t * v (Sum.inl 1)) := by
  rw [jProd_apply, map_one, one_mul, coe_j2, j1Mat_entries]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [uc22p22r_op_low, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Pi.single_apply, CharTwo.neg_eq, tauPerm_symm, tauPerm, Equiv.swap_apply_of_ne_of_ne] <;> ring

theorem uc22p22r_op_comm_smul [CharP F 2] (T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F))
    (hT : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
      (v : Fin 2 ⊕ Fin 2 → F), T (((jProd g : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) =
        ((jProd g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ T v) :
    ∃ μ : F, ∀ v, T v = μ • v := by
  classical
  have r1 : ∀ t v, T (Pi.single (Sum.inl 0) (t * v (Sum.inl 1))) +
      T (Pi.single (Sum.inr 1) (t * v (Sum.inr 0))) =
      Pi.single (Sum.inl 0) (t * T v (Sum.inl 1)) + Pi.single (Sum.inr 1) (t * T v (Sum.inr 0)) := by
    intro t v
    have h := hT (uMat t, 1) v
    rw [uc22p22r_op_act_u1, uc22p22r_op_act_u1, map_add, map_add, add_assoc, add_assoc] at h
    exact add_left_cancel h
  have r2 : ∀ t v, T (Pi.single (Sum.inl 1) (t * v (Sum.inl 0))) +
      T (Pi.single (Sum.inr 0) (t * v (Sum.inr 1))) =
      Pi.single (Sum.inl 1) (t * T v (Sum.inl 0)) + Pi.single (Sum.inr 0) (t * T v (Sum.inr 1)) := by
    intro t v
    have h := hT (uc22p22r_op_low t, 1) v
    rw [uc22p22r_op_act_l1, uc22p22r_op_act_l1, map_add, map_add, add_assoc, add_assoc] at h
    exact add_left_cancel h
  have r3 : ∀ t v, T (Pi.single (Sum.inl 0) (t * v (Sum.inr 1))) +
      T (Pi.single (Sum.inl 1) (t * v (Sum.inr 0))) =
      Pi.single (Sum.inl 0) (t * T v (Sum.inr 1)) + Pi.single (Sum.inl 1) (t * T v (Sum.inr 0)) := by
    intro t v
    have h := hT (1, uMat t) v
    rw [uc22p22r_op_act_u2, uc22p22r_op_act_u2, map_add, map_add, add_assoc, add_assoc] at h
    exact add_left_cancel h
  have r4 : ∀ t v, T (Pi.single (Sum.inr 1) (t * v (Sum.inl 0))) +
      T (Pi.single (Sum.inr 0) (t * v (Sum.inl 1))) =
      Pi.single (Sum.inr 1) (t * T v (Sum.inl 0)) + Pi.single (Sum.inr 0) (t * T v (Sum.inl 1)) := by
    intro t v
    have h := hT (1, uc22p22r_op_low t) v
    rw [uc22p22r_op_act_l2, uc22p22r_op_act_l2, map_add, map_add, add_assoc, add_assoc] at h
    exact add_left_cancel h
  have hab : T (Pi.single (Sum.inl 0) 1) (Sum.inl 1) = 0 := by
    simpa [Pi.single_apply] using (congrFun (r1 1 (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)).symm
  have had : T (Pi.single (Sum.inl 0) 1) (Sum.inr 1) = 0 := by
    simpa [Pi.single_apply] using (congrFun (r3 1 (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)).symm
  obtain ⟨μ, hμ⟩ : ∃ μ, T (Pi.single (Sum.inl 0) 1) (Sum.inl 0) = μ := ⟨_, rfl⟩
  have hB : ∀ t, T (Pi.single (Sum.inl 1) t) = Pi.single (Sum.inl 1) (t * μ) := by
    intro t
    simpa [Pi.single_apply, had, hμ] using r2 t (Pi.single (Sum.inl 0) 1)
  have hD : ∀ t, T (Pi.single (Sum.inr 1) t) = Pi.single (Sum.inr 1) (t * μ) := by
    intro t
    simpa [Pi.single_apply, hab, hμ] using r4 t (Pi.single (Sum.inl 0) 1)
  have hA : ∀ t, T (Pi.single (Sum.inl 0) t) = Pi.single (Sum.inl 0) (t * μ) := by
    intro t
    simpa [Pi.single_apply, hB] using r1 t (Pi.single (Sum.inl 1) 1)
  have hC : ∀ t, T (Pi.single (Sum.inr 0) t) = Pi.single (Sum.inr 0) (t * μ) := by
    intro t
    simpa [Pi.single_apply, hD] using r2 t (Pi.single (Sum.inr 1) 1)
  have hall : ∀ i t, T (Pi.single i t) = Pi.single i (t * μ) := by
    rintro (i | i) t <;> fin_cases i
    exacts [hA t, hB t, hC t, hD t]
  refine ⟨μ, fun v => ?_⟩
  rw [← Finset.univ_sum_single v, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hall]
  ext j
  by_cases hj : j = k
  · subst hj
    simp [mul_comm]
  · simp [Pi.single_eq_of_ne hj]

theorem uc22p22r_op_mulVec_mul
    (g h : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (w : Fin 2 ⊕ Fin 2 → F) :
    ((jProd (g * h) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w =
      ((jProd g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((jProd h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem uc22p22r_op_mulVec_inv
    (g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (w : Fin 2 ⊕ Fin 2 → F) :
    ((jProd g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((jProd g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) = w ∧
      ((jProd g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((jProd g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) = w := by
  rw [← uc22p22r_op_mulVec_mul, ← uc22p22r_op_mulVec_mul, inv_mul_cancel, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec]
  exact ⟨rfl, rfl⟩

theorem uc22p22r_op_fix_iff [CharP F 2] (w : Fin 2 ⊕ Fin 2 → F) :
    (∀ s t : F, ((jProd (uMat s, uMat t) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w = w) ↔
      w (Sum.inl 1) = 0 ∧ w (Sum.inr 0) = 0 ∧ w (Sum.inr 1) = 0 := by
  constructor
  · intro h
    have h1 := h 1 0
    have h3 := h 0 1
    rw [uMat_zero, uc22p22r_op_act_u1] at h1
    rw [uMat_zero, uc22p22r_op_act_u2] at h3
    have e1 := congrFun h1 (Sum.inl 0)
    have e2 := congrFun h1 (Sum.inr 1)
    have e3 := congrFun h3 (Sum.inl 0)
    simp [Pi.single_apply] at e1 e2 e3
    exact ⟨e1, e2, e3⟩
  · rintro ⟨hb, hc, hd⟩ s t
    have hst : ((uMat s, uMat t) : Matrix.SpecialLinearGroup (Fin 2) F ×
        Matrix.SpecialLinearGroup (Fin 2) F) = (uMat s, 1) * (1, uMat t) := by simp
    rw [hst, uc22p22r_op_mulVec_mul, uc22p22r_op_act_u2, hc, hd]
    simp only [mul_zero, Pi.single_zero, add_zero]
    rw [uc22p22r_op_act_u1, hb, hc]
    simp

theorem uc22p22r_op_card_line :
    Nat.card {w : Fin 2 ⊕ Fin 2 → F // w (Sum.inl 1) = 0 ∧ w (Sum.inr 0) = 0 ∧ w (Sum.inr 1) = 0} =
      Nat.card F := by
  classical
  refine Nat.card_congr
    { toFun := fun w => w.1 (Sum.inl 0)
      invFun := fun s => ⟨Pi.single (Sum.inl 0) s, by simp [Pi.single_apply]⟩
      left_inv := fun w => ?_
      right_inv := fun s => by simp }
  obtain ⟨w, hb, hc, hd⟩ := w
  refine Subtype.ext (funext fun i => ?_)
  rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply, hb, hc, hd]

end Model

section Sylow

variable {G : Type} [Group G]

theorem uc22p22r_op_le_of_pGroup {X S : Subgroup G} {m : ℕ} (hm : Odd m)
    (hpow : ∀ c ∈ Subgroup.centralizer (X : Set G), c ^ m = 1) (hS : IsPGroup 2 S)
    (hle : S ≤ X ⊔ Subgroup.centralizer (X : Set G)) : S ≤ X := by
  intro s hs
  have hcomm : ∀ (x : ↥X) (c : ↥(Subgroup.centralizer (X : Set G))),
      Commute (X.subtype x) ((Subgroup.centralizer (X : Set G)).subtype c) :=
    fun x c => Subgroup.mem_centralizer_iff.1 c.2 x x.2
  have hs' : s ∈ (MonoidHom.noncommCoprod X.subtype
      (Subgroup.centralizer (X : Set G)).subtype hcomm).range := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact hle hs
  obtain ⟨⟨x, c⟩, hxc⟩ := hs'
  rw [MonoidHom.noncommCoprod_apply] at hxc
  simp only [Subgroup.coe_subtype] at hxc
  obtain ⟨a, ha⟩ := hS ⟨s, hs⟩
  have hs2 : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hxcomm : Commute (x : G) (c : G) := hcomm x c
  rw [← hxc, hxcomm.mul_pow] at hs2
  have hc1 : (c : G) ^ 2 ^ a ∈ X := by
    rw [eq_inv_of_mul_eq_one_right hs2]
    exact inv_mem (pow_mem x.2 _)
  have hcop : Nat.Coprime (2 ^ a) (orderOf (c : G)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (hpow c c.2))
      (Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hm))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hxc]
  exact mul_mem x.2 (hk ▸ pow_mem hc1 k)

theorem uc22p22r_op_sylow_eq {p : ℕ} {S S' K : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) (hle : S ≤ S') (hS'K : S' ≤ K) (hS' : IsPGroup p S') :
    S' = S := by
  obtain ⟨Q, rfl⟩ := hS
  have h1 : S'.subgroupOf K = Q :=
    Q.is_maximal' hS'.comap_subtype fun q hq => Subgroup.mem_subgroupOf.2 (hle ⟨q, hq, rfl⟩)
  rw [← h1, Subgroup.map_subgroupOf_eq_of_le hS'K]

end Sylow

section Module

variable {H : Type} [Group H] [Finite H] {Vmod : Type} [AddCommGroup Vmod]
  [Module (ZMod 2) Vmod] [Finite Vmod] (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_op_model {X : Subgroup H} {n : ℕ} (hn : 2 ≤ n) (hO : NatOmegaPlus4 ρ X ⊤ ⊥ n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (ψ : Vmod ≃+ (Fin 2 ⊕ Fin 2 → F))
        (e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)),
        ∀ (x : ↥X) (v : Vmod), ψ (ρ (x : H) v) =
          ((jProd (e x) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v := by
  obtain ⟨F, hF1, hF2, hFcard, -, -, -, φ, ψ, -, hker, hsurj, hψ⟩ := hO
  haveI : CharP F 2 := uc22p22d_charP_two (by omega) hFcard
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h0 : ψ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hker (x - y) trivial h0
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this
  let ψe : Vmod ≃+ (Fin 2 ⊕ Fin 2 → F) :=
    AddEquiv.ofBijective ψ ⟨hψinj, fun y => by
      obtain ⟨x, -, hx⟩ := hsurj y
      exact ⟨x, hx⟩⟩
  let e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
    (φ.trans (MulEquiv.subgroupCongr (uc22p22r_op_omega_eq_range h4))).trans
      (MonoidHom.ofInjective jProd_injective).symm
  refine ⟨F, hF1, hF2, inferInstance, hFcard, ψe, e, fun x v => ?_⟩
  have h1 : jProd (e x) = ((φ x : ↥(StatedOmega (StatedQuadPlus 2 F))) : GL (Fin 2 ⊕ Fin 2) F) := by
    simp only [e, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  rw [h1]
  exact hψ x v trivial

theorem uc22p22r_op_scalar {X : Subgroup H} {F : Type} [Field F] [CharP F 2]
    (ψ : Vmod ≃+ (Fin 2 ⊕ Fin 2 → F))
    (e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F))
    (hψ : ∀ (x : ↥X) (v : Vmod), ψ (ρ (x : H) v) =
      ((jProd (e x) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v)
    {c : H} (hc : c ∈ Subgroup.centralizer (X : Set H)) : ∃ μ : F, ∀ v, ψ (ρ c v) = μ • ψ v := by
  let T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F) :=
    ψ.toAddMonoidHom.comp ((ρ c).toAddMonoidHom.comp ψ.symm.toAddMonoidHom)
  have hTapp : ∀ w, T w = ψ (ρ c (ψ.symm w)) := fun w => rfl
  obtain ⟨μ, hμ⟩ := uc22p22r_op_comm_smul T fun g w => by
    obtain ⟨x, rfl⟩ := e.surjective g
    have h1 : ψ.symm (((jProd (e x) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w) = ρ (x : H) (ψ.symm w) := by
      apply ψ.injective
      rw [ψ.apply_symm_apply, hψ, ψ.apply_symm_apply]
    have hcx : ρ c (ρ (x : H) (ψ.symm w)) = ρ (x : H) (ρ c (ψ.symm w)) := by
      have h := Subgroup.mem_centralizer_iff.1 hc (x : H) x.2
      rw [← Module.End.mul_apply, ← map_mul, ← h, map_mul, Module.End.mul_apply]
    rw [hTapp, hTapp, h1, hcx, hψ]
  exact ⟨μ, fun v => by simpa [hTapp] using hμ (ψ v)⟩

theorem uc22p22r_op_pow_eq_one (hfaith : Function.Injective ρ) {X : Subgroup H} {n : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hFcard : Nat.card F = 2 ^ n) (ψ : Vmod ≃+ (Fin 2 ⊕ Fin 2 → F))
    (e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F))
    (hψ : ∀ (x : ↥X) (v : Vmod), ψ (ρ (x : H) v) =
      ((jProd (e x) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v)
    {c : H} (hc : c ∈ Subgroup.centralizer (X : Set H)) : c ^ (2 ^ n - 1) = 1 := by
  obtain ⟨μ, hμ⟩ := uc22p22r_op_scalar ρ ψ e hψ hc
  have hpow : ∀ (j : ℕ) (v : Vmod), ψ (ρ (c ^ j) v) = μ ^ j • ψ v := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
      intro v
      rw [pow_succ, map_mul, Module.End.mul_apply, ih, hμ, smul_smul, ← pow_succ]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h := hpow (orderOf c) (ψ.symm (Pi.single (Sum.inl 0) 1))
    rw [pow_orderOf_eq_one, map_one, Module.End.one_apply, h0, zero_pow (orderOf_pos c).ne',
      zero_smul, ψ.apply_symm_apply] at h
    simpa using congrFun h (Sum.inl 0)
  letI : Fintype F := Fintype.ofFinite F
  have hμ1 : μ ^ (2 ^ n - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hFcard] at this
  apply hfaith
  rw [map_one]
  refine LinearMap.ext fun v => ψ.injective ?_
  rw [hpow, hμ1, one_smul, Module.End.one_apply]

theorem uc22p22r_op_card_fix {X K S : Subgroup H} {F : Type} [Field F] [Finite F] [CharP F 2]
    (ψ : Vmod ≃+ (Fin 2 ⊕ Fin 2 → F))
    (e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F))
    (hψ : ∀ (x : ↥X) (v : Vmod), ψ (ρ (x : H) v) =
      ((jProd (e x) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) (hSX : S ≤ X) (hXK : X ≤ K) :
    Nat.card ↥(fixOn ρ S ⊤) = Nat.card F := by
  classical
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
    (S.subgroupOf X).map e.toMonoidHom with hP
  have hPp : IsPGroup 2 P := hS.isPGroup.comap_subtype.map _
  obtain ⟨g₁, hg₁⟩ := CFSG.ASVolI.burnsideK312_sylow_conj (hPp.map (MonoidHom.fst _ _))
  obtain ⟨g₂, hg₂⟩ := CFSG.ASVolI.burnsideK312_sylow_conj (hPp.map (MonoidHom.snd _ _))
  set Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
    ((rootSub ⊤).map (MulAut.conj g₁).toMonoidHom).prod
      ((rootSub ⊤).map (MulAut.conj g₂).toMonoidHom) with hQ
  have hPQ : P ≤ Q := fun y hy =>
    Subgroup.mem_prod.2 ⟨hg₁ (Subgroup.mem_map_of_mem _ hy), hg₂ (Subgroup.mem_map_of_mem _ hy)⟩
  have hQp : IsPGroup 2 Q := by
    rintro ⟨q, hq⟩
    obtain ⟨⟨r₁, hr₁, h₁⟩, ⟨r₂, hr₂, h₂⟩⟩ := Subgroup.mem_prod.1 hq
    refine ⟨1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [pow_one, Subgroup.coe_pow, Prod.pow_fst, Subgroup.coe_one, Prod.fst_one]
      rw [← h₁, ← map_pow, rootSub_sq _ r₁ hr₁, map_one]
    · simp only [pow_one, Subgroup.coe_pow, Prod.pow_snd, Subgroup.coe_one, Prod.snd_one]
      rw [← h₂, ← map_pow, rootSub_sq _ r₂ hr₂, map_one]
  set S' : Subgroup H := (Q.map e.symm.toMonoidHom).map X.subtype with hS'
  have hSS' : S ≤ S' := fun s hs =>
    ⟨e.symm (e ⟨s, hSX hs⟩), ⟨e ⟨s, hSX hs⟩, hPQ ⟨⟨s, hSX hs⟩, hs, rfl⟩, rfl⟩, by simp⟩
  have hS'p : IsPGroup 2 S' := (hQp.map _).map _
  rw [← uc22p22r_op_sylow_eq hS hSS' ((Subgroup.map_subtype_le _).trans hXK) hS'p]
  set g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F := (g₁, g₂) with hg
  have hact : ∀ q v, ψ (ρ ((e.symm q : ↥X) : H) v) =
      ((jProd q : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v := by
    intro q v
    rw [hψ, e.apply_symm_apply]
  have hconj : ∀ k w, ((jProd (g * k * g⁻¹) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w =
      ((jProd g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((jProd k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          (((jProd g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w)) := by
    intro k w
    rw [uc22p22r_op_mulVec_mul, uc22p22r_op_mulVec_mul]
  have hmemQ : ∀ s t : F, g * (uMat s, uMat t) * g⁻¹ ∈ Q := fun s t =>
    Subgroup.mem_prod.2 ⟨⟨uMat s, mem_rootSub.2 ⟨s, AddSubgroup.mem_top s, rfl⟩, by simp [hg]⟩,
      ⟨uMat t, mem_rootSub.2 ⟨t, AddSubgroup.mem_top t, rfl⟩, by simp [hg]⟩⟩
  have hfix : ∀ v : Vmod, v ∈ fixOn ρ S' ⊤ ↔ ∀ s t : F,
      ((jProd (uMat s, uMat t) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (((jProd g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v) =
        ((jProd g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ ψ v := by
    intro v
    rw [mem_fixOn]
    constructor
    · rintro ⟨-, hv⟩ s t
      have h1 := congrArg ψ (hv _ ⟨e.symm _, ⟨_, hmemQ s t, rfl⟩, rfl⟩)
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom] at h1
      rw [hact, hconj] at h1
      nth_rw 2 [← h1]
      rw [(uc22p22r_op_mulVec_inv g _).1]
    · intro h
      refine ⟨trivial, ?_⟩
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨⟨r₁, h₁', h₁⟩, ⟨r₂, h₂', h₂⟩⟩ := Subgroup.mem_prod.1 hq
      obtain ⟨s, -, rfl⟩ := mem_rootSub.1 h₁'
      obtain ⟨t, -, rfl⟩ := mem_rootSub.1 h₂'
      have hq' : q = g * (uMat s, uMat t) * g⁻¹ :=
        Prod.ext (by rw [← h₁]; simp [hg]) (by rw [← h₂]; simp [hg])
      apply ψ.injective
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      rw [hact, hq', hconj, h s t, (uc22p22r_op_mulVec_inv g _).2]
  have hcard : Nat.card ↥(fixOn ρ S' ⊤) = Nat.card {w : Fin 2 ⊕ Fin 2 → F //
      w (Sum.inl 1) = 0 ∧ w (Sum.inr 0) = 0 ∧ w (Sum.inr 1) = 0} := by
    refine Nat.card_congr
      { toFun := fun v => ⟨_, (uc22p22r_op_fix_iff _).1 ((hfix v).1 v.2)⟩
        invFun := fun w => ⟨ψ.symm (((jProd g : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w.1), (hfix _).2 (by
              rw [ψ.apply_symm_apply, (uc22p22r_op_mulVec_inv g _).1]
              exact (uc22p22r_op_fix_iff _).2 w.2)⟩
        left_inv := fun v => Subtype.ext (by
          simp only
          rw [(uc22p22r_op_mulVec_inv g _).2, ψ.symm_apply_apply])
        right_inv := fun w => Subtype.ext (by
          simp only
          rw [ψ.apply_symm_apply, (uc22p22r_op_mulVec_inv g _).1]) }
  rw [hcard, uc22p22r_op_card_line]

theorem uc22p22r_F1_omegaPlus (hfaith : Function.Injective ρ) {X : Subgroup H} {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hn : 3 ≤ n) (hO : NatOmegaPlus4 ρ X ⊤ ⊥ n)
    {c : H} (hc : c ∈ Subgroup.centralizer (X : Set H)) {k : ℕ} (hck : c ^ (p ^ k) = 1) : c = 1 := by
  obtain ⟨F, _, _, _, hFcard, ψ, e, hψ⟩ := uc22p22r_op_model ρ (by omega) hO
  have hcop : Nat.Coprime (p ^ k) (2 ^ n - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (uc22p22g_not_dvd_pred hp hp2 hpn))
  have h := (pow_gcd_eq_one (a := c)).2 ⟨hck, uc22p22r_op_pow_eq_one ρ hfaith hFcard ψ e hψ hc⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

theorem uc22p22r_F2_omegaPlus (hfaith : Function.Injective ρ) {X : Subgroup H} {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hn : 3 ≤ n) (hO : NatOmegaPlus4 ρ X ⊤ ⊥ n)
    {S : Subgroup H} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (X ⊔ Subgroup.centralizer (X : Set H))) :
    ¬ Nat.card ↥(fixOn ρ S ⊤) ≡ 1 [MOD p] := by
  obtain ⟨F, _, _, _, hFcard, ψ, e, hψ⟩ := uc22p22r_op_model ρ (by omega) hO
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hSX : S ≤ X := uc22p22r_op_le_of_pGroup hodd
    (fun c hc => uc22p22r_op_pow_eq_one ρ hfaith hFcard ψ e hψ hc) hS.isPGroup hS.le
  rw [uc22p22r_op_card_fix ρ ψ e hψ hS hSX le_sup_left, hFcard]
  intro hmod
  exact uc22p22g_not_dvd_pred hp hp2 hpn ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hmod.symm)

end Module

end CFSG.LocalAnalysis.UniquenessCase.UC22

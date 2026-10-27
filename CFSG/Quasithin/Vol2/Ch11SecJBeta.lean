module

public import CFSG.Quasithin.Vol2.Ch11SecJSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

namespace Core

variable (C : Core G T L I n V₁)

theorem psi_conj (l : ↥L) (a b : ↥(fsuV T I)) (hab : (b : G) = l * a * (l : G)⁻¹) :
    C.St.D.ψ b = natAct3 (C.St.D.θ l) (C.St.D.ψ a) := by
  have h : conjAct (fsuV T I) ⟨l, C.St.D.hnorm l.2⟩ a = b :=
    Subtype.ext (by rw [conjAct_coe_apply, hab])
  rw [← h, C.St.D.equiv]

@[expose] noncomputable def betaV : ↥(fsuV T I) →* Wm (GaloisField 2 n) :=
  p12.comp C.St.D.ψ.toMonoidHom

theorem betaV_apply (v : ↥(fsuV T I)) : C.betaV v = p12 (C.St.D.ψ v) := rfl

theorem betaV_surjective : Function.Surjective C.betaV := by
  intro w
  obtain ⟨v, hv⟩ := C.St.D.ψ.surjective
    (Multiplicative.ofAdd ![0, Multiplicative.toAdd w 0, Multiplicative.toAdd w 1])
  refine ⟨v, ?_⟩
  rw [betaV_apply, hv]
  apply Multiplicative.toAdd.injective
  rw [toAdd_p12]
  ext i
  fin_cases i <;> simp

theorem betaV_ker : C.betaV.ker = V₁.subgroupOf (fsuV T I) := by
  ext v
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, C.St.D.line v, betaV_apply]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_p12, toAdd_one] at h'
    refine ⟨Multiplicative.toAdd (C.St.D.ψ v) 0, ?_⟩
    ext i
    fin_cases i
    · simp
    · simpa using congrFun h' 0
    · simpa using congrFun h' 1
  · rintro ⟨c, hc⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_p12, hc, toAdd_one]
    ext i
    fin_cases i <;> simp

theorem betaV_conj_of_mem_Pt (l : ↥L) (hl : C.St.D.θ l ∈ Pt (vE (GaloisField 2 n) 0))
    (a b : ↥(fsuV T I)) (hab : (b : G) = l * a * (l : G)⁻¹) :
    Multiplicative.toAdd (C.betaV b) =
      blk22 (C.St.D.θ l).1 *ᵥ Multiplicative.toAdd (C.betaV a) := by
  rw [betaV_apply, betaV_apply, C.psi_conj l a b hab, p12_natAct3 hl]

theorem betaV_conj (k : ↥(LOf L V₁)) (a b : ↥(fsuV T I)) (hab : (b : G) = k * a * (k : G)⁻¹) :
    Multiplicative.toAdd (C.betaV b) =
      ((C.alpha k : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ
        Multiplicative.toAdd (C.betaV a) := by
  rw [C.coe_alpha]
  exact C.betaV_conj_of_mem_Pt ⟨k, lOf_le_L k.2⟩ (C.theta_mem_Pt k) a b hab

theorem betaV_conj_dg (l : ↥L) {c : GaloisField 2 n} (hc : c ≠ 0) (hl : C.St.D.θ l = dg c hc)
    (a b : ↥(fsuV T I)) (hab : (b : G) = l * a * (l : G)⁻¹) :
    Multiplicative.toAdd (C.betaV b) = c • Multiplicative.toAdd (C.betaV a) := by
  rw [betaV_apply, betaV_apply, C.psi_conj l a b hab, hl, p12_natAct3_dg]

@[expose] noncomputable def thetaU :
    ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →*
      ↥(qhom : Wm (GaloisField 2 n) →* SL(3, GaloisField 2 n)).range :=
  (C.St.D.θ.comp (Subgroup.inclusion C.hUL)).codRestrict _ fun u => by
    rw [qhom_range]
    exact C.theta_mem_Qv_of_mem_U u.2

@[expose] noncomputable def betaU :
    ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →* Wm (GaloisField 2 n) :=
  (MonoidHom.ofInjective qhom_injective).symm.toMonoidHom.comp C.thetaU

theorem qhom_betaU (u : ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    qhom (C.betaU u) = C.St.D.θ ⟨u, C.hUL u.2⟩ := by
  have h := (MonoidHom.ofInjective (qhom_injective (F := GaloisField 2 n))).apply_symm_apply
    (C.thetaU u)
  exact congrArg Subtype.val h

theorem betaU_surjective : Function.Surjective C.betaU := by
  intro q
  have hq : qhom q ∈ Qv (vE (GaloisField 2 n) 0) := by
    rw [← qhom_range]
    exact ⟨q, rfl⟩
  obtain ⟨u, hu, hθ⟩ := C.exists_theta_eq hq
  refine ⟨⟨u, hu⟩, qhom_injective ?_⟩
  rw [qhom_betaU, hθ]

theorem betaU_ker :
    C.betaU.ker =
      (fsuV T I).subgroupOf (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.theta_eq_one_iff ⟨u, C.hUL u.2⟩,
    ← C.qhom_betaU]
  exact ⟨fun h => by rw [h, map_one], fun h => qhom_injective (by rw [h, map_one])⟩

theorem theta_conj (l : ↥L) (a b : ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))))
    (hab : (b : G) = l * a * (l : G)⁻¹) :
    C.St.D.θ ⟨b, C.hUL b.2⟩ = C.St.D.θ l * C.St.D.θ ⟨a, C.hUL a.2⟩ * (C.St.D.θ l)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hab

theorem betaU_conj_of_mem_Pt1 (l : ↥L) (hl : C.St.D.θ l ∈ Pt1 (GaloisField 2 n))
    (a b : ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))))
    (hab : (b : G) = l * a * (l : G)⁻¹) :
    Multiplicative.toAdd (C.betaU b) =
      blk22 (C.St.D.θ l).1 *ᵥ Multiplicative.toAdd (C.betaU a) := by
  have h2 : qhom (C.betaU b) =
      qhom (Multiplicative.ofAdd (blk22 (C.St.D.θ l).1 *ᵥ Multiplicative.toAdd (C.betaU a))) := by
    rw [C.qhom_betaU, C.theta_conj l a b hab, ← C.qhom_betaU a, mul_qhom hl,
      mul_inv_cancel_right]
  rw [qhom_injective h2, toAdd_ofAdd]

theorem betaU_conj (k : ↥(LOf L V₁))
    (a b : ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))))
    (hab : (b : G) = k * a * (k : G)⁻¹) :
    Multiplicative.toAdd (C.betaU b) =
      ((C.alpha k : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ
        Multiplicative.toAdd (C.betaU a) := by
  rw [C.coe_alpha]
  exact C.betaU_conj_of_mem_Pt1 ⟨k, lOf_le_L k.2⟩ (C.theta_mem_Pt1 k) a b hab

theorem betaU_conj_dg (l : ↥L) {c : GaloisField 2 n} (hc : c ≠ 0) (hl : C.St.D.θ l = dg c hc)
    (a b : ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))))
    (hab : (b : G) = l * a * (l : G)⁻¹) :
    Multiplicative.toAdd (C.betaU b) = (c ^ 3)⁻¹ • Multiplicative.toAdd (C.betaU a) := by
  have h2 : qhom (C.betaU b) =
      qhom (Multiplicative.ofAdd ((c ^ 3)⁻¹ • Multiplicative.toAdd (C.betaU a))) := by
    rw [C.qhom_betaU, C.theta_conj l a b hab, ← C.qhom_betaU a, hl, dg_mul_qhom,
      mul_inv_cancel_right]
  rw [qhom_injective h2, toAdd_ofAdd]

end Core

end CFSG.Quasithin.Vol2.Ch11.SecJ

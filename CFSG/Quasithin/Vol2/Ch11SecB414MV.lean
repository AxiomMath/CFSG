module

public import CFSG.Quasithin.Vol2.Ch11SecB414MU
public import CFSG.Quasithin.Vol2.Ch11SecB414MF
public import CFSG.Quasithin.Vol2.Ch11SecB414MR

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F]

theorem cnj_uMat_00 (w : Fin 2 → F) (M : Matrix (Fin 3) (Fin 3) F) :
    cnj (uMat w : Matrix (Fin 3) (Fin 3) F) M 0 0 = M 0 0 + w 0 * M 1 0 + w 1 * M 2 0 := by
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, coe_uMat]
  simp [adjugate_fin_three]

theorem dg_conj_uMat (c : Fˣ) (w : Fin 2 → F) :
    dgHom c * SpecialLinearGroup.toGL (uMat w) * (dgHom c)⁻¹ =
      SpecialLinearGroup.toGL (uMat ((c : F) • w)) := by
  apply Units.ext
  simp only [Units.val_mul, coe_dgHom, coe_dgHom_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_uMat]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

variable [Finite F] [CharP F 2] (hF : Nat.card F = 4)
include hF

theorem isNatEigSection_pCore (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F))
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
      T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    (c : Fˣ) {μ : F} (hμ : ∀ w : Fin 2 → F, T ((c : F) • w) = μ • T w) :
    IsNatEigSection (Ptheta F 0) (ProjGenLinGroup.mk (dgHom c)) α₀' ⊥
      (pCoreOf 2 (Ptheta F 0)) μ := by
  refine isNatEigSection_of_coords α₀' (betaRef hF).toMonoidHom (betaRef hF).surjective
    (fun u => ?_) (fun p => ((rhoRef hF p : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) (fun p u u' h => betaRef_conj hF p u u' h) T hT
    (fun u u' h => ?_) hμ
  · rw [MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, Subgroup.mem_bot]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  · have hu := iota0_betaRef hF u
    have e : (u' : PGL3 F) = iota0 (Multiplicative.ofAdd
        ((c : F) • Multiplicative.toAdd (betaRef hF u))) := by
      rw [h, ← hu, iota0_apply, iota0_apply, toAdd_ofAdd, ← map_inv, ← map_mul, ← map_mul,
        dg_conj_uMat]
    have e2 : betaRef hF u' =
        Multiplicative.ofAdd ((c : F) • Multiplicative.toAdd (betaRef hF u)) := by
      apply iota0_injective
      rw [iota0_betaRef, e]
    show Multiplicative.toAdd (betaRef hF u') = _
    rw [e2, toAdd_ofAdd]
    rfl

variable {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F}

omit [Finite F] [CharP F 2] in
theorem pow_three_of_scalar (T : (Fin 2 → F) ≃+ (Fin 2 → F)) (c : Fˣ) {μ : F}
    (hμ : ∀ w : Fin 2 → F, T ((c : F) • w) = μ • T w) : μ ^ 3 = 1 := by
  have h := tScalar_pow T hμ 3 (T.symm ![1, 0])
  rw [pow_three_eq_one hF c.ne_zero, one_smul, AddEquiv.apply_symm_apply] at h
  have := congrFun h 0
  simpa using this.symm

omit [Finite F] [CharP F 2] hF in
theorem multiset_eig {μ : F} (h3 : μ ^ 3 = 1) (k : ℕ) :
    ({μ ^ (k + 1), μ ^ (2 * k), μ ^ (k + 2)} : Multiset F) =
      {μ ^ (k + 1), (μ ^ k)⁻¹, μ ^ k * μ⁻¹} := by
  have hμ0 : μ ≠ 0 := fun h => by simp [h] at h3
  have hb : μ ^ (2 * k) = (μ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, h3, one_pow])
  have hc : μ ^ (k + 2) = μ ^ k * μ⁻¹ := by
    rw [pow_add]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  rw [hb, hc]

theorem Model.concl_normal (m : Model Γ V Z F k α) (hk3 : k < 3) (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ} (hν : ν ≠ 1)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν))) :
    Concl Γ V Z L X F α (Ptheta F 0) k := by
  refine ⟨fun hk0 => ?_, fun hk0 => m.twistedFixed hF hLΓ hXΓ hL hν hX hk3 hk0, k, hk3, Iff.rfl,
    fun hk1 v hv hvfix hO => ?_, fun α₀' hs hk α₀ hcomp γx hγx _ => ?_⟩
  · subst hk0
    exact m.untwistedFixed hF hLΓ hXΓ hL hν hX
  · subst hk1
    have hvf := (fixed_iff hF hν 1 _).mp ((m.isFixedMod_iff hXΓ hX hv).mp hvfix)
    simp only [facE_one] at hvf
    have hcol : ∀ w : Fin 2 → F, w 0 * Multiplicative.toAdd (m.β ⟨v, hv⟩) 1 0 +
        w 1 * Multiplicative.toAdd (m.β ⟨v, hv⟩) 2 0 = 0 := by
      intro w
      have hw : iota0 (Multiplicative.ofAdd w) ∈ pCoreOf 2 (Ptheta F 0) := by
        rw [← range_iota0 hF]
        exact ⟨_, rfl⟩
      have hwL : iota0 (Multiplicative.ofAdd w) ∈ (L.subgroupOf Γ).map α := by
        rw [hL]
        exact CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
      obtain ⟨γ, -, hγ⟩ := hwL
      have hαγ : α γ ∈ pCoreOf 2 (Ptheta F 0) := by rw [hγ]; exact hw
      have h1 := hO γ hαγ
      have hg : ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uMat w)) = α γ := by
        rw [hγ, iota0_apply, toAdd_ofAdd]
      have h2 := (m.comm_mem_iff hg hv).mp h1
      rw [twAdj_toGL] at h2
      have h3 := congrFun (congrFun h2 0) 0
      rw [cnj_uMat_00] at h3
      linear_combination h3
    have h10 := hcol ![1, 0]
    have h20 := hcol ![0, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero,
      zero_add] at h10 h20
    refine (m.toAdd_eq_zero ⟨v, hv⟩).mp ?_
    ext i j
    by_cases hij : i ≠ 0 ∧ j = 0
    · obtain ⟨hi, rfl⟩ := hij
      fin_cases i
      · exact absurd rfl hi
      · simpa using h10
      · simpa using h20
    · simpa using hvf i j hij
  · obtain ⟨T, hT⟩ := exists_intertwine_levi hF α₀' hs hk
    obtain ⟨c, hc⟩ := exists_dg_of_mem hXΓ hX hγx
    have hc' : α γx = ProjGenLinGroup.mk (dgHom c) := hc
    obtain ⟨μ, hμ⟩ := exists_scalar_of_intertwine α₀' hs
      (fun p => ((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) T hT c
    have hα₀s : Function.Surjective α₀ := by
      intro s
      obtain ⟨p, rfl⟩ := hs s
      have hpL : (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ∈
          (L.subgroupOf Γ).map α := by
        rw [hL]
        exact p.2
      obtain ⟨γ, hγ, hγp⟩ := hpL
      exact ⟨⟨γ, Subgroup.mem_subgroupOf.mp hγ⟩, hcomp _ γ p rfl hγp.symm⟩
    refine ⟨μ, ?_, ?_⟩
    · have h := isNatEigSection_pCore hF α₀' T hT c hμ
      rw [← hc'] at h
      exact h
    · rw [← multiset_eig (pow_three_of_scalar hF T c hμ) k]
      by_cases hk0 : k = 0
      · subst hk0
        exact m.labSeries_untwisted hF hLΓ hXΓ hL hν hX α₀' α₀ hα₀s hcomp T hT hc' hμ
      · exact m.labSeries_twisted hF hk3 hk0 hLΓ hXΓ hL hν hX α₀' α₀ hα₀s hcomp T hT hc' hμ

end CFSG.Quasithin.H13.Ch4.B414.M

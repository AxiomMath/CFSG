module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Basic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_Z_mem (hc : Ctx M Q Z B) {k z : G} (hk : k ∈ M) (hz : z ∈ Z) : k * z * k⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hk) z).mp hz

theorem comm_mem_Z_of_Q (hc : Ctx M Q Z B) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ Z :=
  hc.hyp.toHyp79.comm_mem_V hx hy

theorem Q1_mul_right (hc : Ctx M Q Z B) {y q : G} (hy : y ∈ M) (hq : q ∈ Q) :
    Q1 hc (y * q) = Q1 hc y := by
  have hyq : y * q ∈ M := M.mul_mem hy (hc.hyp.Q_normal.1 hq)
  ext x
  rw [hc.mem_Q1_iff hyq, hc.mem_Q1_iff hy]
  have e : ⁅y * q, x⁆ = y * ⁅q, x⁆ * y⁻¹ * ⁅y, x⁆ := by
    simp only [commutatorElement_def]; group
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h1 : y * ⁅q, x⁆ * y⁻¹ ∈ Z := conj_Z_mem hc hy (comm_mem_Z_of_Q hc hq hx)
    rw [e] at h
    exact (Z.mul_mem_cancel_left h1).mp h
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [e]
    exact Z.mul_mem (conj_Z_mem hc hy (comm_mem_Z_of_Q hc hq hx)) h

theorem Q1_congr (hc : Ctx M Q Z B) {y y' : G} (hy : y ∈ M) (hy' : y' ∈ M)
    (h : y⁻¹ * y' ∈ Q) : Q1 hc y' = Q1 hc y := by
  have := Q1_mul_right hc hy h
  rwa [mul_inv_cancel_left] at this

end Basic

section Case1

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.conj_CN_eq_of_B_le (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) {g ρ : G} (hg : g ∈ M)
    (hρ : ρ ∈ Rt M (LB M Q B) t)
    (hB : conjSubgroup ρ B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    conjSubgroup g (hc.CN t) = hc.CN t := by
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hk : g⁻¹ * ρ ∈ M := M.mul_mem (M.inv_mem hg) hρM
  have hle : conjSubgroup (g⁻¹ * ρ) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le ?_ sec39_Z_le_Vt
    have h1 : conjSubgroup (g⁻¹ * ρ) B ≤
        conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
      rw [conjSubgroup_mul]
      exact Subgroup.map_mono hB
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h1
  obtain ⟨r, hr, hrBZ⟩ := e.conj_orbit I (g⁻¹ * ρ) hk hle
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hLeq : conjSubgroup (g⁻¹ * ρ) (LB M Q B) = conjSubgroup r (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ hk hrM hrBZ
  have hNL : hc.CN t ≤ conjSubgroup (g⁻¹ * ρ) (LB M Q B) := by
    rw [hLeq]
    exact e.CN_le_conj_LB I hr
  have hNgL : conjSubgroup g (hc.CN t) ≤ conjSubgroup ρ (LB M Q B) := by
    have h1 : conjSubgroup g (hc.CN t) ≤ conjSubgroup g (conjSubgroup (g⁻¹ * ρ) (LB M Q B)) :=
      Subgroup.map_mono hNL
    rwa [← conjSubgroup_mul, mul_inv_cancel_left] at h1
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_conjSubgroup])
  have hyL : ρ⁻¹ * y * ρ ∈ LB M Q B := mem_conjSubgroup.mp (hNgL hy)
  have hx : g⁻¹ * y * g ∈ hc.CN t := mem_conjSubgroup.mp hy
  have hx' : ρ⁻¹ * (g⁻¹ * y * g) * ρ ∈ hc.CN t := by
    have := hc.CN_conj_mem e.hs.toSec5.mem ((Rt M (LB M Q B) t).inv_mem hρ) hx
    simpa using this
  have hk' : ρ⁻¹ * g * ρ ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hρM) hg) hρM
  have hcl := h63b _ hx' _ hk' (by
    rw [show ρ⁻¹ * g * ρ * (ρ⁻¹ * (g⁻¹ * y * g) * ρ) * (ρ⁻¹ * g * ρ)⁻¹ = ρ⁻¹ * y * ρ by group]
    exact hyL)
  rw [show ρ⁻¹ * g * ρ * (ρ⁻¹ * (g⁻¹ * y * g) * ρ) * (ρ⁻¹ * g * ρ)⁻¹ = ρ⁻¹ * y * ρ by group]
    at hcl
  have := hc.CN_conj_mem e.hs.toSec5.mem hρ hcl
  rwa [show ρ * (ρ⁻¹ * y * ρ) * ρ⁻¹ = y by group] at this

theorem Env.conj_CN_eq_of_fuse (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) {g : G} (hg : g ∈ M) {x a : G}
    (hx : x ∈ hc.CN t) (hxQ : x ∉ Q) (ha : a ∈ hc.CN t) (haQ : a ∉ Q)
    (hxa : x⁻¹ * (g * a * g⁻¹) ∈ Q) : conjSubgroup g (hc.CN t) = hc.CN t := by
  have hxM : x ∈ M := e.CN_le_M hx
  have haM : a ∈ M := e.CN_le_M ha
  have hgaM : g * a * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg haM) (M.inv_mem hg)
  have h1 : Q1 hc (g * a * g⁻¹) = Q1 hc x := Q1_congr hc hxM hgaM hxa
  have h2 : Q1 hc (g * a * g⁻¹) = conjSubgroup g (Q1 hc a) := Q1_conj hc hg haM
  rw [e.Q1_eq_V I hx hxQ] at h1
  rw [e.Q1_eq_V I ha haQ] at h2
  have hVg : Vt M (LB M Q B) B Z t = conjSubgroup g (Vt M (LB M Q B) B Z t) := h1.symm.trans h2
  refine e.conj_CN_eq_of_B_le I h63b hg (Subgroup.one_mem _) ?_
  rw [conjSubgroup_one, ← hVg]
  exact hc.B_le_Vt e.hs.toSec5.mem

end Case1

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.exists_model_scalar (I : Inputs) (e : Env hc n t m X) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K 2) (Q' : QuadraticForm K (ι → K)) (X' : Subgroup (GL ι K))
      (E : ElemMatrixIso Q' X') (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (ι → K)) (u : ι → K),
      Nat.card K = Nat.card Z ∧ AddCommutantScalar X' ∧ OmegaGeom Q' m ∧
        OmegaModel hc t Q' E φ ψ u := by
  have hs := e.hs.toSec5
  have hnatSO := natSO_of_omega e.hm e.hΩ
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  rcases e.hΩ with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by have := e.hm; omega⟩⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hgeom := omegaGeom_plus (K := K) e.hm
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [hgeom.dim]; have := e.hm; omega
    obtain ⟨u, hQu, hu0, hB, -, hL, hr'⟩ := hc.omega_points_core I.h34 I.hRoot hs hnatSO hK
      (ElemMatrixIso.plus e.hm) (nondegenerate_polarBilin_quadPlus m K) h3
      (addCommutantScalar_statedOmegaPlus e.hm) φ hφ hker ψ hψ
      (hc.omega_singular I.h34 I.hRoot hs hnatSO hK (ElemMatrixIso.plus e.hm)
        (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus e.hm)
        φ hφ ψ hψ)
    exact ⟨Fin m ⊕ Fin m, inferInstance, inferInstance, K, fK, finK, inferInstance, quadPlus m K,
      _, ElemMatrixIso.plus e.hm, φ, hn, ψ, u, hK, addCommutantScalar_statedOmegaPlus e.hm, hgeom,
      ⟨hφ, hker, hψ, hQu, hu0, hB, hL, fun r => (hr' r).2⟩⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hgeom := omegaGeom_minus (K := K) e.hm hirr
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [hgeom.dim]; have := e.hm; omega
    obtain ⟨u, hQu, hu0, hB, -, hL, hr'⟩ := hc.omega_points_core I.h34 I.hRoot hs hnatSO hK
      (ElemMatrixIso.minus (by have := e.hm; omega) hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr) φ hφ hker ψ hψ
      (hc.omega_singular I.h34 I.hRoot hs hnatSO hK
        (ElemMatrixIso.minus (by have := e.hm; omega) hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr) φ hφ ψ hψ)
    exact ⟨Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, inferInstance, inferInstance, K, fK, finK,
      inferInstance, quadMinus m K b c, _, ElemMatrixIso.minus (by have := e.hm; omega) hirr, φ,
      hn, ψ, u, hK, addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr, hgeom,
      ⟨hφ, hker, hψ, hQu, hu0, hB, hL, fun r => (hr' r).2⟩⟩

end Model

section Scalar

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {u : ι → K}

theorem OmegaModel.exists_scalar (I : Inputs) (e : Env hc n t m X) (hX : AddCommutantScalar X')
    (hmod : OmegaModel hc t Q' E φ ψ u) {a : G} (ha : a ∈ hc.CN t) :
    ∃ c : K, ∀ x ∈ Q, vecOf ψ ⁅a, x⁆ = c • vecOf ψ ⁅x, t⁆ := by
  have hχ := e.chi I.h34
  have hNR : ∀ a ∈ hc.CN t, a ∈ Rt M (LB M Q B) t := fun a ha => (Ctx.mem_CN.mp ha).1
  have haR := hNR a ha
  have haM : a ∈ M := hc.Rt_le_M t haR
  have hQM : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hc1 : ∀ x ∈ Q, ⁅a, x⁆ ∈ Vt M (LB M Q B) B Z t := fun x hx => e.comm_mem_V I.h34 ha hx
  have hQQ : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z := fun x hx y hy => comm_mem_Z_of_Q hc hx hy
  have hQV : ∀ x ∈ Q, ∀ g ∈ Vt M (LB M Q B) B Z t,
      x * g * x⁻¹ ∈ Vt M (LB M Q B) B Z t ∧ vecOf ψ (x * g * x⁻¹) = vecOf ψ g := by
    intro x hx g hg
    have hxg : x * g * x⁻¹ = ⁅x, g⁆ * g := by
      simp only [commutatorElement_def]
      group
    have hz : ⁅x, g⁆ ∈ Z := hQQ x hx g (hVQ hg)
    rw [hxg]
    exact ⟨(Vt M (LB M Q B) B Z t).mul_mem (hZV hz) hg, by
      rw [vecOf_mul ψ (hZV hz) hg, vecOf_of_mem_Z ψ hz hZV, zero_add]⟩
  have hadd : ∀ x ∈ Q, ∀ y ∈ Q, vecOf ψ ⁅a, x * y⁆ = vecOf ψ ⁅a, x⁆ + vecOf ψ ⁅a, y⁆ := by
    intro x hx y hy
    have hid : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hid, vecOf_mul ψ (hc1 x hx) (hQV x hx _ (hc1 y hy)).1, (hQV x hx _ (hc1 y hy)).2]
  have hV0 : ∀ x ∈ Vt M (LB M Q B) B Z t, vecOf ψ ⁅a, x⁆ = 0 := fun x hx =>
    (vecOf_eq_zero_iff ψ (hc1 x (hVQ hx))).mpr ((Ctx.mem_CN.mp ha).2 x hx)
  have hequi : ∀ (r : ↥(Rt M (LB M Q B) t)) (x : ↥Q),
      vecOf ψ ⁅a, (r : G) * x * (r : G)⁻¹⁆ =
        (φ r : Matrix ι ι K) *ᵥ vecOf ψ ⁅a, (x : G)⁆ := by
    intro r x
    have hq1 : ⁅(r : G)⁻¹, a⁆ ∈ Q := e.N_central I.h34 _ ((Rt M (LB M Q B) t).inv_mem r.2) a ha
    have hid : ⁅a, (r : G) * x * (r : G)⁻¹⁆ =
        (r : G) * ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ * (r : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hid2 : ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ =
        (⁅(r : G)⁻¹, a⁆ * ⁅a, (x : G)⁆ * ⁅(r : G)⁻¹, a⁆⁻¹) * ⁅⁅(r : G)⁻¹, a⁆, (x : G)⁆ := by
      simp only [commutatorElement_def]
      group
    have hmemN : ⁅(r : G)⁻¹, a⁆ * a ∈ hc.CN t :=
      (hc.CN t).mul_mem (hc.Q_le_CN e.hs.toSec5.mem hq1) ha
    have hg : ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ ∈ Vt M (LB M Q B) B Z t :=
      e.comm_mem_V I.h34 hmemN x.2
    have hq1V : (⁅(r : G)⁻¹, a⁆ * ⁅a, (x : G)⁆ * ⁅(r : G)⁻¹, a⁆⁻¹) ∈ Vt M (LB M Q B) B Z t := by
      have := (hQV _ hq1 _ (hc1 x x.2)).1
      simpa [mul_assoc] using this
    have hzz : ⁅⁅(r : G)⁻¹, a⁆, (x : G)⁆ ∈ Z := hQQ _ hq1 _ x.2
    have hv : vecOf ψ ⁅(⁅(r : G)⁻¹, a⁆ * a), (x : G)⁆ = vecOf ψ ⁅a, (x : G)⁆ := by
      rw [hid2, vecOf_mul_Z ψ hq1V hzz hZV]
      have := (hQV _ hq1 _ (hc1 x x.2)).2
      simpa [mul_assoc] using this
    rw [hid, vecOf_conj ψ φ hmod.equi (hc.Rt_normalizes_Vt e.hs.toSec5.mem) r hg, hv]
  obtain ⟨c, hc'⟩ := exists_scalar_of_chi hχ ψ φ hmod.equi (hc.Rt_normalizes_Vt e.hs.toSec5.mem)
    hQM (by rw [hmod.range]; exact hX) (fun x => vecOf ψ ⁅a, x⁆) hadd hV0
    (fun r x => hequi r x)
  exact ⟨c, hc'⟩

theorem OmegaModel.exists_chiVec (I : Inputs) (e : Env hc n t m X) (w : ι → K) :
    ∃ x ∈ Q, vecOf ψ ⁅x, t⁆ = w := by
  have hχ := e.chi I.h34
  obtain ⟨v, hv⟩ := exists_secVec_eq ψ w
  obtain ⟨x, hxQ, hxv⟩ := hχ.2.1 (v : G) v.2
  refine ⟨x, hxQ, ?_⟩
  rw [vecOf_of_mem ψ (hχ.1 x hxQ), ← hv]
  exact (secVec_eq_iff ψ _ v).mpr hxv

theorem OmegaModel.exists_elt_scalar (I : Inputs) (e : Env hc n t m X)
    (hX : AddCommutantScalar X') (hK : Nat.card K = Nat.card Z)
    (hmod : OmegaModel hc t Q' E φ ψ u) (lam : K) :
    ∃ a ∈ hc.CN t, ∀ x ∈ Q, vecOf ψ ⁅a, x⁆ = lam • vecOf ψ ⁅x, t⁆ := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  have hNM : hc.CN t ≤ M := e.CN_le_M
  obtain ⟨x₀, hx₀Q, hx₀⟩ := OmegaModel.exists_chiVec (ψ := ψ) I e u
  have huν : ∀ c c' : K, c • u = c' • u → c = c' := fun c c' h =>
    smul_left_injective K hmod.u0 h
  choose cof hcof using fun a : ↥(hc.CN t) => hmod.exists_scalar I e hX a.2
  have hcofx : ∀ (a : ↥(hc.CN t)) (x : G), x ∈ Q → vecOf ψ ⁅(a : G), x⁆ = cof a • vecOf ψ ⁅x, t⁆ :=
    fun a x hx => hcof a x hx
  have hmul : ∀ a b : ↥(hc.CN t), cof (a * b) = cof a + cof b := by
    intro a b
    refine huν _ _ ?_
    have hb := e.comm_mem_V I.h34 b.2 hx₀Q
    have hid : ⁅((a * b : ↥(hc.CN t)) : G), x₀⁆ =
        (a : G) * ⁅(b : G), x₀⁆ * (a : G)⁻¹ * ⁅(a : G), x₀⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    have hz : ⁅(a : G), ⁅(b : G), x₀⁆⁆ ∈ Z := (Ctx.mem_CN.mp a.2).2 _ hb
    have hcj : (a : G) * ⁅(b : G), x₀⁆ * (a : G)⁻¹ = ⁅(a : G), ⁅(b : G), x₀⁆⁆ * ⁅(b : G), x₀⁆ := by
      simp only [commutatorElement_def]
      group
    have hcjV : (a : G) * ⁅(b : G), x₀⁆ * (a : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := by
      rw [hcj]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hZV hz) hb
    have h1 := hcofx (a * b) x₀ hx₀Q
    have h2 : vecOf ψ ⁅((a * b : ↥(hc.CN t)) : G), x₀⁆ =
        vecOf ψ ⁅(b : G), x₀⁆ + vecOf ψ ⁅(a : G), x₀⁆ := by
      rw [hid, vecOf_mul ψ hcjV (e.comm_mem_V I.h34 a.2 hx₀Q), hcj, vecOf_mul ψ (hZV hz) hb,
        vecOf_of_mem_Z ψ hz hZV, zero_add]
    rw [h2, hcofx a x₀ hx₀Q, hcofx b x₀ hx₀Q, hx₀] at h1
    rw [add_smul]
    exact h1.symm.trans (add_comm _ _)
  let f : ↥(hc.CN t) →* Multiplicative K :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (cof a)) (fun a b => by
      show Multiplicative.ofAdd (cof (a * b)) = _
      rw [hmul a b, ofAdd_add])
  have hker : f.ker = Q.subgroupOf (hc.CN t) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (cof a) = 1 ↔ (a : G) ∈ Q
    rw [ofAdd_eq_one]
    constructor
    · intro h0
      refine hc.hyp.centralizer_Qt a (hNM a.2) fun y hy => ?_
      have := hcofx a y hy
      rw [h0, zero_smul] at this
      exact (vecOf_eq_zero_iff ψ (e.comm_mem_V I.h34 a.2 hy)).mp this
    · intro haQ
      have h1 := hcofx a x₀ hx₀Q
      rw [(vecOf_eq_zero_iff ψ (e.comm_mem_V I.h34 a.2 hx₀Q)).mpr
        (comm_mem_Z_of_Q hc haQ hx₀Q), hx₀] at h1
      exact huν _ _ (by rw [zero_smul]; exact h1.symm)
  have hcard : Nat.card f.range = Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥(hc.CN t) ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = Nat.card Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
    rw [h2, h3, e.hs.cardN] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [mul_comm (Nat.card f.range)] at h1
    exact (Nat.eq_of_mul_eq_mul_left hQpos h1).symm
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [hcard, ← hK]
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)).symm)
  have hmem : Multiplicative.ofAdd lam ∈ f.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨a, ha⟩ := hmem
  have hcl : cof a = lam := by
    have := congrArg Multiplicative.toAdd ha
    simpa [f] using this
  exact ⟨a, a.2, fun x hx => by rw [hcofx a x hx, hcl]⟩

theorem OmegaModel.exists_B_le_Q1 (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hX : AddCommutantScalar X') (hK : Nat.card K = Nat.card Z)
    (hmod : OmegaModel hc t Q' E φ ψ u) {c : G} (hcM : c ∈ M)
    (hcN : ∀ a ∈ hc.CN t, ⁅c, a⁆ ∈ Q) (hc2 : c * c ∈ Q)
    (hcV : ∀ v ∈ Vt M (LB M Q B) B Z t, c * v * c⁻¹ ∈ Vt M (LB M Q B) B Z t) :
    ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ B ≤ Q1 hc c := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR := hc.Rt_normalizes_Vt ht
  let lift : (ι → K) → ↥(Vt M (LB M Q B) B Z t) := fun w =>
    Classical.choose (exists_secVec_eq ψ w)
  have hlift : ∀ w, secVec ψ (lift w) = w := fun w =>
    Classical.choose_spec (exists_secVec_eq ψ w)
  have hvec_lift : ∀ w, vecOf ψ (lift w : G) = w := fun w => by
    rw [vecOf_of_mem ψ (lift w).2]
    exact hlift w
  let σf : (ι → K) → (ι → K) := fun w => vecOf ψ (c * (lift w : G) * c⁻¹)
  have hσ : ∀ g ∈ Vt M (LB M Q B) B Z t, σf (vecOf ψ g) = vecOf ψ (c * g * c⁻¹) := by
    intro g hg
    have h1 : secVec ψ (lift (vecOf ψ g)) = secVec ψ ⟨g, hg⟩ := by
      rw [hlift, vecOf_of_mem ψ hg]
    have h2 := (secVec_eq_iff ψ _ _).mp h1
    show vecOf ψ (c * (lift (vecOf ψ g) : G) * c⁻¹) = _
    rw [vecOf_eq_iff ψ (hcV _ (lift _).2) (hcV g hg)]
    have : c * (lift (vecOf ψ g) : G) * c⁻¹ * (c * g * c⁻¹)⁻¹ =
        c * ((lift (vecOf ψ g) : G) * g⁻¹) * c⁻¹ := by group
    rw [this]
    exact conj_Z_mem hc hcM h2
  have hadd : ∀ w₁ w₂, σf (w₁ + w₂) = σf w₁ + σf w₂ := by
    intro w₁ w₂
    have e1 : w₁ + w₂ = vecOf ψ ((lift w₁ : G) * (lift w₂ : G)) := by
      rw [vecOf_mul ψ (lift w₁).2 (lift w₂).2, hvec_lift, hvec_lift]
    have e2 : σf (w₁ + w₂) = vecOf ψ (c * ((lift w₁ : G) * (lift w₂ : G)) * c⁻¹) := by
      rw [e1]
      exact hσ _ (Subgroup.mul_mem _ (lift w₁).2 (lift w₂).2)
    have e3 : σf w₁ = vecOf ψ (c * (lift w₁ : G) * c⁻¹) := rfl
    have e4 : σf w₂ = vecOf ψ (c * (lift w₂ : G) * c⁻¹) := rfl
    rw [e2, e3, e4, ← vecOf_mul ψ (hcV _ (lift w₁).2) (hcV _ (lift w₂).2)]
    congr 1
    group
  have hKI : ∀ a ∈ hc.CN t, ∀ x ∈ Q,
      vecOf ψ (c * ⁅a, x⁆ * c⁻¹) = vecOf ψ ⁅a, c * x * c⁻¹⁆ := by
    intro a ha x hx
    have hxc : c * x * c⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hcM).1 x hx
    have h1 : c * ⁅a, x⁆ * c⁻¹ ∈ Vt M (LB M Q B) B Z t := hcV _ (e.comm_mem_V I.h34 ha hx)
    have h2 : ⁅a, c * x * c⁻¹⁆ ∈ Vt M (LB M Q B) B Z t := e.comm_mem_V I.h34 ha hxc
    rw [vecOf_eq_iff ψ h1 h2]
    have hq : ⁅c, a⁆ ∈ Q := hcN a ha
    have haM : a ∈ M := e.CN_le_M ha
    have hu : a * (c * x * c⁻¹) * a⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M haM).1 _ hxc
    have : c * ⁅a, x⁆ * c⁻¹ * ⁅a, c * x * c⁻¹⁆⁻¹ = ⁅⁅c, a⁆, a * (c * x * c⁻¹) * a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact comm_mem_Z_of_Q hc hq hu
  have hsmul : ∀ (lam : K) (w : ι → K), σf (lam • w) = lam • σf w := by
    intro lam w
    obtain ⟨x, hxQ, hx⟩ := OmegaModel.exists_chiVec (ψ := ψ) I e w
    obtain ⟨a, ha, hac⟩ := hmod.exists_elt_scalar I e hX hK lam
    obtain ⟨a₁, ha₁, hac₁⟩ := hmod.exists_elt_scalar I e hX hK 1
    have hxc : c * x * c⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hcM).1 x hxQ
    have hw1 : w = vecOf ψ ⁅a₁, x⁆ := by rw [hac₁ x hxQ, one_smul, hx]
    have hw2 : lam • w = vecOf ψ ⁅a, x⁆ := by rw [hac x hxQ, hx]
    have h1 : σf (lam • w) = lam • vecOf ψ ⁅c * x * c⁻¹, t⁆ := by
      rw [hw2, hσ _ (e.comm_mem_V I.h34 ha hxQ), hKI a ha x hxQ, hac _ hxc]
    have h2 : σf w = vecOf ψ ⁅c * x * c⁻¹, t⁆ := by
      rw [hw1, hσ _ (e.comm_mem_V I.h34 ha₁ hxQ), hKI a₁ ha₁ x hxQ, hac₁ _ hxc, one_smul]
    rw [h1, h2]
  have hsq : ∀ w, σf (σf w) = w := by
    intro w
    have hgV := (lift w).2
    have h1 : σf w = vecOf ψ (c * (lift w : G) * c⁻¹) := rfl
    rw [h1, hσ _ (hcV _ hgV)]
    have hmem : c * (c * (lift w : G) * c⁻¹) * c⁻¹ ∈ Vt M (LB M Q B) B Z t := hcV _ (hcV _ hgV)
    have hZmem : c * (c * (lift w : G) * c⁻¹) * c⁻¹ * (lift w : G)⁻¹ ∈ Z := by
      have : c * (c * (lift w : G) * c⁻¹) * c⁻¹ * (lift w : G)⁻¹ = ⁅c * c, (lift w : G)⁆ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact comm_mem_Z_of_Q hc hc2 (hVQ hgV)
    rw [(vecOf_eq_iff ψ hmem hgV).mpr hZmem, hvec_lift]
  let σ : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := σf
      map_add' := hadd
      map_smul' := fun lam w => hsmul lam w }
  have hs1 : ∀ y, (σ - 1) y = σf y - y := fun y => by simp [σ]
  let F : Submodule K (ι → K) := LinearMap.ker (σ - 1)
  have hF : ∀ w, w ∈ F ↔ σf w = w := fun w => by
    rw [LinearMap.mem_ker, hs1, sub_eq_zero]
  have h2 : ∀ y : ι → K, y + y = 0 := fun y => funext fun i => CharTwo.add_self_eq_zero (y i)
  have hnil : ∀ w, (σ - 1) ((σ - 1) w) = 0 := by
    intro w
    have hσσ : σ (σ w) = w := hsq w
    rw [hs1, hs1]
    show σ (σ w - w) - (σ w - w) = 0
    rw [map_sub, hσσ]
    calc w - σ w - (σ w - w) = (w + w) - (σ w + σ w) := by abel
      _ = 0 := by rw [h2, h2, sub_zero]
  have hrk : Module.finrank K ↥(LinearMap.range (σ - 1)) + Module.finrank K ↥F =
      Module.finrank K (ι → K) := LinearMap.finrank_range_add_finrank_ker (σ - 1)
  have hle : LinearMap.range (σ - 1) ≤ F :=
    LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun w => hnil w)
  have hfr : Module.finrank K ↥(LinearMap.range (σ - 1)) ≤ Module.finrank K ↥F :=
    Submodule.finrank_mono hle
  have hdim : m ≤ Module.finrank K ↥F := by
    have := hg.dim
    omega
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hsing : ∃ w ∈ F, Q' w = 0 ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcardF : Nat.card ↥F = Nat.card K ^ Module.finrank K ↥F :=
      Module.natCard_eq_pow_finrank
    let β : ↥F →+ ↥F →+ K := AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => polarBilin Q' (x : ι → K) (y : ι → K)) (fun y z => by simp))
      (fun x y => by ext z; simp)
    have h := card_le_sq_of_anisotropic (A := ↥F) (K := K) (fun x => Subtype.ext (h2 x.1))
      (fun x => Q' (x : ι → K)) β
      (fun x y => by simpa [β, QuadraticMap.polarBilin_apply_apply] using
        QuadraticMap.map_add Q' (x : ι → K) (y : ι → K))
      (fun x hx => Subtype.ext (hcon x.1 x.2 hx))
    have hm3 := hg.three_le
    have : Nat.card K ^ 2 < Nat.card K ^ Module.finrank K ↥F :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  obtain ⟨w, hwF, hwQ, hw0⟩ := hsing
  obtain ⟨P, P', hP⟩ := hg.two
  obtain ⟨A, hAX, hAu⟩ := E.exists_mulVec_eq hg.nondeg hP hmod.u0 hw0 (by rw [hmod.Qu, hwQ])
  obtain ⟨ρ, hρ⟩ := exists_mulVec_eq_of_range φ hmod.range ⟨A, hAX, hAu⟩
  refine ⟨(ρ : G), ρ.2, fun b hb => ?_⟩
  rw [mem_conjSubgroup] at hb
  have hb₀V : (ρ : G)⁻¹ * b * (ρ : G) ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
  have hbeq : b = (ρ : G) * ((ρ : G)⁻¹ * b * (ρ : G)) * (ρ : G)⁻¹ := by group
  have hb'V : b ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp (hVR ρ.2) _).mp hb₀V
    rwa [← hbeq] at this
  obtain ⟨c₀, hc₀⟩ := (hmod.hB (secVec ψ ⟨(ρ : G)⁻¹ * b * (ρ : G), hb₀V⟩)).mp
    ⟨⟨(ρ : G)⁻¹ * b * (ρ : G), hb₀V⟩, hb, rfl⟩
  have hvec : secVec ψ ⟨b, hb'V⟩ = c₀ • w := by
    have h1 := hmod.equi ρ ⟨(ρ : G)⁻¹ * b * (ρ : G), hb₀V⟩ ⟨b, hb'V⟩ (by
      show b = (ρ : G) * ((ρ : G)⁻¹ * b * (ρ : G)) * (ρ : G)⁻¹
      exact hbeq)
    change secVec ψ ⟨b, hb'V⟩ =
      (φ ρ : Matrix ι ι K) *ᵥ secVec ψ ⟨(ρ : G)⁻¹ * b * (ρ : G), hb₀V⟩ at h1
    rw [h1, hc₀, Matrix.mulVec_smul, hρ]
  rw [hc.mem_Q1_iff hcM]
  refine ⟨hVQ hb'V, ?_⟩
  have hbF : σf (vecOf ψ b) = vecOf ψ b := by
    rw [← hF, vecOf_of_mem ψ hb'V, hvec]
    exact F.smul_mem c₀ hwF
  rw [hσ b hb'V] at hbF
  have hcb : vecOf ψ (c * b * c⁻¹) = vecOf ψ b := hbF
  have := (vecOf_eq_iff ψ (hcV b hb'V) hb'V).mp hcb
  have e1 : ⁅c, b⁆ = c * b * c⁻¹ * b⁻¹ := by simp only [commutatorElement_def]
  rwa [e1]

end Scalar

section Weak

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.conj_CN_eq_of_comm (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) {g : G} (hg : g ∈ M)
    (hcomm : ∀ x ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅x, g * b * g⁻¹⁆ ∈ Q) :
    conjSubgroup g (hc.CN t) = hc.CN t := by
  have ht := e.hs.toSec5.mem
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  obtain ⟨a, ha, haQ⟩ : ∃ a ∈ hc.CN t, a ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card ↥(hc.CN t) ≤ Nat.card ↥Q := Subgroup.card_le_of_le hcon
    rw [e.hs.cardN] at h1
    have h4 := hc.hyp.q4
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    nlinarith
  have haM : a ∈ M := e.CN_le_M ha
  set c : G := g * a * g⁻¹ with hcdef
  have hcM : c ∈ M := M.mul_mem (M.mul_mem hg haM) (M.inv_mem hg)
  have hcN : ∀ x ∈ hc.CN t, ⁅c, x⁆ ∈ Q := by
    intro x hx
    have := Q.inv_mem (hcomm x hx a ha)
    rwa [commutatorElement_inv] at this
  have hc2 : c * c ∈ Q := by
    have h1 : a * a ∈ Q := by
      have := (e.N_mod_Q I.h34).2 a ha
      rwa [pow_two] at this
    have := (hc.conj_mem_Q_of_mem_M hg).1 _ h1
    rwa [show g * (a * a) * g⁻¹ = c * c by simp only [hcdef]; group] at this
  have hcaQ : a⁻¹ * (c * a * c⁻¹) ∈ Q := by
    have h1 : ⁅c, a⁆ ∈ Q := hcN a ha
    have := (hc.conj_mem_Q_of_mem_M haM).2 _ h1
    rwa [show a⁻¹ * ⁅c, a⁆ * a = a⁻¹ * (c * a * c⁻¹) by
      simp only [commutatorElement_def]; group] at this
  have hV1 : Q1 hc (c * a * c⁻¹) = Vt M (LB M Q B) B Z t := by
    rw [Q1_congr hc haM (M.mul_mem (M.mul_mem hcM haM) (M.inv_mem hcM)) hcaQ]
    exact e.Q1_eq_V I ha haQ
  have hV2 : Q1 hc (c * a * c⁻¹) = conjSubgroup c (Q1 hc a) := Q1_conj hc hcM haM
  rw [e.Q1_eq_V I ha haQ] at hV2
  have hcV : ∀ v ∈ Vt M (LB M Q B) B Z t, c * v * c⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    intro v hv
    have : c * v * c⁻¹ ∈ conjSubgroup c (Vt M (LB M Q B) B Z t) :=
      mem_conjSubgroup.mpr (by rw [show c⁻¹ * (c * v * c⁻¹) * c = v by group]; exact hv)
    rwa [← hV2, hV1] at this
  obtain ⟨ι, _, _, K, _, _, _, Q', X', E, φ, _, ψ, u, hK, hX, hgeom, hmod⟩ :=
    e.exists_model_scalar I
  obtain ⟨ρ, hρ, hB⟩ := hmod.exists_B_le_Q1 I e hgeom hX hK hcM hcN hc2 hcV
  refine e.conj_CN_eq_of_B_le I h63b hg hρ ?_
  have hQ1c : Q1 hc c = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [hcdef, Q1_conj hc hg haM, e.Q1_eq_V I ha haQ]
  rw [← hQ1c]
  exact hB

end Weak

section Assembly

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G} [(Q.subgroupOf M).Normal]

theorem comm_mem_Q_of_piM_comm {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (h : piM M Q x * piM M Q y = piM M Q y * piM M Q x) : ⁅x, y⁆ ∈ Q := by
  have hcM : ⁅x, y⁆ ∈ M := by
    simp only [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)
  rw [← piM_eq_one_iff hcM]
  have h2 : piM M Q ⁅x, y⁆ = ⁅piM M Q x, piM M Q y⁆ := by
    simp only [commutatorElement_def]
    rw [piM_mul (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy),
      piM_mul (M.mul_mem hx hy) (M.inv_mem hx), piM_mul hx hy, piM_inv hx, piM_inv hy]
  rw [h2]
  exact commutatorElement_eq_one_iff_mul_comm.mpr h

theorem Env.corBHyp (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) : CorBHyp (bar M Q (hc.CN t)) := by
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hN2 := e.N_mod_Q I.h34
  have hcomm_bar : ∀ x ∈ bar M Q (hc.CN t), ∀ y ∈ bar M Q (hc.CN t), x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    obtain ⟨b, hb, hbM, rfl⟩ := (mem_bar y).mp hy
    exact piM_comm_of_comm_mem haM hbM (hN2.1 a ha b hb)
  unfold CorBHyp
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm_bar a.1 a.2 b.1 b.2)⟩⟩, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    rw [pow_two, ← piM_mul haM haM]
    have := hN2.2 a ha
    rw [pow_two] at this
    exact (piM_eq_one_iff (M.mul_mem haM haM)).mpr this
  · intro gb
    obtain ⟨g, hg, rfl⟩ := exists_piM gb
    rw [conj_bar hQM hg]
    by_cases hbot : bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)) = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ : ∃ y ∈ bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)),
          y ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hbot (eq_bot_iff.mpr fun y hy => (Subgroup.mem_bot).mpr (hcon y hy))
      obtain ⟨x, hx, hxM, hxy⟩ := (mem_bar y).mp hy1
      obtain ⟨z, hz, hzM, hzy⟩ := (mem_bar y).mp hy2
      have hxQ : x ∉ Q := fun hxQ => hy (by rw [← hxy]; exact (piM_eq_one_iff hxM).mpr hxQ)
      have haN : g⁻¹ * z * g ∈ hc.CN t := mem_conjSubgroup.mp hz
      have hzeq : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      have haQ : g⁻¹ * z * g ∉ Q := by
        intro haQ
        apply hy
        have h1 : z ∈ Q := by
          have := (hc.conj_mem_Q_of_mem_M hg).1 _ haQ
          rwa [hzeq] at this
        rw [← hzy]
        exact (piM_eq_one_iff hzM).mpr h1
      have hxa : x⁻¹ * (g * (g⁻¹ * z * g) * g⁻¹) ∈ Q := by
        rw [hzeq]
        exact (piM_eq_iff hxM hzM).mp (hxy.trans hzy.symm)
      have hNg := e.conj_CN_eq_of_fuse I h63b hg hx hxQ haN haQ hxa
      rw [hNg]
      exact inf_idem _
  · intro gb
    obtain ⟨g, hg, rfl⟩ := exists_piM gb
    rw [conj_bar hQM hg]
    constructor
    · intro hH
      have hcomm : ∀ x ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅x, g * b * g⁻¹⁆ ∈ Q := by
        intro x hx b hb
        have hxM := e.CN_le_M hx
        have hbM := e.CN_le_M hb
        have hgbM : g * b * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hbM) (M.inv_mem hg)
        have h1 : piM M Q x ∈ bar M Q (hc.CN t) := piM_mem_bar hx hxM
        have h2 : piM M Q (g * b * g⁻¹) ∈ bar M Q (conjSubgroup g (hc.CN t)) :=
          piM_mem_bar (mem_conjSubgroup.mpr (by
            rw [show g⁻¹ * (g * b * g⁻¹) * g = b by group]; exact hb)) hgbM
        exact comm_mem_Q_of_piM_comm hxM hgbM (hH _ h1 _ h2)
      rw [e.conj_CN_eq_of_comm I h63b hg hcomm]
    · intro hT x hx y hy
      rw [hT] at hy
      exact hcomm_bar x hx y hy

end Assembly

section Statement

@[expose] def Stroth64CorBHypStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
    ∀ [(Q.subgroupOf M).Normal], CorBHyp (bar M Q (hc.CN t))

theorem stroth64CorBHyp_of_inputs (I : Inputs) (hS : Stroth65XSplitStatement)
    (h63a : Stroth63aStatement) (h63b : Stroth63bStatement) : Stroth64CorBHypStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hΩ _
  have hn := h63a G M Q Z B hc n t hs m hm hΩ
  obtain ⟨X, hQX, hXR, hNX, hNXQ, hcen, -⟩ := hS G M Q Z B hc n t hs m hm hn hΩ
  have e : Env hc n t m X := ⟨hs, hm, hn, hΩ, hQX, hXR, hNX, hNXQ, hcen⟩
  exact e.corBHyp I (h63b G M Q Z B hc n t hs m hm hΩ)

end Statement

end HS6

section Certs

theorem stroth64CorBHyp_holds : HS6.Stroth64CorBHypStatement :=
  HS6.stroth64CorBHyp_of_inputs ⟨stroth34Statement_unconditional,
    stroth310Root_of_34 stroth34Statement_unconditional, stroth51Statement_unconditional,
    strothNtStatement_unconditional⟩ stroth65XSplit_holds
    (stroth_6_3a stroth34Statement_unconditional stroth6LBStatement_holds) stroth63b_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80

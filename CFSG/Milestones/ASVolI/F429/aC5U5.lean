module

public import CFSG.Milestones.ASVolI.F429.aR5Gen
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Milestones.ASVolI.F429.aC7U5
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Generic

theorem burnsideF429a_inner_of_borelAutDiag_family {Y : Type} [Group Y] {U H : Subgroup Y}
    {F E : Subgroup (MulAut Y)} (D : BorelAutDiag U H F E) {H₀ : Set Y} (hH₀ : H₀ ⊆ H)
    (hdet : ∀ σ ∈ F, (∀ x ∈ H₀, σ x = x) → σ = 1) (β : MulAut Y)
    (h1 : ∀ x, β x ∈ U ↔ x ∈ U) (h2 : ∀ x ∈ H₀, β x * x⁻¹ ∈ U) {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    β ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨e, he, σ, hσ, rfl⟩ := D.normal_form β h1
  have hfix : ∀ x ∈ H₀, σ x = x := by
    intro x hx0
    have hx := hH₀ hx0
    have hσx : σ x ∈ H := D.F_H σ hσ x hx
    have hσxB : σ x ∈ Subgroup.normalizer (U : Set Y) := D.H_le hσx
    have he1 : (σ x)⁻¹ * e (σ x) ∈ U := D.E_triv e he (σ x) hσxB
    have hc : e (σ x) * x⁻¹ ∈ U := by simpa [MulAut.mul_apply] using h2 x hx0
    have hu1 : σ x * ((σ x)⁻¹ * e (σ x))⁻¹ * (σ x)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 hσxB _).1 (U.inv_mem he1)
    have hmem : σ x * x⁻¹ ∈ U := by
      have e2 : σ x * x⁻¹ =
          (σ x * ((σ x)⁻¹ * e (σ x))⁻¹ * (σ x)⁻¹) * (e (σ x) * x⁻¹) := by group
      rw [e2]
      exact U.mul_mem hu1 hc
    exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hσx (H.inv_mem hx)))
  have hσ1 : σ = 1 := hdet σ hσ hfix
  subst hσ1
  rw [mul_one] at hk ⊢
  obtain ⟨u, -, hu⟩ := D.E_two e he k hk
  exact ⟨u, hu.symm⟩

theorem burnsideF429a_key_of_model_family {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {B U P : Subgroup C} {M : Subgroup E} (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom)
    (hU : pCoreOf 2 B = U) (hM : M.subgroupOf Gp = P.map Ψ.toMonoidHom) {H₀ : Set C}
    (hH₀ : ∀ x ∈ H₀, x ∈ oPPrime 2 P ∧ x ∈ B)
    (hinner : ∀ (β : MulAut C) (k : ℕ), β ^ 2 ^ k = 1 → (∀ x, β x ∈ U ↔ x ∈ U) →
      (∀ x ∈ H₀, β x * x⁻¹ ∈ U) → β ∈ (MulAut.conj : C →* MulAut C).range) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hk hcomm
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ := burnsideF429_inf_eq_map Ψ hB
  have hGM : Gp ⊓ M = P.map φ := burnsideF429_inf_eq_map Ψ hM
  have hL : oPPrime 2 (Gp ⊓ M) = (oPPrime 2 P).map φ := by
    rw [hGM, burnsideF4gU4Inv_oPPrime_map hφ]
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  have hrX : r ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG r,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hr hxM) ((M₁ ⊓ M₂).inv_mem hr)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG r⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hr) hxM) hr
        simpa [mul_assoc] using this
  have hrN : r ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrX
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hβpow : β ^ 2 ^ k = 1 := by
    have key : ∀ n : ℕ, β ^ n = (Ψ.trans ((burnsideF4d_rho Gp r) ^ n)).trans Ψ.symm := by
      intro n
      induction n with
      | zero =>
        ext x
        simp
      | succ n ih =>
        ext x
        rw [pow_succ, ih, pow_succ]
        simp [MulAut.mul_apply, β]
    have hρ : (burnsideF4d_rho Gp r) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    rw [key, hρ]
    ext x
    simp
  have hmemU : ∀ x : C, x ∈ U ↔ φ x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  have h1 : ∀ x, β x ∈ U ↔ x ∈ U := by
    intro x
    rw [hmemU, hmemU, hβφ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (φ x)).symm
  have h2 : ∀ x ∈ H₀, β x * x⁻¹ ∈ U := by
    intro x hx
    rw [hmemU, map_mul, map_inv, hβφ]
    have hb : φ x ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂) := by
      refine ⟨?_, ?_⟩
      · rw [hL]
        exact ⟨x, (hH₀ x hx).1, rfl⟩
      · have : φ x ∈ Gp ⊓ (M₁ ⊓ M₂) := by
          rw [hGB]
          exact ⟨x, (hH₀ x hx).2, rfl⟩
        exact this.2
    exact hcomm (φ x) hb
  obtain ⟨g, hg⟩ := hinner β k hβpow h1 h2
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβφ x
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    rw [← hφx, ← hφx, ← e1]
  have hr' := burnsideF4d_rho_injective hc hρ
  rw [hr']
  exact (Ψ g).2

end Generic

section U5Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem burnsideF429a_U5_rkOneW_mul_self : rkOneW h * rkOneW h = 1 := by
  apply Subtype.ext
  apply Units.ext
  show rkOneWMat * rkOneWMat = (1 : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨x, y, w, rfl⟩ : ∃ x y w : K, v = rkVec x y w := ⟨_, _, _, rkVec_eta v⟩
  rw [← Matrix.mulVec_mulVec, rkOneWMat_mulVec, rkOneWMat_mulVec, Matrix.one_mulVec, neg_neg]

theorem burnsideF429a_U5_rkOneQElt_pow {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneQElt h a b hab ^ 2 ^ 2 = 1 := by
  haveI := h.charP
  have e : rkOneQElt h a b hab ^ 2 ^ 2 = rkOneQElt h a b hab * rkOneQElt h a b hab *
      (rkOneQElt h a b hab * rkOneQElt h a b hab) := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq]
  rw [e]
  apply Subtype.ext
  apply Units.ext
  show rkOneQ h a b * rkOneQ h a b * (rkOneQ h a b * rkOneQ h a b) = 1
  simp only [rkOneQ_mul, CharTwo.add_self_eq_zero, map_zero, mul_zero, zero_mul, sub_self,
    sub_zero, zero_sub, add_zero]
  rw [rkOneQ, CFSG.LinearGroups.heisenbergMatrix_zero_zero, Matrix.submatrix_one_equiv]

theorem burnsideF429a_U5_bruhat {a γ : K} (hγ : γ ≠ 0) (hab : h.norm a + h.trace γ = 0) :
    rkOneQ h (a / γ) γ⁻¹ * rkOneD h (h.bar γ)⁻¹ * rkOneWMat * rkOneQ h (a / h.bar γ) γ⁻¹ =
      rkOneWMat * rkOneQ h a γ * rkOneWMat := by
  haveI := h.charP
  have hbγ : h.bar γ ≠ 0 := (map_ne_zero h.bar).mpr hγ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hab' : a * h.bar a + (γ + h.bar γ) = 0 := hab
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨x, y, w, rfl⟩ : ∃ x y w : K, v = rkVec x y w := ⟨_, _, _, rkVec_eta v⟩
  simp only [← Matrix.mulVec_mulVec, rkOneQ_mulVec, rkOneD_mulVec, rkOneWMat_mulVec, map_div₀,
    map_inv₀, h.bar_bar, inv_inv]
  congr 1
  · field_simp
    linear_combination w * hab'
  · field_simp
    linear_combination (a * x * γ) * h2 - y * hab'
  · field_simp
    linear_combination (-(h.bar a * y)) * h2

theorem burnsideF429a_U5_two_mem_oPPrime {g : hypSU h 1 1} {k : ℕ} (hg : g ^ 2 ^ k = 1) :
    g ∈ (oPPrime 2 (u5PtP h)).comap ((hypProj h 2 1).comp (embSU h)) := by
  have hN : embSU h g ∈ N₂sub h := by
    rw [← range_embSU]
    exact ⟨g, rfl⟩
  have hP : hypProj h 2 1 (embSU h g) ∈ u5PtP h := by
    rw [u5PtP, projIsoStabilizer]
    exact ⟨embSU h g, N₂sub_le_u5PtStab hN, rfl⟩
  exact Subgroup.mem_comap.mpr (burnsideF4gU4Inv_mem_oPPrime hP (k := k)
    (by rw [← map_pow, hg, map_one]))

theorem burnsideF429a_U5_rkOneD_mem_of {γ : K} (hγ : γ ≠ 0) (hD : (h.bar γ)⁻¹ ≠ 0) :
    rkOneDHomSU h (Units.mk0 (h.bar γ)⁻¹ hD) ∈
      (oPPrime 2 (u5PtP h)).comap ((hypProj h 2 1).comp (embSU h)) := by
  haveI := h.charP
  obtain ⟨a, ha⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_eq h
    (c := -h.trace γ) (by rw [map_neg, UnitaryFieldData.trace, map_add, h.bar_bar, add_comm])
  have hab : h.norm a + h.trace γ = 0 := by rw [ha, neg_add_cancel]
  have hbγ : h.bar γ ≠ 0 := (map_ne_zero h.bar).mpr hγ
  have hab' : a * h.bar a + (γ + h.bar γ) = 0 := hab
  have hab₁ : h.norm (a / γ) + h.trace γ⁻¹ = 0 := by
    show a / γ * h.bar (a / γ) + (γ⁻¹ + h.bar γ⁻¹) = 0
    rw [map_div₀, map_inv₀]
    field_simp
    linear_combination hab'
  have hab₂ : h.norm (a / h.bar γ) + h.trace γ⁻¹ = 0 := by
    show a / h.bar γ * h.bar (a / h.bar γ) + (γ⁻¹ + h.bar γ⁻¹) = 0
    rw [map_div₀, map_inv₀, h.bar_bar]
    field_simp
    linear_combination hab'
  set O := (oPPrime 2 (u5PtP h)).comap ((hypProj h 2 1).comp (embSU h)) with hO
  have hQ : rkOneQElt h a γ hab ∈ O :=
    burnsideF429a_U5_two_mem_oPPrime h (burnsideF429a_U5_rkOneQElt_pow h hab)
  have hQ₁ : rkOneQElt h (a / γ) γ⁻¹ hab₁ ∈ O :=
    burnsideF429a_U5_two_mem_oPPrime h (burnsideF429a_U5_rkOneQElt_pow h hab₁)
  have hQ₂ : rkOneQElt h (a / h.bar γ) γ⁻¹ hab₂ ∈ O :=
    burnsideF429a_U5_two_mem_oPPrime h (burnsideF429a_U5_rkOneQElt_pow h hab₂)
  have hW : rkOneW h ∈ O :=
    burnsideF429a_U5_two_mem_oPPrime h (k := 1) (by rw [pow_one, sq, burnsideF429a_U5_rkOneW_mul_self])
  have hrel : rkOneQElt h (a / γ) γ⁻¹ hab₁ * rkOneDHomSU h (Units.mk0 (h.bar γ)⁻¹ hD) * rkOneW h *
      rkOneQElt h (a / h.bar γ) γ⁻¹ hab₂ = rkOneW h * rkOneQElt h a γ hab * rkOneW h := by
    apply Subtype.ext
    apply Units.ext
    exact burnsideF429a_U5_bruhat h hγ hab
  have e : rkOneDHomSU h (Units.mk0 (h.bar γ)⁻¹ hD) = (rkOneQElt h (a / γ) γ⁻¹ hab₁)⁻¹ *
      (rkOneW h * rkOneQElt h a γ hab * rkOneW h) * (rkOneQElt h (a / h.bar γ) γ⁻¹ hab₂)⁻¹ *
      (rkOneW h)⁻¹ := by
    rw [← hrel]
    group
  rw [e]
  exact O.mul_mem (O.mul_mem (O.mul_mem (O.inv_mem hQ₁) (O.mul_mem (O.mul_mem hW hQ) hW))
    (O.inv_mem hQ₂)) (O.inv_mem hW)

theorem burnsideF429a_U5_rkOneD_mem (c : Kˣ) :
    rkOneDHomSU h c ∈ (oPPrime 2 (u5PtP h)).comap ((hypProj h 2 1).comp (embSU h)) := by
  have hγ : (h.bar (c : K))⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero h.bar).mpr c.ne_zero)
  have hD : (h.bar (h.bar (c : K))⁻¹)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero h.bar).mpr hγ)
  have hc : Units.mk0 (h.bar (h.bar (c : K))⁻¹)⁻¹ hD = c := by
    ext
    rw [Units.val_mk0, map_inv₀, h.bar_bar, inv_inv]
  rw [← hc]
  exact burnsideF429a_U5_rkOneD_mem_of h hγ hD

theorem burnsideF429a_U5_mat_embSU_rkOneD (c : Kˣ) :
    (((embSU h (rkOneDHomSU h c) : hypSU h 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      diagonal (fun a => embN₂ (rkOneD h (c : K)) a a) := by
  show embN₂ (rkOneD h (c : K)) = _
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [embN₂, pN₂, rkOneD, rkOneDiag, diagonal_apply]

theorem burnsideF429a_U5_eq_one_of_fieldP_fix (σ : K ≃+* K) {i j : HypIndex 2 1}
    (t : Kˣ → hypSU h 2 1) (hi : ∀ c : Kˣ, mat (t c) i i = c) (hj : ∀ c : Kˣ, mat (t c) j j = 1)
    (hfix : ∀ c : Kˣ, fieldP h σ (hypProj h 2 1 (t c)) = hypProj h 2 1 (t c)) : σ = 1 := by
  have key : ∀ g : hypSU h 2 1, fieldP h σ (hypProj h 2 1 g) = hypProj h 2 1 g →
      mat g j j = 1 → σ (mat g i i) = mat g i i := by
    intro g h1 hj1
    rw [fieldP_apply] at h1
    have hz : (CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h σ g)⁻¹ * g ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨μ, -, -, hμ⟩ := hz
    have h2 : (g : GL (HypIndex 2 1) K) =
        (CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h σ g : GL (HypIndex 2 1) K) *
          GeneralLinearGroup.scalar (HypIndex 2 1) μ := by
      have : (g : GL (HypIndex 2 1) K) =
          (CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h σ g : GL (HypIndex 2 1) K) *
            (((CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h σ g)⁻¹ * g : hypSU h 2 1) :
              GL (HypIndex 2 1) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this, hμ]
    have hmat : ∀ a b, mat g a b = σ (mat g a b) * μ := by
      intro a b
      have := congrArg (fun M : GL (HypIndex 2 1) K =>
        (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b) h2
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mul_diagonal] at this
      exact this
    have e1 := hmat j j
    have e0 := hmat i i
    rw [hj1, map_one, one_mul] at e1
    rw [← e1, mul_one] at e0
    exact e0.symm
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · have := key (t (Units.mk0 x hx)) (hfix _) (hj _)
    rw [hi] at this
    show σ x = x
    simpa using this

theorem burnsideF429a_U5_pt_family :
    (∀ x ∈ Set.range (fun c : Kˣ => hypProj h 2 1 (embSU h (rkOneDHomSU h c))),
      x ∈ oPPrime 2 (u5PtP h) ∧ x ∈ u5PtP h ⊓ u5LnP h) ∧
    Set.range (fun c : Kˣ => hypProj h 2 1 (embSU h (rkOneDHomSU h c))) ⊆
      ((hypTorus h 2 1).map (hypProj h 2 1) : Set (hypPSU h 2 1)) ∧
    ∀ σ ∈ MonoidHom.range (fieldP h),
      (∀ x ∈ Set.range (fun c : Kˣ => hypProj h 2 1 (embSU h (rkOneDHomSU h c))), σ x = x) →
        σ = 1 := by
  have hT : ∀ c : Kˣ, embSU h (rkOneDHomSU h c) ∈ hypTorus h 2 1 := fun c =>
    CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h (burnsideF429a_U5_mat_embSU_rkOneD h c)
  have hTB : (hypTorus h 2 1).map (hypProj h 2 1) ≤ u5PtP h ⊓ u5LnP h := by
    rw [u5PtP_inf_u5LnP]
    exact Subgroup.map_mono (hypTorus_le_hypBorel _)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨Subgroup.mem_comap.mp (burnsideF429a_U5_rkOneD_mem h c), hTB ⟨_, hT c, rfl⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, hT c, rfl⟩
  · rintro _ ⟨τ, rfl⟩ hfix
    have hi : ∀ c : Kˣ, mat (embSU h (rkOneDHomSU h c)) ιe₂ ιe₂ = c := by
      intro c
      show embN₂ (rkOneD h (c : K)) ιe₂ ιe₂ = c
      rw [(embN₂_entries (rkOneD h (c : K))).2.1.2.1]
      simp [rkOneD, rkOneDiag]
    have hj : ∀ c : Kˣ, mat (embSU h (rkOneDHomSU h c)) ιe₁ ιe₁ = 1 := fun c =>
      (embN₂_entries (rkOneD h (c : K))).1.1
    have hτ : τ = 1 := burnsideF429a_U5_eq_one_of_fieldP_fix h τ
      (fun c => embSU h (rkOneDHomSU h c)) hi hj (fun c => hfix _ ⟨c, rfl⟩)
    rw [hτ, map_one]

theorem burnsideF429a_U5_leviSU_diagSL_mem (c : Kˣ) :
    hypProj h 2 1 (leviSU h 1 (diagSL c)) ∈ oPPrime 2 (u5LnP h) := by
  haveI := h.charP
  have hdet : ∀ c : Kˣ, (!![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    intro c
    rw [Matrix.det_fin_two_of, zero_mul, zero_sub, Units.mul_inv, CharTwo.neg_eq]
  let w : Kˣ → Matrix.SpecialLinearGroup (Fin 2) K := fun c => ⟨_, hdet c⟩
  have hw2 : ∀ c, w c * w c = 1 := by
    intro c
    apply Subtype.ext
    show (!![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K) *
      !![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hwd : diagSL c = w c * w 1 := by
    apply Subtype.ext
    show !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] =
      (!![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K) *
        !![0, ((1 : Kˣ) : K); (((1 : Kˣ)⁻¹ : Kˣ) : K), 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem : ∀ c, hypProj h 2 1 (leviSU h 1 (w c)) ∈ oPPrime 2 (u5LnP h) := by
    intro c
    refine burnsideF4gU4Inv_mem_oPPrime (k := 1) ?_ ?_
    · rw [u5LnP, projIsoStabilizer]
      exact ⟨_, leviSU_mem_u5LnStab (h := h) (w c), rfl⟩
    · rw [pow_one, sq, ← map_mul, ← map_mul, hw2, map_one, map_one]
  rw [hwd, map_mul, map_mul]
  exact Subgroup.mul_mem _ (hmem c) (hmem 1)

theorem burnsideF429a_U5_ln_family :
    (∀ x ∈ Set.range (fun c : Kˣ => hypProj h 2 1 (leviSU h 1 (diagSL c))),
      x ∈ oPPrime 2 (u5LnP h) ∧ x ∈ u5PtP h ⊓ u5LnP h) ∧
    Set.range (fun c : Kˣ => hypProj h 2 1 (leviSU h 1 (diagSL c))) ⊆
      ((hypTorus h 2 1).map (hypProj h 2 1) : Set (hypPSU h 2 1)) ∧
    ∀ σ ∈ MonoidHom.range (fieldP h),
      (∀ x ∈ Set.range (fun c : Kˣ => hypProj h 2 1 (leviSU h 1 (diagSL c))), σ x = x) →
        σ = 1 := by
  have hT : ∀ c : Kˣ, leviSU h 1 (diagSL c) ∈ hypTorus h 2 1 := fun c =>
    (leviSU_diagSL (h := h) c).1.1
  have hTB : (hypTorus h 2 1).map (hypProj h 2 1) ≤ u5PtP h ⊓ u5LnP h := by
    rw [u5PtP_inf_u5LnP]
    exact Subgroup.map_mono (hypTorus_le_hypBorel _)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨burnsideF429a_U5_leviSU_diagSL_mem h c, hTB ⟨_, hT c, rfl⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, hT c, rfl⟩
  · rintro _ ⟨τ, rfl⟩ hfix
    have hi : ∀ c : Kˣ, mat (leviSU h 1 (diagSL c)) ιe₁ ιe₁ = c := fun c =>
      (leviSU_diagSL (h := h) c).2.1
    have hj : ∀ c : Kˣ, mat (leviSU h 1 (diagSL c)) ιz ιz = 1 := by
      intro c
      rw [mat_leviSU]
      simp [ιz]
    have hτ : τ = 1 := burnsideF429a_U5_eq_one_of_fieldP_fix h τ
      (fun c => leviSU h 1 (diagSL c)) hi hj (fun c => hfix _ ⟨c, rfl⟩)
    rw [hτ, map_one]

end U5Model

section Key

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_U5_setup5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (hK : UnitaryFieldData 2 f K) (Ψ : hypPSU hK 2 1 ≃* ↥Gp),
      (M₁ ⊓ M₂).subgroupOf Gp = (u5PtP hK ⊓ u5LnP hK).map Ψ.toMonoidHom ∧
      M₁.subgroupOf Gp = (u5PtP hK).map Ψ.toMonoidHom ∧
      M₂.subgroupOf Gp = (u5LnP hK).map Ψ.toMonoidHom := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨Ψ, e1, e2⟩ := burnsideF429a_U5_equiv marking
  refine ⟨marking.field, inferInstance, burnsideF429a_U5_fieldData marking, Ψ, ?_, h1.trans e1,
    h2.trans e2⟩
  rw [burnsideF429a_subgroupOf_inf, h1, h2, e1, e2, Subgroup.map_inf_eq _ _ _ Ψ.injective]

theorem burnsideF429a_key1_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, _, hK, Ψ, hB, h₁, -⟩ := burnsideF429a_U5_setup5 hyp
  obtain ⟨hH₀, hH₀H, hdet⟩ := burnsideF429a_U5_pt_family hK
  exact burnsideF429a_key_of_model_family hyp.centralizer_trivial Ψ hB
    burnsideF429a_U5_pCoreOf_borel h₁ hH₀ fun β k hk hβ1 hβ2 =>
      burnsideF429a_inner_of_borelAutDiag_family (borelAutDiag_u5 hK) hH₀H hdet β hβ1 hβ2 hk

theorem burnsideF429a_key2_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, _, hK, Ψ, hB, -, h₂⟩ := burnsideF429a_U5_setup5 hyp
  obtain ⟨hH₀, hH₀H, hdet⟩ := burnsideF429a_U5_ln_family hK
  exact burnsideF429a_key_of_model_family hyp.centralizer_trivial Ψ hB
    burnsideF429a_U5_pCoreOf_borel h₂ hH₀ fun β k hk hβ1 hβ2 =>
      burnsideF429a_inner_of_borelAutDiag_family (borelAutDiag_u5 hK) hH₀H hdet β hβ1 hβ2 hk

theorem burnsideF429a_c5_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5 .U5 Gp M₁ M₂ hyp T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, _, hK, Ψ, hB, -, -⟩ := burnsideF429a_U5_setup5 hyp
  have hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
    set φ : hypPSU hK 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
    have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
    have hGB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtP hK ⊓ u5LnP hK).map φ := burnsideF429_inf_eq_map Ψ hB
    have htop : (⊤ : Subgroup (hypPSU hK 2 1)).map φ = Gp := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact (Ψ y).2
      · intro hx
        exact ⟨Ψ.symm ⟨x, hx⟩, Subgroup.mem_top _, by simp [hφdef]⟩
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF429a_U5_pCoreOf_borel,
      ← htop]
    exact burnsideF429_isSylowOf_map φ hφ
      (u5_sylow hK : ChF.IsSylowOf 2 (hypProjUnitriangular hK 2 1) ⊤)
  exact Or.inl ⟨burnsideF429a_c5_of_key hSG inf_le_left hT (burnsideF429a_key1_U5 hyp),
    burnsideF429a_c5_of_key hSG inf_le_right hT (burnsideF429a_key2_U5 hyp)⟩

end Key

end CFSG.ASVolI

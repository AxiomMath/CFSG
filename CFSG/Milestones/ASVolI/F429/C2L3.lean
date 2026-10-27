module

public import CFSG.Milestones.ASVolI.F429.Gen
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.aOddGen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ASVolI.ChF.ClassicalRoots
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

section Transport

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_model_aut [Gp.Normal] {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {P₁ P₂ : Subgroup C} (h₁ : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (h₂ : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) {r : E} (hr : r ∈ M₁ ⊓ M₂) :
    ∃ β : MulAut C, (∀ x, β x ∈ P₁ ↔ x ∈ P₁) ∧ (∀ x, β x ∈ P₂ ↔ x ∈ P₂) ∧
      ∀ x : C, ((Ψ (β x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹ := by
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hG₁ : Gp ⊓ M₁ = P₁.map φ := burnsideF429_inf_eq_map Ψ h₁
  have hG₂ : Gp ⊓ M₂ = P₂.map φ := burnsideF429_inf_eq_map Ψ h₂
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hnorm : ∀ M : Subgroup E, r ∈ M → ∀ y : E, y ∈ Gp ⊓ M ↔ r * y * r⁻¹ ∈ Gp ⊓ M := by
    intro M hM y
    constructor
    · rintro ⟨hyG, hyM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem y hyG r,
        M.mul_mem (M.mul_mem hM hyM) (M.inv_mem hM)⟩
    · rintro ⟨hyG, hyM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hyG r⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem hM) hyM) hM
        simpa [mul_assoc] using this
  have hstab : ∀ (P : Subgroup C) (M : Subgroup E), Gp ⊓ M = P.map φ → r ∈ M →
      ∀ x, β x ∈ P ↔ x ∈ P := by
    intro P M hPM hM x
    have e1 : β x ∈ P ↔ φ (β x) ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    have e2 : x ∈ P ↔ φ x ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    rw [e1, e2, ← hPM, hβφ]
    exact (hnorm M hM (φ x)).symm
  exact ⟨β, hstab P₁ M₁ hG₁ hr.1, hstab P₂ M₂ hG₂ hr.2, hβφ⟩

theorem burnsideF429_mem_of_inner [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {β : MulAut C} {r : E}
    (hβ : ∀ x : C, ((Ψ (β x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹)
    (hin : β ∈ (MulAut.conj : C →* MulAut C).range) : r ∈ Gp := by
  obtain ⟨g, hg⟩ := hin
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβ x
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1
    rw [← e1]
  rw [burnsideF4d_rho_injective hc hρ]
  exact (Ψ g).2

end Transport

section Model

open CFSG.QuasithinUnique.Fin257.L3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem burnsideF429_L3_field_descent (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {β : MulAut (projectiveSL 3 K)}
    (h₀ : ∀ x, β x ∈ (Q3 K 0).map (proj 3 K) ↔ x ∈ (Q3 K 0).map (proj 3 K))
    (h₁ : ∀ x, β x ∈ (Q3 K 1).map (proj 3 K) ↔ x ∈ (Q3 K 1).map (proj 3 K))
    (hβ2 : β ^ 2 = 1)
    (hout : β ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Even f ∧ ∃ (H : GL (Fin 3) K) (σ : K ≃+* K), (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧
      β = conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹ := by
  have hBD := CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := K)
  have hOG := CFSG.QuasithinUnique.Borel252.L3.overgroupData_L3 (F := K)
  have hN : ∀ x, β x ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set _) ↔
      x ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set _) := by
    rcases hOG.eq_of_between hBD.lt₁ hBD.lt_top₁ with e | e
    · rw [e]
      exact h₀
    · rw [e]
      exact h₁
  have hV : ∀ x, x ∈ (V1 : Subgroup (projectiveSL 3 K)) ↔ β x ∈ (V1 : Subgroup (projectiveSL 3 K)) :=
    (CFSG.Quasithin.H13.F431.mem_autStab_iff_of_normalizer hBD.core₁ β).mp
      (fun y => (hN y).symm)
  have hS : β ∈ semilinearAutGroup 3 K :=
    CFSG.Quasithin.H13.F431.L3.P3.mem_semilinear_of_map_V1 (fun g hg => (hV g).mp hg)
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp hS
  have hσ : σ ≠ 1 := by
    intro hσ1
    apply hout
    have hlin : β ∈ linearAutGroup 3 K := by
      rw [hAσ, hσ1, map_one, mul_one]
      exact conjAut_mem_linearAutGroup A
    refine CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) β
      hlin 1 ?_
    · have := h.trans (Nat.gcd_dvd_left 3 _)
      omega
    · rw [pow_one, hβ2]
      exact Subgroup.one_mem _
  have hα : (conjAut 3 K A * fieldAut 3 K σ) ^ 2 = 1 := by rw [← hAσ]; exact hβ2
  obtain ⟨hfe, hσpow, H, hH⟩ := even_linear_field_involution_descent hf hK le_rfl A σ hσ hα
  exact ⟨hfe, H, σ, hσpow, hAσ.trans hH⟩

end Model

section L3Coordinates

open CFSG.ASVolI.ChF.ClassicalRoots

private theorem burnsideF429_L3_comap_nativeParabolic (q : ℕ) (K : Type) [Field K]
    (basis : GL (Fin 3) K) (hb : basis = 1) (b : Bool) :
    (nativeParabolic .L3 q K basis b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom =
      Q3 K (if b then 1 else 0) := by
  subst hb
  ext A
  have h1 : A ∈ (nativeParabolic .L3 q K 1 b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom ↔
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : GL (Fin 3) K)) ∈
        rawStabilizer ((fun vector =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
          coordinateSpace (if b then flagTwo .L3 else flagOne .L3 : Set (Fin 3))) :=
    Iff.rfl
  refine h1.trans ?_
  rw [burnsideF4d_Y1_mem_rawStabilizer, burnsideF4d_Y1_image_one, Q3,
    burnsideF4d_Y1_mem_stabilizer_iff]
  have key : ∀ (S : Set (Fin 3)) (i : ℕ), S = {p : Fin 3 | (p : ℕ) < i} →
      ((∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ flagSpace 3 K i ↔
          v ∈ flagSpace 3 K i) := by
    intro S i hS
    subst hS
    simp only [burnsideF4d_Y1_coordinateSpace_flag]
  cases b
  · exact key _ 1 (by ext p; simp [flagOne] <;> omega)
  · exact key _ 2 (by ext p; simp [flagTwo] <;> omega)

noncomputable def burnsideF429_L3_Psi {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) : projectiveSL 3 marking.field ≃* H :=
  (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).trans
    marking.identification

private theorem burnsideF429_L3_Psi_proj {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF429_L3_Psi marking (proj 3 marking.field A) =
      marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :=
  rfl

theorem burnsideF429_L3_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) (b : Bool) :
    marking.parabolic b = ((Q3 marking.field (if b then 1 else 0)).map (proj 3 marking.field)).map
      (burnsideF429_L3_Psi marking).toMonoidHom := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have key := burnsideF429_L3_comap_nativeParabolic (2 ^ f) marking.field marking.basis hbasis b
  have hsurj :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field).surjective
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj z
    refine ⟨proj 3 marking.field A, ⟨A, ?_, rfl⟩, burnsideF429_L3_Psi_proj marking A⟩
    rw [← key]
    exact hz
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    rw [← key] at hA
    exact ⟨_, hA, (burnsideF429_L3_Psi_proj marking A).symm⟩

end L3Coordinates

section Payload

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_subgroupOf_eq_of_inf {M : Subgroup E} {X : Subgroup ↥Gp}
    (h : Gp ⊓ M = X.map Gp.subtype) : M.subgroupOf Gp = X := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have : (x : E) ∈ X.map Gp.subtype := h ▸ ⟨x.2, hx⟩
    obtain ⟨y, hy, hyx⟩ := this
    rwa [Subtype.ext hyx] at hy
  · intro hx
    have : (x : E) ∈ Gp ⊓ M := h ▸ ⟨x, hx, rfl⟩
    exact this.2

section Clause2c


theorem burnsideF429_c2c_L3 {f : ℕ} (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) {t : E} (htT : t ∈ T)
    (htS : t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (htt : t * t = 1) :
    hyp.toHypF_4_4g.chart.IsFieldInv t := by
  haveI := hyp.finite
  haveI := hyp.normal
  have htG : t ∉ Gp := fun h => htS (by rw [← burnsideF429_T_inf_Gp hyp hT]; exact ⟨htT, h⟩)
  have htM : t ∈ M₁ ⊓ M₂ := hT.1 htT
  have hf1 : 1 ≤ f := hyp.model.2.1
  have hfits := hyp.toHypF_4_4g.chart.coordinatePayload_fits
  have hm := hyp.toHypF_4_4g.chart_matches
  unfold NativeChart.IsFieldInv
  refine ⟨htG, htt, ?_⟩
  generalize hcp : hyp.toHypF_4_4g.chart.coordinatePayload = cp at hfits ⊢
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .L3 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    have hK : Nat.card mk.field = 2 ^ f := by simpa using mk.field_card
    haveI : CharP mk.field 2 := burnsideF4gSp_charP_of_card hK
    set Ψ := burnsideF429_L3_Psi mk with hΨ
    have e0 := burnsideF429_L3_parabolic mk false
    have e1 := burnsideF429_L3_parabolic mk true
    simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
    have h₁ : M₁.subgroupOf Gp = ((Q3 mk.field 0).map (proj 3 mk.field)).map Ψ.toMonoidHom := by
      rw [← e0]
      exact burnsideF429_subgroupOf_eq_of_inf (hm.2.1.trans hpts)
    have h₂ : M₂.subgroupOf Gp = ((Q3 mk.field 1).map (proj 3 mk.field)).map Ψ.toMonoidHom := by
      rw [← e1]
      exact burnsideF429_subgroupOf_eq_of_inf (hm.2.2.trans hlns)
    obtain ⟨β, hβ₀, hβ₁, hβ⟩ := burnsideF429_model_aut Ψ h₁ h₂ htM
    have hβ2 : β ^ 2 = 1 :=
      burnsideF429a_pow_eq_one_of_intertwine Ψ hβ (n := 2) (by rw [pow_two]; exact htt)
    have hout : β ∉ (MulAut.conj : projectiveSL 3 mk.field →* MulAut _).range := fun hin =>
      htG (burnsideF429_mem_of_inner hyp.centralizer_trivial Ψ hβ hin)
    obtain ⟨hfe, H, σ, hσpow, hβeq⟩ := burnsideF429_L3_field_descent hK hf1 hβ₀ hβ₁ hβ2 hout
    obtain ⟨d, hd⟩ := hfe
    refine ⟨d, by omega, by omega, ?_⟩
    set conj : MulAut ↥Gp := (Ψ.symm.trans (conjAut 3 mk.field H)).trans Ψ with hconj
    have hconjΨ : ∀ y, conj (Ψ y) = Ψ (conjAut 3 mk.field H y) := by
      intro y
      rw [hconj]
      simp
    have hΨproj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) mk.field,
        Ψ (proj 3 mk.field g) =
          mk.transport (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 mk.field g) :=
      fun g => burnsideF429_L3_Psi_proj mk g
    have hsurj := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 mk.field).surjective
    have hd' : f / 2 = d := by omega
    refine ⟨conj, ⟨H, ?_, ?_⟩, ⟨Or.inl rfl, σ.toRingHom, ?_, ?_⟩⟩
    ·
      ext A
      constructor
      · rintro ⟨B, hB, rfl⟩
        refine CFSG.Open.StatedAPI.mem_statedSL_iff.2 ?_
        have hB' := CFSG.Open.StatedAPI.mem_statedSL_iff.1 hB
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Matrix.det_mul,
          hB', mul_one]
        rw [mul_comm, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.det_one]
      · intro hA
        refine ⟨H⁻¹ * A * H, ?_, by simp [mul_assoc]⟩
        refine CFSG.Open.StatedAPI.mem_statedSL_iff.2 ?_
        have hA' := CFSG.Open.StatedAPI.mem_statedSL_iff.1 hA
        simp only [Units.val_mul, Matrix.det_mul, hA', mul_one]
        rw [mul_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.det_one]
    · intro r
      obtain ⟨g, rfl⟩ := hsurj r
      refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 mk.field
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 mk.field H g), ?_, ?_⟩
      · apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact coe_slConjugation H g
      · rw [← hΨproj, ← hΨproj, ← conjAut_proj, hconjΨ]
    · intro x
      rw [show d = f / 2 by omega]
      exact hσpow x
    · intro r
      obtain ⟨g, rfl⟩ := hsurj r
      refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 mk.field
        (Matrix.SpecialLinearGroup.map σ.toRingHom g), rfl, ?_⟩
      show ((conj (mk.transport _) : ↥Gp) : E) = t * ((conj (mk.transport _) : ↥Gp) : E) * t⁻¹
      rw [← hΨproj, ← hΨproj, hconjΨ, hconjΨ, ← hβ, hβeq]
      simp only [MulAut.mul_apply, MulAut.inv_apply]
      rw [MulEquiv.symm_apply_apply, fieldAut_proj]
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

end Clause2c

end Payload

end CFSG.ASVolI

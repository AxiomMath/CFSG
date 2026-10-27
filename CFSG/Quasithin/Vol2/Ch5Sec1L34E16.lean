module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2

public section

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin

variable {k : Type} [Field k]

theorem unitri_entries {g : SpecialLinearGroup (Fin 3) k} (hg : g ∈ unitriangular 3 k) :
    (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) k) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 2 = 1 :=
  ⟨hg.1 1 0 (by decide), hg.1 2 0 (by decide), hg.1 2 1 (by decide), hg.2 0, hg.2 1, hg.2 2⟩

theorem unitri_mul_apply_zero_one {g h : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ unitriangular 3 k) (hh : h ∈ unitriangular 3 k) :
    ((g * h : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 1 =
      (g : Matrix (Fin 3) (Fin 3) k) 0 1 + (h : Matrix (Fin 3) (Fin 3) k) 0 1 := by
  obtain ⟨-, -, -, g00, -, -⟩ := unitri_entries hg
  obtain ⟨-, -, h21, -, h11, -⟩ := unitri_entries hh
  change ((g : Matrix (Fin 3) (Fin 3) k) * (h : Matrix (Fin 3) (Fin 3) k)) 0 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, g00, h11, h21]
  ring

theorem unitri_mul_apply_one_two {g h : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ unitriangular 3 k) (hh : h ∈ unitriangular 3 k) :
    ((g * h : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 2 =
      (g : Matrix (Fin 3) (Fin 3) k) 1 2 + (h : Matrix (Fin 3) (Fin 3) k) 1 2 := by
  obtain ⟨g10, -, -, -, g11, -⟩ := unitri_entries hg
  obtain ⟨-, -, -, -, -, h22⟩ := unitri_entries hh
  change ((g : Matrix (Fin 3) (Fin 3) k) * (h : Matrix (Fin 3) (Fin 3) k)) 1 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, g10, g11, h22]
  ring

theorem unitri_mul_self_apply_zero_two [CharP k 2] {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ unitriangular 3 k) :
    ((g * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 2 =
      (g : Matrix (Fin 3) (Fin 3) k) 0 1 * (g : Matrix (Fin 3) (Fin 3) k) 1 2 := by
  obtain ⟨-, -, -, g00, -, g22⟩ := unitri_entries hg
  change ((g : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, g00, g22]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  linear_combination ((g : Matrix (Fin 3) (Fin 3) k) 0 2) * h2

theorem unitri_eq_rad {g : SpecialLinearGroup (Fin 3) k} (hg : g ∈ unitriangular 3 k)
    (h12 : (g : Matrix (Fin 3) (Fin 3) k) 1 2 = 0) :
    g = rad ((g : Matrix (Fin 3) (Fin 3) k) 0 1) ((g : Matrix (Fin 3) (Fin 3) k) 0 2) := by
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := unitri_entries hg
  ext i j
  rw [coe_rad]
  fin_cases i <;> fin_cases j <;> simp [g10, g20, g21, g00, g11, g22, h12]

theorem alpha0_proj_unitri {σ : k ≃+* k} {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ unitriangular 3 k) (h01 : (g : Matrix (Fin 3) (Fin 3) k) 0 1 = 0)
    (hsq : g * g = 1) :
    LinearThreeFourOuter.nf σ w0GL 1 1 (proj 3 k g) =
      proj 3 k (rad (σ ((g : Matrix (Fin 3) (Fin 3) k) 1 2))
        (σ ((g : Matrix (Fin 3) (Fin 3) k) 0 2))) := by
  rw [alpha0_proj]
  congr 1
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := unitri_entries hg
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hsq
  ext i j
  rw [alpha0_matrix, hinv, coe_rad]
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  fin_cases i <;> fin_cases j <;>
    simp [r0, r1, r2, g10, g20, g21, g00, g11, g22, h01]

variable (hk : Nat.card k = 4)
include hk

theorem eq_radP_or_of_isElemAbelian {E : Subgroup (projectiveSL 3 k)}
    (hEU : E ≤ projUnitriangular 3 k) (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16) :
    E = radP ∨ E = radP.map (alpha0Aut hk).toMonoidHom := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hrep : ∀ x ∈ E, ∃ g ∈ unitriangular 3 k, proj 3 k g = x := fun x hx => hEU hx
  have hsq : ∀ x ∈ E, ∀ g ∈ unitriangular 3 k, proj 3 k g = x → g * g = 1 := by
    intro x hx g hg hgx
    have h1 : proj 3 k (g * g) = proj 3 k 1 := by
      rw [map_mul, hgx, map_one, ← sq]
      exact hE.2 x hx
    exact proj_injOn_unitriangular 3 ((unitriangular 3 k).mul_mem hg hg)
      (unitriangular 3 k).one_mem h1
  have hprod : ∀ x ∈ E, ∀ g ∈ unitriangular 3 k, proj 3 k g = x →
      (g : Matrix (Fin 3) (Fin 3) k) 0 1 * (g : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by
    intro x hx g hg hgx
    rw [← unitri_mul_self_apply_zero_two hg, hsq x hx g hg hgx]
    simp
  have hcardR : Nat.card (radP (k := k)) = 16 := card_radP hk
  by_cases hcase : ∃ x ∈ E, ∃ g ∈ unitriangular 3 k, proj 3 k g = x ∧
      (g : Matrix (Fin 3) (Fin 3) k) 1 2 ≠ 0
  ·
    obtain ⟨x₁, hx₁, g₁, hg₁, hgx₁, h12⟩ := hcase
    have h01₁ : (g₁ : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
      have := hprod x₁ hx₁ g₁ hg₁ hgx₁
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h h12
    have hall : ∀ x ∈ E, ∀ g ∈ unitriangular 3 k, proj 3 k g = x →
        (g : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
      intro x hx g hg hgx
      by_contra h01
      have h12' : (g : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by
        have := hprod x hx g hg hgx
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h01
        · exact h
      have hmem : x₁ * x ∈ E := E.mul_mem hx₁ hx
      have hgg := hprod (x₁ * x) hmem (g₁ * g) ((unitriangular 3 k).mul_mem hg₁ hg)
        (by rw [map_mul, hgx₁, hgx])
      rw [unitri_mul_apply_zero_one hg₁ hg, unitri_mul_apply_one_two hg₁ hg, h01₁, h12',
        zero_add, add_zero] at hgg
      rcases mul_eq_zero.mp hgg with h | h
      · exact h01 h
      · exact h12 h
    have hle : E.map (alpha0Aut hk).toMonoidHom ≤ radP := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨g, hg, hgx⟩ := hrep x hx
      rw [mem_radP]
      refine ⟨frobeniusEquiv k 2 ((g : Matrix (Fin 3) (Fin 3) k) 1 2),
        frobeniusEquiv k 2 ((g : Matrix (Fin 3) (Fin 3) k) 0 2), ?_⟩
      rw [← hgx, ← alpha0_proj_unitri hg (hall x hx g hg hgx) (hsq x hx g hg hgx)]
      rfl
    have heq : E.map (alpha0Aut hk).toMonoidHom = radP :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (alpha0Aut hk).injective, hcard, hcardR])
    have hE' : E = (radP (k := k)).map (alpha0Aut hk)⁻¹.toMonoidHom := by
      rw [← heq, map_map_mulAut, inv_mul_cancel]
      exact (Subgroup.map_id E).symm
    have hU : (projUnitriangular 3 k).map (alpha0Aut hk)⁻¹.toMonoidHom =
        projUnitriangular 3 k := by
      conv_lhs => rw [← alpha0Aut_map_projUnitriangular hk]
      rw [map_map_mulAut, inv_mul_cancel]
      exact Subgroup.map_id _
    rw [hE']
    exact map_radP_mem hk hU
  ·
    push Not at hcase
    left
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, hcardR])
    intro x hx
    obtain ⟨g, hg, hgx⟩ := hrep x hx
    rw [mem_radP]
    refine ⟨(g : Matrix (Fin 3) (Fin 3) k) 0 1, (g : Matrix (Fin 3) (Fin 3) k) 0 2, ?_⟩
    rw [← hgx, ← unitri_eq_rad hg (hcase x hx g hg hgx)]

omit hk in
@[expose] def upperE12 : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

omit hk in
theorem coe_upperE12 :
    ((upperE12 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

theorem exists_not_mem_centralizer {R : Subgroup (projectiveSL 3 k)}
    (hR : R = radP ∨ R = radP.map (alpha0Aut hk).toMonoidHom) :
    ∃ s ∈ projUnitriangular 3 k, s ∉ Subgroup.centralizer (R : Set (projectiveSL 3 k)) := by
  have hu : upperE12 ∈ unitriangular 3 k := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [coe_upperE12]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · rw [coe_upperE12]
      fin_cases i <;> simp
  have hr : rad (1 : k) 0 ∈ unitriangular 3 k := rad_mem_unitriangular 1 0
  have hne : proj 3 k upperE12 * proj 3 k (rad 1 0) ≠ proj 3 k (rad 1 0) * proj 3 k upperE12 := by
    intro h
    rw [← map_mul, ← map_mul] at h
    have h' := proj_injOn_unitriangular 3 ((unitriangular 3 k).mul_mem hu hr)
      ((unitriangular 3 k).mul_mem hr hu) h
    have h02 : (((upperE12 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        (rad (1 : k) 0 : Matrix (Fin 3) (Fin 3) k)) 0 2 =
        ((rad (1 : k) 0 : Matrix (Fin 3) (Fin 3) k) *
          ((upperE12 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 2 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) 0 2) h'
    rw [coe_upperE12, coe_rad] at h02
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h02
  have hs : proj 3 k upperE12 ∈ projUnitriangular 3 k := ⟨_, hu, rfl⟩
  have hrR : proj 3 k (rad (1 : k) 0) ∈ (radP (k := k)) := mem_radP.mpr ⟨1, 0, rfl⟩
  rcases hR with rfl | rfl
  · refine ⟨_, hs, fun hc => hne ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hc _ hrR).symm
  · refine ⟨alpha0Aut hk (proj 3 k upperE12), ?_, fun hc => hne ?_⟩
    · rw [← alpha0Aut_map_projUnitriangular hk]
      exact Subgroup.mem_map_of_mem _ hs
    · have h1 := Subgroup.mem_centralizer_iff.mp hc _ (Subgroup.mem_map_of_mem _ hrR)
      simp only [MulEquiv.coe_toMonoidHom] at h1
      have h2 : alpha0Aut hk (proj 3 k (rad 1 0) * proj 3 k upperE12) =
          alpha0Aut hk (proj 3 k upperE12 * proj 3 k (rad 1 0)) := by
        rw [map_mul, map_mul]
        exact h1
      exact ((alpha0Aut hk).injective h2).symm

end CFSG.Quasithin.H13.KGL34P

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem twoParRad_model {k : Type} [Field k] (hk : Nat.card k = 4) {R : Subgroup (projectiveSL 3 k)}
    (hR : R = KGL34P.radP ∨ R = (KGL34P.radP (k := k)).map (KGL34P.alpha0Aut hk).toMonoidHom) :
    TwoParRad (projectiveSL 3 k) (projUnitriangular 3 k) R := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : TwoParRad (projectiveSL 3 k) (projUnitriangular 3 k) KGL34P.radP := by
    refine ⟨KGL34P.radP_le_projUnitriangular, ?_, ?_, KGL34P.card_radP hk, ?_, ?_,
      fun α hα hαU => KGL34P.map_radP_of_odd hk hα hαU⟩
    · rw [normalizer_projUnitriangular 2, KGL34P.normalizer_radP hk]
      exact projUpperTriangular_le_projStabilizer 1
    · refine ⟨⟨⟨fun x y => Subtype.ext (KGL34P.radP_comm x.2 y.2)⟩⟩, fun x hx => ?_⟩
      exact KGL34P.radP_sq hk hx
    · have hN := KGL34P.normalizer_radP hk
      refine ⟨(KGL34P.piL2 hk).comp (MulEquiv.subgroupCongr hN).toMonoidHom,
        (KGL34P.piL2_surjective hk).comp (MulEquiv.subgroupCongr hN).surjective, ?_⟩
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, KGL34P.ker_piL2 hk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      rfl
    · rw [KGL34P.normalizer_radP hk]
      exact KGL34P.oTwoUpper_projStabilizer_one hk
  rcases hR with rfl | rfl
  · exact hR2
  · have := hR2.map (KGL34P.alpha0Aut hk)
    rwa [KGL34P.alpha0Aut_map_projUnitriangular hk] at this

theorem exists_twoParRad_of_isElemAbelian {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 3 2 2) {R : Subgroup X} (hR : IsElemAbelian 2 R)
    (hcard : Nat.card R = 16) :
    ∃ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ ∧ TwoParRad X S₀ R ∧
      ∃ s ∈ S₀, s ∉ Subgroup.centralizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨S₀, hS₀, hRS₀⟩ := A4.exists_isSylowTwoOf_ge le_top hR2
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS₀
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hEU : R.map e.toMonoidHom ≤ projUnitriangular 3 k := by
    rw [← he]
    exact Subgroup.map_mono hRS₀
  have hEab := isElemAbelian_map_mulEquiv e hR
  have hEcard : Nat.card (R.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  have hcases := KGL34P.eq_radP_or_of_isElemAbelian hk hEU hEab hEcard
  have hS₀eq : S₀ = (projUnitriangular 3 k).map e.symm.toMonoidHom := by
    rw [← he, Subgroup.map_map]
    simp
  have hReq : R = (R.map e.toMonoidHom).map e.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    simp
  refine ⟨S₀, hS₀, ?_, ?_⟩
  · have := (twoParRad_model hk hcases).map e.symm
    rw [← hS₀eq, ← hReq] at this
    exact this
  · obtain ⟨s, hs, hsC⟩ := KGL34P.exists_not_mem_centralizer hk hcases
    refine ⟨e.symm s, ?_, fun hc => hsC ?_⟩
    · rw [hS₀eq]
      exact Subgroup.mem_map_of_mem _ hs
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hc r hr
      have h2 := congrArg e h1
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2

end CFSG.Quasithin.H13

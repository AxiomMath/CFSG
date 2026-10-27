module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapKill

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial

open scoped Pointwise

@[expose] def A2KleinData {G : Type} [Group G] (S : Subgroup G) : Prop :=
  Nat.card ↥S = 64 ∧ Nat.card ↥(S ⊓ centralizer (S : Set G)) = 4 ∧
    ∃ h ∈ normalizer (S : Set G),
      ∀ z ∈ S ⊓ centralizer (S : Set G), z ≠ 1 → h * z * h⁻¹ ≠ z

section A2

variable {F : Type} [Field F]

private lemma wcgapa2_wMat_injective :
    Function.Injective (LinearFieldFour.wMat : F → Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro a b h
  have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
    (A : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simpa [LinearFieldFour.coe_wMat, LinearFieldFour.wM] using h'

private lemma wcgapa2_wMat_zero :
    LinearFieldFour.wMat (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.coe_wMat, LinearFieldFour.wM]

private lemma wcgapa2_wMat_mem_unitriangular (c : F) :
    LinearFieldFour.wMat c ∈ LinearFlag.unitriangular 3 F := by
  rw [LinearFlag.mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [LinearFieldFour.coe_wMat, LinearFieldFour.wM]
  · intro i
    fin_cases i <;> simp [LinearFieldFour.coe_wMat, LinearFieldFour.wM]

private lemma wcgapa2_wMat_mem_centralizer (c : F) :
    LinearFieldFour.wMat c ∈
      Subgroup.centralizer (LinearFlag.unitriangular 3 F :
        Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.coe_wMat, LinearFieldFour.wM, Matrix.mul_apply,
      Fin.sum_univ_three, hu.2 0, hu.2 1, hu.2 2, hu.1 1 0 (by decide),
      hu.1 2 0 (by decide), hu.1 2 1 (by decide)] <;> ring

private lemma wcgapa2_xMat_mem_unitriangular (a : F) :
    LinearFieldFour.xMat a ∈ LinearFlag.unitriangular 3 F := by
  rw [LinearFlag.mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [LinearFieldFour.xMat, LinearFieldFour.xM]
  · intro i
    fin_cases i <;> simp [LinearFieldFour.xMat, LinearFieldFour.xM]

private lemma wcgapa2_yMat_mem_unitriangular (b : F) :
    LinearFieldFour.yMat b ∈ LinearFlag.unitriangular 3 F := by
  rw [LinearFlag.mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [LinearFieldFour.yMat, LinearFieldFour.yM]
  · intro i
    fin_cases i <;> simp [LinearFieldFour.yMat, LinearFieldFour.yM]

private lemma wcgapa2_coe_eq_of_mem_unitriangular (u : Matrix.SpecialLinearGroup (Fin 3) F)
    (hu : u ∈ LinearFlag.unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) =
      !![1, (u : Matrix (Fin 3) (Fin 3) F) 0 1, (u : Matrix (Fin 3) (Fin 3) F) 0 2;
         0, 1, (u : Matrix (Fin 3) (Fin 3) F) 1 2;
         0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hu.2 0, hu.2 1, hu.2 2, hu.1 1 0 (by decide), hu.1 2 0 (by decide),
      hu.1 2 1 (by decide)]

private lemma wcgapa2_mem_inf_centralizer_imp (u : Matrix.SpecialLinearGroup (Fin 3) F)
    (hu : u ∈ LinearFlag.unitriangular 3 F ⊓
      Subgroup.centralizer (LinearFlag.unitriangular 3 F :
        Set (Matrix.SpecialLinearGroup (Fin 3) F))) :
    ∃ c : F, LinearFieldFour.wMat c = u := by
  obtain ⟨huU, huc⟩ := Subgroup.mem_inf.mp hu
  have hu_eq := wcgapa2_coe_eq_of_mem_unitriangular u huU
  have hx := huc (LinearFieldFour.xMat 1) (wcgapa2_xMat_mem_unitriangular 1)
  have hy := huc (LinearFieldFour.yMat 1) (wcgapa2_yMat_mem_unitriangular 1)
  have h12 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have h := congrFun (congrFun (congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F)) hx) 0) 2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu_eq] at h
    simp [LinearFieldFour.xMat, LinearFieldFour.xM, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.mul_fin_three] at h
    exact h
  have h01 : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
    have h := congrFun (congrFun (congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F)) hy) 0) 2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu_eq] at h
    simp [LinearFieldFour.yMat, LinearFieldFour.yM, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.mul_fin_three] at h
    exact h
  refine ⟨(u : Matrix (Fin 3) (Fin 3) F) 0 2, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.coe_wMat, LinearFieldFour.wM, huU.2 0, huU.2 1, huU.2 2,
      huU.1 1 0 (by decide), huU.1 2 0 (by decide), huU.1 2 1 (by decide), h01, h12]

private lemma wcgapa2_card_inf_centralizer_unitriangular [Finite F] (hF : Nat.card F = 4) :
    Nat.card ↥(LinearFlag.unitriangular 3 F ⊓
      Subgroup.centralizer (LinearFlag.unitriangular 3 F :
        Set (Matrix.SpecialLinearGroup (Fin 3) F))) = 4 := by
  let f : F → ↥(LinearFlag.unitriangular 3 F ⊓
      Subgroup.centralizer (LinearFlag.unitriangular 3 F :
        Set (Matrix.SpecialLinearGroup (Fin 3) F))) := fun c => ⟨LinearFieldFour.wMat c,
    Subgroup.mem_inf.mpr ⟨wcgapa2_wMat_mem_unitriangular c, wcgapa2_wMat_mem_centralizer c⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => wcgapa2_wMat_injective (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨c, hc⟩ := wcgapa2_mem_inf_centralizer_imp
      (z : Matrix.SpecialLinearGroup (Fin 3) F) z.2
    exact ⟨c, Subtype.ext hc⟩
  have hcard : Nat.card F = Nat.card ↥(LinearFlag.unitriangular 3 F ⊓
      Subgroup.centralizer (LinearFlag.unitriangular 3 F :
        Set (Matrix.SpecialLinearGroup (Fin 3) F))) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hcard]
  exact hF

private lemma wcgapa2_hMat_conj_wMat {ω : F} (hω : ω * ω * ω = 1) (c : F) :
    LinearFieldFour.hMat ω hω * LinearFieldFour.wMat c * (LinearFieldFour.hMat ω hω)⁻¹ =
      LinearFieldFour.wMat (ω * ω * c) := by
  rw [LinearFieldFour.hMat_mul_wMat hω c, mul_assoc, mul_inv_cancel, mul_one]

private lemma wcgapa2_a2KleinData_unitriangular [Finite F] (hF : Nat.card F = 4) :
    A2KleinData (LinearFlag.unitriangular 3 F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearFlag.card_unitriangular, hF]
    norm_num
  · exact wcgapa2_card_inf_centralizer_unitriangular hF
  · obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hF
    have hω3 : ω * ω * ω = 1 := LinearFieldFour.omega_cube hF hω0
    refine ⟨LinearFieldFour.hMat ω hω3, ?_, ?_⟩
    · rw [LinearFlag.normalizer_unitriangular, LinearFlag.mem_upperTriangular]
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [LinearFieldFour.hMat, LinearFieldFour.hM]
    · intro z hz hz1
      obtain ⟨c, rfl⟩ := wcgapa2_mem_inf_centralizer_imp z hz
      have hc : c ≠ 0 := by
        intro hc0
        exact hz1 (by rw [hc0, wcgapa2_wMat_zero])
      have hne : ω * ω * c ≠ c := by
        intro heq
        have hω2 : ω * ω = 1 := by
          have h := congrArg (· * c⁻¹) heq
          rw [mul_assoc, mul_inv_cancel₀ hc, mul_one] at h
          exact h
        have hω1' : ω = 1 := by
          have h := hω3
          rw [hω2, one_mul] at h
          exact h
        exact hω1 hω1'
      rw [wcgapa2_hMat_conj_wMat hω3 c]
      exact fun h => hne (wcgapa2_wMat_injective h)

end A2

section Conj

variable {G : Type} [Group G]

private lemma wcgapa2_a2KleinData_map_conj (S : Subgroup G) (e : G ≃* G)
    (h : A2KleinData S) : A2KleinData (S.map (e : G →* G)) := by
  obtain ⟨hcard, hZcard, h1, hh1N, hfix1⟩ := h
  have hZ : (S.map (e : G →* G)) ⊓
        Subgroup.centralizer ((S.map (e : G →* G) : Subgroup G) : Set G)
      = (S ⊓ Subgroup.centralizer (S : Set G)).map (e : G →* G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hxS
      refine Subgroup.mem_map.mpr ⟨s, ⟨hs, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
      have hxt := Subgroup.mem_centralizer_iff.mp hxc (e t)
        (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
      exact e.injective (by rw [map_mul, map_mul]; exact hxt)
    · refine le_inf (Subgroup.map_mono inf_le_left) ?_
      refine (Subgroup.map_mono inf_le_right).trans ?_
      rw [Subgroup.coe_map]
      exact Subgroup.map_centralizer_le_centralizer_image (S : Set G) (e : G →* G)
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MulEquiv.subgroupMap e S).toEquiv]
    exact hcard
  · rw [hZ, ← Nat.card_congr
      (MulEquiv.subgroupMap e (S ⊓ Subgroup.centralizer (S : Set G))).toEquiv]
    exact hZcard
  · refine ⟨e h1, ?_, ?_⟩
    · rw [← Subgroup.map_normalizer_eq_of_bijective S (f := (e : G →* G)) e.bijective]
      exact Subgroup.mem_map.mpr ⟨h1, hh1N, rfl⟩
    · intro z hz hz1
      rw [hZ] at hz
      obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
      have hz0ne : z0 ≠ 1 := fun h0 => hz1 (by rw [h0, map_one])
      have hfix := hfix1 z0 hz0 hz0ne
      intro heq
      exact hfix (by simpa using congrArg e.symm heq)

end Conj

theorem a2KleinData_slThree {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F)) :
    A2KleinData (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  haveI : CharP F 2 := LinearFieldFour.charP_two_of_card_eq_four hF
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU : A2KleinData (LinearFlag.unitriangular 3 F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    wcgapa2_a2KleinData_unitriangular hF
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) F) P₀ S
  have hS : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) =
      (LinearFlag.unitriangular 3 F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hP₀, Subgroup.pointwise_smul_def]
    rfl
  rw [hS]
  exact wcgapa2_a2KleinData_map_conj (LinearFlag.unitriangular 3 F) (MulAut.conj g) hU

theorem borelKills_center_of_a2 {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hp : IsPGroup 2 S) (h : A2KleinData S) : BorelKills S (S ⊓ centralizer (S : Set G)) := by
  obtain ⟨h64, hZ, d, hd, hfix⟩ := h
  refine borelKills_center_of_irred hp ?_ (centerIrred_of_klein hZ hd hfix)
  rw [hZ, h64]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81

end

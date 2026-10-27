module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5GlueA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

private noncomputable def s16c11_case5_scalHomB (K : Type) [Field K] :
    Kˣ →* MulAut (VM K) where
  toFun c := lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
  map_one' := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (1 : Kˣ)) 1 = 1
    rw [map_one, lr_one]
  map_mul' c d := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (c * d)) 1 =
      lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1 *
        lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
    rw [map_mul, lr_mul, mul_one]

private theorem s16c11_case5_scal_eq_rangeB (K : Type) [Field K] :
    s16c11C5Scal K = (s16c11_case5_scalHomB K).range := by
  rw [s16c11C5Scal]
  have h : {x : MulAut (VM K) | ∃ c : Kˣ,
      x = lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1} =
      Set.range (s16c11_case5_scalHomB K) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range, s16c11_case5_scalHomB]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  rw [h, ← MonoidHom.coe_range, Subgroup.closure_eq]

private theorem s16c11_case5_scalHom_injectiveB (K : Type) [Field K] :
    Function.Injective (s16c11_case5_scalHomB K) := by
  intro c d h
  have h1 : Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) =
      Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) :=
    congrArg (fun ψ : MulAut (VM K) =>
      Multiplicative.toAdd (ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K)))) h
  simp only [toAdd_lr, toAdd_ofAdd, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
    Units.coe_map] at h1
  exact Units.ext (Matrix.scalar_inj.mp h1)

private theorem s16c11_case5_card_scalB (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) : Nat.card ↥(s16c11C5Scal K) = 3 := by
  rw [s16c11_case5_scal_eq_rangeB]
  have hcard : Nat.card ↥((s16c11_case5_scalHomB K).range) = Nat.card Kˣ := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (s16c11_case5_scalHom_injectiveB K), Subgroup.card_top]
  rw [hcard, Nat.card_units, hK]

private theorem s16c11_case5_congr_symm {M N : Type*} [Group M] [Group N] (φ : M ≃* N) :
    (MulAut.congr φ).symm = MulAut.congr φ.symm := by
  ext x
  rfl

private theorem s16c11_case5_congr_comp {M N : Type*} [Group M] [Group N] (φ : M ≃* N) :
    (MulAut.congr φ).toMonoidHom.comp (MulAut.congr φ.symm).toMonoidHom =
      MonoidHom.id (MulAut N) := by
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  show (MulAut.congr φ) ((MulAut.congr φ.symm) x) = x
  rw [← s16c11_case5_congr_symm φ]
  exact (MulAut.congr φ).apply_symm_apply x

private theorem s16c11_case5_congr_comp' {M N : Type*} [Group M] [Group N] (φ : M ≃* N) :
    (MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom =
      MonoidHom.id (MulAut M) := by
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  show (MulAut.congr φ.symm) ((MulAut.congr φ) x) = x
  rw [← s16c11_case5_congr_symm φ]
  exact (MulAut.congr φ).symm_apply_apply x

private theorem s16c11_case5_sq_eq_one_VM (K : Type) [Field K] [CharP K 2] (x : VM K) :
    x ^ 2 = 1 := by
  obtain ⟨X, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [pow_two, ← ofAdd_add]
  have hXX : X + X = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero (X i j)
  rw [hXX, ofAdd_zero]

theorem s16c11_case5_core_transport {W : Type} [CommGroup W] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (β : W ≃* VM K) {Lb Y : Subgroup (MulAut W)}
    (hL : Lb.map (MulAut.congr β).toMonoidHom = (rho (K := K)).range)
    (hLY : Lb ≤ Y) (hYN : Y ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hZY : (s16c11C5Scal K).map (MulAut.congr β.symm).toMonoidHom ≤ Y)
    {𝒮 : Set (Subgroup (MulAut W))} (h𝒮 : ∀ A ∈ 𝒮, A = ⊥ ∨ A ∈ E3.aSet 2 Y)
    (h2 : IsPGroup 2 ↥(⨆ A ∈ 𝒮, A))
    (hc : (⨆ A ∈ 𝒮, A) ≤ Subgroup.centralizer
      (((s16c11C5Scal K).map (MulAut.congr β.symm).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W))) :
    ∃ P : Subgroup (MulAut W), P ≤ Y ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P ∧
      P ≤ Subgroup.normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut W)) : Set (MulAut W)) := by
  classical
  let f : MulAut W →* MulAut (VM K) := (MulAut.congr β).toMonoidHom
  let g : MulAut (VM K) →* MulAut W := (MulAut.congr β.symm).toMonoidHom
  have hfg : f.comp g = MonoidHom.id (MulAut (VM K)) := s16c11_case5_congr_comp β
  have hgf : g.comp f = MonoidHom.id (MulAut W) := s16c11_case5_congr_comp' β
  let Z : Subgroup (MulAut (VM K)) := s16c11C5Scal K
  let Zt : Subgroup (MulAut W) := Z.map g
  let Y' : Subgroup (MulAut (VM K)) := Y.map f
  let 𝒮' : Set (Subgroup (MulAut (VM K))) := (Subgroup.map f) '' 𝒮
  have hRY' : (rho (K := K)).range ≤ Y' := by
    rw [← hL]
    exact Subgroup.map_mono hLY
  have hYN' : Y' ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) := by
    have hh : Y.map (MulAut.congr β).toMonoidHom ≤
        Subgroup.normalizer ((Lb.map (MulAut.congr β).toMonoidHom :
          Subgroup (MulAut (VM K))) : Set (MulAut (VM K))) :=
      (map_le_normalizer_map_iff (MulAut.congr β) Y Lb).mpr hYN
    rw [hL] at hh
    exact hh
  have hZY' : Z ≤ Y' := by
    have hh := Subgroup.map_mono (f := f) hZY
    rw [Subgroup.map_map, hfg, Subgroup.map_id] at hh
    exact hh
  have h𝒮' : ∀ A' ∈ 𝒮', A' = ⊥ ∨ A' ∈ E3.aSet 2 Y' := by
    intro A' hA'
    obtain ⟨A, hA, rfl⟩ := hA'
    rcases h𝒮 A hA with hb | hA2
    · left
      rw [hb]
      exact Subgroup.map_bot f
    · exact Or.inr ((aSet_map_congr_equiv_iff β 2 Y A).mpr hA2)
  have hjoin : (⨆ A' ∈ 𝒮', A') = (⨆ A ∈ 𝒮, A).map f := by
    apply le_antisymm
    · refine iSup₂_le fun A' hA' => ?_
      obtain ⟨A, hA, rfl⟩ := hA'
      exact Subgroup.map_mono (f := f)
        (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) A hA)
    · rw [Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hA => ?_
      exact le_iSup₂ (f := fun A' (_ : A' ∈ 𝒮') => A') (A.map f) ⟨A, hA, rfl⟩
  have h2' : IsPGroup 2 ↥(⨆ A' ∈ 𝒮', A') := by
    rw [hjoin]
    exact h2.map f
  have hmap_cent : (Subgroup.centralizer (Zt : Set (MulAut W))).map f ≤
      Subgroup.centralizer (Z : Set (MulAut (VM K))) := by
    refine (Subgroup.map_centralizer_le_centralizer_image (Zt : Set (MulAut W)) f).trans ?_
    apply Subgroup.centralizer_le
    intro z hz
    refine ⟨g z, Subgroup.mem_map_of_mem g hz, ?_⟩
    show f (g z) = z
    rw [← MonoidHom.comp_apply, hfg, MonoidHom.id_apply]
  have hc' : (⨆ A' ∈ 𝒮', A') ≤ Subgroup.centralizer (Z : Set (MulAut (VM K))) := by
    rw [hjoin]
    exact (Subgroup.map_mono hc).trans hmap_cent
  obtain ⟨P', hP'Y', hP'3, hP'nc, hP'norm⟩ :=
    s16c11_case5_core (K := K) hK hRY' hYN' hZY' h𝒮' h2' hc'
  have hPY : P'.map g ≤ Y := by
    have hh := Subgroup.map_mono (f := g) hP'Y'
    rw [Subgroup.map_map, hgf, Subgroup.map_id] at hh
    exact hh
  have hPnc : ¬ IsCyclic ↥(P'.map g) := by
    intro hcyc
    exact hP'nc
      ((Subgroup.equivMapOfInjective P' g (MulAut.congr β.symm).injective).isCyclic.mpr hcyc)
  have hnorm : P'.map g ≤
      Subgroup.normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut W)) : Set (MulAut W)) := by
    have hh := (map_le_normalizer_map_iff (MulAut.congr β.symm) P'
      (⨆ A' ∈ 𝒮', A')).mpr hP'norm
    rw [hjoin, Subgroup.map_map, hgf, Subgroup.map_id] at hh
    exact hh
  exact ⟨P'.map g, hPY, hP'3.map g, hPnc, hnorm⟩

theorem s16c11_case5_core_of_natOmegaPlus {W : Type} [CommGroup W] {Lb Y : Subgroup (MulAut W)}
    (h : NatOmegaPlus Lb ⊤ ⊥ 4 2) (hLY : Lb ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (h27 : 3 ^ 3 ∣ Nat.card ↥Y)
    {𝒮 : Set (Subgroup (MulAut W))} (h𝒮 : ∀ A ∈ 𝒮, A = ⊥ ∨ A ∈ E3.aSet 2 Y)
    (h2 : IsPGroup 2 ↥(⨆ A ∈ 𝒮, A)) :
    ∃ P : Subgroup (MulAut W), P ≤ Y ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P ∧
      P ≤ Subgroup.normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut W)) : Set (MulAut W)) := by
  classical
  obtain ⟨K, hKf, hKfin, β, hKcard, hL⟩ := s16c11_case5_tensor h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK : Nat.card K = 4 := hKcard
  haveI : CharP K 2 := s16c11_case5_charP hK
  haveI : Finite W := Finite.of_equiv (VM K) β.symm
  have hWVM : ∀ x : VM K, x ^ 2 = 1 := fun x => s16c11_case5_sq_eq_one_VM K x
  have hW : ∀ w : W, w ^ 2 = 1 := by
    intro w
    apply β.injective
    rw [map_pow, map_one]
    exact hWVM (β w)
  let f : MulAut W →* MulAut (VM K) := (MulAut.congr β).toMonoidHom
  let g : MulAut (VM K) →* MulAut W := (MulAut.congr β.symm).toMonoidHom
  have hfg : f.comp g = MonoidHom.id (MulAut (VM K)) := s16c11_case5_congr_comp β
  have hgf : g.comp f = MonoidHom.id (MulAut W) := s16c11_case5_congr_comp' β
  let Z : Subgroup (MulAut (VM K)) := s16c11C5Scal K
  let Zt : Subgroup (MulAut W) := Z.map g
  let Y' : Subgroup (MulAut (VM K)) := Y.map f
  have hRY' : (rho (K := K)).range ≤ Y' := by
    rw [← hL]
    exact Subgroup.map_mono hLY
  have hYN' : Y' ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) := by
    have hh : Y.map (MulAut.congr β).toMonoidHom ≤
        Subgroup.normalizer ((Lb.map (MulAut.congr β).toMonoidHom :
          Subgroup (MulAut (VM K))) : Set (MulAut (VM K))) :=
      (map_le_normalizer_map_iff (MulAut.congr β) Y Lb).mpr hYN
    rw [hL] at hh
    exact hh
  have h27' : 3 ^ 3 ∣ Nat.card ↥Y' := by
    rw [show Nat.card ↥Y' = Nat.card ↥Y from
      Subgroup.card_map_of_injective (MulAut.congr β).injective]
    exact h27
  have hZ'model : Z ≤ Y' := s16c11_case5_scal_le_of_dvd hK hYN' h27'
  have hZY : Zt ≤ Y := by
    have hh := Subgroup.map_mono (f := g) hZ'model
    rw [Subgroup.map_map, hgf, Subgroup.map_id] at hh
    exact hh
  have hYZ : Y ≤ Subgroup.normalizer (Zt : Set (MulAut W)) := by
    refine (map_le_normalizer_map_iff (MulAut.congr β) Y Zt).mp ?_
    have hh : Y' ≤ Subgroup.normalizer (Z : Set (MulAut (VM K))) :=
      hYN'.trans (s16c11_case5_normalizer_le_normalizer_scal hK)
    rw [Subgroup.map_map, hfg, Subgroup.map_id]
    exact hh
  have hZtodd : ¬ 2 ∣ Nat.card ↥Zt := by
    have hcard : Nat.card ↥Zt = 3 := by
      change Nat.card ↥(Z.map g) = 3
      rw [Subgroup.card_map_of_injective (MulAut.congr β.symm).injective]
      exact s16c11_case5_card_scalB K hK
    rw [hcard]
    norm_num
  have hc : (⨆ A ∈ 𝒮, A) ≤ Subgroup.centralizer (Zt : Set (MulAut W)) := by
    refine iSup₂_le fun A hA => ?_
    rcases h𝒮 A hA with hb | hA2
    · rw [hb]
      exact bot_le
    · exact s16c11_le_centralizer_of_mem_aSet_two hW hA2 hZtodd (hA2.1.trans hYZ)
  exact s16c11_case5_core_transport hK β hL hLY hYN hZY h𝒮 h2 hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

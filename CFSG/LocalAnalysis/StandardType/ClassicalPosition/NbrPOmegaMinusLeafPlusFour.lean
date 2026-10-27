module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

private theorem nbrpmmx_stdSylow_eq_upperUnipotent {F : Type*} [Field F] :
    CFSG.Quasithin.SL2Sylow.stdSylow F = CFSG.Timmesfeld.upperUnipotent F := by
  ext g
  rw [CFSG.Quasithin.SL2Sylow.mem_stdSylow,
    CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by
      apply CFSG.Quasithin.SL2Sylow.ext_entries <;>
        simp [CFSG.Quasithin.SL2Sylow.upperElt_00, CFSG.Quasithin.SL2Sylow.upperElt_01,
          CFSG.Quasithin.SL2Sylow.upperElt_10, CFSG.Quasithin.SL2Sylow.upperElt_11,
          CFSG.Timmesfeld.RankOne.upperElt]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by
      apply CFSG.Quasithin.SL2Sylow.ext_entries <;>
        simp [CFSG.Quasithin.SL2Sylow.upperElt_00, CFSG.Quasithin.SL2Sylow.upperElt_01,
          CFSG.Quasithin.SL2Sylow.upperElt_10, CFSG.Quasithin.SL2Sylow.upperElt_11,
          CFSG.Timmesfeld.RankOne.upperElt]⟩

private theorem nbrpmmx_eq_top_of_stdSylow_le {F : Type*} [Field F]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hperf : commutator ↥A = ⊤)
    (hU : CFSG.Quasithin.SL2Sylow.stdSylow F ≤ A) : A = ⊤ := by
  haveI : Group.IsPerfect ↥A := ⟨hperf⟩
  by_cases hle : A ≤ CFSG.Quasithin.SL2Sylow.borel F
  · exfalso
    have hne1 : CFSG.Quasithin.SL2Sylow.upperElt (1 : F) ≠ 1 := by
      intro h
      have h0 : (1 : F) = 0 := by
        apply CFSG.Quasithin.SL2Sylow.upperElt_injective
        rw [h, CFSG.Quasithin.SL2Sylow.upperElt_zero]
      exact one_ne_zero h0
    haveI : Nontrivial ↥A :=
      (Subgroup.nontrivial_iff_exists_ne_one A).mpr
        ⟨CFSG.Quasithin.SL2Sylow.upperElt (1 : F),
          hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow 1), hne1⟩
    haveI : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥A inferInstance
  · obtain ⟨g, hgA, hgB⟩ := Set.not_subset.mp hle
    have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simpa [CFSG.Quasithin.SL2Sylow.mem_borel] using hgB
    have hlow : ∀ s : F, CFSG.Quasithin.SL2Sylow.lowerElt s ∈ A := by
      intro s
      have hconj := CFSG.Quasithin.SL2Sylow.conj_upperElt_conj_eq_lowerElt g hc
        (-(s / (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2))
      have ht : -((-(s / (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2)) *
          (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2) = s := by
        field_simp
      rw [ht] at hconj
      rw [← hconj]
      exact mul_mem (mul_mem (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _))
        (mul_mem (mul_mem hgA (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _)))
          (inv_mem hgA)))
        (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _))
    exact CFSG.Quasithin.SL2Sylow.eq_top_of_unitriangular_mem
      (fun t => hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow t)) hlow

private theorem nbrpmmx_eq_top_of_conj_stdSylow_le {F : Type*} [Field F]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hperf : commutator ↥A = ⊤)
    (v : Matrix.SpecialLinearGroup (Fin 2) F)
    (hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow F, v * x * v⁻¹ ∈ A) : A = ⊤ := by
  haveI : Group.IsPerfect ↥A := ⟨hperf⟩
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    MulAut.conj v⁻¹
  have hU1 : CFSG.Quasithin.SL2Sylow.stdSylow F ≤ A.map e.toMonoidHom := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨v * x * v⁻¹, hU x hx, ?_⟩
    show (MulAut.conj v⁻¹) (v * x * v⁻¹) = x
    rw [MulAut.conj_apply]
    group
  haveI : Group.IsPerfect ↥(A.map e.toMonoidHom) :=
    Group.IsPerfect.map (H := A) (f := e.toMonoidHom)
  have hmap : A.map e.toMonoidHom = ⊤ :=
    nbrpmmx_eq_top_of_stdSylow_le (A := A.map e.toMonoidHom)
      (Group.IsPerfect.commutator_eq_top (G := ↥(A.map e.toMonoidHom))) hU1
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map e.symm.toMonoidHom = A :=
    (Subgroup.map_symm_eq_iff_map_eq (H := ⊤) A (e := e)).mpr hmap
  rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom
    (EquivLike.surjective e.symm)] at htop
  exact htop.symm

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))


theorem nbrpmmx_plus_four (n f : ℕ) (hf : 1 ≤ f) (ι : (ggU .PSL 2 f).K →* UK n f)
    (hιcent : ∀ y, ι y ∈ Subgroup.center (UK n f) → y ∈ Subgroup.center (ggU .PSL 2 f).K)
    (β : Fin (ggU .PSL 2 f).D.rank → ℤ) (hβ : β ∈ (ggU .PSL 2 f).D.roots)
    (u : (ggU .PSL 2 f).K) (J' : Subgroup (UK n f)) (hperf : commutator ↥J' = ⊤)
    (hJι : J' ≤ ι.range)
    (hR : (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι ≤ J') :
    ι.range ≤ J' := by
  classical
  let H : Subgroup (ggU .PSL 2 f).K := J'.comap ι
  have hHdef : H = J'.comap ι := rfl
  have hmap : H.map ι = J' := by
    rw [hHdef, Subgroup.map_comap_eq, inf_eq_right.mpr hJι]
  have hcenter : Subgroup.center ((ggU .PSL 2 f).K) = ⊥ := by
    change Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = ⊥
    exact CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (GaloisField 2 f)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyc : y ∈ Subgroup.center ((ggU .PSL 2 f).K) :=
      hιcent y (by rw [hy]; exact Subgroup.one_mem _)
    rw [hcenter] at hyc
    exact Subgroup.mem_bot.mp hyc
  have hHperf : commutator ↥H = ⊤ := by
    have e : ↥H ≃* ↥(H.map ι) := Subgroup.equivMapOfInjective H ι hιinj
    haveI : Group.IsPerfect ↥(H.map ι) := by
      rw [hmap]
      exact ⟨hperf⟩
    haveI : Group.IsPerfect ↥H :=
      Group.IsPerfect.ofSurjective (f := (e.symm : ↥(H.map ι) →* ↥H))
        (EquivLike.surjective e.symm)
    exact Group.IsPerfect.commutator_eq_top (G := ↥H)
  have key : H = ⊤ := by
    let u' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) := u
    have hβ' :=
      CFSG.Timmesfeld.ARS.CaseOA.eq_or_eq_neg_of_mem_roots_SL2 (F := GaloisField 2 f) hβ
    rcases hβ' with hβpos | hβneg
    · have hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow (GaloisField 2 f),
          u' * x * u'⁻¹ ∈ H := by
        intro x hx
        have hxU : x ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
          rwa [← nbrpmmx_stdSylow_eq_upperUnipotent]
        have hroot : x ∈ (ggU .PSL 2 f).D.rootGroup β := by
          have hsingle : (ggU .PSL 2 f).D.rootGroup β =
              CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
            rw [hβpos]
            exact CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_single (GaloisField 2 f)
          rw [hsingle]
          exact hxU
        have hx' : u' * x * u'⁻¹ ∈ ((ggU .PSL 2 f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom := Subgroup.mem_map.mpr ⟨x, hroot, rfl⟩
        exact Subgroup.mem_comap.mpr (hR (Subgroup.mem_map.mpr ⟨_, hx', rfl⟩))
      exact nbrpmmx_eq_top_of_conj_stdSylow_le (A := H) hHperf u' hU
    · let w : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
        CFSG.Timmesfeld.ARS.NaturalModule.weylElt (GaloisField 2 f)
      have hw : w⁻¹ = w :=
        inv_eq_of_mul_eq_one_right CFSG.Timmesfeld.ARS.NaturalModule.weylElt_mul_self
      have hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow (GaloisField 2 f),
          (u' * w) * x * (u' * w)⁻¹ ∈ H := by
        intro x hx
        have hxU : x ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
          rwa [← nbrpmmx_stdSylow_eq_upperUnipotent]
        obtain ⟨t, rfl⟩ :=
          (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff (GaloisField 2 f)).mp hxU
        have hlow : CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t ∈
            CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 f) :=
          (CFSG.Timmesfeld.RankOne.mem_lowerUnipotent_iff (GaloisField 2 f)).mpr ⟨t, rfl⟩
        have hroot : CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t ∈
            (ggU .PSL 2 f).D.rootGroup β := by
          have hsingle : (ggU .PSL 2 f).D.rootGroup β =
              CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 f) := by
            rw [hβneg]
            exact CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_neg_single (GaloisField 2 f)
          rw [hsingle]
          exact hlow
        have hx' : u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ ∈
            ((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨_, hroot, rfl⟩
        have hmem : u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ ∈ H :=
          Subgroup.mem_comap.mpr (hR (Subgroup.mem_map.mpr ⟨_, hx', rfl⟩))
        have heq : (u' * w) * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t *
              (u' * w)⁻¹
            = u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ := by
          calc (u' * w) * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t * (u' * w)⁻¹
              = u' * (w * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t * w) *
                  u'⁻¹ := by
                rw [mul_inv_rev, hw]; group
            _ = u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ := by
                rw [CFSG.Timmesfeld.ARS.NaturalModule.weylElt_mul_upperElt_mul_weylElt t]
        rw [heq]
        exact hmem
      exact nbrpmmx_eq_top_of_conj_stdSylow_le (A := H) hHperf (u' * w) hU
  have hJ : J' = ι.range := by
    rw [← hmap, key, MonoidHom.range_eq_map]
  exact ge_of_eq hJ

end CFSG.StandardType.ClassicalPosition.NbrLeaf

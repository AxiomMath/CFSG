module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreLin
import CFSG.LocalAnalysis.ComponentClassification.GS82L34Omega

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL conjAut)

private theorem q2cLS_map_ggAutFixedSubgroup {R R' : Type*} [Group R] [Group R']
    (e : R ≃* R') (σ : MulAut R) :
    (ggAutFixedSubgroup σ).map e.toMonoidHom = fixSubgroup (MulAut.congr e σ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixSubgroup]
    have hy' : σ y = y := (mem_ggAutFixedSubgroup σ y).mp hy
    simp [MulAut.congr_apply, hy']
  · intro hx
    rw [mem_fixSubgroup] at hx
    have hx' : e (σ (e.symm x)) = x := by simpa [MulAut.congr_apply] using hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hx'

private theorem q2cLS_centerQuotEquiv {N : ℕ} {F : Type} [Field F] [Finite F]
    {g : GL (Fin N) F} {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    {C : Subgroup (GL (Fin N) F)}
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) F))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) F)
    (hJeq : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) F)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F))) :
    Nonempty (↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀) := by
  let φ : ↥C →* LargeEvenProj (LargeEvenSLGroup (Fin N) F) :=
    (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F)).comp (Subgroup.inclusion hCSL)
  let f : ↥C →* ↥J₀ := φ.codRestrict J₀ fun c => by
    rw [hJeq]
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCSL c,
      Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) F)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F)) := by rw [← hJeq]; exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) F), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    exact hyj
  have hperfC : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
  have hker : f.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hφ : φ c = 1 := congrArg Subtype.val hc
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) F) (Subgroup.inclusion hCSL c) = 1 at hφ
    have hc1 : Subgroup.inclusion hCSL c ∈
        (LargeEvenScalars (Fin N) F).subgroupOf (LargeEvenSLGroup (Fin N) F) :=
      (QuotientGroup.eq_one_iff
        (N := (LargeEvenScalars (Fin N) F).subgroupOf (LargeEvenSLGroup (Fin N) F))
        (Subgroup.inclusion hCSL c)).mp hφ
    have hc2 : (c : GL (Fin N) F) ∈ LargeEvenScalars (Fin N) F :=
      Subgroup.mem_subgroupOf.mp hc1
    have hcen : (c : GL (Fin N) F) ∈ Subgroup.center (GL (Fin N) F) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center (Fin N) F]
      exact hc2
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcen (d : GL (Fin N) F)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f hf hperfC hker

theorem q2cLS_split_component_unique {N p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (h4 : 4 ≤ Nat.card F) (hN : 2 ≤ N)
    {g : GL (Fin N) F} (hg : g ^ p = 1) (hu : TableB.linConjAut (Fin N) F g ≠ 1)
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hJ₀ : CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)))
    (huniq : ∀ J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F)),
      CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) → J' = J₀)
    {C : Subgroup (GL (Fin N) F)}
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) F))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) F)
    (hJeq : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) F)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F))) :
    ∃ a t : ℕ, 2 ≤ a ∧ 1 ≤ t ∧ t ≤ p - 1 ∧ N = a + t ∧
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin a) F)) := by
  have hpk : (p : F) ≠ 0 := by
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm
  let eR := TypeA.recipeEquiv N F
  let T : Subgroup (projectiveSL N F) := J₀.map eR.toMonoidHom
  have hσ : MulAut.congr eR (TableB.linConjAut (Fin N) F g) = conjAut N F g :=
    q1CentLin_congr_linConjAut g
  have hgrp : (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)).map eR.toMonoidHom =
      fixSubgroup (conjAut N F g) := by
    rw [q2cLS_map_ggAutFixedSubgroup eR (TableB.linConjAut (Fin N) F g), hσ]
  have hgrp' : (fixSubgroup (conjAut N F g)).map eR.symm.toMonoidHom =
      ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g) := by
    rw [← hgrp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [← hzy]
      simpa using hz
    · intro hx
      exact ⟨eR x, Subgroup.mem_map_of_mem _ hx, by simp⟩
  have hJ₀asm : CFSG.Assembly.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ₀
  have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJ₀asm eR.toMonoidHom eR.injective
  have hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N F g)) := by
    refine CFSG.Assembly.isComponentOf_iff_open.mp ?_
    rw [← hgrp]
    exact hmap
  have hgne : conjAut N F g ≠ 1 := by
    intro h1
    apply hu
    exact (MulAut.congr eR).injective (by rw [hσ, h1, map_one])
  have hTonly : ∀ Q : Subgroup (projectiveSL N F),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N F g)) → p ∣ Nat.card Q → Q = T := by
    intro Q hQ _
    have hQasm : CFSG.Assembly.IsComponentOf Q (fixSubgroup (conjAut N F g)) :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hQ
    have hback := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
      hQasm eR.symm.toMonoidHom eR.symm.injective
    have hback' : CFSG.Assembly.IsComponentOf (Q.map eR.symm.toMonoidHom)
        (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) := by
      rw [← hgrp']
      exact hback
    have heq := huniq _ (CFSG.Assembly.isComponentOf_iff_open.mp hback')
    have hmapid : (Q.map eR.symm.toMonoidHom).map eR.toMonoidHom = Q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        rw [← hzy]
        simpa using hz
      · intro hx
        exact ⟨eR.symm x, Subgroup.mem_map_of_mem _ hx, by simp⟩
    rw [← hmapid, heq]
  obtain ⟨a, ds, E, hEfld, hEfin, hEcard, h2a, hNa, hdsne, hdslen, hds1, ⟨eT⟩⟩ :=
    raLin_split_structure (K := F) hp hp2 hpk hpF hg hgne hT hTonly
  letI : Field E := hEfld
  letI : Fintype E := hEfin
  have hsumlen : ∀ l : List ℕ, (∀ x ∈ l, x = 1) → l.sum = l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons y ys ih =>
      simp only [List.sum_cons, List.length_cons]
      rw [hl y (by simp)]
      rw [ih (fun z hz => hl z (by simp [hz]))]
      omega
  have hsum : ds.sum = ds.length := hsumlen ds hds1
  refine ⟨a, ds.sum, h2a, ?_, ?_, hNa, ?_⟩
  · rw [hsum]
    exact List.length_pos_iff_ne_nil.mpr hdsne
  · rw [hsum]
    omega
  · obtain ⟨eCJ⟩ := q2cLS_centerQuotEquiv hC hCSL hJeq
    let eJ0T : ↥J₀ ≃* ↥T := Subgroup.equivMapOfInjective J₀ eR.toMonoidHom eR.injective
    have hcenter : (Subgroup.center ↥J₀).map eJ0T.toMonoidHom = Subgroup.center ↥T :=
      Subgroup.map_center_eq eJ0T
    let eQ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* (↥T ⧸ Subgroup.center ↥T) :=
      QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥T) eJ0T hcenter
    letI : Fintype F := Fintype.ofFinite F
    have hcardfin : Fintype.card E = Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard]
    let eEF : projectiveSL a E ≃* projectiveSL a F :=
      CFSG.ComponentClassification.GSThmB.L34OmegaAux.projectiveSLCongr
        (FiniteField.ringEquivOfCardEq (K := E) (K' := F) hcardfin)
    exact ⟨eCJ.trans (eQ.trans (eT.trans (eEF.trans (TypeA.recipeEquiv a F).symm)))⟩

theorem q2c_lin_split {N p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (h4 : 4 ≤ Nat.card F) (hN : 2 ≤ N)
    {g : GL (Fin N) F} (hg : g ^ p = 1) (hu : TableB.linConjAut (Fin N) F g ≠ 1)
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hJ₀ : CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)))
    (huniq : ∀ J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F)),
      CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) → J' = J₀) :
    ∃ a t : ℕ, 2 ≤ a ∧ 1 ≤ t ∧ t ≤ p - 1 ∧ N = a + t ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin a) F)) := by
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hN g J₀ hJ₀
  obtain ⟨a, t, ha, ht, htp, hNat, ⟨heC⟩⟩ :=
    q2cLS_split_component_unique hp hp2 hpF h4 hN hg hu hJ₀ huniq hC hCSL hJeq
  refine ⟨a, t, ha, ht, htp, hNat, ?_⟩
  let φ : ↥C →* LargeEvenProj (LargeEvenSLGroup (Fin N) F) :=
    (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F)).comp (Subgroup.inclusion hCSL)
  let f : ↥C →* ↥J₀ := φ.codRestrict J₀ fun c => by
    rw [hJeq]
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCSL c,
      Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) F)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) F)) := by rw [← hJeq]; exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) F), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    exact hyj
  have hperfC : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
  have hker : f.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hφ : φ c = 1 := congrArg Subtype.val hc
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) F) (Subgroup.inclusion hCSL c) = 1 at hφ
    have hc1 : Subgroup.inclusion hCSL c ∈
        (LargeEvenScalars (Fin N) F).subgroupOf (LargeEvenSLGroup (Fin N) F) :=
      (QuotientGroup.eq_one_iff
        (N := (LargeEvenScalars (Fin N) F).subgroupOf (LargeEvenSLGroup (Fin N) F))
        (Subgroup.inclusion hCSL c)).mp hφ
    have hc2 : (c : GL (Fin N) F) ∈ LargeEvenScalars (Fin N) F :=
      Subgroup.mem_subgroupOf.mp hc1
    have hcen : (c : GL (Fin N) F) ∈ Subgroup.center (GL (Fin N) F) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center (Fin N) F]
      exact hc2
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcen (d : GL (Fin N) F)
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperfC f hf hker
  have hc : Subgroup.center ↥C =
      ((QuotientGroup.mk' (Subgroup.center ↥J₀)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hf))
  exact ⟨e.symm.trans heC⟩

end CFSG.StandardType

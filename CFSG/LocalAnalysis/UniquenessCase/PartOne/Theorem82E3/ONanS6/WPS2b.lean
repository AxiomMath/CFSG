module

public import CFSG.GroupTheory.SolvableTransport
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXMovingPlaneKernel
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXPlaneComponentOrbitRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXMutualFourRoots

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem orbit_ncard_eq_one_or_six_le_of_tripleCover
    {P X : Type} [Group P] [Finite P] [Finite X] [MulAction P X]
    (hP : Group.IsPerfect P)
    (h3 : IsTripleCover (P ⧸ CFSG.Open.pCore 2 P) (alternatingGroup (Fin 6)))
    (x : X) :
    (MulAction.orbit P x).ncard = 1 ∨ 6 ≤ (MulAction.orbit P x).ncard := by
  classical
  let Z : Subgroup P := CFSG.Open.pCore 2 P
  let Pbar : Type := P ⧸ Z
  let eA : Pbar ⧸ Subgroup.center Pbar ≃* alternatingGroup (Fin 6) := Classical.choice h3.2
  let πbar : Pbar →* alternatingGroup (Fin 6) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Pbar))
  let π : P →* alternatingGroup (Fin 6) := πbar.comp (QuotientGroup.mk' Z)
  let L : Subgroup P := π.ker
  have hπbar_surj : Function.Surjective πbar := by
    intro a
    obtain ⟨y, rfl⟩ := eA.surjective a
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Pbar) y
    exact ⟨z, rfl⟩
  have hπ_surj : Function.Surjective π := by
    intro a
    obtain ⟨y, hy⟩ := hπbar_surj a
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact ⟨p, hy⟩
  have hπbar_ker : πbar.ker = Subgroup.center Pbar := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center Pbar)) y = 1 :=
        eA.injective (by simpa using h)
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center Pbar)) y = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h
      rw [h1, map_one]
  have hZL : Z ≤ L := by
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hz1 : (QuotientGroup.mk' Z) z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
    rw [hz1, map_one]
  have hLsolv : Group.IsSolvable ↥L := by
    let cL : ↥L →* ↥(Subgroup.center Pbar) :=
      { toFun := fun l =>
          ⟨(QuotientGroup.mk' Z) (l : P), by
            rw [← hπbar_ker, MonoidHom.mem_ker]
            have hl : π (l : P) = 1 := MonoidHom.mem_ker.mp l.2
            simpa only [π, MonoidHom.comp_apply] using hl⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
    have hcL_surj : Function.Surjective cL := by
      intro c
      obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective Z (c : Pbar)
      have hpL : p ∈ L := by
        rw [MonoidHom.mem_ker]
        change πbar ((QuotientGroup.mk' Z) p) = 1
        rw [hp]
        have hc : (c : Pbar) ∈ πbar.ker := by
          rw [hπbar_ker]
          exact c.2
        exact MonoidHom.mem_ker.mp hc
      exact ⟨⟨p, hpL⟩, Subtype.ext hp⟩
    have hcL_ker : MonoidHom.ker cL = Z.subgroupOf L := by
      ext l
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact (QuotientGroup.eq_one_iff _).mp (Subtype.ext_iff.mp h)
      · intro h
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
    have hcL_p : IsPGroup 2 (MonoidHom.ker cL) := by
      rw [hcL_ker]
      exact (pCore_isPGroup (p := 2) (G := P)).of_equiv (Subgroup.subgroupOfEquivOfLe hZL).symm
    have hcen : Group.IsSolvable ↥(Subgroup.center Pbar) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    haveI : Group.IsSolvable ↥(Subgroup.center Pbar) := hcen
    have hcenTop : Group.IsSolvable ↥(⊤ : Subgroup (Subgroup.center Pbar)) :=
      inferInstance
    have h := CFSG.GroupTheory.isSolvable_comap_of_isPGroup_ker cL hcL_surj
      (BQ := ⊤) hcenTop hcL_p
    rw [Subgroup.comap_top] at h
    have hLtop : Group.IsSolvable ↥(⊤ : Subgroup L) := h
    haveI : Group.IsSolvable ↥(⊤ : Subgroup L) := hLtop
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.topEquiv : ↥(⊤ : Subgroup L) ≃* L).symm).toMonoidHom)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup L) ≃* L).symm.injective
  let O : Set X := MulAction.orbit P x
  let ρ : P →* Equiv.Perm O := MulAction.toPermHom P O
  let Q : Subgroup (Equiv.Perm O) := ρ.range
  let K : Subgroup P := ρ.ker
  haveI : Group.IsPerfect P := hP
  have hQperf : Group.IsPerfect ↥Q := by
    have h := Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
    simpa [Q] using h
  have hdich : Q = ⊥ ∨ 360 ≤ Nat.card Q := by
    by_cases hKL : K ≤ L
    · right
      let hfac : P ⧸ K →* alternatingGroup (Fin 6) := QuotientGroup.lift K π hKL
      have hfac_surj : Function.Surjective hfac := by
        intro a
        obtain ⟨p, hp⟩ := hπ_surj a
        refine ⟨QuotientGroup.mk' K p, ?_⟩
        rw [← hp]
        simpa [hfac] using QuotientGroup.lift_mk K hKL p
      have h360 : 360 ≤ Nat.card (P ⧸ K) := by
        have hle := Nat.card_le_card_of_surjective hfac hfac_surj
        have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 :=
          CFSG.QuasithinUnique.Setup.X3.card_of_equiv_alt6 (MulEquiv.refl _)
        rwa [hA6] at hle
      have hcard : Nat.card Q = Nat.card (P ⧸ K) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
      rwa [hcard]
    · left
      have hsimpleP : IsSimpleGroup (P ⧸ L) := by
        haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
          alternatingGroup.isSimpleGroup (by norm_num)
        exact MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj)
      have hKmap : K.map (QuotientGroup.mk' L) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' L)) with h | h
        · exfalso
          apply hKL
          intro k hk
          have hmem : QuotientGroup.mk' L k ∈ (⊥ : Subgroup (P ⧸ L)) := by
            rw [← h]
            exact ⟨k, hk, rfl⟩
          rw [Subgroup.mem_bot] at hmem
          exact (QuotientGroup.eq_one_iff _).mp hmem
        · exact h
      have hKLtop : K ⊔ L = ⊤ := by
        have h1 : (K.map (QuotientGroup.mk' L)).comap (QuotientGroup.mk' L) = L ⊔ K :=
          QuotientGroup.comap_map_mk' L K
        rw [sup_comm]
        rw [← h1, hKmap, Subgroup.comap_top]
      have hPKsolv : Group.IsSolvable (P ⧸ K) := by
        let f : ↥L →* P ⧸ K := (QuotientGroup.mk' K).comp L.subtype
        have hf : Function.Surjective f := by
          intro y
          obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective K y
          have hp' : p ∈ K ⊔ L := by rw [hKLtop]; exact Subgroup.mem_top p
          haveI : L.Normal := MonoidHom.normal_ker π
          rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := L)).mp hp' with
            ⟨k, hk, l, hl, hkl⟩
          refine ⟨⟨l, hl⟩, ?_⟩
          rw [← hp, ← hkl]
          change QuotientGroup.mk' K l = QuotientGroup.mk' K (k * l)
          rw [map_mul, show QuotientGroup.mk' K k = 1 from (QuotientGroup.eq_one_iff _).mpr hk,
            one_mul]
        exact Group.isSolvable_of_surjective (f := f) hf
      have hQsolv : Group.IsSolvable ↥Q := by
        haveI : Group.IsSolvable (P ⧸ K) := hPKsolv
        exact Group.isSolvable_of_surjective
          (f := (QuotientGroup.quotientKerEquivRange ρ).toMonoidHom)
          (QuotientGroup.quotientKerEquivRange ρ).surjective
      by_contra hQne
      haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
      exact Group.IsPerfect.not_isSolvable ↥Q hQsolv
  rcases hdich with hQbot | hQbig
  · left
    have hρ1 : ρ = 1 := MonoidHom.range_eq_bot_iff.mp hQbot
    have horbit : MulAction.orbit P x = {x} := by
      ext y
      constructor
      · rintro ⟨p, rfl⟩
        have hp : p • (⟨x, MulAction.mem_orbit_self x⟩ : O) = ⟨x, MulAction.mem_orbit_self x⟩ := by
          change (ρ p) ⟨x, MulAction.mem_orbit_self x⟩ = ⟨x, MulAction.mem_orbit_self x⟩
          rw [hρ1]
          rfl
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hp)
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        simpa [hy] using MulAction.mem_orbit_self x
    rw [horbit, Set.ncard_singleton]
  · right
    change 6 ≤ O.ncard
    have hQle : Nat.card Q ≤ Nat.card (Equiv.Perm O) := Subgroup.card_le_card_group Q
    have hperm : Nat.card (Equiv.Perm O) = (Nat.card O).factorial := Nat.card_perm
    have hO : Nat.card O = O.ncard := Nat.card_coe_set_eq O
    have h360 : 360 ≤ O.ncard.factorial := by
      calc 360 ≤ Nat.card Q := hQbig
        _ ≤ Nat.card (Equiv.Perm O) := hQle
        _ = (Nat.card O).factorial := hperm
        _ = O.ncard.factorial := by rw [hO]
    by_contra hlt
    have h5 : O.ncard ≤ 5 := by omega
    have hle : O.ncard.factorial ≤ (5).factorial := Nat.factorial_le h5
    norm_num at hle
    omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem perfectCoreL_le_normalizer_iff_orbit_ncard_eq_one
    (c : Ctx82E3 D) (a : G) (J : Subgroup G) :
    perfectCoreL c a ≤ Subgroup.normalizer (J : Set G) ↔
      (orbitConjugates (perfectCoreL c a) J).ncard = 1 := by
  have hmem : J ∈ orbitConjugates (perfectCoreL c a) J :=
    ⟨1, one_mem _, by simp [CFSG.LocalAnalysis.GorensteinLyons.cfsgConjugate_one]⟩
  constructor
  · intro h
    rw [Set.ncard_eq_one]
    refine ⟨J, ?_⟩
    ext K
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (CFSG.LocalAnalysis.GorensteinLyons.conjugate_eq_self_iff).mpr (h hi)
    · intro hK
      rw [hK]
      exact hmem
  · intro h
    intro i hi
    have hKi : CFSG.conjugate J i ∈ orbitConjugates (perfectCoreL c a) J := ⟨i, hi, rfl⟩
    rcases Set.ncard_eq_one.mp h with ⟨K, hK⟩
    have hJK : J = K := by
      rw [hK] at hmem
      exact Set.mem_singleton_iff.mp hmem
    have hKiK : CFSG.conjugate J i = K := by
      rw [hK] at hKi
      exact Set.mem_singleton_iff.mp hKi
    exact (CFSG.LocalAnalysis.GorensteinLyons.conjugate_eq_self_iff).mp (hKiK.trans hJK.symm)

theorem perfectCoreL_orbit_card
    (c : Ctx82E3 D) {a : G}
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
      (alternatingGroup (Fin 6)))
    (J : Subgroup G) :
    (orbitConjugates (perfectCoreL c a) J).ncard = 1 ∨
      6 ≤ (orbitConjugates (perfectCoreL c a) J).ncard := by
  letI : MulAction ↥(perfectCoreL c a) (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp (perfectCoreL c a).subtype)
  have hsmul : ∀ (b : ↥(perfectCoreL c a)) (M : Subgroup G),
      b • M = M.map (MulAut.conj (b : G)).toMonoidHom := fun b M => by
    change (MulAut.conj (b : G)) • M = _
    rw [Subgroup.pointwise_smul_def]
    rfl
  have horbit : MulAction.orbit ↥(perfectCoreL c a) J =
      orbitConjugates (perfectCoreL c a) J := by
    ext K
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(p : G)⁻¹, inv_mem p.2, ?_⟩
      change p • J = CFSG.conjugate J ((p : G)⁻¹)
      rw [hsmul, CFSG.conjugate]
      simp
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b⁻¹, inv_mem hb⟩, ?_⟩
      change (⟨b⁻¹, inv_mem hb⟩ : ↥(perfectCoreL c a)) • J = CFSG.conjugate J b
      rw [hsmul, CFSG.conjugate]
  have h := orbit_ncard_eq_one_or_six_le_of_tripleCover
    (P := ↥(perfectCoreL c a)) (X := Subgroup G) (perfectCoreL_isPerfect c a) hP2 J
  rwa [horbit] at h

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

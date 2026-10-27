module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24Hbar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.SimpleSection

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14 CFSG.Blueprint CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_sup_theta
    {A Y : Subgroup G} [(ker148 A Y).Normal] {J : Subgroup G} (hJY : J ≤ Y)
    (e : ↥(img148 A Y J) ≃* NativeSporadic.M24)
    {a : G} {La : Subgroup G} (hLa : La ∈ thetaComponentsAt 3 a)
    (eLa : Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* NativeSporadic.J2))
    {R : Subgroup G} (hRJ : R ≤ J) (hRC : R ≤ Subgroup.centralizer ({a} : Set G))
    (hRsub : R ≤ La ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (himg : img148 A Y R = img148 A Y J) : False := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set T : Subgroup ↥C := aschbacherSolvableCore 3 ↥C with hT
  have hTsolv : Group.IsSolvable T :=
    (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).1
  haveI : T.Normal := inferInstance
  obtain ⟨L', hL', hLaeq0⟩ := hLa
  have hLaeq : L'.map C.subtype = La := hLaeq0
  set K : Subgroup ↥L' := aschbacherSolvableCore 3 ↥L' with hK
  have hKT : K.map L'.subtype ≤ T := by
    have h := aschbacherSolvableCore_eq_subgroupOf (p := 3) (H := ↥C) Nat.prime_three hL'.2.1
    rintro _ ⟨k, hk, rfl⟩
    rw [hK, h] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  haveI : IsSimpleGroup NativeSporadic.M24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
  have hM24ns : ¬ Group.IsSolvable NativeSporadic.M24 := by
    intro hsol
    have hc := (IsSimpleGroup.comm_iff_isSolvable (G := NativeSporadic.M24)).2 hsol
    have h := hc CFSG.Sporadic.Mathieu.m24a CFSG.Sporadic.Mathieu.m24b
    have hne : ¬ (CFSG.Sporadic.Mathieu.m24a * CFSG.Sporadic.Mathieu.m24b =
        CFSG.Sporadic.Mathieu.m24b * CFSG.Sporadic.Mathieu.m24a) := by
      decide +kernel
    exact hne h
  have hRYA : R ≤ Y ⊔ A := hRJ.trans (hJY.trans le_sup_left)
  set R' : Subgroup ↥C := R.subgroupOf C with hR'
  have hR'le : R' ≤ L' ⊔ T := by
    intro x hx
    have hxR : (x : G) ∈ R := hx
    have h1 : (x : G) ∈ La ⊔ inSubgroup (aschbacherSolvableCore 3) C := hRsub hxR
    have e1 : La ⊔ inSubgroup (aschbacherSolvableCore 3) C = (L' ⊔ T).map C.subtype := by
      rw [Subgroup.map_sup, hLaeq]; rfl
    rw [e1] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let ψR : ↥R →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hRYA)
  have hψrange : ψR.range = img148 A Y J := (range_eq_img148 hRYA).trans himg
  let φ0 : ↥R →* ↥(img148 A Y J) :=
    ψR.codRestrict (img148 A Y J) fun p => hψrange ▸ ⟨p, rfl⟩
  have hφ0 : Function.Surjective φ0 := by
    rintro ⟨y, hy⟩
    rw [← hψrange] at hy
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  let eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRC
  let φ : ↥R' →* NativeSporadic.M24 := (e.toMonoidHom.comp φ0).comp eR.toMonoidHom
  have hφ : Function.Surjective φ := e.surjective.comp (hφ0.comp eR.surjective)
  have hcardL : Nat.card (↥L' ⧸ K) = 604800 := by
    obtain ⟨φJ⟩ := eLa
    let eL : ↥L' ≃* ↥La :=
      (L'.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hLaeq)
    have hmap : K.map eL.toMonoidHom = aschbacherSolvableCore 3 ↥La :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL
    let eQ : ↥L' ⧸ K ≃* ↥La ⧸ aschbacherSolvableCore 3 ↥La := QuotientGroup.congr K _ eL hmap
    rw [Nat.card_congr (eQ.trans φJ).toEquiv,
      Nat.card_congr CFSG.Sporadic.J2.nativeEquiv.toEquiv, CFSG.Sporadic.J2.card_J]
  have hle := card_le_of_simple_section T hTsolv L' K hKT hM24ns R' hR'le φ hφ
  rw [CFSG.Sporadic.Mathieu.card_M24, hcardL] at hle
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

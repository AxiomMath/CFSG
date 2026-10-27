module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoCoverKernel
public import CFSG.GroupTheory.ElementaryCyclicProduct
public import CFSG.GroupTheory.QuasisimpleAutQuotient
public import CFSG.GroupTheory.PowMemSupOfPGroup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import Certificates.Certificate41501

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem bstar_le_normalizer_j (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Bs ≤ Subgroup.normalizer (J : Set G) := by
  have hpre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  have hD : D ≤ Bs := hpre.1.trans hS.1.1.2.1.1
  have hEA : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val
      (hEA.1.is_comm.comm (⟨d, hD hd⟩ : Bs) ⟨b, hb⟩)
  intro b hb
  have hnC : b ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_centralizer (hN hb) (hBsD hb)
  rw [hpre.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le (S := Subgroup.zpowers b)
    (fun g hg => map_conj_largeEvenLayer_le ((Subgroup.zpowers_le.mpr hnC) hg))
    (Subgroup.mem_zpowers b)

theorem exists_original_normalizer_lift (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {j₀ : G} (hj₀ : j₀ ∈ J)
    (hA : L.normalizerMonoidHom ⟨j₀, Subgroup.le_normalizer
        ((hS.1.1.2.2.1.2.2.2.2.2.1.1 hj₀).1)⟩ ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut L))) :
    ∃ j ∈ J, ∃ hjB : j ∈ Subgroup.normalizer (Bs : Set G),
      ∃ hjL : j ∈ Subgroup.normalizer (L : Set G),
        L.normalizerMonoidHom ⟨j, hjL⟩ =
          L.normalizerMonoidHom ⟨j₀, Subgroup.le_normalizer
            ((hS.1.1.2.2.1.2.2.2.2.2.1.1 hj₀).1)⟩ := by
  letI : Fact p.Prime := ⟨hp⟩
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hBJ : Bs ≤ Subgroup.normalizer (J : Set G) := bstar_le_normalizer_j hS hN
  let Y : Subgroup G := Bs ⊔ J
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hN (hJL.trans Subgroup.le_normalizer)
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) := sup_le hBJ Subgroup.le_normalizer
  let B₀ : Subgroup Y := Bs.subgroupOf Y
  let J₀ : Subgroup Y := J.subgroupOf Y
  let ρ : Y →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  let C : Subgroup Y := ρ.ker
  have hCeq : C = (Subgroup.centralizer (L : Set G)).subgroupOf Y :=
    quasisimpleActionKernel_eq_centralizer Y L hYN
  letI : J₀.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_right : J ≤ Y)).mpr hYJ
  letI : C.Normal := inferInstance
  letI : ((C ⊓ J₀).subgroupOf C).Normal := inferInstance
  have hNcen : (C ⊓ J₀).subgroupOf C ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    apply Subtype.ext
    have hzJ : (((z : C) : Y) : G) ∈ J := hz.2
    have hcC : (c : G) ∈ Subgroup.centralizer (L : Set G) := by
      have hc : (c : Y) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf Y := by
        rw [← hCeq]
        exact c.property
      exact Subgroup.mem_subgroupOf.mp hc
    exact (Subgroup.mem_centralizer_iff.mp hcC _ (hJL hzJ)).symm
  have hBY : IsElemAbelian p B₀ := hS.1.1.2.1.2.1.subgroupOf Y
  have hYQ : IsPGroup p (Y ⧸ J₀) := isPGroup_quotient_sup_left hS.1.1.2.1.2.1.isPGroup
  have hCQ : IsPGroup p (C ⧸ (C ⊓ J₀).subgroupOf C) := by
    let f : C →* Y ⧸ J₀ := (QuotientGroup.mk' J₀).comp C.subtype
    have hker : f.ker = (C ⊓ J₀).subgroupOf C := by
      ext c
      change ((c : Y) : Y ⧸ J₀) = 1 ↔
        (c : Y) ∈ C ⊓ J₀
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_inf]
      exact ⟨fun hc => ⟨c.property, hc⟩, fun hc => hc.2⟩
    exact hYQ.of_injective
      (QuotientGroup.lift ((C ⊓ J₀).subgroupOf C) f hker.symm.le)
      ((QuotientGroup.injective_lift_iff _ f hker.symm.le).2 hker.symm)
  let P : Sylow p C := Classical.choice inferInstance
  let Pg : Subgroup Y := (P : Subgroup C).map C.subtype
  have hPnormal : (P : Subgroup C).Normal :=
    (CFSG.RankThree.PGroups.sylow_normal_of_le_center_of_isPGroup_quotient hp hNcen hCQ P).1
  have hPchar : (P : Subgroup C).Characteristic := Sylow.characteristic_of_normal P hPnormal
  have hPgC : Pg ≤ C := Subgroup.map_subtype_le _
  have hPgsub : Pg.subgroupOf C = (P : Subgroup C) :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hPgchar : (Pg.subgroupOf C).Characteristic := hPgsub ▸ hPchar
  have hBPN : B₀ ≤ Subgroup.normalizer (Pg : Set Y) :=
    (le_top : B₀ ≤ ⊤).trans
      (Subgroup.le_normalizer_of_normal.trans
        (normalizer_le_normalizer_of_characteristic hPgC hPgchar))
  have hPcyc : IsCyclic Pg := by
    let P_G : Subgroup G := Pg.map Y.subtype
    have hP_GC : P_G ≤ Subgroup.centralizer (L : Set G) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzC : z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf Y := by
        rw [← hCeq]
        exact hPgC hz
      exact Subgroup.mem_subgroupOf.mp hzC
    have hcyc : IsCyclic P_G := hSS.2.2.2.2 P_G hP_GC
      ((P.isPGroup'.map C.subtype).map Y.subtype)
    letI : IsCyclic P_G := hcyc
    exact isCyclic_of_injective
      (Pg.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom
      (Pg.equivMapOfInjective Y.subtype Y.subtype_injective).injective
  have hxB : x ∈ Bs := hS.1.1.2.1.1 hSS.2.1
  let xY : Y := ⟨x, (le_sup_left : Bs ≤ Y) hxB⟩
  have hxC : xY ∈ C := by
    rw [hCeq]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSS.2.2.2.1.1 hl)
  have hxpow : xY ^ p = 1 := Subtype.ext (hS.1.1.2.1.2.1.2 x hxB)
  have hxne : xY ≠ 1 := fun h => hSS.2.2.1 (congrArg Subtype.val h)
  have hxP : xY ∈ Pg := by
    have hxc : (⟨xY, hxC⟩ : C) ^ p = 1 := Subtype.ext hxpow
    have hxGp : IsPGroup p (Subgroup.zpowers (⟨xY, hxC⟩ : C)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime hxc
          (fun h => hxne (congrArg Subtype.val h))]
        simp)
    obtain ⟨Q, hQ⟩ := hxGp.exists_le_sylow
    letI : Unique (Sylow p C) := Sylow.unique_of_normal P hPnormal
    have hQP : Q = P := Subsingleton.elim _ _
    exact ⟨⟨xY, hxC⟩, hQP ▸ hQ (Subgroup.mem_zpowers _), rfl⟩
  have hOmega : ∀ z ∈ Pg, z ^ p = 1 → z ∈ B₀ := by
    intro z hz hzpow
    letI := hPcyc
    have hzX : z ∈ Subgroup.zpowers xY :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245.mem_of_pow_eq_one_of_cyclic hp
        (Subgroup.zpowers_le.mpr hxP) (by rw [Nat.card_zpowers, orderOf_eq_prime hxpow hxne])
        hz hzpow
    exact (Subgroup.zpowers_le.mpr (show xY ∈ B₀ from hxB)) hzX
  letI : CFSG.IsElementaryAbelian p B₀ := hBY.isElementaryAbelian
  have hBchar : (B₀.subgroupOf (B₀ ⊔ Pg)).Characteristic :=
    characteristic_subgroupOf_sup_of_isElementaryAbelian_isCyclic hp hp2 hPcyc
      (P.isPGroup'.map C.subtype) hBPN hOmega
  have hρB : (ρ.comp B₀.subtype).range = (ggGamma L hN).range := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, b.property⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨⟨b, (le_sup_left : Bs ≤ Y) b.property⟩, b.property⟩, rfl⟩
  let jY : Y := ⟨j₀, (le_sup_right : J ≤ Y) hj₀⟩
  have hjA : ρ jY ∈ Subgroup.normalizer ((ρ.comp B₀.subtype).range : Set (MulAut L)) := by
    rw [hρB]
    exact hA
  obtain ⟨j, hjJ, hjB, hjρ⟩ := central_quotient_normalizer_lift ρ hBY inferInstance
    inferInstance hNcen hCQ P rfl hBchar (show jY ∈ J₀ from hj₀) hjA
  have hjBG : (j : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact (Subgroup.mem_normalizer_iff.mp hjB ⟨b, (le_sup_left : Bs ≤ Y) hb⟩).mp hb
    · intro hb
      have hbY : b ∈ Y := by
        have hcY : (j : G) * b * (j : G)⁻¹ ∈ Y := (le_sup_left : Bs ≤ Y) hb
        have h := Y.mul_mem (Y.mul_mem (Y.inv_mem j.property) hcY) j.property
        have heq : (j : G)⁻¹ * ((j : G) * b * (j : G)⁻¹) * j = b := by group
        rwa [heq] at h
      exact (Subgroup.mem_normalizer_iff.mp hjB ⟨b, hbY⟩).mpr hb
  exact ⟨j, hjJ, hjBG, hYN j.property, hjρ⟩

end CFSG.StandardType.QTwoCav

end

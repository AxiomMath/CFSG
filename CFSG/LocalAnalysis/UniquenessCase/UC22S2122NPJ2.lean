module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPJ2A
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev uc22s2122npTbar (D : Data G) : Subgroup (Bar2 D.M) := barImage D.M D.T

abbrev uc22s2122npLbar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 D.M) := barImage D.M L

abbrev uc22s2122npKbar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 D.M) :=
  barImage D.M (conjClosure D.M L)

abbrev uc22s2122npQbar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 D.M) :=
  uc22s2122npTbar D ⊓ uc22s2122npKbar D L

abbrev uc22s2122npNbar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 D.M) :=
  Subgroup.normalizer (uc22s2122npQbar D L) ⊓ uc22s2122npKbar D L

abbrev uc22s2122npQNbar (D : Data G) (L : Subgroup G) : Subgroup (uc22s2122npNbar D L) :=
  (uc22s2122npQbar D L).subgroupOf (uc22s2122npNbar D L)

instance uc22s2122npQNbarNormal (D : Data G) (L : Subgroup G) :
    (uc22s2122npQNbar D L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show uc22s2122npQbar D L ≤ uc22s2122npNbar D L from
      le_inf Subgroup.le_normalizer inf_le_right)).2 inf_le_left

theorem uc22s2122np_Kbar_eq_sup (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hK : conjClosure D.M L = L ⊔ L') :
    uc22s2122npKbar D L = uc22s2122npLbar D L ⊔ barImage D.M L' := by
  simpa only [uc22s2122npKbar, uc22s2122npLbar] using
    uc22s2122np_barImage_conjClosure_eq_sup hL hL' hK

theorem uc22s2122np_Kbar_normal (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M) :
    (uc22s2122npKbar D L).Normal := by
  simpa only [uc22s2122npKbar] using
    uc22s2122np_barImage_conjClosure_normal (M := D.M) (L := L) hL

theorem uc22s2122np_card_Kbar (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card (uc22s2122npKbar D L) = 175560 * 175560 := by
  simpa only [uc22s2122npKbar] using
    uc22s2122np_card_barImage_conjClosure hL hL' hne hJ hJ' hK

theorem uc22s2122np_card_Qbar (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card (uc22s2122npQbar D L) = 64 := by
  simpa only [uc22s2122npQbar, uc22s2122npTbar, uc22s2122npKbar] using
    uc22s2122np_card_inf_barImage_T (D := D) hL hL' hne hJ hJ' hK

theorem uc22s2122np_card_Nbar (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card (uc22s2122npNbar D L) = 168 * 168 := by
  have hQbK : uc22s2122npQbar D L ≤ uc22s2122npKbar D L := inf_le_right
  have hNk : Nat.card (Subgroup.normalizer
      ((uc22s2122npQbar D L).subgroupOf (uc22s2122npKbar D L) :
        Set (uc22s2122npKbar D L))) = 168 * 168 := by
    simpa only [uc22s2122npQbar, uc22s2122npTbar, uc22s2122npKbar] using
      uc22s2122np_card_normalizer_inf_barImage_T (D := D) hL hL' hne hJ hJ' hK
  have hEq : uc22s2122npNbar D L =
      (Subgroup.normalizer ((uc22s2122npQbar D L).subgroupOf
        (uc22s2122npKbar D L) : Set (uc22s2122npKbar D L))).map
          (uc22s2122npKbar D L).subtype := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQbK, Subgroup.subgroupOf_map_subtype]
  rw [hEq, Subgroup.card_map_of_injective (uc22s2122npKbar D L).subtype_injective]
  exact hNk

theorem uc22s2122np_card_QNbar (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card (uc22s2122npQNbar D L) = 64 := by
  rw [show Nat.card (uc22s2122npQNbar D L) = Nat.card (uc22s2122npQbar D L) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show uc22s2122npQbar D L ≤
      uc22s2122npNbar D L from le_inf Subgroup.le_normalizer inf_le_right)).toEquiv]
  exact uc22s2122np_card_Qbar D hL hL' hne hJ hJ' hK

theorem uc22s2122np_Tbar_le_normalizer_Nbar (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    uc22s2122npTbar D ≤
      Subgroup.normalizer (uc22s2122npNbar D L : Set (Bar2 D.M)) := by
  have hNK_top : (⊤ : Subgroup (Bar2 D.M)) ≤
      Subgroup.normalizer (uc22s2122npKbar D L : Set (Bar2 D.M)) := by
    haveI : (uc22s2122npKbar D L).Normal := uc22s2122np_Kbar_normal D hL
    exact Subgroup.le_normalizer_of_normal (H := uc22s2122npKbar D L) (K := ⊤)
  have hT_le_NQ : uc22s2122npTbar D ≤
      Subgroup.normalizer (uc22s2122npQbar D L : Set (Bar2 D.M)) := by
    intro t ht
    exact uc22s2122np_mem_normalizer_inf (Subgroup.le_normalizer ht)
      (hNK_top (Subgroup.mem_top t))
  intro t ht
  have h1 := uc22s2122np_normalizer_le_normalizer_normalizer (hT_le_NQ ht)
  have h2 := hNK_top (Subgroup.mem_top t)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    (H := Subgroup.normalizer (uc22s2122npQbar D L : Set (Bar2 D.M)))
    (K := uc22s2122npKbar D L) (Subgroup.mem_inf.2 ⟨h1, h2⟩)

theorem uc22s2122np_mem_Nbar (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') {b : G} (hbM : b ∈ D.M)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbK : b ∈ conjClosure D.M L) :
    uc22p21cPi D.M ⟨b, hbM⟩ ∈ uc22s2122npNbar D L := by
  have hbKb : uc22p21cPi D.M ⟨b, hbM⟩ ∈ uc22s2122npKbar D L := by
    rw [show uc22s2122npKbar D L = barImage D.M (conjClosure D.M L) from rfl]
    exact uc22p21c_mem_barImage.2 ⟨⟨b, hbM⟩, hbK, rfl⟩
  have hb_norm_Tb : uc22p21cPi D.M ⟨b, hbM⟩ ∈
      Subgroup.normalizer (uc22s2122npTbar D : Set (Bar2 D.M)) := by
    have hbTsub : (⟨b, hbM⟩ : ↥D.M) ∈
        Subgroup.normalizer ((D.T.subgroupOf D.M) : Set ↥D.M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq D.sylowM.le]
      exact Subgroup.mem_subgroupOf.2 hbT
    have h := Subgroup.le_normalizer_map (H := D.T.subgroupOf D.M)
      (f := uc22p21cPi D.M) (Subgroup.mem_map_of_mem (uc22p21cPi D.M) hbTsub)
    simpa only [uc22s2122npTbar, barImage] using h
  have hNK_top : (⊤ : Subgroup (Bar2 D.M)) ≤
      Subgroup.normalizer (uc22s2122npKbar D L : Set (Bar2 D.M)) := by
    haveI : (uc22s2122npKbar D L).Normal := uc22s2122np_Kbar_normal D hL
    exact Subgroup.le_normalizer_of_normal (H := uc22s2122npKbar D L) (K := ⊤)
  have hb_norm_Qb : uc22p21cPi D.M ⟨b, hbM⟩ ∈
      Subgroup.normalizer (uc22s2122npQbar D L : Set (Bar2 D.M)) :=
    uc22s2122np_mem_normalizer_inf hb_norm_Tb (hNK_top (Subgroup.mem_top _))
  exact Subgroup.mem_inf.2 ⟨hb_norm_Qb, hbKb⟩

theorem uc22s2122np_Tbar_le_normalizer_Rm (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (P : Sylow 7 (uc22s2122npNbar D L ⧸ uc22s2122npQNbar D L))
    (hPnormal : (P : Subgroup (uc22s2122npNbar D L ⧸ uc22s2122npQNbar D L)).Normal)
    {R : Subgroup (uc22s2122npNbar D L)}
    (hR : R = Subgroup.comap (QuotientGroup.mk' (uc22s2122npQNbar D L))
      (P : Subgroup (uc22s2122npNbar D L ⧸ uc22s2122npQNbar D L))) :
    uc22s2122npTbar D ≤ Subgroup.normalizer
      ((R.map (uc22s2122npNbar D L).subtype : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
  have hT_le_NNb : uc22s2122npTbar D ≤
      Subgroup.normalizer (uc22s2122npNbar D L : Set (Bar2 D.M)) :=
    uc22s2122np_Tbar_le_normalizer_Nbar D hL
  have hNK_top : (⊤ : Subgroup (Bar2 D.M)) ≤
      Subgroup.normalizer (uc22s2122npKbar D L : Set (Bar2 D.M)) := by
    haveI : (uc22s2122npKbar D L).Normal := uc22s2122np_Kbar_normal D hL
    exact Subgroup.le_normalizer_of_normal (H := uc22s2122npKbar D L) (K := ⊤)
  have hT_le_NQb : uc22s2122npTbar D ≤
      Subgroup.normalizer (uc22s2122npQbar D L : Set (Bar2 D.M)) := by
    intro t ht
    exact uc22s2122np_mem_normalizer_inf (Subgroup.le_normalizer ht)
      (hNK_top (Subgroup.mem_top t))
  intro t ht
  have htN : t ∈ Subgroup.normalizer (uc22s2122npNbar D L : Set (Bar2 D.M)) :=
    hT_le_NNb ht
  have htQ : t ∈ Subgroup.normalizer (uc22s2122npQbar D L : Set (Bar2 D.M)) :=
    hT_le_NQb ht
  let ψ : MulAut (uc22s2122npNbar D L) :=
    Subgroup.normalizerMonoidHom (uc22s2122npNbar D L) ⟨t, htN⟩
  have hQinv : Subgroup.map ψ.toMonoidHom (uc22s2122npQNbar D L) =
      uc22s2122npQNbar D L :=
    uc22s2122np_map_normalizerMonoidHom_subgroupOf_eq
      (show uc22s2122npQbar D L ≤ uc22s2122npNbar D L from
        le_inf Subgroup.le_normalizer inf_le_right) htN htQ
  have hRinv : Subgroup.map ψ.toMonoidHom R = R := by
    rw [hR]
    exact uc22s2122np_map_comap_of_sylow_normal (Q := uc22s2122npQNbar D L) P hPnormal ψ hQinv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj t).toMonoidHom
    (Subgroup.map (uc22s2122npNbar D L).subtype R) =
      Subgroup.map (uc22s2122npNbar D L).subtype R
  have hcomp : (MulAut.conj t).toMonoidHom.comp (uc22s2122npNbar D L).subtype =
      (uc22s2122npNbar D L).subtype.comp ψ.toMonoidHom := by
    ext x
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe (uc22s2122npNbar D L) ⟨t, htN⟩ x).symm
  rw [Subgroup.map_map R (MulAut.conj t).toMonoidHom (uc22s2122npNbar D L).subtype,
    hcomp, ← Subgroup.map_map R (uc22s2122npNbar D L).subtype ψ.toMonoidHom, hRinv]

theorem uc22s2122np_Qbar_le_Rm (D : Data G) {L : Subgroup G}
    (P : Sylow 7 (uc22s2122npNbar D L ⧸ uc22s2122npQNbar D L))
    {R : Subgroup (uc22s2122npNbar D L)}
    (hR : R = Subgroup.comap (QuotientGroup.mk' (uc22s2122npQNbar D L))
      (P : Subgroup (uc22s2122npNbar D L ⧸ uc22s2122npQNbar D L))) :
    uc22s2122npQbar D L ≤ R.map (uc22s2122npNbar D L).subtype := by
  have hQNb_le_R : uc22s2122npQNbar D L ≤ R := by
    intro x hx
    rw [hR, Subgroup.mem_comap]
    have hx1 : (QuotientGroup.mk' (uc22s2122npQNbar D L)) x = 1 :=
      (QuotientGroup.eq_one_iff _).2 hx
    rw [hx1]
    exact P.one_mem
  have h1 : uc22s2122npQbar D L =
      (uc22s2122npQNbar D L).map (uc22s2122npNbar D L).subtype :=
    (Subgroup.map_subgroupOf_eq_of_le (show uc22s2122npQbar D L ≤
      uc22s2122npNbar D L from le_inf Subgroup.le_normalizer inf_le_right)).symm
  rw [h1]
  exact Subgroup.map_mono hQNb_le_R

theorem uc22s2122np_exists_Rm_setup (D : Data G) {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') {b : G} (hbM : b ∈ D.M)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbK : b ∈ conjClosure D.M L)
    (hb7 : b ^ 7 = 1) :
    ∃ R : Subgroup (uc22s2122npNbar D L),
      Nat.card (R.map (uc22s2122npNbar D L).subtype) = 3136 ∧
      R.map (uc22s2122npNbar D L).subtype ≤ uc22s2122npKbar D L ∧
      uc22s2122npQbar D L ≤ R.map (uc22s2122npNbar D L).subtype ∧
      uc22p21cPi D.M ⟨b, hbM⟩ ∈ R.map (uc22s2122npNbar D L).subtype ∧
      uc22s2122npTbar D ≤ Subgroup.normalizer
        ((R.map (uc22s2122npNbar D L).subtype : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
  obtain ⟨P, R, hPnormal, hPcard, hRcard, hR_eq⟩ :=
    uc22s2122np_exists_sylow_preimage (N := uc22s2122npNbar D L)
      (Q := uc22s2122npQNbar D L)
      (uc22s2122np_card_Nbar D hL hL' hne hJ hJ' hK)
      (uc22s2122np_card_QNbar D hL hL' hne hJ hJ' hK)
  have hb7' : (⟨b, hbM⟩ : ↥D.M) ^ 7 = 1 := Subtype.ext hb7
  have hbbar7 : uc22p21cPi D.M ⟨b, hbM⟩ ^ 7 = 1 := by
    rw [← map_pow, hb7', map_one]
  have hbNbar : uc22p21cPi D.M ⟨b, hbM⟩ ∈ uc22s2122npNbar D L :=
    uc22s2122np_mem_Nbar D hL hL' hne hJ hJ' hK hbM hbT hbK
  have hbNb7 : (⟨uc22p21cPi D.M ⟨b, hbM⟩, hbNbar⟩ : uc22s2122npNbar D L) ^ 7 = 1 := by
    apply Subtype.ext
    simpa using hbbar7
  have hbR : (⟨uc22p21cPi D.M ⟨b, hbM⟩, hbNbar⟩ : uc22s2122npNbar D L) ∈ R := by
    rw [hR_eq]
    exact uc22s2122np_mem_comap_of_pow_seven (QN := uc22s2122npQNbar D L) P hPnormal hbNb7
  have hRmcard : Nat.card (R.map (uc22s2122npNbar D L).subtype) = 3136 := by
    rw [Subgroup.card_map_of_injective (uc22s2122npNbar D L).subtype_injective, hRcard]
  refine ⟨R, hRmcard, ?_, uc22s2122np_Qbar_le_Rm D P hR_eq, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Subgroup.mem_inf.1 r.2).2
  · exact Subgroup.mem_map_of_mem (uc22s2122npNbar D L).subtype hbR
  · exact uc22s2122np_Tbar_le_normalizer_Rm D hL P hPnormal hR_eq

theorem uc22s2122np_exists_sylow_Ebar {B : Type} [Group B] [Finite B]
    {Rm Kb : Subgroup B} {x : B} (hx7 : x ^ 7 = 1) (hxRm : x ∈ Rm)
    (hRmcard : Nat.card Rm = 3136) (hRmK : Rm ≤ Kb)
    (hKbcard : Nat.card Kb = 175560 * 175560) :
    ∃ Ē : Subgroup B, Nat.card Ē = 49 ∧ x ∈ Ē ∧ Ē ≤ Rm ∧
      CFSG.ABGLocalTools.IsSylowOf 7 Ē Kb := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 7 Rm,
      (Subgroup.zpowers x).subgroupOf Rm ≤ (Q : Subgroup Rm) := by
    have hz : IsPGroup 7 (Subgroup.zpowers x : Subgroup B) :=
      uc22s2122np_isPGroup_zpowers_of_pow_seven hx7
    have hzRm : IsPGroup 7 ((Subgroup.zpowers x).subgroupOf Rm) := hz.comap_subtype
    exact hzRm.exists_le_sylow
  let Ē : Subgroup B := (Q : Subgroup Rm).map Rm.subtype
  have hEcard : Nat.card Ē = 49 := by
    change Nat.card (Subgroup.map Rm.subtype (Q : Subgroup Rm)) = 49
    rw [Subgroup.card_map_of_injective Rm.subtype_injective, Sylow.card_eq_multiplicity,
      hRmcard, uc22s2122np_factorization_seven_card_thirtyone_thirtysix]
    norm_num
  have hE_le_Rm : Ē ≤ Rm := by
    change Subgroup.map Rm.subtype (Q : Subgroup Rm) ≤ Rm
    exact Subgroup.map_subtype_le _
  have hxE : x ∈ Ē := by
    have hxz : (⟨x, hxRm⟩ : Rm) ∈ (Q : Subgroup Rm) :=
      hQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x))
    exact Subgroup.mem_map_of_mem Rm.subtype hxz
  have hEsylow : CFSG.ABGLocalTools.IsSylowOf 7 Ē Kb := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hE_le_Rm.trans hRmK) ?_
    rw [hEcard, hKbcard, uc22s2122np_factorization_seven_card_J1_sq]
    norm_num
  exact ⟨Ē, hEcard, hxE, hE_le_Rm, hEsylow⟩

theorem uc22s2122np_Lbar_normal_in_Kbar (D : Data G) {L L' : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hne : L ≠ L')
    (hK : conjClosure D.M L = L ⊔ L') :
    uc22s2122npLbar D L ≤ uc22s2122npKbar D L ∧
      uc22s2122npKbar D L ≤
        Subgroup.normalizer (uc22s2122npLbar D L : Set (Bar2 D.M)) := by
  have hsup := uc22s2122np_Kbar_eq_sup D hL hL' hK
  constructor
  · rw [hsup]
    exact le_sup_left
  · rw [hsup]
    refine sup_le Subgroup.le_normalizer ?_
    exact CFSG.CGT.PushingUpLit.SYMB.le_normalizer_of_commute fun x hx y hy =>
      (uc22p22l_barImage_commute hL hL' hne y hy x hx).symm

theorem uc22s2122np_card_inf_of_sylow_seven {B : Type} [Group B] [Finite B]
    {Ē Kb Lb : Subgroup B} (hE : CFSG.ABGLocalTools.IsSylowOf 7 Ē Kb)
    (hLbK : Lb ≤ Kb) (hKbN : Kb ≤ Subgroup.normalizer (Lb : Set B))
    (hLbcard : Nat.card Lb = 175560) :
    Nat.card ↥(Ē ⊓ Lb) = 7 ∧ Ē ⊓ Lb ≠ ⊥ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 7 (Ē ⊓ Lb) Lb :=
    hE.inf_of_le_normalizer hLbK hKbN
  have hcard : Nat.card ↥(Ē ⊓ Lb) = 7 := by
    rw [hS.card_eq, hLbcard, uc22s2122np_factorization_seven_card_J1]
    norm_num
  refine ⟨hcard, ?_⟩
  intro hbot
  have h1 : Nat.card ↥(Ē ⊓ Lb) = 1 := by rw [hbot, Subgroup.card_bot]
  omega

theorem uc22s2122np_isComplement_of_card {B : Type} [Group B] [Finite B]
    {Rm Ē Qb : Subgroup B} (hERm : Ē ≤ Rm) (hQRm : Qb ≤ Rm)
    (hEp : IsPGroup 7 Ē) (hQp : IsPGroup 2 Qb)
    (hEcard : Nat.card Ē = 49) (hQcard : Nat.card Qb = 64)
    (hRmcard : Nat.card Rm = 3136) :
    (Ē.subgroupOf Rm).IsComplement' (Qb.subgroupOf Rm) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hdisj : Disjoint (Ē.subgroupOf Rm) (Qb.subgroupOf Rm) :=
    IsPGroup.disjoint_of_ne 7 2 (by norm_num) _ _
      (hEp.comap_subtype) (hQp.comap_subtype)
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisj
  rw [show Nat.card ↥(Ē.subgroupOf Rm) = Nat.card Ē from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hERm).toEquiv,
    show Nat.card ↥(Qb.subgroupOf Rm) = Nat.card Qb from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQRm).toEquiv,
    hEcard, hQcard, hRmcard]

theorem uc22s2122np_set_product_eq {B : Type} [Group B] [Finite B]
    {Tb Rm Ē Qb : Subgroup B} (hTRm : Tb ≤ Subgroup.normalizer (Rm : Set B))
    (hERm : Ē ≤ Rm) (hQRm : Qb ≤ Rm) (hQT : Qb ≤ Tb)
    (hcompl : (Ē.subgroupOf Rm).IsComplement' (Qb.subgroupOf Rm)) :
    ((Ē ⊔ Tb : Subgroup B) : Set B) = (Ē : Set B) * (Tb : Set B) := by
  have hRm_le_sup : Rm ≤ Ē ⊔ Tb := by
    intro r hr
    obtain ⟨e, he, q, hq, rfl⟩ := uc22s2122np_exists_mul_of_isComplement hcompl r hr
    exact (Ē ⊔ Tb).mul_mem ((le_sup_left : Ē ≤ Ē ⊔ Tb) he)
      ((le_sup_right : Tb ≤ Ē ⊔ Tb) (hQT hq))
  have hsup_eq : (Ē ⊔ Tb : Subgroup B) = Rm ⊔ Tb :=
    le_antisymm (sup_le (hERm.trans le_sup_left) le_sup_right) (sup_le hRm_le_sup le_sup_right)
  rw [hsup_eq, Subgroup.coe_mul_of_right_le_normalizer_left Rm Tb hTRm]
  apply Set.eq_of_subset_of_subset
  · intro x hx
    obtain ⟨r, hr, t, ht, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨e, he, q, hq, rfl⟩ := uc22s2122np_exists_mul_of_isComplement hcompl r hr
    exact Set.mem_mul.2 ⟨e, he, q * t, Tb.mul_mem (hQT hq) ht, by group⟩
  · exact Set.mul_subset_mul (fun x hx => hERm hx) (subset_refl _)

theorem uc22s2122np_exists_barE_of_pair {D : Data G} {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L ≠ L') (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') {b : G} (hbM : b ∈ D.M)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbK : b ∈ conjClosure D.M L)
    (hb7 : b ^ 7 = 1) :
    ∃ Ē : Subgroup (Bar2 D.M), Nat.card Ē = 49 ∧
      ((Ē ⊔ barImage D.M D.T : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) =
        (Ē : Set (Bar2 D.M)) * (barImage D.M D.T : Set (Bar2 D.M)) ∧
      uc22p21cPi D.M ⟨b, hbM⟩ ∈ Ē ∧ Ē ⊓ barImage D.M L ≠ ⊥ := by
  classical
  have hKbcard : Nat.card (uc22s2122npKbar D L) = 175560 * 175560 :=
    uc22s2122np_card_Kbar D hL hL' hne hJ hJ' hK
  have hQbcard : Nat.card (uc22s2122npQbar D L) = 64 :=
    uc22s2122np_card_Qbar D hL hL' hne hJ hJ' hK
  obtain ⟨R, hRmcard, hRm_le_Kb, hQb_le_Rm, hbRm, hT_le_NRm⟩ :=
    uc22s2122np_exists_Rm_setup D hL hL' hne hJ hJ' hK hbM hbT hbK hb7
  have hb7' : (⟨b, hbM⟩ : ↥D.M) ^ 7 = 1 := Subtype.ext hb7
  have hbbar7 : uc22p21cPi D.M ⟨b, hbM⟩ ^ 7 = 1 := by
    rw [← map_pow, hb7', map_one]
  obtain ⟨Ē, hEcard, hbĒ, hE_le_Rm, hE_sylow⟩ :=
    uc22s2122np_exists_sylow_Ebar (Rm := R.map (uc22s2122npNbar D L).subtype)
      (Kb := uc22s2122npKbar D L) (x := uc22p21cPi D.M ⟨b, hbM⟩)
      hbbar7 hbRm hRmcard hRm_le_Kb hKbcard
  obtain ⟨hLb_le_Kb, hKb_le_NLb⟩ := uc22s2122np_Lbar_normal_in_Kbar D hL hL' hne hK
  have hinf := uc22s2122np_card_inf_of_sylow_seven hE_sylow hLb_le_Kb hKb_le_NLb
    (uc22s2122np_card_barImage_of_isJ1 hL hJ)
  have hQb_p : IsPGroup 2 (uc22s2122npQbar D L) := by
    refine IsPGroup.of_card (p := 2) (n := 6) ?_
    rw [hQbcard]
    norm_num
  have hcompl := uc22s2122np_isComplement_of_card hE_le_Rm hQb_le_Rm
    hE_sylow.isPGroup hQb_p hEcard hQbcard hRmcard
  have hset := uc22s2122np_set_product_eq hT_le_NRm hE_le_Rm hQb_le_Rm
    (inf_le_left : uc22s2122npQbar D L ≤ uc22s2122npTbar D) hcompl
  refine ⟨Ē, hEcard, ?_, hbĒ, hinf.2⟩
  · simpa only [uc22s2122npTbar] using hset

end CFSG.LocalAnalysis.UniquenessCase.UC22

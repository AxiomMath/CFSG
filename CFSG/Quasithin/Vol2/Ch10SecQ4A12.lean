module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10SecQ4A7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] {K J X T : Subgroup G}

@[expose] noncomputable def fK (hKJ : K ≤ J) : ↥K →* ↥J ⧸ CFSG.pCore 2 ↥J :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (Subgroup.inclusion hKJ)

theorem fK_eq_one_iff (hKJ : K ≤ J) (x : ↥K) : fK hKJ x = 1 ↔ (x : G) ∈ pCoreOf 2 J := by
  rw [fK, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨fun h => mem_blockQ_of_mem_pCore h, fun h => mem_pCore_of_mem_blockQ h⟩

theorem fK_apply (hKJ : K ≤ J) (x : ↥K) :
    fK hKJ x = QuotientGroup.mk (⟨x, hKJ x.2⟩ : ↥J) := rfl

theorem inf_pCoreOf_le_blockQ (hKJ : K ≤ J) : K ⊓ pCoreOf 2 J ≤ blockQ K := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  refine le_pCoreOf_of_normalized inf_le_left ?_ (hP2.to_le inf_le_right)
  intro g hg
  exact CFSG.QuasithinUnique.C5.mem_normalizer_inf (Subgroup.le_normalizer hg) (hPnorm (hKJ hg))

theorem fK_ker_le (hKJ : K ≤ J) (x : ↥K) (hx : fK hKJ x = 1) : (x : G) ∈ blockQ K :=
  inf_pCoreOf_le_blockQ hKJ ⟨x.2, (fK_eq_one_iff hKJ x).mp hx⟩

theorem isSQTKCat_of_le' [Finite G] (hJX : J ≤ X) (hX : CFSG.SectionRank.IsSQTKCat ↥X) :
    CFSG.SectionRank.IsSQTKCat ↥J :=
  CFSG.SectionRank.IsSQTKCat.of_le hJX hX

theorem sqtkHypCat_quot [Finite G] (hJX : J ≤ X) (hX : CFSG.SectionRank.IsSQTKCat ↥X) :
    Vol2Native.SQTKHypCat (↥J ⧸ CFSG.pCore 2 ↥J) :=
  Vol2Native.SQTKHypCat.quotient_pCore ↥J (isSQTKCat_of_le' hJX hX)

theorem isSylowTwoOf_quot [Finite G] (hT : IsSylowTwoOf T X) (hJ : J ∈ cComp X) :
    IsSylowTwoOf (((T ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf
    (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJ) hT)) _
    (QuotientGroup.mk'_surjective _)

theorem quotSylow_le_normalizer (hKJ : K ≤ J) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ((T ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ≤
      Subgroup.normalizer ((fK hKJ).range : Set (↥J ⧸ CFSG.pCore 2 ↥J)) := by
  rintro _ ⟨s, hs, rfl⟩
  have hsT : (s : G) ∈ T := (Subgroup.mem_subgroupOf.mp hs).1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, rfl⟩
    have hk' : (s : G) * k * (s : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK hsT) k).mp k.2
    refine ⟨⟨_, hk'⟩, ?_⟩
    rw [fK_apply, fK_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  · rintro ⟨k, hk⟩
    have hk' : (s : G)⁻¹ * k * (s : G)⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTK hsT)) k).mp k.2
    refine ⟨⟨_, hk'⟩, ?_⟩
    have h1 : y = (QuotientGroup.mk' (CFSG.pCore 2 ↥J) s)⁻¹ * fK hKJ k *
        QuotientGroup.mk' (CFSG.pCore 2 ↥J) s := by
      rw [hk]
      group
    rw [h1, fK_apply, fK_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp

theorem range_fK_ne_top (hJ : J ∈ cComp X) (hKJ : K < J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hKp : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    (fK hKJ.le).range ≠ ⊤ := by
  intro htop
  have hnorm : (K.subgroupOf J).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ.le).mpr fun j hj => ?_
    obtain ⟨k, hk⟩ : QuotientGroup.mk (⟨j, hj⟩ : ↥J) ∈ (fK hKJ.le).range :=
      htop ▸ Subgroup.mem_top _
    rw [fK_apply, QuotientGroup.eq] at hk
    have hq : (k : G)⁻¹ * j ∈ pCoreOf 2 J := mem_blockQ_of_mem_pCore hk
    have hj' : j = k * ((k : G)⁻¹ * j) := by group
    rw [hj']
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer k.2) (hQK hq)
  exact not_subnormal_of_mem_cComp hJ hKJ hK1 hKp
    (A3.subnormal_trans (A3.subnormal_of_normal hKJ.le hnorm) (subnormal_of_mem_cComp hJ))

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

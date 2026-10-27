module

public import CFSG.Quasithin.MS93.S5ACand
public import CFSG.Quasithin.MS93.S51Cand
public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.S5ALift

public section

namespace CFSG.Quasithin.MS93.S51

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem card_V4_le_of_isMaxElemAbelian (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp (S5.imSp a A)) * Nat.card (S5.imSp a A) := by
  have hl := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  have hAT : A ≤ T := hA.1
  have hAM : A ≤ M := hAT.trans h.le
  have hUe : IsElemAbelian 2 (Uq M T L) := h.isElemAbelian_Uq
  have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (h.Z0q_le_pCoreOf.trans h.pCore_le)
  have h1 := card_le_relIndex_mul_card hUe hUT hA
  have hQC : A ⊓ pCoreOf 2 M ≤ A ⊓ Subgroup.centralizer (Uq M T L : Set G) :=
    inf_le_inf_left A (h.pCoreOf_le_centralizer_Z0q.trans
      (Subgroup.centralizer_le (Uq_le_Z0q h.L_le)))
  have h2 : (A ⊓ Subgroup.centralizer (Uq M T L : Set G)).relIndex A ≤
      (pCoreOf 2 M).relIndex A := by
    rw [← Subgroup.inf_relIndex_right (pCoreOf 2 M), inf_comm (pCoreOf 2 M)]
    refine Subgroup.relIndex_le_of_le_left hQC ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) (Uq M T L)
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h4 : (Subgroup.centralizer (A : Set G)).relIndex (Uq M T L) ≤ (pCoreOf 2 M).relIndex A := by
    rw [inf_comm] at h3
    have : (Subgroup.centralizer (A : Set G)).relIndex (Uq M T L) *
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (A : Set G)) ≤
        (pCoreOf 2 M).relIndex A * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [h3]
      exact h1.trans (Nat.mul_le_mul_right _ h2)
    exact Nat.le_of_mul_le_mul_right this hpos
  rw [hd.card_eq_mul_relIndex hl hAM, hd.card_imSp h hAT]
  exact Nat.mul_le_mul_left _ h4

theorem candMax_le_imSp_jOffM (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {A : Subgroup ↥(StatedSp 2 F)} (hA : A ∈ S5.candMax (S5.imSp a T)) :
    A ≤ S5.imSp a (S5.jOffM M T L (2 ^ k)) := by
  have hl := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  have hmem := hd.liftT_mem_offSetM h hl hA
  rw [← S5.imSp_liftT hA.1.1]
  exact S5.imSp_mono a (le_iSup₂_of_le _ hmem le_rfl)

theorem thompson_conf (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂)
    (hJ : S5.imSp a (S5.jOffM M T L (2 ^ k)) = MSP.xPoint p₁ ⊔ MSP.xPoint p₂) :
    S5.jOffM M T L (2 ^ k) = S5.liftT T a (MSP.xPoint p₁ ⊔ MSP.xPoint p₂) ∧
      thompsonJ T ≤ S5.jOffM M T L (2 ^ k) ∧ ¬ thompsonJ T ≤ pCoreOf 2 M ∧
      baum T ≤ S5.jOffM M T L (2 ^ k) := by
  classical
  have := hd.charP
  have hl := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  set J := S5.jOffM M T L (2 ^ k) with hJdef
  set Jb := MSP.xPoint p₁ ⊔ MSP.xPoint p₂ with hJb
  have hJT : J ≤ T := iSup₂_le fun E hE => hE.1.1
  have hJM : J ≤ M := hJT.trans h.le
  have hR : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hJR : Jb ≤ S5.imSp a T := hJ ▸ S5.imSp_mono a hJT
  have hmax : ∀ A ∈ S5.candMax (S5.imSp a T), A ≤ Jb := fun A hA =>
    hJ ▸ candMax_le_imSp_jOffM hd h hA
  obtain ⟨hcm, hfix, hab⟩ := conf_analysis hR hp₁ hp₂ hJR hmax
  have hJeq : J = S5.liftT T a Jb := hd.jOffM_eq_of_candMax_eq h hl hcm
  have hthom : thompsonJ T ≤ J := by
    refine iSup₂_le fun A hA => ?_
    have hAT : A ≤ T := hA.1
    have hcomm : ∀ x ∈ S5.imSp a A, ∀ y ∈ S5.imSp a A, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have hc := hA.2.1.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
        ⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩
      have hc' : (x : G) * y = y * x := congrArg Subtype.val hc
      exact Subtype.ext (by simpa using hc')
    have hAJ := hab (S5.imSp a A) (S5.imSp_mono a hAT) hcomm
      (card_V4_le_of_isMaxElemAbelian hd h hA)
    rw [hJeq]
    intro t ht
    exact S5.mem_liftT.2 ⟨hAT ht, hAT.trans h.le ht,
      hAJ (S5.mem_imSp.2 ⟨t, ht, hAT.trans h.le ht, rfl⟩)⟩
  have hnotQ : ¬ thompsonJ T ≤ pCoreOf 2 M := by
    intro hle
    have heq : thompsonJ (pCoreOf 2 M) = thompsonJ T := B6.thompsonJ_eq_of_le hle h.pCore_le
    have := Setup.characteristic_thompsonJ (pCoreOf 2 M)
    have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((thompsonJ (pCoreOf 2 M)).subgroupOf (pCoreOf 2 M))
    rw [Subgroup.map_subgroupOf_eq_of_le (C1GN.thompsonJ_le _), heq] at hN
    exact h.noChar _ (C1GN.thompsonJ_le T) (Setup.thompsonJ_ne_bot h.isPGroup h.ne_bot)
      (Setup.characteristic_thompsonJ T) ((le_normalizer_pCoreOf M).trans hN)
  have hbaum : baum T ≤ J := by
    obtain ⟨nv⟩ := hd.nonempty_natVec
    have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (h.Z0q_le_pCoreOf.trans h.pCore_le)
    have hCU : Uq M T L ⊓ Subgroup.centralizer (J : Set G) ≤ omegaOneCenterOf (thompsonJ T) := by
      rw [(omegaOne_centralizer_thompsonJ T).2]
      intro u hu
      simp only [Subgroup.mem_iInf]
      intro A hA
      rw [eq_omegaOneOf_centralizer hA]
      refine Subgroup.subset_closure ⟨⟨hUT hu.1, ?_⟩, h.isElemAbelian_Uq.2 u hu.1⟩
      exact Subgroup.centralizer_le ((B6.le_thompsonJ hA).trans hthom) hu.2
    refine (inf_le_inf_left T (Subgroup.centralizer_le hCU)).trans ?_
    intro t ⟨htT, htC⟩
    have htM : t ∈ M := h.le htT
    have hfixt : (⟨t, htM⟩ : ↥M) ∈ (Subgroup.comap a (MSP.fixer (MSP.fixSp Jb))) := by
      rw [Subgroup.mem_comap, MSP.mem_fixer]
      intro w hw
      obtain ⟨u, rfl⟩ := nv.surj (Multiplicative.ofAdd w)
      have huJ : (u : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [nv.mem_centralizer_iff_vec_mem_fixSp hd.nat.1 hl hJM u, hJ]
        exact hw
      have hcomm : ((⟨t, htM⟩ : ↥M) : G) * (u : G) = (u : G) * ((⟨t, htM⟩ : ↥M) : G) := by
        have := Subgroup.mem_centralizer_iff.1 htC (u : G) ⟨u.2, huJ⟩
        exact this.symm
      exact nv.mat_mulVec_vec_of_commute ⟨t, htM⟩ u hcomm
    have htJ : a ⟨t, htM⟩ ∈ Jb :=
      hfix ⟨S5.mem_imSp.2 ⟨t, htT, htM, rfl⟩, hfixt⟩
    rw [hJeq]
    exact S5.mem_liftT.2 ⟨htT, htM, htJ⟩
  exact ⟨hJeq, hthom, hnotQ, hbaum⟩

end CFSG.Quasithin.MS93.S51

module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conjSubgroup_Rt_le_of_forall {L : Subgroup G} {t ν : G}
    (h : ∀ m ∈ M, t ∈ conjSubgroup m L → conjSubgroup (ν * m) L ≤ Rt M L t) :
    conjSubgroup ν (Rt M L t) ≤ Rt M L t := by
  unfold Rt conjSubgroup
  rw [Subgroup.map_iSup]
  refine iSup_le fun m => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hm => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ht => ?_
  have := h m hm ht
  rw [conjSubgroup_mul] at this
  exact this

theorem sec8NormV_le_normR (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {ν : G}
    (hνM : ν ∈ M) (hνV : ν ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)) :
    ν ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hle : conjSubgroup ν (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) t := by
    refine conjSubgroup_Rt_le_of_forall (fun m hm htm => ?_)
    have hBV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm htm
    have hνmM : ν * m ∈ M := M.mul_mem hνM hm
    have hle1 : conjSubgroup (ν * m) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
      refine sup_le ?_ sec39_Z_le_Vt
      rw [conjSubgroup_mul]
      have h : conjSubgroup ν (conjSubgroup m B) ≤
          conjSubgroup ν (Vt M (LB M Q B) B Z t) := Subgroup.map_mono hBV
      rwa [conjSubgroup_eq_self_iff.mpr hνV] at h
    obtain ⟨r', hr', heq⟩ := stroth56Sp_holds G M Q Z B hc n t hs (ν * m) hνmM hle1
    have hr'M : r' ∈ M := hc.Rt_le_M t hr'
    have hκM : r'⁻¹ * (ν * m) ∈ M := M.mul_mem (M.inv_mem hr'M) hνmM
    have hκBZ : r'⁻¹ * (ν * m) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
      refine conjSubgroup_eq_self_iff.mp ?_
      have hZr : conjSubgroup r'⁻¹ Z = Z := hc.conj_Z_eq (M.inv_mem hr'M)
      have hrB : conjSubgroup r'⁻¹ (conjSubgroup r' B) = B := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
      rw [conjSubgroup_mul, conjSubgroup_sup', hc.conj_Z_eq hνmM, heq, conjSubgroup_sup', hrB, hZr]
    have hκL : r'⁻¹ * (ν * m) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      (hc.mem_normalizer_LB_iff' hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hκM).mpr hκBZ
    have hmul : ν * m = r' * (r'⁻¹ * (ν * m)) := by group
    have e1 : conjSubgroup (ν * m) (LB M Q B) = conjSubgroup r' (LB M Q B) := by
      rw [hmul, conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr hκL]
    rw [e1, ← hc.LB_conj hr'M]
    exact hc.LB_conj_le_Rt_of_mem ht hr'
  exact conjSubgroup_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]))

theorem sec8NormR_le_normZ0 (hc : Ctx M Q Z B) {R Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 R Q)
    {ν : G} (hνM : ν ∈ M) (hνR : ν ∈ Subgroup.normalizer (R : Set G)) :
    ν ∈ Subgroup.normalizer (Z0 : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hzZ : z ∈ Z0 := hz
  have hzR : z ∈ R := hZ0.le hzZ
  have hνzR : ν * z * ν⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hνR z).mp hzR
  refine (hZ0.mem_iff).mpr ⟨hνzR, fun ρ hρ => ?_⟩
  have hρ' : ν⁻¹ * ρ * ν ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hνR) ρ).mp hρ
    simpa using h
  have hq : ⁅z, ν⁻¹ * ρ * ν⁆ ∈ Q := hZ0.comm_mem hzZ hρ'
  have e : ⁅ν * z * ν⁻¹, ρ⁆ = ν * ⁅z, ν⁻¹ * ρ * ν⁆ * ν⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hνM) _).mp hq

theorem sec8NormZ0_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
        m ∈ Subgroup.normalizer (Z0 : Set G) := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 m hm hmV
  exact sec8NormR_le_normZ0 hc hZ0 hm (sec8NormV_le_normR hc hs hm hmV)

@[expose] def Sec8ZVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ u ∈ Z0, u ∉ Q → Ut Q Z u = Vt M (LB M Q B) B Z t

theorem sec8TI_of (hZV : Sec8ZVStatement) : Sec8TIStatement := by
  have hNZ := sec8NormZ0_holds
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 g hg u hu huQ hgu
  have hgN : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 (M.inv_mem hg)
  have huQ' : g * u * g⁻¹ ∉ Q := by
    intro h
    apply huQ
    have h4 := (Subgroup.mem_normalizer_iff.mp hgN (g * u * g⁻¹)).mp h
    have h3 : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rwa [h3] at h4
  have hZu : Ut Q Z u = Vt M (LB M Q B) B Z t := hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ
  have hZu' : Ut Q Z (g * u * g⁻¹) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 (g * u * g⁻¹) hgu huQ'
  have hconj := Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) u
  have hgV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    ((congrArg (conjSubgroup g) hZu).symm.trans hconj.symm).trans hZu'
  exact hNZ G M Q Z B hc n t hs Z0 hZ0 g hg (conjSubgroup_eq_self_iff.mp hgV)

end CFSG.RankThree.GF2n.Stroth80

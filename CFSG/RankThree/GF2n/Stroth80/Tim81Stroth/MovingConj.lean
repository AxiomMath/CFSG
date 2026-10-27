module

public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem exists_conj_le_CN_of_pCore_le_of_not_weaklyClosed
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hVleO2 : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      inSubgroup (pCore 2) (MbarPrime M Q Z Z0))
    (hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    (hNWC : ¬ WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 := by
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt hs.toSec5.mem
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hx : ∃ x : Hbar M Q Z, conjSubgroup x V ≤ inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ∧
      conjSubgroup x V ≠ V := by
    by_contra hcon
    apply hNWC
    refine ⟨hVleO2, fun x hxle => ?_⟩
    by_contra hne
    exact hcon ⟨x, hxle, hne⟩
  obtain ⟨x, hxle, hxne⟩ := hx
  obtain ⟨y, hyH0, hyx⟩ := Subgroup.mem_map.mp x.2
  let g : G := y.1
  have hgM : g ∈ M := y.2
  have hgH0 : g ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hyH0
  have hy_eq : (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) y := hyx.symm
  have hconjH : conjSubgroup g Z0 ≤ H0 M Z := by
    rintro w ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hgM (hZ0M hz)) (M.inv_mem hgM), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hgu : u * g = g * u := Subgroup.mem_centralizer_iff.mp hgH0.2 u hu
    have hzu : u * z = z * u := Subgroup.mem_centralizer_iff.mp (hZ0H hz).2 u hu
    have hgu' : u * g⁻¹ = g⁻¹ * u := by
      calc u * g⁻¹ = g⁻¹ * (g * u) * g⁻¹ := by group
        _ = g⁻¹ * (u * g) * g⁻¹ := by rw [hgu]
        _ = g⁻¹ * u := by group
    calc u * (g * z * g⁻¹) = (u * g) * z * g⁻¹ := by group
      _ = (g * u) * z * g⁻¹ := by rw [hgu]
      _ = g * (u * z) * g⁻¹ := by group
      _ = g * (z * u) * g⁻¹ := by rw [hzu]
      _ = g * z * (u * g⁻¹) := by group
      _ = g * z * (g⁻¹ * u) := by rw [hgu']
      _ = (g * z * g⁻¹) * u := by group
  have hbarconjH : bar M Q (conjSubgroup g Z0) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hconjH)
  have hconjBar : bar M Q (conjSubgroup g Z0) =
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) y) (bar M Q Z0) := by
    have hsub : conjSubgroup y (Z0.subgroupOf M) = (conjSubgroup g Z0).subgroupOf M := by
      ext z
      simp only [mem_conjSubgroup, Subgroup.mem_subgroupOf]
      rfl
    rw [show bar M Q Z0 = (Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) from rfl]
    rw [CFSG.GroupTheory.map_conjSubgroup, hsub]
    rfl
  have hconjEq : conjSubgroup x V =
      (bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z)) := by
    apply Subgroup.map_injective (f := (bar M Q (H0 M Z)).subtype)
      (bar M Q (H0 M Z)).subtype_injective
    calc (conjSubgroup x V).map (bar M Q (H0 M Z)).subtype
        = conjSubgroup (x : Mbar M Q) (V.map (bar M Q (H0 M Z)).subtype) :=
          (CFSG.GroupTheory.map_conjSubgroup (bar M Q (H0 M Z)).subtype V x).symm
      _ = conjSubgroup (x : Mbar M Q) (bar M Q Z0) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hbarZ0H]
      _ = bar M Q (conjSubgroup g Z0) := by
          rw [hy_eq]
          exact hconjBar.symm
      _ = ((bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z))).map
            (bar M Q (H0 M Z)).subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hbarconjH]
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hQCN : Q ≤ hc.CN t := sec8_Q_le_CN hc hs.toSec5.mem
  have hbarCNH : bar M Q (hc.CN t) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hCNH0)
  have hleCN : conjSubgroup x V ≤ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    hxle.trans hO2
  have hsub : (bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := hconjEq ▸ hleCN
  have hbarle : bar M Q (conjSubgroup g Z0) ≤ bar M Q (hc.CN t) := by
    have h := Subgroup.map_mono (f := (bar M Q (H0 M Z)).subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hbarconjH,
      Subgroup.map_subgroupOf_eq_of_le hbarCNH] at h
  refine ⟨g, hgM, ?_, ?_⟩
  · intro z hz
    have hzM : z ∈ M := conj_le_M hZ0M hgM hz
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ bar M Q (conjSubgroup g Z0) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
    exact (mk_mem_bar_iff_sec4 hQCN ⟨z, hzM⟩).mp (hbarle hmem)
  · intro heq
    apply hxne
    rw [hconjEq, heq]

theorem pCore_two_MbarPrime_le_CN_of_fitting
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  let K : Subgroup (Mbar M Q) := bar M Q (NormH0 M Z Z0)
  let H : Subgroup (Mbar M Q) := bar M Q (H0 M Z)
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hKH : K ≤ H := MbarPrimeLe M Q Z Z0
  let e : ↥M' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hFK : generalizedFitting ↥K = (bar M Q (hc.CN t)).subgroupOf K := by
    simpa [K] using hF
  have hleF : pCore 2 ↥K ≤ generalizedFitting ↥K := by
    rw [generalizedFitting.eq_sup]
    exact (CFSG.pCore_le_fitting (G := ↥K) 2).trans le_sup_left
  have hpcK : pCore 2 ↥K ≤ (bar M Q (hc.CN t)).subgroupOf K := hleF.trans (le_of_eq hFK)
  have hmapP : (pCore 2 ↥M').map e.toMonoidHom = pCore 2 ↥K := CFSG.pCore_map_iso 2 e
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt hs.toSec5.mem
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hCNN : hc.CN t ≤ NormH0 M Z Z0 := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hCNH0 hy,
      IsCentrePre.mem_normalizer hZ0 hnormR (Ctx.mem_CN.mp hy).1⟩
  have hCNK : bar M Q (hc.CN t) ≤ K :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hCNN)
  have hKle : (pCore 2 ↥K).map K.subtype ≤ bar M Q (hc.CN t) :=
    calc (pCore 2 ↥K).map K.subtype
        ≤ ((bar M Q (hc.CN t)).subgroupOf K).map K.subtype := Subgroup.map_mono hpcK
      _ = bar M Q (hc.CN t) := Subgroup.map_subgroupOf_eq_of_le hCNK
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  have hea : e a ∈ pCore 2 ↥K := by
    rw [← hmapP]
    exact Subgroup.mem_map_of_mem e.toMonoidHom ha
  have hxbar : (M'.subtype a : Mbar M Q) ∈ bar M Q (hc.CN t) := by
    have h := hKle (Subgroup.mem_map_of_mem K.subtype hea)
    have hcoe : ((M'.subtype a : Hbar M Q Z) : Mbar M Q) = K.subtype (e a) := rfl
    rwa [hcoe]
  exact Subgroup.mem_subgroupOf.mpr hxbar

theorem bar_Z0_subgroupOf_le_pCore_of_centreStatement
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZc : Sec7CentreStatement) :
    (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      inSubgroup (pCore 2) (MbarPrime M Q Z Z0) := by
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hE : Assembly.IsElemAbelian 2 V :=
    (isElemAbelian_bar_Z0 hc hs hZc hZ0).subgroupOf (bar M Q (H0 M Z))
  have hVp : IsPGroup 2 ↥V := CFSG.Open.IsElemAbelian.isPGroup hE
  have hbarZ0K : bar M Q Z0 ≤ bar M Q (NormH0 M Z Z0) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M fun z hz =>
        Subgroup.mem_inf.mpr ⟨hZ0H hz, Z0.le_normalizer hz⟩)
  have hVle : V ≤ M' := fun v hv =>
    Subgroup.mem_subgroupOf.mpr (hbarZ0K (Subgroup.mem_subgroupOf.mp hv))
  have hM'norm : M' ≤ Subgroup.normalizer (V : Set (Hbar M Q Z)) := by
    have h := MbarPrime_eq_normalizer_bar_Z0 hc hs hZ0
    simpa [M', V] using h.le
  have hVnorm : (V.subgroupOf M').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hM'norm
  have hVsubp : IsPGroup 2 (V.subgroupOf M') := hVp.comap_subtype
  have hle : V.subgroupOf M' ≤ pCore 2 ↥M' :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hVnorm hVsubp
  intro v hv
  exact Subgroup.mem_map.mpr ⟨⟨v, hVle hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

theorem exists_conj_le_CN_of_fitting_of_not_weaklyClosed
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZc : Sec7CentreStatement)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNWC : ¬ WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 :=
  exists_conj_le_CN_of_pCore_le_of_not_weaklyClosed hc hs hZ0
    (bar_Z0_subgroupOf_le_pCore_of_centreStatement hc hs hZ0 hZc)
    (pCore_two_MbarPrime_le_CN_of_fitting hc hs hZ0 hF) hNWC

end CFSG.RankThree.GF2n.Stroth80

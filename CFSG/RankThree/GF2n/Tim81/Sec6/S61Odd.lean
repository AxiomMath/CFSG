module

public import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem Sec6Hyp.exists_conjSubgroup_eq_of_commute (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) {x b : ↥M} (hb : (b : G) ∈ B) (hb1 : (b : G) ≠ 1)
    (hxb : QuotientGroup.mk' (pCore 2 ↥M) x * QuotientGroup.mk' (pCore 2 ↥M) b =
      QuotientGroup.mk' (pCore 2 ↥M) b * QuotientGroup.mk' (pCore 2 ↥M) x) :
    ∃ p ∈ Pc M V, conjSubgroup (x : G) B = conjSubgroup p B := by
  set c : ↥M := x * b * x⁻¹ * b⁻¹ with hcdef
  have hc_ker : c ∈ pCore 2 ↥M := by
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) c = 1 := by
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hxb]
      group
    have h2 : c ∈ (QuotientGroup.mk' (pCore 2 ↥M)).ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hcP : (c : G) ∈ Pc M V := by
    have h2 : c ∈ (Pc M V).subgroupOf M := by
      rw [hS.sec5.Pc_subgroupOf hS.ne]
      exact hc_ker
    exact h2
  have hxb_eq : (x * b * x⁻¹ : ↥M) = c * b := by
    rw [hcdef]
    group
  have hcoe : (((x * b * x⁻¹ : ↥M)) : G) = (x : G) * (b : G) * (x : G)⁻¹ := by simp
  have hyBx : (((x * b * x⁻¹ : ↥M)) : G) ∈ conjSubgroup (x : G) B := by
    rw [mem_conjSubgroup, hcoe,
      show (x : G)⁻¹ * ((x : G) * (b : G) * (x : G)⁻¹) * (x : G) = (b : G) by group]
    exact hb
  have hy_sup : (((x * b * x⁻¹ : ↥M)) : G) ∈ B ⊔ Pc M V := by
    have h1 : (((x * b * x⁻¹ : ↥M)) : G) = (c : G) * (b : G) := by
      rw [hxb_eq]
      simp
    rw [h1, sup_comm]
    exact Subgroup.mul_mem_sup hcP hb
  have hy_ne : (((x * b * x⁻¹ : ↥M)) : G) ≠ 1 := by
    intro h1
    have h2 : (x * b * x⁻¹ : ↥M) = 1 := Subtype.ext h1
    have h3 : b = 1 := by
      have h5 := congrArg (fun t : ↥M => x⁻¹ * t * x) h2
      rw [show x⁻¹ * (x * b * x⁻¹) * x = b by group] at h5
      rwa [show x⁻¹ * (1 : ↥M) * x = 1 by group] at h5
    exact hb1 (by rw [h3]; rfl)
  have hne : conjSubgroup (x : G) B ⊓ (B ⊔ Pc M V) ≠ ⊥ := by
    intro hbot
    have hmem : (((x * b * x⁻¹ : ↥M)) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hyBx, hy_sup⟩
    exact hy_ne (Subgroup.mem_bot.mp hmem)
  exact hS.sec5.stmt55 B hB (conjSubgroup (x : G) B)
    (hS.sec5.conj_mem_sigmaSet x.2 hB) hne

theorem Sec6Hyp.conj_mem_imgQ_of_commute (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) {x b : ↥M} (hb : (b : G) ∈ B) (hb1 : (b : G) ≠ 1)
    (hxb : QuotientGroup.mk' (pCore 2 ↥M) x * QuotientGroup.mk' (pCore 2 ↥M) b =
      QuotientGroup.mk' (pCore 2 ↥M) b * QuotientGroup.mk' (pCore 2 ↥M) x)
    {z : MBar M} (hz : z ∈ imgQ M B) :
    QuotientGroup.mk' (pCore 2 ↥M) x * z * (QuotientGroup.mk' (pCore 2 ↥M) x)⁻¹ ∈
      imgQ M B := by
  obtain ⟨w, hwB, rfl⟩ := mem_imgQ_iff.mp hz
  obtain ⟨p, hpP, hpconj⟩ := hS.exists_conjSubgroup_eq_of_commute hB hb hb1 hxb
  set p' : ↥M := ⟨p, hS.sec5.toRootHyp.toHyp.Pc_le_M hpP⟩ with hp'def
  have hp'1 : QuotientGroup.mk' (pCore 2 ↥M) p' = 1 := (hS.mk_eq_one_iff p').mpr hpP
  have hwBp : (((x * w * x⁻¹ : ↥M)) : G) ∈ conjSubgroup p B := by
    rw [← hpconj, mem_conjSubgroup]
    have hcoe' : (((x * w * x⁻¹ : ↥M)) : G) = (x : G) * (w : G) * (x : G)⁻¹ := by simp
    rw [hcoe',
      show (x : G)⁻¹ * ((x : G) * (w : G) * (x : G)⁻¹) * (x : G) = (w : G) by group]
    exact hwB
  have hw'B : (((p'⁻¹ * (x * w * x⁻¹) * p' : ↥M)) : G) ∈ B := by
    have := mem_conjSubgroup.mp hwBp
    simpa using this
  have hmkw' : QuotientGroup.mk' (pCore 2 ↥M) (p'⁻¹ * (x * w * x⁻¹) * p') =
      QuotientGroup.mk' (pCore 2 ↥M) (x * w * x⁻¹) := by
    rw [map_mul, map_mul, map_inv, hp'1]
    group
  have hstep : QuotientGroup.mk' (pCore 2 ↥M) x * QuotientGroup.mk' (pCore 2 ↥M) w *
      (QuotientGroup.mk' (pCore 2 ↥M) x)⁻¹ =
      QuotientGroup.mk' (pCore 2 ↥M) (x * w * x⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hstep, ← hmkw']
  exact mk_mem_imgQ hw'B

private theorem Sec6Hyp.isElemAbelian_imgQ_of_mem_sigmaSet (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) : IsElemAbelian 2 (imgQ M B) := by
  obtain ⟨g, rfl, -⟩ := hB
  exact ((Tim78.isElemAbelian_conjSubgroup hS.sec5.toRootHyp.toHyp.elem g).subgroupOf M).map _

theorem Sec6Hyp.card_imgQ_of_mem_sigmaSet (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) : Nat.card (imgQ M B) = Nat.card V := by
  rw [hS.card_imgQ_of_inf_Pc_eq_bot (hS.sec5.le_M_of_mem_sigmaSet hB).1
    (hS.sec5.inf_Pc_eq_bot hB)]
  obtain ⟨g, rfl, -⟩ := hB
  exact card_conjSubgroup g V

private theorem Sec6Hyp.oddCore_inf_imgQ_eq_bot (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) :
    (pPrimeCore 2 ↥(imgQ M (m0Of M V))).map (imgQ M (m0Of M V)).subtype ⊓ imgQ M B = ⊥ := by
  haveI : Finite (MBar M) := inferInstance
  let X : Subgroup (MBar M) := imgQ M (m0Of M V)
  let O : Subgroup (MBar M) := (pPrimeCore 2 ↥X).map X.subtype
  have hOcard : Nat.card O = Nat.card (pPrimeCore 2 ↥X) := Subgroup.card_subtype X _
  have hOcoprime : Nat.Coprime 2 (Nat.card O) := by
    rw [hOcard]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥X)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hS.isElemAbelian_imgQ_of_mem_sigmaSet hB).isPGroup
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (H := O) (K := imgQ M B) ?_)
  rw [hn]
  exact hOcoprime.symm.pow_right n

theorem Sec6Hyp.oddCore_le_centralizer_imgQ (hS : Sec6Hyp M V) {B : Subgroup G}
    (hB : B ∈ sigmaSet M V) :
    (pPrimeCore 2 ↥(imgQ M (m0Of M V))).map (imgQ M (m0Of M V)).subtype ≤
      Subgroup.centralizer (imgQ M B : Set (MBar M)) := by
  haveI : Finite (MBar M) := inferInstance
  let X : Subgroup (MBar M) := imgQ M (m0Of M V)
  let O : Subgroup (MBar M) := (pPrimeCore 2 ↥X).map X.subtype
  show O ≤ Subgroup.centralizer (imgQ M B : Set (MBar M))
  have hBelem := hS.isElemAbelian_imgQ_of_mem_sigmaSet hB
  have hBcard := hS.card_imgQ_of_mem_sigmaSet hB
  have hOcard : Nat.card O = Nat.card (pPrimeCore 2 ↥X) := Subgroup.card_subtype X _
  have hXO : X ≤ Subgroup.normalizer (O : Set (MBar M)) :=
    le_normalizer_map_subtype X (pPrimeCore 2 ↥X)
  have hdisj : O ⊓ imgQ M B = ⊥ := hS.oddCore_inf_imgQ_eq_bot hB
  refine CFSG.RankThree.GroupTheory.SteinbergBM.le_of_forall_inf_centralizer_le
    (p := 2) (B := imgQ M B) (V := O)
    (W := Subgroup.centralizer (imgQ M B : Set (MBar M))) ?_ ?_ ?_ ?_ ?_
  · exact (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)).mp hBelem
  · have h4 := hS.sec5.toRootHyp.four_le_card
    rw [hBcard]
    exact h4
  · rw [hOcard]
    exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥X))
  · exact (imgQ_mono (le_m0Of_of_mem_sigmaSet hB)).trans hXO
  · intro b hb hb1 o ho
    obtain ⟨hoO, hob⟩ := Subgroup.mem_inf.mp ho
    rw [Subgroup.mem_centralizer_iff] at hob
    rw [Subgroup.mem_centralizer_iff]
    have hoX : o ∈ X := Subgroup.map_subtype_le (H := X) (K := pPrimeCore 2 ↥X) hoO
    obtain ⟨x, -, hxo⟩ := mem_imgQ_iff.mp hoX
    obtain ⟨bb, hbbB, hbb⟩ := mem_imgQ_iff.mp hb
    have hbb1 : (bb : G) ≠ 1 := by
      intro h
      apply hb1
      rw [← hbb, show bb = 1 from Subtype.ext h]
      simp
    have hxb : QuotientGroup.mk' (pCore 2 ↥M) x * QuotientGroup.mk' (pCore 2 ↥M) bb =
        QuotientGroup.mk' (pCore 2 ↥M) bb * QuotientGroup.mk' (pCore 2 ↥M) x := by
      rw [hxo, hbb]
      exact ((Subgroup.mem_centralizer_iff.mp hob) b (Set.mem_singleton b)).symm
    intro z hz
    have hzb : z ∈ X := (imgQ_mono (le_m0Of_of_mem_sigmaSet hB)) hz
    have hzo : o * z * o⁻¹ ∈ imgQ M B := by
      rw [← hxo]
      exact hS.conj_mem_imgQ_of_commute hB hbbB hbb1 hxb hz
    have hcommO : o * z * o⁻¹ * z⁻¹ ∈ O := by
      have h1 : z * o⁻¹ * z⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hXO hzb) o⁻¹).mp (O.inv_mem hoO)
      simpa [mul_assoc] using O.mul_mem hoO h1
    have hcommB : o * z * o⁻¹ * z⁻¹ ∈ imgQ M B :=
      (imgQ M B).mul_mem hzo ((imgQ M B).inv_mem hz)
    have hbot : o * z * o⁻¹ * z⁻¹ ∈ (⊥ : Subgroup (MBar M)) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hcommO, hcommB⟩
    have h1 : o * z * o⁻¹ * z⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h2 : o * z * o⁻¹ = z := by
      simpa [mul_assoc] using congrArg (· * z) h1
    calc z * o = (o * z * o⁻¹) * o := by rw [h2]
      _ = o * z := by group

theorem Sec6Hyp.imgQ_m0Of_le_centralizer_oddCore (hS : Sec6Hyp M V) :
    imgQ M (m0Of M V) ≤ Subgroup.centralizer
      ((pPrimeCore 2 ↥(imgQ M (m0Of M V))).map (imgQ M (m0Of M V)).subtype :
        Set (MBar M)) := by
  let O : Subgroup (MBar M) :=
    (pPrimeCore 2 ↥(imgQ M (m0Of M V))).map (imgQ M (m0Of M V)).subtype
  have hle : m0Of M V ≤ ((Subgroup.centralizer (O : Set (MBar M))).comap
      (QuotientGroup.mk' (pCore 2 ↥M))).map M.subtype := by
    unfold m0Of
    refine iSup₂_le fun U hU => ?_
    intro x hxU
    have hxM : x ∈ M := (hS.sec5.le_M_of_mem_sigmaSet hU).1 hxU
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact Subgroup.le_centralizer_iff.mp (hS.oddCore_le_centralizer_imgQ hU) (mk_mem_imgQ hxU)
  intro z hz
  obtain ⟨x, hxM0, rfl⟩ := mem_imgQ_iff.mp hz
  obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp (hle hxM0)
  have hsy' : s = x := Subtype.ext hsy
  rwa [hsy'] at hs

end CFSG.RankThree.GF2n.Tim81

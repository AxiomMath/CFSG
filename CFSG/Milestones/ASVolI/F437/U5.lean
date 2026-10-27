module

public import CFSG.Milestones.ASVolI.F437.Deg
public import CFSG.Milestones.ASVolI.F431.BF436U5C
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F437.Syl2
public import CFSG.Milestones.ASVolI.F437.Top

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

section Weak

variable {G : Type} [Group G]

theorem burnsideF437_mem_zpowers_of_sq {z w : G} (hzz : z * z = 1) (hw : w ∈ Subgroup.zpowers z) :
    w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem burnsideF437_conj_mem_ctr {X : Subgroup G} {n u : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) (hu : u ∈ ctr X) : n * u * n⁻¹ ∈ ctr X := by
  obtain ⟨huX, huC⟩ := Subgroup.mem_inf.mp hu
  have hnX := Subgroup.mem_normalizer_iff.mp hn
  refine Subgroup.mem_inf.mpr ⟨(hnX u).mp huX, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at huC ⊢
  intro y hy
  have hy' : n⁻¹ * y * n ∈ X := by
    rw [hnX]
    simpa [mul_assoc] using hy
  have := huC _ hy'
  calc y * (n * u * n⁻¹) = n * ((n⁻¹ * y * n) * u) * n⁻¹ := by group
    _ = n * (u * (n⁻¹ * y * n)) * n⁻¹ := by rw [this]
    _ = n * u * n⁻¹ * y := by group

theorem burnsideF437_sylow_of_ctr_weakClosure [Finite G] {f z : G} {Tf M' : Subgroup G}
    (hTf : IsSylowTwoOf Tf (M' ⊓ Subgroup.centralizer ({f} : Set G)))
    (hz : z ∈ ctr Tf) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ M')
    (hfus : ∀ y ∈ ctr Tf, IsConj z y → y = z) :
    IsSylowTwoOf Tf (Subgroup.centralizer ({f} : Set G)) := by
  obtain ⟨R, hTfR, hR⟩ := exists_isSylowTwoOf_of_le (hTf.1.trans inf_le_right) hTf.2.1
  have hzT : z ∈ Tf := (Subgroup.mem_inf.mp hz).1
  have hW1p : IsPGroup 2 (Subgroup.zpowers z) :=
    hTf.2.1.to_le ((Subgroup.zpowers_le (H := Tf)).mpr hzT)
  have hne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hnorm : ∀ n ∈ R, n ∈ Subgroup.normalizer (Tf : Set G) →
      ∀ x ∈ Subgroup.zpowers z, n * x * n⁻¹ ∈ Subgroup.zpowers z := by
    intro n _ hn x hx
    have hnz : n * z * n⁻¹ = z :=
      hfus _ (burnsideF437_conj_mem_ctr hn hz) (isConj_iff.mpr ⟨n, rfl⟩)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hc : n * z ^ k * n⁻¹ = (n * z * n⁻¹) ^ k := by
      have := map_zpow (MulAut.conj n) z k
      simpa only [MulAut.conj_apply] using this
    rw [hc, hnz]
  have hcent' : ∀ w ∈ Subgroup.zpowers z, w ≠ 1 →
      Subgroup.centralizer ({w} : Set G) ≤ M' := by
    intro w hw hw1
    rcases burnsideF437_mem_zpowers_of_sq hzz hw with h | h
    · exact absurd h hw1
    · rw [h]; exact hcent
  have hRTf := CFSG.Quasithin.H13.F431.eq_of_weakly_closed hR hTfR hTf hW1p hne hnorm hcent'
  rw [hRTf] at hR
  exact hR

end Weak

section Data

variable {E : Type} [Group E]

structure burnsideF437_U5Data (Gp M₁ M₂ Tb : Subgroup E) (fb : E) : Prop where
  sylow : IsSylowTwoOf (Tb ⊓ Subgroup.centralizer ({fb} : Set E))
    (M₁ ⊓ Subgroup.centralizer ({fb} : Set E))
  Z_ctr : ctr (oPPrime 2 (Gp ⊓ M₁)) ≤ ctr Tb
  Z_le : ctr (oPPrime 2 (Gp ⊓ M₁)) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))
  weak : ∀ y ∈ ctr (Tb ⊓ Subgroup.centralizer ({fb} : Set E)),
    y ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → ∀ x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)), x ≠ 1 →
      (∃ g ∈ Gp, g * x * g⁻¹ = y) → y = x

end Data

@[expose] def burnsideF437_U5DataInput : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂),
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) → ∀ fb : E, fb ∈ Tb →
      burnsideF437_Inv Gp M₁ M₂ fb → hyp.toHypF_4_4g.chart.IsGraphInv fb →
        burnsideF437_U5Data Gp M₁ M₂ Tb fb

@[expose] def burnsideF437_F435U5 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 .U5 1 Gp M₁ M₂ β ε z →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      IsConj (bM β ε i) (bM β ε j) → ∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)

theorem burnsideF437_F435U5_of_F_4_35 (h : F_4_35) : burnsideF437_F435U5 :=
  fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp i j hi hj hi1 hj1 hii hjj hc =>
    (h .U5 1 E Gp M₁ M₂ Y β M ε z hyp i j hi hj hi1 hj1 hii hjj).mpr hc

section U5

set_option linter.unusedSectionVars false

theorem burnsideF437_sylowInputDeg_U5 (hcls : burnsideF437_ClassInputDeg .U5 1)
    (h35 : burnsideF437_F435U5) (hd : burnsideF437_U5DataInput) :
    burnsideF437_SylowInputDeg .U5 1 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp Tb hTb fb hfbT hfbS hsq hFG hsyl
  left
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hgraph : hyp.amalgam.toHypF_4_4g.chart.IsGraphInv (fb : E) := by
    rcases hFG with h | h
    · exact absurd rfl (burnsideF437_field_kind h).2
    · exact h
  have hfG : (fb : E) ∉ Gp := burnsideF437_not_mem_Gp hsyl (fun h => hfbS h.1) hsq
  have hinv : burnsideF437_Inv Gp M₁ M₂ (fb : E) := ⟨fb.2, hfG, hsq, hsyl⟩
  have D := hd E Gp M₁ M₂ hyp.amalgam Tb hTb (fb : E) hfbT hinv hgraph
  set b := burnsideF4d_bOne β ε with hbdef
  have hb : Function.Injective b := burnsideF4j_bOne_injective hyp
  have hfM1 : (fb : E) ∈ M₁ := fb.2.1
  have hTb12 : Tb ≤ M₁ ⊓ M₂ := hTb.1
  have hTb1 : Tb ≤ M₁ := hTb12.trans inf_le_left
  have hTf1 : Tb ⊓ Subgroup.centralizer ({(fb : E)} : Set E) ≤ M₁ := inf_le_left.trans hTb1
  have hS12 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hTf : imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M) =
      subImg b (Tb ⊓ Subgroup.centralizer ({(fb : E)} : Set E)) := by
    rw [burnsideF437_imB_eq β ε hTb12, burnsideF437_bM_eq,
      CFSG.Quasithin.H13.F431.L3.subImg_inf_centralizer b hb hfM1]
  have hM1f : MiOne β ε ⊓ Subgroup.centralizer ({bM β ε fb} : Set M) =
      subImg b (M₁ ⊓ Subgroup.centralizer ({(fb : E)} : Set E)) := by
    rw [burnsideF437_MiOne_eq, burnsideF437_bM_eq,
      CFSG.Quasithin.H13.F431.L3.subImg_inf_centralizer b hb hfM1]
  have hzZ : z ∈ ctr (oPPrime 2 (GiOne Gp β ε)) := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hzZ
  obtain ⟨zb, hzbM, hzbZ, hzb⟩ := mem_subImg.mp hzZ
  have hzbS : zb ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := D.Z_le hzbZ
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    apply hyp.z_inv.1
    rw [← hzb]
    exact map_one b
  have hzbb : zb * zb = 1 := by
    have h1 : b (⟨zb, hzbM⟩ * ⟨zb, hzbM⟩) = b 1 := by
      rw [map_mul, hzb, map_one]
      exact hyp.z_inv.2
    have := congrArg (fun t : ↥M₁ => (t : E)) (hb h1)
    simpa using this
  rw [hTf]
  refine burnsideF437_sylow_of_ctr_weakClosure (M' := MiOne β ε) ?_ ?_ hyp.z_inv.1 hyp.z_inv.2
    hyp.hb ?_
  · rw [hM1f]
    exact (burnsideF4j_isSylow_subImg_iff b hb hTf1 inf_le_left).mpr D.sylow
  ·
    rw [burnsideF4j_ctr_subImg b hb hTf1, ← hzb]
    refine mem_subImg_of_mem b hzbM ?_
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp (D.Z_ctr hzbZ)
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzT, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hzC) _ hfbT).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp hzC) t (Subgroup.mem_inf.mp ht).1
  ·
    intro y hy hzy
    rw [burnsideF4j_ctr_subImg b hb hTf1] at hy
    obtain ⟨yb, hybM, hybW, rfl⟩ := mem_subImg.mp hy
    have hybT : yb ∈ Tb := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hybW).1).1
    have hyb12 : yb ∈ M₁ ⊓ M₂ := hTb12 hybT
    obtain ⟨c, hc⟩ := isConj_iff.mp hzy
    have hyy : b ⟨yb, hybM⟩ * b ⟨yb, hybM⟩ = 1 := by
      rw [← hc]
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hyp.z_inv.2]; group
    have hybb : yb * yb = 1 := by
      have h1 : b (⟨yb, hybM⟩ * ⟨yb, hybM⟩) = b 1 := by rw [map_mul, hyy, map_one]
      have := congrArg (fun t : ↥M₁ => (t : E)) (hb h1)
      simpa using this
    by_cases hyS : yb ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))
    ·
      let i : ↥(M₁ ⊓ M₂) := ⟨zb, hS12 hzbS⟩
      let j : ↥(M₁ ⊓ M₂) := ⟨yb, hyb12⟩
      have hbi : bM β ε i = z := by rw [burnsideF437_bM_eq]; exact hzb
      have hbj : bM β ε j = b ⟨yb, hybM⟩ := burnsideF437_bM_eq β ε j
      have hi1 : i ≠ 1 := fun h => hzb1 (congrArg Subtype.val h)
      have hj1 : j ≠ 1 := by
        intro h
        apply hyp.z_inv.1
        have h1 : b ⟨yb, hybM⟩ = 1 := by rw [← hbj, h, map_one]
        rw [← hc] at h1
        have := congrArg (fun t => c⁻¹ * t * c) h1
        simpa [mul_assoc] using this
      have hii : i * i = 1 := Subtype.ext hzbb
      have hjj : j * j = 1 := Subtype.ext hybb
      have hconj : IsConj (bM β ε i) (bM β ε j) := by rw [hbi, hbj]; exact hzy
      have hG := h35 E Gp M₁ M₂ Y β M ε z hyp i j hzbS hyS hi1 hj1 hii hjj hconj
      have hyz : yb = zb := D.weak yb hybW hyS zb hzbZ hzb1 hG
      rw [← hzb]
      exact congrArg b (Subtype.ext hyz)
    ·
      exfalso
      let j : ↥(M₁ ⊓ M₂) := ⟨yb, hyb12⟩
      have hbj : bM β ε j = b ⟨yb, hybM⟩ := burnsideF437_bM_eq β ε j
      rcases hcls E Gp M₁ M₂ hyp.amalgam Tb hTb yb hybT hyS hybb with h | h | h
      · exact (burnsideF437_field_kind h).2 rfl
      · refine burnsideF4m_F_4_36 .U5 1 E Gp M₁ M₂ Y β M ε z hyp (Or.inr rfl) rfl Tb hTb j hybT
          h.1 ?_
        rw [hbj]
        exact hzy
      · exact absurd h.1 (by decide)

theorem burnsideF437_F_4_37_of_U4_U5 (hU4 : burnsideF437_F437KindDeg .U4 1)
    (hcls5 : burnsideF437_ClassInputDeg .U5 1) (hfix5 : burnsideF437_FixedInputDeg .U5 1)
    (h35 : burnsideF437_F435U5) (hd : burnsideF437_U5DataInput) : F_4_37 :=
  burnsideF437_F_4_37_of_U hU4
    (burnsideF437_F437KindDeg_of ChF.nativeChartCompatibility hcls5 hfix5
      (burnsideF437_sylowInputDeg_U5 hcls5 h35 hd))

end U5

end CFSG.ASVolI

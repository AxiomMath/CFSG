module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofINorm
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155INorm

open Proof153Twin2 Proof153Twin3

theorem nonempty_quot_equiv_img {A M : Subgroup G} [(ker148 A M).Normal] (hAM : A ≤ M)
    {X D : Subgroup G} (hX : X ∈ thetaComponentsIn M) (hXD : X ≤ D) :
    Nonempty (↥X ⧸ CFSG.pPrimeCore 3 ↥X ≃* ↥((img148 A M X).subgroupOf (img148 A M D))) := by
  have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
  obtain ⟨hXH, hX₁⟩ := subgroupOf_mem_thetaComponents hMA hX
  have hker := ker148_eq_pPrimeCore hAM
  obtain ⟨e₂⟩ := nonempty_quot_equiv_map (H := ↥(M ⊔ A)) hker hX₁.2.1
  set e : ↥X ≃* ↥(X.subgroupOf (M ⊔ A)) := (Subgroup.subgroupOfEquivOfLe hXH).symm with he
  exact ⟨(QuotientGroup.congr (CFSG.pPrimeCore 3 ↥X)
    (CFSG.pPrimeCore 3 ↥(X.subgroupOf (M ⊔ A))) e
    (CFSG.pPrimeCore_map_iso 3 e)).trans
    (e₂.trans (Subgroup.subgroupOfEquivOfLe (img148_mono hXD)).symm)⟩

theorem hasFaithfulE9_of_case1487 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY A)
    (hAM : A ≤ M) {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A)) (hXM : X ∈ thetaComponentsIn M) :
    letI := ker148_normal hM.2
    Case1487 A (lB A) M → HasFaithfulE9 X := by
  intro h7
  let := ker148_normal hM.2
  have hXM' : X ≤ M := (mem_thetaComponentsIn_iff.mp hXM).1
  obtain ⟨heq149, -, -⟩ := h149 M hM
  have hX0Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hXD : X ≤ deltaZero A (lB A) M := (le_oPrimeResidualOf_delta hX hXM').trans hX0Δ
  set U := (img148 A M X).subgroupOf (img148 A M (deltaZero A (lB A) M)) with hUdef
  have hU : U.IsSubnormal := Proof153Twin3.isSubnormal_img_subgroupOf hAM hXM
  obtain ⟨eY⟩ := nonempty_quot_equiv_img hAM hXM hXD
  have hUq : IsQuasisimple ↥U := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY
    (Proof1515.isQuasisimple_quot_pPrimeCore hX)
  obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, _, _, -, -, -, -, hJ₁, hJ₂, hsup,
    -, hcomm, -, -, -, -, hP₁, hP₂, -, -⟩ := h7
  have hAab : IsMulCommutative ↥A := h.isElemAbelian.1
  have hBc : IsMulCommutative ↥(img148 A M A) := ⟨⟨fun x y => img148_comm hAab x y⟩⟩
  have hBD : img148 A M A ≤
      Subgroup.normalizer (img148 A M (deltaZero A (lB A) M) : Set _) :=
    Sec14.img148_le_normalizer (Sec16.le_normalizer_deltaZero (A := A) (LB := lB A) M)
  have hJ₁M : J₁ ≤ M ⊔ A := hJ₁.trans (inf_le_right.trans le_sup_left)
  have hJ₂M : J₂ ≤ M ⊔ A := hJ₂.trans (inf_le_right.trans le_sup_left)
  rw [img148_sup hJ₁M le_sup_right] at hP₁
  rw [img148_sup hJ₂M le_sup_right] at hP₂
  have hJ₁D : img148 A M J₁ ≤ img148 A M (deltaZero A (lB A) M) := hsup ▸ le_sup_left
  have hJ₂D : img148 A M J₂ ≤ img148 A M (deltaZero A (lB A) M) := hsup ▸ le_sup_right
  obtain ⟨hZ, hE9⟩ : Subgroup.center ↥U = ⊥ ∧
      ∃ E : Subgroup ↥U, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    rcases le_or_le_of_isQuasisimple hsup hcomm hU hUq with h1 | h2
    · exact center_eq_bot_and_e9_of_le_factor hBc hBD hJ₁D hP₁ hU hUq h1
    · exact center_eq_bot_and_e9_of_le_factor hBc hBD hJ₂D hP₂ hU hUq h2
  exact hasFaithfulE9_of_quot_pPrimeCore eY hZ hE9

theorem map_conj_eq_of_item148
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) {X M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G))
    (hX : X ∈ scriptY4 A (lB A)) (hXM : X ∈ thetaComponentsIn M) {t : G} (ht : t ∈ M) {k : ℕ}
    (htk : t ^ 3 ^ k = 1) : X.map (MulAut.conj t).toMonoidHom = X := by
  classical
  by_cases hF : HasFaithfulE9 X
  · exact Proof155w3.map_conj_eq_of_hasE9KerThree_of_mem h hM hXM
      (hasE9KerThree_of_hasFaithfulE9 hF) ht htk
  · obtain ⟨hXM', hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
    have hMY : M ∈ scriptY A := hM2.1
    let := ker148_normal hMY.2
    by_contra hne
    set X₂ := X.map (MulAut.conj t).toMonoidHom with hX₂def
    set X₃ := X.map (MulAut.conj (t ^ 2)).toMonoidHom with hX₃def
    have hodd : Odd (orderOf t) := by
      have hdvd : orderOf t ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one htk
      exact (Odd.pow (by decide)).of_dvd_nat hdvd
    obtain ⟨m, hm⟩ := hodd
    have htsq : (t ^ 2) ^ (m + 1) = t := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf t + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have h12 : X ≠ X₂ := fun he => hne (he.trans hX₂def).symm
    have h13 : X ≠ X₃ := by
      intro he
      apply hne
      have ht2N : t ^ 2 ∈ Subgroup.normalizer (X : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (he.trans hX₃def).symm
      have htN : t ∈ Subgroup.normalizer (X : Set G) := by
        have h := pow_mem ht2N (m + 1)
        rwa [htsq] at h
      exact Late.map_conj_eq_of_mem_normalizer htN
    have h23 : X₂ ≠ X₃ := by
      intro he
      apply h12
      have h := congrArg (fun S : Subgroup G => S.map (MulAut.conj t⁻¹).toMonoidHom) he
      rw [hX₂def, hX₃def, Late.map_conj_map_conj, Late.map_conj_map_conj,
        show t⁻¹ * t = 1 by group, show t⁻¹ * (t ^ 2) = t by group,
        Late.map_conj_one] at h
      exact h.trans hX₂def.symm
    have hX₂θ : X₂ ∈ thetaComponentsIn M :=
      map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer ht) hXM
    have hX₃θ : X₃ ∈ thetaComponentsIn M :=
      map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer (pow_mem ht 2)) hXM
    obtain ⟨heq149, -, -⟩ := h149 M hMY
    have hX0Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M := by
      rw [heq149]
      exact (Sec14.oPrimeResidualOf_le_self 3 _).trans
        (Sec14.inSubgroup_oResidual_le_self 2 _)
    have hMX0 : M ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M) : Set G) :=
      normalizer_le_normalizer_oPrimeResidualOf_delta h149 hMY
    have hX0 : X ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
      le_oPrimeResidualOf_delta hX hXM'
    have hXD : X ≤ deltaZero A (lB A) M := hX0.trans hX0Δ
    have hX₂0 : X₂ ≤ oPrimeResidualOf 3 (delta A (lB A) M) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMX0 ht) x).mp (hX0 hx)
    have hX₂D : X₂ ≤ deltaZero A (lB A) M := hX₂0.trans hX0Δ
    have hX₃0 : X₃ ≤ oPrimeResidualOf 3 (delta A (lB A) M) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMX0 (pow_mem ht 2)) x).mp (hX0 hx)
    have hX₃D : X₃ ≤ deltaZero A (lB A) M := hX₃0.trans hX0Δ
    have hDM : deltaZero A (lB A) M ≤ M ⊔ A := (deltaZero_le M).trans le_sup_left
    have hcX₂ : ⁅X, X₂⁆ ≤ pPrimeCoreOf 3 M :=
      (commutator_le_of_mem_thetaComponentsIn hXM hX₂θ h12).trans
        (map_aschbacherSolvableCore_le_pPrimeCoreOf M)
    have hcX₃ : ⁅X, X₃⁆ ≤ pPrimeCoreOf 3 M :=
      (commutator_le_of_mem_thetaComponentsIn hXM hX₃θ h13).trans
        (map_aschbacherSolvableCore_le_pPrimeCoreOf M)
    have hc₂₃ : ⁅X₂, X₃⁆ ≤ pPrimeCoreOf 3 M :=
      (commutator_le_of_mem_thetaComponentsIn hX₂θ hX₃θ h23).trans
        (map_aschbacherSolvableCore_le_pPrimeCoreOf M)
    haveI : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX
    haveI : Group.IsPerfect ↥X₂ := Group.IsPerfect.map _
    haveI : Group.IsPerfect ↥X₃ := Group.IsPerfect.map _
    obtain ⟨x, hxX, hx3, y, hyX, hxy⟩ :=
      Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hX
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hxy
      rw [one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    have hconj1 : ∀ g : G, MulAut.conj g x ≠ 1 := fun g h1 =>
      hx1 ((MulAut.conj g).injective (h1.trans (map_one _).symm))
    have hconj3 : ∀ g : G, (MulAut.conj g x) ^ 3 = 1 := fun g => by
      rw [← map_pow, hx3, map_one]
    exact false_of_triple_of_item148 h148 hMY
      (fun h7 => hF (hasFaithfulE9_of_case1487 h h149 hMY hAM hX hXM h7))
      _ _ _
      (isSubnormal_img_subgroupOf hAM hXM) (isSubnormal_img_subgroupOf hAM hX₂θ)
      (isPerfect_img_subgroupOf hXD hDM) (isPerfect_img_subgroupOf hX₂D hDM)
      (isPerfect_img_subgroupOf hX₃D hDM)
      (img_subgroupOf_ne_bot hXD hDM hxX hx3 hx1)
      (img_subgroupOf_ne_bot hX₂D hDM ⟨x, hxX, rfl⟩ (hconj3 t) (hconj1 t))
      (img_subgroupOf_ne_bot hX₃D hDM ⟨x, hxX, rfl⟩ (hconj3 (t ^ 2)) (hconj1 (t ^ 2)))
      (commutator_img_subgroupOf_eq_bot hXD hX₂D hDM hcX₂)
      (commutator_img_subgroupOf_eq_bot hXD hX₃D hDM hcX₃)
      (commutator_img_subgroupOf_eq_bot hX₂D hX₃D hDM hc₂₃)

theorem oPrimeResidualOf_le_normalizer_of_item148
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {X M H : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G))
    (hX : X ∈ scriptY4 A (lB A)) (hXM : X ∈ thetaComponentsIn M) (hHM : H ≤ M) :
    oPrimeResidualOf 3 H ≤ Subgroup.normalizer (X : Set G) := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro t ⟨htH, k, htk⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_of_item148 h h148 h149 hM hX hXM (hHM htH) htk)

end Proof155INorm

open Proof155INorm

theorem step155INormX2W_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) : Step155INormX2W A c L := by
  intro h X K Y M T P hC _ _ hE _ _
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hMX : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G) := by
    refine ⟨hC.mem_m.1, ?_⟩
    have hAY : (A ⊔ Y : Subgroup G) ≤ M := hC.mem_m.2
    exact fun z hz => (sup_le (hXY.trans (le_sup_right.trans hAY))
      (le_sup_left.trans hAY)) hz
  exact oPrimeResidualOf_le_normalizer_of_item148 h h148 h149 hMX hX4 hE.mem_x (delta_le M)

theorem step155INormX2RkW_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) : Step155INormX2RkW A c L := by
  intro h X K Y M T P hC hmax hab hE hW1 hbl _
  exact step155INormX2W_of h148 h149 h X K Y M T P hC hmax hab hE hW1 hbl

theorem step155INormX2RkWR_of
    (h148 : Item148R) (h149 : Sec16.Item149S14) : Step155INormX2RkWR := by
  exact fun G _ _ A c L hR =>
    step155INormX2RkW_of (h148 G A c L hR) (h149 G A c L hR.toSec14Std)

end CFSG.RankThree.PartTwo.Sec15

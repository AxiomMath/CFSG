module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaCompY
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16.KStep166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

theorem commutatorElement_eq_of_div_mem_centralizer {G : Type*} [Group G] {H : Subgroup G}
    {a b h : G} (hbN : b ∈ Subgroup.normalizer (H : Set G))
    (hab : a / b ∈ Subgroup.centralizer (H : Set G)) (hh : h ∈ H) :
    ⁅h, a⁆ = ⁅h, b⁆ := by
  let c : G := a / b
  have ha : a = c * b := by
    simp [c, div_eq_mul_inv, mul_assoc]
  have hcH : c ∈ Subgroup.centralizer (H : Set G) := hab
  have hhc : h * c = c * h :=
    Subgroup.mem_centralizer_iff.mp hcH h hh
  have hcommH : ⁅h, b⁆ ∈ H := by
    have hzb : Subgroup.zpowers b ≤ Subgroup.normalizer (H : Set G) :=
      Subgroup.zpowers_le.mpr hbN
    have hrev : ⁅Subgroup.zpowers b, H⁆ ≤ H :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hzb
    have hle : ⁅H, Subgroup.zpowers b⁆ ≤ H := by
      simpa [Subgroup.commutator_comm] using hrev
    exact hle (Subgroup.commutator_mem_commutator hh (Subgroup.mem_zpowers b))
  have hkc : ⁅h, b⁆ * c = c * ⁅h, b⁆ :=
    Subgroup.mem_centralizer_iff.mp hcH ⁅h, b⁆ hcommH
  rw [ha]
  simp only [commutatorElement_def, mul_inv_rev]
  calc
    h * (c * b) * h⁻¹ * (b⁻¹ * c⁻¹) =
        (h * c) * b * h⁻¹ * b⁻¹ * c⁻¹ := by group
    _ = (c * h) * b * h⁻¹ * b⁻¹ * c⁻¹ := by rw [hhc]
    _ = c * (h * b * h⁻¹ * b⁻¹) * c⁻¹ := by group
    _ = h * b * h⁻¹ * b⁻¹ := by rw [← commutatorElement_def, ← hkc]; group

theorem commutator_commutator_le {G : Type*} [Group G] {P Q O W X : Subgroup G} {c d : G}
    (hQP : Q ≤ P) (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hdP : d ∈ Subgroup.normalizer (P : Set G)) (hcO : c ∈ Subgroup.normalizer (O : Set G))
    (hdO : d ∈ Subgroup.normalizer (O : Set G)) (hWO : W ≤ Subgroup.normalizer (O : Set G))
    (hWc : W ≤ Subgroup.centralizer {c}) (hQ : Q ≤ W ⊔ O)
    (hOX : O ≤ Subgroup.normalizer (X : Set G)) (hdX : d ∈ X) :
    ⁅⁅Q, Subgroup.zpowers c⁆, Subgroup.zpowers d⁆ ≤ P ⊓ (X ⊓ O) := by
  have ha : ⁅W ⊔ O, Subgroup.zpowers c⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have hx' : x ∈ (W : Set G) * (O : Set G) := by
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right W O hWO]
    rw [Set.mem_mul] at hx'
    obtain ⟨w, hw, o, ho, rfl⟩ := hx'
    have hcg : g ∈ Subgroup.normalizer (O : Set G) := Subgroup.zpowers_le.mpr hcO hg
    have hwg : Commute w g := by
      have hcCw : c ∈ Subgroup.centralizer ({w} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hWc hw)).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.zpowers_le.mpr hcCw hg)).symm
    have hoO : ⁅o, g⁆ ∈ O := by
      rw [commutatorElement_def]
      have h : g * o⁻¹ * g⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp hcg o⁻¹).mp (O.inv_mem ho)
      simpa [mul_assoc] using O.mul_mem ho h
    rw [commutatorElement_mul_left_eq_conj_mul, hwg.commutator_eq, mul_one]
    exact (Subgroup.mem_normalizer_iff.mp (hWO hw) ⁅o, g⁆).mp hoO
  have hR_le_O : ⁅Q, Subgroup.zpowers c⁆ ≤ O :=
    (Subgroup.commutator_mono hQ le_rfl).trans ha
  have hR_le_P : ⁅Q, Subgroup.zpowers c⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    rw [commutatorElement_def]
    have h : g * x⁻¹ * g⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hcP hg) x⁻¹).mp
        (P.inv_mem (hQP hx))
    simpa [mul_assoc] using P.mul_mem (hQP hx) h
  rw [Subgroup.commutator_le]
  intro r hr g hg
  have hrP : r ∈ P := hR_le_P hr
  have hrO : r ∈ O := hR_le_O hr
  have hgP : g ∈ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hdP hg
  have hgO : g ∈ Subgroup.normalizer (O : Set G) := Subgroup.zpowers_le.mpr hdO hg
  have hgX : g ∈ X := Subgroup.zpowers_le.mpr hdX hg
  have hrN : r ∈ Subgroup.normalizer (X : Set G) := hOX hrO
  have hmemP : ⁅r, g⁆ ∈ P := by
    rw [commutatorElement_def]
    have h : g * r⁻¹ * g⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hgP r⁻¹).mp (P.inv_mem hrP)
    simpa [mul_assoc] using P.mul_mem hrP h
  have hmemO : ⁅r, g⁆ ∈ O := by
    rw [commutatorElement_def]
    have h : g * r⁻¹ * g⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hgO r⁻¹).mp (O.inv_mem hrO)
    simpa [mul_assoc] using O.mul_mem hrO h
  have hmemX : ⁅r, g⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hrN g).mp hgX) (X.inv_mem hgX)
  exact ⟨hmemP, hmemX, hmemO⟩

lemma pPrimeCoreOf_le_normalizer_of_thetaComponentsIn {G : Type} [Group G] [Finite G]
    {H X : Subgroup G} (hX : X ∈ thetaComponentsIn H)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6))) :
    pPrimeCoreOf 3 H ≤ Subgroup.normalizer (X : Set G) := by
  have hXH : X ≤ H := (mem_thetaComponentsIn_iff.mp hX).1
  have hXin : X.subgroupOf H ∈ thetaComponents 3 H := (mem_thetaComponentsIn_iff.mp hX).2
  have hUs : (CFSG.pPrimeCore 3 ↥H).IsSubnormal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)).isSubnormal
  rcases CFSG.RankThree.GroupTheory.theta_component_subnormal_subgroup_dichotomy
    Nat.prime_three hXin hUs with hle | ⟨hnorm, -⟩
  ·
    exfalso
    have hXO_le : X ≤ pPrimeCoreOf 3 H := by
      have hmap := Subgroup.map_mono (f := H.subtype) hle
      rw [Subgroup.map_subgroupOf_eq_of_le hXH] at hmap
      simpa [pPrimeCoreOf] using hmap
    have hXO : X ⊓ pPrimeCoreOf 3 H = inSubgroup (aschbacherSolvableCore 3) X := by
      simpa [inSubgroup] using ThetaCompY.inf_pPrimeCoreOf_eq hX hT
    have hθX_eq_X : inSubgroup (aschbacherSolvableCore 3) X = X := by
      rw [← hXO]
      exact inf_eq_left.mpr hXO_le
    have hFtop : aschbacherSolvableCore 3 ↥X = ⊤ := by
      apply Subgroup.map_subtype_inj.mp
      have hmap : (aschbacherSolvableCore 3 ↥X).map X.subtype = X := by
        simpa [inSubgroup] using hθX_eq_X
      rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
    let T := ↥X ⧸ aschbacherSolvableCore 3 ↥X
    have hTsub : Subsingleton (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
      rw [hFtop]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton T := hTsub
    have hcardT : Nat.card T = 1 :=
      Nat.card_of_subsingleton (Classical.arbitrary T)
    have h3 : 3 ∣ Nat.card T := by
      have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.center T)
      rwa [show Nat.card (Subgroup.center T) = 3 from hT.1] at hdvd
    rw [hcardT] at h3
    exact absurd h3 Nat.prime_three.not_dvd_one
  · have hmap := Subgroup.map_mono (f := H.subtype) hnorm
    have hle_norm := Subgroup.le_normalizer_map (f := H.subtype) (H := X.subgroupOf H)
    rw [Subgroup.map_subgroupOf_eq_of_le hXH] at hle_norm
    exact hmap.trans hle_norm

lemma sup_pPrimeCoreOf_lB_le_centralizer {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} {x : G}
    (hxA : x ∈ A) (hxB : x ∈ B) :
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ lB A B ≤
      Subgroup.centralizer ({x} : Set G) := by
  refine sup_le ?_ ?_
  · refine (pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G))).trans ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA)
  · refine (lB_le_centralizer A B).trans ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxB)

end CFSG.RankThree.PartTwo.Sec16.KStep166

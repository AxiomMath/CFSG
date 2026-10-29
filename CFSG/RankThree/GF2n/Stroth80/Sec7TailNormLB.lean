module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec7NormLB'Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0

theorem sec7_CN_pgroup_bar [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) :
    IsPGroup 2 ↥(bar M Q (hc.CN t)) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRne := sec7_Rt_ne_LB hc hs
  have hN2 : IsPGroup 2 ↥(hc.CN t) := hc.isPGroup_CN_of_311 h34 hs.toSec5
    (h311a G M Q Z B hc n hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen t ht
      hs.toSec5.notQ hRne)
  exact endg_N_pgroup_bar hc ht hN2

theorem exists_normalizer_LB_not_normalizer_Z0 (h710 : Stroth710Statement)
    (hNC : Sec7ConjStatement) (hNC4 : Sec7ConjOm4Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      ν ∉ Subgroup.normalizer (Z0 : Set G) := by
  obtain ⟨g, hg, hgL, hgne⟩ := h710 G M Q Z B hc n t hs Z0 hZ0
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hex : ∃ z ∈ Z0, g * z * g⁻¹ ∉ Z0 := by
    by_contra hall
    push Not at hall
    apply hgne
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_conjSubgroup])
    rw [mem_conjSubgroup] at hx
    have h1 := hall (g⁻¹ * x * g) hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  obtain ⟨z, hz, hgz⟩ := hex
  have hzR : z ∈ Rt M (LB M Q B) t := hZ0.le hz
  have hzM : z ∈ M := hc.Rt_le_M t hzR
  have hxL : g * z * g⁻¹ ∈ LB M Q B := by
    have : g * z * g⁻¹ ∈ conjSubgroup g Z0 := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hz
    exact hgL this
  have hxM : g * z * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hzM) (M.inv_mem hg)
  have hconj : ConjMod M Q z (g * z * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
  obtain ⟨ν, hνM, hνL, hνQ⟩ : ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      g * z * g⁻¹ * (ν * z * ν⁻¹)⁻¹ ∈ Q := by
    by_cases hom : OmegaMinusNat hc t 2
    · exact hNC4 G M Q Z B hc n t hs hom Z0 hZ0 z hz _ hxL hconj
    · exact hNC G M Q Z B hc n t hs hom Z0 hZ0 z hz _ hxL hconj
  refine ⟨ν, hνM, hνL, ?_⟩
  intro hν
  apply hgz
  have hνz : ν * z * ν⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hν z).mp hz
  have e : g * z * g⁻¹ = (g * z * g⁻¹ * (ν * z * ν⁻¹)⁻¹) * (ν * z * ν⁻¹) := by group
  rw [e]
  exact Z0.mul_mem (hQZ0 hνQ) hνz

theorem sec7NormLB'_of_710 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h710 : Stroth710Statement) (hNC : Sec7ConjStatement) (hNC4 : Sec7ConjOm4Statement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) : Sec7NormLB'Statement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hMA hTI hF hle
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQLB : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  obtain ⟨ν, hνM, hνL, hνZ⟩ := exists_normalizer_LB_not_normalizer_Z0 h710 hNC hNC4 hc hs hZ0
  have hconf := hc.tiConfig hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hMA hTI hF
  haveI hnormH := hc.normal_bar_H0
  have hHn : ∀ x : Mbar M Q, x ∈ Subgroup.normalizer
      ((bar M Q (H0 M Z) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hNL := hc.bar_CN_le_normalizer h34 hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen ht
  have hY : Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) ⊓
      bar M Q (H0 M Z) ≤ NormIn (bar M Q (H0 M Z)) (bar M Q Z0) := by
    intro x hx
    obtain ⟨hxL, hxH⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hxH
    have hyL : (y : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      mem_normalizer_of_mk_mem_normalizer_bar hQLB hc.LB_le_M y hxL
    have hyK : (y : G) ∈ NormH0 M Z Z0 := hle (Subgroup.mem_inf.mpr ⟨hyH, hyL⟩)
    exact ⟨hxH, mk_mem_normalizer_bar_of_normalizer hQZ0 y (Subgroup.mem_inf.mp hyK).2⟩
  have key := hconf.refined_frattini hHn (L := bar M Q (LB M Q B)) hNL hY
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⟨ν, hνM⟩ ∈ Subgroup.normalizer
      ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) :=
    mk_mem_normalizer_bar_of_normalizer hQLB ⟨ν, hνM⟩ hνL
  exact hνZ (mem_normalizer_of_mk_mem_normalizer_bar hQZ0 hZ0M ⟨ν, hνM⟩ (key h1))

end CFSG.RankThree.GF2n.Stroth80

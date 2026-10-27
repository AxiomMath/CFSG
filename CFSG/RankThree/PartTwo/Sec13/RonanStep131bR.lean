module

import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.Implications

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Aux

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

private theorem centralizer_le_of_mem_zpowers {c y : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hy : y ∈ Subgroup.zpowers c) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hdvd : orderOf y ∣ 3 := by
    simpa [Nat.card_zpowers, hco] using Subgroup.orderOf_dvd_natCard _ hy
  have hyo : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_
    simp [Nat.card_zpowers, hco, hyo]
  have hcy : c ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers c
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcy
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← hk]
  exact (Commute.zpow_right (show Commute x y from hx) k).eq

private theorem le_normalizer_centralizer_inf {E : Subgroup G} {a c : G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcE : c ∈ E)
    (hcomm : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) :
    E ≤ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro e he d hd
  obtain ⟨hda, hdc⟩ := Subgroup.mem_inf.mp hd
  rw [Subgroup.mem_centralizer_singleton_iff] at hda hdc
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨z, hzc, hw⟩ : ∃ z ∈ Subgroup.zpowers c, e⁻¹ * a * e = z * a :=
      ⟨(a * e⁻¹ * a⁻¹ * e⁻¹⁻¹)⁻¹, Subgroup.inv_mem _ (hcomm e⁻¹ (Subgroup.inv_mem _ he)), by group⟩
    have hcd : c ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hdc.symm
    have hzd : z * d = d * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hcd hzc)
    have hwd : (e⁻¹ * a * e) * d = d * (e⁻¹ * a * e) := by
      rw [hw]
      calc z * a * d = z * (a * d) := mul_assoc _ _ _
        _ = z * (d * a) := by rw [hda]
        _ = (z * d) * a := (mul_assoc _ _ _).symm
        _ = (d * z) * a := by rw [hzd]
        _ = d * (z * a) := mul_assoc _ _ _
    calc e * d * e⁻¹ * a = e * (d * (e⁻¹ * a * e)) * e⁻¹ := by group
      _ = e * ((e⁻¹ * a * e) * d) * e⁻¹ := by rw [hwd]
      _ = a * (e * d * e⁻¹) := by group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hec : Commute e c := hEc e he c hcE
    have hdc' : Commute d c := hdc
    exact ((hec.mul_left hdc').mul_left hec.inv_left).eq

private theorem odd_card_theta_inf {E : Subgroup G} {a c : G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hE : E ∉ partTwoE G)
    (hcE : c ∈ E) (hcomm : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G))) := by
  set D : Subgroup G := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)
    with hD
  have hED : E ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_centralizer_inf (fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEe hx hy) hcE
      hcomm
  have hEN : E ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) D : Subgroup G) : Set G) :=
    Sec21.le_normalizer_theta hED
  have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) D)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Sec11.not_three_dvd_card_inSubgroup_theta _)
  by_contra hodd
  have h2 : 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) D) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨S, hSN, hS1⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    3 2 Nat.prime_three Nat.prime_two E _ (CFSG.Open.IsElemAbelian.isPGroup hEe) hEN hcop h2
  exact hE ⟨hEe, hE27, _, hS1, S.isPGroup'.map _, hSN⟩

private theorem odd_card_theta_inf_centralizer {a c : G}
    (hodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)))) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.centralizer ({c} : Set G))) := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hTD : T ⊓ Subgroup.centralizer ({c} : Set G) ≤ C ⊓ Subgroup.centralizer ({c} : Set G) :=
    inf_le_inf_right _ hTC
  obtain ⟨hTsol, hT3⟩ := Sec4.Item422Proof.inSubgroup_theta_solvable_coprime C
  have hsol : Group.IsSolvable ↥(T ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_left : T ⊓ Subgroup.centralizer ({c} : Set G) ≤ T))
  have h3 : ¬ 3 ∣ Nat.card ↥(T ⊓ Subgroup.centralizer ({c} : Set G)) := fun h =>
    hT3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hnorm : ((T ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf
      (C ⊓ Subgroup.centralizer ({c} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTD]
    intro x hx
    obtain ⟨hxa, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxT : x ∈ Subgroup.normalizer (T : Set G) :=
      Sec21.le_normalizer_theta (A := C) (L := C) Subgroup.le_normalizer hxa
    have hxC : x ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := Subgroup.le_normalizer hxc
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hxT, hxC⟩)
  have hle := Sec4.Item422Proof.le_inSubgroup_theta_of_normal hTD hnorm hsol h3
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

private theorem exists_invariant_two_subgroup {a c : G} {F : Subgroup G}
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hFa : F ≤ Subgroup.centralizer ({a} : Set G))
    (hev : 2 ∣ Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))))
    (hodd : Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)) ⊓ Subgroup.centralizer ({c} : Set G)))) :
    ∃ S : Subgroup G,
      S ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ∧
      IsPGroup 2 S ∧ S ≠ ⊥ ∧ F ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3)
    (Subgroup.centralizer ({a} : Set G)) with hT
  have hFN : F ≤ Subgroup.normalizer (T : Set G) :=
    Sec21.le_normalizer_theta (hFa.trans Subgroup.le_normalizer)
  have hcop : Nat.Coprime 3 (Nat.card T) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Sec11.not_three_dvd_card_inSubgroup_theta _)
  obtain ⟨S0, hSN, hS1⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    3 2 Nat.prime_three Nat.prime_two F T (CFSG.Open.IsElemAbelian.isPGroup hFe) hFN hcop hev
  have hS2 : IsPGroup 2 ((S0 : Subgroup T).map T.subtype) := S0.isPGroup'.map _
  refine ⟨(S0 : Subgroup T).map T.subtype, Subgroup.map_subtype_le _, hS2, hS1, hSN, ?_⟩
  refine Sec21.eq_bot_of_isPGroup_two_of_odd (hS2.to_le inf_le_left) ?_
  exact Odd.of_dvd_nat hodd
    (Subgroup.card_dvd_of_le (inf_le_inf_right _ (Subgroup.map_subtype_le _)))

private theorem exists_b {E F S : Subgroup G} {c : G}
    (hEF : CFSG.Assembly.IsElemAbelian 3 (E ⊓ F)) (hcard : Nat.card ↥(E ⊓ F) = 9)
    (hFS : F ≤ Subgroup.normalizer (S : Set G)) (hS3 : Nat.Coprime 3 (Nat.card S))
    (hS1 : S ≠ ⊥) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    ∃ b ∈ E ⊓ F, b ∉ Subgroup.zpowers c ∧ S ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_three hEF
    (by rw [hcard]; norm_num) (inf_le_right.trans hFS) hS3
  by_contra hcon
  push Not at hcon
  apply hS1
  rw [← hgen]
  refine iSup_eq_bot.mpr fun y => iSup_eq_bot.mpr fun hy => iSup_eq_bot.mpr fun hy1 => ?_
  by_cases hyc : y ∈ Subgroup.zpowers c
  · exact eq_bot_mono (inf_le_inf_left S (centralizer_le_of_mem_zpowers hc3 hc1 hyc hy1)) hSc
  · exact hcon y hy hyc

end Aux

theorem exists_bR {G : Type} [Group G] [Finite G] {E F : Subgroup G} {a c : G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hE : E ∉ partTwoE G)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (haF : a ∈ F) (hcF : c ∈ F) (hcE : c ∈ E) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hFa : F ≤ Subgroup.centralizer ({a} : Set G))
    (hcomm : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) (hac : a * c = c * a)
    (hFEcard : Nat.card (E ⊓ F : Subgroup G) = 9) (hFgen : F = Subgroup.zpowers a ⊔ (E ⊓ F))
    (hev : 2 ∣ Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))) :
    ∃ (b : G) (R : Subgroup G), b ∈ E ∧ b ∈ F ∧ b ∉ Subgroup.zpowers c ∧ R ≠ ⊥ ∧
      IsPGroup 2 R ∧
      R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ∧
      R ≤ Subgroup.centralizer ({b} : Set G) ∧ F ≤ Subgroup.normalizer (R : Set G) ∧
      (∀ r ∈ R, c * r * c⁻¹ = r → r = 1) := by
  have hodd1 := odd_card_theta_inf hEe hE27 hE hcE hcomm
  have hodd2 := odd_card_theta_inf_centralizer hodd1
  obtain ⟨S, hST, hS2, hS1, hFS, hSc⟩ := exists_invariant_two_subgroup hFe hFa hev hodd2
  have hS3 : Nat.Coprime 3 (Nat.card S) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hST)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (Sec11.not_three_dvd_card_inSubgroup_theta _))
  have hEFe : CFSG.Assembly.IsElemAbelian 3 (E ⊓ F) :=
    CFSG.Open.IsElemAbelian.mono hEe inf_le_left
  obtain ⟨b, hbEF, hbc, hSb⟩ := exists_b hEFe hFEcard hFS hS3 hS1 hc3 hc1 hSc
  have hbE : b ∈ E := (Subgroup.mem_inf.mp hbEF).1
  have hbF : b ∈ F := (Subgroup.mem_inf.mp hbEF).2
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hFe hx hy
  set H : Subgroup G := S ⊓ Subgroup.centralizer ({b} : Set G) with hH
  have hFH : F ≤ Subgroup.normalizer (H : Set G) := by
    intro f hf
    refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hFS hf, ?_⟩)
    exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hFc f hf b hbF))
  have hFK : F ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro f hf
    have hfc : f ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hFc f hf c hcF)
    exact Subgroup.centralizer_le_normalizer _ hfc
  have hKH : Subgroup.zpowers c ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr (hFH hcF)
  have hRH : ⁅H, Subgroup.zpowers c⁆ ≤ H :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKH
  refine ⟨b, ⁅H, Subgroup.zpowers c⁆, hbE, hbF, hbc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hR
    have h1 : H ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR
    apply hSb
    refine eq_bot_mono ?_ hSc
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)) (h1 hx)
  · exact hS2.to_le (hRH.trans inf_le_left)
  · exact (hRH.trans inf_le_left).trans hST
  · exact hRH.trans inf_le_right
  · intro f hf
    exact mem_normalizer_commutator (hFH hf) (hFK hf)
  · intro r hr hcr
    have hrS : r ∈ S := (Subgroup.mem_inf.mp (hRH hr)).1
    have hrc : r ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * c = c * r * c⁻¹ * c := by rw [hcr]
        _ = c * r := by group
    have hmem : r ∈ S ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.mem_inf.mpr ⟨hrS, hrc⟩
    rw [hSc] at hmem
    exact Subgroup.mem_bot.mp hmem

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

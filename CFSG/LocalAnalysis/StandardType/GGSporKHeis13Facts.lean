module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HeisThirteen
import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
import CFSG.Assembly.QuasithinDefs
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
open scoped commutatorElement

theorem heis13_c_mem_closure {G : Type*} [Group G] {x y c : G} (hc : c ^ 13 = 1)
    (hcx : c * x = x * c) (hcy : c * y = y * c) (hyx : y * x = x * (y * c ^ 4)) :
    c ∈ Subgroup.closure ({x, y} : Set G) := by
  have hcx' : Commute c x := hcx
  have hcy' : Commute c y := hcy
  have hxS : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hxy9 : ⁅x, y⁆ = c ^ 9 := by
    have hgd : x * y * x⁻¹ = y * c ^ 9 := gd_conj hcx hcy hyx hc
    have hy9 : y * c ^ 9 * y⁻¹ = c ^ 9 := by
      rw [← (hcy'.pow_left 9).eq]; group
    rw [commutatorElement_def, hgd, hy9]
  have hc27 : c ^ 27 = c := by
    rw [show (27 : ℕ) = 13 * 2 + 1 by norm_num, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
  have hc9S : c ^ 9 ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [← hxy9, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxS hyS)
      (Subgroup.inv_mem _ hxS)) (Subgroup.inv_mem _ hyS)
  have : c = (c ^ 9) ^ 3 := by rw [← pow_mul, hc27]
  rw [this]
  exact Subgroup.pow_mem _ hc9S 3

theorem heis13_mem_normalizer {G : Type*} [Group G] [Finite G] {x y c h : G} (hc : c ^ 13 = 1)
    (hcx : c * x = x * c) (hcy : c * y = y * c) (hyx : y * x = x * (y * c ^ 4))
    {a b g d e f : ℕ} (hhx : h * x = c ^ a * (y ^ b * (x ^ g * h)))
    (hhy : h * y = c ^ d * (y ^ e * (x ^ f * h))) :
    h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
  have hcS := heis13_c_mem_closure hc hcx hcy hyx
  have hxS : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
    have : h * x * h⁻¹ = c ^ a * (y ^ b * x ^ g) := by rw [hhx]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcS a)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hyS b) (Subgroup.pow_mem _ hxS g))
  have h2 : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
    have : h * y * h⁻¹ = c ^ d * (y ^ e * x ^ f) := by rw [hhy]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcS d)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hyS e) (Subgroup.pow_mem _ hxS f))
  have hle : Subgroup.closure ({x, y} : Set G) ≤
      (Subgroup.closure ({x, y} : Set G)).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h1
    · exact h2
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem heis13_sylow_facts {G : Type} [Group G] [Finite G] {x y c : G}
    (hcard : (Nat.card G).factorization 13 = 3)
    (hx : x ^ 13 = 1) (hy : y ^ 13 = 1) (hc : c ^ 13 = 1) (hc1 : c ≠ 1)
    (hcx : c * x = x * c) (hcy : c * y = y * c) (hyx : y * x = x * (y * c ^ 4)) :
    IsPGroup 13 (Subgroup.closure ({x, y} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y} : Set G)) = 13 ^ (Nat.card G).factorization 13 ∧
      Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({c} : Set G) ∧
      (∀ q ∈ Subgroup.closure ({x, y} : Set G), q ^ 13 = 1) ∧
      ⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆ =
        Subgroup.zpowers c ∧
      Subgroup.closure ({x, y} : Set G) ⊓
        Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G) = Subgroup.zpowers c := by
  set S : Subgroup G := Subgroup.closure ({x, y} : Set G) with hSdef
  have hp : Nat.Prime 13 := by norm_num
  haveI : Fact (Nat.Prime 13) := ⟨hp⟩
  have hcx' : Commute c x := hcx
  have hcy' : Commute c y := hcy
  have hxS : x ∈ S := Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := Subgroup.subset_closure (by simp)
  have hxy9 : ⁅x, y⁆ = c ^ 9 := by
    have hgd : x * y * x⁻¹ = y * c ^ 9 := gd_conj hcx hcy hyx hc
    have hy9 : y * c ^ 9 * y⁻¹ = c ^ 9 := by
      rw [← (hcy'.pow_left 9).eq]; group
    rw [commutatorElement_def, hgd, hy9]
  have hc27 : c ^ 27 = c := by
    rw [show (27 : ℕ) = 13 * 2 + 1 by norm_num, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
  have hcS : c ∈ S := heis13_c_mem_closure hc hcx hcy hyx
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy9]; exact hcx'.pow_left 9
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy9]; exact hcy'.pow_left 9
  have hpg : IsPGroup 13 S :=
    CFSG.AGLEmbedding.Norton.MON11_13.isPGroup_closure_of_central_commutator hp hx hy hzx hzy
  have hSc : S ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hSdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcy.symm
  have hexp : ∀ q ∈ S, q ^ 13 = 1 := by
    intro q hq
    obtain ⟨i, j, k, -, -, -, hq_eq⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm (r := 13) (by norm_num) hx hy hzx hzy hq
    have h1 := gpow_dpow hcx hcy hyx hc i j
    have hcm : ∀ m : ℕ, Commute (c ^ m) (y ^ j * x ^ i) := fun m =>
      ((hcy'.pow_right j).mul_right (hcx'.pow_right i)).pow_left m
    have hq' : q = c ^ (9 * i * j + 9 * k) * y ^ j * x ^ i := by
      calc q = x ^ i * y ^ j * (c ^ 9) ^ k := by rw [hq_eq, hxy9]
        _ = y ^ j * x ^ i * c ^ (9 * i * j) * c ^ (9 * k) := by rw [h1, ← pow_mul]
        _ = (y ^ j * x ^ i) * c ^ (9 * i * j + 9 * k) := by rw [pow_add]; simp only [mul_assoc]
        _ = c ^ (9 * i * j + 9 * k) * (y ^ j * x ^ i) := ((hcm _).eq).symm
        _ = c ^ (9 * i * j + 9 * k) * y ^ j * x ^ i := (mul_assoc _ _ _).symm
    rw [hq']
    exact heis_pow_thirteen hcx hcy hyx hc hx hy i j (9 * i * j + 9 * k)
  have hnc : x * y ≠ y * x := by
    intro h
    have h4 : c ^ 4 = 1 := by
      have h' : x * y = x * y * c ^ 4 := by
        calc x * y = y * x := h
          _ = x * (y * c ^ 4) := hyx
          _ = x * y * c ^ 4 := by rw [mul_assoc]
      exact (mul_eq_left.1 h'.symm)
    apply hc1
    have hc40 : c ^ 40 = c := by
      rw [show (40 : ℕ) = 13 * 3 + 1 by norm_num, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
    calc c = c ^ 40 := hc40.symm
      _ = (c ^ 4) ^ 10 := by rw [← pow_mul]
      _ = 1 := by rw [h4, one_pow]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hnle : n ≤ 3 := by
    have h13 : 13 ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card S
    have := (hp.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne').1 h13
    omega
  have hSnc : ¬ ∀ a b : S, a * b = b * a := by
    intro hcomm
    exact hnc (congrArg Subtype.val (hcomm ⟨x, hxS⟩ ⟨y, hyS⟩))
  have hn3 : n = 3 := by
    by_contra hne
    apply hSnc
    interval_cases n
    · haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      intro a b
      exact Subsingleton.elim _ _
    · haveI : IsCyclic S := isCyclic_of_prime_card (by simpa using hn)
      intro a b
      exact mul_comm' a b
    · intro a b
      exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 13)
        (by simpa using hn)).is_comm.comm a b
    · exact absurd rfl hne
  have hScard : Nat.card S = 13 ^ (Nat.card G).factorization 13 := by rw [hcard, hn, hn3]
  have hord : orderOf c = 13 := orderOf_eq_prime hc hc1
  have hzcard : Nat.card (Subgroup.zpowers c) = 13 := by rw [Nat.card_zpowers, hord]
  have hcentral : ∀ a ∈ Subgroup.zpowers c, ∀ s ∈ S, s * a = a * s := by
    intro a ha s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hsc : Commute s c := Subgroup.mem_centralizer_singleton_iff.1 (hSc hs)
    exact (hsc.zpow_right k).eq
  have hZ'normal : ((Subgroup.zpowers c).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ((g * n * g⁻¹ : S) : G) = (n : G) := by
      have := hcentral _ hn g g.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [this, mul_inv_cancel_right]
    rw [h1]
    exact hn
  have hcomm1 : ⁅S, S⁆ ≤ Subgroup.zpowers c := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    set Z' : Subgroup S := (Subgroup.zpowers c).subgroupOf S with hZ'
    have hzS : Subgroup.zpowers c ≤ S := by
      rw [Subgroup.zpowers_le]; exact hcS
    have hZ'card : Nat.card Z' = 13 := by
      rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzS).toEquiv, hzcard]
    have hqcard : Nat.card (S ⧸ Z') = 13 ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
      rw [hScard, hcard, hZ'card] at h
      have h13 : (13 : ℕ) ^ 3 = 13 ^ 2 * 13 := by norm_num
      rw [hcard] at *
      omega
    haveI : IsPGroup 13 (S ⧸ Z') := hpg.to_quotient Z'
    have hcq : ∀ u v : S ⧸ Z', u * v = v * u := fun u v =>
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 13) hqcard).is_comm.comm u v
    have h1 : QuotientGroup.mk' Z' ⁅(⟨a, ha⟩ : S), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcq _ _)
    have h2 : ⁅(⟨a, ha⟩ : S), ⟨b, hb⟩⁆ ∈ Z' := (QuotientGroup.eq_one_iff _).1 h1
    rw [hZ', Subgroup.mem_subgroupOf] at h2
    simpa [commutatorElement_def] using h2
  have hz6 : S ⊓ Subgroup.centralizer (S : Set G) = Subgroup.zpowers c := by
    set Zc : Subgroup G := S ⊓ Subgroup.centralizer (S : Set G) with hZc
    have hZS : Zc ≤ S := inf_le_left
    have hzle : Subgroup.zpowers c ≤ Zc := by
      rw [Subgroup.zpowers_le]
      exact ⟨hcS, Subgroup.mem_centralizer_iff.2 fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.1 (hSc hh)⟩
    have hle : Nat.card Zc ≤ 13 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hpg.to_le hZS)
      have hm2 : 2 ≤ m := by
        by_contra hlt
        push Not at hlt
        have h13 : 13 < 13 ^ m := hm ▸ hgt
        interval_cases m <;> simp at h13
      set Z' : Subgroup S := Zc.subgroupOf S with hZ'
      have hZ'card : Nat.card Z' = 13 ^ m := by
        rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, hm]
      have hZ'c : Z' ≤ Subgroup.center S := by
        intro a ha
        rw [hZ', Subgroup.mem_subgroupOf] at ha
        refine Subgroup.mem_center_iff.2 fun b => ?_
        have := Subgroup.mem_centralizer_iff.1 ha.2 (b : G) b.2
        exact Subtype.ext (by simpa using this)
      haveI : Z'.Normal := ⟨fun n hn g => by
        have := Subgroup.mem_center_iff.1 (hZ'c hn) g
        rw [this, mul_inv_cancel_right]; exact hn⟩
      have hq : Nat.card (S ⧸ Z') * 13 ^ m = 13 ^ 3 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
        rw [hZ'card, hScard, hcard] at h
        exact h.symm
      have hm3 : m ≤ 3 := by
        have : 13 ^ m ∣ 13 ^ 3 := ⟨Nat.card (S ⧸ Z'), by rw [← hq]; ring⟩
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
      haveI : IsCyclic (S ⧸ Z') := by
        interval_cases m
        · have hq' : Nat.card (S ⧸ Z') * 169 = 2197 := by simpa using hq
          have hq13 : Nat.card (S ⧸ Z') = 13 := by omega
          exact isCyclic_of_prime_card hq13
        · have hq' : Nat.card (S ⧸ Z') * 2197 = 2197 := by simpa using hq
          have hq1 : Nat.card (S ⧸ Z') = 1 := by omega
          haveI : Subsingleton (S ⧸ Z') := (Nat.card_eq_one_iff_unique.mp hq1).1
          infer_instance
      exact hSnc (fun a b => commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z')
        (by rw [QuotientGroup.ker_mk']; exact hZ'c) a b)
    exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard]; exact hle)).symm
  have hcomm2 : Subgroup.zpowers c ≤ ⁅S, S⁆ := by
    have h9 : c ^ 9 ∈ ⁅S, S⁆ := by
      rw [← hxy9]
      exact Subgroup.commutator_mem_commutator hxS hyS
    have : c = (c ^ 9) ^ 3 := by rw [← pow_mul, hc27]
    rw [Subgroup.zpowers_le, this]
    exact Subgroup.pow_mem _ h9 3
  exact ⟨hpg, hScard, hSc, hexp, le_antisymm hcomm1 hcomm2, hz6⟩

end CFSG.StandardType.SporadicShape

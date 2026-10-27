module

import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_theta_of_mem_sup {a x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    {K' : Subgroup G} (hK' : K' ≤ Subgroup.centralizer ({a} : Set G))
    (h : ∀ k ∈ K', ⁅k, x⁆ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    {n : G} (hn : n ∈ K' ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    ⁅n, x⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta C
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  let S : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ⁅g, x⁆ ∈ T}
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨C.mul_mem hg₁ hg₂, ?_⟩
        have e : ⁅g₁ * g₂, x⁆ = g₁ * ⁅g₂, x⁆ * g₁⁻¹ * ⁅g₁, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCT hg₁) _).mp h₂) h₁
      one_mem' := ⟨C.one_mem, by rw [commutatorElement_one_left]; exact T.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, h₁⟩
        refine ⟨C.inv_mem hg, ?_⟩
        have e : ⁅g⁻¹, x⁆ = g⁻¹ * ⁅g, x⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCT (C.inv_mem hg)) _).mp (T.inv_mem h₁) }
  have hK'S : K' ≤ S := fun k hk => ⟨hK' hk, h k hk⟩
  have hTS : T ≤ S := by
    intro t ht
    refine ⟨hTC ht, ?_⟩
    have e : ⁅t, x⁆ = t * (x * t⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact T.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (hCT hx) _).mp (T.inv_mem ht))
  exact (sup_le hK'S hTS hn).2

theorem mem_normalizer_sup_theta {a x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    {K' : Subgroup G} (hK' : K' ≤ Subgroup.centralizer ({a} : Set G))
    (h : ∀ k ∈ K', ⁅k, x⁆ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    x ∈ Subgroup.normalizer ((K' ⊔ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun n hn => ?_
  have h1 := commutator_mem_theta_of_mem_sup hx hK' h hn
  have e : x * n * x⁻¹ = ⁅n, x⁆⁻¹ * n := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1)) hn

theorem eq_one_of_mem_theta_of_isPGroup {a : G} {R : Subgroup G} (hR : IsPGroup 3 R) {z : G}
    (hzR : z ∈ R)
    (hzT : z ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    z = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨z, hzR⟩
  have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact eq_one_of_mem_of_pow_three_pow
    (Sec6.theta_solvable_and_not_dvd (Subgroup.centralizer ({a} : Set G))).2 hzT hk'

theorem exists_isSylowOf_commute_of_le {a : G} {A S K' : Subgroup G} (hAp : IsPGroup 3 A)
    (hAS : A ≤ S) (hSC : S ≤ Subgroup.centralizer ({a} : Set G))
    (hK'C : K' ≤ Subgroup.centralizer ({a} : Set G))
    (hSK : ∀ s ∈ S, ∀ k ∈ K', ⁅k, s⁆ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 T (K' ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) ∧
      ∀ t ∈ T, ∀ x ∈ A, t * x = x * t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := K' ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))
    with hN
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_sup_theta (hSC (hAS hx)) hK'C (fun k hk => hSK x (hAS hx) k hk)
  have hNH : N ≤ A ⊔ N := le_sup_right
  have hHN : A ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hAN Subgroup.le_normalizer
  obtain ⟨R, hR, hAR⟩ := exists_isSylowOf_ge (le_sup_left : A ≤ A ⊔ N) hAp
  refine ⟨R ⊓ N, hR.inf_of_le_normalizer hNH hHN, fun t ht x hx => ?_⟩
  have h1 := commutator_mem_theta_of_mem_sup (hSC (hAS hx)) hK'C
    (fun k hk => hSK x (hAS hx) k hk) ht.2
  have h2 : ⁅t, x⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ht.1 (hAR hx)) (R.inv_mem ht.1)) (R.inv_mem (hAR hx))
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_theta_of_isPGroup hR.isPGroup h2 h1)

theorem false_of_isSylowOf_commute {A : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {T N E : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T N)
    (hTA : ∀ t ∈ T, ∀ x ∈ A, t * x = x * t) (hEN : E ≤ N) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨T', hT', hET'⟩ := exists_isSylowOf_ge hEN hEp
  obtain ⟨k, -, hk⟩ := hT.exists_mem_conj hT'
  have hmem : ∀ x ∈ E, k⁻¹ * x * k ∈ A := by
    intro x hx
    have hxT : k⁻¹ * x * k ∈ T := (hk x).mp (hET' hx)
    refine Sec4.mem_of_maximal_of_commute hAmax ?_ fun α hα => (hTA _ hxT α hα).symm
    rw [show k⁻¹ * x * k = k⁻¹ * x * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hE3 x hx, mul_one,
      mul_inv_cancel]
  obtain ⟨⟨hAc, -⟩, -⟩ := hAmax
  obtain ⟨x, hx, y, hy, hxy⟩ := hEc
  apply hxy
  have hc : (k⁻¹ * x * k) * (k⁻¹ * y * k) = (k⁻¹ * y * k) * (k⁻¹ * x * k) :=
    congrArg Subtype.val (hAc.is_comm.comm ⟨_, hmem x hx⟩ ⟨_, hmem y hy⟩)
  calc x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by rw [hc]
    _ = y * x := by group

section J2


theorem pow_three_eq_one_of_quot_j2 {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {x : G} (hxL : x ∈ L) {k : ℕ} (hx : x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hJ
  set y : ↥L := ⟨x, hxL⟩ with hy
  have hyk : y ^ 3 ^ k = 1 := Subtype.ext (by simpa [hy] using hx)
  set κ : ↥L ⧸ aschbacherSolvableCore 3 ↥L := (y : ↥L ⧸ aschbacherSolvableCore 3 ↥L) with hκ
  have hκk : κ ^ 3 ^ k = 1 := by rw [hκ, ← QuotientGroup.mk_pow, hyk, QuotientGroup.mk_one]
  have hκp : IsPGroup 3 (Subgroup.zpowers κ) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hκk, one_zpow]
  obtain ⟨P, hP⟩ := hκp.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -⟩ := Sec4.Sporadic.rank3II_4_15 _ ⟨e⟩ P _ rfl _ rfl
  have hκ3 : κ ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨κ, hP (Subgroup.mem_zpowers κ)⟩ : ↥(P : Subgroup _))
    rw [hHeis.2.2] at h
    exact congrArg Subtype.val h
  have h1 : y ^ 3 ∈ aschbacherSolvableCore 3 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hκ3
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have h2 : (y ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hyk, one_pow]
  have h3 := eq_one_of_mem_of_pow_three_pow hθ3 h1 h2
  simpa [hy] using congrArg Subtype.val h3

theorem exists_nonabelian_le_lB {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (hc : IsLBConfig A D b d Lb) :
    ∃ E : Subgroup G, E ≤ lB A D ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h.isE27'
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, hd1⟩ := hc.ne_one hD hA
  have hres := Item148HJ.lB_eq_residual h hD hc
  have h9 : Nat.card (A ⊓ Lb : Subgroup G) = 9 :=
    (j2_point_facts (Item148HJ.sec14Std_of_isLBConfig h hc).toSec13Data hJ).2.1
  have hcfg := hc.2.2.2.2
  obtain ⟨hdL, S, hdS, hSd⟩ := hcfg
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  obtain ⟨-, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  set E := (S : Subgroup ↥Lb).map Lb.subtype with hE
  have hEelt : ∀ x ∈ E, x ∈ Lb ∧ x ∈ Subgroup.centralizer ({d} : Set G) ∧
      ∃ k : ℕ, x ^ 3 ^ k = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_, ?_⟩
    · have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h1
    · obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
      exact ⟨k, by
        simpa using congrArg (fun z : ↥(S : Subgroup ↥Lb) => ((z : ↥Lb) : G)) hk⟩
  refine ⟨E, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨hxL, hxd, k, hk⟩ := hEelt x hx
    rw [hres]
    exact mem_residual_of_pow_three h415 hJ hdL hd1 ⟨S, hdS, hSd⟩ hxL hxd hk
  · obtain ⟨hxL, -, k, hk⟩ := hEelt x hx
    exact pow_three_eq_one_of_quot_j2 hJ hxL hk
  · by_contra hall
    push Not at hall
    have hEZ : E ≤ Subgroup.zpowers d := by
      intro x hx
      rw [← hZ]
      refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hall _ y.2 _ hx), rfl⟩
    have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA.1.2 d (hD.1 (hc.1 ▸ Subgroup.subset_closure
        (Set.mem_insert_of_mem b rfl)))) hd1
    have h9L : 3 ^ 2 ∣ Nat.card ↥Lb := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h9S := S.pow_dvd_card_of_pow_dvd_card h9L
    have hES : Nat.card E = Nat.card (S : Subgroup ↥Lb) :=
      Subgroup.card_map_of_injective Lb.subtype_injective
    have hle := Subgroup.card_le_of_le hEZ
    rw [hES, hd3] at hle
    have := Nat.le_of_dvd (Nat.card_pos) h9S
    omega

end J2

end CFSG.RankThree.PartTwo.Sec14.Ronan148D

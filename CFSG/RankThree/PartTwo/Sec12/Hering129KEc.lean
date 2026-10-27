module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KE1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEd
import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.KFacts.KS44Transport
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


theorem hessData_of_core {H : Type} [Group H] [Finite H] {Y A : Subgroup H} {x b c : H}
    (hYn : Y.Normal) (hY : Y ∈ thetaComponents 3 H) (hT : aschbacherSolvableCore 3 H ≤ Y)
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hgen : A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    (hb3 : b ^ 3 = 1) (hxc : ∀ h : H, x * h = h * x) (hcY : c ∈ Y)
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    (hX : ∃ X : Subgroup H, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set H) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set H))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)))
    (hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField) :
    HessData (Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
      (A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H) x)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H) b)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H) c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
  have hinj : Set.InjOn π (A : Set H) := injOn_mk_of_isPGroup Nat.prime_three hA3
  have hxA : x ∈ A := hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hYhn : (Y.map π).Normal := hYn.map π hπs
  have hstruct := theta_component_quotient_structure (G := H) Nat.prime_three hY
  have hin : inSubgroup (aschbacherSolvableCore 3) Y = Y ⊓ aschbacherSolvableCore 3 H :=
    hstruct.1
  have hxc' : ∀ p : H ⧸ aschbacherSolvableCore 3 H, π x * p = p * π x := fun p => by
    obtain ⟨h, rfl⟩ := hπs p
    rw [← map_mul, ← map_mul, hxc h]
  refine ⟨hYhn, ?_, ?_, ?_, hxc', ?_, Subgroup.mem_map_of_mem π hcY, ?_, ?_⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π A hAel
  · rw [Sec13.card_map_eq_of_injOn π hinj]
    exact hA27
  · rw [hgen, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
  ·
    ext β
    constructor
    · rintro ⟨hβB, hβC⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hβB
      have haC : a ∈ Sec4.thetaQuotCentralizer Y := by
        rw [Sec6.mem_thetaQuotCentralizer_iff]
        refine ⟨by rw [Subgroup.normalizer_eq_top_iff.mpr hYn]; exact Subgroup.mem_top _,
          fun l hl => ?_⟩
        rw [hin]
        refine ⟨Y.mul_mem (Y.inv_mem hl) (hYn.conj_mem l hl a), ?_⟩
        have hc := Subgroup.mem_centralizer_iff.mp hβC (π l) (Subgroup.mem_map_of_mem π hl)
        refine (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 H) _).mp ?_
        have hc' : π a * π l * (π a)⁻¹ = π l := by rw [← hc, mul_inv_cancel_right]
        have hπe : π (l⁻¹ * (a * l * a⁻¹)) = (π l)⁻¹ * (π a * π l * (π a)⁻¹) := by
          simp only [map_mul, map_inv]
        change π (l⁻¹ * (a * l * a⁻¹)) = 1
        rw [hπe, hc', inv_mul_cancel]
      have hax : a ∈ Subgroup.zpowers x := by
        rw [← hAC]
        exact ⟨ha, haC⟩
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem π hax
    · intro hβ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
      refine ⟨Subgroup.mem_map.mpr ⟨x ^ k, A.zpow_mem hxA k, by simp⟩,
        Subgroup.mem_centralizer_iff.mpr fun y _ => ?_⟩
      exact (Commute.zpow_right (show Commute y (π x) from (hxc' y).symm) k).eq
  ·
    obtain ⟨X, hXY, hXC, hXp, hXs, hcX, p, n, hp, h4, ⟨e⟩⟩ := hX
    haveI := hp
    haveI := hXp
    obtain ⟨φ, hφ⟩ := Hering129KEd.exists_surjective_hom_map X e
    refine ⟨X.map π, Subgroup.map_mono hXY, ?_, ?_,
      Hering129KEd.isSubnormal_map_inf_centralizer hb3 hT (le_inf hXY hXC) hXs,
      Subgroup.mem_map_of_mem π hcX, p, n, hp, h4, φ, hφ⟩
    · rintro _ ⟨x', hx', rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hb := Subgroup.mem_centralizer_singleton_iff.mp (hXC hx')
      rw [← map_mul, ← map_mul, hb]
    · exact Group.IsPerfect.ofSurjective (f := π.subgroupMap X) (π.subgroupMap_surjective X)
  ·
    intro β hβ
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hβ
    have hh := Sec8.Item812Res4.subgroupMap_mem_core_iff hY
    have hxN : a ∈ Subgroup.normalizer (Y : Set H) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hYn]
      exact Subgroup.mem_top _
    exact ⟨fun hk => (hkind a ha).1 (KFacts.InducesStdKind.of_map π Y hh hxN hk),
      fun hk => (hkind a ha).2 (KFacts.InducesStdKind.of_map π Y hh hxN hk)⟩

end CFSG.RankThree.PartTwo.Sec12

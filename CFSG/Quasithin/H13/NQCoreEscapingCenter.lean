module

public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem center_eq_of_odd_kernel (hcent : CFSG.SectionRank.OddKernelCentralization)
    (hSQT : CFSG.IsStronglyQuasithin H) {Y J : Subgroup H} [J.Normal] (hYn : Y.Normal)
    (hYp : Group.IsPerfect Y) (hRJ : CFSG.Open.pCore 2 H ≤ J)
    (hJnil : Group.IsNilpotent ((J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)))))
    (hJodd : Odd (Nat.card ((J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))))))
    (hqY : (CFSG.Open.pCore 2 ↥Y).map Y.subtype = Y ⊓ CFSG.Open.pCore 2 H)
    (hYbar : CFSG.layer ↥(Y.map (QuotientGroup.mk' J)) = ⊤ ∧
      center ↥(Y.map (QuotientGroup.mk' J)) = ⊥) :
    ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) =
        center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ∧
      Odd (Nat.card (((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqR : CFSG.Open.pCore 2 ↥Y = (CFSG.Open.pCore 2 H).subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [hqY, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hqJ : CFSG.Open.pCore 2 ↥Y ≤ (Y ⊓ J).subgroupOf Y := by
    rw [hqR]
    intro y hy
    exact ⟨y.2, hRJ hy⟩
  have hXp : Group.IsPerfect (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥Y) (⊤ : Subgroup ↥Y)
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))
    rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥Y))] at h1
    exact h1.symm
  have hYJn : ((Y ⊓ J).subgroupOf Y).Normal := by
    have : (Y ⊓ J).Normal := Subgroup.normal_inf_normal Y J
    exact Subgroup.normal_subgroupOf
  have hCn : (((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))).Normal :=
    hYJn.map _ (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥Y))
  set ψR : ↥Y →* H ⧸ CFSG.Open.pCore 2 H := (QuotientGroup.mk' (CFSG.Open.pCore 2 H)).comp Y.subtype
    with hψR
  have hkerR : ψR.ker = CFSG.Open.pCore 2 ↥Y := by
    rw [hqR]
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (y : H)
  let φR : ↥Y ⧸ CFSG.Open.pCore 2 ↥Y →* H ⧸ CFSG.Open.pCore 2 H := (QuotientGroup.kerLift ψR).comp
    (QuotientGroup.quotientMulEquivOfEq hkerR.symm).toMonoidHom
  have hφR : Function.Injective φR :=
    (QuotientGroup.kerLift_injective ψR).comp (MulEquiv.injective _)
  have hCJ : ∀ c ∈ ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)),
      φR c ∈ J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(y : H), (mem_subgroupOf.mp hy).2, rfl⟩
  let ι : ↥(((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) →*
      ↥(J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) :=
    (φR.comp (((Y ⊓ J).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))).subtype).codRestrict _ fun c => hCJ c c.2
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (hφR (congrArg Subtype.val hab))
  have hCnil : Group.IsNilpotent
      ↥(((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) := by
    have := hJnil
    have : Group.IsNilpotent ↥ι.range := Subgroup.isNilpotent _
    exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hι).symm
  have hCodd : Odd (Nat.card
      ↥(((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)))) :=
    Odd.of_dvd_nat hJodd (Subgroup.card_dvd_of_injective ι hι)
  set ψJ : ↥Y →* ↥(Y.map (QuotientGroup.mk' J)) := (QuotientGroup.mk' J).subgroupMap Y
    with hψJ
  have hkerJ : ψJ.ker = (Y ⊓ J).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hy
      exact ⟨y.2, (QuotientGroup.eq_one_iff (y : H)).mp (congrArg Subtype.val hy)⟩
    · intro hy
      exact Subtype.ext ((QuotientGroup.eq_one_iff (y : H)).mpr hy.2)
  have hqψ : CFSG.Open.pCore 2 ↥Y ≤ ψJ.ker := hkerJ ▸ hqJ
  let φJ : ↥Y ⧸ CFSG.Open.pCore 2 ↥Y →* ↥(Y.map (QuotientGroup.mk' J)) :=
    QuotientGroup.lift (CFSG.Open.pCore 2 ↥Y) ψJ hqψ
  have hφJs : Function.Surjective φJ := by
    intro z
    obtain ⟨y, rfl⟩ := (QuotientGroup.mk' J).subgroupMap_surjective Y z
    exact ⟨(y : ↥Y ⧸ CFSG.Open.pCore 2 ↥Y), rfl⟩
  have hkerφJ : φJ.ker = ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) := by
    rw [QuotientGroup.ker_lift, hkerJ]
  let e : (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ⧸
      ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) ≃*
        ↥(Y.map (QuotientGroup.mk' J)) :=
    (QuotientGroup.quotientMulEquivOfEq hkerφJ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φJ hφJs)
  have hquot : ∀ (N : Subgroup ((↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ⧸
      ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)))) [N.Normal],
      center (((↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ⧸
        ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) ⧸ N) = ⊥ := by
    intro N _
    exact (CFSG.SectionRank.centerless_semisimple_quotient hYbar.1 hYbar.2
      ((QuotientGroup.mk' N).comp e.symm.toMonoidHom)
      ((QuotientGroup.mk'_surjective N).comp e.symm.surjective)).2
  have hrank : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) →
        CFSG.Open.pRank r (((Y ⊓ J).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) ≤ 2 := by
    intro r hr hrC
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr hrC)
    have h1 : CFSG.Open.pRank r (((Y ⊓ J).subgroupOf Y).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))) ≤
          CFSG.Open.pRank r (⊤ : Subgroup (↥Y ⧸ CFSG.Open.pCore 2 ↥Y)) :=
      CFSG.SectionRank.pRank_mono hr.one_lt le_top
    have hq2 : ¬ r ∣ Nat.card (CFSG.Open.pCore 2 ↥Y) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥Y))
      rw [hk]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)
      exact hr2 this
    have h2 : CFSG.pRank r (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) = CFSG.pRank r ↥Y :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr _ hq2
    have h3 : CFSG.pRank r ↥Y ≤ CFSG.pRank r H := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt Y.subtype Y.subtype_injective
    have h4 := hSQT r hr hr2
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega
  have hCZ : ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) ≤
      center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) :=
    hcent _ hXp _ hCnil hCodd hquot hrank
  have hZC : center (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) ≤
      ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) := by
    intro z hz
    rw [← hkerφJ, MonoidHom.mem_ker]
    have hz' : φJ z ∈ center ↥(Y.map (QuotientGroup.mk' J)) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨x, rfl⟩ := hφJs w
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) x]
    rw [hYbar.2, mem_bot] at hz'
    exact hz'
  exact ⟨le_antisymm hCZ hZC, hCodd⟩

end CFSG.Quasithin.H13.NQCore

module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof1515

variable {G : Type} [Group G] [Finite G]

@[expose] def NoPerfectTwoCoreSection (S T : Type) [Group S] [Group T] : Prop :=
  ∀ H : Subgroup S, Group.IsPerfect ↥H → CFSG.pCore 2 ↥H ≠ ⊥ →
    IsEmpty (↥H ⧸ CFSG.pCore 2 ↥H ≃* T)

theorem pCoreOf_two_le_pCoreOf_two_of_noPerfectTwoCoreSection {X K : Subgroup G}
    (hXK : X ≤ K) (hperf : Group.IsPerfect ↥X)
    (hsimple : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hS : NoPerfectTwoCoreSection (↥K ⧸ CFSG.pCore 2 ↥K) (↥X ⧸ CFSG.pCore 2 ↥X)) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  haveI := hperf
  let Q : Subgroup ↥X := CFSG.pCore 2 ↥X
  let f : ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hXK)
  have hker : f.ker = (X ⊓ CFSG.Open.pCoreOf 2 K).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have h1 : (Subgroup.inclusion hXK x : ↥K) ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hXK x)).mp hx
      refine ⟨x.2, ?_⟩
      have h2 : ((Subgroup.inclusion hXK x : ↥K) : G) ∈
          (CFSG.pCore 2 ↥K).map K.subtype := Subgroup.mem_map_of_mem K.subtype h1
      rwa [Subgroup.coe_inclusion] at h2
    · rintro ⟨-, hx⟩
      have h1 : ((Subgroup.inclusion hXK x : ↥K) : G) ∈ (CFSG.pCore 2 ↥K).map K.subtype := by
        rwa [Subgroup.coe_inclusion]
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hXK x)).mpr
        ((Subgroup.mem_map_iff_mem K.subtype_injective).mp h1)
  have hiff : Q ≤ f.ker ↔ CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
    constructor
    · intro hle x hx
      have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
      have hx' : (⟨x, hxX⟩ : ↥X) ∈ Q := (Subgroup.mem_map_iff_mem X.subtype_injective).mp hx
      have h1 : (⟨x, hxX⟩ : ↥X) ∈ (X ⊓ CFSG.Open.pCoreOf 2 K).subgroupOf X := by
        rw [← hker]; exact hle hx'
      exact (Subgroup.mem_subgroupOf.mp h1).2
    · intro hle x hx
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hx' : (x : G) ∈ CFSG.Open.pCoreOf 2 X := Subgroup.mem_map_of_mem X.subtype hx
      exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 X hx', hle hx'⟩
  by_contra hcon
  have hQnker : ¬ Q ≤ f.ker := fun h => hcon (hiff.mp h)
  let H : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := f.range
  have hHperf : Group.IsPerfect ↥H := Group.IsPerfect.range f
  have hMle : Q.map f.rangeRestrict ≤ CFSG.pCore 2 ↥H :=
    CFSG.LieType.BorelTits.le_pCore 2
      ((CFSG.LieType.BorelTits.pCore_normal (G := ↥X) 2).map f.rangeRestrict
        f.rangeRestrict_surjective)
      ((CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).map f.rangeRestrict)
  have hMne : Q.map f.rangeRestrict ≠ ⊥ := by
    intro hbot
    apply hQnker
    have h1 : Q ≤ f.rangeRestrict.ker := (Subgroup.map_eq_bot_iff Q).mp hbot
    rwa [MonoidHom.ker_rangeRestrict] at h1
  have hHcore : CFSG.pCore 2 ↥H ≠ ⊥ :=
    fun hbot => hMne (le_bot_iff.mp (hMle.trans (le_of_eq hbot)))
  let ψ : ↥X →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp f.rangeRestrict
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H)).comp f.rangeRestrict_surjective
  have hQψ : Q ≤ ψ.ker := by
    intro x hx
    have h1 : f.rangeRestrict x ∈ Q.map f.rangeRestrict := Subgroup.mem_map_of_mem f.rangeRestrict hx
    exact (QuotientGroup.eq_one_iff (f.rangeRestrict x)).mpr (hMle h1)
  let N : Subgroup (↥X ⧸ Q) := (ψ.ker).map (QuotientGroup.mk' Q)
  have hNnormal : N.Normal :=
    (MonoidHom.normal_ker ψ).map (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  rcases (haveI := hNnormal; hsimple.eq_bot_or_eq_top_of_normal N) with hNbot | hNtop
  ·
    have hQ' : ψ.ker = Q := by
      refine le_antisymm ?_ hQψ
      intro x hx
      have hxN : QuotientGroup.mk' Q x ∈ N := Subgroup.mem_map_of_mem _ hx
      rw [hNbot] at hxN
      simpa using hxN
    have e : (↥X ⧸ Q) ≃* (↥H ⧸ CFSG.pCore 2 ↥H) :=
      (QuotientGroup.quotientMulEquivOfEq hQ'.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
    exact (hS H hHperf hHcore).false e.symm
  ·
    have hQtop : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxN : QuotientGroup.mk' Q x ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxN
      have h2 : QuotientGroup.mk' Q (y⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have h3 : y⁻¹ * x ∈ Q := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : y * (y⁻¹ * x) ∈ ψ.ker := ψ.ker.mul_mem hy (hQψ h3)
      simpa [mul_assoc] using h4
    have hHle : H ≤ CFSG.Open.pCoreOf 2 H := by
      intro y hy
      obtain ⟨x, hx⟩ := f.rangeRestrict_surjective (⟨y, hy⟩ : ↥H)
      have h1 : ψ x = 1 := by
        have hx' : x ∈ ψ.ker := by rw [hQtop]; exact Subgroup.mem_top x
        exact hx'
      have h3 : f.rangeRestrict x ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
      rw [hx] at h3
      exact Subgroup.mem_map_of_mem H.subtype h3
    exfalso
    have hHnt : Nontrivial ↥H := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      haveI := hnt
      exact hMne (Subgroup.ext fun x => by
        rw [Subgroup.mem_bot]
        exact ⟨fun _ => Subsingleton.elim (x : ↥H) 1, fun h => h ▸ (Q.map f.rangeRestrict).one_mem⟩)
    have hHp : IsPGroup 2 ↥H := by
      intro y
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hHle y.2)
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2
        (⟨z, hz⟩ : CFSG.pCore 2 ↥H)
      refine ⟨n, ?_⟩
      have h1 : z ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      refine H.subtype_injective ?_
      rw [map_pow, map_one, show H.subtype y = H.subtype z from hzy.symm, ← map_pow, h1, map_one]
    haveI hnil : Group.IsNilpotent ↥H := hHp.isNilpotent
    haveI := hHperf
    have hsol : Group.IsSolvable ↥H := inferInstance
    exact absurd hsol (Group.IsPerfect.not_isSolvable ↥H)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

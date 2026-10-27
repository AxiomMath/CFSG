module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Bar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

namespace HS6

section BarEquiv

variable {G : Type} [Group G] {M Q : Subgroup G} [(Q.subgroupOf M).Normal]

noncomputable def barHom {S : Subgroup G} (hSM : S ≤ M) : ↥S →* ↥(bar M Q S) :=
  ((QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)).codRestrict (bar M Q S)
    (fun s => ⟨Subgroup.inclusion hSM s, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩)

theorem barHom_surjective {S : Subgroup G} (hSM : S ≤ M) :
    Function.Surjective (barHom (Q := Q) hSM) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, hgS, hgM, rfl⟩ := (mem_bar y).mp hy
  exact ⟨⟨g, hgS⟩, Subtype.ext (by
    show QuotientGroup.mk (Subgroup.inclusion hSM ⟨g, hgS⟩) = piM M Q g
    rw [piM_of_mem hgM]; rfl)⟩

theorem barHom_ker {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) :
    (barHom (Q := Q) hSM).ker = Q.subgroupOf S := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : QuotientGroup.mk (Subgroup.inclusion hSM s) = (1 : ↥M ⧸ Q.subgroupOf M) :=
      congrArg Subtype.val h
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (Subgroup.inclusion hSM s)).mp h1)
  · intro h
    apply Subtype.ext
    show QuotientGroup.mk (Subgroup.inclusion hSM s) = (1 : ↥M ⧸ Q.subgroupOf M)
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (Subgroup.inclusion hSM s)).mpr
      (Subgroup.mem_subgroupOf.mpr h)

@[expose] noncomputable def barEquiv {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M)
    [(Q.subgroupOf S).Normal] :
    (↥S ⧸ Q.subgroupOf S) ≃* ↥(bar M Q S) :=
  (QuotientGroup.quotientMulEquivOfEq (barHom_ker hQS hSM).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (barHom_surjective hSM))

theorem bar_normal {S : Subgroup G} (hQM : Q ≤ M) (hS : ∀ g ∈ M, conjSubgroup g S = S) :
    (bar M Q S).Normal := by
  refine ⟨fun y hy gb => ?_⟩
  obtain ⟨g, hg, rfl⟩ := exists_piM gb
  have h1 : conjSubgroup (piM M Q g) (bar M Q S) = bar M Q S := by
    rw [conj_bar hQM hg, hS g hg]
  have : piM M Q g * y * (piM M Q g)⁻¹ ∈ conjSubgroup (piM M Q g) (bar M Q S) := by
    rw [mem_conjSubgroup, show (piM M Q g)⁻¹ * (piM M Q g * y * (piM M Q g)⁻¹) * piM M Q g = y
      by group]
    exact hy
  rwa [h1] at this

theorem bar_normalizer {N : Subgroup G} (hQM : Q ≤ M) (hQN : Q ≤ N) (hNM : N ≤ M) :
    bar M Q (Subgroup.normalizer (N : Set G) ⊓ M) =
      Subgroup.normalizer ((bar M Q N : Subgroup _) : Set _) := by
  have hQn : ∀ x ∈ Q, ∀ k ∈ M, k * x * k⁻¹ ∈ Q := by
    intro x hx k hk
    have hn : (Q.subgroupOf M).Normal := inferInstance
    have := hn.conj_mem ⟨x, hQM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩
    exact Subgroup.mem_subgroupOf.mp this
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, hgM, rfl⟩ := (mem_bar y).mp hy
    exact piM_mem_normalizer hQM hgM (conjSubgroup_eq_self_iff.mpr hg.1)
  · intro hy
    obtain ⟨h, hhM, rfl, hhN⟩ := exists_lift_normalizer hQM hQn hQN hNM hy
    exact piM_mem_bar ⟨conjSubgroup_eq_self_iff.mp hhN, hhM⟩ hhM

end BarEquiv

end HS6

end CFSG.RankThree.GF2n.Stroth80

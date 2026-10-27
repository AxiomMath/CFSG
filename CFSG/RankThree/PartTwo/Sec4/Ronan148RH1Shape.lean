module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Core

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Shape

variable {S : Type} [Group S]

theorem autFix_eq_fixSubgroup (β : MulAut S) : Sec4.autFix β = fixSubgroup β := by
  ext x
  rw [mem_fixSubgroup]
  rfl

variable [Finite S]

theorem good427_of_compShape {T : ∀ (Q : Type) [Group Q], Prop}
    (hT : ∀ (Q : Type) [Group Q], T Q → ¬ IsA5Type Q) {β : MulAut S} (h : CompShape T β) :
    Good427 (fixSubgroup β) := by
  set C := fixSubgroup β with hCdef
  intro K hKC hKq hKs hA5
  haveI : Group.IsPerfect K := hKq.1
  set T' := K ⧸ CFSG.pCore 2 K
  haveI : Group.IsPerfect T' := inferInstance
  haveI hTs : IsSimpleGroup T' := hA5.isSimpleGroup
  haveI : Nontrivial T' := hA5.nontrivial
  have hcompN : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L C →
      ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro L hL g hg l hl
    have hg' : β g = g := hg
    have hcomm : MulAut.conj g * β = β * MulAut.conj g := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hg']
    have hmap := h.norm (MulAut.conj g) hcomm L hL
    have : (MulAut.conj g).toMonoidHom l ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rw [hmap] at this
    exact this
  have hdich : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L C →
      L ≤ K ∨ ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
    intro L hL
    have hLC : L ≤ C := hL.1
    have hLq : IsQuasisimple L := isQuasisimple_of_open hL.2.2
    set L' : Subgroup C := L.subgroupOf C
    have hL'n : L'.Normal := by
      constructor
      intro a ha g
      exact hcompN L hL g g.2 a ha
    have hL'c : IsComponent L' :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hLq,
        hL'n.isSubnormal⟩
    rcases CFSG.LocalCores.component_subnormal_subgroup hL'c hKs with h1 | h1
    · left
      intro l hl
      have : (⟨l, hLC hl⟩ : C) ∈ K.subgroupOf C := h1 hl
      exact this
    · right
      intro l hl k hk
      have hmem : ⁅(⟨l, hLC hl⟩ : C), (⟨k, hKC hk⟩ : C)⁆ ∈ ⁅L', K.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator hl hk
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact congrArg Subtype.val hmem
  have hlay : K ≤ CFSG.Open.GLALayer C :=
    h.layer K hKC (Subgroup.commutator_eq_self (H := K))
  obtain ⟨L, hL, hLK⟩ : ∃ L : Subgroup S, CFSG.Open.IsComponentOf L C ∧ L ≤ K := by
    by_contra hno
    push Not at hno
    have hcent : CFSG.Open.GLALayer C ≤ Subgroup.centralizer (K : Set S) := by
      apply sSup_le
      rintro L hL
      rcases hdich L hL with h1 | h1
      · exact absurd h1 (hno L hL)
      · intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (h1 l hl k hk).symm
    have hab : ⁅K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hlay.trans hcent)
    rw [Subgroup.commutator_eq_self] at hab
    haveI : Subsingleton K := by
      rw [hab]
      infer_instance
    haveI : Subsingleton T' := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) |>.subsingleton
    exact not_subsingleton T' inferInstance
  have hLq : IsQuasisimple L := isQuasisimple_of_open hL.2.2
  set π : K →* T' := QuotientGroup.mk' (CFSG.pCore 2 K)
  set ψ : L →* T' := π.comp (Subgroup.inclusion hLK)
  have hψn : ψ.range.Normal := by
    constructor
    rintro _ ⟨l, rfl⟩ t
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) t
    refine ⟨⟨k * l * k⁻¹, hcompN L hL k (hKC k.2) l l.2⟩, ?_⟩
    show π (Subgroup.inclusion hLK _) = π k * π (Subgroup.inclusion hLK l) * (π k)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  haveI : Group.IsPerfect L := hLq.1
  haveI : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  have hψs : Function.Surjective ψ := by
    rcases hψn.eq_bot_or_eq_top with h1 | h1
    · exfalso
      have hker : ∀ l : L, ψ l = 1 := fun l => by
        have : ψ l ∈ ψ.range := ⟨l, rfl⟩
        rw [h1, Subgroup.mem_bot] at this
        exact this
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : IsPGroup 2 L := by
        intro l
        have hl : (Subgroup.inclusion hLK l) ∈ CFSG.pCore 2 K := by
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 K)]
          exact hker l
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, hl⟩
        refine ⟨n, ?_⟩
        apply Subtype.ext
        have := congrArg (fun y : CFSG.pCore 2 K => ((y : K) : S)) hn
        simpa using this
      exact not_isPGroup_of_isPerfect h2
    · intro t
      have : t ∈ ψ.range := h1 ▸ Subgroup.mem_top t
      exact this
  have hkerZ : ψ.ker = Subgroup.center L := by
    have hZT : Subgroup.center T' = ⊥ := by
      rcases (inferInstance : (Subgroup.center T').Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        have hcomm : ∀ a b : T', a * b = b * a := fun a b =>
          Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a
        have hab : ⁅(⊤ : Subgroup T'), (⊤ : Subgroup T')⁆ = (⊥ : Subgroup T') := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a _
          rw [Subgroup.mem_centralizer_iff]
          intro b _
          exact hcomm b a
        have htop : commutator T' = ⊤ := Group.IsPerfect.commutator_eq_top
        rw [commutator_def, hab] at htop
        exact bot_ne_top htop
    refine le_antisymm ?_ ?_
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker ψ) with h1 | h1
      · exfalso
        have : ∀ t : T', t = 1 := by
          intro t
          obtain ⟨l, rfl⟩ := hψs t
          have : l ∈ ψ.ker := h1 ▸ Subgroup.mem_top l
          exact this
        exact not_subsingleton T' ⟨fun a b => by rw [this a, this b]⟩
      · exact h1
    · intro z hz
      have hzc : ψ z ∈ Subgroup.center T' := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨l, rfl⟩ := hψs t
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz l)]
      rw [hZT, Subgroup.mem_bot] at hzc
      exact hzc
  have eT : T' ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hkerZ)
  exact hT _ (h.type L hL) (hA5.congr eT.symm)

theorem noCfgS427_of_compShape {T : ∀ (Q : Type) [Group Q], Prop}
    (hT : ∀ (Q : Type) [Group Q], T Q → ¬ IsA5Type Q)
    (h : ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → CompShape T β) : NoCfgS427 S := by
  intro β h3 h1
  rw [autFix_eq_fixSubgroup]
  exact good427_of_compShape hT (h β h3 h1)

end Shape

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end

module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowTriRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

local instance triGenNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

@[expose] def triRootA2 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 0, 0, 0, 0]

@[expose] def triRootA3 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 0, 0, 0]

@[expose] def triRootB13 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 0, 0, 0]

@[expose] def triRootB134 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 0, 0]

@[expose] def triRootB34 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 0, 0]

theorem triGen_check :
    (triOverlapB triRootA4 triRootA1 = true ∧ triOverlapB triRootA4 (-triRootA1) = true ∧
      permLattice TwistTag.E6.perm triRootA1 ≠ triRootA1 ∧
      permLattice TwistTag.E6.perm (-triRootA1) ≠ -triRootA1) ∧
    (triOverlapB triRootG3 triRootA4 = true ∧ triOverlapB triRootG3 (-triRootA4) = true ∧
      permLattice TwistTag.E6.perm (-triRootA4) = -triRootA4 ∧
      triOverlapB triRootG3 triRootB13 = true ∧ triOverlapB triRootG3 (-triRootB13) = true ∧
      permLattice TwistTag.E6.perm triRootB13 ≠ triRootB13 ∧
      permLattice TwistTag.E6.perm (-triRootB13) ≠ -triRootB13 ∧
      triOverlapB triRootG3 triRootB134 = true ∧ triOverlapB triRootG3 (-triRootB134) = true ∧
      permLattice TwistTag.E6.perm triRootB134 ≠ triRootB134 ∧
      permLattice TwistTag.E6.perm (-triRootB134) ≠ -triRootB134) ∧
    (triOverlapB triRootA4 triRootA6 = true ∧ triOverlapB triRootA4 (-triRootA6) = true ∧
      permLattice TwistTag.E6.perm triRootA6 ≠ triRootA6 ∧
      permLattice TwistTag.E6.perm (-triRootA6) ≠ -triRootA6 ∧
      permLattice TwistTag.E6.perm (-triRootA6) = -triRootA1 ∧
      permLattice TwistTag.E6.perm (-triRootB234) = -triRootB245 ∧
      twistedE6TwoRootB triRootA6 = true) ∧
    (triPairB (-triRootA1) triRootB13 triRootA3 = true ∧
      triPairB triRootA1 (-triRootB13) (-triRootA3) = true ∧
      triPairB (-triRootB134) triRootA1 (-triRootB34) = true ∧
      triPairB triRootB134 (-triRootA1) triRootB34 = true ∧
      triFixedB (-triRootB34) triRootB234 triRootA2 = true ∧
      triFixedB triRootB34 (-triRootB234) (-triRootA2) = true) := by
  decide +kernel

variable {K : Type} [Field K]


theorem coe_orbitXY_of_card_two_tri (σ : K →+* K) {a : Fin TwistTag.E6.foldedTag.rank}
    {i j : Fin TwistTag.E6.tag.rank} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hA : (TwistTag.E6.orbit a).card = 2) (hm : TwistTag.E6.orbitMin a = i)
    (hp : TwistTag.E6.perm i = j) (hi : Pi.single i 1 = β)
    (hj : Pi.single j 1 = permLattice TwistTag.E6.perm β) (c : orbitField TwistTag.E6 K σ a) :
    (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) = twistedE6PairX σ β c ∧
      (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) = twistedE6PairX σ (-β) c := by
  have hj' : -(Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      permLattice TwistTag.E6.perm (-β) := by
    rw [hj]
    rfl
  constructor
  · rw [coe_orbitX, hA, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, hm, hp,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
    rw [twistedE6PairX, ← hj, ← hi, pinnedX_single, pinnedX_single]
  · rw [coe_orbitY, hA, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, hm, hp,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
    rw [twistedE6PairX, ← hj', ← hi, pinnedX_neg_single, pinnedX_neg_single]

theorem coe_orbitXY_of_card_one_tri (σ : K →+* K) {a : Fin TwistTag.E6.foldedTag.rank}
    {i : Fin TwistTag.E6.tag.rank} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hA : (TwistTag.E6.orbit a).card = 1) (hm : TwistTag.E6.orbitMin a = i)
    (hi : Pi.single i 1 = β) (c : orbitField TwistTag.E6 K σ a) :
    σ c = c ∧
      (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K β c ∧
        (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) =
          pinnedX TwistTag.E6.tag K (-β) c := by
  refine ⟨?_, ?_, ?_⟩
  · have h := mem_orbitField.1 c.2
    rwa [hA, pow_one] at h
  · rw [coe_orbitX, hA, List.range_one]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero, hm,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
    rw [← hi, pinnedX_single]
  · rw [coe_orbitY, hA, List.range_one]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero, hm,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
    rw [← hi, pinnedX_neg_single]

theorem exists_add_sigma_eq_one_tri (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) : ∃ c₀ : K, c₀ + σ c₀ = 1 := by
  have : CharP K 2 := charP_two_of_card le_rfl hK
  obtain ⟨c, hc⟩ := exists_apply_ne le_rfl hK hσ
  refine ⟨c, ?_⟩
  have hfix : σ (c + σ c) = c + σ c := by
    rw [map_add, apply_apply_eq hK hσ, add_comm]
  have he0 : c + σ c ≠ 0 := by
    intro h
    apply hc
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  have hsq : (c + σ c) * (c + σ c) = (c + σ c) * 1 := by
    rw [mul_one, ← sq]
    rw [hσ, pow_one] at hfix
    exact hfix
  exact mul_left_cancel₀ he0 hsq

theorem graphFixedRootGroup_le_sup_tri (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {O₁ O₂ O₃ : Subgroup (ModGL TwistTag.E6.tag K)}
    (h₁ : TriOverlapRoots σ triRootA4 O₁) (h₂ : TriOverlapRoots σ triRootG3 O₂)
    (h₃ : TriOverlapRoots σ triRootA4 O₃) :
    graphFixedRootGroup TwistTag.E6 K σ ≤
      O₁ ⊔ O₂ ⊔ O₃.map (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom := by
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨c₀, hc₀⟩ := exists_add_sigma_eq_one_tri hK hσ
  obtain ⟨⟨o1, o1', o1ρ, o1ρ'⟩, ⟨o2a, o2a', o2aρ', o2b, o2b', o2bρ, o2bρ', o2c, o2c', o2cρ,
    o2cρ'⟩, ⟨o3, o3', o3ρ, o3ρ', ρa6, ρb234, ra6⟩, ⟨p1, p2, p3, p4, f1, f2⟩⟩ := triGen_check
  obtain ⟨-, -, -, -, -, -, -, ⟨w6, w6'⟩, ⟨w1, w1'⟩⟩ := triTransport_check
  obtain ⟨-, -, hρA4, -, -, -, -, -, ρa6', ρb234', -⟩ := triRoots_check
  set n := twistedE6RelWeyl K triWord2 with hn
  set O := O₁ ⊔ O₂ ⊔ O₃.map (MulAut.conj n).toMonoidHom with hO
  have m₁ : ∀ {x}, x ∈ O₁ → x ∈ O := fun hx => mem_sup_left (mem_sup_left hx)
  have m₂ : ∀ {x}, x ∈ O₂ → x ∈ O := fun hx => mem_sup_left (mem_sup_right hx)
  have m₃ : ∀ {x}, x ∈ O₃ → n * x * n⁻¹ ∈ O := fun hx => mem_sup_right ⟨_, hx, rfl⟩
  have yA1 : ∀ s, twistedE6PairX σ triRootA1 s ∈ O := fun s =>
    m₁ (twistedE6PairX_mem_of_triOverlapB h₁ o1 o1ρ s)
  have yA1' : ∀ s, twistedE6PairX σ (-triRootA1) s ∈ O := fun s =>
    m₁ (twistedE6PairX_mem_of_triOverlapB h₁ o1' o1ρ' s)
  have xA4 : ∀ {s : K}, σ s = s → pinnedX TwistTag.E6.tag K triRootA4 s ∈ O := fun hs =>
    m₂ (pinnedX_mem_of_triOverlapB h₂ o2a hρA4 hs)
  have xA4' : ∀ {s : K}, σ s = s → pinnedX TwistTag.E6.tag K (-triRootA4) s ∈ O := fun hs =>
    m₂ (pinnedX_mem_of_triOverlapB h₂ o2a' o2aρ' hs)
  have yB13 : ∀ s, twistedE6PairX σ triRootB13 s ∈ O := fun s =>
    m₂ (twistedE6PairX_mem_of_triOverlapB h₂ o2b o2bρ s)
  have yB13' : ∀ s, twistedE6PairX σ (-triRootB13) s ∈ O := fun s =>
    m₂ (twistedE6PairX_mem_of_triOverlapB h₂ o2b' o2bρ' s)
  have yB134 : ∀ s, twistedE6PairX σ triRootB134 s ∈ O := fun s =>
    m₂ (twistedE6PairX_mem_of_triOverlapB h₂ o2c o2cρ s)
  have yB134' : ∀ s, twistedE6PairX σ (-triRootB134) s ∈ O := fun s =>
    m₂ (twistedE6PairX_mem_of_triOverlapB h₂ o2c' o2cρ' s)
  have ha6 : IsRoot TwistTag.E6.tag triRootA6 := isRoot_of_triRootB ra6
  have yB234 : ∀ u, twistedE6PairX σ triRootB234 u ∈ O := fun u => by
    rw [← conj_twistedE6PairX_tri σ triWord2 ha6 w6 (by rw [ρa6', ρb234']; exact w1) u]
    exact m₃ (twistedE6PairX_mem_of_triOverlapB h₃ o3 o3ρ u)
  have yB234' : ∀ u, twistedE6PairX σ (-triRootB234) u ∈ O := fun u => by
    rw [← conj_twistedE6PairX_tri σ triWord2 (CFSG.LieType.Chevalley.IsRoot.neg ha6) w6'
      (by rw [ρa6, ρb234]; exact w1') u]
    exact m₃ (twistedE6PairX_mem_of_triOverlapB h₃ o3' o3ρ' u)
  have yA3 : ∀ s, twistedE6PairX σ triRootA3 s ∈ O := fun s => by
    rw [← mul_one s, ← commutator_twistedE6PairX_of_triPairB σ p1 s 1]
    exact commutatorElement_mem_tri (yA1' s) (yB13 1)
  have yA3' : ∀ s, twistedE6PairX σ (-triRootA3) s ∈ O := fun s => by
    rw [← mul_one s, ← commutator_twistedE6PairX_of_triPairB σ p2 s 1]
    exact commutatorElement_mem_tri (yA1 s) (yB13' 1)
  have yB34' : ∀ s, twistedE6PairX σ (-triRootB34) s ∈ O := fun s => by
    rw [← mul_one s, ← commutator_twistedE6PairX_of_triPairB σ p3 s 1]
    exact commutatorElement_mem_tri (yB134' s) (yA1 1)
  have yB34 : ∀ s, twistedE6PairX σ triRootB34 s ∈ O := fun s => by
    rw [← mul_one s, ← commutator_twistedE6PairX_of_triPairB σ p4 s 1]
    exact commutatorElement_mem_tri (yB134 s) (yA1' 1)
  have htr : ∀ {c : K}, σ c = c → c₀ * c * 1 + σ (c₀ * c * 1) = c := fun {c} hc => by
    rw [mul_one, map_mul, hc, ← add_mul, hc₀, one_mul]
  have xA2 : ∀ {c : K}, σ c = c → pinnedX TwistTag.E6.tag K triRootA2 c ∈ O := fun {c} hc => by
    rw [← htr hc, ← commutator_twistedE6PairX_of_triFixedB σ f1 (c₀ * c) 1]
    exact commutatorElement_mem_tri (yB34' _) (yB234 1)
  have xA2' : ∀ {c : K}, σ c = c → pinnedX TwistTag.E6.tag K (-triRootA2) c ∈ O :=
    fun {c} hc => by
      rw [← htr hc, ← commutator_twistedE6PairX_of_triFixedB σ f2 (c₀ * c) 1]
      exact commutatorElement_mem_tri (yB34 _) (yB234' 1)
  rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup hsurj]
  refine iSup_le fun a => (closure_le _).2 ?_
  fin_cases a <;> (try dsimp only) <;> rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> (try dsimp only) <;>
    rw [SetLike.mem_coe]
  · rw [(coe_orbitXY_of_card_two_tri σ (a := ⟨0, by decide⟩) (i := 0) (j := 5)
      (β := triRootA1) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) c).1]
    exact yA1 _
  · rw [(coe_orbitXY_of_card_two_tri σ (a := ⟨0, by decide⟩) (i := 0) (j := 5)
      (β := triRootA1) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) c).2]
    exact yA1' _
  · rw [(coe_orbitXY_of_card_two_tri σ (a := ⟨1, by decide⟩) (i := 2) (j := 4)
      (β := triRootA3) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) c).1]
    exact yA3 _
  · rw [(coe_orbitXY_of_card_two_tri σ (a := ⟨1, by decide⟩) (i := 2) (j := 4)
      (β := triRootA3) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) c).2]
    exact yA3' _
  · obtain ⟨hc, hx, -⟩ := coe_orbitXY_of_card_one_tri σ (a := ⟨2, by decide⟩) (i := 3)
      (β := triRootA4) (by decide) (by decide) (by decide +kernel) c
    rw [hx]
    exact xA4 hc
  · obtain ⟨hc, -, hy⟩ := coe_orbitXY_of_card_one_tri σ (a := ⟨2, by decide⟩) (i := 3)
      (β := triRootA4) (by decide) (by decide) (by decide +kernel) c
    rw [hy]
    exact xA4' hc
  · obtain ⟨hc, hx, -⟩ := coe_orbitXY_of_card_one_tri σ (a := ⟨3, by decide⟩) (i := 1)
      (β := triRootA2) (by decide) (by decide) (by decide +kernel) c
    rw [hx]
    exact xA2 hc
  · obtain ⟨hc, -, hy⟩ := coe_orbitXY_of_card_one_tri σ (a := ⟨3, by decide⟩) (i := 1)
      (β := triRootA2) (by decide) (by decide) (by decide +kernel) c
    rw [hy]
    exact xA2' hc

end CFSG.SeitzReduction.TwistedE6Pilot

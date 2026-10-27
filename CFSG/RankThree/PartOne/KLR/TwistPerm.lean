module

public import CFSG.RankThree.PartOne.KLR.RootKernel

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

section Perm

theorem eq_one_of_mul_self_eq_one_charTwo {ε : L} (hε : ε * ε = 1) : ε = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)

theorem canonicalRep_conj_pinnedX (v : WeylGroup ReeTag.F4.tag)
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) (c : L) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L v * pinnedX ReeTag.F4.tag L γ c *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ =
      pinnedX ReeTag.F4.tag L (v • γ) c := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L v hγ
  rw [h c, eq_one_of_mul_self_eq_one_charTwo hε, one_mul]

@[expose] def PermAct (g : ModGL ReeTag.F4.tag L) (v : WeylGroup ReeTag.F4.tag) : Prop :=
  ∀ γ, IsRoot ReeTag.F4.tag γ → ∀ c : L,
    g * pinnedX ReeTag.F4.tag L γ c * g⁻¹ = pinnedX ReeTag.F4.tag L (v • γ) c

theorem permAct_canonicalRep (v : WeylGroup ReeTag.F4.tag) :
    PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) v :=
  fun _ hγ c => canonicalRep_conj_pinnedX v hγ c

omit [CharP L 2] in
theorem PermAct.one : PermAct (1 : ModGL ReeTag.F4.tag L) 1 := by
  intro γ _ c
  simp

omit [CharP L 2] in
theorem PermAct.mul {g h : ModGL ReeTag.F4.tag L} {v w : WeylGroup ReeTag.F4.tag}
    (hg : PermAct g v) (hh : PermAct h w) : PermAct (g * h) (v * w) := by
  intro γ hγ c
  have e : g * h * pinnedX ReeTag.F4.tag L γ c * (g * h)⁻¹ =
      g * (h * pinnedX ReeTag.F4.tag L γ c * h⁻¹) * g⁻¹ := by group
  rw [e, hh γ hγ c, hg _ (IsRoot.smul hγ w) c, mul_smul]

omit [CharP L 2] in
theorem PermAct.inv {g : ModGL ReeTag.F4.tag L} {v : WeylGroup ReeTag.F4.tag}
    (hg : PermAct g v) : PermAct g⁻¹ v⁻¹ := by
  intro γ hγ c
  have h := hg (v⁻¹ • γ) (IsRoot.smul hγ v⁻¹) c
  rw [smul_inv_smul] at h
  rw [← h]
  group

end Perm

section FrobAction

omit [CharP L 2] in
theorem IsReeFrob.fext_xUnit (hF : IsReeFrob a F) (j : Fin ReeTag.F4.tag.rank) (c : L) :
    Fext F (xUnit ReeTag.F4.tag L j c) =
      xUnit ReeTag.F4.tag L (ReeTag.F4.perm j) (c ^ ReeTag.F4.relationExponent a j) := by
  rw [Fext_of_mem F (xUnit_mem_adjointGroup j c)]
  exact congrArg Subtype.val (hF j c).1

theorem IsReeFrob.fext_canonicalRep (hF : IsReeFrob a F) (v : WeylGroup ReeTag.F4.tag) :
    Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L v) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm v) := by
  rw [Fext_of_mem F (canonicalRep_mem_adjointGroup _ L v)]
  exact congrArg Subtype.val (hF.map_nrep v)

omit [CharP L 2] in
@[expose] def rootExp (a : ℕ) (α : Fin ReeTag.F4.tag.rank → ℤ) : ℕ :=
  if ReeTag.F4.quadForm α = 2 then 2 ^ (a + 1) else 2 ^ a

omit [CharP L 2] in
theorem rootExp_smul_single (a : ℕ) (v : WeylGroup ReeTag.F4.tag) (j : Fin ReeTag.F4.tag.rank) :
    rootExp a (v • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      ReeTag.F4.relationExponent a j := by
  unfold rootExp
  rw [quadForm_smul, ReeTag.F4_quadForm_single]
  by_cases hj : j ∈ ReeTag.F4.longSet
  · simp [hj, relExp_long a j hj]
  · simp [hj, relExp_short a j hj]

theorem IsReeFrob.fext_pinnedX (hF : IsReeFrob a F) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) (c : L) :
    Fext F (pinnedX ReeTag.F4.tag L α c) =
      pinnedX ReeTag.F4.tag L (ReeTag.F4.dualRoot α) (c ^ rootExp a α) := by
  obtain ⟨v, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  have hjr := isRoot_single ReeTag.F4.tag j
  have hjr' := isRoot_single ReeTag.F4.tag (ReeTag.F4.perm j)
  have h1 : pinnedX ReeTag.F4.tag L (v • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) c =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L v * xUnit ReeTag.F4.tag L j c *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ := by
    rw [← pinnedX_single, canonicalRep_conj_pinnedX v hjr c]
  rw [h1, Fext_conj F (canonicalRep_mem_adjointGroup _ L v) (xUnit_mem_adjointGroup j c),
    hF.fext_canonicalRep, hF.fext_xUnit, ← pinnedX_single,
    canonicalRep_conj_pinnedX _ hjr', ReeTag.dualRoot_smul v hjr, ReeTag.dualRoot_single,
    rootExp_smul_single]

theorem IsReeFrob.twist_pinnedX (hF : IsReeFrob a F) {n : ModGL ReeTag.F4.tag L}
    {w : WeylGroup ReeTag.F4.tag} (hn : PermAct n w) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) (c : L) :
    n * Fext F (pinnedX ReeTag.F4.tag L γ c) * n⁻¹ =
      pinnedX ReeTag.F4.tag L (w • ReeTag.F4.dualRoot γ) (c ^ rootExp a γ) := by
  rw [hF.fext_pinnedX hγ, hn _ (ReeTag.isRoot_dualRoot hγ)]

end FrobAction

section Transport

omit [CharP L 2] in
theorem conj_mem_twistedFixed_iff {N n g : ModGL ReeTag.F4.tag L}
    (hN : N ∈ adjointGroup ReeTag.F4.tag L) (hg : g ∈ adjointGroup ReeTag.F4.tag L) :
    N * g * N⁻¹ ∈ twistedFixed F (N * n * (Fext F N)⁻¹) ↔ g ∈ twistedFixed F n := by
  have hNg : N * g * N⁻¹ ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hN hg) (inv_mem hN)
  have key : N * n * (Fext F N)⁻¹ * Fext F (N * g * N⁻¹) * (N * n * (Fext F N)⁻¹)⁻¹ =
      N * (n * Fext F g * n⁻¹) * N⁻¹ := by
    rw [Fext_conj F hN hg]
    group
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hg, ?_⟩
    rw [key] at h
    have h2 : N * (n * Fext F g * n⁻¹) * N⁻¹ = N * g * N⁻¹ := h
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3
  · rintro ⟨-, h⟩
    refine ⟨hNg, ?_⟩
    rw [key, h]

omit [CharP L 2] in
theorem map_conj_inf_twistedFixed {N n : ModGL ReeTag.F4.tag L}
    (hN : N ∈ adjointGroup ReeTag.F4.tag L) (Q : Subgroup (ModGL ReeTag.F4.tag L))
    (hQ : Q ≤ adjointGroup ReeTag.F4.tag L) :
    (Q ⊓ twistedFixed F n).map (MulAut.conj N).toMonoidHom =
      Q.map (MulAut.conj N).toMonoidHom ⊓ twistedFixed F (N * n * (Fext F N)⁻¹) := by
  ext x
  constructor
  · rintro ⟨g, ⟨hgQ, hgT⟩, rfl⟩
    exact ⟨⟨g, hgQ, rfl⟩, (conj_mem_twistedFixed_iff hN hgT.1).2 hgT⟩
  · rintro ⟨⟨g, hgQ, rfl⟩, hx⟩
    exact ⟨g, ⟨hgQ, (conj_mem_twistedFixed_iff hN (hQ hgQ)).1 hx⟩, rfl⟩

omit [CharP L 2] in
theorem map_conj_rootSpan_inf_twistedFixed (u : WeylGroup ReeTag.F4.tag)
    {S : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot ReeTag.F4.tag γ)
    (n : ModGL ReeTag.F4.tag L) :
    (rootSpan ReeTag.F4.tag L S ⊓ twistedFixed F n).map
        (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom =
      rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S) ⊓
        twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u * n *
          (Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹) := by
  rw [map_conj_inf_twistedFixed (canonicalRep_mem_adjointGroup _ L u) _
    (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L S), map_conj_rootSpan u hS]

end Transport

end CFSG.RankThree.PartOne.KLR

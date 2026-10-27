module

public import CFSG.RankThree.PartOne.KLR.TwistPerm

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.RF4

section Norm

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def nseqF (n₀ : ModGL τ L) (F₀ : MulAut (adjointGroup τ L)) : ℕ → ModGL τ L
  | 0 => 1
  | k + 1 => n₀ * Fext F₀ (nseqF n₀ F₀ k)

theorem nseqF_succ (n₀ : ModGL τ L) (F₀ : MulAut (adjointGroup τ L)) (k : ℕ) :
    nseqF n₀ F₀ (k + 1) = n₀ * Fext F₀ (nseqF n₀ F₀ k) := rfl

theorem nseqF_mem {n₀ : ModGL τ L} (hn : n₀ ∈ adjointGroup τ L) (F₀ : MulAut (adjointGroup τ L))
    (k : ℕ) : nseqF n₀ F₀ k ∈ adjointGroup τ L := by
  induction k with
  | zero => exact one_mem _
  | succ k ih => exact mul_mem hn (Fext_mem F₀ ih)

theorem Fext_pow_apply (F₀ : MulAut (adjointGroup τ L)) {u : ModGL τ L}
    (hu : u ∈ adjointGroup τ L) (k : ℕ) :
    ((F₀ ^ k) ⟨u, hu⟩ : adjointGroup τ L) = (Fext F₀)^[k] u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, Function.iterate_succ_apply', ← ih]
    exact (Fext_of_mem F₀ ((F₀ ^ k) ⟨u, hu⟩).2).symm

theorem iterate_Fext_mem (F₀ : MulAut (adjointGroup τ L)) {u : ModGL τ L}
    (hu : u ∈ adjointGroup τ L) (k : ℕ) : (Fext F₀)^[k] u ∈ adjointGroup τ L := by
  rw [← Fext_pow_apply F₀ hu k]
  exact ((F₀ ^ k) ⟨u, hu⟩).2

theorem Fext_pow_eq_iterate (F₀ : MulAut (adjointGroup τ L)) {u : ModGL τ L}
    (hu : u ∈ adjointGroup τ L) (k : ℕ) : Fext (F₀ ^ k) u = (Fext F₀)^[k] u := by
  rw [Fext_of_mem _ hu]
  exact Fext_pow_apply F₀ hu k

theorem iterate_lang_nseqF {F₀ : MulAut (adjointGroup τ L)} {g₀ n₀ : ModGL τ L}
    (hg₀C : g₀ ∈ adjointGroup τ L) (hn₀C : n₀ ∈ adjointGroup τ L)
    (hg : Fext F₀ g₀ = g₀ * n₀) (k : ℕ) : (Fext F₀)^[k] g₀ = g₀ * nseqF n₀ F₀ k := by
  induction k with
  | zero => simp [nseqF]
  | succ k ih =>
    have hit : (Fext F₀)^[k] g₀ ∈ adjointGroup τ L := iterate_Fext_mem F₀ hg₀C k
    rw [Function.iterate_succ_apply', ih, Fext_mul F₀ hg₀C (nseqF_mem hn₀C F₀ k), hg, nseqF_succ,
      mul_assoc]

end Norm

section Weyl

variable {L : Type} [Field L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] noncomputable def nseqW (w₀ : WeylGroup ReeTag.F4.tag) : ℕ → WeylGroup ReeTag.F4.tag
  | 0 => 1
  | k + 1 => w₀ * ReeTag.F4.weylPerm (nseqW w₀ k)

theorem nseqW_succ (w₀ : WeylGroup ReeTag.F4.tag) (k : ℕ) :
    nseqW w₀ (k + 1) = w₀ * ReeTag.F4.weylPerm (nseqW w₀ k) := rfl

theorem rootExp_pos (a : ℕ) (α : Fin ReeTag.F4.tag.rank → ℤ) : 0 < rootExp a α := by
  unfold rootExp
  split_ifs <;> positivity

theorem rootExp_smul (a : ℕ) (w : WeylGroup ReeTag.F4.tag) (α : Fin ReeTag.F4.tag.rank → ℤ) :
    rootExp a (w • α) = rootExp a α := by
  unfold rootExp
  rw [quadForm_smul]

theorem permAct_fext [CharP L 2] [IsAlgClosed L] (hF : IsReeFrob a F)
    {m : ModGL ReeTag.F4.tag L} (hm : m ∈ adjointGroup ReeTag.F4.tag L)
    {v : WeylGroup ReeTag.F4.tag} (hv : PermAct m v) :
    PermAct (Fext F m) (ReeTag.F4.weylPerm v) := by
  intro γ hγ c
  have hβ : IsRoot ReeTag.F4.tag (ReeTag.F4.dualRoot γ) := ReeTag.isRoot_dualRoot hγ
  obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c (rootExp_pos a (ReeTag.F4.dualRoot γ))
  have hX : pinnedX ReeTag.F4.tag L γ c =
      Fext F (pinnedX ReeTag.F4.tag L (ReeTag.F4.dualRoot γ) c') := by
    rw [hF.fext_pinnedX hβ, ReeTag.dualRoot_dualRoot hγ, hc']
  have hXadj : pinnedX ReeTag.F4.tag L (ReeTag.F4.dualRoot γ) c' ∈ adjointGroup ReeTag.F4.tag L :=
    rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨c', rfl⟩)
  rw [hX, ← Fext_conj F hm hXadj, hv _ hβ, hF.fext_pinnedX (IsRoot.smul hβ v),
    ReeTag.dualRoot_smul v hβ, ReeTag.dualRoot_dualRoot hγ, rootExp_smul, hc']

theorem permAct_nseqF [CharP L 2] [IsAlgClosed L] (hF : IsReeFrob a F)
    {n₀ : ModGL ReeTag.F4.tag L} (hn₀C : n₀ ∈ adjointGroup ReeTag.F4.tag L)
    {w₀ : WeylGroup ReeTag.F4.tag} (hn₀ : PermAct n₀ w₀) (k : ℕ) :
    PermAct (nseqF n₀ F k) (nseqW w₀ k) := by
  induction k with
  | zero => exact PermAct.one
  | succ k ih =>
    exact hn₀.mul (permAct_fext hF (nseqF_mem hn₀C F k) ih)

end Weyl

section Stable

@[expose] noncomputable def tauMap (w₀ : WeylGroup ReeTag.F4.tag) (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    Fin ReeTag.F4.tag.rank → ℤ :=
  w₀ • ReeTag.F4.dualRoot γ

theorem isRoot_tauMap_iterate (w₀ : WeylGroup ReeTag.F4.tag) (k : ℕ)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) :
    IsRoot ReeTag.F4.tag ((tauMap w₀)^[k] β) := by
  induction k with
  | zero => exact hβ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact IsRoot.smul (ReeTag.isRoot_dualRoot ih) w₀

theorem isRoot_dualRoot_iterate (k : ℕ) {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : IsRoot ReeTag.F4.tag β) : IsRoot ReeTag.F4.tag ((ReeTag.F4.dualRoot)^[k] β) := by
  induction k with
  | zero => exact hβ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ReeTag.isRoot_dualRoot ih

theorem dualRoot_iterate_odd {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β)
    {p : ℕ} (hp : Odd p) : (ReeTag.F4.dualRoot)^[p] β = ReeTag.F4.dualRoot β := by
  obtain ⟨m, rfl⟩ := hp
  have h2 : ∀ m : ℕ, (ReeTag.F4.dualRoot)^[2 * m] β = β := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Function.iterate_succ_apply',
        Function.iterate_succ_apply', ReeTag.dualRoot_dualRoot (isRoot_dualRoot_iterate _ hβ), ih]
  have h3 := Function.iterate_succ_apply' ReeTag.F4.dualRoot (2 * m) β
  rw [h2] at h3
  exact h3

theorem tauMap_iterate (w₀ : WeylGroup ReeTag.F4.tag) (k : ℕ) {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : IsRoot ReeTag.F4.tag β) :
    (tauMap w₀)^[k] β = nseqW w₀ k • (ReeTag.F4.dualRoot)^[k] β := by
  induction k with
  | zero => simp [nseqW]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, tauMap, ReeTag.dualRoot_smul _ (isRoot_dualRoot_iterate k hβ),
      ← mul_smul, nseqW_succ, Function.iterate_succ_apply' (ReeTag.F4.dualRoot)]

theorem mem_iff_nseqW_smul_dualRoot {Sg : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    {w₀ : WeylGroup ReeTag.F4.tag}
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w₀ • ReeTag.F4.dualRoot β ∈ Sg ↔ β ∈ Sg))
    {p : ℕ} (hp : Odd p) {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) :
    nseqW w₀ p • ReeTag.F4.dualRoot β ∈ Sg ↔ β ∈ Sg := by
  have hit : ∀ k : ℕ, (tauMap w₀)^[k] β ∈ Sg ↔ β ∈ Sg := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', tauMap, hst _ (isRoot_tauMap_iterate w₀ k hβ), ih]
  rw [← dualRoot_iterate_odd hβ hp, ← tauMap_iterate w₀ p hβ]
  exact hit p

end Stable

end CFSG.RankThree.PartOne.TCX.Ree

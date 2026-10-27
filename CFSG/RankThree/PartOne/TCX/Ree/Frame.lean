module

public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartOne.TCX.Ree.Conj
public import CFSG.RankThree.PartOne.TCX.Ree.Engine

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4

section Norm

variable {τ : Tag} {L : Type} [Field L] {F₀ F : MulAut (adjointGroup τ L)}

theorem fext_lang_norm {p : ℕ} (hFF : F = F₀ ^ p) {g₀ n₀ : ModGL τ L}
    (hg₀C : g₀ ∈ adjointGroup τ L) (hn₀C : n₀ ∈ adjointGroup τ L)
    (hg : Fext F₀ g₀ = g₀ * n₀) : Fext F g₀ = g₀ * nseqF n₀ F₀ p := by
  rw [hFF, Fext_pow_eq_iterate F₀ hg₀C p, iterate_lang_nseqF hg₀C hn₀C hg p]

theorem Rg_eq_twistedFixed {C : Type} [Group C] {θ : C →* ModGL τ L}
    (hfix : ∀ y, Fext F (θ y) = θ y) (hrange : ∀ u ∈ adjointGroup τ L, Fext F u = u → u ∈ θ.range)
    (hθC : ∀ y, θ y ∈ adjointGroup τ L) {g₀ N : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L)
    (hFg : Fext F g₀ = g₀ * N) : Rg θ g₀ = twistedFixed F N := by
  ext u
  rw [mem_Rg]
  constructor
  · rintro ⟨y, hy⟩
    have : g₀⁻¹ * θ y * g₀ = u := by rw [hy]; group
    rw [← this]
    exact conj_mem_twistedFixed F hg₀C hFg (hθC y) (hfix y)
  · intro hu
    obtain ⟨hadj, hfx⟩ := fixed_of_mem_twistedFixed F hg₀C hFg hu
    exact hrange _ hadj hfx

theorem twistedFixed_le_Rg {p : ℕ} (hFF : F = F₀ ^ p) {C : Type} [Group C] {θ : C →* ModGL τ L}
    (hrange : ∀ u ∈ adjointGroup τ L, Fext F u = u → u ∈ θ.range)
    {g₀ n₀ : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L) (hg : Fext F₀ g₀ = g₀ * n₀) :
    twistedFixed F₀ n₀ ≤ Rg θ g₀ := by
  intro u hu
  rw [mem_Rg]
  obtain ⟨hadj, hfx⟩ := fixed_of_mem_twistedFixed F₀ hg₀C hg hu
  refine hrange _ hadj ?_
  rw [hFF, Fext_pow_eq_iterate F₀ hadj p]
  exact Function.iterate_fixed hfx p

end Norm

section Perm

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem permAct_conjTwist (hF : IsReeFrob a F) {n : ModGL ReeTag.F4.tag L}
    {w : WeylGroup ReeTag.F4.tag} (hn : PermAct n w) (u : WeylGroup ReeTag.F4.tag) :
    PermAct (conjTwist F u n) (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
  have hFN : Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    hF.fext_canonicalRep u
  unfold conjTwist
  rw [hFN]
  exact ((permAct_canonicalRep u).mul hn).mul (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv

omit [CharP L 2] in
theorem conjTwist_mem {n : ModGL ReeTag.F4.tag L} (hn : n ∈ adjointGroup ReeTag.F4.tag L)
    (u : WeylGroup ReeTag.F4.tag) : conjTwist F u n ∈ adjointGroup ReeTag.F4.tag L := by
  unfold conjTwist
  exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L u) hn)
    (inv_mem (Fext_mem F (canonicalRep_mem_adjointGroup _ L u)))

theorem phi0_mem_rootSpan [IsAlgClosed L] (hF : IsReeFrob a F) {w₀ : WeylGroup ReeTag.F4.tag}
    {Sg : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hS : ∀ γ ∈ Sg, IsRoot ReeTag.F4.tag γ)
    (hst : ∀ β ∈ Sg, w₀ • ReeTag.F4.dualRoot β ∈ Sg) {u : ModGL ReeTag.F4.tag L}
    (hu : u ∈ rootSpan ReeTag.F4.tag L Sg) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * Fext F u *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)⁻¹ ∈ rootSpan ReeTag.F4.tag L Sg := by
  have huadj : u ∈ adjointGroup ReeTag.F4.tag L := rootSpan_le_adjointGroup L Sg hu
  have h1 : Fext F u ∈ rootSpan ReeTag.F4.tag L (ReeTag.F4.dualRoot '' Sg) := by
    rw [Fext_of_mem F huadj]
    exact hF.mem_rootSpan hS (g := ⟨u, huadj⟩) hu
  have hS' : ∀ γ ∈ ReeTag.F4.dualRoot '' Sg, IsRoot ReeTag.F4.tag γ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ReeTag.isRoot_dualRoot (hS β hβ)
  have h2 := map_conj_rootSpan (L := L) w₀ hS'
  have h3 : canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * Fext F u *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)⁻¹ ∈
      rootSpan ReeTag.F4.tag L ((fun γ => w₀ • γ) '' (ReeTag.F4.dualRoot '' Sg)) := by
    rw [← h2]
    exact ⟨_, h1, by simp [MulAut.conj_apply]⟩
  refine rootSpan_mono ?_ h3
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
  exact hst β hβ

end Perm

section Torsion

variable {L : Type} [Field L] [CharP L 2]

theorem exists_odd_pow_eq_one_of_mem_torusGroup_ree (K : Type) [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ torusGroup ReeTag.F4.tag L) : ∃ m : ℕ, Odd m ∧ h ^ m = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hodd : ∀ i, Odd (orderOf (a i)) := fun i =>
    CFSG.RankThree.PartOne.KLCE.odd_orderOf_of_charTwo (a i)
      (CFSG.RankThree.PartOne.KLCE.isOfFinOrder_of_isAlgebraic (K := K) (a i))
  refine ⟨∏ i, orderOf (a i), ?_, ?_⟩
  · exact Finset.prod_induction _ Odd (fun x y hx hy => hx.mul hy) odd_one
      (fun i _ => hodd i)
  · have h1 : a ^ (∏ i, orderOf (a i)) = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      exact orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    have h2 := (rootDiagUnitHom ReeTag.F4.tag L).map_pow a (∏ i, orderOf (a i))
    rw [h1, map_one] at h2
    exact h2.symm

end Torsion

end CFSG.RankThree.PartOne.TCX.Ree

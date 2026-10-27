module

public import CFSG.RankThree.GF2n.Stroth80.Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem inf_centralizer_Z_eq (hc : Ctx M Q Z B) :
    Q ⊓ Subgroup.centralizer (Z : Set G) = Q := by
  refine inf_eq_left.mpr ?_
  intro y hy
  exact Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hy

theorem Ctx.inducesSL2 (hc : Ctx M Q Z B) :
    ∃ n : ℕ, Nat.card Z = 2 ^ n ∧ Tim78.InducesNaturalSL2 n (Q ⊔ QB B) (Z ⊔ B) ∧
      (Q ⊔ QB B) ⊓ Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G) =
        inSubgroup (pCore 2) (Q ⊔ QB B) := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hW : Z ⊔ B = Z ⊔ conjSubgroup g Z := by rw [hg]
  have hH : Q ⊔ QB B = Q ⊔ conjSubgroup g Q := by rw [hQB]
  obtain ⟨-, ⟨-, n, hn, hind⟩, -, -, -, -, hC⟩ :=
    Tim78.tim78_2_18 (g := g) hc.hyp.maxLocal hc.hyp.fitting hc.hyp.maxAb
      hc.hyp.toHyp79.sq_eq_one hc.hyp.ti hc.hyp.hQ hgV hgQ hc.hyp.q4
      (inf_centralizer_Z_eq hc).symm hW hH
  exact ⟨n, hn, hind, hC⟩

theorem Ctx.cartan (hc : Ctx M Q Z B) :
    ∃ k ∈ M ⊓ (Q ⊔ QB B), orderOf k = Nat.card Z - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, k ^ i * v = v * k ^ i → v = 1 := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  obtain ⟨k, hk, hko, hkreg⟩ :=
    Tim78.tim78_2_18_cartan (g := g) hc.hyp.maxLocal hc.hyp.fitting hc.hyp.maxAb
      hc.hyp.toHyp79.sq_eq_one hc.hyp.ti hc.hyp.hQ hgV hgQ hc.hyp.q4
      (inf_centralizer_Z_eq hc).symm
  refine ⟨k, ?_, hko, hkreg⟩
  rw [hQB]
  exact hk

theorem Ctx.inf_QB_elemAbelian (hc : Ctx M Q Z B) :
    Assembly.IsElemAbelian 2 (Q ⊓ QB B) := by
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hinf : Z ⊓ B = ⊥ := hc.inf_eq_bot
  have hmem : ∀ x ∈ Q ⊓ QB B, x ∈ Q ∧ x ∈ conjSubgroup g Q := by
    intro x hx
    rw [hQB] at hx
    exact Subgroup.mem_inf.mp hx
  have hcomm : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxQ, hxg⟩ := hmem x hx
    obtain ⟨hyQ, hyg⟩ := hmem y hy
    have h1 : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hxQ hyQ
    have h2 : ⁅x, y⁆ ∈ B := by
      rw [hg]
      exact hc.hyp.toHyp79.comm_mem_conj g hxg hyg
    have h3 : ⁅x, y⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hsq : ∀ x ∈ Q ⊓ QB B, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨hxQ, hxg⟩ := hmem x hx
    have h1 : x ^ 2 ∈ Z := hc.hyp.toHyp79.sq_mem_V hxQ
    have h2 : x ^ 2 ∈ B := by
      rw [hg]
      exact hc.hyp.toHyp79.sq_mem_conj g hxg
    have h3 : x ^ 2 ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hsq x hx⟩

end CFSG.RankThree.GF2n.Stroth80

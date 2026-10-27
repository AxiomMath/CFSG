module

public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.RankThree.GF2n.Stroth80.Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.sl2Model (hc : Ctx M Q Z B) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card Z = 2 ^ n ∧
      ∃ (φ : ↥(Q ⊔ QB B) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
        (ψ : ↥(Z ⊔ B) ≃* Multiplicative (Fin 2 → GaloisField 2 n)),
        Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G)).subgroupOf (Q ⊔ QB B) ∧
        (∀ (z : ↥(Q ⊔ QB B)) (w w' : ↥(Z ⊔ B)), (w' : G) = (z : G) * w * (z : G)⁻¹ →
          Multiplicative.toAdd (ψ w') =
            (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)) ∧
        (Q.subgroupOf (Q ⊔ QB B)).map φ = upperUnipotent (GaloisField 2 n) ∧
        ((QB B).subgroupOf (Q ⊔ QB B)).map φ = lowerUnipotent (GaloisField 2 n) ∧
        ∀ w : ↥(Z ⊔ B), (w : G) ∈ Z ↔ Multiplicative.toAdd (ψ w) 1 = 0 := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hP : Q = Q ⊓ Subgroup.centralizer (Z : Set G) := by
    refine (inf_eq_left.mpr fun y hy => ?_).symm
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hy
  have h : Tim78.Hyp218 M Z Q Q (Z ⊔ conjSubgroup g Z) g :=
    ⟨hc.hyp.maxLocal, hc.hyp.fitting, hc.hyp.maxAb, hc.hyp.toHyp79.sq_eq_one, hc.hyp.ti, hgV,
      hgQ, hc.hyp.hQ, hP, rfl⟩
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  subst hg
  obtain ⟨n, hn2, hVn, φ, ψ, hφs, hφker, hcompat, hφP, hφPg, -, hVψ⟩ :=
    h.exists_natural hxW hxV hy hc.hyp.q4 (H := Q ⊔ QB (conjSubgroup g Z)) (by rw [hQB])
  refine ⟨n, hn2, hVn, φ, ψ, hφs, hφker, hcompat, hφP, ?_, hVψ⟩
  have e : (QB (conjSubgroup g Z)).subgroupOf (Q ⊔ QB (conjSubgroup g Z)) =
      (conjSubgroup g Q).subgroupOf (Q ⊔ QB (conjSubgroup g Z)) :=
    congrArg (fun S : Subgroup G => S.subgroupOf (Q ⊔ QB (conjSubgroup g Z))) hQB
  rw [e]
  exact hφPg

module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

namespace CFSG
end CFSG
open CFSG

universe u v

namespace CFSG.Glauberman

/-- If `H` is involved in a quotient of `G`, then `H` is involved in `G`.

Given a subquotient `A ⧸ B` of `G ⧸ N`, take the full preimage `A₀` of `A`
in `G`.  The restricted quotient map `A₀ → A` is surjective, so composing it
with `A → A ⧸ B` realizes `A ⧸ B` as a quotient of `A₀`. -/
public theorem involved_of_involved_quotient {H : Type u} {G : Type v}
    [Group H] [Group G] (N : Subgroup G) [N.Normal]
    (h : Involved H (G ⧸ N)) : Involved H G := by
  classical
  rcases h with ⟨A, B, hB, ⟨e⟩⟩
  let : B.Normal := hB
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let A₀ : Subgroup G := A.comap q
  let f : ↥A₀ →* ↥A :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := by ext; simp [q]
      map_mul' := by
        intro x y
        ext
        simp [q] }
  have hf : Function.Surjective f := by
    intro a
    rcases QuotientGroup.mk'_surjective N (a : G ⧸ N) with ⟨g, hg⟩
    have hgA₀ : g ∈ A₀ := by
      change q g ∈ A
      rw [hg]
      exact a.property
    refine ⟨⟨g, hgA₀⟩, ?_⟩
    apply Subtype.ext
    exact hg
  let φ : ↥A₀ →* ↥A ⧸ B := (QuotientGroup.mk' B).comp f
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective B).comp hf
  let B₀ : Subgroup A₀ := φ.ker
  have hB₀ : B₀.Normal := inferInstance
  let E : A₀ ⧸ B₀ ≃* A ⧸ B :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨A₀, B₀, hB₀, ⟨E.trans e⟩⟩

end CFSG.Glauberman

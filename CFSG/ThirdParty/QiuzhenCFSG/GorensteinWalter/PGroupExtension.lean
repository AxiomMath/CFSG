module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Small p-group extension and quotient-action bridges

This module packages three generic steps used by the Gorenstein--Walter
minimal-counterexample argument: a normal `p`-complement with trivial
`p'`-core is a `p`-group, `p`-groups are closed under extensions, and the
conjugation action on a normal subgroup embeds the quotient by its
centralizer in the automorphism group.
-/

namespace CFSG.GorensteinWalter

universe u v

/-- A group with a normal `p`-complement and trivial `p'`-core is a
`p`-group. -/
public theorem isPGroup_of_normalPComplement_of_pPrimeCore_eq_bot
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G]
    (hNPC : Glauberman.NormalPComplement p G)
    (hcore : pPrimeCore p G = ⊥) : IsPGroup p G := by
  have hOp : Op_p'p p G = ⊤ := Glauberman.normalPComplement_eq_top hNPC
  have hpcore : pCore p G = ⊤ := by
    rw [← Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G) (p := p) hcore]
    exact hOp
  have htop : IsPGroup p (⊤ : Subgroup G) := by
    rw [← hpcore]
    exact pCore_isPGroup
  exact htop.of_equiv Subgroup.topEquiv

/-- Convert the existential normal-complement predicate used by the
Feit--Thompson transfer API into Glauberman's `O_{p',p}(G) = G` predicate. -/
public theorem normalPComplement_of_hasNormalPComplement
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (hcomp : HasNormalPComplement p G) :
    Glauberman.NormalPComplement p G := by
  let Q := G ⧸ pPrimeCore p G
  have hq : IsPGroup p Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) G hcomp
  have hqtop : IsPGroup p (⊤ : Subgroup Q) := hq.to_subgroup ⊤
  have hpcore : pCore p Q = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hqtop⟩
  apply Glauberman.normalPComplement_of_eq_top
  simp [Op_p'p, Q, hpcore]

/-- An extension of a `p`-group by a `p`-group is a `p`-group. -/
public theorem isPGroup_of_normal_subgroup_of_quotient
    {p : ℕ} {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  intro g
  obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk' N g)
  have hmem : g ^ p ^ k ∈ N := by
    rw [← QuotientGroup.ker_mk' (N := N), MonoidHom.mem_ker]
    simpa [map_pow] using hk
  obtain ⟨l, hl⟩ := hN ⟨g ^ p ^ k, hmem⟩
  have hl' : (g ^ p ^ k) ^ p ^ l = 1 := congrArg Subtype.val hl
  refine ⟨k + l, ?_⟩
  rw [pow_add, pow_mul]
  simpa using hl'

/-- Conjugation on a normal subgroup gives a faithful action of the quotient
by its centralizer on that subgroup. -/
public theorem quotient_centralizer_mulAut_embedding
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal] :
    ∃ φ : (G ⧸ Subgroup.centralizer (H : Set G)) →* MulAut H,
      Function.Injective φ := by
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let f : G →* MulAut H := MulAut.conjNormal
  have hCker : C = f.ker := by
    ext g
    simp only [C, f, MonoidHom.mem_ker]
    constructor
    · intro hg
      ext x
      rw [MulAut.conjNormal_apply]
      change g * (x : G) * g⁻¹ = x
      rw [← (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2]
      simp
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' := congrArg (fun a : H => (a : G)) (DFunLike.congr_fun hg ⟨x, hx⟩)
      change g * x * g⁻¹ = x at hx'
      calc
        x * g = (g * x * g⁻¹) * g := by rw [hx']
        _ = g * x := by group
  let φ : (G ⧸ C) →* MulAut H := QuotientGroup.lift C f hCker.le
  refine ⟨φ, ?_⟩
  exact (QuotientGroup.injective_lift_iff C f hCker.le).mpr hCker

end CFSG.GorensteinWalter

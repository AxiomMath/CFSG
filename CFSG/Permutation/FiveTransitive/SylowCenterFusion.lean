module

public import CFSG.Permutation.FiveTransitive.SylowTwoSmallOrbit

public section

namespace CFSG

namespace FiveTransitive.SylowCenterFusion

private theorem normalizer_conj_eq
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (q r : G)
    (hq : q ∈ Subgroup.centralizer (P : Set G))
    (horbit : ∀ n ∈ Subgroup.normalizer (P : Set G),
      n * q * n⁻¹ = q ∨ n * q * n⁻¹ = r) :
    ∀ n ∈ Subgroup.normalizer (P : Set G), n * q * n⁻¹ = q := by
  let _ : MulAction G G := MulAction.compHom G ConjAct.toConjAct.toMonoidHom
  let N := Subgroup.normalizer (P : Set G)
  let R : Sylow 2 N := P.subtype (P : Subgroup G).le_normalizer
  have hR : ∀ p : R, (p : N) • q = q := by
    intro p
    change (p.val.val : G) * q * (p.val.val : G)⁻¹ = q
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Subgroup.mem_centralizer_iff.mp hq p.val.val p.property
  have hsmall : ∀ n : N, n • q = q ∨ n • q = r := by
    intro n
    exact horbit n.val n.property
  have hfix := SylowTwoSmallOrbit.smul_eq_of_smul_eq_or R q r hR hsmall
  intro n hn
  exact hfix ⟨n, hn⟩

theorem eq_of_conjugate_of_normalizer_conj_eq_or
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (q r : G)
    (hq : q ∈ Subgroup.centralizer (P : Set G))
    (hr : r ∈ Subgroup.centralizer (P : Set G))
    (horbit : ∀ n ∈ Subgroup.normalizer (P : Set G),
      n * q * n⁻¹ = q ∨ n * q * n⁻¹ = r)
    (hconj : ∃ g : G, g * q * g⁻¹ = r) : q = r := by
  obtain ⟨g, hg⟩ := hconj
  have hcentral : (g⁻¹)⁻¹ * q * g⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    simpa only [inv_inv, hg] using hr
  obtain ⟨n, hn, heq⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer q g⁻¹ hq hcentral
  have hfix := normalizer_conj_eq P q r hq horbit n⁻¹
    ((Subgroup.normalizer (P : Set G)).inv_mem hn)
  calc
    q = n⁻¹ * q * n := by simpa only [inv_inv] using hfix.symm
    _ = r := by simpa only [inv_inv, hg] using heq.symm

end FiveTransitive.SylowCenterFusion

end CFSG

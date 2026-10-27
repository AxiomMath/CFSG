module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6S34

variable {G : Type*} [Group G]

theorem eq_or_eq_of_singleOrbit [Finite G] {p : ℕ} (hp : p.Prime) {K U : Subgroup G}
    (hK : IsSemisimple K) {c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hcp : c ^ p = 1)
    (hmove : ∀ J ∈ lcal K, c ∉ Subgroup.normalizer (J : Set G))
    (horb : ∀ J ∈ lcal K, ∀ J' ∈ lcal K,
      ∃ g ∈ Subgroup.zpowers c, J' = J.map (MulAut.conj g).toMonoidHom)
    (hUK : U ≤ K) (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hC : K ⊓ Subgroup.centralizer {c} ≤ U) :
    U = K ⊓ Subgroup.centralizer {c} ∨ U = K := by
  have hKdp : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  have hZK : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hcK
  have hZU : Subgroup.zpowers c ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.zpowers_le.mpr hcU
  have hprojC : ∀ J ∈ lcal K, projIn (lcal K) J (K ⊓ Subgroup.centralizer {c}) = J :=
    fun J hJ => Nonsolv.Diag.projIn_inf_centralizer_eq_self hp hKdp hcK hcp hJ (hmove J hJ)
  have hproj : ∀ J ∈ lcal K, projIn (lcal K) J U = J := fun J hJ =>
    le_antisymm (projIn_le J U) ((hprojC J hJ).symm.le.trans (Nonsolv.Diag.projIn_mono J hC))
  by_cases hex : ∃ J₀ ∈ lcal K, J₀ ≤ U
  ·
    right
    obtain ⟨J₀, hJ₀, hJ₀U⟩ := hex
    refine le_antisymm hUK ?_
    rw [← hKdp.sSup_eq]
    refine sSup_le fun J hJ => ?_
    obtain ⟨g, hg, rfl⟩ := horb J₀ hJ₀ J hJ
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hZU hg) x).mp (hJ₀U hx)
  ·
    left
    push Not at hex
    have hAS : ∀ b ∈ Subgroup.zpowers c, ∀ J ∈ lcal K,
        J.map (MulAut.conj b).toMonoidHom ∈ lcal K :=
      fun b hb J hJ => map_conj_mem_lcal hJ (hZK hb)
    have hsame : ∀ J ∈ lcal K,
        Nonsolv.Diag.SameBlock (lcal K) U J (J.map (MulAut.conj c).toMonoidHom) := by
      intro J hJ
      obtain hle | ⟨J₁, hJ₁, hne, hJ₁same⟩ :=
        Nonsolv.Diag.exists_le_or_sameBlock hK hUK hproj hJ
      · exact absurd hle (hex J hJ)
      · obtain ⟨g, hg, rfl⟩ := Nonsolv.Diag.mem_conjOrbit_of_sameBlock hp hKdp hcK hcp hJ
          (hmove J hJ) hC hJ₁ hJ₁same
        exact Nonsolv.Diag.sameBlock_map_conj_of_ne hp (Subgroup.mem_zpowers c) hcp hAS hZU hg
          hne hJ₁same
    have hle : U ≤ Subgroup.centralizer {c} :=
      Nonsolv.Diag.le_centralizer_of_forall_sameBlock hKdp
        (fun J hJ => map_conj_mem_lcal hJ hcK) (fun J hJ => map_conj_mem_lcal hJ (inv_mem hcK))
        hUK hC hprojC hsame
    exact le_antisymm (le_inf hUK hle) hC

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6S34

module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

namespace LinModel

variable {m : ℕ} {G : Type} [Group G]

theorem torusModel_of_sl (h4 : GGLinearRegularConjInput) (h5 : GGLinearTypeAkTripleInput)
    [Finite G] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p) (hf : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs)
    (hNBs : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ψ.range : Set G))
    (hfield : p ∣ f → ∀ y ∈ Subgroup.normalizer (ψ.range : Set G), y ^ p = 1 →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (y, A) ∈ LinFusion.ggInducedPairs ψ)
    (hyex : ∃ y ∈ Subgroup.normalizer (ψ.range : Set G), orderOf y = p ∧
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g⁻¹ * y * g ∉ Bs) :
    (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
      IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
        Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G))) ∧
    ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) →
      z ^ p = 1 → ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs ψ.range f z v := by
  have hp2 : p ≠ 2 := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hm : 2 ≤ m := by omega
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpf
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpF
  set ω : (GaloisField 2 f)ˣ := (hζ.isUnit hp.ne_zero).unit with hωdef
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hωdef, IsUnit.unit_spec]; exact hζ)
  obtain ⟨P, hBsD, hW⟩ := exists_frame_of_sl hp hp5 hmp hf hpf hker hC hBsM hBsE hBsI hom hU
  set ψ' := ψ.comp (InnerDiagA.conjSL P⁻¹) with hψ'
  have hker' := LinTorus.ker_comp_conjSL_le hker P⁻¹
  have hrange' : ψ'.range = ψ.range := LinTorus.range_comp_conjSL ψ P⁻¹
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by rw [hrange']; exact hC
  have hBs : rootTorus p ψ' = Bs := le_antisymm hW (le_rootTorus hker' hBsD hBsE.2)
  obtain ⟨y, hyM, hyo, hy⟩ := hyex
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hreal : ∀ A : GL (Fin (m + 1)) (GaloisField 2 f), ∃ g : G,
      (g, A) ∈ LinFusion.ggInducedPairs ψ' := by
    by_contra hne
    push Not at hne
    obtain ⟨A₁, hA₁⟩ := hne
    have hdetall : ∀ (g : G) (A : GL (Fin (m + 1)) (GaloisField 2 f)),
        (g, A) ∈ LinFusion.ggInducedPairs ψ' → ∃ c, c ^ p = GeneralLinearGroup.det A := by
      intro g A h
      by_contra hnd
      obtain ⟨g', hg'⟩ := exists_mem_of_det hmp h hnd A₁
      exact hA₁ g' hg'
    obtain ⟨Y, hY⟩ : ∃ Y : GL (Fin (m + 1)) (GaloisField 2 f),
        (y, Y) ∈ LinFusion.ggInducedPairs ψ := by
      by_cases hpf' : p ∣ f
      · exact hfield hpf' y hyM hyp
      · exact exists_mem_ggInducedPairs_of_pow_eq_one hm hp hp2
          (fun σ h => eq_one_of_pow_eq_one_of_not_dvd (by omega) hp hpf' h) hker hC hyM hyp
    have hY' := mem_ggInducedPairs_comp_conjSL_inv hY P
    obtain ⟨s, hs⟩ := exists_conj_mem_rootTorus hp hp2 hmp hζ hker' hyp hY' (hdetall _ _ hY')
    have hsM : (ψ' s)⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := by
      refine Subgroup.le_normalizer (Subgroup.inv_mem _ ?_)
      rw [← hrange']
      exact ⟨s, rfl⟩
    exact hy _ hsM (by rw [inv_inv]; exact hW hs)
  have hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (u, A) ∈ LinFusion.ggInducedPairs ψ' := by
    rintro u hu ⟨k, hk⟩
    have huN : u ∈ Subgroup.normalizer (ψ'.range : Set G) := by
      rw [hrange']
      exact hNBs hu
    exact exists_mem_ggInducedPairs_of_pow_pow_eq_one hker' hC' hm hp hp2 hpF hreal hBs hom huN hk
  have hω1 : ω ≠ 1 := hω.ne_one hp.one_lt
  have hreal1 : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ' := fun l =>
    hreal _
  have hmono : ∀ u ∈ Subgroup.normalizer (Bs : Set G), ∀ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (u, A) ∈ LinFusion.ggInducedPairs ψ' → ∃ π,
        IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) π :=
    fun u hu A hA => exists_isPermOf fun i l l' hl hl' =>
      eq_of_ne_zero_of_mem_normalizer hker' hω1 hω.pow_eq_one hreal1 hBs hu hA hl hl'
  refine ⟨fun Q hQN hQp => torus_clause_one hp hmp hm hker' hC' hω1 hω.pow_eq_one hreal1 hBs hmat
    Q hQN hQp, ?_⟩
  intro z hzN hzC hzp
  rw [← hrange']
  exact torusCoords_of_inputs h4 h5 hp hmp hm hker' hC' hω hBs hmat hmono hzN hzC hzp

end LinModel

section Inputs

@[expose] def GGSixLinearFieldOrderPInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSL n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ → GGSixLinearCase p .PSL n f →
    p ∣ f → ∀ y ∈ Subgroup.normalizer (G₀ : Set G), y ^ p = 1 →
      GGPsiInnerDiag (ggU .PSL n f).D ψ y

theorem ggSixLinearTorusModelV2On_PSL_of_inputs (hfield : GGSixLinearFieldOrderPInput)
    (h4 : GGLinearRegularConjInput) (h5 : GGLinearTypeAkTripleInput) :
    GGSixLinearTorusModelV2On .PSL := by
  intro G _ _ p Bs G₀ n f ψ hS hlin _ hyex
  have hlin' := hlin
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpf : p ∣ 2 ^ f - 1 := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  have hS' := hS
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hrange
  have hfield' : p ∣ f → ∀ y ∈ Subgroup.normalizer (ψ.range : Set G), y ^ p = 1 →
      ∃ A, (y, A) ∈ LinFusion.ggInducedPairs ψ := fun hpf' y hy hyp =>
    LinFusion.exists_mem_ggInducedPairs (by omega) ψ hker
      (hfield G p Bs _ (m + 1) f ψ hS' hlin' hpf' y⁻¹ (Subgroup.inv_mem _ hy)
        (by rw [inv_pow, hyp, inv_one]))
  exact LinModel.torusModel_of_sl h4 h5 hS.prime hp5 hnp hadm.2.1 hpf hker hS.2.2.1 hS.bstar_le
    hS.elem hS.2.2.2.1.2.2 hS.omega hS.unique hS.normalizer_le hfield' hyex

end Inputs

end CFSG.StandardType

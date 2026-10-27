module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NbrInnerMore

variable {G : Type} [Group G]

theorem exists_conj_of_ggLAut_eq_conj {K : Subgroup G} (hK : commutator K = ⊤) {R : Type}
    [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) {r : R}
    (hr : ggLAut K θ ⟨x, hx⟩ = MulAut.conj r) :
    ∃ k ∈ K, ∀ l ∈ K, x⁻¹ * l * x = k⁻¹ * l * k := by
  obtain ⟨q, hq⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hcN : (k : G)⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := mul_mem (inv_mem hkN) hx
  have hc1 : ggLAut K θ ⟨(k : G)⁻¹ * x, hcN⟩ = 1 := by
    have e : (⟨(k : G)⁻¹ * x, hcN⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨k, hkN⟩ : Subgroup.normalizer (K : Set G))⁻¹ * ⟨x, hx⟩ := Subtype.ext rfl
    rw [e, map_mul, map_inv, hr, ggLAut_mk_self, hq, inv_mul_cancel]
  have hcC := mem_centralizer_of_ggLAut_eq_one K θ hK hc1
  refine ⟨k, k.2, fun l hl => ?_⟩
  have h1 : (k : G)⁻¹ * l * k ∈ K := mul_mem (mul_mem (inv_mem k.2) hl) k.2
  have h2 := Subgroup.mem_centralizer_iff.mp hcC _ h1
  calc x⁻¹ * l * x = ((k : G)⁻¹ * x)⁻¹ * ((k : G)⁻¹ * l * k) * ((k : G)⁻¹ * x) := by group
    _ = ((k : G)⁻¹ * x)⁻¹ * (((k : G)⁻¹ * x) * ((k : G)⁻¹ * l * k)) := by
        rw [mul_assoc, h2]
    _ = (k : G)⁻¹ * l * k := by group

section Inner

theorem not_ggNbrClauseFiveMarking_of_inner' {G : Type} [Group G] {K' : Subgroup G} {p : ℕ}
    {x : G} (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k)
    (hHS : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') →
        ¬ LargeEvenHalfSplit p lab (Subgroup.center ↥K' = ⊥))
    (h3 : ∀ lab : LargeEvenLabel, markChar lab ≠ 2 → ¬ MarkedModel lab (↥K' ⧸ Subgroup.center ↥K'))
    (hRIF : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') → LargeEvenLabelAll lab (GGRawInnField p)) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  intro hmark
  rcases largeEvenMarking_or hmark with hHS' | hPF
  · obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hHS'', hMM⟩ :=
      largeEvenMarking_exists_markedModel hHS'
    have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hMM
    by_cases hc : markChar lab = 2
    · exact hHS lab hlab hc hX hHS''
    · exact h3 lab hc hX
  · have hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R),
        (LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x) ∧
          MarkedModel lab R) →
        markChar lab = 2 ∧ MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := by
      intro lab R _ I F θ hP
      have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hP.2
      by_cases hc : markChar lab = 2
      · exact ⟨hc, hX⟩
      · exact absurd hX (h3 lab hc)
    have hPF' := largeEvenMarking_and_labelAll (fun lab hlab hS' => hRIF lab hlab hS'.1 hS'.2) hS
      (largeEvenMarking_markedModel hPF)
    obtain ⟨-, lab, hlab, hraw'⟩ := hPF'
    obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨-, f', hf', u', hu', hord, hind⟩, -⟩, hRIF'⟩ :=
      largeEvenRawDatum_exists hraw'
    obtain ⟨-, -, hinnI, hnot⟩ := hRIF' hs hna
    obtain ⟨k, hk, hkx⟩ := hinn
    set r₀ : R := (θ (QuotientGroup.mk (⟨k, hk⟩ : ↥K')))⁻¹ with hr₀
    have hc : u' * f' * u'⁻¹ = MulAut.conj r₀ := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl' : k⁻¹ * (l : G) * k ∈ K' :=
        K'.mul_mem (K'.mul_mem (K'.inv_mem hk) l.2) hk
      have h1 := hind l ⟨k⁻¹ * l * k, hl'⟩ (hkx l l.2).symm
      have h2 : (⟨k⁻¹ * l * k, hl'⟩ : ↥K') = (⟨k, hk⟩ : ↥K')⁻¹ * l * ⟨k, hk⟩ := rfl
      rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
        map_mul, map_inv, MulAut.conj_apply, hr₀, inv_inv]
    have hf'I : f' ∈ I := by
      have e : f' = MulAut.conj (u'⁻¹ r₀) := by
        calc f' = u'⁻¹ * (u' * f' * u'⁻¹) * u' := by group
          _ = u'⁻¹ * MulAut.conj r₀ * u' := by rw [hc]
          _ = MulAut.conj (u'⁻¹ r₀) := by
            ext s
            simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
              MulAut.inv_apply_self]
      rw [e]
      exact hinnI _
    exact hnot f' hf' hord hf'I

end Inner

end NbrInnerMore

open NbrInnerMore

section Main

theorem ggTableBNbrInnerInputOn_of_clauseFive {S : ℕ → LargeEvenLabel → Prop}
    (h3 : ∀ p lab, S p lab → p ≠ 3 ∨ ∀ (X : Type) [Group X], MarkedModel lab X →
      ∀ lab' : LargeEvenLabel, markChar lab' ≠ 2 → ¬ MarkedModel lab' X)
    (hout : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I))
    (hdet : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → ∀ (X : Type) [Group X], MarkedModel lab X → ∀ lab' : LargeEvenLabel,
        LargeEvenInLambda2 lab' → markChar lab' = 2 → MarkedModel lab' X →
          ∀ c, ¬ LargeEvenHalfSplit p lab' c) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hcfg.2.2, hnb.2⟩).2
  have hxB : x ∈ B := hcfg.1.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hxp : x ^ p = 1 := hcfg.1.2.2.2.2.2.2.1.1.1.2 x hxB
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (hout p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ, hMM⟩, hO⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hBsI => ?_⟩
    exfalso
    have hφp : ggLAut K θ ⟨x, hN hxBs⟩ ^ p = 1 := by
      have e : (⟨x, hN hxBs⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by simpa using hxp)
      rw [← map_pow, e, map_one]
    obtain ⟨r, hr⟩ := hO hs hna _ (hBsI x hxBs) hφp
    obtain ⟨k, hk, hkx⟩ := exists_conj_of_ggLAut_eq_conj hK θ (hN hxBs) hr.symm
    have hMK : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv θ.symm hMM
    rcases h3 p lab hSl with hp3 | hX3
    · exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 ⟨k, hk, hkx⟩
        (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
        (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
    · exact not_ggNbrClauseFiveMarking_of_inner' ⟨k, hk, hkx⟩
        (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
        (fun lab' hc' hM' => hX3 _ hMK lab' hc' hM')
        (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end Main

end CFSG.StandardType

end

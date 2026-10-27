module

public import CFSG.LocalAnalysis.StandardType.GGTDModelBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Inner

variable {K : Type} [Field K] {N m : ℕ} {L' : Type} [Group L']

private lemma l48g3_pair_pow {p : ℕ} {ζ : Kˣ} (hζp : ζ ^ p = 1)
    (k l i : Fin (N + 1)) :
    ((Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹ : Fin (N + 1) → Kˣ) i) ^ p = 1 := by
  rw [Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
  split_ifs <;> simp [hζp]

private lemma l48g3_c13 (M : GGTDModel K N m L') (A : Subgroup (MulAut L'))
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) :
    ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range →
      ∃ t ∈ ⨆ k, (ggTDcor M k).range, a = MulAut.conj t := by
  intro a ha har
  obtain ⟨l, rfl⟩ := har
  obtain ⟨t, ht⟩ := hAT (MulAut.conj l) ha
  obtain ⟨g, rfl⟩ := M.surj l
  obtain ⟨s, z, hz, hs⟩ := M.inner_diag g ht
  refine ⟨M.φ (M.dgm s), ggTDTsc_le M ⟨s, rfl⟩, ?_⟩
  rw [hs, map_mul]
  have hcz : MulAut.conj z = 1 := by
    ext x
    change z * x * z⁻¹ = x
    rw [(Subgroup.mem_center_iff.mp hz x).symm, mul_inv_cancel_right]
  rw [hcz, mul_one]

private lemma l48g3_c14 (M : GGTDModel K N m L') :
    ∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ (M.φ.comp M.dgm).range := by
  intro z hz hodd
  obtain ⟨s, hs⟩ := M.central_diag z hz hodd
  exact ⟨s, hs.symm⟩

private lemma l48g3_c15a (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hm : 0 < m) {A : Subgroup (MulAut L')}
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) (hsc : GGTorusSelfCent p A) :
    ∀ g : L', (∀ a ∈ A, MulAut.conj g * a = a * MulAut.conj g) →
      g ∈ (M.φ.comp M.dgm).range ⊔ Subgroup.center L' := by
  intro g h
  obtain ⟨g₀, rfl⟩ := M.surj g
  obtain ⟨ζ, hζμ, hζp, _hζ1, hζ2⟩ := ggTDzeta M hp hp2 hpm hm
  obtain ⟨s, z, hz, hs⟩ := M.cent_diag hζμ hζ2 g₀ (fun k l _hkl s hs => by
    have hsp : ∀ i, (s : Fin (N + 1) → Kˣ) i ^ p = 1 := by
      intro i
      rw [hs]
      exact l48g3_pair_pow hζp k l i
    have hmemA : MulAut.conj (M.φ (M.dgm s)) ∈ A := M.heart_mem hsc hAT s hsp
    exact h (MulAut.conj (M.φ (M.dgm s))) hmemA)
  rw [hs]
  exact Subgroup.mul_mem_sup ⟨s, rfl⟩ hz

private lemma l48g3_c15b (M : GGTDModel K N m L') :
    ∀ τ ∈ ggTDT M, ∀ t ∈ (M.φ.comp M.dgm).range, τ t = t := by
  intro τ hτ t ht
  obtain ⟨u, hu⟩ := hτ
  obtain ⟨s, rfl⟩ := ht
  exact M.act_fix hu s

private lemma l48g3_c15c (M : GGTDModel K N m L') :
    ∀ t ∈ (M.φ.comp M.dgm).range, t ^ m = 1 → t ∈ ⨆ k, (ggTDcor M k).range := by
  intro t ht _
  exact ggTDTsc_le M ht

theorem ggTDholdsThree (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hm : 0 < m) {A : Subgroup (MulAut L')}
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) (hsc : GGTorusSelfCent p A) :
    GGTDHoldsThree (ggTDwit M A hN) := by
  refine ⟨l48g3_c13 M A hN hAT, l48g3_c14 M, l48g3_c15a M hp hp2 hpm hm hAT hsc,
    l48g3_c15b M, l48g3_c15c M⟩

end Inner

end CFSG.StandardType

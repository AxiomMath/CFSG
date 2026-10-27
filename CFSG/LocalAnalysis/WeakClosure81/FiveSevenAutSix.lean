module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

theorem card_fixedPoints_eq_ten_of_not_mem_range_conjNormal
    {γ : MulAut (alternatingGroup (Fin 6))} (h2 : γ * γ = 1)
    (hγ : γ ∉ (MulAut.conjNormal :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range) :
    Nat.card {l : alternatingGroup (Fin 6) // γ l = l} = 10 := by
  obtain ⟨θ, ψ, hθinj, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  let φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 :=
    (MulEquiv.refl (alternatingGroup (Fin 6))).trans ψ.symm
  let b : ↥A6Models.autA6 := Unc25K1.A6Model.thetaEquiv φ γ
  have hb2 : (b : P10) * (b : P10) = 1 := by
    have : b * b = 1 := by
      rw [← map_mul, h2, map_one]
    exact congrArg Subtype.val this
  have hb1 : (b : P10) ≠ 1 := by
    intro h
    have hb : b = 1 := Subtype.ext h
    have : γ = 1 := (Unc25K1.A6Model.thetaEquiv φ).injective (by rw [map_one]; exact hb)
    exact hγ ⟨1, by rw [map_one, this]⟩
  have hs6 : (b : P10) ∉ s6 := by
    intro hmem
    obtain ⟨τ, hτ⟩ := Unc25K1.A6Model.s6_induces θ ψ hψθ (MulEquiv.refl _) γ hmem
    apply hγ
    refine ⟨τ, ?_⟩
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact (hτ k).symm
  have hpsl : (b : P10) ∉ A6Models.psl29 := fun h => hs6 (psl29_le_s6 h)
  have h10 := card_psl29_centralizer_of_not_mem b.2 hb2 hb1 hpsl hs6
  rw [← h10]
  have hcomm : ∀ l : {l : alternatingGroup (Fin 6) // γ l = l},
      ((φ l.1 : ↥A6Models.psl29) : P10) * (b : P10) =
        (b : P10) * ((φ l.1 : ↥A6Models.psl29) : P10) := by
    intro l
    have hsp := Unc25K1.A6Model.thetaEquiv_spec φ γ l.1
    rw [l.2] at hsp
    calc ((φ l.1 : ↥A6Models.psl29) : P10) * (b : P10)
        = ((b : P10) * ((φ l.1 : ↥A6Models.psl29) : P10) * (b : P10)⁻¹) * (b : P10) := by
          rw [← hsp]
      _ = (b : P10) * ((φ l.1 : ↥A6Models.psl29) : P10) := by group
  refine Nat.card_congr (Equiv.ofBijective
    (fun l => (⟨((φ l.1 : ↥A6Models.psl29) : P10),
      Subgroup.mem_inf.2 ⟨(φ l.1).2, Subgroup.mem_centralizer_singleton_iff.2 (hcomm l)⟩⟩ :
        ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(b : P10)} : Set P10)))) ⟨?_, ?_⟩)
  · intro l l' hll
    have h1 : ((φ l.1 : ↥A6Models.psl29) : P10) = ((φ l'.1 : ↥A6Models.psl29) : P10) :=
      congrArg (fun z : ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(b : P10)} : Set P10)) =>
        (z : P10)) hll
    exact Subtype.ext (φ.injective (Subtype.ext h1))
  · rintro ⟨x, hx⟩
    obtain ⟨hxpsl, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxc' : x * (b : P10) = (b : P10) * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
    have hl : γ (φ.symm ⟨x, hxpsl⟩) = φ.symm ⟨x, hxpsl⟩ := by
      apply φ.injective
      apply Subtype.ext
      rw [Unc25K1.A6Model.thetaEquiv_spec φ γ, MulEquiv.apply_symm_apply]
      show (b : P10) * x * (b : P10)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul, hxc']
    refine ⟨⟨φ.symm ⟨x, hxpsl⟩, hl⟩, ?_⟩
    apply Subtype.ext
    show ((φ (φ.symm ⟨x, hxpsl⟩) : ↥A6Models.psl29) : P10) = x
    rw [MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.WeakClosure81

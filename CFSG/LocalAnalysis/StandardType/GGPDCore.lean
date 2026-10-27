module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDWeights
public import CFSG.LocalAnalysis.StandardType.GGPDWeightSupport
public import CFSG.LocalAnalysis.StandardType.GGPDAffine
public import CFSG.LocalAnalysis.StandardType.GGPDSymm
public import CFSG.LocalAnalysis.StandardType.GGPDOrbit
public import CFSG.LocalAnalysis.StandardType.GGPDFinite

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPD_core {K : Type} [Field K] [IsAlgClosed K] (hK : ringChar K ≠ 3) {d : ℕ}
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hM : M = ggPDC3 ∨ M = ggPDC3.transpose)
    (ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K)
    (hρ : ∀ v, ρ v ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K) → v = 1)
    (hz : ∃ z : Matrix.GeneralLinearGroup (Fin d) K, ∀ v, z * ρ v * z⁻¹ = ρ v⁻¹)
    (hg : ∀ i : Fin 4, ∃ g : Matrix.GeneralLinearGroup (Fin d) K, ∀ v, ∃ c : Kˣ,
      g * ρ v * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
        ρ (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v)))) :
    24 ≤ d := by
  classical
  have hK3 : (3 : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := K) (p := ringChar K) (by norm_num) hK
  obtain ⟨ζ, hζ⟩ := @HasEnoughRootsOfUnity.prim K _ 3
    (@IsSepClosed.hasEnoughRootsOfUnity K _ 3 (⟨hK3⟩ : NeZero (3 : K))
      (IsSepClosed.of_isAlgClosed K))
  obtain ⟨b, u, hb⟩ := ggPD_weights hK hζ ρ
  let Ω : Set (Fin 4 → ZMod 3) := Set.range u
  have hΩfin : Ω.Finite := Set.finite_range u
  have hΩle : Ω.ncard ≤ d := by
    have h := Set.ncard_image_le (s := Set.univ (α := Fin d)) (f := u)
    rw [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact h
  have hws := ggPD_weight_support hζ ρ b u hb
  have hnonzero : ∃ j, u j ≠ 0 := hws.2.1 hρ
  have hneg' : ∀ j, ∃ j', u j' = -u j := hws.2.2 hz
  have hneg : (fun x : Fin 4 → ZMod 3 => -x) '' Ω = Ω := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rcases hx with ⟨j, rfl⟩
      rcases hneg' j with ⟨j', hj'⟩
      exact ⟨j', hj'⟩
    · intro z hz'
      rcases hz' with ⟨j, rfl⟩
      rcases hneg' j with ⟨j', hj'⟩
      exact ⟨-u j, ⟨j', hj'⟩, neg_neg (u j)⟩
  have hsq : ∀ i : Fin 4, ggPDRefl M i * ggPDRefl M i = 1 := by
    intro i
    rcases hM with hM | hM
    · rw [hM]
      exact PDFinite.ggPDF_S_mul_self i
    · rw [hM]
      fin_cases i <;> decide +kernel
  have hstable : ∀ i, ∀ x ∈ Ω, (ggPDRefl M i).transpose.mulVec x ∈ Ω := by
    intro i x hx
    have hsq_i : ggPDRefl M i * ggPDRefl M i = 1 := hsq i
    have hsqT : (ggPDRefl M i).transpose * (ggPDRefl M i).transpose = 1 := by
      have h := congrArg Matrix.transpose hsq_i
      rwa [Matrix.transpose_mul, Matrix.transpose_one] at h
    have hinv : ∀ v, (ggPDRefl M i).mulVec ((ggPDRefl M i).mulVec v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hsq_i, Matrix.one_mulVec]
    obtain ⟨g, hgv⟩ := hg i
    obtain ⟨t, ht⟩ := ggPD_weight_affine hζ M i ρ b u hb hinv g hgv
    have hsubset : (fun y : Fin 4 → ZMod 3 =>
        (ggPDRefl M i).transpose.mulVec y + t) '' Ω ⊆ Ω := by
      rintro z ⟨y, hy, rfl⟩
      rcases hy with ⟨j, rfl⟩
      rcases ht j with ⟨j', hj'⟩
      exact ⟨j', hj'⟩
    have hinj : Function.Injective (fun y : Fin 4 → ZMod 3 =>
        (ggPDRefl M i).transpose.mulVec y + t) := by
      intro y₁ y₂ hyp
      have h1 : (ggPDRefl M i).transpose.mulVec y₁ =
          (ggPDRefl M i).transpose.mulVec y₂ := add_right_cancel hyp
      have h2 : (ggPDRefl M i).transpose.mulVec
            ((ggPDRefl M i).transpose.mulVec y₁)
          = (ggPDRefl M i).transpose.mulVec ((ggPDRefl M i).transpose.mulVec y₂) := by
        rw [h1]
      simpa only [Matrix.mulVec_mulVec, hsqT, Matrix.one_mulVec] using h2
    have hcard : Ω.ncard ≤ ((fun y : Fin 4 → ZMod 3 =>
        (ggPDRefl M i).transpose.mulVec y + t) '' Ω).ncard :=
      ge_of_eq (Set.ncard_image_of_injective Ω hinj)
    have himg : (fun y : Fin 4 → ZMod 3 =>
        (ggPDRefl M i).transpose.mulVec y + t) '' Ω = Ω :=
      Set.eq_of_subset_of_ncard_le hsubset hcard hΩfin
    let L : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3) :=
      AddMonoidHom.mk' (fun y => (ggPDRefl M i).transpose.mulVec y) (by
        intro a b
        rw [Matrix.mulVec_add])
    have hLapply : ∀ y, L y = (ggPDRefl M i).transpose.mulVec y := fun _ => rfl
    have haff : (fun y => L y + t) '' Ω = Ω := by
      simpa only [hLapply] using himg
    have h3 : ∀ y : Fin 4 → ZMod 3, (3 : ℕ) • y = 0 := by
      intro y
      funext k
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    have hLin : L '' Ω = Ω := ggPD_symm_support h3 L Ω t hneg haff
    have hmem : L x ∈ Ω := by
      rw [← hLin]
      exact ⟨x, hx, rfl⟩
    rw [hLapply] at hmem
    exact hmem
  obtain ⟨j₀, hj₀⟩ := hnonzero
  have h24 : 24 ≤ Ω.ncard :=
    ggPD_orbit_finite M hM Ω hstable (u j₀) ⟨j₀, rfl⟩ hj₀
  exact le_trans h24 hΩle

end CFSG.StandardType

end

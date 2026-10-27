module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def NatSingularConj (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (Q' : QuadraticForm K (ι → K)) (X : Subgroup (GL ι K)) : Prop :=
  ∀ (φ : ↥(Rt M (LB M Q B) t) →* GL ι K), φ.range = X →
    φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) →
    ∀ [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (ι → K)),
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) →
      ∀ g ∈ M, conjSubgroup g B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ conjSubgroup g B → Q' (secVec ψ b) = 0

@[expose] def Sec56SingularConjStatement : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      ∀ m : ℕ, 3 ≤ m → NatSingularConj hc t (quadPlus m K) (StatedOmega (StatedQuadPlus m K))) ∧
  (∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      ∀ (m : ℕ) (b c : K), 3 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      NatSingularConj hc t (quadMinus m K b c) (StatedOmega (StatedQuadMinus m K b c)))

theorem Ctx.conj_orbit_omegaPlus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {mm : ℕ} (hm3 : 3 ≤ mm)
    (hSC : NatSingularConj hc t (quadPlus mm K) (StatedOmega (StatedQuadPlus mm K)))
    (hnat : NaturalRep (ι := Fin mm ⊕ Fin mm) K (StatedOmega (StatedQuadPlus mm K))
      (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z := by
  intro m hm hmV
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hmV
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, inferInstance, inferInstance, hK, Or.inl ⟨mm, hm3, hnat⟩⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin mm ⊕ Fin mm) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have h3 : 3 ≤ Module.finrank K (Fin mm ⊕ Fin mm → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
  have hsB := hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm3)
    (nondegenerate_polarBilin_quadPlus mm K) h3 (addCommutantScalar_statedOmegaPlus hm3)
    φ hφ ψ hψ
  have hsC := hSC φ hφ hker ψ hψ m hm hmV
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv hs.mem hK
    (addCommutantScalar_statedOmegaPlus hm3) φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ hglob θ hθ
  obtain ⟨d₀, hd₀D, hd0, hDiff⟩ := hD.exists_point_of_le hDV ψ hglob θ hθ
  have hQ : quadPlus mm K (secVec ψ b₀) = quadPlus mm K (secVec ψ d₀) :=
    (hsB b₀ hb₀B).trans (hsC d₀ hd₀D).symm
  obtain ⟨A, hA, hAu⟩ := (ElemMatrixIso.plus hm3).exists_mulVec_eq
    (nondegenerate_polarBilin_quadPlus mm K)
    (plusPair_orth (K := K) (n := mm) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hu0 hd0 hQ
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A := by
    rw [← hφ] at hA
    exact MonoidHom.mem_range.mp hA
  exact ⟨r, r.2, hc.conj_sup_eq_of_mulVec_eq hs φ ψ hψ hm hmV hBiff hDiff r
    (by rw [hr]; exact hAu)⟩

theorem Ctx.conj_orbit_omegaMinus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {mm : ℕ} {b c : K} (hm3 : 3 ≤ mm)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hSC : NatSingularConj hc t (quadMinus mm K b c) (StatedOmega (StatedQuadMinus mm K b c)))
    (hnat : NaturalRep (ι := Fin (mm - 1) ⊕ Fin (mm - 1) ⊕ Fin 2) K
      (StatedOmega (StatedQuadMinus mm K b c)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hc.CN t)) :
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z := by
  intro m hm hmV
  have hmm : 2 ≤ mm := by omega
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hmV
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, inferInstance, inferInstance, hK, Or.inr ⟨mm, b, c, hmm, hirr, hnat⟩⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin (mm - 1) ⊕ Fin (mm - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have h3 : 3 ≤ Module.finrank K (Fin (mm - 1) ⊕ Fin (mm - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  have hsB := hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hmm hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite mm K hirr) h3
    (addCommutantScalar_statedOmegaMinus hmm hirr) φ hφ ψ hψ
  have hsC := hSC φ hφ hker ψ hψ m hm hmV
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv hs.mem hK
    (addCommutantScalar_statedOmegaMinus hmm hirr) φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ hglob θ hθ
  obtain ⟨d₀, hd₀D, hd0, hDiff⟩ := hD.exists_point_of_le hDV ψ hglob θ hθ
  have hQ : quadMinus mm K b c (secVec ψ b₀) = quadMinus mm K b c (secVec ψ d₀) :=
    (hsB b₀ hb₀B).trans (hsC d₀ hd₀D).symm
  obtain ⟨A, hA, hAu⟩ := (ElemMatrixIso.minus hmm hirr).exists_mulVec_eq
    (nondegenerate_polarBilin_quadMinus_of_finite mm K hirr)
    (minusPair_orth (K := K) (n := mm) (b := b) (c := c) (i := ⟨0, by omega⟩)
      (j := ⟨1, by omega⟩) (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hu0 hd0 hQ
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A := by
    rw [← hφ] at hA
    exact MonoidHom.mem_range.mp hA
  exact ⟨r, r.2, hc.conj_sup_eq_of_mulVec_eq hs φ ψ hψ hm hmV hBiff hDiff r
    (by rw [hr]; exact hAu)⟩

theorem stroth56Nat_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hS : Sec56SingularConjStatement) : Stroth56NatStatement := by
  intro G _ _ M Q Z B hc n t hs7 hnot
  have hs := hs7.toSec5
  obtain ⟨mm, hmm, hpm⟩ := hs7.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ mm := by
      by_contra hlt
      have : mm = 2 := by omega
      subst this
      exact hs7.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    exact hc.conj_orbit_omegaPlus h34 hRoot hs hK hm3 (hS.1 G M Q Z B hc n t hs K hK mm hm3) hnat
  · have hm3 : 3 ≤ mm := by
      by_contra hlt
      have : mm = 2 := by omega
      subst this
      exact hnot ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
    exact hc.conj_orbit_omegaMinus h34 hRoot hs hK hm3 hirr
      (hS.2 G M Q Z B hc n t hs K hK mm b c hm3 hirr) hnat

end CFSG.RankThree.GF2n.Stroth80

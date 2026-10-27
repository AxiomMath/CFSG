module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAB

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra
open CFSG.LinearAlgebra.SteinbergBQ
open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

theorem qtwoDB41C_polarBilin_nondegenerate_of_anisotropic {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {P : Submodule (ZMod 2) V}
    (hfr : Module.finrank (ZMod 2) P = 2) (han : ∀ x ∈ P, Q x = 0 → x = 0) :
    (QuadraticMap.polarBilin (Q.comp P.subtype)).Nondegenerate := by
  have hmain : ∀ x : P, (∀ y : P,
      QuadraticMap.polarBilin (Q.comp P.subtype) x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hxV : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hq0 : Q (x : V) ≠ 0 := fun h => hxV (han x x.2 h)
    have hex : ∃ y ∈ P, y ∉ Submodule.span (ZMod 2) {(x : V)} := by
      by_contra hcon
      have hle : P ≤ Submodule.span (ZMod 2) {(x : V)} := by
        intro y hy
        by_contra hy'
        exact hcon ⟨y, hy, hy'⟩
      have hmono := Submodule.finrank_mono hle
      rw [hfr, finrank_span_singleton hxV] at hmono
      omega
    obtain ⟨y, hyP, hy⟩ := hex
    have hy0 : y ≠ 0 := fun h => hy (by rw [h]; exact Submodule.zero_mem _)
    have hxy0 : (x : V) + y ≠ 0 := by
      intro h
      apply hy
      have h2 : y = -((x : V)) := (neg_eq_iff_add_eq_zero.mpr h).symm
      rw [h2]
      exact neg_mem (Submodule.subset_span (Set.mem_singleton (x : V)))
    have hqy : Q y ≠ 0 := fun h => hy0 (han y hyP h)
    have hqxy : Q ((x : V) + y) ≠ 0 := fun h => hxy0 (han _ (P.add_mem x.2 hyP) h)
    have hp : QuadraticMap.polar Q (x : V) y = 0 := by
      have h := hx ⟨y, hyP⟩
      simpa only [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
        QuadraticMap.polarBilin_apply_apply, Submodule.subtype_apply] using h
    have hmap := QuadraticMap.map_add Q (x : V) y
    rw [hp, add_zero] at hmap
    have hsum : Q (x : V) + Q y = 0 := by
      have key : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0 := by decide
      exact key _ _ hq0 hqy
    rw [hsum] at hmap
    exact hqxy hmap
  refine ⟨hmain, fun y hy => hmain y fun x => ?_⟩
  have h := hy x
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h
  rwa [QuadraticMap.polarBilin_apply_apply]

theorem qtwoDB41_fixedFree_type {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) [IsElementaryAbelian 3 E]
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcard : Nat.card E = 3 ^ (m - 1)) (hfix : fixedSub E = ⊥)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m := by
  obtain ⟨I, d, -, ⟨-, -, horthBlocks⟩, -, hsum, -, -, -, -, -, -, hplanes, -, -,
    -⟩ :=
    binary_quadratic_three_action_canonical_kernel_blocks Q hQ hdim E hEO hcard hfix
  choose P hP using hplanes
  have hcardSigma : Fintype.card (Σ N : I, Fin (d N)) = m := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact (Finset.sum_coe_sort I d).trans hsum
  let e : Fin m ≃ Σ N : I, Fin (d N) := (Fintype.equivFinOfCardEq hcardSigma).symm
  let U : Fin m → Submodule (ZMod 2) V := fun j => P (e j).1.1 (e j).1.2 (e j).2
  have hUfr : ∀ j, Module.finrank (ZMod 2) (U j) = 2 :=
    fun j => ((hP (e j).1.1 (e j).1.2).1 (e j).2).2.1
  have hUan : ∀ j, ∀ x ∈ U j, Q x = 0 → x = 0 :=
    fun j => ((hP (e j).1.1 (e j).1.2).1 (e j).2).2.2.1
  have hUle : ∀ j, U j ≤ fixedSub (e j).1.1 :=
    fun j => ((hP (e j).1.1 (e j).1.2).1 (e j).2).1
  have hperpSigma : ∀ s t : Σ N : I, Fin (d N), s ≠ t →
      ∀ x ∈ P s.1.1 s.1.2 s.2, ∀ y ∈ P t.1.1 t.1.2 t.2,
        QuadraticMap.polar Q x y = 0 := by
    rintro ⟨⟨Ns, hs⟩, is⟩ ⟨⟨Nt, ht⟩, it⟩ hst x hx y hy
    by_cases hN : (⟨Ns, hs⟩ : I) = ⟨Nt, ht⟩
    · have hsub : Ns = Nt := congrArg Subtype.val hN
      subst hsub
      have hisne : is ≠ it := by
        intro h
        apply hst
        subst h
        exact Sigma.ext (Subtype.ext rfl) (heq_of_eq rfl)
      have hy' : y ∈ P Ns hs it := by
        have hht : ht = hs := Subsingleton.elim ht hs
        rwa [hht] at hy
      exact ((hP Ns hs).2.1 is it hisne) x hx y hy'
    · have hne : Ns ≠ Nt := fun h => hN (Subtype.ext h)
      have hxfix : x ∈ fixedSub Ns := ((hP Ns hs).1 is).1 hx
      have hyfix : y ∈ fixedSub Nt := ((hP Nt ht).1 it).1 hy
      exact horthBlocks Ns hs Nt ht hne x hxfix y hyfix
  have hsys : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem Q U :=
    { finrank_eq := hUfr
      nondeg := fun j =>
        qtwoDB41C_polarBilin_nondegenerate_of_anisotropic (hUfr j) (hUan j)
      not_isPlusType := fun j => by
        have hfr : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) ↥(U j)) = 2 := by
          simpa only [finrank_top] using hUfr j
        have han : ∀ x ∈ (⊤ : Submodule (ZMod 2) ↥(U j)),
            (Q.comp (U j).subtype) x = 0 → x = 0 := by
          intro x _ hx
          exact Subtype.ext (hUan j x x.2 hx)
        intro hp
        exact qtwoDB41_not_isPlusType_of_aniso (W := U j) (q := Q.comp (U j).subtype)
          (P := ⊤) hfr han
          ((CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isPlusType_comp_top_iff
            (Q := Q.comp (U j).subtype)).mpr hp)
      perp := fun i j hij x hx y hy =>
        hperpSigma (e i) (e j) (fun h => hij (e.injective h)) x hx y hy }
  exact qtwoDB41_isPlaneSystem_iff hsys hdim

end CFSG.StandardType.QTwo

end

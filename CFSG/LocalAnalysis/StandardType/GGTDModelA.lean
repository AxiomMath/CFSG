module

public import CFSG.LocalAnalysis.StandardType.GGTDModelAssemble
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
import CFSG.LocalAnalysis.StandardType.GGTDCentFour
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.SpecialLinear TypeA

private lemma l48a1_coe_prod {M : Type*} [CommMonoid M] {ι : Type*} (t : Finset ι)
    (f : ι → Mˣ) : (↑(t.prod f) : M) = t.prod (fun i => ↑(f i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Units.val_mul, ih]

private lemma l48a1_dgm_det {K : Type} [Field K] {N : ℕ}
    (s : ggTDTg (⊤ : Subgroup Kˣ) N) :
    (∏ i, ((s : Fin (N + 1) → Kˣ) i : K)) = 1 := by
  rw [← l48a1_coe_prod Finset.univ (fun i => (s : Fin (N + 1) → Kˣ) i), s.2.2,
    Units.val_one]

private noncomputable def l48a1_dgmFun (K : Type) [Field K] (N : ℕ) :
    ggTDTg (⊤ : Subgroup Kˣ) N → SpecialLinearGroup (Fin (N + 1)) K :=
  fun s => ⟨diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)), by
    rw [det_diagonal]
    exact l48a1_dgm_det s⟩

private noncomputable def l48a1_dgm (K : Type) [Field K] (N : ℕ) :
    ggTDTg (⊤ : Subgroup Kˣ) N →* SpecialLinearGroup (Fin (N + 1)) K where
  toFun := l48a1_dgmFun K N
  map_one' := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact diagonal_one
  map_mul' s t := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change diagonal (fun i => (((s * t : ggTDTg (⊤ : Subgroup Kˣ) N) :
        Fin (N + 1) → Kˣ) i : K)) =
      diagonal (fun i => (((s : ggTDTg (⊤ : Subgroup Kˣ) N) : Fin (N + 1) → Kˣ) i : K)) *
        diagonal (fun i => (((t : ggTDTg (⊤ : Subgroup Kˣ) N) : Fin (N + 1) → Kˣ) i : K))
    rw [diagonal_mul_diagonal]
    congr 1

private lemma l48a1_dgm_apply {K : Type} [Field K] {N : ℕ}
    (s : ggTDTg (⊤ : Subgroup Kˣ) N) :
    ((l48a1_dgm K N s : SpecialLinearGroup (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
      diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) := rfl

private lemma l48a1_dgm_exists_of_diagonal {K : Type} [Field K] {N : ℕ}
    {v : Fin (N + 1) → K} (hv : ∀ i, v i ≠ 0) {g : SpecialLinearGroup (Fin (N + 1)) K}
    (hg : (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) = diagonal v) :
    ∃ s : ggTDTg (⊤ : Subgroup Kˣ) N, l48a1_dgm K N s = g := by
  refine ⟨⟨fun i => Units.mk0 (v i) (hv i), ⟨fun i => Subgroup.mem_top _, ?_⟩⟩, ?_⟩
  · apply Units.ext
    rw [l48a1_coe_prod Finset.univ (fun i => Units.mk0 (v i) (hv i)), Units.val_one]
    simp only [Units.val_mk0]
    rw [← det_diagonal, ← hg, g.2]
  · apply Subtype.ext
    simpa only [l48a1_dgm_apply, Units.val_mk0] using hg.symm

private noncomputable def l48a1_model {K : Type} [Field K] [Finite K] [CharP K 2] {N : ℕ}
    (hN : 3 ≤ N) {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin (N + 1)) K →* L'}
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars (N + 1) K) :
    GGTDModel K N (Nat.card K - 1) L' where
  μ := ⊤
  ι := by
    haveI hcyc : IsCyclic ↥(⊤ : Subgroup Kˣ) := subgroup_units_cyclic (⊤ : Subgroup Kˣ)
    have hcard : Nat.card ↥(⊤ : Subgroup Kˣ) = Nat.card K - 1 := by
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_units]
    exact hcard ▸ (zmodCyclicMulEquiv hcyc).symm
  H := SpecialLinearGroup (Fin (N + 1)) K
  φ := φ'
  surj := hφ's
  Act := fun a t => TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K))
  act_one := by
    change TypeANbrDvd.ActsDiag φ' 1 (fun i => ((1 : Fin (N + 1) → Kˣ) i : K))
    simpa using TypeANbrDvd.actsDiag_one (φ' := φ')
  act_mul := by
    intro a b t u ha hb
    change TypeANbrDvd.ActsDiag φ' (a * b) (fun i => ((t * u) i : K))
    simpa only [Pi.mul_apply, Units.val_mul] using ha.mul hb
  act_inv := by
    intro a t ha
    change TypeANbrDvd.ActsDiag φ' a⁻¹ (fun i => ((t⁻¹) i : K))
    simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using ha.inv
  act_unique := by
    intro a b t ha hb
    change TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K)) at ha
    change TypeANbrDvd.ActsDiag φ' b (fun i => (t i : K)) at hb
    exact TypeANbrDvd.ActsDiag.unique hφ's ha hb
  act_ratio := by
    intro a t u ha hu
    change TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K)) at ha
    change TypeANbrDvd.ActsDiag φ' a (fun i => (u i : K)) at hu
    refine ⟨u 0 / t 0, fun i => ?_⟩
    by_cases hi : i = 0
    · subst hi; rw [div_mul_cancel]
    · have h := TypeANbrDvd.ActsDiag.ratio hφker ha hu (k := i) (l := 0) hi
      have hK : t i * (t 0)⁻¹ = u i * (u 0)⁻¹ := by
        apply Units.val_inj.mp
        rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
        exact h
      calc u i = u i * (u 0)⁻¹ * u 0 := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = t i * (t 0)⁻¹ * u 0 := by rw [← hK]
        _ = (u 0 / t 0) * t i := by rw [div_eq_mul_inv]; ac_rfl
  act_const := by
    intro a c ha
    change TypeANbrDvd.ActsDiag φ' a (fun _ => (c : K)) at ha
    exact TypeANbrDvd.ActsDiag.eq_one (Nat.succ_pos N) hφ's ha (fun _ _ => rfl)
  act_ratio_mem := by
    intro a t ha i j
    exact Subgroup.mem_top _
  dgm := l48a1_dgm K N
  act_dgm := by
    intro s
    change TypeANbrDvd.ActsDiag φ' (MulAut.conj (φ' (l48a1_dgm K N s)))
      (fun i => ((s : Fin (N + 1) → Kˣ) i : K))
    exact TypeANbrDvd.actsDiag_conj (D := l48a1_dgm K N s) rfl
  act_fix := by
    intro a t ha s
    change TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K)) at ha
    change a (φ' (l48a1_dgm K N s)) = φ' (l48a1_dgm K N s)
    refine ha.apply_of_isDiag (s := l48a1_dgm K N s) ?_
    rw [l48a1_dgm_apply]
    exact isDiag_diagonal _
  ker_dgm := by
    intro s h
    have hz : l48a1_dgm K N s ∈ scalars (N + 1) K := hφker (l48a1_dgm K N s) h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
    refine ⟨c, fun i => ?_⟩
    apply Units.val_inj.mp
    have hii := congrFun (congrFun hc i) i
    simp only [l48a1_dgm_apply, diagonal_apply_eq, scalar_apply, if_true] at hii
    exact hii
  Pm := fun σ => permSL σ
  act_perm := by
    intro a t σ ha
    change TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K)) at ha
    change TypeANbrDvd.ActsDiag φ'
      (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹)
      (fun i => (t (σ i) : K))
    exact TypeANbrDvd.ActsDiag.conj_perm ha σ
  act_apply_perm := by
    intro a t σ s ha hs
    change TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K)) at ha
    obtain ⟨D, hD, haD⟩ := ha
    change a (φ' (permSL σ)) = φ' (l48a1_dgm K N s * permSL σ)
    rw [haD (permSL σ)]
    congr 1
    apply Subtype.ext
    have hcoe : ((l48a1_dgm K N s * permSL σ : SpecialLinearGroup (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
        diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) * Equiv.Perm.permMatrix K σ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, l48a1_dgm_apply, coe_permSL]
    rw [hcoe, coe_slConjugation', hD, coe_inv_of_diagonal hD, coe_permSL,
      Matrix.mul_assoc, permMatrix_mul_diagonal, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have hAC : (fun i => (t i : K) * ((fun k => ((t k : K))⁻¹) ∘ σ) i) =
        (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) := by
      funext i
      rw [Function.comp_apply, hs i, Units.val_div_eq_div_val, div_eq_mul_inv]
    rw [hAC]
  inner_diag := by
    intro g t h
    change TypeANbrDvd.ActsDiag φ' (MulAut.conj (φ' g)) (fun i => (t i : K)) at h
    obtain ⟨c, hc⟩ := TypeANbrDvd.exists_diagonal_of_actsDiag_conj hφker h
    have hprod : ∏ i, (c * (t i : K)) = 1 := by
      rw [← det_diagonal, ← hc, g.2]
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 : (∏ _i : Fin (N + 1), (0 : K)) = 1 := by simpa [h0] using hprod
      simp at h1
    obtain ⟨s, hs⟩ := l48a1_dgm_exists_of_diagonal (N := N)
      (v := fun i => c * (t i : K)) (fun i => mul_ne_zero hc0 (h.ne_zero i)) hc
    exact ⟨s, 1, Subgroup.one_mem _, by rw [hs, mul_one]⟩
  central_diag := by
    intro z hz _
    obtain ⟨g, rfl⟩ := hφ's z
    have hg : MulAut.conj (φ' g) = 1 := by
      ext x
      change φ' g * x * (φ' g)⁻¹ = x
      rw [(Subgroup.mem_center_iff.mp hz x).symm, mul_inv_cancel_right]
    have hy : ∀ y, φ' (g * y * g⁻¹) = φ' y := by
      intro y
      simpa only [map_mul, map_inv, MulAut.conj_apply, MulAut.one_apply] using
        congrArg (fun f : MulAut L' => f (φ' y)) hg
    obtain ⟨c, hc⟩ := TypeANbrDvd.exists_scalar_of_map_conj_eq hφker hy
    have hcd : c ^ (N + 1) = 1 := (mem_scalars_of_coe_eq_scalar (Nat.succ_pos N) hc).1
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (Nat.succ_ne_zero N)] at hcd
      exact zero_ne_one hcd
    have hgd : (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) = diagonal (fun _ => c) := by
      rw [hc]
      ext i j
      simp [scalar_apply, diagonal_apply]
    obtain ⟨s, hs⟩ := l48a1_dgm_exists_of_diagonal (N := N)
      (v := fun _ => c) (fun _ => hc0) hgd
    exact ⟨s, by rw [hs]⟩
  cent_diag := by
    intro ζ hζmem hζne g h
    have hζ' : (ζ : K) ≠ (ζ : K)⁻¹ := by
      intro hh
      apply hζne
      apply Units.val_inj.mp
      rw [Units.val_inv_eq_inv_val]
      exact hh
    have hcomm : ∀ k l : Fin (N + 1), k ≠ l →
        ∀ D : SpecialLinearGroup (Fin (N + 1)) K,
          (D : Matrix (Fin (N + 1)) (Fin (N + 1)) K) = diagonal (ggPairVec k l (ζ : K)) →
          MulAut.conj (φ' g) * MulAut.conj (φ' D) =
            MulAut.conj (φ' D) * MulAut.conj (φ' g) := by
      intro k l hkl D hD
      let s : ggTDTg (⊤ : Subgroup Kˣ) N :=
        ⟨Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹, by
          refine ⟨fun _ => Subgroup.mem_top _, ?_⟩
          simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']⟩
      have hs : (s : Fin (N + 1) → Kˣ) = Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹ := rfl
      have hfun : (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) = ggPairVec k l (ζ : K) := by
        funext i
        rw [hs, Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply, ggPairVec_apply]
        split_ifs <;> simp_all [Units.val_mul, Units.val_inv_eq_inv_val]
      have hdgm : l48a1_dgm K N s = D := by
        apply Subtype.ext
        rw [l48a1_dgm_apply, hD, hfun]
      have hc := h k l hkl s hs
      rwa [hdgm] at hc
    have hdiag : (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K).IsDiag := by
      rcases Nat.lt_or_ge (N + 1) 5 with hd | hd
      · obtain rfl : N = 3 := by omega
        exact TypeANbrDvd.isDiag_of_conj_comm_four hφker hζ' hcomm
      · exact TypeANbrDvd.isDiag_of_conj_comm (s := g) hφker hd hζ' hcomm
    have hgd : (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
        diagonal (fun i => (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i) :=
      ((isDiag_iff_diagonal_diag _).mp hdiag).symm
    have hdet : ∏ i, (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i = 1 := by
      rw [← det_diagonal, ← hgd, g.2]
    have hv : ∀ i, (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i ≠ 0 := by
      intro i hi
      have h1 : (∏ j, (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) j j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hdet] at h1
      exact one_ne_zero h1
    obtain ⟨s, hs⟩ := l48a1_dgm_exists_of_diagonal (N := N)
      (v := fun i => (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i) hv hgd
    exact ⟨s, 1, Subgroup.one_mem _, by rw [hs, mul_one]⟩
  heart_mem := by
    intro p A hsc hdiag s hu
    change MulAut.conj (φ' (l48a1_dgm K N s)) ∈ A
    refine TypeANbrDvd.conj_mem_of_selfCent hsc ?_
      (D := l48a1_dgm K N s) (u := fun i => ((s : Fin (N + 1) → Kˣ) i : K)) rfl ?_
    · intro a ha
      obtain ⟨t, ht⟩ := hdiag a ha
      exact ⟨fun i => (t i : K), ht⟩
    · intro i
      have h1 := congrArg (fun u : Kˣ => (u : K)) (hu i)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h1

theorem exists_ggTDModel_A {K : Type} [Field K] [Finite K] [CharP K 2] {N : ℕ} (hN : 3 ≤ N)
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin (N + 1)) K →* L'}
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars (N + 1) K) :
    ∃ M : GGTDModel K N (Nat.card K - 1) L',
      (∀ a : MulAut L', (∃ t, M.Act a t) ↔
        ∃ t : Fin (N + 1) → K, TypeANbrDvd.ActsDiag φ' a t) ∧
      ∀ σ : Equiv.Perm (Fin (N + 1)), M.φ (M.Pm σ) = φ' (permSL σ) := by
  refine ⟨l48a1_model hN hφ's hφker, ?_, fun σ => rfl⟩
  intro a
  change (∃ t : Fin (N + 1) → Kˣ,
      TypeANbrDvd.ActsDiag φ' a (fun i => (t i : K))) ↔
    ∃ t : Fin (N + 1) → K, TypeANbrDvd.ActsDiag φ' a t
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨fun i => (t i : K), ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun i => Units.mk0 (t i) (ht.ne_zero i), ?_⟩
    have hfun : (fun i => ((Units.mk0 (t i) (ht.ne_zero i) : Kˣ) : K)) = t := by
      funext i
      rfl
    rw [hfun]
    exact ht

theorem exists_torusWit_of_model_A {K : Type} [Field K] [Finite K] [CharP K 2] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hN : 3 ≤ N)
    {L' : Type} [Group L'] [Finite L'] {φ' : SpecialLinearGroup (Fin (N + 1)) K →* L'}
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars (N + 1) K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (N + 1) → K, TypeANbrDvd.ActsDiag φ' a t) :
    ∃ w : GGTorusTorWit (Nat.card K - 1) N L' A,
      w.Holds (CartanMatrix.A N) (CoxeterMatrix.A N) ∧
        ∀ k : Fin N, w.n k = φ' (permSL (Equiv.swap k.castSucc k.succ)) := by
  obtain ⟨M, hMact, hMP⟩ := exists_ggTDModel_A hN hφ's hφker
  have hNperm : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag σ
  have hN' : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro σ
    rw [hMP]
    exact hNperm σ.symm
  have hm : 0 < Nat.card K - 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  refine ⟨ggTDwit M A hN', ?_, fun k => hMP _⟩
  refine ggTDwit_holds_of_model M hp hp2 hpK hm (by omega) hsc
    (fun a ha => (hMact a).mpr (hdiag a ha)) hN' (TypeANbrDvd.permAut φ' A hNperm)
    (TypeANbrDvd.permAut_injective hp hp2 hpK (by omega) hφ's hφker hA hsc hdiag hNperm)
    (TypeANbrDvd.ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφker hA hsc hdiag hNperm).symm
    fun k => ?_
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  rw [TypeANbrDvd.permAut_apply, ggConjAut_apply, ggConjAut_apply, hMP]
  rfl

theorem ggTorusTorData_of_model_A {K : Type} [Field K] [Finite K] [CharP K 2] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hN : 3 ≤ N)
    {L' : Type} [Group L'] [Finite L'] {φ' : SpecialLinearGroup (Fin (N + 1)) K →* L'}
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars (N + 1) K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (N + 1) → K, TypeANbrDvd.ActsDiag φ' a t) :
    GGTorusTorData (Nat.card K - 1) N (CartanMatrix.A N) (CoxeterMatrix.A N) L' A := by
  obtain ⟨w, hw, -⟩ := exists_torusWit_of_model_A hp hp2 hpK hN hφ's hφker hA hsc hdiag
  exact ⟨w, hw⟩

theorem ggTorusTorW_typeA {K : Type} [Field K] [Finite K] [CharP K 2] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hN : 3 ≤ N) :
    GGTorusTorW p (N - 1) (Nat.card K - 1) N (CartanMatrix.A N) (CoxeterMatrix.A N)
      (LargeEvenProj (LargeEvenSLGroup (Fin (N + 1)) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (N + 1)) K)) Set.univ) := by
  intro L' _ _ ψ A hTB
  have hTB' := hTB.mulEquiv (TypeA.recipeEquiv (N + 1) K) (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
  obtain ⟨φ', hφ's, hφker, hdiag⟩ := exists_actsDiag_model_of_tbGroup hp hpK
    (by omega : 4 ≤ N + 1) (r := N - 1) (by omega) hTB'
  obtain ⟨-, -, -, hAe, -, -, -, hsc⟩ := hTB
  exact ggTorusTorData_of_model_A hp hp2 hpK hN hφ's hφker hAe hsc hdiag

end CFSG.StandardType

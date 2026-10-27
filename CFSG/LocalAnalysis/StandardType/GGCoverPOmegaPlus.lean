module

public import CFSG.LocalAnalysis.StandardType.GGCoverPToral
public import CFSG.LocalAnalysis.StandardType.GGCoverPClassicalInner
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

namespace CoverPOmPlus

private theorem matrix_map_omPlusTorusGL {K : Type} [Field K] {m p : ℕ} [NeZero p] {ζ : Kˣ}
    (hζ : ζ ^ p = 1) {τ : K ≃+* K} (hτ : ∀ x : K, x ^ p = 1 → τ x = x)
    (g : Fin m → Multiplicative (ZMod p)) :
    (((omPlusTorusGL (K := K) (m := m) (p := p) hζ g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map τ) =
      ((omPlusTorusGL (K := K) (m := m) (p := p) hζ g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [omPlusTorusGL_eq_spTorusGL, TableBSymp.spTorusGL_apply, TauCeti.diagGL_coe,
    Matrix.diagonal_map (map_zero τ)]
  congr 1
  funext a
  rcases a with i | i
  · simp only [TableBSymp.pairedUnits, Sum.elim_inl]
    apply hτ
    have hroot : (TableBSymp.zmodPowHom hζ (g i)) ^ p = 1 := by
      rw [TableBSymp.zmodPowHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [← Units.val_pow_eq_pow_val, hroot, Units.val_one]
  · simp only [TableBSymp.pairedUnits, Sum.elim_inr]
    apply hτ
    have hroot : (TableBSymp.zmodPowHom hζ (g i)) ^ p = 1 := by
      rw [TableBSymp.zmodPowHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [← Units.val_pow_eq_pow_val, inv_pow, hroot, inv_one, Units.val_one]

private theorem fieldAutP_fixes_omPlusTorus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p s : ℕ} [NeZero m] (hm : 1 ≤ m) (hp : p.Prime) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    {τ : K ≃+* K} (hτ : τ ^ p ^ s = 1) (g : Fin m → Multiplicative (ZMod p)) :
    (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) hm)).symm (AutOm.fieldAutP m τ)
        ((rPlusEquivStatedOmega K m).symm (omPlusTorus hζ g)) =
      (rPlusEquivStatedOmega K m).symm (omPlusTorus hζ g) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let h : LargeEvenOmega (LargeEvenQPlus K m) :=
    ⟨omPlusTorusGL hζ g, omPlusTorusGL_mem hζ g⟩
  have he : (rPlusEquivStatedOmega K m).symm (omPlusTorus hζ g) =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)) h := rfl
  rw [he]
  have hrel : (((h : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map τ) =
      ((h : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
    matrix_map_omPlusTorusGL hζ (fun x hx => fieldAut_fixes_pow_eq_one hp hτ hx) g
  exact RecipeFieldOmega.graphAut_fieldAutP hm τ h h hrel.symm

private theorem exists_inner_mul_field_omegaPlus {K : Type} [Field K] [Finite K]
    {m n p : ℕ} (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : m = 4 → p ≠ 3)
    {a : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))} {k : ℕ}
    (hk : a ^ p ^ k = 1) :
    ∃ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))),
      ∃ f ∈ Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))),
        a = u * f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card hK
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  by_cases hm5 : 5 ≤ m
  · exact RawAutOmega.ggOddAutInnField_omegaPlus hm5 hodd a hk
  · have hm4 : m = 4 := by omega
    subst hm4
    have hp3' : p ≠ 3 := hp3 rfl
    have h6 : Nat.Coprime 6 p := by
      rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
      exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
        (Nat.coprime_primes Nat.prime_three hp).2 hp3'.symm⟩
    have hcop6 : Nat.Coprime 6 (p ^ k) := h6.pow_right k
    exact (RawAutOmega.ggOddAutInnField_omegaPlus_of (by norm_num : 1 ≤ 4) (M := 6) hcop6
      (RawAutOmega.exists_eq_mul_mul_fieldAutP_four (K := K))) a hk

private theorem omegaPlus_hA {K : Type} [Field K] [Finite K] [CharP K 2]
    {m n p : ℕ} [NeZero m] (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : m = 4 → p ≠ 3) (hn1 : 1 ≤ n) {ζ : Kˣ} (hζ : ζ ^ p = 1) :
    let V : Set (OrthRest.RPlus K m) :=
      (rPlusEquivStatedOmega K m).symm ''
        ((omPlusTorus (K := K) (m := m) (p := p) hζ).range :
          Set (StatedOmega (StatedQuadPlus m K)))
    ∀ a : MulAut (OrthRest.RPlus K m), (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ (ρ₁ : OrthRest.RPlus K m) (φ : MulAut (OrthRest.RPlus K m)),
        a = MulAut.conj ρ₁ * φ ∧ ∀ v ∈ V, φ v = v := by
  dsimp only
  intro a ha
  obtain ⟨k, hk⟩ := ha
  obtain ⟨u, hu, f, hf, haeq⟩ := exists_inner_mul_field_omegaPlus hK hm hp hp2 hp3 hk
  have hm1 : 1 ≤ m := by omega
  let Θ := RecipeFieldOmega.plusEquiv (K := K) hm1
  obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_closure hm1 hf
  have hσn : σ ^ n = 1 := by
    rw [← (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1]
    exact pow_card_eq_one'
  have hn0 : n ≠ 0 := by omega
  obtain ⟨ρ₁, j, ee, hdiv, haj⟩ :=
    CFSG.exists_eq_conj_mul_pow_of_eq_mul hp hn0 hu hk haeq
  obtain ⟨d, hd⟩ := hdiv
  have hσpow : (σ ^ j) ^ p ^ ee = 1 := by
    rw [← pow_mul, mul_comm j (p ^ ee), hd, pow_mul, hσn, one_pow]
  refine ⟨ρ₁, f ^ j, haj, ?_⟩
  intro v hv
  obtain ⟨t, ht, rfl⟩ := hv
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp ht
  have hfj : f ^ j = (MulAut.congr Θ).symm (AutOm.fieldAutP m (σ ^ j)) := by
    apply (MulAut.congr Θ).injective
    rw [MulEquiv.apply_symm_apply, map_pow, hσ]
    exact (map_pow (AutOm.fieldAutP m) σ j).symm
  rw [hfj]
  exact fieldAutP_fixes_omPlusTorus hm1 hp hζ hσpow g

theorem ggCoverPTableB_omegaPlus {K : Type} [Field K] [Finite K] {m n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hp3 : m = 4 → p ≠ 3) :
    GGCoverPTableB p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))
  change GGCoverPTableB p R (LargeEvenInnSet R)
  have hn1 : 1 ≤ n := CFSG.SeitzReduction.one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one' hn1 hpn
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero m := ⟨by omega⟩
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hZ : Subgroup.center R = ⊥ :=
    TableBOrth.center_omegaPlus_eq_bot (K := K) hp hp2 hpq (m := m) (by omega)
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  let e : R ≃* StatedOmega (StatedQuadPlus m K) := rPlusEquivStatedOmega K m
  let V : Set R := e.symm ''
    ((omPlusTorus (K := K) (m := m) (p := p) hζ).range :
      Set (StatedOmega (StatedQuadPlus m K)))
  have hI : ∀ φ ∈ LargeEvenInnSet R, φ ∈ (MulAut.conj : R →* MulAut R).range :=
    fun φ hφ => hφ
  have hcard : ∀ {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
      {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)},
      GGTableBPosition p L' E (LargeEvenInnSet R) θ hE →
        p ^ m ≤ Nat.card (ggLAutImage L' θ E) := by
    intro M _ _ L' E θ hE hP
    exact pow_le_card_ggLAutImage hP hp
      (TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega : 3 ≤ m))
  have hT : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ m ≤ Nat.card E' →
      ∃ β : MulAut R, ∀ x ∈ E', β x ∈ V := fun E' hE' hc =>
    CoverPToral.exists_mulAut_mapsTo_of_mulEquiv e
      (fun E hE hc' => exists_mulEquiv_eq_map_omPlusTorus hp2 hζ hζo hE hc') hE' hc
  have hA : ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ (ρ₁ : R) (φ : MulAut R), a = MulAut.conj ρ₁ * φ ∧ ∀ v ∈ V, φ v = v :=
    omegaPlus_hA hK hm hp hp2 hp3 hn1 hζ
  have hfix : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ m ≤ Nat.card E' →
      ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : R, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x :=
    fun E' hE' hcardE a ha => CoverPToral.forall_fix_of_toral V hT hA hE' hcardE ha
  exact CoverPToral.ggCoverPTableB_of_forall_fix (r := m) hZ hI hcard hfix

theorem largeEvenLabelAll_coverP_omegaPlus {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (ht : lab.tag = .D) (h4 : 4 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n - 1)
    (hD4 : ¬ GGD4Three p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  refine largeEvenLabelAll_omegaPlus ht h4 fun K _ _ _ hK => ?_
  exact ggCoverPTableB_omegaPlus hK h4 hp hpn fun h4' hp3 => hD4 ⟨ht, h4', hp3⟩

end CoverPOmPlus

end CFSG.StandardType

end

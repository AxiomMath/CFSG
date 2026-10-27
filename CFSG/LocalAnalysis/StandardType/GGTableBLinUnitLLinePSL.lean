module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine

public section

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem prime_ne_two_of_dvd_card_sub_one (hpK : p ∣ Nat.card K - 1) : p ≠ 2 := by
  rintro rfl
  have := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
  have h2 : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff K 2 _).mp h0
  have h1 : 0 < Nat.card K := Nat.card_pos
  omega

theorem exists_model_of_pow_lt_card (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 1) < Nat.card A) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧ ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t := by
  classical
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := isToral_comap_of_pow_lt_card hp hp2 hpK _ hXA hXI (hcardX ▸ hcard)
  exact TypeANbrDvd.exists_actsDiag_model hperfSL (slHasSections_of_five_le hd) hψ hker hperf
    hAI hA₀

theorem exists_model (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 2) ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧ ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t := by
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdiv : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
  have hcard : p ^ (d / p + 1) < Nat.card A := by
    by_cases hsmall : d - 2 ≤ 3
    · exact (Nat.pow_lt_pow_right hp.one_lt (by omega : d / p + 1 < 3)).trans_le h3
    · exact (Nat.pow_lt_pow_right hp.one_lt (by omega : d / p + 1 < d - 2)).trans_le hr
  exact exists_model_of_pow_lt_card hp hpK hd hψ hker hperf hA hAI hcard

omit [Finite K] in
theorem weyl_spec {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    ∀ n ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)), ∀ a ∈ A,
      (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  rintro _ ⟨σ, rfl⟩ a ha
  obtain ⟨t, hat⟩ := hdiag a ha
  obtain ⟨E, hE, haE⟩ := id hat
  have hg : ((permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹ :
      SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal fun i => t (σ i) * (t i)⁻¹ := by
    rw [← map_inv, permSL_inv, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, coe_permSL,
      coe_permSL, coe_inv_of_diagonal hE, hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      permMatrix_mul_diagonal_mul_inv, diagonal_mul_diagonal]
    rfl
  have e : φ' (permSL σ) * (a (φ' (permSL σ)))⁻¹ =
      φ' (permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹) := by
    rw [haE, map_mul, map_inv]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [e, ← map_pow,
      pow_eq_one_of_diagonal hg (fun i => hat.ratio_pow hφker (hAp a ha) (σ i) i), map_one]
  · obtain ⟨t', hat'⟩ := hdiag a' ha'
    rw [e]
    exact hat'.apply_of_isDiag (by rw [hg]; exact isDiag_diagonal _)

@[expose] def diagSLOf (u : Fin d → K) (hu : ∏ i, u i = 1) : SpecialLinearGroup (Fin d) K :=
  ⟨diagonal u, by rw [det_diagonal, hu]⟩

omit [Finite K] [CharP K 2] in
theorem coe_diagSLOf (u : Fin d → K) (hu : ∏ i, u i = 1) :
    ((diagSLOf u hu : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u :=
  rfl

theorem ggNoInvariantLineSCr_PSL (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {r : ℕ}
    (hrd : d - 2 ≤ r) :
    GGNoInvariantLineSCr p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have := Fact.mk hp
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  obtain ⟨φ', hφ's, hφker, hdiag⟩ := exists_model hp hpK hd hψ hker hperf hA hAI
    ((Nat.pow_le_pow_right hp.pos hrd).trans hr) h3
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  refine ⟨_, weyl_spec hφker hAp hdiag, fun Λ hΛA hΛ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hinv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ Λ,
      MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ ∈ Λ :=
    fun σ a ha => hcon _ ⟨σ, rfl⟩ a ha
  have : Nontrivial Λ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hΛ]; exact hp.one_lt)
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := exists_ne (1 : Λ)
  have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  set i2 : Fin d := ⟨2, by omega⟩
  set i3 : Fin d := ⟨3, by omega⟩
  set i4 : Fin d := ⟨4, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  have h24 : i2 ≠ i4 := by simp [i2, i4, Fin.ext_iff]
  set D₁ := diagSLOf (rootT ζ i0 i1) (prod_rootT hζ0 h01) with hD₁
  set D₂ := diagSLOf (rootT ζ i2 i3) (prod_rootT hζ0 h23) with hD₂
  have he₁ : MulAut.conj (φ' D₁) ∈ Λ :=
    conj_mem_of_invariant hp (by omega) hφ's hφker hΛA hsc hdiag hAp hinv ha₀ ha₀1'
      (coe_diagSLOf _ _) (rootT_pow hζ.pow_eq_one i0 i1)
  have he₂ : MulAut.conj (φ' D₂) ∈ Λ :=
    conj_mem_of_invariant hp (by omega) hφ's hφker hΛA hsc hdiag hAp hinv ha₀ ha₀1'
      (coe_diagSLOf _ _) (rootT_pow hζ.pow_eq_one i2 i3)
  have hact₁ : ActsDiag φ' (MulAut.conj (φ' D₁)) (rootT ζ i0 i1) := actsDiag_conj (coe_diagSLOf _ _)
  have hact₂ : ActsDiag φ' (MulAut.conj (φ' D₂)) (rootT ζ i2 i3) := actsDiag_conj (coe_diagSLOf _ _)
  have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have he₁1 : MulAut.conj (φ' D₁) ≠ 1 := by
    intro h1
    have h2 : ActsDiag φ' (MulAut.conj (φ' D₁)) (fun _ => (1 : K)) := by rw [h1]; exact actsDiag_one
    have h3' := hact₁.ratio hφker h2 hi02
    rw [rootT_left, rootT_other ζ (Ne.symm hi02) (by simp [i2, i1, Fin.ext_iff])] at h3'
    simp only [inv_one, mul_one] at h3'
    exact hζ1 h3'
  have hord : orderOf (MulAut.conj (φ' D₁)) = p :=
    orderOf_eq_prime (hAp _ (hΛA he₁)) he₁1
  have hΛz : Subgroup.zpowers (MulAut.conj (φ' D₁)) = Λ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₁)
      (by rw [hΛ, Nat.card_zpowers, hord])
  have hfin : IsOfFinOrder (MulAut.conj (φ' D₁)) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hAp _ (hΛA he₁)⟩
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    (hfin.mem_powers_iff_mem_zpowers.mpr (hΛz ▸ he₂))
  have hact₂' := hact₁.pow k
  rw [hk] at hact₂'
  have h5 := hact₂.ratio hφker hact₂' h24
  rw [rootT_left, rootT_other ζ h24.symm (by simp [i4, i3, Fin.ext_iff]),
    rootT_other ζ (by simp [i2, i0, Fin.ext_iff]) (by simp [i2, i1, Fin.ext_iff]),
    rootT_other ζ (by simp [i4, i0, Fin.ext_iff]) (by simp [i4, i1, Fin.ext_iff])] at h5
  simp only [one_pow, inv_one, mul_one] at h5
  exact hζ1 h5

end CFSG.StandardType.LinUnitL

namespace CFSG.StandardType

open CFSG.Assembly LocalAnalysis.ComponentInitial.LinearFlag

theorem largeEvenLabelAll_linDvd_line {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  have hd5 : 5 ≤ l + 1 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases hpd with ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · have : p ≠ 4 := by
        intro h4
        rw [h4] at hp
        exact absurd hp (by decide)
      omega
    · nlinarith
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le hd5)),
    ggNoInvariantLineSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinUnitL.ggNoInvariantLineSCr_PSL hp hpK hd5 le_rfl)⟩

theorem ggLNoInvariantLineInputOn_linDvd : GGLNoInvariantLineInputOn GGLinDvdLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ hp hlab h =>
    largeEvenLabelAll_linDvd_line hp hlab h

end CFSG.StandardType

end

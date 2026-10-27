module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflTypeACore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGReflTypeALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank ≠ 3 ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1) ∨
    (lab.tag = .twD ∧ lab.rank = 2 ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

theorem ggTorusReflBridge_small [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusReflBridge p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

theorem ggTorusReflBridge_psl [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) (hpd : Nat.Coprime p d) :
    GGTorusReflBridge p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 β β' hββ' hN _ hfix
  have := Fact.mk hp
  have hd0 : 0 < d := by omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover (slHasSections_of_five_le hd) ψ hψ hker hperf
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : ∀ x ∈ X, ∃ B : GL (Fin d) K, conjAut d K B = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hXA hx hy
  have hXp : ∀ x ∈ X, x ^ p = 1 := hXA.2
  obtain ⟨A₀, hdiag, hle, hfull⟩ := exists_diagonalizing_slLift hp hpK hd0 hpd X hXc hXp hXI
  have hfull' := hfull (le_antisymm hle (by rw [hcardX]; exact hr))
  set Y := slLift hd0 hpd X hXc with hY
  have hTd : ∀ g ∈ Y, (∀ k, conjMat A₀ g k k ^ p = 1) ∧ ∏ k, conjMat A₀ g k k = 1 :=
    fun g hg => (conjMat_diag hg.1 (hdiag g hg)).2
  have hindA : ∀ a ∈ A, ∃ g ∈ Y,
      ∀ l, conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    obtain ⟨g, hg, hgφ⟩ := exists_mem_slLift_of_mem hd0 hpd hXc hXp hXI
      (show φa ∈ X from ⟨a, ha, hφa⟩)
    exact ⟨g, hg, fun l => by rw [hgφ, hφa]⟩
  have hβinv : ∀ l, β'⁻¹ (ψ l) = ψ (β⁻¹ l) := by
    intro l
    apply β'.injective
    rw [MulAut.apply_inv_self, hββ', MulAut.apply_inv_self]
  have hconj : ∀ (a : MulAut L') (x : MulAut (projectiveSL d K)), (∀ l, x (ψ l) = ψ (a l)) →
      ∀ l, (β' * x * β'⁻¹) (ψ l) = ψ ((β * a * β⁻¹) l) := by
    intro a x hx l
    simp only [MulAut.mul_apply]
    rw [hβinv, hx, hββ']
  have hNX : ∀ x ∈ X, β' * x * β'⁻¹ ∈ X := by
    rintro x ⟨a, ha, hxa⟩
    exact ⟨β * a * β⁻¹, hN a ha, hconj a x hxa⟩
  obtain ⟨π, m, hform⟩ := exists_pow_normal_form hd0 hpd hXc hp hp2 hpK (by omega) hXp hXI
    hdiag hfull' hNX
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by
    have := pow_pos hp.pos 3
    omega)
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hA hx hy
  have hrank : ∀ g₁ ∈ Y, ∀ g₂ ∈ Y, ∃ h ∈ Y, (h = g₁ ∨ ∃ e : ℕ, h = g₁ ^ e * g₂⁻¹) ∧
      β' * conjAut d K (SpecialLinearGroup.toGL h) * β'⁻¹ =
        conjAut d K (SpecialLinearGroup.toGL h) := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, h1⟩ := hg₁.2
    obtain ⟨a₂, ha₂, h2⟩ := hg₂.2
    rcases pseudoRefl_rank_one hp hAc hN hfix ha₁ ha₂ with hfix1 | ⟨e, he⟩
    · refine ⟨g₁, hg₁, Or.inl rfl, induced_unique ψ hψ (a := a₁) (fun l => ?_) h1⟩
      rw [hconj a₁ _ h1 l, hfix1]
    · have hinv2 : ∀ l, (conjAut d K (SpecialLinearGroup.toGL g₂))⁻¹ (ψ l) = ψ (a₂⁻¹ l) := by
        intro l
        apply (conjAut d K (SpecialLinearGroup.toGL g₂)).injective
        rw [MulAut.apply_inv_self, h2, MulAut.apply_inv_self]
      have hind : ∀ l, conjAut d K (SpecialLinearGroup.toGL (g₁ ^ e * g₂⁻¹)) (ψ l) =
          ψ ((a₁ ^ e * a₂⁻¹) l) := by
        intro l
        simp only [map_mul, map_pow, map_inv, MulAut.mul_apply]
        rw [hinv2, induced_pow ψ h1 e]
      refine ⟨g₁ ^ e * g₂⁻¹, Y.mul_mem (Y.pow_mem hg₁ e) (Y.inv_mem hg₂), Or.inr ⟨e, rfl⟩,
        induced_unique ψ hψ (a := a₁ ^ e * a₂⁻¹) (fun l => ?_) hind⟩
      rw [hconj _ _ hind l, he]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hvec : ∀ i j k : Fin d, i ≠ j → i ≠ k → j ≠ k → ∃ h ∈ Y,
      (∀ l, l ≠ i → l ≠ j → l ≠ k → conjMat A₀ h l l = 1) ∧ (∃ x, conjMat A₀ h x x ≠ 1) ∧
        ∀ l, conjMat A₀ h l l = conjMat A₀ h (π l) (π l) ^ m := by
    intro i j k hij hik hjk
    obtain ⟨g₁, hg₁, hg₁t⟩ := hfull' (rootT ζ i j) (rootT_pow hζ.pow_eq_one i j)
      (prod_rootT hζ0 hij)
    obtain ⟨g₂, hg₂, hg₂t⟩ := hfull' (rootT ζ i k) (rootT_pow hζ.pow_eq_one i k)
      (prod_rootT hζ0 hik)
    have hT1 : ∀ l, conjMat A₀ g₁ l l = rootT ζ i j l := fun l => by
      rw [hg₁t, diagonal_apply_eq]
    have hT2 : ∀ l, conjMat A₀ g₂ l l = rootT ζ i k l := fun l => by
      rw [hg₂t, diagonal_apply_eq]
    have hT12 : ∀ (e : ℕ) (l : Fin d),
        conjMat A₀ (g₁ ^ e * g₂⁻¹) l l = rootT ζ i j l ^ e * (rootT ζ i k l)⁻¹ := by
      intro e l
      rw [conjMat_mul_apply hd0 hpd hXc hdiag (Y.pow_mem hg₁ e),
        conjMat_pow_apply hd0 hpd hXc hdiag hg₁, conjMat_inv_apply hd0 hpd hXc hdiag hg₂, hT1,
        hT2]
    obtain ⟨h, hh, hh', hfixh⟩ := hrank g₁ hg₁ g₂ hg₂
    refine ⟨h, hh, ?_, ?_, fun l => hform h hh h hh hfixh.symm l⟩
    · intro l hli hlj hlk
      rcases hh' with rfl | ⟨e, rfl⟩
      · rw [hT1, rootT_other ζ hli hlj]
      · rw [hT12, rootT_other ζ hli hlj, rootT_other ζ hli hlk, one_pow, inv_one, mul_one]
    · rcases hh' with rfl | ⟨e, rfl⟩
      · exact ⟨i, by rw [hT1, rootT_left]; exact hζ1⟩
      · refine ⟨k, ?_⟩
        rw [hT12, rootT_other ζ (Ne.symm hik) (Ne.symm hjk), rootT_right ζ hik, one_pow, one_mul,
          inv_inv]
        exact hζ1
  obtain ⟨i, j, k, hij, hik, hjk, hπi, hπj, hπk⟩ := exists_three_fixed_of_supports hd π
    fun i j k hij hik hjk => by
      obtain ⟨h, hh, hsupp, ⟨x, hx⟩, hfixT⟩ := hvec i j k hij hik hjk
      refine ⟨fun l => conjMat A₀ h l l ≠ 1, fun l hl => ?_, fun l hl h1 => hl ?_, ?_⟩
      · by_contra hne
        push Not at hne
        exact hl (hsupp l hne.1 hne.2.1 hne.2.2)
      · rw [hfixT l, h1, one_pow]
      · obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ conjMat A₀ h y y ≠ 1 := by
          by_contra hne
          push Not at hne
          apply hx
          rw [← (hTd h hh).2, Finset.prod_eq_single x (fun l _ hl => hne l hl)
            (fun h' => absurd (Finset.mem_univ x) h')]
        exact ⟨x, y, Ne.symm hyx, hx, hy⟩
  have hm1 : ∀ y : K, y ^ p = 1 → y ^ m = y := by
    obtain ⟨h, hh, hsupp, ⟨x, hx⟩, hfixT⟩ := hvec i j k hij hik hjk
    have hπx : π x = x := by
      by_cases hxi : x = i
      · rw [hxi, hπi]
      by_cases hxj : x = j
      · rw [hxj, hπj]
      by_cases hxk : x = k
      · rw [hxk, hπk]
      exact absurd (hsupp x hxi hxj hxk) hx
    have hxm : conjMat A₀ h x x ^ m = conjMat A₀ h x x := by
      have h1 := hfixT x
      rw [hπx] at h1
      exact h1.symm
    have hprim : IsPrimitiveRoot (conjMat A₀ h x x) p :=
      IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime ((hTd h hh).1 x) hx)
    have : NeZero p := ⟨hp.ne_zero⟩
    intro y hy
    obtain ⟨c, -, hc⟩ := hprim.eq_pow_of_pow_eq_one hy
    rw [← hc, ← pow_mul, mul_comm c m, pow_mul, hxm]
  have hPY := fun g (hg : g ∈ Y) => permConj_conj_slLift hd0 hpd hXc hdiag hfull' π hg
  have hβa : ∀ a ∈ A, ∀ g ∈ Y, (∀ l, conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (a l)) →
      ∀ s, (β * a * β⁻¹) (φ s) = φ (permConj A₀ π * g * (permConj A₀ π)⁻¹ * s *
        (permConj A₀ π * g * (permConj A₀ π)⁻¹)⁻¹) := by
    intro a ha g hg hind
    obtain ⟨g'', hg'', hgg''⟩ := exists_mem_slLift_of_mem hd0 hpd hXc hXp hXI
      (hNX _ (show conjAut d K (SpecialLinearGroup.toGL g) ∈ X from hg.2))
    have heq : g'' = permConj A₀ π * g * (permConj A₀ π)⁻¹ :=
      eq_of_conjMat_apply hd0 hpd hXc hdiag hg'' (hPY g hg).1 fun l => by
        rw [hform g hg g'' hg'' hgg'' l, hm1 _ ((hTd g hg).1 _), (hPY g hg).2 l]
    have hind'' : ∀ l, conjAut d K (SpecialLinearGroup.toGL g'') (ψ l) =
        ψ ((β * a * β⁻¹) l) := by
      intro l
      rw [hgg'']
      exact hconj a _ hind l
    rw [← heq]
    exact act_of_lift hperfSL hker hφ hind''
  refine ⟨φ (permConj A₀ π), fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨g, hg, hind⟩ := hindA a ha
    have hact := act_of_lift hperfSL hker hφ hind
    have hmem : permConj A₀ π * g * (permConj A₀ π)⁻¹ * g⁻¹ ∈ Y :=
      Y.mul_mem (hPY g hg).1 (Y.inv_mem hg)
    have e : φ (permConj A₀ π) * (a (φ (permConj A₀ π)))⁻¹ =
        φ (permConj A₀ π * g * (permConj A₀ π)⁻¹ * g⁻¹) := by
      rw [hact]
      simp only [map_mul, map_inv]
      group
    refine ⟨by rw [e, ← map_pow, hmem.1, map_one], fun a' ha' => ?_⟩
    obtain ⟨g', hg', hind'⟩ := hindA a' ha'
    rw [e, act_of_lift hperfSL hker hφ hind', slLift_comm hd0 hpd X hXc hg' hmem,
      mul_inv_cancel_right]
  · obtain ⟨g, hg, hind⟩ := hindA a ha
    have hact := act_of_lift hperfSL hker hφ hind
    ext l
    obtain ⟨s, rfl⟩ := hφs l
    rw [hβa a ha g hg hind s]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    have e1 : (φ (permConj A₀ π))⁻¹ * φ s * φ (permConj A₀ π) =
        φ ((permConj A₀ π)⁻¹ * s * permConj A₀ π) := by
      simp only [map_mul, map_inv]
    rw [e1, hact]
    simp only [map_mul, map_inv]
    group

theorem recipeLinear_reflBridge {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hd4 : d ≠ 4) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 5 ≤ d by omega) with hd3 | hd5
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggTorusReflBridge_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusReflBridge_small hp hpK (by omega) hd3 hpd')⟩
  · exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' (slHasSections_of_five_le hd5)),
      ggTorusReflBridge_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusReflBridge_psl hp hp2 hpK hd5 hpd')⟩

theorem largeEvenLabelAll_reflBridge_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hl3, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hl3 hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_reflBridge hp hpn ⟨n, rfl⟩ (by omega) (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    exact recipeLinear_reflBridge hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl (by norm_num)
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end TypeA

end CFSG.StandardType

end

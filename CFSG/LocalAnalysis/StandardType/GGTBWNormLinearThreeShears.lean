module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTwoShears
public import CFSG.LocalAnalysis.StandardType.GGPGLBlockFrobenius
public import CFSG.LocalAnalysis.StandardType.GGTBWNormMpCellLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

namespace PGLTor

theorem CentralBlockModel.exists_SL_increment_three
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel 3 G)
    (hpK : 3 ∣ Nat.card K - 1) (hG : IsProjElem 3 G)
    {y : GL ι K} (hy : y ∈ G) (hy3 : y ^ 3 = 1) :
    ∃ E : SpecialLinearGroup ι K,
      SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
        (SpecialLinearGroup.toGL E)⁻¹ = y * (D.primitive : GL ι K) ∧
      ∀ z ∈ D.kernel, Commute (SpecialLinearGroup.toGL E) z := by
  classical
  have : Nonempty ι := ⟨D.point⟩
  let k := (Nat.card K - 1) / 3
  have hpk : 3 * k = Nat.card K - 1 := by
    have h := Nat.mod_add_div (Nat.card K - 1) 3
    rw [Nat.mod_eq_zero_of_dvd hpK, zero_add] at h
    exact h
  have hq : Nat.card K = 3 * k + 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hunit : ∀ u : Kˣ, u ^ (Nat.card K - 1) = 1 := by
    intro u
    simpa only [Nat.card_units] using pow_card_eq_one' (x := u)
  let ζ : Kˣ := D.scalar ^ k
  have hζ3 : ζ ^ 3 = 1 := by
    dsimp only [ζ]
    rw [← pow_mul, Nat.mul_comm k 3, hpk]
    exact hunit _
  have hζne : ζ ≠ 1 := by
    intro h0
    have hdiv : 3 ∣ Nat.card Kˣ := by simpa only [Nat.card_units] using hpK
    have hpow : D.scalar ^ (Nat.card Kˣ / 3) = 1 := by
      simpa only [ζ, k, Nat.card_units] using h0
    obtain ⟨u, hu⟩ := IsCyclic.exists_pow_eq_of_pow_card_div_eq_one
      (by decide : 0 < 3) hdiv hpow
    exact D.scalar_not_pow u hu
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζne
  have hζ : IsPrimitiveRoot ζ 3 := ⟨hζ3, fun m hm => by
    simpa only [hord] using orderOf_dvd_of_pow_eq_one hm⟩
  have hxq : (D.primitive : GL ι K) ^ Nat.card K =
      GeneralLinearGroup.scalar ι ζ * (D.primitive : GL ι K) := by
    rw [hq, pow_add, pow_mul, pow_one, D.primitive_pow, ← map_pow]
  have hc : (Nat.card G : K) ≠ 0 :=
    isProjElem_card_cast_ne_zero Nat.prime_three (by decide) hG
  let w : Fin D.numBlocks → Fin D.numBlocks → Kˣ :=
    fun b j => if j = b then ζ else 1
  have hraw : ∀ b : Fin D.numBlocks, ∃ E : SpecialLinearGroup ι K,
      SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
        (SpecialLinearGroup.toGL E)⁻¹ = D.scalarBlocks (w b) * (D.primitive : GL ι K) ∧
      ∀ f : Fin D.numBlocks → Kˣ, Commute (SpecialLinearGroup.toGL E) (D.scalarBlocks f) := by
    intro b
    obtain ⟨E, hEc, hEx⟩ := D.exists_raw_SL_block_operator hc b
    exact ⟨E, hEx D.primitive ζ hxq, hEc⟩
  choose Eb hEbx hEbc using hraw
  have hyK : y ∈ D.kernel := (D.kernel_mem_iff y hy).mpr
    ⟨1, by simpa using hy3⟩
  obtain ⟨f, hf, hfy⟩ := Subgroup.mem_map.mp (D.kernel_le_blockKernelGroup hyK)
  have hf3 : f ^ 3 = 1 := D.scalarBlocks_injective (by
    rw [map_pow, hfy, hy3, map_one])
  have hfc : ∀ b, f b ^ 3 = 1 := fun b => by
    simpa only [Pi.pow_apply, Pi.one_apply] using congrFun hf3 b
  have hexp : ∀ b, ∃ r : ℕ, r < 3 ∧ ζ ^ r = f b :=
    fun b => QuotMove.exists_pow_eq_units hζ (hfc b)
  choose r hr hrf using hexp
  have hpow : ∀ b m,
      (SpecialLinearGroup.toGL (Eb b)) ^ m * (D.primitive : GL ι K) *
        ((SpecialLinearGroup.toGL (Eb b)) ^ m)⁻¹ =
      (D.scalarBlocks (w b)) ^ m * (D.primitive : GL ι K) := by
    intro b m
    induction m with
    | zero => group
    | succ m ih =>
      have hcomm := ((hEbc b (w b)).pow_right m).eq
      calc (SpecialLinearGroup.toGL (Eb b)) ^ (m + 1) * (D.primitive : GL ι K) *
            ((SpecialLinearGroup.toGL (Eb b)) ^ (m + 1))⁻¹ =
          SpecialLinearGroup.toGL (Eb b) *
            ((SpecialLinearGroup.toGL (Eb b)) ^ m * (D.primitive : GL ι K) *
              ((SpecialLinearGroup.toGL (Eb b)) ^ m)⁻¹) *
            (SpecialLinearGroup.toGL (Eb b))⁻¹ := by group
        _ = SpecialLinearGroup.toGL (Eb b) * (D.scalarBlocks (w b)) ^ m *
            (D.primitive : GL ι K) * (SpecialLinearGroup.toGL (Eb b))⁻¹ := by rw [ih]; group
        _ = (D.scalarBlocks (w b)) ^ m *
            (SpecialLinearGroup.toGL (Eb b) * (D.primitive : GL ι K) *
              (SpecialLinearGroup.toGL (Eb b))⁻¹) := by rw [hcomm]; group
        _ = (D.scalarBlocks (w b)) ^ (m + 1) * (D.primitive : GL ι K) := by rw [hEbx]; group
  let fs : Finset (Fin D.numBlocks) → Fin D.numBlocks → Kˣ :=
    fun s j => if j ∈ s then f j else 1
  have hbuild : ∀ s : Finset (Fin D.numBlocks), ∃ E : SpecialLinearGroup ι K,
      SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
        (SpecialLinearGroup.toGL E)⁻¹ = D.scalarBlocks (fs s) * (D.primitive : GL ι K) ∧
      ∀ g : Fin D.numBlocks → Kˣ, Commute (SpecialLinearGroup.toGL E) (D.scalarBlocks g) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, fun g => by simp⟩
      have hfs0 : fs ∅ = (1 : Fin D.numBlocks → Kˣ) := by
        ext j
        simp [fs]
      rw [hfs0]
      simp only [map_one, inv_one, one_mul, mul_one]
    | @insert b s hb ih =>
      obtain ⟨E, hEx, hEc⟩ := ih
      have hfun : fs s * w b ^ r b = fs (insert b s) := by
        ext j
        by_cases hj : j = b
        · subst j
          simp [fs, w, hb, hrf b]
        · simp [fs, w, hj]
      refine ⟨Eb b ^ r b * E, ?_, ?_⟩
      · rw [map_mul, map_pow]
        have hcomm := ((hEbc b (fs s)).pow_left (r b)).eq
        calc (SpecialLinearGroup.toGL (Eb b) ^ r b * SpecialLinearGroup.toGL E) *
              (D.primitive : GL ι K) *
              (SpecialLinearGroup.toGL (Eb b) ^ r b * SpecialLinearGroup.toGL E)⁻¹ =
            SpecialLinearGroup.toGL (Eb b) ^ r b *
              (SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
                (SpecialLinearGroup.toGL E)⁻¹) *
              (SpecialLinearGroup.toGL (Eb b) ^ r b)⁻¹ := by group
          _ = SpecialLinearGroup.toGL (Eb b) ^ r b * D.scalarBlocks (fs s) *
              (D.primitive : GL ι K) * (SpecialLinearGroup.toGL (Eb b) ^ r b)⁻¹ := by
            rw [hEx]; group
          _ = D.scalarBlocks (fs s) *
              (SpecialLinearGroup.toGL (Eb b) ^ r b * (D.primitive : GL ι K) *
                (SpecialLinearGroup.toGL (Eb b) ^ r b)⁻¹) := by rw [hcomm]; group
          _ = D.scalarBlocks (fs s) * ((D.scalarBlocks (w b)) ^ r b *
              (D.primitive : GL ι K)) := by rw [hpow]
          _ = D.scalarBlocks (fs s * w b ^ r b) * (D.primitive : GL ι K) := by
            rw [map_mul, map_pow]; group
          _ = D.scalarBlocks (fs (insert b s)) * (D.primitive : GL ι K) := by rw [hfun]
      · intro g
        rw [map_mul, map_pow]
        exact ((hEbc b g).pow_left (r b)).mul_left (hEc g)
  obtain ⟨E, hEx, hEc⟩ := hbuild Finset.univ
  have hfs : fs Finset.univ = f := by ext j; simp [fs]
  refine ⟨E, ?_, ?_⟩
  · rwa [hfs, hfy] at hEx
  · intro z hz
    obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp (D.kernel_le_blockKernelGroup hz)
    rw [← hgz]
    exact hEc g


end PGLTor

theorem central_order_three_lifts_of_reflections
    {K : Type} [Field K] [Finite K] {d : ℕ}
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d K} {A : Subgroup (MulAut L')}
    (hpK : 3 ∣ Nat.card K - 1) (hd3 : 3 ∣ d) (hd0 : 0 < d)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) :
    ∀ x : GL (Fin d) K, conjAut d K x ∈ inducedSub ψ A → x ^ 3 = 1 →
      ∀ y : GL (Fin d) K, conjAut d K y ∈ inducedSub ψ A → y * x = x * y := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hG : PGLTor.IsProjElem 3 ((inducedSub ψ A).comap (conjAut d K)) :=
    isProjElem_comap hd0 (isElemAbelian_inducedSub hψ hA)
  intro x hx hx3 y hy
  by_contra hne
  have hu1 : PGLTor.commChar hG hx ⟨y, hy⟩ ≠ 1 := fun h1 =>
    hne ((PGLTor.commChar_eq_one_iff hG hx ⟨y, hy⟩).mp h1).symm
  obtain ⟨l, hl⟩ := hG.pow_scalar y hy
  exact false_of_noncomm_lifts_three hpK hd3 hd0 hψ hker hperf hA hAI hx hy hx3
    (PGLTor.commChar_spec hG hx ⟨y, hy⟩) hu1
    (PGLTor.commChar_pow_eq_one hG hx ⟨y, hy⟩) hl ι φ h α hdiag hlin hgen


theorem ggTorusWNormSC_three_ge_twelve
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (hpK : 3 ∣ Nat.card K - 1) (hd3 : 3 ∣ d) (hd : 12 ≤ d) :
    GGTorusWNormSC 3 (projectiveSL d K) (Set.range (conjAut d K)) := by
  have hd5 : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ hh α
    hM hC hpair hlin hgen s hs
  classical
  let G := (inducedSub ψ A).comap (conjAut d K)
  have hG : PGLTor.IsProjElem 3 G :=
    isProjElem_comap hd0 (isElemAbelian_inducedSub hψ hA)
  have hdiag : ∀ i, α i (hh i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
  have hcent := central_order_three_lifts_of_reflections hpK hd3 hd0 hψ hker hperf hA hAI
    ι φ hh α hdiag hlin hgen
  rcases PGLTor.toral_or_exists_centralBlockModel Nat.prime_three (by decide) hpK hG hcent with
    htor | hnt
  · obtain ⟨A₀, hA₀⟩ := htor
    have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
      (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
        (Or.inl (by omega))).commutator_eq_top
    obtain ⟨π, hπs, hπker, hdiagA⟩ := TypeANbrDvd.exists_actsDiag_model hperfSL
      (slHasSections_of_five_le hd5) hψ hker hperf hAI (A₀ := A₀) fun B hB => hA₀ B hB
    exact ggWNormConcl_of_linear_diagonal Nat.prime_three (by decide) hpK hd5 hπs hπker
      hA h3 hsc hdiagA hM hC ι φ hh α hpair hlin hgen hs
  · exfalso
    obtain ⟨D⟩ := hnt
    let x₀ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨D.primitive, Subgroup.mem_top _⟩
    refine QuotMove.false_of_shears (QuotMove.isScalarQuot_PSL hd0) Nat.prime_three
      (by decide : (3 : ℕ) ≠ 2) hψ hker hperf hA ?_ h3 (x₀ := x₀)
      D.primitive.2 D.primitive_pow D.scalar_not_pow ?_ hM hC ι φ hh α hpair hlin hgen
    · intro a ha
      obtain ⟨φa, hφa, hact⟩ := hAI a ha
      obtain ⟨g, rfl⟩ := hφa
      exact ⟨⟨g, Subgroup.mem_top _⟩, hact⟩
    · intro y hy hyp
      have hyG : (y : GL (Fin d) K) ∈ G := hy
      obtain ⟨E, hEx, hEc⟩ := D.exists_SL_increment_three hpK hG hyG hyp
      refine ⟨⟨SpecialLinearGroup.toGL E, E, rfl⟩, hEx, ?_⟩
      intro z hz hzp
      have hzK : (z : GL (Fin d) K) ∈ D.kernel :=
        (D.kernel_mem_iff z hz).mpr ⟨1, by simpa using hzp⟩
      exact (hEc z hzK).eq

end TypeA


theorem ggTorusWNormSC_linear_three_ge_twelve
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (hpK : 3 ∣ Nat.card K - 1) (hd3 : 3 ∣ d) (hd : 12 ≤ d) :
    GGTorusWNormSC 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_three_ge_twelve hpK hd3 hd)

theorem largeEvenLabelAll_wnorm_linear_w3 {p : ℕ} {lab : LargeEvenLabel}
    (hW : GGTBWNormW3SplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  rcases hW with ⟨ht, hp, hd3, hd, hpK⟩
  dsimp only at ht hp hd3 hd hpK ⊢
  subst tag
  subst p
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n)
    (fun R _ I F => Q R I F ∧ GGTorusWNormSC 3 R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_three_ge_twelve (by rwa [hK]) hd3 hd

end CFSG.StandardType

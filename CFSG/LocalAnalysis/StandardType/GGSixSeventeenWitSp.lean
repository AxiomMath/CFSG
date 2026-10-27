module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpBasic
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame

public section

namespace CFSG.StandardType

namespace WitSp

open Matrix hiding gram gram_apply
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {K : Type} [Field K] {n : ℕ}

theorem equivStatedSp_diagonal (t : Fin n → Kˣ) :
    CFSG.LieType.Universal.Symplectic.equivStatedSp n K (TauCeti.GLSymplecticFin.diagonal t) =
      diagSp K n t := by
  apply mat_injective
  rw [mat_apply, RestSp.coe_equiv_diagonal, TauCeti.diagGL_coe, mat_diagSp]
  congr 1
  funext a
  rcases a with i | i <;> rfl

@[expose] noncomputable def rootElt (k : Fin n) : StatedSp n K :=
  longBlock K n k (mkSL !![1, 1; 0, 1] (by simp [det_fin_two_of]))

theorem mat_rootElt_apply (k : Fin n) :
    mat n K (rootElt k) (Sum.inl k) (Sum.inr k) = 1 := by
  rw [rootElt, mat_longBlock]
  simp [CFSG.LieType.Steinberg.Sp.blockMat]

theorem rootElt_mem_suppGroup (k : Fin n) : rootElt (K := K) k ∈ suppGroup (coords k) := by
  rw [← range_longBlock]
  exact ⟨_, rfl⟩

theorem eq_one_of_commute_rootElt [CharP K 2] {u : Fin n → Kˣ} {k : Fin n}
    (h : Commute (rootElt (K := K) k) (diagSp K n u)) : u k = 1 := by
  have hz := (commute_diagSp_iff (rootElt k) u).1 h (Sum.inl k) (Sum.inr k)
  rw [mat_rootElt_apply] at hz
  have hw : diagSpEntry u (Sum.inl k) = diagSpEntry u (Sum.inr k) := by
    by_contra hne
    exact one_ne_zero (hz hne)
  rw [diagSpEntry_inl, diagSpEntry_inr] at hw
  have hu : u k = (u k)⁻¹ := Units.ext hw
  exact eq_one_of_mul_self_eq_one (by
    calc u k * u k = u k * (u k)⁻¹ := by rw [← hu]
      _ = 1 := mul_inv_cancel _)

section Witness

variable {G : Type} [Group G]

theorem card_le_of_diag [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {φ : StatedSp n K →* G} {X : Subgroup G} (T : Finset (Fin n))
    (hX : ∀ x ∈ X, ∃ u : Fin n → Kˣ, x = φ (diagSp K n u) ∧ (∀ k, u k ^ p = 1) ∧
      ∀ k ∉ T, u k = 1) :
    Nat.card X ≤ p ^ T.card := by
  classical
  choose u hu using fun x : X => hX x.1 x.2
  let r : X → (↥T → rootsOfUnity p K) := fun x k => ⟨u x k, by
    rw [mem_rootsOfUnity]
    exact (hu x).2.1 k⟩
  have hr : Function.Injective r := by
    intro x y hxy
    have huv : u x = u y := by
      funext k
      by_cases hk : k ∈ T
      · have := congrArg (fun g => ((g ⟨k, hk⟩ : rootsOfUnity p K) : Kˣ)) hxy
        simpa [r] using this
      · rw [(hu x).2.2 k hk, (hu y).2.2 k hk]
    apply Subtype.ext
    rw [(hu x).1, (hu y).1, huv]
  calc Nat.card X ≤ Nat.card (↥T → rootsOfUnity p K) := Nat.card_le_card_of_injective r hr
    _ = p ^ T.card := by
      rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_fintype_card,
        Fintype.card_coe]

theorem witness_of_diag [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) {B Bs G₀ : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : StatedSp n K →* G} (hφ : Function.Injective φ) (hrange : φ.range = G₀)
    (hfr : ∀ x ∈ Bs, ∃ u : Fin n → Kˣ, x = φ (diagSp K n u))
    {s : Fin n → Kˣ} (hsp : ∀ k, s k ^ p = 1) {j₁ j₂ : Fin n} (hs1 : s j₁ ≠ 1)
    (hsupp : ∀ k, k ≠ j₁ → k ≠ j₂ → s k = 1) {k₀ : Fin n} (hk₀1 : k₀ ≠ j₁) (hk₀2 : k₀ ≠ j₂) :
    φ (diagSp K n s) ∈ Bs ∧ φ (diagSp K n s) ≠ 1 ∧
      ∃ L₂ : Subgroup G, IsComponentOf L₂ (G₀ ⊓ Subgroup.centralizer {φ (diagSp K n s)}) ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2 := by
  set e := φ (diagSp K n s) with he
  have hsP : s ^ p = 1 := funext hsp
  have hcomm : ∀ x ∈ Bs, x * e = e * x := by
    intro x hx
    obtain ⟨u, rfl⟩ := hfr x hx
    rw [he, ← φ.map_mul, ← φ.map_mul, (commute_diagSp_diagSp u s).eq]
  have heB : e ∈ Bs := hBs.2.2.2 e (Subgroup.mem_centralizer_iff.mpr hcomm)
    (by rw [he, ← map_pow, ← map_pow, hsP, map_one, map_one])
  have he1 : e ≠ 1 := by
    intro h1
    apply hs1
    have h2 : diagSp K n s = 1 := hφ (by rw [← he, h1, map_one])
    have h3 : s = 1 := diagSp_injective (by rw [h2, map_one])
    rw [h3, Pi.one_apply]
  refine ⟨heB, he1, (oneBlock s).map φ, ?_, ?_⟩
  · have hle : (oneBlock s).map φ ≤ G₀ ⊓ Subgroup.centralizer {e} := by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨hrange ▸ ⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [he, ← map_mul, ← map_mul, (commute_diagSp_of_mem_oneBlock hg).eq]
    have hnorm : (((oneBlock s).map φ).subgroupOf (G₀ ⊓ Subgroup.centralizer {e})).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      rintro _ y ⟨g, hg, rfl⟩ ⟨hyG, hyc⟩
      rw [← hrange] at hyG
      obtain ⟨c, rfl⟩ := hyG
      have hc : Commute c (diagSp K n s) := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyc
        exact hφ (by rw [map_mul, map_mul, ← he]; exact h1)
      exact ⟨c * g * c⁻¹, conj_mem_oneBlock hc hg, by rw [map_mul, map_mul, map_inv]⟩
    have hker : φ.ker ≤ Subgroup.center (StatedSp n K) := by
      intro z hz
      rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ, Subgroup.mem_bot] at hz
      rw [hz]
      exact Subgroup.one_mem _
    exact ⟨hle, IsSubnormal.step hle hnorm (IsSubnormal.refl _),
      SURepair.isQuasisimple_map_of_isQuasisimple hker
        (isQuasisimple_oneBlock h4 (hsupp k₀ hk₀1 hk₀2))⟩
  · refine (card_le_of_diag (φ := φ) hp hpK {j₁, j₂} fun x hx => ?_).trans
      (Nat.pow_le_pow_right hp.pos Finset.card_le_two)
    obtain ⟨u, rfl⟩ := hfr x hx.1
    have hup : u ^ p = 1 := diagSp_injective (hφ (by
      rw [map_pow, map_pow, hBs.2.1.2 _ hx.1, map_one, map_one]))
    refine ⟨u, rfl, fun k => congrFun hup k, fun k hk => ?_⟩
    have hk1 : k ≠ j₁ := fun h => hk (by simp [h])
    have hk2 : k ≠ j₂ := fun h => hk (by simp [h])
    have hmem : rootElt (K := K) k ∈ oneBlock s :=
      suppGroup_mono (coords_subset_oneSet (hsupp k hk1 hk2)) (rootElt_mem_suppGroup k)
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ ⟨_, hmem, rfl⟩
    exact eq_one_of_commute_rootElt (hφ (by rw [map_mul, map_mul]; exact hc))

end Witness

@[expose] noncomputable def rdiag (j₁ j₂ : Fin n) (ζ : Kˣ) : Fin n → Kˣ :=
  Function.update (Function.update (fun _ => (1 : Kˣ)) j₁ ζ) j₂ ζ⁻¹

theorem rdiag_left {j₁ j₂ : Fin n} (h : j₁ ≠ j₂) (ζ : Kˣ) : rdiag j₁ j₂ ζ j₁ = ζ := by
  rw [rdiag, Function.update_of_ne h, Function.update_self]

theorem rdiag_of_ne {j₁ j₂ k : Fin n} (h₁ : k ≠ j₁) (h₂ : k ≠ j₂) (ζ : Kˣ) :
    rdiag j₁ j₂ ζ k = 1 := by
  rw [rdiag, Function.update_of_ne h₂, Function.update_of_ne h₁]

theorem rdiag_pow {j₁ j₂ : Fin n} {N : ℕ} {ζ : Kˣ} (hζ : ζ ^ N = 1) (k : Fin n) :
    rdiag j₁ j₂ ζ k ^ N = 1 := by
  by_cases h₂ : k = j₂
  · subst h₂
    rw [rdiag, Function.update_self, inv_pow, hζ, inv_one]
  by_cases h₁ : k = j₁
  · subst h₁
    rw [rdiag_left h₂, hζ]
  · rw [rdiag_of_ne h₁ h₂, one_pow]

theorem prod_rdiag {j₁ j₂ : Fin n} (h : j₁ ≠ j₂) (ζ : Kˣ) : ∏ i, rdiag j₁ j₂ ζ i = 1 := by
  rw [rdiag, SLRep.prod_update_update_const h, one_pow, mul_one, inv_mul_cancel]

theorem oneBlock_eq_bot {t : Fin n → Kˣ} (ht : ∀ k, t k ≠ 1) : oneBlock (K := K) t = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hS : ∀ a, a ∉ oneSet t := by
    intro a
    rcases a with i | i
    · exact fun h => ht i (mem_oneSet_inl.mp h)
    · exact fun h => ht i (mem_oneSet_inr.mp h)
  have hm : mat n K g = 1 := by
    ext r c
    exact hg r c (fun h => hS r h.1)
  rw [Subgroup.mem_bot]
  exact mat_injective (by rw [hm, map_one])

theorem leviEmbedSL_mem_oneBlock {t : Fin n → Kˣ} {I : Finset (Fin n)}
    (hI : ∀ j ∈ I, t j = 1) {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hA : A ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I) :
    leviEmbedSL K n A ∈ oneBlock t := by
  have hA' : A⁻¹ ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I :=
    Subgroup.inv_mem _ hA
  intro r c hrc
  rw [mat_leviEmbedSL]
  rcases r with a | a <;> rcases c with b | b
  · rw [fromBlocks_apply₁₁]
    have hab : a ∉ I ∨ b ∉ I := by
      by_contra h
      push Not at h
      exact hrc ⟨mem_oneSet_inl.mpr (hI a h.1), mem_oneSet_inl.mpr (hI b h.2)⟩
    rw [hA a b hab]
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (Sum.inl_injective h'))]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.one_apply_ne Sum.inl_ne_inr]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.one_apply_ne Sum.inr_ne_inl]
  · rw [fromBlocks_apply₂₂, Matrix.transpose_apply]
    have hab : b ∉ I ∨ a ∉ I := by
      by_contra h
      push Not at h
      exact hrc ⟨mem_oneSet_inr.mpr (hI a h.2), mem_oneSet_inr.mpr (hI b h.1)⟩
    rw [hA' b a hab]
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (Ne.symm h),
        Matrix.one_apply_ne (fun h' => h (Sum.inr_injective h'))]

theorem toGL_ggDiagSL_eq [CharP K 2] (δ : Fin n → Kˣ) (hδ : ∏ i, (δ i : K) = 1) :
    Matrix.SpecialLinearGroup.toGL (ggDiagSL (fun i => (δ i : K)) hδ) = TauCeti.diagGL δ := by
  apply Units.ext
  rw [TauCeti.diagGL_coe]
  rfl

theorem innerDiagA_diagGL_eq {m : ℕ} (t : Fin (m + 1) → Kˣ) :
    InnerDiagA.diagGL t = TauCeti.diagGL t := by
  apply Units.ext
  rw [InnerDiagA.coe_diagGL, TauCeti.diagGL_coe]

theorem toGL_conjSL {m : ℕ} (A : GL (Fin (m + 1)) K)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) K) :
    Matrix.SpecialLinearGroup.toGL (InnerDiagA.conjSL A u) =
      A * Matrix.SpecialLinearGroup.toGL u * A⁻¹ := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, InnerDiagA.coe_conjSL, Units.val_mul,
    Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

end WitSp

section Inputs

open scoped commutatorElement in
open WitSp CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot CFSG.LieType.Universal in
theorem ggSixSeventeenWitnessOn_PSpSplit : GGSixSeventeenWitnessOn GGPSpSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨rfl, hpq⟩ := hP
  obtain ⟨A₀, hA₀⟩ := ggSpBstarFrameInput_holds G p B Bs x L D J n f ψ hctx s1 hpq
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hadm := hctx.2.2.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hpq
  have hq4 : 4 ≤ 2 ^ f := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.le_of_dvd (by omega) hpq
    have h3 := hp.two_le
    have h5 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := hcardF ▸ hq4
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hBs : GGBstar p B Bs := hctx.2.1
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨ψS, hψS⟩ : ∃ ψS : StatedSp n (GaloisField 2 f) →* G, ∀ a, ψS a = ψ a :=
    ⟨ψ, fun _ => rfl⟩
  have hψS' : Function.Injective ψS := fun a c h => hψ (by rw [← hψS, ← hψS]; exact h)
  have hrangeS : ψS.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hψS a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hψS a⟩
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : StatedSp n (GaloisField 2 f) →* G,
      φ₀ = ψS.comp (MulAut.conj A₀).toMonoidHom := ⟨_, rfl⟩
  have hφ₀a : ∀ a, φ₀ a = ψS (A₀ * a * A₀⁻¹) := fun a => by
    rw [hφ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hframe₀ : ∀ y ∈ Bs, ∃ u, y = φ₀ (diagSp (GaloisField 2 f) n u) := by
    intro y hy
    obtain ⟨u, hu⟩ := hA₀ y hy
    refine ⟨u, ?_⟩
    rw [hu, RestSp.frameDiag, equivStatedSp_diagonal, hφ₀a, hψS]
  obtain ⟨tb, htb⟩ := hframe₀ b hpair.1
  obtain ⟨S, hS⟩ := exists_aligned tb
  obtain ⟨t', ht'⟩ : ∃ t' : Fin n → (GaloisField 2 f)ˣ, t' = flipU S tb := ⟨_, rfl⟩
  rw [← ht'] at hS
  obtain ⟨φ, hφ⟩ : ∃ φ : StatedSp n (GaloisField 2 f) →* G,
      φ = φ₀.comp (MulAut.conj (swapSp S)).toMonoidHom := ⟨_, rfl⟩
  have hφa : ∀ a, φ a = φ₀ (swapSp S * a * (swapSp S)⁻¹) := fun a => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hφd : ∀ u, φ (diagSp _ n u) = φ₀ (diagSp _ n (flipU S u)) := by
    intro u
    rw [hφa, swapSp_conj_diagSp]
  have hframe : ∀ y ∈ Bs, ∃ u, y = φ (diagSp (GaloisField 2 f) n u) := by
    intro y hy
    obtain ⟨u, rfl⟩ := hframe₀ y hy
    exact ⟨flipU S u, by rw [hφd, flipU_flipU]⟩
  have hb : b = φ (diagSp _ n t') := by rw [hφd, ht', flipU_flipU]; exact htb
  have hφinj : Function.Injective φ := by
    intro a c h
    rw [hφa, hφa, hφ₀a, hφ₀a] at h
    have h1 := hψS' h
    have h2 : swapSp S * a * (swapSp S)⁻¹ = swapSp S * c * (swapSp S)⁻¹ :=
      mul_left_cancel (mul_right_cancel h1)
    exact mul_left_cancel (mul_right_cancel h2)
  have hφrange : φ.range = ggG0 p B x L D J := by
    rw [← hrangeS]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hφa, hφ₀a]
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(swapSp S)⁻¹ * (A₀⁻¹ * a * A₀) * swapSp S, ?_⟩
      rw [hφa, hφ₀a]
      congr 1
      group
  have hkerφ : φ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := by
    intro z hz
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφinj, Subgroup.mem_bot] at hz
    rw [hz]
    exact Subgroup.one_mem _
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hn4 : 4 ≤ n := by
    have h := card_le_of_diag (φ := φ) hp hpF (X := Bs) Finset.univ fun y hy => by
      obtain ⟨u, rfl⟩ := hframe y hy
      have hup : u ^ p = 1 := diagSp_injective (hφinj (by
        rw [map_pow, map_pow, hBs.2.1.2 _ hy, map_one, map_one]))
      exact ⟨u, rfl, fun k => congrFun hup k, fun k hk => absurd (Finset.mem_univ k) hk⟩
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans h)
  have hLc : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) := hpair.2.2.1
  have hmemC : ∀ y ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {b},
      ∃ c, y = φ c ∧ Commute c (diagSp _ n t') := by
    rintro y ⟨hyG, hyc⟩
    rw [← hφrange] at hyG
    obtain ⟨c, rfl⟩ := hyG
    refine ⟨c, rfl, hφinj ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyc
    rw [hb] at h1
    rw [map_mul, map_mul]
    exact h1
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = (oneBlock t').map φ := ⟨_, rfl⟩
  have hNle : N ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} := by
    rw [hN]
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨hφrange ▸ ⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hb, ← φ.map_mul, ← φ.map_mul, (commute_diagSp_of_mem_oneBlock hg).eq]
  have hNnorm : (N.subgroupOf (ggG0 p B x L D J ⊓ Subgroup.centralizer {b})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNle]
    intro h y hh hy
    rw [hN] at hh ⊢
    obtain ⟨g, hg, rfl⟩ := hh
    obtain ⟨c, rfl, hc⟩ := hmemC y hy
    exact ⟨c * g * c⁻¹, conj_mem_oneBlock hc hg, by rw [map_mul, map_mul, map_inv]⟩
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hLc.1).mp hLc
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
  obtain ⟨ζu, hζu⟩ : ∃ ζu : (GaloisField 2 f)ˣ, (ζu : GaloisField 2 f) = ζ :=
    ⟨Units.mk0 ζ (hζ.ne_zero hp.ne_zero), rfl⟩
  have hζu1 : ζu ≠ 1 := fun h => hζ.ne_one hp.one_lt (by rw [← hζu, h, Units.val_one])
  have hζup : ζu ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one,
    Units.val_one])
  rcases CFSG.LocalAnalysis.ComponentInitial.component_normal_subgroup hc hNnorm with hA | hB
  ·
    have hLN : L₁ ≤ N := CFSG.LocalCores.le_of_subgroupOf_le hLc.1 hA
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, t' k₀ = 1 := by
      by_contra h
      push Not at h
      apply commutator_ne_bot_of_isQuasisimple hLc.2.2
      have hN' : N = ⊥ := by rw [hN, oneBlock_eq_bot h, Subgroup.map_bot]
      have hL0 : L₁ = ⊥ := le_bot_iff.mp (by rw [← hN']; exact hLN)
      rw [hL0]
      exact Subgroup.commutator_bot_left _
    have hNq : CFSG.Assembly.IsQuasisimple N := by
      rw [hN]
      exact SURepair.isQuasisimple_map_of_isQuasisimple hkerφ (isQuasisimple_oneBlock h4 hk₀)
    have hLeq := LinTypeAk.eq_of_isComponentOf_of_le hLc hLN hNle hNq
    obtain ⟨k', hk'⟩ := SLRep.exists_ne_fin hn2 k₀
    have hsp : ∀ k, (Pi.mulSingle k₀ ζu : Fin n → (GaloisField 2 f)ˣ) k ^ p = 1 := by
      intro k
      by_cases hk : k = k₀
      · subst hk
        rw [Pi.mulSingle_eq_same, hζup]
      · simp [hk]
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe
      (s := Pi.mulSingle k₀ ζu) hsp (j₁ := k₀) (j₂ := k₀)
      (by rw [Pi.mulSingle_eq_same]; exact hζu1)
      (fun k hk _ => by simp [hk]) hk' hk'
    have heL : φ (diagSp _ n (Pi.mulSingle k₀ ζu)) ∈ L₁ := by
      rw [hLeq, hN]
      exact ⟨_, suppGroup_mono (coords_subset_oneSet hk₀) (isSupp_rootTorusHom k₀ ζu), rfl⟩
    exact Or.inr ⟨_, heL, Or.inl ⟨heB, he1, Or.inr ⟨L₂, hL₂, hcard⟩⟩⟩
  ·
    have hcomm : ⁅L₁, N⁆ = ⊥ := by
      have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLc.1 hB
      rwa [inf_eq_left.mpr hNle] at h'
    have hSL : ∀ y ∈ L₁, ∃ c ∈ siegelLeviGL (GaloisField 2 f) n, y = φ c := by
      intro y hy
      obtain ⟨c, rfl, hc⟩ := hmemC y (hLc.1 hy)
      refine ⟨c, mem_siegelLeviGL_of_aligned h4 hS hc fun g hg => ?_, rfl⟩
      have h1 : ⁅φ c, φ g⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hy (show φ g ∈ N from hN ▸ ⟨g, hg, rfl⟩)
        rw [hcomm] at this
        exact Subgroup.mem_bot.mp this
      exact hφinj (by rw [map_mul, map_mul]; exact commutatorElement_eq_one_iff_mul_comm.mp h1)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨ψB, hψB⟩ : ∃ ψB : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G,
        ψB = φ.comp (leviEmbedSL (GaloisField 2 f) (m + 1)) := ⟨_, rfl⟩
    have hψBa : ∀ A, ψB A = φ (leviEmbedSL (GaloisField 2 f) (m + 1) A) := fun A => by
      rw [hψB, MonoidHom.comp_apply]
    have hkerB : ψB.ker ≤ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := by
      intro z hz
      have h1 : ψB z = ψB 1 := by rw [MonoidHom.mem_ker.mp hz, map_one]
      rw [hψBa, hψBa] at h1
      rw [leviEmbedSL_injective (hφinj h1)]
      exact Subgroup.one_mem _
    have hLB : L₁ ≤ ψB.range := by
      rw [← LinSemisimple.commutator_eq_self_of_isQuasisimple hLc.2.2, Subgroup.commutator_le]
      intro y₁ hy₁ y₂ hy₂
      obtain ⟨c₁, hc₁, rfl⟩ := hSL y₁ hy₁
      obtain ⟨c₂, hc₂, rfl⟩ := hSL y₂ hy₂
      obtain ⟨A, hA⟩ := commutator_mem_siegelLevi hc₁ hc₂
      exact ⟨A, by rw [hψBa, hA, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
        map_inv]⟩
    have hbI : (b, InnerDiagA.diagGL t') ∈ LinFusion.ggInducedPairs ψB := by
      rw [LinFusion.mem_ggInducedPairs]
      intro u
      rw [hb, hψBa, hψBa, ← φ.map_inv, ← φ.map_mul, ← φ.map_mul, innerDiagA_diagGL_eq]
      congr 1
      rw [leviEmbedSL, MonoidHom.comp_apply, MonoidHom.comp_apply, toGL_conjSL, diagSp_apply,
        map_mul, map_mul, map_inv]
    have hL' : IsComponentOf L₁
        (ψB.range ⊓ Subgroup.centralizer (Set.range fun _ : Unit => b)) := by
      rw [Set.range_const]
      refine CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hLc
        (le_inf hLB (hLc.1.trans inf_le_right)) (inf_le_inf_right _ ?_)
      rintro _ ⟨A, rfl⟩
      rw [hψBa, ← hφrange]
      exact ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hkerB
      (d := fun _ : Unit => t') (b := fun _ => b) (fun _ => hbI) hL'
    obtain ⟨hI2, -⟩ := LinSemisimple.two_le_card_of_isQuasisimple_le hL'.2.2 hi.le
    have hmemI : ∀ j, j ∈ LinSemisimple.eigClass (fun _ : Unit => t') i ↔ t' j = t' i :=
      fun j => by
        rw [LinSemisimple.mem_eigClass]
        exact ⟨fun h => h (), fun h _ => h⟩
    have hti : t' i ≠ 1 := by
      intro h1
      apply LinSemisimple.false_of_isQuasisimple_of_commute hL'.2.2
      have hLN : L₁ ≤ N := by
        rw [hi, hN]
        rintro _ ⟨A, hA, rfl⟩
        exact ⟨_, leviEmbedSL_mem_oneBlock (fun j hj => ((hmemI j).mp hj).trans h1) hA,
          (hψBa A).symm⟩
      intro y₁ hy₁ y₂ hy₂
      have := Subgroup.commutator_mem_commutator hy₁ (hLN hy₂)
      rw [hcomm, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.mp
      (show 1 < (LinSemisimple.eigClass (fun _ : Unit => t') i).card by omega)
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin (m + 1), k₀ ∉ ({j₁, j₂} : Finset (Fin (m + 1))) := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      have h := Finset.card_le_card
        (fun k _ => hall k : (Finset.univ : Finset (Fin (m + 1))) ⊆ _)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have h2 := Finset.card_le_two (a := j₁) (b := j₂)
      omega
    have hk₀1 : k₀ ≠ j₁ := fun h => hk₀ (by simp [h])
    have hk₀2 : k₀ ≠ j₂ := fun h => hk₀ (by simp [h])
    have hsprod : ∏ k, ((rdiag j₁ j₂ ζu k : (GaloisField 2 f)ˣ) : GaloisField 2 f) = 1 := by
      rw [← Units.coe_prod, prod_rdiag hj, Units.val_one]
    have hAe : ψB (ggDiagSL (fun k => ((rdiag j₁ j₂ ζu k : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)) hsprod) = φ (diagSp _ (m + 1) (rdiag j₁ j₂ ζu)) := by
      rw [hψBa, leviEmbedSL, MonoidHom.comp_apply, toGL_ggDiagSL_eq, ← diagSp_apply]
    have heL : ψB (ggDiagSL (fun k => ((rdiag j₁ j₂ ζu k : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)) hsprod) ∈ L₁ := by
      rw [hi]
      refine ⟨_, WitSL.ggDiagSL_mem_blockSpecialLinear hsprod fun k hk => ?_, rfl⟩
      rw [rdiag_of_ne (fun h : k = j₁ => hk (h ▸ hj₁)) (fun h : k = j₂ => hk (h ▸ hj₂)),
        Units.val_one]
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe
      (s := rdiag j₁ j₂ ζu) (rdiag_pow hζup) (j₁ := j₁) (j₂ := j₂)
      (by rw [rdiag_left hj]; exact hζu1) (fun k h1 h2 => rdiag_of_ne h1 h2 ζu) hk₀1 hk₀2
    rw [← hAe] at heB he1 hL₂
    exact Or.inr ⟨_, heL, Or.inl ⟨heB, he1, Or.inr ⟨L₂, hL₂, hcard⟩⟩⟩

end Inputs

end CFSG.StandardType

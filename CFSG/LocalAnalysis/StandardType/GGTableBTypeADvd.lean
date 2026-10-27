module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvd

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Matrix

namespace TypeA

variable {d p : ℕ} {K : Type} [Field K]

theorem card_le_of_toral [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) {A₀ : GL (Fin d) K}
    (hA₀ : ∀ B : GL (Fin d) K, conjAut d K B ∈ X → ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    Nat.card X ≤ p ^ (d - 1) := by
  classical
  choose B hB using fun x : X => hXI x.2
  obtain ⟨Dm, hDm⟩ : ∃ Dm : X → GL (Fin d) K, ∀ x, Dm x = A₀ * B x * A₀⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : X → Fin d → K, ∀ x k, δ x k = (Dm x : Matrix (Fin d) (Fin d) K) k k :=
    ⟨_, fun _ _ => rfl⟩
  have hDdiag : ∀ x, (Dm x : Matrix (Fin d) (Fin d) K) = diagonal (δ x) := fun x => by
    have h1 := CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag
      (X := (Dm x : Matrix (Fin d) (Fin d) K)) fun i j hij => by
        rw [hDm x, Units.val_mul, Units.val_mul]
        exact hA₀ (B x) ((hB x).symm ▸ x.2) i j hij
    rw [h1]
    congr 1
    funext k
    exact (hδ x k).symm
  have hδ0 : ∀ x k, δ x k ≠ 0 := fun x k => diag_ne_zero (hDdiag x) k
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hpow : ∀ x k, δ x k ^ p = δ x i₀ ^ p := by
    intro x k
    have h1 : conjAut d K (B x ^ p) = 1 := by rw [map_pow, hB x]; exact hX.2 _ x.2
    obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h1
    have h2 : ((Dm x ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c := by
      have h3 : Dm x ^ p = A₀ * B x ^ p * A₀⁻¹ := by rw [hDm x, conj_pow]
      have hsc := (Matrix.scalar_commute c (fun _ => Commute.all _ _)
        (A₀ : Matrix (Fin d) (Fin d) K)).eq
      rw [h3, Units.val_mul, Units.val_mul, hc, ← hsc, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [Units.val_pow_eq_pow_val, hDdiag x, diagonal_pow, scalar_apply] at h2
    have h4 := congrFun (congrFun h2 k) k
    have h5 := congrFun (congrFun h2 i₀) i₀
    simp only [diagonal_apply_eq, Pi.pow_apply] at h4 h5
    rw [h4, h5]
  set S : Finset (Fin d) := {i₀}ᶜ with hS
  let f : X → (S → rootsOfUnity p K) := fun x k =>
    ⟨Units.mk0 (δ x k * (δ x i₀)⁻¹) (mul_ne_zero (hδ0 x k) (inv_ne_zero (hδ0 x i₀))), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, mul_pow, inv_pow, hpow x k,
        mul_inv_cancel₀ (pow_ne_zero _ (hδ0 x i₀)), Units.val_one]⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hrat : ∀ k, δ y k = (δ y i₀ * (δ x i₀)⁻¹) * δ x k := by
      intro k
      have hy0 := hδ0 y i₀
      have hx0 := hδ0 x i₀
      by_cases hk : k = i₀
      · rw [hk, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
      · have h1 := congrArg (fun g : S → rootsOfUnity p K =>
          (((g ⟨k, by simp [hS, hk]⟩ : rootsOfUnity p K) : Kˣ) : K)) hxy
        simp only [f, Units.val_mk0] at h1
        calc δ y k = δ y k * (δ y i₀)⁻¹ * δ y i₀ := by field_simp
          _ = δ x k * (δ x i₀)⁻¹ * δ y i₀ := by rw [h1]
          _ = δ y i₀ * (δ x i₀)⁻¹ * δ x k := by ring
    set c : Kˣ := Units.mk0 (δ y i₀ * (δ x i₀)⁻¹)
      (mul_ne_zero (hδ0 y i₀) (inv_ne_zero (hδ0 x i₀))) with hc
    have hDy' : (Dm y : Matrix (Fin d) (Fin d) K) =
        scalar (Fin d) (c : K) * (Dm x : Matrix (Fin d) (Fin d) K) := by
      rw [hDdiag x, hDdiag y, scalar_apply, diagonal_mul_diagonal]
      congr 1
      funext k
      exact hrat k
    have hDy : Dm y = Matrix.GeneralLinearGroup.scalar (Fin d) c * Dm x :=
      Units.ext (hDy'.trans (by
        rw [← Matrix.GeneralLinearGroup.coe_scalar]
        exact (Units.val_mul _ _).symm))
    have hBy : B y = Matrix.GeneralLinearGroup.scalar (Fin d) c * B x := by
      have h1 : B y = A₀⁻¹ * Dm y * A₀ := by rw [hDm y]; group
      have h2 : B x = A₀⁻¹ * Dm x * A₀ := by rw [hDm x]; group
      rw [h1, hDy, h2]
      have hcomm := (commute_scalar_GL c A₀⁻¹).eq
      calc A₀⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) c * Dm x) * A₀ =
          (A₀⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin d) c) * Dm x * A₀ := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c * A₀⁻¹) * Dm x * A₀ := by rw [hcomm]
        _ = _ := by group
    apply Subtype.ext
    rw [← hB x, ← hB y, hBy, map_mul, conjAut_scalar, one_mul]
  have hcard : Nat.card (S → rootsOfUnity p K) = p ^ (d - 1) := by
    rw [Nat.card_fun, card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_fintype_card, Fintype.card_coe,
      hS, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  exact hcard ▸ Nat.card_le_card_of_injective f hinj


theorem card_lt_of_torality [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (htor : GGPGLTorality p d K) {X : Subgroup (MulAut (projectiveSL d K))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X < p ^ 3 := by
  by_contra h
  push Not at h
  have h1 : p ^ (d - 2) ≤ Nat.card X :=
    (Nat.pow_le_pow_right hp.pos (by omega)).trans h
  obtain ⟨A₀, hA₀⟩ := htor X hX hXI h1 h
  have h2 := card_le_of_toral hp hpK hd hX hXI hA₀
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h.trans h2)
  omega

theorem ggBstarBound_small_of_torality [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hd3 : d ≤ 3) (htor : GGPGLTorality p d K) :
    GGBstarBound p 0 (projectiveSL d K) (Set.range (conjAut d K)) :=
  ggBstarBound_of_card_lt fun _ hXI hX => card_lt_of_torality hp hpK hd hd3 htor hX hXI

theorem ggEndNode_small_of_torality [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hd3 : d ≤ 3) (htor : GGPGLTorality p d K) :
    GGEndNode p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
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
  have := card_lt_of_torality hp hpK hd hd3 htor hX hXI
  rw [hcard] at this
  omega

end TypeA

@[expose] def GGPGLToralityInput : Prop :=
  ∀ (p d : ℕ) (K : Type) [Field K] [Finite K], p.Prime → p ≠ 2 → p ∣ Nat.card K - 1 → p ∣ d →
    TypeA.GGPGLTorality p d K

theorem recipeLinear_tableB_dvd (htor : GGPGLToralityInput) {d N p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
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
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hd3 : 3 ≤ d := (hp3.trans (Nat.le_of_dvd (by omega) hpd))
  have htor' := htor p d K hp hp2 hpK hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4' | h5
  · subst h3
    exact ⟨0, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num))),
      TypeA.ggBstarBound_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
        (TypeA.ggBstarBound_small_of_torality hp hpK (by norm_num) le_rfl htor'),
      TypeA.ggEndNode_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
        (TypeA.ggEndNode_small_of_torality hp hpK (by norm_num) le_rfl htor')⟩
  · subst h4'
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have hsec : TypeA.SLHasSections d K := TypeA.slHasSections_of_five_le h5
    exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK hd hsec),
      TypeA.ggBstarBound_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (TypeA.ggBstarBound_of_torality hp hp2 hd3 htor'),
      TypeA.ggEndNode_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (TypeA.ggEndNode_of_torality hp hp2 hpK h5 h4 hsec htor')⟩

@[expose] def GGTypeALabelDvd (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1

theorem largeEvenLabelAll_typeA_dvd (htor : GGPGLToralityInput) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabelDvd p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨h, hpn, hpl⟩ := h
  dsimp only at h hpn hpl
  subst h
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  exact recipeLinear_tableB_dvd htor hp hpn ⟨n, rfl⟩ (by omega) hpl hQ

theorem ggBstarInputOn_typeA_dvd (htor : GGPGLToralityInput) : GGBstarInputOn GGTypeALabelDvd :=
  ggBstarInputOn_of_labels (fun _ _ h => Or.inl h.1) fun _ _ hp hlab h =>
    (largeEvenLabelAll_typeA_dvd htor hp hlab h).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_typeA_dvd (htor : GGPGLToralityInput) :
    GGStdSubPreInputOn GGTypeALabelDvd :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_typeA_dvd htor hp hlab h).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

@[expose] def GGTypeASplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTypeALabel p lab ∨ GGTypeALabelDvd p lab

theorem ggBstarInputOn_typeA_split (htor : GGPGLToralityInput) :
    GGBstarInputOn GGTypeASplitLabel :=
  ggBstarInputOn_of_labels (fun _ _ h => h.elim GGTypeALabel.pilot fun h' => Or.inl h'.1)
    fun _ _ hp hlab h => h.elim
      (fun h' => (largeEvenLabelAll_typeA hp hlab h').mono fun _ _ _ _ ⟨r, h1, h2, _⟩ =>
        ⟨r, h1, h2⟩)
      (fun h' => (largeEvenLabelAll_typeA_dvd htor hp hlab h').mono fun _ _ _ _ ⟨r, h1, h2, _⟩ =>
        ⟨r, h1, h2⟩)

theorem ggStdSubPreInputOn_typeA_split (htor : GGPGLToralityInput) :
    GGStdSubPreInputOn GGTypeASplitLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h => h.elim
    (fun h' => (largeEvenLabelAll_typeA hp hlab h').mono fun _ _ _ _ ⟨r, h1, _, h3⟩ =>
      ⟨r, h1, h3⟩)
    (fun h' => (largeEvenLabelAll_typeA_dvd htor hp hlab h').mono fun _ _ _ _ ⟨r, h1, _, h3⟩ =>
      ⟨r, h1, h3⟩)

end CFSG.StandardType

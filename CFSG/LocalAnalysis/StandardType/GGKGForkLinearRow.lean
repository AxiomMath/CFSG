module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly UCoord

theorem ggTorusLattice_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusLattice p r R' I') : GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  refine h L' (e.toMonoidHom.comp ψ) A ⟨e.surjective.comp hψ, ?_, hperf, hAe, ?_, hr, h3, hsc⟩
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane

private noncomputable def ggKGTa_diagSL {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    SpecialLinearGroup (Fin d) K :=
  ⟨diagonal (fun k => ((UModel.uvec hu f k : Kˣ) : K)), by
    rw [Matrix.det_diagonal]
    have h1 : (∏ k, ((UModel.uvec hu f k : Kˣ) : K)) =
        ((∏ k, UModel.uvec hu f k : Kˣ) : K) := by simp
    rw [h1, UModel.prod_uvec hu hord f, Units.val_one]⟩

private theorem ggKGTa_diagSL_matrix {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    ((ggKGTa_diagSL u hu hord f : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => ((UModel.uvec hu f k : Kˣ) : K)) :=
  rfl

private theorem ggKGTa_diagSL_one {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) :
    ggKGTa_diagSL u hu hord (1 : ↥(sumZero d p)) = 1 := by
  apply Subtype.ext
  rw [ggKGTa_diagSL_matrix, Matrix.SpecialLinearGroup.coe_one]
  have h1 : (fun k => ((UModel.uvec hu (1 : ↥(sumZero d p)) k : Kˣ) : K)) =
      fun _ => (1 : K) := by
    funext k
    rw [map_one, Pi.one_apply, Units.val_one]
  rw [h1, diagonal_one]

private theorem ggKGTa_diagSL_mul {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) (f g : ↥(sumZero d p)) :
    ggKGTa_diagSL u hu hord (f * g) =
      ggKGTa_diagSL u hu hord f * ggKGTa_diagSL u hu hord g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ggKGTa_diagSL_matrix, ggKGTa_diagSL_matrix,
    ggKGTa_diagSL_matrix, map_mul, Matrix.diagonal_mul_diagonal]
  congr 1

private theorem ggKGTa_diagSL_pow {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    ggKGTa_diagSL u hu hord f ^ p = 1 := by
  refine TypeA.pow_eq_one_of_pow_diagonal (D := ggKGTa_diagSL u hu hord f) rfl (fun k => ?_)
  show (((UModel.uvec hu f k : Kˣ) : K)) ^ p = 1
  simpa using congrArg (fun x : Kˣ => (x : K)) (UModel.uvec_pow_eq_one hu f k)

private theorem ggKGTa_diagSL_mem {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} (hM : IsDiagTorusModel p φ A) (u : Kˣ) (hu : u ^ p = 1)
    (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    MulAut.conj (φ (ggKGTa_diagSL u hu hord f)) ∈ A :=
  (hM _).mpr ⟨ggKGTa_diagSL u hu hord f,
    ⟨fun k => ((UModel.uvec hu f k : Kˣ) : K), ggKGTa_diagSL_matrix u hu hord f⟩,
    ggKGTa_diagSL_pow u hu hord f, rfl⟩

private theorem ggKGTa_diagSL_perm {d p : ℕ} {K : Type} [Field K] [CharP K 2] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (hord : orderOf u = p) (σ : Equiv.Perm (Fin d))
    (f : ↥(sumZero d p)) :
    permSL σ⁻¹ * ggKGTa_diagSL u hu hord f * (permSL σ⁻¹)⁻¹ =
      ggKGTa_diagSL u hu hord (permAutV σ f) := by
  apply Subtype.ext
  rw [TypeA.coe_permSL_conj (D := ggKGTa_diagSL u hu hord f)
    (t := fun k => ((UModel.uvec hu f k : Kˣ) : K)) (ggKGTa_diagSL_matrix u hu hord f) (σ⁻¹),
    ggKGTa_diagSL_matrix, UModel.uvec_permAutV]
  rfl

theorem ggKGTA_permModel {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) {L' : Type} [Group L']
    [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hr : p ^ (d - 1) ≤ Nat.card A) (hsc : GGTorusSelfCent p A)
    (hM : IsDiagTorusModel p φ A) :
    ∃ Θ : ↥(sumZero d p) ≃* ↥A, ∀ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ∃ π : Equiv.Perm (Fin d), ggConjAut A hn = MulAut.congr Θ (permAutV π) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  let u : Kˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hu : u ^ p = 1 := by
    ext
    simp only [u, Units.val_pow_eq_pow_val, Units.val_one, Units.mk0_val]
    exact hζ.pow_eq_one
  have hord : orderOf u = p := by
    have hζu : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp hζ
    exact hζu.eq_orderOf.symm
  let Θ₀ : ↥(sumZero d p) →* ↥A :=
    { toFun := fun f => ⟨MulAut.conj (φ (ggKGTa_diagSL u hu hord f)),
        ggKGTa_diagSL_mem hM u hu hord f⟩
      map_one' := by
        apply Subtype.ext
        show MulAut.conj (φ (ggKGTa_diagSL u hu hord 1)) = (1 : MulAut L')
        rw [ggKGTa_diagSL_one, map_one, map_one]
      map_mul' := fun f g => by
        apply Subtype.ext
        show MulAut.conj (φ (ggKGTa_diagSL u hu hord (f * g))) =
          MulAut.conj (φ (ggKGTa_diagSL u hu hord f)) *
            MulAut.conj (φ (ggKGTa_diagSL u hu hord g))
        rw [ggKGTa_diagSL_mul, map_mul, map_mul] }
  have hΘ₀val : ∀ f, ((Θ₀ f : ↥A) : MulAut L') =
      MulAut.conj (φ (ggKGTa_diagSL u hu hord f)) := fun _ => rfl
  have hsurj : Function.Surjective Θ₀ := by
    rintro ⟨a, ha⟩
    obtain ⟨D, ⟨t, hD⟩, hDp, rfl⟩ := (hM a).mp ha
    have ht : ∀ k, t k ^ p = 1 := fun k => pow_eq_one_of_diagonal hD hDp k
    have ht0 : ∀ k, t k ≠ 0 := fun k => diag_entry_ne_zero hD k
    let t' : Fin d → Kˣ := fun k => Units.mk0 (t k) (ht0 k)
    have ht'p : ∀ k, t' k ^ p = 1 := by
      intro k
      ext
      simp only [t', Units.val_pow_eq_pow_val, Units.val_one, Units.mk0_val]
      exact ht k
    have hprodt' : ∏ k, t' k = 1 := by
      apply Units.ext
      have h1 : ((∏ k, t' k : Kˣ) : K) = ∏ k, ((t' k : Kˣ) : K) := by simp
      rw [h1]
      have h2 : ∀ k, ((t' k : Kˣ) : K) = t k := fun k => rfl
      simp only [h2]
      exact prod_eq_one_of_diagonal hD
    obtain ⟨f, hf⟩ := UModel.exists_uvec_eq hu hord ht'p hprodt'
    refine ⟨f, Subtype.ext ?_⟩
    have hDeq : ggKGTa_diagSL u hu hord f = D := by
      apply Subtype.ext
      rw [ggKGTa_diagSL_matrix, hD]
      congr 1
      funext k
      rw [hf]
      rfl
    rw [hΘ₀val, hDeq]
  have hcard : Nat.card ↥(sumZero d p) ≤ Nat.card ↥A := by
    have hdm : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    calc Nat.card ↥(sumZero d p) = Nat.card ↥(sumZero (d - 1 + 1) p) := by rw [hdm]
      _ ≤ p ^ (d - 1) := UCoord.card_sumZero_le (d - 1) p
      _ ≤ Nat.card ↥A := hr
  have hbij : Function.Bijective Θ₀ := hsurj.bijective_of_nat_card_le hcard
  let Θ : ↥(sumZero d p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hbij
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') =
      MulAut.conj (φ (ggKGTa_diagSL u hu hord f)) := fun _ => rfl
  refine ⟨Θ, ?_⟩
  intro n hn
  obtain ⟨s, rfl⟩ := hφs n
  have hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ a t := by
    intro a ha
    obtain ⟨D, ⟨t, hD⟩, -, rfl⟩ := (hM a).mp ha
    exact ⟨t, TypeANbrDvd.actsDiag_conj hD⟩
  obtain ⟨σ, hσ⟩ := TypeANbrDvd.exists_perm_of_conj_mem_normalizer hp hp2 hpK hφs hφker
    hA hsc hdiag hn
  have hN : ∀ τ, NbrInnerWeylA.permConj φ τ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun τ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφs hφker hA.2 hsc hdiag τ
  refine ⟨σ, ?_⟩
  have hgg : ggConjAut A hn = ggConjAut A (hN σ) := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, ggConjAut_apply, hσ b b.2]
  rw [hgg, ← TypeANbrDvd.permAut_apply]
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨f, rfl⟩ := Θ.surjective b
  rw [TypeANbrDvd.permAut_apply, ggConjAut_apply, hΘval]
  rw [show ((MulAut.congr Θ (permAutV σ) (Θ f) : ↥A) : MulAut L') =
      MulAut.conj (φ (ggKGTa_diagSL u hu hord (permAutV σ f))) from by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    exact hΘval (permAutV σ f)]
  change MulAut.conj (φ (permSL σ⁻¹)) * MulAut.conj (φ (ggKGTa_diagSL u hu hord f)) *
      (MulAut.conj (φ (permSL σ⁻¹)))⁻¹ =
    MulAut.conj (φ (ggKGTa_diagSL u hu hord (permAutV σ f)))
  rw [← map_inv (MulAut.conj), ← map_mul (MulAut.conj), ← map_mul (MulAut.conj),
    ← map_inv (φ), ← map_mul (φ), ← map_mul (φ), ggKGTa_diagSL_perm]

theorem ggTorusLattice_psl_coprime {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusLattice p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨φ, hφs, hφker, hM⟩ :=
    exists_isDiagTorusModel hp hpK hd hpd hsec hψ hker hperf hAe hAI hr
  obtain ⟨Θ, hS⟩ := ggKGTA_permModel hp hp2 hpK hd hφs hφker hAe hr hsc hM
  exact ggTorusLattice_of_permModel hp hp2 ((Nat.Prime.coprime_iff_not_dvd hp).mp hpd) h3 Θ hS

theorem ggTorusLattice_psl_small {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusLattice p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, -⟩ := hA
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

theorem recipeLinear_lattice {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
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
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggTorusLattice_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusLattice_psl_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggTorusLattice_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusLattice_psl_coprime hp hp2 hpK hd4 hpd' hsec)⟩

end TypeA

theorem ggKGTwoOn_typeA : GGKGTwoOn fun p lab => GGTypeALabel p lab := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨h, hpn, hpl⟩ | ⟨h, hl3, hpn⟩ | ⟨h, hl2, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact TypeA.recipeLinear_lattice hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl3 hpn
    subst h hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine TypeA.recipeLinear_lattice hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl2 hpn
    subst h hl2
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine TypeA.recipeLinear_lattice hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end CFSG.StandardType

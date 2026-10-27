module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeTor
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType.L3Three

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.StandardType.TypeA.PGLTor TauCeti CFSG.ComponentClassification

variable {K : Type} [Field K]

theorem exists_diagGL_of_offDiag {A x : GL (Fin 3) K}
    (h : ∀ i j, i ≠ j → ((A : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j = 0) :
    ∃ δ : Fin 3 → Kˣ, A * x * A⁻¹ = diagGL δ := by
  have hd : conjMatrix A x = diagonal fun i => conjMatrix A x i i :=
    eq_diagonal_of_offDiag_eq_zero h
  have h0 : ∀ i, conjMatrix A x i i ≠ 0 := fun i =>
    diag_ne_zero_of_eq_diagonal (D := A * x * A⁻¹) (δ := fun i => conjMatrix A x i i)
      (by rw [Units.val_mul, Units.val_mul]; exact hd) i
  refine ⟨fun i => Units.mk0 _ (h0 i), Units.ext ?_⟩
  rw [diagGL_coe, Units.val_mul, Units.val_mul]
  simp only [Units.val_mk0]
  exact hd

theorem det_permutationGL [CharP K 2] (σ : Equiv.Perm (Fin 3)) :
    ((permutationGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [permutationGL_coe, det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

@[expose] def weylGL (A₀ : GL (Fin 3) K) (σ : Equiv.Perm (Fin 3)) : GL (Fin 3) K :=
  A₀⁻¹ * permutationGL σ * A₀

@[expose] def weylSL [CharP K 2] (A₀ : GL (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨(weylGL A₀ σ : Matrix (Fin 3) (Fin 3) K), by
    rw [weylGL, Units.val_mul, Units.val_mul, det_mul, det_mul, det_permutationGL, mul_one,
      ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]⟩

theorem toGL_weylSL [CharP K 2] (A₀ : GL (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    SpecialLinearGroup.toGL (weylSL A₀ σ) = weylGL A₀ σ :=
  Units.ext rfl

theorem conj_weylGL_mul {A₀ B : GL (Fin 3) K} {δ : Fin 3 → Kˣ} (hB : A₀ * B * A₀⁻¹ = diagGL δ)
    (σ : Equiv.Perm (Fin 3)) (k : ℤ) :
    A₀ * (weylGL A₀ σ * B * (weylGL A₀ σ)⁻¹ * (B ^ k)⁻¹) * A₀⁻¹ =
      diagGL fun i => δ (σ⁻¹ i) * (δ i ^ k)⁻¹ := by
  have hBk : A₀ * B ^ k * A₀⁻¹ = diagGL δ ^ k := by rw [← hB, conj_zpow]
  calc A₀ * (weylGL A₀ σ * B * (weylGL A₀ σ)⁻¹ * (B ^ k)⁻¹) * A₀⁻¹
      = (permutationGL σ * (A₀ * B * A₀⁻¹) * (permutationGL σ)⁻¹) * (A₀ * B ^ k * A₀⁻¹)⁻¹ := by
        rw [weylGL]
        group
    _ = diagGL (fun i => δ (σ⁻¹ i)) * (diagGL δ ^ k)⁻¹ := by
        rw [hB, hBk, permutationGL_mul_diagGL_mul_inv]
    _ = diagGL fun i => δ (σ⁻¹ i) * (δ i ^ k)⁻¹ := by
        rw [← map_zpow, ← map_inv, ← map_mul]
        rfl

theorem exists_perm_conjAut_ne [Finite K] {A₀ B : GL (Fin 3) K} {δ : Fin 3 → Kˣ}
    (hB : A₀ * B * A₀⁻¹ = diagGL δ) (hinj : ¬ Function.Injective δ) (hconst : ∃ i j, δ i ≠ δ j) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : ℤ,
      conjAut 3 K (weylGL A₀ σ * B * (weylGL A₀ σ)⁻¹) ≠ conjAut 3 K (B ^ k) := by
  obtain ⟨i₀, hi₀⟩ := exists_simple_entry hinj hconst
  obtain ⟨x, y, hxy, hxy'⟩ : ∃ x y, δ x = δ y ∧ x ≠ y := by
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨x, y, h, hne⟩ := hinj
    exact ⟨x, y, h, hne⟩
  have hx : x ≠ i₀ := by
    rintro rfl
    exact hi₀ y (Ne.symm hxy') hxy.symm
  have hy : y ≠ i₀ := by
    rintro rfl
    exact hi₀ x hxy' hxy
  refine ⟨Equiv.swap i₀ x, fun k hk => ?_⟩
  have h1 : conjAut 3 K (weylGL A₀ (Equiv.swap i₀ x) * B * (weylGL A₀ (Equiv.swap i₀ x))⁻¹ *
      (B ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, hk, mul_inv_cancel]
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
  have h2 := conj_weylGL_mul hB (Equiv.swap i₀ x) k
  have h3 : ((diagGL fun i => δ ((Equiv.swap i₀ x)⁻¹ i) * (δ i ^ k)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c := by
    rw [← h2, Units.val_mul, Units.val_mul, hc,
      ← (scalar_commute c (fun _ => Commute.all _ _) _).eq, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have hx' := congrFun (congrFun h3 x) x
  have hy' := congrFun (congrFun h3 y) y
  rw [diagGL_coe, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at hx' hy'
  rw [Equiv.swap_inv, Equiv.swap_apply_right] at hx'
  rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hy hxy'.symm] at hy'
  apply hi₀ x hx
  have h4 : δ i₀ * (δ x ^ k)⁻¹ = δ y * (δ y ^ k)⁻¹ := Units.ext (hx'.trans hy'.symm)
  rw [← hxy] at h4
  exact (mul_right_cancel h4).symm

theorem ggTorusNoLineTwoKX_projectiveSL_of_lift [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {Kp : ℕ → Prop}
    (hlift : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* projectiveSL 3 K),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Kp (Nat.card ψ.ker) →
          ∃ φ : SpecialLinearGroup (Fin 3) K →* L', ∀ g, ψ (φ g) = proj 3 K g) :
    GGTorusNoLineTwoKX 3 Kp (projectiveSL 3 K) (Set.range (conjAut 3 K))
      (conjAut 3 K '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) K)}) := by
  classical
  intro L' _ _ ψ hψ hker hperf hKp A hA hAI _ _
  obtain ⟨φ, hφ⟩ := hlift L' ψ hψ hker hperf hKp
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ', -, h⟩ := hAI a ha
    exact ⟨φ', h⟩)
  have hIndI : ∀ a : A, ∃ B : GL (Fin 3) K, conjAut 3 K B = Ind a := by
    intro a
    obtain ⟨φ', hφ', h⟩ := hAI a a.2
    rw [ggInduced_unique hψ (hInd a) h]
    exact hφ'
  choose B hB using hIndI
  have hinj : Function.Injective Ind := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (ggAut_eq_one_of_induced_one ψ hker hperf a fun l => ?_)
    rw [← hInd a l, ha, MulAut.one_apply]
  have hX : IsElemAbelian 3 Ind.range := ggIsElemAbelian_range le_rfl hA Ind
  set G := Ind.range.comap (conjAut 3 K) with hG
  have hGp : IsProjElem 3 G := TypeA.isProjElem_comap (by norm_num) hX
  have hBG : ∀ a, B a ∈ G := fun a => by
    change conjAut 3 K (B a) ∈ Ind.range
    rw [hB a]
    exact ⟨a, rfl⟩
  have hperfSL : commutator (SpecialLinearGroup (Fin 3) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl).commutator_eq_top
  have hS3 : ∀ (a : A) (g : SpecialLinearGroup (Fin 3) K),
      (a : MulAut L') (φ g) = φ (CatalogueBHigherLinearAction.slConjugation 3 K (B a) g) := by
    intro a
    have h := TypeA.eq_of_inv_mul_mem_center hperfSL ((a : MulAut L').toMonoidHom.comp φ)
      (φ.comp (CatalogueBHigherLinearAction.slConjugation 3 K (B a)).toMonoidHom)
      (fun s => hker ?_)
    · intro g
      exact DFunLike.congr_fun h g
    · rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← hInd a, hφ, hφ, ← hB a, conjAut_proj, inv_mul_cancel]
  have hBns : ∀ a : A, a ≠ 1 → ∀ c : Kˣ, B a ≠ GeneralLinearGroup.scalar (Fin 3) c := by
    intro a ha c hc
    apply ha
    apply hinj
    rw [map_one, ← hB a, hc, conjAut_scalar]
  rcases toral_or_isReg h3 hGp with ⟨A₀, hA₀⟩ | hreg
  ·
    choose δ hδ using fun a : A => exists_diagGL_of_offDiag (hA₀ (B a) (hBG a))
    have hcube : ∀ (a : A) (i j : Fin 3), δ a i ^ 3 = δ a j ^ 3 := by
      intro a i j
      obtain ⟨u, hu⟩ := hGp.pow_scalar (B a) (hBG a)
      have h1 : diagGL (δ a ^ 3) = diagGL (fun _ : Fin 3 => u) := by
        rw [map_pow, ← hδ a, conj_pow, hu, ← scalar_mul_comm u A₀, mul_inv_cancel_right,
          diagGL_const]
      have h2 := diagGL_injective h1
      exact (congrFun h2 i).trans (congrFun h2 j).symm
    refine ⟨{n | ∃ σ : Equiv.Perm (Fin 3), n = φ (weylSL A₀ σ)}, ?_, ?_⟩
    ·
      rintro n ⟨σ, rfl⟩ a ha
      set E : SpecialLinearGroup (Fin 3) K := weylSL A₀ σ *
        (CatalogueBHigherLinearAction.slConjugation 3 K (B ⟨a, ha⟩) (weylSL A₀ σ))⁻¹ with hE
      have hn : φ (weylSL A₀ σ) * (a (φ (weylSL A₀ σ)))⁻¹ = φ E := by
        rw [show a = ((⟨a, ha⟩ : A) : MulAut L') from rfl, hS3 ⟨a, ha⟩, hE, map_mul, map_inv]
      have hEgl : A₀ * SpecialLinearGroup.toGL E * A₀⁻¹ =
          diagGL fun i => δ ⟨a, ha⟩ (σ⁻¹ i) * (δ ⟨a, ha⟩ i ^ (1 : ℤ))⁻¹ := by
        rw [← conj_weylGL_mul (hδ ⟨a, ha⟩) σ 1, hE, map_mul, map_inv,
          CatalogueBHigherLinearAction.toGL_slConjugation, toGL_weylSL, zpow_one]
        group
      rw [hn]
      refine ⟨?_, fun a' ha' => ?_⟩
      · have h1 : A₀ * SpecialLinearGroup.toGL (E ^ 3) * A₀⁻¹ = 1 := by
          rw [map_pow, ← conj_pow, hEgl, ← map_pow]
          have h5 : (fun i => δ ⟨a, ha⟩ (σ⁻¹ i) * (δ ⟨a, ha⟩ i ^ (1 : ℤ))⁻¹) ^ 3 = 1 := by
            funext i
            simp only [Pi.pow_apply, Pi.one_apply, zpow_one, mul_pow, inv_pow]
            rw [hcube ⟨a, ha⟩ (σ⁻¹ i) i, mul_inv_cancel]
          rw [h5, map_one]
        have h2 : SpecialLinearGroup.toGL (E ^ 3) = 1 :=
          calc SpecialLinearGroup.toGL (E ^ 3)
              = A₀⁻¹ * (A₀ * SpecialLinearGroup.toGL (E ^ 3) * A₀⁻¹) * A₀ := by group
            _ = 1 := by rw [h1]; group
        have hE3 : E ^ 3 = 1 := SpecialLinearGroup.toGL_injective (by rw [h2, map_one])
        rw [← map_pow, hE3, map_one]
      · rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hS3 ⟨a', ha'⟩]
        congr 1
        apply SpecialLinearGroup.toGL_injective
        rw [CatalogueBHigherLinearAction.toGL_slConjugation]
        have h1 : A₀ * (B ⟨a', ha'⟩ * SpecialLinearGroup.toGL E * (B ⟨a', ha'⟩)⁻¹) * A₀⁻¹ =
            A₀ * SpecialLinearGroup.toGL E * A₀⁻¹ := by
          have e : A₀ * (B ⟨a', ha'⟩ * SpecialLinearGroup.toGL E * (B ⟨a', ha'⟩)⁻¹) * A₀⁻¹ =
              (A₀ * B ⟨a', ha'⟩ * A₀⁻¹) * (A₀ * SpecialLinearGroup.toGL E * A₀⁻¹) *
                (A₀ * B ⟨a', ha'⟩ * A₀⁻¹)⁻¹ := by group
          rw [e, hδ ⟨a', ha'⟩, hEgl, ← map_inv, ← map_mul, ← map_mul, mul_inv_cancel_comm]
        exact mul_left_cancel (mul_right_cancel h1)
    ·
      intro _ a₀ ha₀ hne
      have hne' : (⟨a₀, ha₀⟩ : A) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      by_cases hδinj : Function.Injective (δ ⟨a₀, ha₀⟩)
      · left
        refine ⟨Ind ⟨a₀, ha₀⟩, ⟨B ⟨a₀, ha₀⟩, ?_, hB _⟩, hInd ⟨a₀, ha₀⟩⟩
        refine isReg_of_conjMatrix_eq_diagonal (A := A₀)
          (r := fun i => ((δ ⟨a₀, ha₀⟩ i : Kˣ) : K)) ?_ fun i j hij => hδinj (Units.ext hij)
        have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) (hδ ⟨a₀, ha₀⟩)
        simp only [Units.val_mul, diagGL_coe] at h1
        exact h1
      · right
        have hconst : ∃ i j, δ ⟨a₀, ha₀⟩ i ≠ δ ⟨a₀, ha₀⟩ j := by
          by_contra hc
          push Not at hc
          apply hBns _ hne' (δ ⟨a₀, ha₀⟩ 0)
          have h1 : δ ⟨a₀, ha₀⟩ = fun _ => δ ⟨a₀, ha₀⟩ 0 := funext fun i => hc i 0
          have h2 : A₀ * B ⟨a₀, ha₀⟩ * A₀⁻¹ =
              GeneralLinearGroup.scalar (Fin 3) (δ ⟨a₀, ha₀⟩ 0) := by
            rw [hδ, h1, diagGL_const]
          calc B ⟨a₀, ha₀⟩ = A₀⁻¹ * (A₀ * B ⟨a₀, ha₀⟩ * A₀⁻¹) * A₀ := by group
            _ = _ := by
              rw [h2, ← scalar_mul_comm (δ ⟨a₀, ha₀⟩ 0) A₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
        obtain ⟨σ, hσ⟩ := exists_perm_conjAut_ne (hδ ⟨a₀, ha₀⟩) hδinj hconst
        refine ⟨φ (weylSL A₀ σ), ⟨σ, rfl⟩, fun hmem => ?_⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        apply hσ k
        have e1 : ∀ l, (Ind ⟨a₀, ha₀⟩ ^ k) (ψ l) = ψ ((a₀ ^ k) l) := by
          intro l
          rw [← map_zpow, hInd]
          rfl
        have e2 := ggInduced_conj_mul_conj_inv ψ (φ (weylSL A₀ σ)) (hInd ⟨a₀, ha₀⟩)
        rw [← hk] at e2
        have e3 := ggInduced_unique hψ e2 e1
        rw [hφ, ← conjAut_toGL, toGL_weylSL, ← hB ⟨a₀, ha₀⟩] at e3
        rw [map_mul, map_mul, map_inv, map_zpow]
        exact e3
  ·
    refine ⟨∅, fun n hn => absurd hn (Set.notMem_empty n), fun _ a₀ ha₀ hne => Or.inl ?_⟩
    have hne' : (⟨a₀, ha₀⟩ : A) ≠ 1 := fun h => hne (congrArg Subtype.val h)
    exact ⟨Ind ⟨a₀, ha₀⟩, ⟨B ⟨a₀, ha₀⟩, hreg _ (hBG _) (hBns _ hne'), hB _⟩, hInd ⟨a₀, ha₀⟩⟩

theorem ggTorusNoLineTwoKX_projectiveSL [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    (h2 : Nat.card K ≠ 2) (h4 : Nat.card K ≠ 4) (Kp : ℕ → Prop) :
    GGTorusNoLineTwoKX 3 Kp (projectiveSL 3 K) (Set.range (conjAut 3 K))
      (conjAut 3 K '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) K)}) := by
  refine ggTorusNoLineTwoKX_projectiveSL_of_lift h3 fun L' _ _ ψ hψ hker hperf _ => ?_
  have hsec : TypeA.SLHasSections 3 K :=
    TypeA.slHasSections_of_card le_rfl h2 (fun h => h4 h.2) (fun h => absurd h.1 (by norm_num))
  obtain ⟨φ, -, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  exact ⟨φ, hφ⟩

end CFSG.StandardType.L3Three

end

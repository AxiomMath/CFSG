module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofFlag
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofPar
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)

section L3

variable {K : Type} [Field K]

theorem exists_stabilizer_of_parabolic [Finite K] [CharP K 2] {P : Subgroup (projectiveSL 3 K)}
    (hP : IsProperParabolic P) :
    ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ s : SpecialLinearGroup (Fin 3) K,
      proj 3 K s ∈ P → ∀ v ∈ W, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
  obtain ⟨hPtop, T, hT⟩ := isProperParabolic_comap (proj 3 K) (proj_surjective 3 K) hP
  obtain ⟨W, hW0, hWtop, hW⟩ :=
    Step1917EqProof.exists_uniform_invariant_of_normalizes_parabolic hPtop hT
  refine ⟨W, hW0, hWtop, fun s hs v hv => ?_⟩
  have h1 := hW (SpecialLinearGroup.toGL s) (fun t ht => by
    rw [Step1911EndProof.glConj_toGL]
    exact (P.comap (proj 3 K)).mul_mem ((P.comap (proj 3 K)).mul_mem hs ht)
      ((P.comap (proj 3 K)).inv_mem hs)) v hv
  exact h1

theorem range_subfieldProj_not_le [Finite K] [CharP K 2] (σ : K ≃+* K)
    {P : Subgroup (projectiveSL 3 K)} (hP : IsProperParabolic P) :
    ¬ (subfieldProj σ).range ≤ P := by
  intro hle
  obtain ⟨W, hW0, hWtop, hW⟩ := exists_stabilizer_of_parabolic hP
  have hall : ∀ a b : Fin 3, a ≠ b → ∀ v ∈ W, transvection a b (1 : K) *ᵥ v ∈ W := by
    intro a b hab v hv
    have hmem : proj 3 K (SpecialLinearGroup.map (fixedField σ).subtype
        (SpecialLinearGroup.transvection hab (1 : fixedField σ))) ∈ P :=
      hle ⟨_, subfieldProj_proj σ _⟩
    have h1 := hW _ hmem v hv
    rwa [slMap_transvection_one σ hab] at h1
  rcases eq_bot_or_eq_top_of_transvection hall with h | h
  · exact hW0 h
  · exact hWtop h

theorem fieldAut_subfieldProj (σ : K ≃+* K) (x : projectiveSL 3 (fixedField σ)) :
    fieldAut 3 K σ (subfieldProj σ x) = subfieldProj σ x := by
  obtain ⟨A, rfl⟩ := proj_surjective 3 _ x
  rw [subfieldProj_proj, fieldAut_proj]
  congr 1
  ext i j
  exact CFSG.GH74.GLS.IVK.fixedField_apply σ _

theorem card_le_nine_of_le_linearAutGroup [Finite K] (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : E ≤ linearAutGroup 3 K)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 9 := by
  set Z := CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K with hZ
  have hZle : Z ≤ (conjAut 3 K).ker := by
    rintro _ ⟨u, rfl⟩
    exact conjAut_scalar u
  set ι : GL (Fin 3) K ⧸ Z →* MulAut (projectiveSL 3 K) := QuotientGroup.lift Z (conjAut 3 K) hZle
    with hι
  have hιmk : ∀ A : GL (Fin 3) K, ι (A : GL (Fin 3) K ⧸ Z) = conjAut 3 K A := fun A => rfl
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hιmk] at hx
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl A 1
      (by rw [map_one, mul_one]; exact hx)
    rw [QuotientGroup.eq_one_iff]
    exact ⟨u, hu⟩
  have hrange : E ≤ ι.range := by
    intro x hx
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (hE hx)
    exact ⟨A, by rw [hιmk, hA]⟩
  set E' : Subgroup (GL (Fin 3) K ⧸ Z) := E.comap ι with hE'
  have hcard : Nat.card E' = Nat.card E := by
    have hmap : E'.map ι = E := Subgroup.map_comap_eq_self hrange
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  rw [← hcard]
  refine Sec4.card_le_nine_of_comm h3 hτ hτ1 E' (fun x hx y hy => hinj ?_) (fun x hx => hinj ?_)
  · rw [map_mul, map_mul]
    exact hcomm _ hx _ hy
  · rw [map_pow, map_one]
    exact hexp _ hx

theorem exists_cube_root_of_even {n : ℕ} (hn : 1 ≤ n) (hne : Even n) :
    ∃ τ : GaloisField 2 n, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  have h3 : 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [GaloisField.card 2 n (by omega)]
    obtain ⟨m, rfl⟩ := hne
    rw [← two_mul, pow_mul]
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]
    have : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  have hcard : Nat.card (rootsOfUnity 3 (GaloisField 2 n)) = 3 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd h3
  have : Nontrivial (rootsOfUnity 3 (GaloisField 2 n)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : rootsOfUnity 3 (GaloisField 2 n))
  refine ⟨((t : (GaloisField 2 n)ˣ) : GaloisField 2 n), ?_, fun h => ht (Subtype.ext (Units.ext h))⟩
  have := (mem_rootsOfUnity 3 (t : (GaloisField 2 n)ˣ)).mp t.2
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

theorem ks1919SplitAut_psl {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 1 ≤ n) (hne : Even n)
    (ψ : Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) (E : Subgroup (MulAut Y))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (F : Subgroup (MulAut Y))
    (hFE : F ≤ E) (hFinn : F ≤ (MulAut.conj : Y →* MulAut Y).range) (hF9 : Nat.card F = 9)
    (c : MulAut Y) (hcE : c ∈ E) (hcF : c ∉ F) (P : Subgroup Y) (hP : IsProperParabolic P) :
    ¬ ∀ y : Y, c y = y → y ∈ P := by
  intro hfixP
  set K := GaloisField 2 n with hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ψ : Y ≃* projectiveSL 3 K := ψ.trans (Sec4.projSLEquivProjectiveSL 3 K) with hΨ
  set Γ : MulAut Y ≃* MulAut (projectiveSL 3 K) := MulAut.congr Ψ with hΓ
  set α := Γ c with hα
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hc3, map_one]
  by_cases hlin : α ∈ linearAutGroup 3 K
  ·
    set E₁ := E.map Γ.toMonoidHom with hE₁
    set F₁ := F.map Γ.toMonoidHom with hF₁
    set E' := E₁ ⊓ linearAutGroup 3 K with hE'
    have hF₁lin : F₁ ≤ linearAutGroup 3 K := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := hFinn hx
      change Γ (MulAut.conj y) ∈ linearAutGroup 3 K
      rw [hΓ, KFacts.congr_mulAutConj]
      exact KFacts.innAut_le_linearAutGroup 3 K ⟨Ψ y, rfl⟩
    have hF₁E' : F₁ ≤ E' := le_inf (Subgroup.map_mono hFE) hF₁lin
    have hαE' : α ∈ E' := ⟨⟨c, hcE, rfl⟩, hlin⟩
    have hαF₁ : α ∉ F₁ := by
      rintro ⟨x, hx, hxc⟩
      exact hcF (Γ.injective hxc ▸ hx)
    have hcardF₁ : Nat.card F₁ = 9 := by
      rw [hF₁, Subgroup.card_map_of_injective Γ.injective, hF9]
    have hcardE₁ : Nat.card E₁ = 27 := by
      rw [hE₁, Subgroup.card_map_of_injective Γ.injective, hE27]
    have hdvd1 : Nat.card E' ∣ 27 := hcardE₁ ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : 9 ∣ Nat.card E' := hcardF₁ ▸ Subgroup.card_dvd_of_le hF₁E'
    have hne9 : Nat.card E' ≠ 9 := by
      intro h9
      have : F₁ = E' := Subgroup.eq_of_le_of_card_ge hF₁E' (by rw [h9, hcardF₁])
      exact hαF₁ (this ▸ hαE')
    have h27 : Nat.card E' = 27 := by
      obtain ⟨k, hk⟩ := hdvd2
      have hk27 : 9 * k ≤ 27 := hk ▸ Nat.le_of_dvd (by norm_num) hdvd1
      rw [hk] at hdvd1 hne9 ⊢
      have hk3 : k ≤ 3 := by omega
      interval_cases k <;> first | rfl | omega
    obtain ⟨τ, hτ3, hτ1⟩ := exists_cube_root_of_even hn hne
    have h3 : (3 : K) ≠ 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have h : (3 : K) = 1 := by linear_combination h2
      rw [h]
      exact one_ne_zero
    have hcommE₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hexpE₁ : ∀ x ∈ E₁, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
    have hle := card_le_nine_of_le_linearAutGroup h3 hτ3 hτ1 (E := E') inf_le_right
      (fun x hx y hy => hcommE₁ x hx.1 y hy.1) (fun x hx => hexpE₁ x hx.1)
    omega
  · obtain ⟨σ, hσ, H, hαH⟩ := KFacts.linear_order_three_field_descent le_rfl α hα3 hlin
    set β := conjAut 3 K H with hβ
    have hfixα : ∀ x, α (β (subfieldProj σ x)) = β (subfieldProj σ x) := by
      intro x
      rw [hαH]
      change β (fieldAut 3 K σ (β⁻¹ (β (subfieldProj σ x)))) = _
      rw [MulAut.inv_apply_self, fieldAut_subfieldProj]
    set P' := (P.map Ψ.toMonoidHom).map ((β⁻¹ : MulAut (projectiveSL 3 K)) :
      projectiveSL 3 K ≃* projectiveSL 3 K).toMonoidHom with hP'
    have hP'par : IsProperParabolic P' :=
      isProperParabolic_map_equiv _ (isProperParabolic_map_equiv Ψ hP)
    apply range_subfieldProj_not_le σ hP'par
    rintro _ ⟨x, rfl⟩
    have hz := hfixα x
    set z := β (subfieldProj σ x) with hz'
    have hcfix : c (Ψ.symm z) = Ψ.symm z := by
      have h1 : Ψ (c (Ψ.symm z)) = z := hz
      have h2 := congrArg Ψ.symm h1
      rwa [MulEquiv.symm_apply_apply] at h2
    refine ⟨z, ⟨Ψ.symm z, hfixP _ hcfix, by simp⟩, ?_⟩
    change β⁻¹ (β (subfieldProj σ x)) = subfieldProj σ x
    rw [MulAut.inv_apply_self]

end L3

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

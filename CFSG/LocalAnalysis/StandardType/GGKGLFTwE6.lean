module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

namespace KGLF

theorem ggTorusLiftFix_of_lift {p r : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 →
      ∃ (R₀ : Type) (_ : Group R₀) (_ : ggFixDer x ≃* R₀), IsSimpleGroup R₀ ∧
        (∃ a b : R₀, a * b ≠ b * a) ∧ GGTorusLift p r R₀) :
    GGTorusLiftFix p r R I F := by
  intro L' _ _ ψ hψ hker hperf f hfp hind hnot
  obtain ⟨x, hx, hxψ⟩ := hind
  have hxI : x ∉ I := fun h => hnot ⟨x, h, hxψ⟩
  have hxp : x ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggInduced_pow ψ hxψ p l, hfp]
    rfl
  obtain ⟨R₀, _, θ₀, hs, hna, hlift⟩ := hfix x hx hxI hxp
  obtain ⟨ψ'', -, hsurj, hker', hkerc, hperf''⟩ :=
    ggSubfieldCore ψ hψ hker (ggFixDer x) (ggFixDer_perfect θ₀ hs hna) θ₀
  have hfH : ∀ l ∈ ggCore ψ (ggFixDer x), f l = l := fun l hl =>
    ggFixes_core ψ hker f x (fun l => (hxψ l).symm) ((ggFixDer x).comap ψ)
      (fun l hl => ggFixDer_le_ggFixSub x hl) hl
  exact ggTorusLift_pushforward ψ (ggCore ψ (ggFixDer x)) ψ'' hsurj hkerc hperf'' hker' hlift f hfH

theorem three_dvd_two_pow_add_one_of_mul {d : ℕ} (h : 3 ∣ 2 ^ (3 * d) + 1) : 3 ∣ 2 ^ d + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [pow_mul', Nat.add_mod, Nat.pow_mod] at h
  have hr := Nat.mod_lt (2 ^ d) (show 3 > 0 by norm_num)
  interval_cases hm : 2 ^ d % 3
  · simp at h
  · simp at h
  · omega

variable {n : ℕ} {K : Type} [Field K] [Finite K]


theorem ggTorusLiftFix_recipe (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (hna : ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a)
    (hconj : GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n))) :
    GGTorusLiftFix 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) := by
  refine ggTorusLiftFix_of_lift fun x hx hxI hx3 => ?_
  have h3n : 3 ∣ n := by
    by_contra h
    exact hxI (TwE6Per.mem_recipeI_of_pow_eq_one hn hK Nat.prime_three (by norm_num) h hx3)
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      TwE6Delta.RecipeI K n = D := ⟨_, rfl⟩
  have hN : GGInndiagNormal (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    InndiagE6.ggInndiagNormal_twE6 hn K hK
  have hle : ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ≤ D := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hy : MulAut.conj y ∈ TwE6Delta.RecipeI K n :=
        Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
      rw [hD] at hy
      exact hy
    · rw [Subgroup.closure_le, hD]
  have : D.Normal := ⟨fun φ hφ α => hle (hN α φ (by rw [hD]; exact hφ))⟩
  have hcl : Subgroup.closure (TwE6Delta.RecipeI K n ∪
      LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) ≤
      D ⊔ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hD] at hy
      exact Subgroup.mem_sup_left hy
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hy)
  obtain ⟨u, hu, f, hf, rfl⟩ : ∃ u ∈ D, ∃ f ∈ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)), u * f = x := by
    have h := hcl hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h
    exact Set.mem_mul.mp h
  have huI : u ∈ TwE6Delta.RecipeI K n := by
    rw [hD]
    exact hu
  obtain ⟨f', hf'F, u', hu'I, hf'o, e⟩ := hconj hs hna u huI f hf hxI hx3
  obtain ⟨k, _, _, hk, hs₀, hna₀, θ₀, hgeom⟩ :=
    twE6Fix_fixStd hn hK Nat.prime_three (by norm_num) hf'F hf'o
  have hgeom' : GGFixGeom (D : Set (MulAut (TwE6Delta.RecipeR K n))) f'
      (LargeEvenChevIDImage (LargeEvenCartanE 6) k
        (LargeEvenTwistedH (LargeEvenCartanE 6) k LargeEvenRhoE6 (n / 3))) θ₀ := hD ▸ hgeom
  rw [hD] at hu'I
  obtain ⟨θ, -⟩ := ggFixGeom_conj (J := D) hu'I hgeom'
  rw [e]
  refine ⟨_, inferInstance, θ, hs₀, hna₀, ?_⟩
  obtain ⟨d, rfl⟩ := h3n
  have e3 : 3 * d / 3 = d := by omega
  have hd : 1 ≤ 3 * d / 3 := by omega
  have h3d : 3 ∣ 2 ^ (3 * d / 3) + 1 := by
    rw [e3]
    exact three_dvd_two_pow_add_one_of_mul h3
  exact ggTorusLift_twE6Add_holds hd hk Nat.prime_three h3d

end KGLF

theorem ggNbrKGFieldTwE6ThreeAddLiftFix_holds :
    GGNbrKGFieldTwE6ThreeAddLiftFix := by
  intro lab hlab ht h3
  have hF : LargeEvenLabelAll lab (GGRawFieldConj 3) :=
    ggRawFieldConjInputExc_holds 3 Nat.prime_three (by norm_num) lab hlab (by simp [ht])
  have hR : LargeEvenLabelAll lab fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTorusLiftFix 3 4 R I F := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨hn, -⟩ := hlab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    exact recipeTwisted_and (P := fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTorusLiftFix 3 4 R I F)
      (fun K _ _ hK hc hs hna => KGLF.ggTorusLiftFix_recipe hn hK h3 hs hna hc) hQ
  intro Q hQ
  exact largeEvenRawDatum_mono (fun _ _ _ _ h' => ⟨h'.1.1, h'.2 h'.1.2⟩) (hR _ (hF Q hQ))

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KKernel
public import CFSG.LieType.Chevalley.TorusTupleLift

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
open scoped MatrixGroups

private theorem card_subgroup_pow_three_le_nine {L : Type*} [Field L]
    (H : Subgroup (Lˣ × Lˣ)) (hH : ∀ x ∈ H, x ^ 3 = 1) : Nat.card H ≤ 9 := by
  classical
  let φ : H → (rootsOfUnity 3 L) × (rootsOfUnity 3 L) := fun x =>
    (⟨x.1.1, by
        rw [mem_rootsOfUnity]
        exact congrArg Prod.fst (hH x.1 x.2)⟩,
      ⟨x.1.2, by
        rw [mem_rootsOfUnity]
        exact congrArg Prod.snd (hH x.1 x.2)⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : x.1.1 = y.1.1 := congrArg (fun z => (z.1 : Lˣ)) hxy
    have h2 : x.1.2 = y.1.2 := congrArg (fun z => (z.2 : Lˣ)) hxy
    exact Subtype.ext (Prod.ext h1 h2)
  calc
    Nat.card H ≤ Nat.card ((rootsOfUnity 3 L) × (rootsOfUnity 3 L)) :=
      Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 3 L) * Nat.card (rootsOfUnity 3 L) :=
      Nat.card_prod (rootsOfUnity 3 L) (rootsOfUnity 3 L)
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity (k := 3) (R := L))
        (card_rootsOfUnity (k := 3) (R := L))
    _ = 9 := by norm_num

theorem card_le_twentySeven_of_le_torus
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18)
    (hker : kernelRoots (rootCharHom a) =
      componentRoots (rootCharHom a) i ∪ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' componentRoots (rootCharHom a) i ∪ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2] '' componentRoots (rootCharHom a) i)
    (X : Subgroup (ModGL Tag.E6 L)) (hX : X ≤ S.D.torus) (hX3 : ∀ x ∈ X, x ^ 3 = 1) :
    Nat.card X ≤ 27 := by
  classical
  obtain ⟨γ₁, γ₂, -, hΨ, -⟩ :=
    Up34Exc.RD.glue_of_check2 Up34Exc.RD.noG2_E6 73 Up34Exc.RD.okE6 (by norm_num)
      Up34Exc.RD.rdCheck2_E6 a hap i h6
  have hXG : X ≤ torusGroup Tag.E6 L :=
    fun x hx => (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 (hX hx)).1
  obtain ⟨β, hβ⟩ := exists_rootDiagUnitHom_comp_eq (X.subtype : X →* ModGL Tag.E6 L)
    (fun x => hXG x.2)
  have hβx : ∀ z : X, rootDiagUnit Tag.E6 (β z) = (z : ModGL Tag.E6 L) :=
    fun z => DFunLike.congr_fun hβ z
  let χ₁ : (Fin Tag.E6.rank → Lˣ) →* Lˣ :=
    { toFun := fun a => rootChar a γ₁
      map_one' := CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one γ₁
      map_mul' := fun a b => CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul a b γ₁ }
  let χ₂ : (Fin Tag.E6.rank → Lˣ) →* Lˣ :=
    { toFun := fun a => rootChar a γ₂
      map_one' := CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one γ₂
      map_mul' := fun a b => CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul a b γ₂ }
  let f : X →* Lˣ × Lˣ := (χ₁.comp β).prod (χ₂.comp β)
  have hf_apply : ∀ z : X, f z = (rootChar (β z) γ₁, rootChar (β z) γ₂) := fun _ => rfl
  let T : Set (Fin Tag.E6.rank → Lˣ) :=
    {c | (∀ j, c j ^ 3 = 1) ∧ ∀ γ ∈ kernelRoots (rootCharHom a), rootChar c γ = 1}
  have hTenc : T.encard ≤ 3 := encard_trivialOn_kernelRoots_le_three h3 hap h18
  have hTfin : T.Finite := Set.finite_of_encard_le_coe hTenc
  have hTncard : T.ncard ≤ 3 := (Set.encard_le_coe_iff_finite_ncard_le.1 hTenc).2
  have : Finite T := hTfin.to_subtype
  have hroot_of_mem : ∀ {γ : Fin Tag.E6.rank → ℤ},
      γ ∈ componentRoots (rootCharHom a) i → IsRoot Tag.E6 γ := fun hγ => hγ.1.1
  let ψ : f.ker → T := fun x => ⟨β x.1, by
    set c : Fin Tag.E6.rank → Lˣ := β x.1 with hc
    have hcx : rootDiagUnit Tag.E6 c = (x.1 : ModGL Tag.E6 L) := by
      rw [hc]; exact hβx x.1
    have hc3 : c ^ 3 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6)
      rw [← rootDiagUnit_pow, rootDiagUnit_one, hcx, hX3 x.1.val x.1.2]
    have hfx : f x.1 = 1 := MonoidHom.mem_ker.1 x.2
    rw [hf_apply x.1] at hfx
    have hγ₁ : rootChar c γ₁ = 1 := by
      have := congrArg Prod.fst hfx
      simpa [hc] using this
    have hγ₂ : rootChar c γ₂ = 1 := by
      have := congrArg Prod.snd hfx
      simpa [hc] using this
    have hneg : ∀ v : Fin Tag.E6.rank → ℤ, rootChar c (-v) = (rootChar c v)⁻¹ := by
      intro v
      simpa [rootChar_zero] using rootChar_sub c 0 v
    have hPΨ : ∀ γ ∈ componentRoots (rootCharHom a) i, rootChar c γ = 1 := by
      intro γ hγ
      rw [hΨ] at hγ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hγ₁
      · exact hγ₂
      · rw [rootChar_add, hγ₁, hγ₂, one_mul]
      · rw [hneg, hγ₁, inv_one]
      · rw [hneg, hγ₂, inv_one]
      · rw [hneg, rootChar_add, hγ₁, hγ₂, one_mul, inv_one]
    have hc_torus : rootDiagUnit Tag.E6 c ∈ S.D.torus := by
      rw [hcx]; exact hX x.1.2
    have hPρ : ∀ γ ∈ componentRoots (rootCharHom a) i, rootChar c (S.ρ γ) = 1 := by
      intro γ hγ
      rw [S.frob.rootChar_eq c hc_torus γ (hroot_of_mem hγ), hPΨ γ hγ, one_pow]
    have hPρ2 : ∀ γ ∈ componentRoots (rootCharHom a) i,
        rootChar c ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2] γ) = 1 := by
      intro γ hγ
      have hγroot : IsRoot Tag.E6 γ := hroot_of_mem hγ
      have hργroot : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγroot
      have h2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2] γ =
          S.ρ (S.ρ γ) := by
        rw [Function.iterate_succ_apply', Function.iterate_one]
      rw [h2, S.frob.rootChar_eq c hc_torus (S.ρ γ) hργroot, hPρ γ hγ, one_pow]
    have hPker : ∀ γ ∈ kernelRoots (rootCharHom a), rootChar c γ = 1 := by
      intro γ hγ
      rw [hker] at hγ
      simp only [Set.mem_union, Set.mem_image] at hγ
      rcases hγ with (hγ | ⟨δ, hδ, rfl⟩) | ⟨δ, hδ, rfl⟩
      · exact hPΨ γ hγ
      · exact hPρ δ hδ
      · exact hPρ2 δ hδ
    exact ⟨fun j => by simpa using congrFun hc3 j, hPker⟩⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : β x.1 = β y.1 := congrArg Subtype.val hxy
    have h2 : (x.1 : ModGL Tag.E6 L) = (y.1 : ModGL Tag.E6 L) := by
      rw [← hβx x.1, ← hβx y.1, h1]
    exact Subtype.ext (Subtype.ext h2)
  have hker3 : Nat.card f.ker ≤ 3 :=
    calc
      Nat.card f.ker ≤ Nat.card T := Nat.card_le_card_of_injective ψ hψ
      _ = T.ncard := Nat.card_coe_set_eq T
      _ ≤ 3 := hTncard
  have hrange_pow : ∀ x ∈ f.range, x ^ 3 = 1 := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hX3 y.val y.2
    rw [← map_pow, hy3, map_one]
  have hrange9 : Nat.card f.range ≤ 9 := card_subgroup_pow_three_le_nine f.range hrange_pow
  have key := Subgroup.card_ker_mul_card_range f
  calc
    Nat.card X = Nat.card f.ker * Nat.card f.range := key.symm
    _ ≤ 3 * 9 := Nat.mul_le_mul hker3 hrange9
    _ = 27 := by norm_num

end CFSG.StandardType.TwE6TwA2K

end

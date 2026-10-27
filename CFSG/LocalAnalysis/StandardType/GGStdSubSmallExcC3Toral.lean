module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3At
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3ToralCore
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC12Core
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndNode
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus

public section

namespace CFSG.StandardType.SmallExc

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three E6ThreeEnd

section Toral

variable {K : Type} [Field K]

theorem slTwoWitness_rootSL2 [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) {E : Subgroup (hatGroup .E6 K)}
    (hET : ∀ x ∈ E, ∃ b, (x : ModGL .E6 K) = rootDiagUnit .E6 b)
    {D : Subgroup (adjointGroup .E6 K)} {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hβD : ∀ A, rootSL2 .E6 K β A ∈ D.map (adjointGroup .E6 K).subtype) {ζ : Kˣ}
    (hζ2 : ζ ^ 2 ≠ 1) {e : hatGroup .E6 K} (he : e ∈ E) (he3 : e ^ 3 = 1)
    (het : (e : ModGL .E6 K) = rootTorusSL2 .E6 K β ζ) :
    SLTwoWitness 3 (E.map (hatAut .E6 K)) D := by
  have hmem : ∀ A, rootSL2 .E6 K β A ∈ adjointGroup .E6 K := fun A => by
    obtain ⟨d, -, hd⟩ := hβD A
    rw [← hd]
    exact d.2
  set ρ : SL(2, K) →* adjointGroup .E6 K := (rootSL2 .E6 K β).codRestrict _ hmem with hρdef
  have hρc : ∀ A, (ρ A : ModGL .E6 K) = rootSL2 .E6 K β A := fun A => rfl
  have hρinj : Function.Injective ρ := fun A B h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field β (by rw [← hρc, ← hρc, h])
  have hρD : ∀ A, ρ A ∈ D := fun A => by
    obtain ⟨d, hd, hdA⟩ := hβD A
    rwa [show ρ A = d from Subtype.ext ((hρc A).trans hdA.symm)]
  have hte : (ρ (HSL ζ) : ModGL .E6 K) = e := by
    rw [het]
    rfl
  have hcomm : ∀ x ∈ E, (x : ModGL .E6 K) * e * (x : ModGL .E6 K)⁻¹ = e := by
    intro x hx
    obtain ⟨b, hb⟩ := hET x hx
    obtain ⟨b', hb'⟩ := hET e he
    rw [hb, hb', ← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]
  refine ⟨ρ (HSL ζ), Subtype.ext ?_, ?_, ⟨e, he, MulEquiv.ext fun h => Subtype.ext ?_⟩,
    ⟨ρ (uSL 1), hρD _, fun h => ?_⟩, K, inferInstance, inferInstance, inferInstance, n, hn, hK,
    ρ, hρinj, ⟨HSL ζ, rfl⟩, ?_, ?_⟩
  · simpa [hte] using congrArg Subtype.val he3
  · rintro _ ⟨x, hx, rfl⟩
    exact Subtype.ext (by rw [coe_hatAut_apply, hte, hcomm x hx])
  · rw [coe_hatAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hte]
  · have h1 : HSL ζ * uSL (1 : K) = uSL 1 * HSL ζ := hρinj (by rw [map_mul, map_mul]; exact h)
    have h2 := CFSG.LieType.Chevalley.E6GraphLevi.HSL_conj_uSL ζ (1 : K)
    rw [h1, mul_inv_cancel_right] at h2
    have h3 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h2
    simp only [coe_uSL] at h3
    exact hζ2 (Units.ext (by simpa using h3.symm))
  · rintro _ ⟨A, rfl⟩
    exact hρD A
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨A, rfl⟩
    obtain ⟨b, hb⟩ := hET x hx
    obtain ⟨B, hB⟩ : ∃ B, rootDiagUnit .E6 b * rootSL2 .E6 K β A * (rootDiagUnit .E6 b)⁻¹ =
        rootSL2 .E6 K β B := ⟨_, CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b hβ A⟩
    exact ⟨B, Subtype.ext (by rw [hρc, ← hB, coe_hatAut_apply, hb, hρc])⟩

theorem slTwoAt_toral [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) {E : Subgroup (hatGroup .E6 K)}
    (hET : ∀ x ∈ E, ∃ b, (x : ModGL .E6 K) = rootDiagUnit .E6 b) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (h5 : 3 ^ 5 ≤ Nat.card E) : SLTwoAt 3 (E.map (hatAut .E6 K)) := by
  have := Fact.mk Nat.prime_three
  have hn : 2 ≤ n := by
    by_contra hlt
    interval_cases n
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK] at h1
      norm_num at h1
    · norm_num at h3
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) (by rw [hK]; exact h3)
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 =>
    absurd (hζo ▸ orderOf_dvd_of_pow_eq_one h2 : 3 ∣ 2) (by norm_num)
  have : Finite (ModGL .E6 K) := finite_modGL
  set E' := E.map (hatGroup .E6 K).subtype with hE'
  have hEab : IsElemAbelian 3 E := ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (by
    obtain ⟨b₁, h₁⟩ := hET a a.2
    obtain ⟨b₂, h₂⟩ := hET b b.2
    change ((a : hatGroup .E6 K) : ModGL .E6 K) * (b : hatGroup .E6 K) =
      ((b : hatGroup .E6 K) : ModGL .E6 K) * (a : hatGroup .E6 K)
    rw [h₁, h₂, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]))⟩⟩, hE3⟩
  have hE'X : E' ≤ xHat .E6 K ⊥ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hET x hx
    change (x : ModGL .E6 K) ∈ _
    rw [hb]
    exact rootDiagUnit_mem_xHat ⊥ b
  obtain ⟨A, hA, -, -, hcount⟩ :=
    card_eq_mul_card_expE hζo hζ (TableB.isElemAbelian_map hEab _) hE'X
  have hcardE : Nat.card (expE ζ hζ E') = Nat.card E := by
    have h1 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective
    rw [← h1, hcount, le_bot_iff.mp hA, Subgroup.card_bot, one_mul]
  obtain ⟨c, hc⟩ := exists_forall_mem_iff_dot (expE ζ hζ E') (by rw [hcardE]; exact h5)
  rintro _ ⟨e, he, rfl⟩ - D hD hDn hDq hcent
  obtain ⟨b, hb⟩ := hET e he
  have hb3' : b ^ 3 = 1 := by
    have h1 : (e : ModGL .E6 K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hE3 e he, Subgroup.coe_one]
    rw [hb, rootDiagUnit_pow] at h1
    exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  have hb3 : ∀ i, b i ^ 3 = 1 := fun i => by simpa using congrFun hb3' i
  have hfixC : ∀ g : adjointGroup .E6 K, g ∈ ggFix (hatAut .E6 K e) ↔
      (g : ModGL .E6 K) ∈ Subgroup.centralizer {rootDiagUnit .E6 b} := fun g => by
    rw [mem_ggFix, ← conj_eq_iff_mem_centralizer, ← hb, ← coe_hatAut_apply]
    exact Subtype.ext_iff
  set D' := D.map (adjointGroup .E6 K).subtype with hD'
  have hD'C : D' ≤ toralCentralizer .E6 K b := by
    rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.mem_inf.2 ⟨d.2, (hfixC d).mp (hD hd)⟩
  have hn' : ∀ c ∈ toralCentralizer .E6 K b, ∀ d ∈ D', c * d * c⁻¹ ∈ D' := by
    rintro c hc _ ⟨d, hd, rfl⟩
    obtain ⟨hcC, hcz⟩ := Subgroup.mem_inf.1 hc
    exact ⟨_, hDn ⟨c, hcC⟩ ((hfixC ⟨c, hcC⟩).mpr hcz) d hd, rfl⟩
  have hqe : CFSG.IsQuasisimple D' := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (D.equivMapOfInjective _ (adjointGroup .E6 K).subtype_injective) hDq
  obtain ⟨i, hi⟩ :=
    SmallExcC12.exists_eq_componentRootSpan .E6 hζ2 Nat.prime_three b hb3 D' hD'C hn' hqe
  set Ψ := componentRoots (rootCharHom b) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hD'Ψ : D' = rootSpan .E6 K Ψ := hi
  obtain ⟨⟨α, hαk⟩, hαi⟩ := Quotient.exists_rep i
  set f : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 := AddMonoidHom.mk'
    (fun β => ∑ j, c j * ((iform β (Pi.single j 1) : ℤ) : ZMod 3))
    (fun β β' => by simp only [iform_add_left, Int.cast_add, mul_add, Finset.sum_add_distrib])
    with hf
  have hτ : ∀ j, Tag.E6.symmetrizer j j = 1 := by decide
  rcases exists_root_eq_zero_or_span hτ hΨ (α := α) ⟨hαk, hαi⟩ f with
    ⟨β, hβ, hfβ⟩ | ⟨β, γ, hspan⟩
  ·
    have hβr := hΨ.isRoot β hβ
    obtain ⟨e', he', he'x⟩ :=
      mem_expE.mp ((hc fun j => ((iform β (Pi.single j 1) : ℤ) : ZMod 3)).mpr hfβ)
    have het : (e' : ModGL .E6 K) = rootTorusSL2 .E6 K β ζ := by
      rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβr]
      refine he'x.trans (congrArg _ (funext fun j => ?_))
      rw [SimplyLacedCover.iform_self_eq_two hτ hβr,
        show 2 * iform β (Pi.single j 1) / 2 = iform β (Pi.single j 1) by omega, zetaVec_apply,
        ← zpow_natCast, ZMod.val_intCast, ← hζo, zpow_mod_orderOf]
    have hβD : ∀ A, rootSL2 .E6 K β A ∈ D' := fun A => by
      have hle : (rootSL2 .E6 K β).range ≤ rootSpan .E6 K Ψ := by
        rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβr]
        exact sup_le (le_iSup₂ (f := fun γ (_ : γ ∈ Ψ) => rootSubgroup .E6 K γ) β hβ)
          (le_iSup₂ (f := fun γ (_ : γ ∈ Ψ) => rootSubgroup .E6 K γ) (-β) (hΨ.neg_mem β hβ))
      rw [hD'Ψ]
      exact hle ⟨A, rfl⟩
    exact slTwoWitness_rootSL2 hK hn hET hβr hβD hζ2 he' (hE3 e' he') het
  ·
    exfalso
    obtain ⟨y, hy⟩ := exists_zetaVec_eq hζo hζ hb3'
    obtain ⟨x, hxE, hxu, hxv, hxk⟩ := exists_mem_ker_ne_smul (expE ζ hζ E')
      (by rw [hcardE]; exact le_trans (by norm_num) h5)
      (AddMonoidHom.mk' (fun x => ∑ j, ((β j : ℤ) : ZMod 3) * x j)
        (fun x x' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]))
      (AddMonoidHom.mk' (fun x => ∑ j, ((γ j : ℤ) : ZMod 3) * x j)
        (fun x x' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])) y
    obtain ⟨e₁, he₁, he₁x⟩ := mem_expE.mp hxE
    have he₁x' : (e₁ : ModGL .E6 K) = rootDiagUnit .E6 (zetaVec ζ hζ x) := he₁x
    have hcentx : rootSpan .E6 K Ψ ≤
        Subgroup.centralizer {rootDiagUnit .E6 (zetaVec ζ hζ x)} := by
      refine rootSpan_le_centralizer _ fun δ hδ => ⟨hΨ.isRoot δ hδ, ?_⟩
      obtain ⟨m, k, rfl⟩ := hspan δ hδ
      have hsum : ∑ j, (((m • β + k • γ) j : ℤ) : ZMod 3) * x j = 0 := by
        have hu : ∑ j, ((β j : ℤ) : ZMod 3) * x j = 0 := hxu
        have hv : ∑ j, ((γ j : ℤ) : ZMod 3) * x j = 0 := hxv
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, add_mul,
          Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hu, hv, mul_zero, add_zero]
      rw [StandardType.NoOffE8Five.rootChar_zetaVec hζ x, hsum, ofAdd_zero, map_one]
    have hfixD : ∀ d ∈ D, hatAut .E6 K e₁ d = d := fun d hd => by
      have h1 : (d : ModGL .E6 K) ∈ rootSpan .E6 K Ψ := by
        rw [← hD'Ψ]
        exact ⟨d, hd, rfl⟩
      refine Subtype.ext ?_
      rw [coe_hatAut_apply, he₁x']
      exact conj_eq_iff_mem_centralizer.mpr (hcentx h1)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcent _ ⟨e₁, he₁, rfl⟩ hfixD)
    have hEm : ∀ z ∈ E, (z : ModGL .E6 K) ∈ monoHat .E6 K := fun z hz => by
      obtain ⟨b', hb'⟩ := hET z hz
      rw [hb']
      exact rootDiagUnit_mem_monoHat b'
    have hek : e ^ k = e₁ := mul_inv_eq_one.mp (eq_one_of_hatAut_eq_one
      (hEm _ (mul_mem (zpow_mem he k) (inv_mem he₁)))
      (by rw [map_mul, map_zpow, map_inv, hk, mul_inv_cancel]))
    have h2 : rootDiagUnit .E6 (b ^ k) = rootDiagUnit .E6 (zetaVec ζ hζ x) := by
      rw [← rootDiagHom_apply, map_zpow, rootDiagHom_apply, ← hb, ← Subgroup.coe_zpow, hek,
        he₁x']
    have h3 : zetaVec ζ hζ x = zetaVec ζ hζ ((k : ZMod 3) • y) := by
      rw [← rootDiagUnit_injective h2, ← hy]
      funext j
      exact zmodPowHom_zpow ζ hζ k (y j)
    exact hxk k (zetaVec_injective hζo hζ h3)

end Toral

end CFSG.StandardType.SmallExc

end

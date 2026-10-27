module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmFieldPlus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  QuadraticMap CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.CatalogueBHigherLinearField TableBOrth

namespace OrdPOm

section FrobFix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem frobeniusEquiv_pow_apply (k : ℕ) (x : K) : ((frobeniusEquiv K 2) ^ k) x = x ^ 2 ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    change ((frobeniusEquiv K 2) ^ k) ((frobeniusEquiv K 2) x) = _
    rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, ← pow_succ']

theorem frobPair_pow_conjAct_fix (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hb : b ≠ 0) {k p : ℕ} (hp : p.Prime) (hσ : ((frobeniusEquiv K 2) ^ k) ^ p = 1) {ζ : Kˣ}
    (hζp : ζ ^ p = 1) {x : spinGroup (quadMinus n K b c)}
    (hx : spinMatrix (quadMinus n K b c) x ∈ (minusTorusGL (K := K) (m := n - 1) hζp).range) :
    conjAct (Qm n hn4 b c) ((frobPair n (by omega) b c hb) ^ k) (AutOm.spinModelMinus hn4 hirr x) =
      AutOm.spinModelMinus hn4 hirr x := by
  have hn : 1 ≤ n := by omega
  obtain ⟨a, ha⟩ := hx
  set e := minusIndexEquiv n hn with he
  set d := minusUnits fun i => TableBSymp.zmodPowHom hζp (a i) with hd
  have hz : ∀ i, (TableBSymp.zmodPowHom hζp (a i)) ^ p = 1 := fun i => by
    rw [← map_pow, show a i ^ p = 1 from congrFun (TableBSymp.pow_card_eq_one_zmod a) i,
      map_one]
  have hdp : ∀ i, d i ^ p = 1 := by
    rintro (i | i | i)
    · exact hz i
    · change ((TableBSymp.zmodPowHom hζp (a i))⁻¹) ^ p = 1
      rw [inv_pow, hz i, inv_one]
    · exact one_pow _
  have hfix : ∀ i, ((d i : Kˣ) : K) ^ 2 ^ k = d i := fun i => by
    rw [← frobeniusEquiv_pow_apply]
    exact OrdPRest.ringAut_fix_of_pow_eq_one hp hσ
      (by rw [← Units.val_pow_eq_pow_val, hdp i, Units.val_one])
  have hA : ∀ y i, Matrix.mulVec ((AutOm.spinModelMinus hn4 hirr x : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) y i = (d (e.symm i) : K) * y i := by
    intro y i
    have h1 := AutOm.spinModelMinus_mulVec hn4 hirr x ((reindexVectorEquiv (K := K) e).symm y)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [h1, reindexVectorEquiv_apply, ← spinMatrix_mulVec, ← ha, minusTorusGL_apply,
      TauCeti.diagGL_coe, Matrix.mulVec_diagonal, reindexVectorEquiv_symm_apply,
      Equiv.apply_symm_apply]
  have h0 : d (e.symm (tailZero n hn)) = 1 := by
    rw [tailZero, ← he, Equiv.symm_apply_apply]
    rfl
  have h1 : d (e.symm (tailOne n hn)) = 1 := by
    rw [tailOne, ← he, Equiv.symm_apply_apply]
    rfl
  refine AutOm.conjAct_apply_eq_of _ _ _ fun y => ?_
  funext i
  rw [frobPair_pow_apply, hA, hA, hA, frobPair_pow_apply]
  split_ifs with hi0 hi1
  · subst hi0
    rw [h0, h1, Units.val_one, one_mul, one_mul, one_mul]
  · subst hi1
    rw [h1, Units.val_one, one_mul, one_mul]
  · rw [mul_pow, hfix]

end FrobFix

section FieldMinusMain

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ} {b c : K}

theorem exists_conj_mem_centralizer_field_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n) {f₀ : ℕ}
    (hf : Nat.card K = 2 ^ f₀) (hf1 : 1 ≤ f₀) {ψ : spinGroup (quadMinus n K b c) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (minusDatum n hirr) .POmegaMinus n f ψ)
    (hp : p ∣ Nat.card K - 1) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G))
    (hyp : y ^ p = 1) (hyI : ¬ GGPsiInnerDiag (minusDatum n hirr) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hn : 1 ≤ n := by omega
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn4]
    exact hker
  set j := spinMatrix (quadMinus n K b c) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (StatedQuadMinus n K b c) :=
    range_spinMatrix_quadMinus hn4 hirr
  set π := AutOm.spinModelMinus hn4 hirr with hπdef
  have hπ : Function.Injective π := AutOm.spinModelMinus_injective hn4 hirr
  have hπs : Function.Surjective π := AutOm.spinModelMinus_surjective hn4 hirr
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := p) hp
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn4 ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
  obtain ⟨hA, hAj, hAc⟩ := transfer_range ψ hψ j hj hS.elem hBsψ
  have hBs : Nat.card Bs ≤ p ^ (n - 1) := by
    rw [← hAc]
    exact card_le_minus hp2 hζ hirr hn (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  have hk : π.ker = ψ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hπ, (MonoidHom.ker_eq_bot_iff _).2 hψ]
  set Θ := AutSt.modelEquiv ψ π hπs hk with hΘdef
  have hΘ : ∀ x, ((Θ (π x) : ψ.range) : G) = ψ x := AutSt.modelEquiv_apply ψ π hπs hk
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hyM
  set a : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : ψ.range, ((a x : ψ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (matrixDerived (Qm n hn4 b c)) := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ z, Θ (β z) = a (Θ z) := fun z => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ z, ((Θ (β z) : ψ.range) : G) = y⁻¹ * Θ z * y := fun z => by rw [hβ, ha]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (Qm n hn4 b c)) := by
    rintro ⟨h, hh⟩
    obtain ⟨x₀, hx₀⟩ := hπs h
    apply hyI
    have hcent : y * ψ x₀ ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have e := hrel (π x)
      rw [← hh, MulAut.conj_apply, ← hx₀, ← map_inv, ← map_mul, ← map_mul, hΘ, hΘ] at e
      rw [map_mul, map_mul, map_inv] at e
      calc ψ x * (y * ψ x₀) = y * (y⁻¹ * ψ x * y) * ψ x₀ := by group
        _ = y * (ψ x₀ * ψ x * (ψ x₀)⁻¹) * ψ x₀ := by rw [← e]
        _ = y * ψ x₀ * ψ x := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hy : y = ψ x₀⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hcent
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨x₀⁻¹, hy.symm⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨ι, ⟨h, rfl⟩, k, hβeq⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf β
  have hb := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  set S := (frobPair n hn b c hb) ^ k with hSdef
  have hτS : AutOm.frobAut hn4 hirr ^ k = conjAct (Qm n hn4 b c) S := by
    change AutOm.frobAut hn4 hirr ^ k = conjAct (Qm n hn4 b c) (frobPair n hn b c hb ^ k)
    rw [map_pow]
    rfl
  have hSiso : RecipeFieldOmega.IsIsoPair (Qm n hn4 b c) S.val := by
    rw [SubmonoidClass.coe_pow]
    exact (RecipeFieldOmega.isIsoPair_frobPair hn hb).pow k
  have hout : MulAut.conj h * conjAct _ S ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
    rw [← hτS, ← hβeq]
    exact hβout
  have hord' : (MulAut.conj h * conjAct _ S) ^ p = 1 := by
    rw [← hτS, ← hβeq, hβp]
  have hfp : conjAct _ S ^ p = 1 := by
    have h1 := RecipeFieldOmega.pow_mem_inner_of_mul_pow_eq_one ⟨h, rfl⟩ hord'
    rw [← hτS, ← pow_mul] at h1
    have h2 : AutOm.frobAut hn4 hirr ^ (k * p) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ⊓
          Subgroup.zpowers (AutOm.frobAut hn4 hirr) :=
      ⟨h1, Subgroup.npow_mem_zpowers _ _⟩
    rw [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at h2
    rw [← hτS, ← pow_mul, h2]
  obtain ⟨u', ⟨w, rfl⟩, heq⟩ := RecipeFieldOmega.exists_conj_of_isIsoPair hn hnd hT3 hAP hpp hp2
    hSiso (AutOm.tailVec_form_ne_zero n hn b c) (RecipeFieldOmega.frobPair_pow_tailVec hn hb k) h
    hout hord' hfp
  have hβw : β = MulAut.conj w * conjAct _ S * (MulAut.conj w)⁻¹ := by
    rw [hβeq, hτS, heq]
  have hSp : S ^ p = 1 := RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT3 hAP
    ⟨_, AutOm.tailVec_form_ne_zero n hn b c⟩
    (by rw [SubmonoidClass.coe_pow]; exact hSiso.pow p) (by rw [map_pow, hfp])
  have hσ : ((frobeniusEquiv K 2) ^ k) ^ p = 1 := by
    have e1 : ((S ^ p : similarityPairs (Qm n hn4 b c)) :
        coordinateSemilinearGroup (2 * n) K).right = 1 := by
      rw [hSp]
      rfl
    rw [SubmonoidClass.coe_pow, RecipeFieldOmega.right_pow, hSdef, SubmonoidClass.coe_pow,
      RecipeFieldOmega.right_pow, frobPair_right] at e1
    exact e1
  set T := (minusTorusGL (K := K) (m := n - 1) hζp).range with hT
  set EΓ := ((T.comap j).map π).map (MulAut.conj w).toMonoidHom with hEΓ
  have hfix : ∀ z ∈ EΓ, β z = z := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have e1 : (MulAut.conj w)⁻¹ (MulAut.conj w (π x)) = π x := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    calc β ((MulAut.conj w).toMonoidHom (π x)) =
        MulAut.conj w (conjAct _ S ((MulAut.conj w)⁻¹ (MulAut.conj w (π x)))) := by
          rw [hβw]
          rfl
      _ = MulAut.conj w (π x) := by
        rw [e1, hSdef, frobPair_pow_conjAct_fix hn4 hirr hb hpp hσ hζp hx]
      _ = (MulAut.conj w).toMonoidHom (π x) := rfl
  obtain ⟨ι, hιz⟩ : ∃ ι : matrixDerived (Qm n hn4 b c) →* G, ∀ z, ι z = (Θ z : G) :=
    ⟨ψ.range.subtype.comp Θ.toMonoidHom, fun _ => rfl⟩
  have hι : Function.Injective ι := fun z z' hzz' => by
    rw [hιz, hιz] at hzz'
    exact Θ.injective (Subtype.ext hzz')
  have hTj : T ≤ j.range := by
    rw [hjr]
    rintro _ ⟨a, rfl⟩
    exact minusTorusGL_mem_omega hζp hodd a
  have hEel : IsElemAbelian p (EΓ.map ι) := isElemAbelian_map _ (isElemAbelian_map _
    (isElemAbelian_map _ (isElemAbelian_comap j hj (isElemAbelian_range_minusTorusGL hζp))))
  have hEcard : Nat.card (EΓ.map ι) = p ^ (n - 1) := by
    rw [Subgroup.card_map_of_injective hι, hEΓ,
      Subgroup.card_map_of_injective (MulAut.conj w).injective,
      Subgroup.card_map_of_injective hπ, ← Subgroup.card_map_of_injective hj,
      Subgroup.map_comap_eq_self hTj, card_range_minusTorusGL hζp hζ]
  have hEM : EΓ.map ι ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨z, -, rfl⟩
    rw [hιz]
    exact (hrange.le.trans Subgroup.le_normalizer) (Θ z).2
  have hcomm : ∀ e ∈ EΓ.map ι, y * e = e * y := by
    rintro _ ⟨z, hz, rfl⟩
    have e := hrel z
    rw [hfix z hz] at e
    rw [hιz]
    generalize (Θ z : G) = θ at e ⊢
    calc y * θ = y * (y⁻¹ * θ * y) := by rw [← e]
      _ = θ * y := by group
  exact OrdPNS.exists_conj_mem_centralizer_of_card hS hEM hEel (by rw [hEcard]; exact hBs) hcomm

end FieldMinusMain

end OrdPOm

section Family

theorem ggOrdPFieldConj_POmegaMinus_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hp y hyM hyo hyI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨-, hf, hn⟩ := hadm
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact OrdPOm.exists_conj_mem_centralizer_field_minus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hK hf hS (by rw [hK]; exact hp) hyM (hyo ▸ pow_orderOf_eq_one y) hyI

@[expose] def GGOrdPFieldConjPOmegaMinusNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .POmegaMinus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiDiagField (ggU .POmegaMinus n f).D ψ y →
      ¬ GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPFieldConjAt_POmegaMinus_of_nonsplit (h : GGOrdPFieldConjPOmegaMinusNonsplit) :
    GGOrdPFieldConjAt .POmegaMinus := by
  intro G _ _ p Bs G₀ n f ψ hS h24 y hyM hyo hDF hyI
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPFieldConj_POmegaMinus_split G p Bs G₀ n f ψ hS hpq y hyM hyo hyI
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hDF hyI

end Family

end CFSG.StandardType

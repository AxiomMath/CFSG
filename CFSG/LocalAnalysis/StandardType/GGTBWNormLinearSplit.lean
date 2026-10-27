module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeAOuter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeANbrDvd

open TypeA

theorem pow_sub_one_le_card_of_selfCent {K : Type} [Field K] [Finite K] {d p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) (hpd : Nat.Coprime p d)
    {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ a t) :
    p ^ (d - 1) ≤ Nat.card A := by
  classical
  have hu (u : (piProd p d K).ker) (i : Fin d) :
      rootEnt (u : Fin d → rootsOfUnity p K) i ^ p = 1 := by
    have he := congrArg (fun x : Kˣ => (x : K)) (u.1 i).2
    simpa [rootEnt] using he
  let F : (piProd p d K).ker → A := fun u =>
    ⟨MulAut.conj (φ (diagSL p d K u)),
      conj_mem_of_selfCent hsc hdiag (coe_diagSL u) (hu u)⟩
  have hF : Function.Injective F := by
    intro u v huv
    have he : MulAut.conj (φ (diagSL p d K u)) = MulAut.conj (φ (diagSL p d K v)) :=
      congrArg Subtype.val huv
    have hau : TypeA.GGActsBy φ (MulAut.conj (φ (diagSL p d K u))) (diagSL p d K u) := by
      intro s
      simp [MulAut.conj_apply, map_mul, map_inv]
    have hav : TypeA.GGActsBy φ (MulAut.conj (φ (diagSL p d K u))) (diagSL p d K v) := by
      rw [he]
      intro s
      simp [MulAut.conj_apply, map_mul, map_inv]
    have hcoords := TypeA.GGActsBy.diag_eq hφker hpd hd (coe_diagSL u) (coe_diagSL v)
      (hu u) (hu v) hau hav
    apply Subtype.ext
    funext i
    apply Subtype.ext
    apply Units.ext
    exact congrFun hcoords i
  rw [← card_ker_piProd hp hpK hd]
  exact Nat.card_le_card_of_injective F hF

end TypeANbrDvd

namespace TypeA

theorem ggTorusWNormSC_coprime {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) :
    GGTorusWNormSC p (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    _hM _hC _hpair _hlin hgen s hs
  have hsec : SLHasSections d K := slHasSections_of_four_le hp hpK hd
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨η, hηs, hη⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨η', hη's, hη'ker, hdiag, -, -⟩ :=
    exists_diagonal_model hp hpK (by omega) hpd hperfSL hψ hker hperf hηs hη hA hAI
  have hdiag' : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag η' a t := by
    intro a ha
    obtain ⟨D, ⟨t, hD⟩, -, haD⟩ := hdiag a ha
    refine ⟨t, SpecialLinearGroup.toGL D, hD, fun x => ?_⟩
    simpa only [TypeANbrDvd.slConjugation_toGL_eq, MulAut.conj_apply] using haD x
  have hr : p ^ (d - 1) ≤ Nat.card A :=
    TypeANbrDvd.pow_sub_one_le_card_of_selfCent hp hpK (by omega) hpd hη'ker hsc hdiag'
  let W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  obtain ⟨F, hFmul, hF1, -, hFW, hFA, hFinj, -⟩ :=
    exists_weylModel_psl hp hp2 hpK hd hpd hsec hψ hker hperf hA hAI hr
  let ρ : Equiv.Perm (Fin d) →* W :=
    { toFun := fun σ => ⟨F (σ⁻¹), hFA _⟩
      map_one' := by apply Subtype.ext; simpa using hF1
      map_mul' := fun σ τ => by
        apply Subtype.ext
        change F ((σ * τ)⁻¹) = F (σ⁻¹) * F (τ⁻¹)
        rw [_root_.mul_inv_rev, hFmul] }
  have hρ : Function.Bijective ρ := by
    constructor
    · intro σ τ he
      exact inv_injective (hFinj (congrArg Subtype.val he))
    · intro w
      obtain ⟨π, hπ⟩ := hFW w w.2
      exact ⟨π⁻¹, Subtype.ext (by change F ((π⁻¹)⁻¹) = w; simpa using hπ.symm)⟩
  have hZW : Subgroup.center ↥W = ⊥ := by
    let e : Equiv.Perm (Fin d) ≃* W := MulEquiv.ofBijective ρ hρ
    have hz := center_perm_eq_bot_of_three_le_card (α := Fin d) (by simpa using (show 3 ≤ d by omega))
    rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
  have hNI : NormInducesInner W :=
    ggTorusWeylNormInner_coprime hp hp2 hpK hd hpd hsec
      L' ψ hψ hker hperf A hA hAI hr h3
  obtain ⟨S, hSW, -, -, hSchur⟩ := ggTorusIrred_coprime hp hp2 hpK hd hpd hsec
    L' ψ hψ hker hperf A hA hAI hr h3
  have hscalar : ∀ f : MulAut ↥A, (∀ w ∈ W, f * w = w * f) →
      ∃ c : ZMod p, ∀ v, ggLin (p := p) ι f v = c • v := by
    intro f hf
    let g : MulAut L' → MulAut L' := fun a => if ha : a ∈ A then f ⟨a, ha⟩ else a
    have hg (a : MulAut L') (ha : a ∈ A) : g a = (f ⟨a, ha⟩ : MulAut L') := by
      simp only [g, dif_pos ha]
    obtain ⟨c, hc⟩ := hSchur g
      (fun a ha => by rw [hg a ha]; exact (f ⟨a, ha⟩).2)
      (fun a ha b hb => by
        rw [hg _ (A.mul_mem ha hb), hg a ha, hg b hb]
        exact congrArg Subtype.val (map_mul f ⟨a, ha⟩ ⟨b, hb⟩))
      (by
        intro n hn a ha
        have hnN : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
          apply Subgroup.mem_normalizer_fintype
          intro b hb
          have he : MulAut.conj n * b * (MulAut.conj n)⁻¹ =
              MulAut.conj (n * (b n)⁻¹) * b := by
            ext x
            change n * b (n⁻¹ * x * n) * n⁻¹ =
              (n * (b n)⁻¹) * b x * (n * (b n)⁻¹)⁻¹
            rw [map_mul, map_mul, map_inv]
            group
          rw [he]
          obtain ⟨hbp, hbfix⟩ := hSW n hn b hb
          exact A.mul_mem (hsc _ hbfix hbp) hb
        have htW : ggConjAut A hnN ∈ W :=
          ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN
        rw [hg _ ((Subgroup.mem_normalizer_iff.mp hnN a).mp ha), hg a ha]
        have he := congrArg (fun u : MulAut ↥A => (u ⟨a, ha⟩ : MulAut L'))
          (hf _ htW)
        have haeq : ggConjAut A hnN ⟨a, ha⟩ =
            ⟨MulAut.conj n * a * (MulAut.conj n)⁻¹,
              (Subgroup.mem_normalizer_iff.mp hnN a).mp ha⟩ :=
          Subtype.ext (ggConjAut_apply A hnN ⟨a, ha⟩)
        simpa only [MulAut.mul_apply, haeq, ggConjAut_apply] using he)
    refine ⟨(c : ZMod p), fun v => ?_⟩
    obtain ⟨a, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
    have he : f a = a ^ c := Subtype.ext ((hg a a.2).symm.trans (hc a a.2))
    change ggLin (p := p) ι f (ι (Additive.ofMul a)) = (c : ZMod p) • ι (Additive.ofMul a)
    rw [ggLin_apply_ofMul, he, ofMul_pow, map_nsmul, Nat.cast_smul_eq_nsmul (ZMod p)]
  have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by simpa using (Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt)) h3)
  have : Nontrivial V := ι.injective.nontrivial
  have : (MulAut.conj : L' →* MulAut L').range.Normal := RootCentExc.normal_range_mulAutConj
  exact ggWNormConcl_of_centerless ι φ h α hgen hZW hNI hscalar
    (mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs)

end TypeA

theorem ggTorusWNormSC_linear_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) (hpd : ¬ p ∣ d) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  exact ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_coprime hp hp2 hpq hd ((hp.coprime_iff_not_dvd).mpr hpd))

theorem largeEvenLabelAll_wnorm_linear_split {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n - 1) (hpd : ¬ p ∣ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hpq hpd ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
    change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_split (d := r + 1) hp hp2 (by rwa [hK]) (by omega) hpd
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_split (d := 4) hp hp2 (by rwa [hK]) (by norm_num) hpd

end CFSG.StandardType

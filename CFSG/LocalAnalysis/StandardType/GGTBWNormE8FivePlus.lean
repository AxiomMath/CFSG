module

public import CFSG.LocalAnalysis.StandardType.GGTorusE8PlusToral
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Plus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoNorm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet
public import CFSG.LocalAnalysis.StandardType.GGL45NtE8Five
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KE8F.Stab5

public noncomputable section

namespace CFSG.StandardType.E8FivePlusWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem card_closure_range_rootDiagUnit {K : Type} [Field K] [Finite K]
    (E : Subgroup (adjointGroup .E8 K))
    {g : ModGL .E8 (AlgebraicClosure K)} (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g) :
    Nat.card (Subgroup.closure (Set.range fun x : E => rootDiagUnit .E8 (a x))) = Nat.card E ∧
      Nat.card (Set.range fun x : E => rootDiagUnit .E8 (a x)) = Nat.card E := by
  let f : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E8 K).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    simpa [f] using hxy
  have hfx : ∀ x : E, rootDiagUnit .E8 (a x) = f x := by
    intro x
    rw [ha x]
    simp [f, MulAut.conj_apply]
  have hrange : (Set.range fun x : E => rootDiagUnit .E8 (a x)) = (E.map f : Set _) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hfx x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hfx ⟨x, hx⟩⟩
  have hcard : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
  refine ⟨?_, ?_⟩
  · rw [hrange, Subgroup.closure_eq, hcard]
  · rw [hrange]
    exact hcard

theorem card_le_ncard_range {K : Type} [Field K] [Finite K]
    (E : Subgroup (adjointGroup .E8 K))
    {g : ModGL .E8 (AlgebraicClosure K)} (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g) :
    Nat.card E ≤ (Set.range a).ncard := by
  have h := (card_closure_range_rootDiagUnit E a ha).2
  rw [Nat.card_coe_set_eq] at h
  rw [← h]
  have himg : (Set.range fun x : E => rootDiagUnit .E8 (a x)) =
      rootDiagUnit .E8 '' Set.range a := by
    rw [← Set.range_comp]
    rfl
  rw [himg]
  exact Set.ncard_image_le (Set.finite_range a)

theorem ggWNormConcl_E8_plus_of_toral {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K + 1)
    {L : Type} [Group L] [Finite L] (A : Subgroup (MulAut L))
    (e : L ≃* adjointGroup .E8 K) (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hAE : A.map (MulAut.congr e).toMonoidHom = E.map MulAut.conj)
    {g : ModGL .E8 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E8 (AlgebraicClosure K))
    (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g)
    (hcent : familyCentralizer .E8 (AlgebraicClosure K) a =
      familyGroup (K := AlgebraicClosure K) a)
    {Λ' V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ' → MulAut ↥A) (h : Λ' → V) (α : Λ' → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨-, -, -, -, t, n, -, -, -, -, ht, htr, -, -, hns, hN⟩ :=
    exists_e8_scalar_frame_of_family hp hp2 hq E hE hSC hg a ha hcent
  let Λ0 : adjointGroup .E8 K →* MulAut L :=
    (MulAut.congr e.symm).toMonoidHom.comp MulAut.conj
  have hΛ0 : Function.Injective Λ0 :=
    (MulAut.congr e.symm).injective.comp mulAut_conj_injective_adjointGroup
  have hΛψ : ∀ l, Λ0 (e l) = MulAut.conj l := by
    intro l
    ext x
    simp [Λ0, MulAut.congr_apply, MulAut.conj_apply]
  have hEA : E.map Λ0 = A := by
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    change E.map ((MulAut.congr e.symm).toMonoidHom.comp MulAut.conj) = A
    rw [← Subgroup.map_map, ← hAE, Subgroup.map_map, hcomp, Subgroup.map_id]
  exact ExcWeylCoord.wNormConcl_of_centralCover_weylFrame_E7E8 (Or.inr rfl) hp2 e.toMonoidHom
    e.surjective Λ0 hΛ0 hΛψ E A hEA t ht htr n hns hN ι φ h α hgen hs


theorem false_of_nonToral_datum {K : Type} [Field K] [Finite K] [CharP K 2]
    {L : Type} [Group L] [Finite L] (A : Subgroup (MulAut L)) (hA : IsElemAbelian 5 A)
    (e : L ≃* adjointGroup .E8 K) (E : Subgroup (adjointGroup .E8 K))
    (hE : IsElemAbelian 5 E) (hcard : 5 ^ 3 ≤ Nat.card E)
    (hAE : A.map (MulAut.congr e).toMonoidHom = E.map MulAut.conj)
    (hNT : ¬ ExcFramesHalf.IsToralSubgroup .E8 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E8 K).subtype)))
    [Fact (Nat.Prime 5)] {Λ' V : Type} [Fintype Λ'] [DecidableEq Λ'] [AddCommGroup V]
    [Module (ZMod 5) V] (ι : Additive ↥A ≃+ V) (φ : Λ' → MulAut ↥A) (h : Λ' → V)
    (α : Λ' → Module.Dual (ZMod 5) V) (M : CoxeterMatrix Λ') (C : Matrix Λ' Λ' ℤ)
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod 5))
    (hlin : ∀ i w, ggLin (p := 5) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ)) :
    False := by
  classical
  obtain ⟨i⟩ : Nonempty Λ' := by
    rcases hM with ⟨n, e', hn, -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩
    · exact ⟨e' ⟨0, by omega⟩⟩
    all_goals exact ⟨e' 0⟩
  let Λ0 : adjointGroup .E8 K →* MulAut L :=
    (MulAut.congr e.symm).toMonoidHom.comp MulAut.conj
  have hΛ0 : Function.Injective Λ0 :=
    (MulAut.congr e.symm).injective.comp mulAut_conj_injective_adjointGroup
  have hΛψ : ∀ l, Λ0 (e l) = MulAut.conj l := by
    intro l
    ext x
    simp [Λ0, MulAut.congr_apply, MulAut.conj_apply]
  have hEA : E.map Λ0 = A := by
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    change E.map ((MulAut.congr e.symm).toMonoidHom.comp MulAut.conj) = A
    rw [← Subgroup.map_map, ← hAE, Subgroup.map_map, hcomp, Subgroup.map_id]
  let β : adjointGroup .E8 K →* adjointGroup .E8 (AlgebraicClosure K) :=
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup .E8 K).subtype).codRestrict _
      fun x => baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) x.2
  have hβ : Function.Injective β := by
    intro x y hxy
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    exact congrArg Subtype.val hxy
  let E' := E.map β
  have : Finite E' := Finite.of_surjective _ (Subgroup.equivMapOfInjective E β hβ).surjective
  have hE' : IsElemAbelian 5 E' := TableB.isElemAbelian_map hE β
  have hcard' : 5 ^ 3 ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective hβ]
    exact hcard
  have hNT' : ¬ ExcFramesHalf.IsToralSubgroup .E8 (AlgebraicClosure K)
      (E'.map (adjointGroup .E8 (AlgebraicClosure K)).subtype) := by
    rwa [Subgroup.map_map]
  have hperf :=
    HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.universal_nonToral_normalizer_isPerfect
      E' hE' hNT' hcard'
  let ΘA : ↥E ≃* ↥A := (E.equivMapOfInjective Λ0 hΛ0).trans (MulEquiv.subgroupCongr hEA)
  let ΘE : ↥E ≃* ↥E' := E.equivMapOfInjective β hβ
  let Θ : ↥A ≃* ↥E' := ΘA.symm.trans ΘE
  have hΘA : ∀ x : E, ((ΘA x : ↥A) : MulAut L) = Λ0 x := fun x => rfl
  have hΘE : ∀ x : E, ((ΘE x : ↥E') : adjointGroup .E8 (AlgebraicClosure K)) = β x := fun x => rfl
  have hcA : ∀ a b : ↥A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have hpA : ∀ b : ↥A, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hA.2 b b.2)
  have hcE : ∀ a b : ↥E', a * b = b * a := fun a b => hE'.1.is_comm.comm a b
  have hpE : ∀ b : ↥E', b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hE'.2 b b.2)
  let dA := ggDetAut 5 Nat.prime_five hcA hpA
  let dE := ggDetAut 5 Nat.prime_five hcE hpE
  have hdE : ∀ n, dE (E'.normalizerMonoidHom n) = 1 := by
    intro n
    let P := E'.normalizerMonoidHom.range
    have hker : commutator ↥P ≤ (dE.comp P.subtype).ker := Abelianization.commutator_subset_ker _
    rw [Group.isPerfect_def.mp hperf] at hker
    exact hker (Subgroup.mem_top ⟨_, n, rfl⟩)
  have hgenA : ∀ ψ ∈ ggInduced (MulAut.conj : L →* MulAut L).range A, dA ψ = 1 := by
    rintro ψ ⟨_, ⟨l, rfl⟩, hlN, hψ⟩
    have hEl : ∀ x ∈ E, e l * x * (e l)⁻¹ ∈ E := by
      intro x hx
      have hmem : Λ0 x ∈ A := hEA ▸ Subgroup.mem_map_of_mem Λ0 hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hlN (Λ0 x)).mp hmem
      rw [← hΛψ l, ← map_inv, ← map_mul, ← map_mul, ← hEA] at h1
      obtain ⟨x', hx', hxx'⟩ := h1
      rw [← hΛ0 hxx']
      exact hx'
    have hn : β (e l) ∈ Subgroup.normalizer (E' : Set (adjointGroup .E8 (AlgebraicClosure K))) := by
      apply Subgroup.mem_normalizer_fintype
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hEl x hx, by rw [map_mul, map_mul, map_inv]⟩
    have hconj : MulAut.congr Θ ψ = E'.normalizerMonoidHom ⟨β (e l), hn⟩ := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := ΘE.surjective y
      have hψx : ψ (ΘA x) = ΘA ⟨e l * x * (e l)⁻¹, hEl x x.2⟩ := by
        apply Subtype.ext
        rw [hψ, hΘA, hΘA, ← hΛψ l, ← map_inv, ← map_mul, ← map_mul]
      apply Subtype.ext
      rw [MulAut.congr_apply]
      change ((ΘE (ΘA.symm (ψ (ΘA (ΘE.symm (ΘE x)))))) :
        adjointGroup .E8 (AlgebraicClosure K)) = _
      rw [ΘE.symm_apply_apply, hψx, ΘA.symm_apply_apply, hΘE,
        Subgroup.normalizerMonoidHom_apply_apply_coe, hΘE]
      change β (e l * (x : adjointGroup .E8 K) * (e l)⁻¹) = β (e l) * β x * (β (e l))⁻¹
      rw [map_mul, map_mul, map_inv]
    rw [show dA ψ = dE (MulAut.congr Θ ψ) from
      (ggDetAut_congr 5 Nat.prime_five hcA hpA hcE hpE Θ ψ).symm, hconj]
    exact hdE _
  have hφi : dA (φ i) = 1 := by
    have hle : ggAutomizer (MulAut.conj : L →* MulAut L).range A ≤ dA.ker := by
      rw [ggAutomizer, Subgroup.closure_le]
      intro ψ hψ
      exact hgenA ψ hψ
    exact hle (hgen ▸ Subgroup.subset_closure ⟨i, rfl⟩)
  have hii : α i (h i) = 2 := by
    rw [hpair i i, hC.1 i]
    norm_num
  have hrefl : ggLin (p := 5) ι (φ i) = Module.reflection hii := by
    ext w
    rw [hlin i w, Module.reflection_apply]
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hdet : (ggLin (p := 5) ι (φ i)).det = -1 := by
    rw [hrefl]
    exact Module.det_reflection hii
  rw [← ggDetAut_eq_det_ggLin hA ι (φ i)] at hdet
  have h3 : dA (φ i) = -1 := hdet
  rw [hφi] at h3
  have h4 : (1 : ZMod 5) = -1 := by simpa using congrArg Units.val h3
  have : Fact (2 < 5) := ⟨by norm_num⟩
  exact ZMod.neg_one_ne_one h4.symm

theorem ggTorusWNormSC_recipe_E8_five_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 5 ∣ Nat.card K + 1) :
    GGTorusWNormSC 5 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ' _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen s hs
  obtain ⟨e, -, E, hE, hcard, hSC, hAE⟩ :=
    exists_e8_model_of_tableB ψ A ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩
  by_cases htor : ExcFramesHalf.IsToralSubgroup .E8 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E8 K).subtype))
  · obtain ⟨g, hg, hgt⟩ := htor
    have hgt' : ∀ x : E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g ∈ torusGroup .E8 (AlgebraicClosure K) :=
      fun x => hgt _ (Subgroup.mem_map_of_mem _ x.2)
    choose a ha using fun x : E => exists_rootDiagUnit_eq_of_mem_torusGroup (hgt' x)
    have ha' : ∀ x : E, rootDiagUnit .E8 (a x) = g⁻¹ * baseChangeGL
        (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup .E8 K) : ModGL .E8 K) * g :=
      fun x => (ha x).symm
    have hexp : ∀ x j, a x j ^ 5 = 1 := by
      intro x j
      have hpow : rootDiagUnit .E8 (a x ^ 5) = rootDiagUnit .E8 1 := by
        rw [show rootDiagUnit .E8 (a x ^ 5) = rootDiagUnit .E8 (a x) ^ 5 from
          (rootDiagUnitHom .E8 (AlgebraicClosure K)).map_pow (a x) 5, ha' x, rootDiagUnit_one]
        rw [show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E8 K) : ModGL .E8 K) * g =
          (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E8 K) : ModGL .E8 K)) by simp only [MulAut.conj_apply, inv_inv],
          ← map_pow, ← map_pow]
        have hx5 : ((x : adjointGroup .E8 K) : ModGL .E8 K) ^ 5 = 1 := by
          rw [← Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]
        rw [hx5, map_one, map_one]
      exact congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hpow) j
    have hrank : 25 < (Set.range a).ncard :=
      lt_of_lt_of_le (by norm_num) ((hcard ▸ h3).trans (card_le_ncard_range E a ha'))
    have hcent : familyCentralizer .E8 (AlgebraicClosure K) a =
        familyGroup (K := AlgebraicClosure K) a := CFSG.HardMathSupport.C14Lattice.familyCentralizer_eq_familyGroup_E8_five a hexp hrank
    exact ggWNormConcl_E8_plus_of_toral (by decide) hq A e E hE hSC hAE hg a ha' hcent ι φ h α
      hgen hs
  · exact (false_of_nonToral_datum A hA e E hE (hcard ▸ h3) hAE htor ι φ h α M C hM hC hpair
      hlin hgen).elim

theorem largeEvenLabelAll_wnorm_E8_five_plus {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hq : 5 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 5 R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_five_plus (by rw [hK]; exact hq)

end CFSG.StandardType.E8FivePlusWNorm

end

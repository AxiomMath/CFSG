module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public section

namespace CFSG.StandardType.RCKBand

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.ExcMaxToral CFSG.LieType.Universal
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem isToral_ggFixGp_of_maxElem
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) {f : ℕ} (hf : 1 ≤ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h4 : 4 ≤ excDegCount (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)))
    {A : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) (hel : IsElemAbelian p A)
    (hcard : p ^ excDegCount (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) ≤ Nat.card A) :
    IsToralSubgroup (langTag t) GGL A := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let K := GaloisField 2 f
  letI : Algebra K GGL := (ggRatEmb f).toAlgebra
  have hcardK : Nat.card K = 2 ^ f := GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp hf)
  have hτ : langTag t = .F4 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  have hΦ : ggPhi t f = Units.map (entrywiseHom (ggFrobT f)) := by
    rcases ht with rfl | rfl | rfl <;> rfl
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card K := fun c => by
    rw [ggFrobT_apply, hcardK]
  have hbij : Function.Bijective (ggFrobT f) := by
    show Function.Bijective (iterateFrobenius GGL 2 f)
    exact bijective_iterateFrobenius GGL 2 f
  have hfixed := CFSG.HardMathSupport.C14ExcBridgeU.fixed_eq_map (K := K) (L := GGL)
    (τ := langTag t) (Or.inr hτ) (ggFrobT f) hFr hbij
  have hggFix : ggFixGp t f =
      (adjointGroup (langTag t) K).map (baseChangeGL (algebraMap K GGL)) := by
    unfold ggFixGp
    rw [hΦ]
    exact hfixed
  let fBC : ModGL (langTag t) K →* ModGL (langTag t) GGL := baseChangeGL (algebraMap K GGL)
  have hfBCinj : Function.Injective fBC := baseChangeGL_injective (algebraMap K GGL)
  let F : adjointGroup (langTag t) K →* ModGL (langTag t) GGL :=
    fBC.comp (adjointGroup (langTag t) K).subtype
  have hFinj : Function.Injective F := hfBCinj.comp Subtype.val_injective
  let E : Subgroup (adjointGroup (langTag t) K) := A.comap F
  have hEel : IsElemAbelian p E := by
    refine ⟨(isMulCommutative_iff).2 ?_, ?_⟩
    · intro x y
      apply Subtype.ext
      change (x : adjointGroup (langTag t) K) * (y : adjointGroup (langTag t) K) =
        (y : adjointGroup (langTag t) K) * (x : adjointGroup (langTag t) K)
      apply hFinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_iff.mp hel.1) ⟨F x, show F x ∈ A from x.2⟩
          ⟨F y, show F y ∈ A from y.2⟩)
    · intro x hx
      apply hFinj
      rw [map_pow, map_one]
      exact hel.2 (F x) (show F x ∈ A from hx)
  have hAle : A ≤ F.range := by
    intro a ha
    have h1 : a ∈ (adjointGroup (langTag t) K).map fBC := by
      rw [← hggFix]; exact hA ha
    rw [Subgroup.mem_map] at h1
    obtain ⟨e, he, heq⟩ := h1
    rw [MonoidHom.range_eq_map, Subgroup.mem_map]
    exact ⟨⟨e, he⟩, trivial, heq⟩
  have hmap : E.map F = A := by
    rw [show E = A.comap F from rfl]
    exact Subgroup.map_comap_eq_self hAle
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hFinj).symm
  have h4' : 4 ≤ excDegCount (langTag t) (orderOf (Nat.card K : ZMod p)) := by
    rw [hcardK]; exact h4
  have hcardE : p ^ excDegCount (langTag t) (orderOf (Nat.card K : ZMod p)) ≤ Nat.card E := by
    rw [hEcard, hcardK]
    exact hcard
  obtain ⟨Fr, -, D, -, -, -, hDtor, -⟩ :=
    adjointMaxElemToral (langTag t) K p (inferInstance : Finite K)
      (inferInstance : CharP K 2) hp hp2 h4' E hEel hcardE
  let j : AlgebraicClosure K →+* GGL :=
    (IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := GGL) :
      AlgebraicClosure K →ₐ[K] GGL).toRingHom
  have hj : j.comp (algebraMap K (AlgebraicClosure K)) = algebraMap K GGL := by
    ext c
    exact AlgHom.commutes
      (IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := GGL)) c
  have hgmem : baseChangeGL j D.g0 ∈ adjointGroup (langTag t) GGL :=
    baseChangeGL_mem_adjointGroup j D.g0_mem
  refine ⟨baseChangeGL j D.g0, hgmem, fun x hx => ?_⟩
  have hxA : x ∈ (adjointGroup (langTag t) K).map fBC := by
    rw [← hggFix]; exact hA hx
  obtain ⟨e, he, heq⟩ := hxA
  let e0 : adjointGroup (langTag t) K := ⟨e, he⟩
  have he0E : e0 ∈ E := by
    rw [show E = A.comap F from rfl, Subgroup.mem_comap]
    change fBC e ∈ A
    rw [heq]
    exact hx
  have hDT : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e0 : ModGL (langTag t) K) * D.g0 ∈ torusGroup (langTag t) (AlgebraicClosure K) := by
    have h : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e0 : ModGL (langTag t) K) * D.g0 ∈
        CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ := hDtor e0 he0E
    exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp h).1
  have hpush : baseChangeGL j
      (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e0 : ModGL (langTag t) K) * D.g0) ∈ torusGroup (langTag t) GGL :=
    CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup j hDT
  have hconj : (baseChangeGL j D.g0)⁻¹ * x * baseChangeGL j D.g0 =
      baseChangeGL j (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e : ModGL (langTag t) K) * D.g0) := by
    rw [← heq]
    rw [show fBC e = baseChangeGL j
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) e) from by
      rw [CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hj]]
    rw [← map_inv, map_mul, map_mul]
  rw [hconj]
  exact hpush

theorem isToral_ggFixGp_E8_five_four
    {f : ℕ} (hf : 1 ≤ f) (hd : orderOf ((2 ^ f : ℕ) : ZMod 5) = 4)
    {A : Subgroup (ModGL (langTag .E8) GGL)} (hA : A ≤ ggFixGp .E8 f) (hel : IsElemAbelian 5 A)
    (hcard : 5 ^ 4 ≤ Nat.card A) : IsToralSubgroup (langTag .E8) GGL A := by
  have hc : excDegCount (langTag .E8) (orderOf ((2 ^ f : ℕ) : ZMod 5)) = 4 := by
    rw [hd]; decide
  exact isToral_ggFixGp_of_maxElem (Or.inr (Or.inr rfl)) hf Nat.prime_five (by norm_num)
    (by rw [hc]) hA hel (by rw [hc]; exact hcard)

end CFSG.StandardType.RCKBand

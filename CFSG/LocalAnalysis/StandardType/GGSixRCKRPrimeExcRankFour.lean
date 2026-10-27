module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
import CFSG.LocalAnalysis.StandardType.GGExcPRankBound

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rckExc_ggFixGp_eq_map_adjoint
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) {f : ℕ} (hf : 1 ≤ f) :
    (letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
     ggFixGp t f =
       (adjointGroup (langTag t) (GaloisField 2 f)).map
         (baseChangeGL (algebraMap (GaloisField 2 f) GGL))) := by
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let K := GaloisField 2 f
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
  unfold ggFixGp
  rw [hΦ]
  exact hfixed

private theorem rckExc_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ}
    {f : G →* H} (hf : Function.Injective f) {A : Subgroup H} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap f) := by
  refine ⟨(isMulCommutative_iff).2 ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    apply hf
    change f ((x : G) * (y : G)) = f ((y : G) * (x : G))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp hA.1) ⟨f x, show f x ∈ A from x.2⟩
        ⟨f y, show f y ∈ A from y.2⟩)
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hA.2 (f x) (show f x ∈ A from hx)

theorem rckExc_card_le_of_adjoint
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) {f p B : ℕ} (hf : 1 ≤ f)
    (hB : ∀ E : Subgroup (adjointGroup (langTag t) (GaloisField 2 f)), IsElemAbelian p E →
      Nat.card E ≤ B)
    {A : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) (hel : IsElemAbelian p A) :
    Nat.card A ≤ B := by
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  let fBC : ModGL (langTag t) (GaloisField 2 f) →* ModGL (langTag t) GGL :=
    baseChangeGL (algebraMap (GaloisField 2 f) GGL)
  let F : adjointGroup (langTag t) (GaloisField 2 f) →* ModGL (langTag t) GGL :=
    fBC.comp (adjointGroup (langTag t) (GaloisField 2 f)).subtype
  have hFinj : Function.Injective F :=
    (baseChangeGL_injective (algebraMap (GaloisField 2 f) GGL)).comp Subtype.val_injective
  have hAle : A ≤ F.range := by
    intro a ha
    have h1 : a ∈ (adjointGroup (langTag t) (GaloisField 2 f)).map fBC := by
      rw [← rckExc_ggFixGp_eq_map_adjoint ht hf]
      exact hA ha
    rw [Subgroup.mem_map] at h1
    obtain ⟨e, he, heq⟩ := h1
    rw [MonoidHom.range_eq_map, Subgroup.mem_map]
    exact ⟨⟨e, he⟩, trivial, heq⟩
  let E : Subgroup (adjointGroup (langTag t) (GaloisField 2 f)) := A.comap F
  have hmap : E.map F = A := by
    rw [show E = A.comap F from rfl]
    exact Subgroup.map_comap_eq_self hAle
  have hEel : IsElemAbelian p E := rckExc_isElemAbelian_comap hFinj hel
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hFinj).symm
  have := hB E hEel
  rwa [hEcard] at this

theorem rckExcRankFour_holds :
    ∀ t : StatedLieTag, (t = .F4 ∨ t = .E7 ∨ t = .E8) → ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ A : Subgroup (ModGL (langTag t) GGL), A ≤ ggFixGp t f → IsElemAbelian p A →
        p ^ 4 ≤ Nat.card A →
        4 ≤ ExcMaxToral.excDegCount (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) := by
  intro t ht f hf p hp hp2 A hA hel h4
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hcardK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  by_contra hlt
  have hd : ExcMaxToral.excDegCount (langTag t)
      (orderOf (Nat.card (GaloisField 2 f) : ZMod p)) ≤ 3 := by
    rw [hcardK]
    omega
  have hτ : langTag t = .E7 ∨ langTag t = .E8 ∨ langTag t = .F4 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  have hb := rckExc_card_le_of_adjoint ht (p := p) (B := p ^ 3) hf
    (fun E hE => ExcMaxToral.excPRankBound hτ (GaloisField 2 f) hp hp2 hd E hE) hA hel
  have h43 : p ^ 4 ≤ p ^ 3 := h4.trans hb
  exact absurd h43 (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

end CFSG.StandardType.RCKRP

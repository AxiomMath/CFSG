module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public noncomputable section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.RCKK1IIISp
open CFSG.Open (StatedSp)

theorem fixedSpBlockAt_of_native_PSp_two_of_jRow_III
    {X : Type} [Group X] [Finite X] {K J : Subgroup X} {d : X} {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ^ p = 1)
    (φ : (ggU .PSp n 1).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n 1).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hdID : GGPsiInnerDiag (ggU .PSp n 1).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : FixedSpBlockAt K J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs, _, hsodd, ε, hε, ⟨e, he, heε, hcase⟩, J', hJ'comp, hJ'map⟩ :=
    RCKRP.rckF1_PSp hp hp2 hdp (by decide : 1 ≤ (1 : ℕ)) φ hφr hφk hdN hdID hJ
  let S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 1)) := {s}
  have hSU : ∀ a ∈ S, a ∈ StatedSp n (GaloisField 2 1) := by
    intro a ha
    have ha' : a = s := ha
    subst a
    exact hs
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a = s := ha
    have hb' : b = s := hb
    subst a
    subst b
    exact Commute.refl _
  have hodd : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    have ha' : a = s := ha
    subst a
    exact hsodd
  have hcard : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by decide)
  have hfe : ¬ GGSixLSevenFieldExtCase (J'.map φ) .PSp 1 := by
    rw [hJ'map]
    exact not_fieldExtCase_of_row_III hrow (by decide)
  have heq : e = ε := by
    rcases hcase with hself | ⟨hne, hpair, _⟩
    · exact hself
    · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 2
      · have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)).det := by
          have hneg : (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 1)) = 1 := by
            ext i j
            rw [Matrix.neg_apply, CharTwo.neg_eq]
          rw [hneg]
          simpa only [Matrix.J, hneg] using Matrix.isUnit_det_J (Fin n) (GaloisField 2 1)
        have hsG := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hs
        exact False.elim (hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 hG hsG he hd))
      · exact False.elim (hfe (ggSixLSevenFieldExtCase_PSp n 1 (GaloisField 2 1) hcard φ hφk
          S hSU hS hodd hε hJ'comp he heε (Or.inr ⟨hne, by omega⟩)))
  have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4 := by
    by_contra hd
    exact hfe (ggSixLSevenFieldExtCase_PSp n 1 (GaloisField 2 1) hcard φ hφk
      S hSU hS hodd hε hJ'comp he heε (Or.inl ⟨heq, by omega⟩))
  have hadj : formAdj (RingHom.id (GaloisField 2 1))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 1)) e = e := by
    rw [heq]
    exact hε.2.2.2.1
  have hZ : Subgroup.center (ggU .PSp n 1).K = ⊥ := by
    change Subgroup.center (StatedSp n (GaloisField 2 1)) = ⊥
    exact CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
  have hφinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).mp (le_antisymm (hφk.trans hZ.le) bot_le)
  let φK : (ggU .PSp n 1).K →* K := φ.codRestrict K fun x => by
    rw [← hφr]
    exact ⟨x, rfl⟩
  have hφKinj : Function.Injective φK := by
    intro x y hxy
    exact hφinj (congrArg Subtype.val hxy)
  have hφKsurj : Function.Surjective φK := by
    intro k
    have hk : (k : X) ∈ φ.range := by rw [hφr]; exact k.property
    obtain ⟨x, hx⟩ := hk
    exact ⟨x, Subtype.ext hx⟩
  let eK : (ggU .PSp n 1).K ≃* K := MulEquiv.ofBijective φK ⟨hφKinj, hφKsurj⟩
  let η : K ≃* SpG n := eK.symm
  have hηφ : φ.comp η.toMonoidHom = K.subtype := by
    ext k
    exact congrArg Subtype.val (eK.apply_symm_apply k)
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJη : (J.subgroupOf K).map η.toMonoidHom = J' := by
    have hηφpoint (y : K) : φ (η y) = (y : X) := DFunLike.congr_fun hηφ y
    ext x
    change (∃ y : K, (y : X) ∈ J ∧ η y = x) ↔ x ∈ J'
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : φ (η y) ∈ J := by rw [hηφpoint]; exact hy
      rw [← hJ'map] at hy'
      obtain ⟨z, hz, hzx⟩ := hy'
      rw [← hφinj hzx]
      exact hz
    · intro hx
      have hxK : φ x ∈ K := by rw [← hφr]; exact ⟨x, rfl⟩
      let y : K := ⟨φ x, hxK⟩
      have hy : (y : X) ∈ J := by rw [← hJ'map]; exact ⟨x, hx, rfl⟩
      refine ⟨y, hy, ?_⟩
      apply hφinj
      exact hηφpoint y
  refine ⟨n, η, S, e, hS, he, hadj, ?_, ?_⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 2
    · exact Or.inl hd
    · exact Or.inr ⟨hSU, hodd, by omega, hdeg⟩
  · rw [hJη, heq]
    exact hJ'comp

end CFSG.StandardType.RCKC1

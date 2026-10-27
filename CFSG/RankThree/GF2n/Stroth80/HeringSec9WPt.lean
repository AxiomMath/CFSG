module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RW
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneSL
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9WPts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem slNat_or_omegaPlus (h310 : Stroth310Statement) (hT : Sec97OneTypesNoSL)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) : SLNat hc x ∨ OmegaPlusNat hc x 2 := by
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have ha := one_part_a hc hsplit h4 hxL hx.2
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans ha
  have hRne := Rt_ne_LB_of_Y_le hc hsplit h4 hYR
  rcases h310 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen x hxL hxQ with hRL | ⟨K, fK,
    finK, hK, hcls⟩
  · exact absurd hRL hRne
  · obtain ⟨hSp2, hOm3, hOmM⟩ := hT G M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
    rcases hcls with ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, b, c, hm, hirr, hnat⟩
    · exact Or.inl ⟨K, fK, finK, hK, m, hm, hnat⟩
    · by_cases hm1 : m = 1
      · subst hm1
        obtain ⟨K', fK', finK', hK', hnat'⟩ : SLMNat hc x 2 :=
          HS6.slMNat_of_alt (Or.inr ⟨rfl, ⟨K, fK, finK, hK, hnat⟩⟩)
        exact Or.inl ⟨K', fK', finK', hK', 2, le_rfl, hnat'⟩
      · exact absurd ⟨K, fK, finK, hK, hnat⟩ (hSp2 m (by omega))
    · by_cases hm2 : m = 2
      · subst hm2
        exact Or.inr ⟨K, fK, finK, hK, hnat⟩
      · exact absurd ⟨K, fK, finK, hK, hnat⟩ (hOm3 m (by omega))
    · exact absurd ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ (hOmM m hm)

theorem wpoint_of_dichotomy (h95 : Stroth95Statement) (hS4 : Sec4Statement)
    (hOne : Sec97OneStatement) (h57 : Sec57WStatement) (h96 : Sec96WStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B)
    (hxQ : x ∉ Q) (hdich : SLNat hc x ∨ OmegaPlusNat hc x 2) : WPointConcl M Q Z B x := by
  have hs5 : Sec5Hyp hc n x :=
    ⟨hs.toSec5.width, hs.toSec5.n_gt, hs.toSec5.noA2, hs.toSec5.gen, hxL, hxQ⟩
  rcases hdich with hSL | hOm
  · exact h57 G M Q Z B hc n x hs5 hSL
  · have hsx : Sec9Hyp hc n x := ⟨hs5, hOm, hs.large⟩
    obtain ⟨X', Y', hsp'⟩ := h95 G M Q Z B hc n x hsx
    have h4' := hS4 G M Q Z B hc n x hsx X' Y' hsp'
    have h1' := hOne G M Q Z B hc n x hsx X' Y' hsp' h4'
    exact h96 G M Q Z B hc n x hsx X' Y' hsp' h4' h1'

theorem exists_swapped_point (hc : Ctx M Q Z B) (hRT : RootTrans M Q Z B) {F P : Subgroup G}
    {g : G} (hgB : conjSubgroup g B = Z) (hgQ : conjSubgroup g Q = QB F)
    (hgQB : conjSubgroup g (QB B) = Q) (hP : IsConjB M B P) {d : G} (hdP : d ∈ P)
    (hxL : g⁻¹ * d * g ∈ LB M Q B) (hxQ : g⁻¹ * d * g ∉ Q)
    (hW : WPointConcl M Q Z B (g⁻¹ * d * g)) :
    ∃ C' : Subgroup G, IsConjB M B C' ∧ C' ≤ QB F ∧ C' ≤ QB P := by
  obtain ⟨m', hm', rfl⟩ := hP
  obtain ⟨g₀, hg₀⟩ := hc.conj
  set x : G := g⁻¹ * d * g with hx
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hx1 : x ≠ 1 := fun h => hxQ (h ▸ Q.one_mem)
  set P' : Subgroup G := conjSubgroup g⁻¹ (conjSubgroup m' B) with hP'
  have hP'Z : P' = conjSubgroup (g⁻¹ * m' * g₀) Z := by
    rw [hP', hg₀, ← conjSubgroup_mul, ← conjSubgroup_mul]
  have hxP' : x ∈ P' := by
    rw [hP', mem_conjSubgroup]
    simpa [hx, mul_assoc] using hdP
  have hs : Sit M Q Z P' x := ⟨hc.hyp, ⟨_, hP'Z⟩, hxP', hx1, hxM, hxQ⟩
  have hb : ∃ g' : G, ∃ b ∈ B, g' * x * g'⁻¹ = b := by
    have hdb : m'⁻¹ * d * m' ∈ B := mem_conjSubgroup.mp hdP
    refine ⟨m'⁻¹ * g, m'⁻¹ * d * m', hdb, ?_⟩
    simp only [hx]
    group
  have hinv : conjSubgroup g⁻¹ Q = QB B := by
    rw [← hgQB, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hP'Q : P' ≤ QB B := by
    have hPQ : conjSubgroup m' B ≤ Q := (hc.conj_of_mem hm').le
    rw [← hinv]
    exact Subgroup.map_mono hPQ
  have hBP' : B ≤ QB P' :=
    (IsZConjugate.le_QB_iff hc.hyp ⟨_, hP'Z⟩ ⟨g₀, hg₀⟩).mpr hP'Q
  have hBx : B ≤ QB (Subgroup.zpowers x) := hBP'.trans (QB_le_QB_zpowers hs)
  obtain ⟨C, hCB, hCne, hCle⟩ := hW hb hBx
  have hCQ : C ≤ Q := hCle.trans (inf_le_left.trans inf_le_left)
  have hCx : C ≤ QB (Subgroup.zpowers x) := hCle.trans (inf_le_left.trans inf_le_right)
  have hCQB : C ≤ QB B := hCle.trans inf_le_right
  have hCZ : IsZConjugate Z C := isZConjugate_of_isConjB hc hCB
  have hginv : ∀ S : Subgroup G, conjSubgroup g (conjSubgroup g⁻¹ S) = S := fun S => by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  refine ⟨conjSubgroup g C, ?_, ?_, ?_⟩
  · have hle : conjSubgroup g C ≤ Q := by
      rw [← hgQB]
      exact Subgroup.map_mono hCQB
    have hne : conjSubgroup g C ≠ Z := by
      intro h
      apply hCne
      rw [← hgB] at h
      exact conjSubgroup_inj.mp h
    obtain ⟨m, hm, hmB⟩ := hRT (conjSubgroup g C)
      ⟨hc.hyp, (hCZ.conj g), hle, hne⟩
    exact ⟨m, hm, hmB.symm⟩
  · rw [← hgQ]
    exact Subgroup.map_mono hCQ
  · have hCP' : C ≤ QB P' := root_le_QB_of_le_QB_zpowers hs hCZ hCx
    have : conjSubgroup g C ≤ conjSubgroup g (QB P') := Subgroup.map_mono hCP'
    rw [hP', QB_conj, hginv] at this
    exact this

end HS9

end CFSG.RankThree.GF2n.Stroth80

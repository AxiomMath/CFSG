module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Ext
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Mono

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Matrix Subgroup CFSG.Open CFSG.RepresentationTheory
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.RankThree.SubgroupLists (translate IsTransitiveMonomial)

section K323


theorem k323_holds : K323 := by
  intro p _ hp2 G hirr Z hZ X hXG hXZ hXcyc hXcard
  by_contra hpG
  have hpp : p.Prime := Fact.out
  have hirrG := K322Rows.irreducible_of_irredGL3 hirr
  obtain ⟨m, hm0, hnm, -, hnp, hpn⟩ := K323B.arith hp2
  obtain ⟨g, hgX, hgord, hgpow⟩ := K323B.cyclic_data hXcyc
  rw [hXcard] at hgord
  obtain ⟨z, hz0, hzZ, hZz⟩ := K323B.exists_nonzero_of_finrank_one hZ
  have hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z :=
    fun y hy => hXZ y hy z hzZ
  have hfr := K323B.frobenius hgX hgord hnp hpn hgpow hz0 hXz
  obtain ⟨hxord, hx4, hxX, hfix⟩ := K323B.fixed_sq hgX hm0 hnm hgord hfr hzZ hZz hXZ
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hgpow a ha
    obtain ⟨j, rfl⟩ := hgpow b hb
    exact ((Commute.pow_pow_self g i j).eq)
  set x : GL (Fin 3) (ZMod p) := g ^ m with hxdef
  have hxG : x ∈ G := hXG hxX
  by_cases hp3 : p = 3
  · subst hp3
    exact false_of_irreducible_threePrime hirr hpG hxG hxord hZ hfix
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hpp) (by norm_num)
    · exact h
  have ht2 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
  have htG : x ^ 2 ∈ G := G.pow_mem hxG 2
  have hK : LinearMap.ker (Matrix.toLin' (((x ^ 2 : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) - 1)) = Z := by
    ext v
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    exact Set.ext_iff.1 hfix v
  have hfixK : Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin'
      (((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1))) = 1 := by
    rw [hK, hZ]
  have hZne : ¬ (Z = ⊥ ∨ Z = ⊤) := by
    rintro (h | h)
    · rw [h, finrank_bot] at hZ
      exact zero_ne_one hZ
    · rw [h, finrank_top, Module.finrank_fin_fun] at hZ
      norm_num at hZ
  obtain ⟨H, hHG, hnorm, hHirr, hcase⟩ :=
    CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hp2 hirrG
  have hHp : ¬ p ∣ Nat.card H := fun h => hpG (h.trans (Subgroup.card_dvd_of_le hHG))
  rcases hcase with hSL | ⟨M, hMt, hMdet, hΩ⟩ | ⟨⟨e⟩, -, hprod, hint⟩ | ⟨⟨e⟩, h7⟩ |
    ⟨hperf, hZ3, ⟨e6⟩, h30⟩ | ⟨hcyc, -, -⟩ | ⟨h27, hex, h31⟩ | ⟨rfl, hmono⟩
  ·
    exact hHp (by rw [hSL]; exact K322Rows.p_dvd_card_statedSL)
  ·
    exact hHp (by rw [hΩ]; exact K322Rows.p_dvd_card_omegaGL hp5 hMt hMdet)
  ·
    have hc := K322Rows.central_sq_of_alt5 hHG e hprod hint hxG hx4
    apply hZne
    refine hirr Z fun g hg w hw => ?_
    have hw' : ((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w = w := by
      have : w ∈ (Z : Set (Fin 3 → ZMod p)) := hw
      rw [← hfix] at this
      exact this
    have hgoal : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w ∈ (Z : Set (Fin 3 → ZMod p)) := by
      rw [← hfix]
      show ((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
        ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hc g hg, Units.val_mul, ← Matrix.mulVec_mulVec,
        hw']
    exact hgoal
  ·
    exact K323A.false_of_gl32 hp2 hXG hnorm hHirr e h7 hz0 hXz hXcard
  ·
    exact K323A.false_of_threeCoverA6 hp2 hXG hnorm hHirr hperf e6 h30 hz0 hXz hXcyc hXcard
  ·
    obtain ⟨h, hh⟩ := hcyc.exists_generator
    have hHz : H = Subgroup.zpowers (h : GL (Fin 3) (ZMod p)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hh ⟨y, hy⟩)
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have := congrArg Subtype.val hk
        simpa using this
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact H.zpow_mem h.2 k
    have hmem : x ^ 2 * (h : GL (Fin 3) (ZMod p)) * (x ^ 2)⁻¹ ∈
        Subgroup.zpowers (h : GL (Fin 3) (ZMod p)) := hHz ▸ hnorm _ htG _ h.2
    obtain ⟨m', hm'⟩ := mem_powers_iff_mem_zpowers.2 hmem
    rw [hHz] at hHirr
    exact K322Lin.false_of_cyclic_involution hHirr ht2 hm'.symm hfixK
  ·
    exact K323E.false_of_extraspecial27 hp5 hXG hnorm hHirr h27 hex h31 hz0 hXz hXab hfr hXcard
  ·
    exact K323Mono.false_of_monomial hp5 hXG hmono hgX hgord rfl hx4 hxG hZ hfix hXZ

end K323

end CFSG.LocalAnalysis.UniquenessCase.UCK

module

public import CFSG.RankThree.PartTwo.Sec4.Statements430L3
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Group
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3SL
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3PSL
import CFSG.RankThree.PartTwo.Sec4.Item417ResProof
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec11.Item119Used
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage projSL)


theorem zpowers_subgroupOf {G : Type*} [Group G] {N : Subgroup G} {x : G} (hx : x ∈ N) :
    (Subgroup.zpowers x).subgroupOf N = Subgroup.zpowers (⟨x, hx⟩ : N) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩

section Certs


theorem step430L3_holds : Step430L3 := by
  intro G _ _ hG hEF hθ A hA L hL a hCA ha3 c hcA hca B hsup hinf hWc hWB R hR hR1 hRc hcase
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hnofield : ¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField :=
    fun h => hcon (Or.inl h)
  obtain ⟨hAab, h27⟩ := id hA
  obtain ⟨hRL, hR2, hAR⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  have hAE : A ∈ partTwoE G := ⟨hAab, h27, R, hR1, hR2, hAR⟩
  have hAF : A ∈ partTwoF G := hEF ▸ hAE
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hAab, fun ⦃X⦄ hX hAX => (hAF.2.1 X hX hAX).le⟩
  have haA : a ∈ A := (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have hmodel : IsSLThreePi L ∨ ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi L p e := by
    rcases hcase with ⟨p, hp, -, e, he, hSL | hPSL⟩ | ⟨⟨n, hn0, hnev, ⟨⟨φ⟩, -⟩ | ⟨hSL, -⟩⟩, -⟩
    · exact Or.inl ⟨_, hSL⟩
    · exact Or.inr ⟨p, e, hp, he, hPSL⟩
    · refine Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn0, Or.inl ⟨?_, ⟨φ⟩⟩⟩
      obtain ⟨k, rfl⟩ := hnev
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    · exact Or.inl ⟨_, hSL⟩
  have hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 := by
    intro z hz hzc
    have hzZ : (⟨z, hz⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (hzc m m.2).symm
    rcases hmodel with hSL | ⟨p, e, hp, he, hPSL⟩
    · obtain ⟨π, p, f, K, _, hK, hq, -, ⟨eL⟩⟩ := exists_slPi_model hSL hL.1
      have hcen : eL ⟨z, hz⟩ ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨m, rfl⟩ := eL.surjective s
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hzZ m)]
      have h3 := pow_three_eq_one_of_mem_center hK hq hcen
      have : (⟨z, hz⟩ : L) ^ 3 = 1 := eL.injective (by rw [map_pow, h3, map_one])
      have := congrArg Subtype.val this
      simpa using this
    · obtain ⟨π, K, _, hK, hq, -, ⟨eL⟩⟩ := exists_pslPi_model he hPSL hL.1
      have : Group.IsPerfect L := hL.1.1
      have := isPerfect_projImage_of_equiv eL
      rw [center_eq_bot_proj hK hq eL, Subgroup.mem_bot] at hzZ
      have : z = 1 := congrArg Subtype.val hzZ
      rw [this, one_pow]
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isComponent hL hZ hRL hR2 hAR hR1
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  set L' : Subgroup N := L.subgroupOf N with hL'def
  have hL'n : L'.Normal := Subgroup.normal_in_normalizer
  let eL : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLN
  have hLq' : IsQuasisimple L' := LocalCores.isQuasisimple_of_mulEquiv eL.symm hL.1
  have hA' : Maximal (fun B : Subgroup N => CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf N) :=
    Sec11.maximal_subgroupOf_of_le (fun B hB hAB => hAmax.eq_of_ge hB hAB) hAmax.prop hAL
  have hcardA' : Nat.card (A.subgroupOf N) = 27 := by
    rw [← h27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have ha3' : orderOf (⟨a, hAL haA⟩ : N) = 3 := by rw [Subgroup.orderOf_mk]; exact ha3
  have hAc' := Res417.inf_centralizer_subgroupOf hCA (hAL haA)
  have hcN : c ∈ N := hAL hcA
  have hcA' : (⟨c, hcN⟩ : N) ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.mpr hcA
  have hca' : (⟨c, hcN⟩ : N) ∉ Subgroup.zpowers (⟨a, hAL haA⟩ : N) := by
    rw [← zpowers_subgroupOf (hAL haA), Subgroup.mem_subgroupOf]
    exact hca
  have hBN : B ≤ N := (le_sup_right.trans hsup.le).trans hAL
  have hzcN : Subgroup.zpowers c ≤ N := Subgroup.zpowers_le.mpr hcN
  have hsup' : Subgroup.zpowers (⟨c, hcN⟩ : N) ⊔ B.subgroupOf N = A.subgroupOf N := by
    rw [← zpowers_subgroupOf hcN, ← Subgroup.subgroupOf_sup hzcN hBN, hsup]
  have hinf' : Subgroup.zpowers (⟨c, hcN⟩ : N) ⊓ B.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [← zpowers_subgroupOf hcN, Subgroup.mem_subgroupOf] at hx1
    have : (x : G) ∈ Subgroup.zpowers c ⊓ B := ⟨hx1, Subgroup.mem_subgroupOf.mp hx2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hnorm : ∀ X : Subgroup G, X ≤ N → ∀ n : N,
      n ∈ Subgroup.normalizer ((X.subgroupOf N : Subgroup N) : Set N) ↔
        (n : G) ∈ Subgroup.normalizer (X : Set G) := fun X hX n => by
    rw [← Subgroup.subgroupOf_normalizer_eq hX]
    exact Subgroup.mem_subgroupOf
  have hWc' : Subgroup.normalizer ((A.subgroupOf N : Subgroup N) : Set N) ≤
      Subgroup.normalizer ((Subgroup.zpowers (⟨c, hcN⟩ : N) : Subgroup N) : Set N) := by
    intro n hn
    rw [← zpowers_subgroupOf hcN, hnorm _ hzcN]
    exact hWc ((hnorm A hAL n).mp hn)
  have hWB' : Subgroup.normalizer ((A.subgroupOf N : Subgroup N) : Set N) ≤
      Subgroup.normalizer ((B.subgroupOf N : Subgroup N) : Set N) := by
    intro n hn
    rw [hnorm _ hBN]
    exact hWB ((hnorm A hAL n).mp hn)
  have hRN : R ≤ N := hRL.trans hLN
  have hRL' : R.subgroupOf N ≤ L' := fun t ht => Subgroup.mem_subgroupOf.mpr
    (hRL (Subgroup.mem_subgroupOf.mp ht))
  have hR2' : IsPGroup 2 (R.subgroupOf N) := hR2.comap_of_injective N.subtype N.subtype_injective
  have hAR' : A.subgroupOf N ≤ Subgroup.normalizer ((R.subgroupOf N : Subgroup N) : Set N) :=
    fun x hx => (hnorm R hRN x).mpr (hAR (Subgroup.mem_subgroupOf.mp hx))
  have hRc' : ⁅R.subgroupOf N, Subgroup.zpowers (⟨c, hcN⟩ : N)⁆ = R.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hRN,
      MonoidHom.map_zpowers]
    exact hRc
  have hR1' : R.subgroupOf N ≠ ⊥ := by
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro t ht
    have h1 : (⟨t, hRN ht⟩ : N) ∈ R.subgroupOf N := Subgroup.mem_subgroupOf.mpr ht
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hLL : L'.map N.subtype = L := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLN]
  have hnofield' : ∀ σ ∈ A.subgroupOf N, ¬ InducesStdKind L' σ .field := by
    intro σ hσ hσf
    have h1 := Sec13.inducesStdKind_sub N L' hσf
    rw [hLL] at h1
    exact hnofield ⟨σ, Subgroup.mem_subgroupOf.mp hσ, Or.inl h1⟩
  have hcube : ∀ x ∈ A.subgroupOf N,
      (⟨x, mem_normalizer_of_normal x⟩ : Subgroup.normalizer (L' : Set N)) ^ 3 = 1 :=
    fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact hA'.1.2 x hx)
  rcases hmodel with ⟨q, hSL⟩ | ⟨p, e, hp, he, hPSL⟩
  ·
    have hSL' : IsSLThreePi L' := ⟨q, Res417.isSLThreePiAt_congr eL hSL⟩
    obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hSL' hLq'
    have hθ₁ := aschbacherSolvableCore_eq_bot_of_slPi hK hq hLq' e
    have : Group.IsPerfect L' := hLq'.1
    have hpgl : ∀ x ∈ A.subgroupOf N, ∃ y, IsPGLAt e x y := by
      intro x hx
      rcases slAct_pgl_or_field hK hq2 hθ₁ e _ (hcube x hx) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield' x hx hk).elim
    exact false_of_slPi hK hq hLq'.1 e hA' hcardA' ha3' hAc' hpgl hnofield' hcA' hca' hsup' hinf'
      hWc' hWB' hRL' hR2' hAR' hRc' hR1'
  ·
    have hiso' : IsoLThreePi L' p e := Res417.isoLThreePi_congr eL hPSL
    obtain ⟨π, K, _, hK, hq, hq2, ⟨e₁⟩⟩ := exists_pslPi_model he hiso' hLq'
    have hθ₁ := aschbacherSolvableCore_eq_bot_proj hK hq hLq' e₁
    have : Group.IsPerfect L' := hLq'.1
    have := isPerfect_projImage_of_equiv e₁
    have hpgl : ∀ x ∈ A.subgroupOf N, ∃ y, IsPGLAtP e₁ x y := by
      intro x hx
      rcases pslAct_pgl_or_field hK hq2 hθ₁ e₁ _ (hcube x hx) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield' x hx hk).elim
    exact false_of_pslPi hK hq hLq' e₁ hA' hcardA' ha3' hAc' hpgl hcA' hca' hsup' hinf' hWc' hWB'
      hRL' hR2' hAR' hRc' hR1'

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3

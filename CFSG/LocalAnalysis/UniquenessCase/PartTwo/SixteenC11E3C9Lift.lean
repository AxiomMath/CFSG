module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb43ThreeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_le_normalizer_preBarSub_bot {M V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ stabTil V₀ V) :
    M ≤ normalizer (preBarSub M V₀ V hV ⊥ : Set G) := by
  have hKM : preBarSub M V₀ V hV ⊥ ≤ M := inf_le_left
  have hker : ((actTil V₀ V hV).comp (Subgroup.inclusion hM)).ker =
      (preBarSub M V₀ V hV ⊥).subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_preBarSub]
    constructor
    · intro h1
      refine ⟨x.2, hM x.2, ?_⟩
      rw [Subgroup.mem_bot]
      show actTil V₀ V hV (Subgroup.inclusion hM x) = 1
      exact h1
    · rintro ⟨-, h, h1⟩
      rw [Subgroup.mem_bot] at h1
      show actTil V₀ V hV (Subgroup.inclusion hM x) = 1
      have : Subgroup.inclusion hM x = ⟨(x : G), h⟩ := Subtype.ext rfl
      rw [this, h1]
  haveI : ((preBarSub M V₀ V hV ⊥).subgroupOf M).Normal :=
    hker ▸ (inferInstance :
      ((actTil V₀ V hV).comp (Subgroup.inclusion hM)).ker.Normal)
  exact Subgroup.le_normalizer_of_normal_subgroupOf hKM

theorem s1611e3_exists_X_lift (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp125 D V₀ V) :
    ∃ X : Subgroup G, X ≤ D.M ∧ D.T ≤ X ∧ barSub V₀ V hV X = Mbar D.M V₀ V hV ∧
      ∃ π : ↥X →* ↥(Mbar D.M V₀ V hV), Function.Surjective π ∧ Group.IsSolvable ↥π.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hT : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  set K : Subgroup G := preBarSub D.M V₀ V hV ⊥ with hK
  set Q₀ : Subgroup G := D.T ⊓ K with hQ₀
  set X : Subgroup G := D.M ⊓ normalizer (Q₀ : Set G) with hX
  have hXM : X ≤ D.M := by rw [hX]; exact inf_le_left
  have hXs : X ≤ stabTil V₀ V := hXM.trans hM
  have hKM : K ≤ D.M := by rw [hK]; exact inf_le_left
  have hMN : D.M ≤ normalizer (K : Set G) := by
    rw [hK]; exact s1611e3_le_normalizer_preBarSub_bot hV hM
  have hQ₀T : Q₀ ≤ D.T := by rw [hQ₀]; exact inf_le_left
  have hQ₀K : Q₀ ≤ K := by rw [hQ₀]; exact inf_le_right
  have hT_N : D.T ≤ normalizer (Q₀ : Set G) := by
    have h4 : D.T ≤ normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
      (le_inf (Subgroup.le_normalizer) (D.sylowM.le.trans hMN)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := D.T) (K := K))
    rw [hQ₀]; exact h4
  have hTX : D.T ≤ X := by rw [hX]; exact le_inf D.sylowM.le hT_N
  have hbar : barSub V₀ V hV X = Mbar D.M V₀ V hV := by
    refine le_antisymm (barSub_mono V₀ V hV hXM) ?_
    intro φ hφ
    obtain ⟨m, hm, hmM, hmN, hmφ⟩ :=
      s16c1_normalizer_lift hM hT (S₁ := ⊥) bot_le hφ (by
        rw [Subgroup.mem_normalizer_iff]; intro x; simp)
    refine (mem_barSub V₀ V hV X φ).2 ⟨⟨m, hm⟩, ?_, hmφ⟩
    rw [hX]
    exact ⟨hmM, by rw [hQ₀, hK]; exact hmN⟩
  set Y : Subgroup G := X ⊓ K with hY
  have hYX : Y ≤ X := by rw [hY]; exact inf_le_left
  have hY_K : Y ≤ K := by rw [hY]; exact inf_le_right
  have hQ₀_syl : IsSylowIn 2 Q₀ K := by
    rw [hQ₀, hK]
    exact s16c1_sylow_preBarSub hM hT (Q := ⊥) bot_le
  have hQ₀Y : Q₀ ≤ Y := by rw [hY]; exact le_inf (hQ₀T.trans hTX) hQ₀K
  have hYnorm : Y ≤ normalizer (Q₀ : Set G) := by
    rw [hY]; exact inf_le_left.trans (by rw [hX]; exact inf_le_right)
  haveI : (Q₀.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀Y).2 hYnorm
  have hQ₀Yp : IsPGroup 2 (Q₀.subgroupOf Y) := hQ₀_syl.isPGroup.comap_subtype
  haveI := hQ₀Yp.isNilpotent
  have hdvd : Q₀.relIndex Y ∣ Q₀.relIndex K := by
    rw [← Subgroup.relIndex_mul_relIndex Q₀ Y K hQ₀Y hY_K]
    exact ⟨Y.relIndex K, rfl⟩
  have hoddY : ¬ 2 ∣ Q₀.relIndex Y := fun h2 => hQ₀_syl.not_dvd_relIndex (h2.trans hdvd)
  have hodd' : Odd (Q₀.relIndex Y) :=
    Nat.not_even_iff_odd.mp fun he => hoddY (even_iff_two_dvd.mp he)
  have hodd_card : Odd (Nat.card (↥Y ⧸ (Q₀.subgroupOf Y))) := hodd'
  haveI : Group.IsSolvable (↥Y ⧸ (Q₀.subgroupOf Y)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd_card
  haveI hYsolv : Group.IsSolvable ↥Y := Group.isSolvable_of_subgroup_quotient (Q₀.subgroupOf Y)
  haveI hYsubsolv : Group.IsSolvable ↥(Y.subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYX).injective
  let ψ : ↥X →* ↥(stabTil V₀ V) := Subgroup.inclusion hXs
  let π : ↥X →* ↥(Mbar D.M V₀ V hV) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp ψ) (Mbar D.M V₀ V hV) fun g => by
      have hmem : actTil V₀ V hV (ψ g) ∈ barSub V₀ V hV X :=
        actTil_mem_barSub V₀ V hV g.2 (hXs g.2)
      rw [hbar] at hmem
      exact hmem
  have hπsurj : Function.Surjective π := by
    intro φ
    have hφ' : (φ : MulAut (Vtil V₀ V hV)) ∈ barSub V₀ V hV X := by
      rw [hbar]; exact φ.2
    obtain ⟨g, hgX, hgφ⟩ := (mem_barSub V₀ V hV X _).1 hφ'
    refine ⟨⟨(g : G), hgX⟩, ?_⟩
    apply Subtype.ext
    show actTil V₀ V hV (ψ ⟨(g : G), hgX⟩) = (φ : MulAut (Vtil V₀ V hV))
    have hψg : ψ ⟨(g : G), hgX⟩ = g := Subtype.ext rfl
    rw [hψg, hgφ]
  have hker : π.ker = Y.subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hY, Subgroup.mem_inf]
    constructor
    · intro h1
      refine ⟨g.2, ?_⟩
      have h2 : actTil V₀ V hV (ψ g) = 1 := by
        have h2' : ((π g : ↥(Mbar D.M V₀ V hV)) : MulAut (Vtil V₀ V hV)) = 1 := by
          rw [h1]; rfl
        exact h2'
      rw [hK]
      exact (mem_preBarSub D.M V₀ V hV ⊥).2
        ⟨hXM g.2, hXs g.2, by rw [Subgroup.mem_bot]; exact h2⟩
    · rintro ⟨-, hgK⟩
      rw [hK] at hgK
      obtain ⟨-, hh, hh1⟩ := (mem_preBarSub D.M V₀ V hV ⊥).1 hgK
      apply Subtype.ext
      show actTil V₀ V hV (ψ g) = 1
      have hψg : ψ g = ⟨(g : G), hh⟩ := Subtype.ext rfl
      rw [hψg]
      exact Subgroup.mem_bot.1 hh1
  exact ⟨X, hXM, hTX, hbar, π, hπsurj, hker.symm ▸ hYsubsolv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

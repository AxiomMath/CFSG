module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb43ThreeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c11_compFactorAutInF_of_isSolvable (j : ℕ) {H S : Subgroup G}
    (hH : Group.IsSolvable ↥H) : CompFactorAutInF j H S := by
  haveI := hH
  intro Y hYH hY
  haveI := hY
  intro X hXn hX1 hXmin hXnc L hL
  haveI := hXn
  haveI : CFSG.IsMinimalNormal X := ⟨fun K hK hle => hXmin K hK hle⟩
  exact absurd (CFSG.minimalNormal_solvable_isMulCommutative X) hXnc

theorem s16c11_charTwo_of_sylow_le (D : Data G) {X : Subgroup G} (hXM : X ≤ D.M)
    (hTX : D.T ≤ X) : CFSG.QuasithinUnique.CharTwo X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.QuasithinUnique.CharTwo]
  intro x hx
  obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.1 hx
  have hxM : x ∈ D.M := hXM hxX
  have hTsyl : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hO2M_T : pCoreOf 2 D.M ≤ D.T := CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl
  have hO2M_X : pCoreOf 2 D.M ≤ X := hO2M_T.trans hTX
  have hnorm : X ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hnormal : ((pCoreOf 2 D.M).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2M_X).2 hnorm
  have hp : IsPGroup 2 (pCoreOf 2 D.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hO2M_O2X : pCoreOf 2 D.M ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hO2M_X hnormal hp
  have hxcent : x ∈ centralizer (pCoreOf 2 D.M : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hxc y (hO2M_O2X hy)
  exact hO2M_O2X ((D.standing.charTwo D.M D.maxLocal.1)
    (Subgroup.mem_inf.2 ⟨hxM, hxcent⟩))

private theorem s16c11_routefx_le_normalizer_preBarSub_bot {M V₀ V : Subgroup G}
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

theorem s16c11_exists_preimage_of_solvable (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V)
    {Xbar : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : Xbar ≤ Mbar D.M V₀ V hV)
    (hTX : barSub V₀ V hV D.T ≤ Xbar) (hsolv : Group.IsSolvable ↥Xbar) :
    ∃ X : Subgroup G, X ≤ D.M ∧ D.T ≤ X ∧ barSub V₀ V hV X = Xbar ∧
      Group.IsSolvable ↥X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hsolv
  have hM : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hT : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  set K : Subgroup G := preBarSub D.M V₀ V hV ⊥ with hK
  set Q₀ : Subgroup G := D.T ⊓ K with hQ₀
  set X₁ : Subgroup G := preBarSub D.M V₀ V hV Xbar with hX₁
  set X : Subgroup G := X₁ ⊓ normalizer (Q₀ : Set G) with hX
  have hX₁M : X₁ ≤ D.M := by rw [hX₁]; exact inf_le_left
  have hX₁s : X₁ ≤ stabTil V₀ V := by
    rw [hX₁]; exact inf_le_right.trans (Subgroup.map_subtype_le _)
  have hXM' : X ≤ D.M := by rw [hX]; exact inf_le_left.trans hX₁M
  have hXs : X ≤ stabTil V₀ V := by rw [hX]; exact inf_le_left.trans hX₁s
  have hKM : K ≤ D.M := by rw [hK]; exact inf_le_left
  have hMN : D.M ≤ normalizer (K : Set G) := by
    rw [hK]; exact s16c11_routefx_le_normalizer_preBarSub_bot hV hM
  have hQ₀T : Q₀ ≤ D.T := by rw [hQ₀]; exact inf_le_left
  have hQ₀K : Q₀ ≤ K := by rw [hQ₀]; exact inf_le_right
  have hT_X₁ : D.T ≤ X₁ := by
    rw [hX₁]
    intro t ht
    exact (mem_preBarSub D.M V₀ V hV Xbar).2
      ⟨D.sylowM.le ht, hM (D.sylowM.le ht),
        hTX (actTil_mem_barSub V₀ V hV ht (hM (D.sylowM.le ht)))⟩
  have hT_N : D.T ≤ normalizer (Q₀ : Set G) := by
    have h4 : D.T ≤ normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
      (le_inf (Subgroup.le_normalizer) (D.sylowM.le.trans hMN)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := D.T) (K := K))
    rw [hQ₀]; exact h4
  have hT_X : D.T ≤ X := by rw [hX]; exact le_inf hT_X₁ hT_N
  have hbar : barSub V₀ V hV X = Xbar := by
    refine le_antisymm ?_ ?_
    · intro φ hφ
      have h1 : φ ∈ barSub V₀ V hV X₁ := barSub_mono V₀ V hV inf_le_left hφ
      rw [hX₁, barSub_preBarSub D.M V₀ V hV Xbar] at h1
      exact h1.1
    · intro φ hφ
      have hφM : φ ∈ Mbar D.M V₀ V hV := hXM hφ
      obtain ⟨m, hm, hmM, hmN, hmφ⟩ :=
        s16c1_normalizer_lift hM hT (S₁ := ⊥) bot_le hφM (by
          rw [Subgroup.mem_normalizer_iff]; intro x; simp)
      have hmX₁ : m ∈ X₁ := by
        rw [hX₁]
        exact (mem_preBarSub D.M V₀ V hV Xbar).2
          ⟨hmM, hm, by rw [hmφ]; exact hφ⟩
      have hmN' : m ∈ normalizer (Q₀ : Set G) := by rw [hQ₀, hK]; exact hmN
      refine (mem_barSub V₀ V hV X φ).2 ⟨⟨m, hm⟩, ?_, hmφ⟩
      rw [hX]; exact ⟨hmX₁, hmN'⟩
  have hQ₀_syl : IsSylowIn 2 Q₀ K := by
    rw [hQ₀, hK]
    exact s16c1_sylow_preBarSub hM hT (Q := ⊥) bot_le
  set Y : Subgroup G := X ⊓ K with hY
  have hYX : Y ≤ X := by rw [hY]; exact inf_le_left
  have hY_le_K : Y ≤ K := by rw [hY]; exact inf_le_right
  have hQ₀Y : Q₀ ≤ Y := by rw [hY]; exact le_inf (hQ₀T.trans hT_X) hQ₀K
  have hYnorm : Y ≤ normalizer (Q₀ : Set G) := by
    rw [hY]; exact inf_le_left.trans (by rw [hX]; exact inf_le_right)
  haveI : (Q₀.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀Y).2 hYnorm
  have hQ₀Yp : IsPGroup 2 (Q₀.subgroupOf Y) := hQ₀_syl.isPGroup.comap_subtype
  haveI := hQ₀Yp.isNilpotent
  have hdvd : Q₀.relIndex Y ∣ Q₀.relIndex K := by
    rw [← Subgroup.relIndex_mul_relIndex Q₀ Y K hQ₀Y hY_le_K]
    exact ⟨Y.relIndex K, rfl⟩
  have hoddY : ¬ 2 ∣ Q₀.relIndex Y := fun h2 => hQ₀_syl.not_dvd_relIndex (h2.trans hdvd)
  have hodd' : Odd (Q₀.relIndex Y) :=
    Nat.not_even_iff_odd.mp fun he => hoddY (even_iff_two_dvd.mp he)
  have hodd_card : Odd (Nat.card (↥Y ⧸ (Q₀.subgroupOf Y))) := hodd'
  haveI : Group.IsSolvable (↥Y ⧸ (Q₀.subgroupOf Y)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd_card
  haveI : Group.IsSolvable ↥Y := Group.isSolvable_of_subgroup_quotient (Q₀.subgroupOf Y)
  let ψ : ↥X →* ↥(stabTil V₀ V) := Subgroup.inclusion hXs
  let f : ↥X →* ↥Xbar := MonoidHom.codRestrict ((actTil V₀ V hV).comp ψ) Xbar fun g => by
    have hmem : actTil V₀ V hV (ψ g) ∈ barSub V₀ V hV X :=
      actTil_mem_barSub V₀ V hV g.2 (hXs g.2)
    rw [hbar] at hmem
    exact hmem
  have hker : f.ker = Y.subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hY, Subgroup.mem_inf]
    constructor
    · intro h1
      refine ⟨g.2, ?_⟩
      have h2 : actTil V₀ V hV (ψ g) = 1 := by
        have h2' : ((f g : ↥Xbar) : MulAut (Vtil V₀ V hV)) = 1 := by rw [h1]; rfl
        exact h2'
      rw [hK]
      exact (mem_preBarSub D.M V₀ V hV ⊥).2
        ⟨hXM' g.2, hXs g.2, by rw [Subgroup.mem_bot]; exact h2⟩
    · rintro ⟨-, hgK⟩
      rw [hK] at hgK
      obtain ⟨-, h, hh⟩ := (mem_preBarSub D.M V₀ V hV ⊥).1 hgK
      have hh1 : actTil V₀ V hV ⟨(g : G), h⟩ = 1 := Subgroup.mem_bot.1 hh
      apply Subtype.ext
      show actTil V₀ V hV (ψ g) = 1
      have : ψ g = ⟨(g : G), h⟩ := Subtype.ext rfl
      rw [this, hh1]
  exact ⟨X, hXM', hT_X, hbar,
    Group.isSolvable_of_ker_le_range (Subgroup.inclusion hYX) f
      (by rw [hker, Subgroup.inclusion_range])⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

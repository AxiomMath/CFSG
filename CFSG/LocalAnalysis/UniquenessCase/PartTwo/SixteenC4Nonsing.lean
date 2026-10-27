module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4FrameM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

theorem s16c4_z_centralizer_le (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  have h62 : CFSG.LocalAnalysis.WeakClosure81.Hyp62 D.M V₀ V :=
    hS.setting.hyp16.hyp125.hyp62
  have hXV : Subgroup.zpowers z ≤ V₀ := Subgroup.zpowers_le.2 hz
  have hX1 : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
  have hN := h62.normalizer_le (Subgroup.zpowers z) hXV hX1
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact (le_of_eq hcent_eq).trans ((Subgroup.centralizer_le_normalizer _).trans hN)

theorem s16c4_nonsing_centralizer_le (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L)
    (F : UFrame V₀ V hV L) (x : IntMod V hV) (hx : ¬ F.Sing (mkTil V₀ V hV x)) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hH125.pairFacts
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases hH125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4card : Nat.card V₀ ≤ 4 := by
    have hV₀2 : IsPGroup 2 V₀ := fun g =>
      ⟨1, Subtype.ext (by simpa using hP.elemAbelian₀.2 (g : G) g.2)⟩
    rw [card_eq_two_pow_mSub hV₀2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
      _ = 4 := by norm_num
  have h3 : 3 ∈ D.sig := by rw [h4.2.2]; exact Set.mem_singleton 3
  have hx0 : x.val ∉ V₀ := by
    intro h0
    apply hx
    have h1 : mkTil V₀ V hV x = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0
    rw [h1]
    exact F.Sing_one
  have hxsum : ∑ i, F.vec (mkTil V₀ V hV x) i ^ (2 ^ 1 + 1) ≠ 0 := by
    intro h0
    apply hx
    rw [F.Sing_iff_sum]
    exact h0
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  obtain ⟨E, hE, hEab, hEcard, hEfix⟩ :=
    exists_stab_elemAbelian_nonsing (p := 3) (n := 1) Nat.prime_three
      (by norm_num : 3 ∣ 2 ^ 1 + 1) hF hxsum
  have hEsu : E ≤ SUid F.σ 4 := by
    rw [F.suid_eq_statedSU]
    exact hE
  obtain ⟨E', hE'le, ⟨e⟩⟩ :=
    F.exists_subgroup_ptCent E hEsu (F.vec (mkTil V₀ V hV x)) hEfix
  rw [F.ofVec_vec] at hE'le
  have hE'M : E' ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) :=
    hE'le.trans (inf_le_inf_right _ (lBar_le_Mbar hS))
  have hEp : IsPGroup 3 E :=
    fun g => ⟨1, Subtype.ext (by simpa using hEab.2 (g : GL (Fin 4) F.K) g.2)⟩
  have hE'p : IsPGroup 3 E' := hEp.of_equiv e
  have hE'c : ¬ IsCyclic E' :=
    fun hc => (CFSG.AGLEmbedding.BlockCyc.not_isCyclic_of_isElemAbelian_sq hEab hEcard)
      ((MulEquiv.isCyclic e).2 hc)
  exact centralizer_le_of_noncyclic_bar D h61 Nat.prime_three (by norm_num) h3 hV hP hcase
    h4card x hx0 hE'M hE'p hE'c

theorem s16c4_ts_of_not_centralizer_le (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L)
    (F : UFrame V₀ V hV L) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    (∀ x : IntMod V hV, x.val ∈ U → F.Sing (mkTil V₀ V hV x)) ∧
      (V₀ ≠ ⊥ → U ⊓ V₀ = ⊥) := by
  constructor
  · intro x hxU
    by_contra hns
    exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
      (s16c4_nonsing_centralizer_le D h61 hS h4 F x hns))
  · intro _
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    obtain ⟨hzU, hzV₀⟩ := Subgroup.mem_inf.1 hz
    exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)).trans
      (s16c4_z_centralizer_le D hS hzV₀ hz1))

theorem s16c4_sing_of_mem_inf_conj (D : Data G) (h61 : UC6.R6_1 D) (h22 : R1622 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) (F : UFrame V₀ V hV L) {g : G} (hg : g ∉ D.M)
    (x : IntMod V hV) (hxg : x.val ∈ conjSubgroup V g) : F.Sing (mkTil V₀ V hV x) := by
  by_contra hn
  have hx0 : x.val ∉ V₀ := by
    intro h0
    apply hn
    have h1 : mkTil V₀ V hV x = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0
    rw [h1]
    exact F.Sing_one
  have hx1 : x.val ≠ 1 := fun h => hx0 (h ▸ V₀.one_mem)
  have hcent : centralizer ({x.val} : Set G) ≤ D.M :=
    s16c4_nonsing_centralizer_le D h61 hS h4 F x hn
  have hx2 : x.val ^ 2 = 1 := hV.2 x.val x.val_mem
  have horder : orderOf x.val = 2 := by
    have hdvd : orderOf x.val ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hUV : Subgroup.zpowers x.val ≤ V := Subgroup.zpowers_le.2 x.val_mem
  have hNle : ∀ X : Subgroup G, X ≤ Subgroup.zpowers x.val → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) ≤ D.M := by
    intro X hXU hX1
    have hcardX : Nat.card X = 2 := by
      have hdvd : Nat.card X ∣ 2 := by
        have h := Subgroup.card_dvd_of_le hXU
        rwa [Nat.card_zpowers, horder] at h
      have hlt : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).2 hX1
      have hle2 : Nat.card X ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hXtop : X = Subgroup.zpowers x.val := by
      refine Subgroup.eq_of_le_of_card_ge hXU ?_
      rw [Nat.card_zpowers, horder, hcardX]
    rw [hXtop]
    refine (show Subgroup.normalizer (Subgroup.zpowers x.val : Set G) ≤
      centralizer ({x.val} : Set G) from ?_).trans hcent
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hmem : n * x.val * n⁻¹ ∈ Subgroup.zpowers x.val :=
      (Subgroup.mem_normalizer_iff.1 hn x.val).1 (Subgroup.mem_zpowers x.val)
    have hcn : n * x.val * n⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have e : x.val = n⁻¹ * (n * x.val * n⁻¹) * n := by group
      rw [e, h]; group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hnx : n * x.val * n⁻¹ = x.val := by
      have hmod : x.val ^ (k % (2 : ℤ)) = n * x.val * n⁻¹ := by
        have hz := zpow_mod_orderOf x.val k
        rw [horder] at hz
        exact hz.trans hk
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [h0, zpow_zero] at hmod
        exact absurd hmod.symm hcn
      · rw [h1, zpow_one] at hmod
        exact hmod.symm
    have : n * x.val = x.val * n := by
      calc n * x.val = (n * x.val * n⁻¹) * n := by group
        _ = x.val * n := by rw [hnx]
    exact this.symm
  have hΓ : rankThreeGamma 1 2 (Subgroup.zpowers x.val) ≤ D.M :=
    CFSG.LocalAnalysis.WeakClosure81.rankThreeGamma_le_of_normalizer_le hNle le_rfl
  have hg' : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
  have h22' := h22 V₀ V hS.setting.hyp16 g⁻¹ hg' (Subgroup.zpowers x.val) hUV hΓ
  have hmem : g * x.val * g⁻¹ ∈ conjSubgroup (Subgroup.zpowers x.val) g⁻¹ ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_conjSubgroup_iff.1 hxg⟩
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * x.val * g⁻¹) * g⁻¹⁻¹ = x.val := by group
    rw [e]
    exact Subgroup.mem_zpowers x.val
  rw [h22', Subgroup.mem_bot] at hmem
  have hconj_ne : g * x.val * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x.val = g⁻¹ * (g * x.val * g⁻¹) * g := by group
    rw [e, h]; group
  exact hconj_ne hmem

theorem s16c4_V0_inf_conj_eq_bot (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {g : G} (hg : g ∉ D.M) :
    V₀ ⊓ conjSubgroup V g = ⊥ := by
  have h62 : CFSG.LocalAnalysis.WeakClosure81.Hyp62 D.M V₀ V :=
    hS.setting.hyp16.hyp125.hyp62
  have hΓ : rankThreeGamma 1 2 V₀ ≤ D.M :=
    CFSG.LocalAnalysis.WeakClosure81.rankThreeGamma_le_of_normalizer_le
      h62.normalizer_le le_rfl
  have hg' : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
  have h22' := h22 V₀ V hS.setting.hyp16 g⁻¹ hg' V₀ h62.le hΓ
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hw₀, hwV⟩ := Subgroup.mem_inf.1 hw
  have hmem : g * w * g⁻¹ ∈ conjSubgroup V₀ g⁻¹ ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_conjSubgroup_iff.1 hwV⟩
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rw [e]
    exact hw₀
  rw [h22', Subgroup.mem_bot] at hmem
  apply hw1
  have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
  rw [e, hmem]
  group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

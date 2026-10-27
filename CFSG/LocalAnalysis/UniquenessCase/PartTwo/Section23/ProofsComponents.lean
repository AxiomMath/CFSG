module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.GroupTheory.InvertingElements
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s23_exists_two_element {D : Data G} {m : G}
    (hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G)) (hmM : m ∈ D.M) :
    ∃ y : G, y ∈ D.M ∧ y ∈ Subgroup.centralizer (D.Z : Set G) ∧
      ∀ b : G, m * b * m⁻¹ = b⁻¹ → y * b * y⁻¹ = b⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, q, hqodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  refine ⟨m ^ q, D.M.pow_mem hmM q, ?_,
    fun b hinv => CFSG.GroupTheory.pow_odd_inverts hinv hqodd⟩
  have hdvd : q ∣ orderOf m := ⟨2 ^ a, by rw [hord]; ring⟩
  have hyord : orderOf (m ^ q) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hqodd.pos.ne' hdvd, hord]
    exact Nat.mul_div_cancel _ hqodd.pos
  have hP : IsPGroup 2 (Subgroup.zpowers (m ^ q)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hyord])
  obtain ⟨k, hkM, hk⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM
    (Subgroup.zpowers_le.mpr (D.M.pow_mem hmM q)) hP
  have hmem : k⁻¹ * m ^ q * k ∈ D.T := hk _ (Subgroup.mem_zpowers _)
  have htC : k⁻¹ * m ^ q * k ∈ Subgroup.centralizer (D.Z : Set G) :=
    uc22main1_T_le_centralizer D hmem
  have hkN : k ∈ Subgroup.normalizer (D.Z : Set G) := hZM hkM
  have hconj : k * (k⁻¹ * m ^ q * k) * k⁻¹ ∈ Subgroup.centralizer (D.Z : Set G) :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (D.Z) hkN) (k⁻¹ * m ^ q * k)).mp htC
  rwa [show k * (k⁻¹ * m ^ q * k) * k⁻¹ = m ^ q by group] at hconj

private theorem uc22s23_mem_uniqueSet_of_strong {D : Data G} {p : ℕ}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (hp : p.Prime)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXp : IsPGroup p ↥X) (hXM : X ≤ D.M) :
    X ∈ uniqueSet D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hXM, fun g hXg => ?_⟩
  by_contra hne
  have hMs : Subgroup.normalizer (D.M : Set G) = D.M :=
    UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hgM : g ∉ D.M := by
    intro hg
    have hgN : g ∈ Subgroup.normalizer (D.M : Set G) := by rw [hMs]; exact hg
    exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
  have hpdvdX : p ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      have h1 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot (H := X)).2 hXne
      omega
    rw [hn]
    exact dvd_pow_self p hn0
  have hle : X ≤ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := le_inf hXM hXg
  exact hsp.2.2 g hgM (hpdvdX.trans (Subgroup.card_dvd_of_le hle))

theorem s23_5_4_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) :
    S23_5_4 D Ch := by
  intro h1930 c b hb hbZ
  obtain ⟨hUZ, hUM, hMN⟩ := h4 h1930 c
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by simpa [hUZ] using hMN
  have hbM : b ∈ D.M := (c.hle.trans c.hBM) hb
  have hbodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB hb
  have hnotinv : ¬ InvertedIn D.M (Subgroup.zpowers b) := by
    rintro ⟨m, hmM, hm_inv⟩
    have hbm : m * b * m⁻¹ = b⁻¹ := hm_inv b (Subgroup.mem_zpowers b)
    obtain ⟨y, -, hyZ, hyinv⟩ := uc22s23_exists_two_element hZM hmM
    exact hbZ (CFSG.GroupTheory.mem_centralizer_of_inverted hbodd (hyinv b hbm)
        (fun a ha => (Subgroup.mem_centralizer_iff.mp hyZ a ha).symm) (hZM hbM))
  refine ⟨hnotinv, ?_⟩
  intro p hp X hXne hXp hXle
  have hXM : X ≤ D.M := hXle.trans inf_le_left
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := hXle.trans inf_le_right
  have hXcent : X ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute x b := Subgroup.mem_centralizer_singleton_iff.mp (hXb hx)
    exact (hcomm.zpow_right n).eq.symm
  have hXN : X ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hXcent.trans (Subgroup.centralizer_le_normalizer _)
  have hXnotU : X ∉ uniqueSet D.M := by
    intro hXU
    have hb1 : b ≠ 1 := by
      intro h1
      exact hbZ (h1 ▸ Subgroup.one_mem _)
    have hAne : Subgroup.zpowers b ≠ ⊥ := by
      intro hbot
      exact hb1 (Subgroup.zpowers_eq_bot.mp hbot)
    have hAB : Subgroup.zpowers b ≤ c.B := Subgroup.zpowers_le.2 hb
    exact hnotinv (s21_10 D Ch h1930 c.toCtx21 (Subgroup.zpowers b) hAne hAB X hXne
      ⟨p, hp, hXp⟩ hXN hXU)
  refine ⟨hXnotU, ?_⟩
  intro hp1
  exact hXnotU (uc22s23_mem_uniqueSet_of_strong (hsp p hp1) hp hXne hXp hXM)

end CFSG.LocalAnalysis.UniquenessCase.UC22

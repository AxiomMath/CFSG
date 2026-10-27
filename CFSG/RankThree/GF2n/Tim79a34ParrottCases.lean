module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa)

variable {G : Type} [Group G] [Finite G]

private theorem card_oMinusSixTwo : Nat.card OMinusSixTwo = 51840 := by
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) (b := 1) (c := 1) 2
      (by decide)).2
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) : ℤ) = ((51840 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    first | decide | norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast h2

private theorem qa_le_centralizer (x : G) :
    Qa x ≤ Subgroup.centralizer ({x} : Set G) := by
  intro g hg
  obtain ⟨y, -, rfl⟩ := hg
  exact y.2

private theorem card_of_quotient_1024 {C : Type} [Group C] (K : Subgroup C)
    (hK : Nat.card K = 1024) (hq : Nat.card (C ⧸ K) = 51840) : Nat.card C = 53084160 := by
  have h := Subgroup.card_mul_index (H := K)
  have hidx : K.index = 51840 := by
    unfold Subgroup.index
    exact hq
  rw [hK, hidx] at h
  omega

theorem parrottCaseII_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : ¬ ParrottCaseII cfg.aG := by
  intro h
  obtain ⟨z₁, -, -, hord, hnorm, -⟩ := h
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers z₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord] <;> norm_num)
  have hle : Subgroup.zpowers z₁ ≤ pCore 2 G := le_sSup ⟨hnorm, hpg⟩
  have hz : z₁ ∈ pCore 2 G := hle (Subgroup.mem_zpowers z₁)
  rw [hc.o2, Subgroup.mem_bot] at hz
  rw [hz, orderOf_one] at hord
  norm_num at hord

theorem fi22_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (hFi : Fi22InvolutionCentralizerStatement) (h11a : Lemma11aStatement)
    (h12 : Lemma12Statement) (h13 : Lemma13Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) (hw : w = 2 * n - 2)
    (hV : StrothCaseV cfg.aG w)
    (hsp : CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22) : False := by
  obtain ⟨hw4, ⟨hN, ⟨eM⟩⟩, -, -⟩ := hV
  have hn3 : n = 3 := by omega
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hH cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hPcard : Nat.card ↥P = 2 ^ (4 * n - 2) :=
    (h11a G M V Q P H hH cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).2.2.2
  have hP1024 : Nat.card ↥P = 1024 := by
    rw [hPcard, hn3] <;> norm_num
  have hQP : Q = P := le_antisymm cfg.qp hc.P_le_Q
  have hQa : Qa cfg.aG = Q := qa_aG_eq h12 cfg
  have hK : Nat.card ↥((Qa cfg.aG).subgroupOf
      (Subgroup.centralizer ({cfg.aG} : Set G))) = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (qa_le_centralizer cfg.aG)).toEquiv,
      hQa, hQP, hP1024]
  have hq : Nat.card (↥(Subgroup.centralizer ({cfg.aG} : Set G)) ⧸
      (Qa cfg.aG).subgroupOf (Subgroup.centralizer ({cfg.aG} : Set G))) = 51840 := by
    rw [Nat.card_congr eM.toEquiv, card_oMinusSixTwo]
  have hCa : Nat.card ↥(Subgroup.centralizer ({cfg.aG} : Set G)) = 53084160 :=
    card_of_quotient_1024 _ hK hq
  have hMcard : Nat.card ↥M = 53084160 := by
    rw [← hcent]
    exact hCa
  obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hv1 : v ≠ 1 := fun h => hvW (by rw [h]; exact (wOf V H).one_mem)
  have hv2 : orderOf v = 2 := by
    have hsq : v ^ 2 = 1 := by
      rw [pow_two]
      exact elemAbelian_mul_self hc.elemAb hvV
    exact orderOf_eq_prime hsq hv1
  have h13v := h13 G M V Q P H hH cfg.centre cfg.iw v hvV hvW
  have hvcard : Nat.card ↥(Subgroup.centralizer ({v} : Set G)) = 26542080 := by
    rw [h13v.1]
    have h2 := h13v.2
    rw [hMcard] at h2
    omega
  rcases hFi G hsp v hv2 with h | h | h <;> omega

end CFSG.RankThree.GF2n.Tim79a

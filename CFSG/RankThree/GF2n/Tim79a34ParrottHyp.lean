module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_of_commute_eq_bot {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype
      fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype
      fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2) := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (a1 : G) * (b1 : G) = (a2 : G) * (b2 : G) := h
    have hab : (a2 : G)⁻¹ * (a1 : G) = (b2 : G) * (b1 : G)⁻¹ := by
      calc (a2 : G)⁻¹ * (a1 : G) = (a2 : G)⁻¹ * ((a1 : G) * (b1 : G)) * (b1 : G)⁻¹ := by group
        _ = (a2 : G)⁻¹ * ((a2 : G) * (b2 : G)) * (b1 : G)⁻¹ := by rw [h']
        _ = (b2 : G) * (b1 : G)⁻¹ := by group
    have hmem : (a2 : G)⁻¹ * (a1 : G) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem a2.2) a1.2, ?_⟩
      rw [hab]
      exact B.mul_mem b2.2 (B.inv_mem b1.2)
    rw [hi, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hb : (b2 : G) * (b1 : G)⁻¹ = 1 := by rw [← hab, hmem, inv_mul_cancel]
    rw [mul_inv_eq_one] at hb
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb.symm)
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

theorem parrottHyp_of_caseV (hO : OMinusSixTwoAutPSp43Statement) (hH : NTStrothHypStatement)
    (h11a : Lemma11aStatement) (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) (hw : w = 2 * n - 2) (hV : StrothCaseV cfg.aG w) :
    ParrottHyp cfg.aG := by
  obtain ⟨hw4, ⟨hN, ⟨eQ⟩⟩, -, -⟩ := hV
  have hn3 : n = 3 := by
    have := cfg.three
    omega
  have hyp := cfg.hyp
  have hc : MinCex M V Q P H := hyp.setup.mc.toMinCex
  have hQP : Q = P := le_antisymm cfg.qp hc.P_le_Q
  have haV : cfg.aG ∈ V := qpCfg_aG_mem_V cfg
  have haW : cfg.aG ∈ wOf V H := (Additive.toMul (ψ a)).2
  have haG1 : cfg.aG ≠ 1 := qpCfg_aG_ne_one cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord2 : orderOf cfg.aG = 2 := orderOf_eq_prime (hc.elemAb.2 cfg.aG haV) haG1
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hQa : Qa cfg.aG = Q := qa_aG_eq h12 cfg
  have hJ : inSubgroup (pCore 2) (Subgroup.centralizer ({cfg.aG} : Set G)) = Qa cfg.aG := by
    rw [hcent, ← hc.hQ, hQa]
  have hCJ : Subgroup.centralizer ({cfg.aG} : Set G) ⊓
      Subgroup.centralizer (inSubgroup (pCore 2) (Subgroup.centralizer ({cfg.aG} : Set G)) :
        Set G) ≤ inSubgroup (pCore 2) (Subgroup.centralizer ({cfg.aG} : Set G)) := by
    rw [hcent]
    exact CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq hc.fitting
  rw [hJ] at hCJ
  obtain ⟨E, F, w', hE, hw', hcardF⟩ := hH G M V Q P H Φ ψ a T cfg
  have hw'9 : 2 * w' + 1 = 9 := by omega
  have hFcard : Nat.card ↥F = 2 ^ 9 := by rw [hcardF, hw'9]
  have hPcard : Nat.card ↥P = 2 ^ 10 := by
    have h := (h11a G M V Q P H hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
      cfg.point).2.2.2
    have h10 : 4 * n - 2 = 10 := by omega
    rw [h10] at h
    exact h
  have hQcard : Nat.card ↥Q = 2 ^ 10 := by
    rw [hQP]
    exact hPcard
  have hEcard : Nat.card ↥E = 2 := by
    have hprod := card_sup_of_commute_eq_bot (A := E) (B := F)
      (fun e he f hf => hE.commute e he f hf) hE.inf_eq_bot
    rw [hE.sup_eq, hQa, hQcard, hFcard] at hprod
    have h2 : Nat.card ↥E * 2 ^ 9 = 2 * 2 ^ 9 := hprod.symm.trans (by norm_num)
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hyp.module.trans hyp.q_two
  have hzp : Subgroup.zpowers cfg.aG = V ⊓ wOf V H := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨haV, haW⟩)
    · exact le_of_eq (by rw [hVW, Nat.card_zpowers, hord2])
  have hcommQP : ⁅Q, Q⁆ = ⁅P, P⁆ := by rw [hQP]
  have hcomm : ⁅Qa cfg.aG, Qa cfg.aG⁆ = Subgroup.zpowers cfg.aG := by
    rw [hQa, hcommQP, (h11b G M V Q P H hyp cfg.centre cfg.iw).1, hzp]
  obtain ⟨X, hXg, hX, ⟨eO⟩⟩ := hO
  unfold ParrottHyp
  rw [hJ]
  exact ⟨hord2, ⟨E, F, hEcard, hE.extraspecial, hFcard, hE.inf_eq_bot, hE.commute, hE.sup_eq⟩,
    hcomm, hCJ, hN, X, hXg, hX, ⟨eQ.trans eO⟩⟩

end CFSG.RankThree.GF2n.Tim79a

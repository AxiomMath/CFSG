module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts
public import CFSG.RankThree.GF2n.Tim79a34Lemma13

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)

variable {G : Type} [Group G] [Finite G]

theorem strothCaseIII_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) (hw : w = 2 * n - 2) :
    ¬ StrothCaseIII cfg.aG w := by
  rintro ⟨hw2, -⟩
  have h3 := cfg.three
  omega

theorem strothCaseIV_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) (hw : w = 2 * n - 2) :
    ¬ StrothCaseIV cfg.aG w := by
  rintro ⟨hw3, -⟩
  omega

theorem strothCaseVII_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) : ¬ StrothCaseVII cfg.aG w := by
  rintro ⟨-, -, -, -, hcard⟩
  rw [card_centerIn_qa h11b h12 cfg] at hcard
  have hpos : 0 < Nat.card ↥(centerIn (Subgroup.centralizer ({cfg.aG} : Set G))) :=
    Nat.card_pos
  omega

theorem strothCaseI_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11a : Lemma11aStatement) (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) : ¬ StrothCaseI cfg.aG := by
  intro hI
  have h2n : 2 ≤ n := by
    have := cfg.three
    omega
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hQP : Q = P := le_antisymm cfg.qp hc.P_le_Q
  have hH := cfg.hyp
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hinj : ∀ x y : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) = ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) →
        x = y :=
    fun x y h => ψ.injective (Additive.toMul.injective (Subtype.ext h))
  have h0 : ((Additive.toMul (ψ 0) : ↥(wOf V H)) : G) = 1 := by
    rw [map_zero]
    rfl
  obtain ⟨w₁, hw₀, hperp, hne⟩ := exists_perp_vec_not_smul h2n cfg.ne
  have hw₁a : w₁ ≠ a := fun h => hne 1 (by rw [one_smul]; exact h)
  have huP : ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) ∈ P :=
    ((h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
      w₁).mpr hperp
  have huV : ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) ∉ V := by
    intro huV
    have hu1 : ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) ≠ 1 :=
      fun h => hw₀ (hinj w₁ 0 (h.trans h0.symm))
    have ha1 : cfg.aG ≠ 1 := fun h => cfg.ne (hinj a 0 (h.trans h0.symm))
    have heq := l13_eq_of_natCard_two hVW
      (Subgroup.mem_inf.mpr ⟨huV, (Additive.toMul (ψ w₁)).2⟩)
      (Subgroup.mem_inf.mpr ⟨qpCfg_aG_mem_V cfg, (Additive.toMul (ψ a)).2⟩) hu1 ha1
    exact hw₁a (hinj w₁ a heq)
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero cfg.ne hw₀
  obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g)
  have hgx : Φ.symm (xToXbar hVH x) = g := by
    rw [hx, MulEquiv.symm_apply_apply]
  have key := cfg.nat.equiv x a
  rw [hgx, hg] at key
  have hconj : (x : G) * cfg.aG * (x : G)⁻¹ = ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) :=
    key.symm
  have hmemQ : (x : G) * cfg.aG * (x : G)⁻¹ ∈ Qa cfg.aG := by
    rw [hconj, qa_aG_eq h12 cfg, hQP]
    exact huP
  have hcen := hI (x : G) hmemQ
  rw [hconj, qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg] at hcen
  exact huV hcen

end CFSG.RankThree.GF2n.Tim79a

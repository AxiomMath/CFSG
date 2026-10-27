module

public import CFSG.RankThree.GF2n.Tim79a34Hauptsatz
public import CFSG.RankThree.GF2n.Tim79a34TwBound

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)

variable {G : Type} [Group G] [Finite G]

theorem qpCfg_aG_mem_V {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : cfg.aG ∈ V :=
  cfg.nat.point a T cfg.ne cfg.trans cfg.point

theorem qpCfg_aG_mem_W {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : cfg.aG ∈ wOf V H :=
  (Additive.toMul (ψ a) : ↥(wOf V H)).2

theorem qpCfg_aG_ne_one {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : cfg.aG ≠ 1 := by
  intro h
  have h1 : (Additive.toMul (ψ a) : ↥(wOf V H)) = 1 := Subtype.ext h
  have h2 : ψ a = 0 := Additive.toMul.injective (show Additive.toMul (ψ a) =
    Additive.toMul (0 : Additive ↥(wOf V H)) from h1)
  exact cfg.ne (ψ.injective (h2.trans (map_zero ψ).symm))

theorem qpCfg_orderOf_aG {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : orderOf cfg.aG = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : cfg.aG ^ 2 = 1 := cfg.hyp.setup.mc.toMinCex.elemAb.2 _ (qpCfg_aG_mem_V cfg)
  exact orderOf_eq_prime hsq (qpCfg_aG_ne_one cfg)

theorem qa_aG_eq {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h12 : Lemma12Statement) (cfg : QPCfg M V Q P H Φ ψ a T) : Qa cfg.aG = Q := by
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hH cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  show fStar (Subgroup.centralizer ({cfg.aG} : Set G)) = Q
  rw [hcent]
  unfold fStar
  rw [hc.fitting, hc.hQ]
  rfl

theorem centerIn_Q_eq {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T) : centerIn Q = V := by
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQP : Q = P := le_antisymm cfg.qp hc.P_le_Q
  have hcen : Subgroup.centralizer (P : Set G) = V :=
    (h11b G M V Q P H hH cfg.centre cfg.iw).2.2
  rw [hQP]
  show P ⊓ Subgroup.centralizer (P : Set G) = V
  rw [hcen]
  exact inf_eq_right.mpr hc.V_le_P

theorem qpCfg_card_V {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : Nat.card ↥V = 4 := by
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have h := twb_card_barOf_mul (V := V) (H := H) (K := V) hc.V_le_H
  have e1 : Nat.card ↥(barOf V H V) = 2 := hH.q_two
  have e2 : Nat.card ↥(V ⊓ wOf V H) = 2 := by rw [hH.module]; exact hH.q_two
  rw [e1, e2] at h
  omega

theorem card_centerIn_qa {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement) (cfg : QPCfg M V Q P H Φ ψ a T) :
    Nat.card ↥(centerIn (Qa cfg.aG)) = 4 := by
  rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
  exact qpCfg_card_V cfg

end CFSG.RankThree.GF2n.Tim79a

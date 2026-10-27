module

public import CFSG.RankThree.GF2n.Tim79a34Hauptsatz
import CFSG.RankThree.GF2n.Tim79a34Gamma
import CFSG.RankThree.GF2n.Stroth78.Sec2Conj
public import CFSG.RankThree.GF2n.Tim79a34Natural
public import CFSG.RankThree.GF2n.Tim79aSpPair
import CFSG.RankThree.GF2n.Tim79a34Lemma13

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)
open Matrix

variable {G : Type} [Group G] [Finite G]

theorem qpCfg_centralizer_le {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement) (h13 : Lemma13Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) {r : G} (hrV : r ∈ V) (hr : r ≠ 1) :
    Subgroup.centralizer ({r} : Set G) ≤ Subgroup.centralizer ({cfg.aG} : Set G) := by
  have hH := cfg.hyp
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hH cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have haV : cfg.aG ∈ V := qpCfg_aG_mem_V cfg
  have haW : cfg.aG ∈ wOf V H := qpCfg_aG_mem_W cfg
  have haG1 : cfg.aG ≠ 1 := qpCfg_aG_ne_one cfg
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  intro g hg
  have hgr : r * g = g * r :=
    Subgroup.mem_centralizer_iff.mp hg r (Set.mem_singleton r)
  by_cases hW : r ∈ wOf V H
  · have hreq : r = cfg.aG :=
      l13_eq_of_natCard_two hVW (Subgroup.mem_inf.mpr ⟨hrV, hW⟩)
        (Subgroup.mem_inf.mpr ⟨haV, haW⟩) hr haG1
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk, ← hreq]
    exact hgr
  · have hgr' : g ∈ Subgroup.centralizer ({r} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact hgr
    rw [(h13 G M V Q P H hH cfg.centre cfg.iw r hrV hW).1] at hgr'
    rw [hcent]
    exact (Subgroup.mem_inf.mp hgr').1

theorem qpCfg_assumption212 {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement) (h13 : Lemma13Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) : Stroth78.Stroth78Assumption212 cfg.aG := by
  rintro ⟨R, hRc, hRcard, hnot⟩
  have hcV : centerIn (Qa cfg.aG) = V := by
    rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
  have hV4 : Nat.card ↥V = 4 := qpCfg_card_V cfg
  rw [hcV] at hRc
  rw [hcV, hV4] at hRcard
  have hR2 : Nat.card ↥R = 2 := by omega
  have hRnt : Nontrivial ↥R := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨r, hr1⟩ := exists_ne (1 : ↥R)
  have hr : (r : G) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hle : Subgroup.centralizer (R : Set G) ≤ Subgroup.centralizer ({cfg.aG} : Set G) := by
    intro g hg
    have hgr : g ∈ Subgroup.centralizer ({(r : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact Subgroup.mem_centralizer_iff.mp hg r r.2
    exact qpCfg_centralizer_le h11b h12 h13 cfg (hRc r.2) hr hgr
  exact hnot (fun g hg => Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hle hg, hg⟩))

theorem qpCfg_inv_conj_mem_P {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T) (hVH : V ≤ H)
    {g : ↥(StatedSp n (GaloisField 2 1))} {x : ↥(xOf V H)}
    (hgx : Φ.symm (xToXbar hVH x) = g)
    (hperp : CaseM.spForm a (SpExtras.mat n (GaloisField 2 1) g *ᵥ a) = 0) :
    (x : G)⁻¹ * cfg.aG * (x : G) ∈ P := by
  have hxi : ((x⁻¹ : ↥(xOf V H)) : G) = (x : G)⁻¹ := rfl
  have hgx' : Φ.symm (xToXbar hVH x⁻¹) = g⁻¹ := by
    have h1 : xToXbar hVH x⁻¹ = (xToXbar hVH x)⁻¹ := map_inv (xToXbar hVH) x
    rw [h1, map_inv]
    exact congrArg Inv.inv hgx
  have key2 := cfg.nat.equiv x⁻¹ a
  rw [hgx', hxi, inv_inv] at key2
  have hconj2 : (x : G)⁻¹ * cfg.aG * (x : G) =
      ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 1) g⁻¹ *ᵥ a)) :
        ↥(wOf V H)) : G) := key2.symm
  have hperp2 : CaseM.spForm a (SpExtras.mat n (GaloisField 2 1) g⁻¹ *ᵥ a) = 0 := by
    have h := spForm_mat_mulVec g (SpExtras.mat n (GaloisField 2 1) g⁻¹ *ᵥ a) a
    rw [mat_mulVec_mat_inv_mulVec] at h
    exact spForm_eq_zero_comm (h.symm.trans hperp)
  have hmem := ((h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne
    cfg.trans cfg.point).1 (SpExtras.mat n (GaloisField 2 1) g⁻¹ *ᵥ a)).mpr hperp2
  rw [hconj2]
  exact hmem

theorem qpCfg_exists_conj {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11a : Lemma11aStatement) (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) :
    ∃ x : G, x * cfg.aG * x⁻¹ ∈ P ∧ x * cfg.aG * x⁻¹ ∉ V ∧ x⁻¹ * cfg.aG * x ∈ P := by
  have h2n : 2 ≤ n := by
    have := cfg.three
    omega
  have hVH : V ≤ H := cfg.hyp.setup.mc.toMinCex.V_le_H
  have hH := cfg.hyp
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
    ((h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
      cfg.point).1 w₁).mpr hperp
  have huV : ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) ∉ V := by
    intro huV
    have hu1 : ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) ≠ 1 :=
      fun h => hw₀ (hinj w₁ 0 (h.trans h0.symm))
    have ha1 : cfg.aG ≠ 1 := fun h => cfg.ne (hinj a 0 (h.trans h0.symm))
    have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
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
  have hconj : (x : G) * cfg.aG * (x : G)⁻¹ =
      ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) := key.symm
  have h₂ : (x : G)⁻¹ * cfg.aG * (x : G) ∈ P :=
    qpCfg_inv_conj_mem_P h11a cfg hVH hgx (by rw [hg]; exact hperp)
  refine ⟨(x : G), ?_, ?_, h₂⟩
  · rw [hconj]
    exact huP
  · rw [hconj]
    exact huV

theorem qpCfg_exists_sec4Setup {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11a : Lemma11aStatement) (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) :
    ∃ b : G, b ∈ Stroth78.Q cfg.aG ∧ b ∉ Stroth78.ZQ cfg.aG ∧ IsConj cfg.aG b ∧
      cfg.aG ∈ Stroth78.QaOf b := by
  obtain ⟨x, hxP, hxV, hxP'⟩ := qpCfg_exists_conj h11a h11b h12 cfg
  have hQP : Q = P := le_antisymm cfg.qp cfg.hyp.setup.mc.toMinCex.P_le_Q
  have hQaConj : Qa (x * cfg.aG * x⁻¹) =
      (Qa cfg.aG).map (MulAut.conj x).toMonoidHom := by
    show fStar (Subgroup.centralizer ({x * cfg.aG * x⁻¹} : Set G)) =
      (fStar (Subgroup.centralizer ({cfg.aG} : Set G))).map (MulAut.conj x).toMonoidHom
    rw [Stroth78.centralizer_map_conj, Stroth78.fStar_map_conj]
  have hQa : Qa cfg.aG = P := by rw [qa_aG_eq h12 cfg, hQP]
  refine ⟨x * cfg.aG * x⁻¹, ?_, ?_, isConj_iff.2 ⟨x, rfl⟩, ?_⟩
  · show x * cfg.aG * x⁻¹ ∈ Qa cfg.aG
    rwa [hQa]
  · show x * cfg.aG * x⁻¹ ∉ centerIn (Qa cfg.aG)
    rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
    exact hxV
  · show cfg.aG ∈ Qa (x * cfg.aG * x⁻¹)
    rw [hQaConj, hQa]
    have h1 : (MulEquiv.toMonoidHom (MulAut.conj x)) (x⁻¹ * cfg.aG * x) = cfg.aG := by
      have h2 : (MulAut.conj x) (x⁻¹ * cfg.aG * x) = cfg.aG := by
        rw [MulAut.conj_apply]
        group
      exact h2
    have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hxP'
    rwa [h1] at h

theorem qpCfgSec4Setup_holds (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h12 : Lemma12Statement) (h13 : Lemma13Statement) : QPCfgSec4SetupStatement := by
  intro G _ _ M V Q P H n Φ ψ a T cfg
  exact ⟨qpCfg_assumption212 h11b h12 h13 cfg, qpCfg_exists_sec4Setup h11a h11b h12 cfg⟩

theorem qpCfgSec4Setup_of (hN : NaturalModuleStatement) (hI : Sec34IWStatement) :
    QPCfgSec4SetupStatement := by
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h11c : Lemma11cStatement := lemma11c_holds spRadFactsStatement_holds h11a
  exact qpCfgSec4Setup_holds h11a h11b
    (lemma12_holds hI Gamma.sec34GammaStatement_holds h11a h11b h11c)
    (lemma13_holds hN h11b h11c)

end CFSG.RankThree.GF2n.Tim79a

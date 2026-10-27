module

public import CFSG.RankThree.GF2n.Tim79a34Hauptsatz
public import CFSG.RankThree.GF2n.Tim79a34ResidualX

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa)

variable {G : Type} [Group G] [Finite G]

theorem commutator_xOf_eq_of_isPerfect {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (hperf : Group.IsPerfect (Xbar V H)) : ⁅xOf V H, xOf V H⁆ = xOf V H := by
  have hVH : V ≤ H := hc.V_le_H
  have hW : wOf V H ≤ ⁅xOf V H, xOf V H⁆ := by
    rw [← hc.commutator_wOf_xOf]
    exact Subgroup.commutator_mono (wOf_le_xOf V H) le_rfl
  have hker : (xToXbar hVH).ker ≤ commutator ↥(xOf V H) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ((xToXbar hVH x : Xbar V H) : Hbar V H) = 1 := by rw [hx]; rfl
    rw [coe_xToXbar] at h1
    have hmem : (x : G) ∈ (commutator ↥(xOf V H)).map (xOf V H).subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hW ((piBar_eq_one_iff _).mp h1)
    obtain ⟨c, hcmem, hcx⟩ := Subgroup.mem_map.mp hmem
    rwa [show c = x from Subtype.ext hcx] at hcmem
  have hmap : (commutator ↥(xOf V H)).map (xToXbar hVH) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (xToXbar_surjective hVH), ← commutator_def,
      hperf.commutator_eq_top]
  have htop : commutator ↥(xOf V H) = ⊤ := by
    have h := Subgroup.comap_map_eq (xToXbar hVH) (commutator ↥(xOf V H))
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at h
    exact h.symm
  rw [← Subgroup.map_subtype_commutator (xOf V H), htop, Subgroup.map_top,
    Subgroup.range_subtype]

theorem qpCfg_commutator_xOf_eq {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : ⁅xOf V H, xOf V H⁆ = xOf V H :=
  commutator_xOf_eq_of_isPerfect cfg.hyp.setup.mc.toMinCex
    (isPerfect_xbar_of_statedSp cfg.three cfg.centre
      (Φ.trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq cfg.centre.symm))))

theorem qpCfg_xOf_le_commutator {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : xOf V H ≤ commutator G := by
  rw [← qpCfg_commutator_xOf_eq cfg, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem qpCfg_V_le_commutator {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : V ≤ commutator G :=
  (le_xOf (V_mem_omegaOf V H)).trans (qpCfg_xOf_le_commutator cfg)

end CFSG.RankThree.GF2n.Tim79a

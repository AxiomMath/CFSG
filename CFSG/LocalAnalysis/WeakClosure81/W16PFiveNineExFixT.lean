module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFixTA
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRep
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

namespace ExCfg

variable {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X} {p : ℕ}

private theorem exists_mem_V₀_iota_eq_of_mem_traceSpace
    (c : ExCfg M V₀ V U S H φ p)
    (D : ModDataE (conjClosure V H) (conjClosure V₀ (conjClosure V H)))
    {t : ↥(conjClosure V H)} (htV : (t : G) ∈ V)
    {w : D.W} (hw : w ∈ traceSpace (tautRep D.W) (D.ρ t)) :
    ∃ e ∈ V₀, D.ι e = w := by
  rw [mem_traceSpace] at hw
  obtain ⟨v, hv⟩ := hw
  obtain ⟨e, heE, hev⟩ := D.ι_surj v
  rw [← hev] at hv
  rw [tautRep_apply] at hv
  refine ⟨⁅(t : G), e⁆, ?_, ?_⟩
  · have heI : e ∈ iSub16 V H :=
      conjClosure_V₀_conjClosure_le_iSub16 c.five c.std c.cex c.min.1 c.not_le heE
    have heS : e ∈ S :=
      Cex16.pCoreOf_le_S c.one c.std c.cex c.min.1
        (Cex16.iSub16_le_pCoreOf c.cex c.min.1 heI)
    have hcomm : ⁅e, (t : G)⁆ ∈ V₀ := Cex16.comm_mem_V₀ c.cex heS htV
    simpa [commutatorElement_inv e (t : G)] using V₀.inv_mem hcomm
  · rw [← hv, D.ι_commutator t.2 heE]
    rfl

theorem traceSpace_ne_bot (c : ExCfg M V₀ V U S H φ p)
    (D : ModDataE (conjClosure V H) (conjClosure V₀ (conjClosure V H)))
    (hK : ∀ q : ↥(conjClosure V H), φ q ∈ fusionOddCore X →
      (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) →
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype)
    {t : ↥(conjClosure V H)} (htV : (t : G) ∈ V) (ht : φ t ≠ 1) :
    traceSpace (tautRep D.W) (D.ρ t) ≠ ⊥ := by
  intro hbot
  have h0 : (D.ρ t : D.W →ₗ[ZMod 2] D.W) - 1 = 0 := by
    have hb : LinearMap.range ((D.ρ t : D.W →ₗ[ZMod 2] D.W) - 1) = ⊥ := by
      simpa only [traceSpace, tautRep_apply] using hbot
    exact LinearMap.range_eq_bot.mp hb
  have hρt : D.ρ t = 1 := by
    refine LinearEquiv.ext fun w => ?_
    have h1 := congrArg (fun f : D.W →ₗ[ZMod 2] D.W => f w) (sub_eq_zero.mp h0)
    simpa using h1
  have htker : t ∈ D.ρ.ker := MonoidHom.mem_ker.2 hρt
  have hnorm : ((D.ρ.ker).map φ).Normal :=
    Subgroup.Normal.map (inferInstance : (D.ρ.ker).Normal) φ c.bar.surjective
  have hφtker : φ t ∈ (D.ρ.ker).map φ := Subgroup.mem_map.2 ⟨t, htker, rfl⟩
  set Y : Subgroup X := SevenK.barSub (conjClosure V H) φ V with hY
  have hY2 : Nat.card Y = 2 := by rw [hY]; simpa using c.shape.1
  have hφtY : φ t ∈ Y := by
    rw [hY]; exact SevenK.mem_barSub.2 ⟨t, htV, rfl⟩
  have hne : Y ⊓ (D.ρ.ker).map φ ≠ ⊥ := by
    intro hb
    have hmem : φ t ∈ (⊥ : Subgroup X) := hb ▸ Subgroup.mem_inf.2 ⟨hφtY, hφtker⟩
    exact ht (Subgroup.mem_bot.1 hmem)
  have hYle : Y ≤ (D.ρ.ker).map φ := CFSG.Quasithin.le_of_card_eq_two_of_inf_ne_bot hY2 hne
  have hgen : Subgroup.normalClosure (Y : Set X) = ⊤ := by
    rw [hY]
    exact IsMinFam16.normalClosure_barSub_eq_top c.one c.std c.cex c.min c.not_le c.bar
  have hCmap_top : (D.ρ.ker).map φ = ⊤ := by
    haveI : ((D.ρ.ker).map φ).Normal := hnorm
    have hle := Subgroup.normalClosure_le_normal hYle
    rw [hgen] at hle
    exact top_le_iff.mp hle
  have hKleC : ∀ k : ↥(conjClosure V H), D.ρ k = 1 := by
    intro k
    have hk : φ k ∈ (D.ρ.ker).map φ := by rw [hCmap_top]; exact Subgroup.mem_top _
    obtain ⟨d, hdker, hdφ⟩ := Subgroup.mem_map.1 hk
    have hdρ : D.ρ d = 1 := MonoidHom.mem_ker.1 hdker
    have hdker2 : d⁻¹ * k ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdφ]
      group
    have hdn : ((d⁻¹ * k : ↥(conjClosure V H)) : G) ∈ pCoreOf 2 (conjClosure V H) :=
      (c.bar.ker_iff (d⁻¹ * k)).mp (MonoidHom.mem_ker.1 hdker2)
    have hdcent : ((d⁻¹ * k : ↥(conjClosure V H)) : G) ∈
        centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
      Subgroup.centralizer_le
        (fun _ hx => conjClosure_V₀_conjClosure_le_iSub16 c.five c.std c.cex c.min.1 c.not_le hx)
        (c.pCore_le hdn)
    have hdρ2 : D.ρ (d⁻¹ * k) = 1 := (D.ρ_eq_one_iff (d⁻¹ * k)).mpr hdcent
    calc D.ρ k = D.ρ (d * (d⁻¹ * k)) := by rw [show d * (d⁻¹ * k) = k by group]
      _ = D.ρ d * D.ρ (d⁻¹ * k) := map_mul D.ρ d (d⁻¹ * k)
      _ = 1 := by rw [hdρ, hdρ2, one_mul]
  have hNle : fusionOddCore X ≤
      (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
    intro n hn
    obtain ⟨q, hq⟩ := c.bar.surjective n
    have hqN : φ q ∈ fusionOddCore X := by rw [hq]; exact hn
    have hqcent : (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
      (D.ρ_eq_one_iff q).mp (hKleC q)
    rw [← hq]
    exact hK q hqN hqcent
  have hEq : (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype =
      fusionOddCore X :=
    le_antisymm (Subgroup.map_subtype_le (Subgroup.center ↥(fusionOddCore X))) hNle
  have hcard_center : Nat.card (Subgroup.center ↥(fusionOddCore X)) =
      Nat.card ↥(fusionOddCore X) := by
    rw [← Subgroup.card_map_of_injective (f := (fusionOddCore X).subtype)
      (fusionOddCore X).subtype_injective, hEq]
  have hpp : p = p ^ 3 := by
    calc p = Nat.card (Subgroup.center ↥(fusionOddCore X)) := c.extra.center_order_p.symm
      _ = Nat.card ↥(fusionOddCore X) := hcard_center
      _ = p ^ 3 := c.card
  have h13 : (1 : ℕ) = 3 := Nat.pow_right_injective c.prime.one_lt (by simpa using hpp)
  omega

theorem commute_of_traceSpace_inf_ne_bot (c : ExCfg M V₀ V U S H φ p)
    (D : ModDataE (conjClosure V H) (conjClosure V₀ (conjClosure V H)))
    {t : ↥(conjClosure V H)} (htV : (t : G) ∈ V) (k : ↥(conjClosure V H))
    (hk : traceSpace (tautRep D.W) (D.ρ t) ⊓
      (traceSpace (tautRep D.W) (D.ρ t)).map (tautRep D.W (D.ρ k)) ≠ ⊥) :
    D.ρ k * D.ρ t = D.ρ t * D.ρ k := by
  by_cases ht1 : φ t = 1
  · have htn : (t : G) ∈ pCoreOf 2 (conjClosure V H) := (c.bar.ker_iff t).mp ht1
    have htcent : (t : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
      Subgroup.centralizer_le
        (fun _ hx => conjClosure_V₀_conjClosure_le_iSub16 c.five c.std c.cex c.min.1 c.not_le hx)
        (c.pCore_le htn)
    have hρt : D.ρ t = 1 := (D.ρ_eq_one_iff t).mpr htcent
    rw [hρt, mul_one, one_mul]
  · obtain ⟨w, hw_mem, hw0⟩ := (Submodule.ne_bot_iff _).mp hk
    have hwT : w ∈ traceSpace (tautRep D.W) (D.ρ t) := (Submodule.mem_inf.1 hw_mem).1
    have hwTk : w ∈ (traceSpace (tautRep D.W) (D.ρ t)).map (tautRep D.W (D.ρ k)) :=
      (Submodule.mem_inf.1 hw_mem).2
    obtain ⟨e₁, he₁V₀, he₁w⟩ := exists_mem_V₀_iota_eq_of_mem_traceSpace c D htV hwT
    have he₁1 : e₁ ≠ 1 := fun h => hw0 (by rw [← he₁w, h, D.ι_one])
    obtain ⟨w', hw'T, hw'w⟩ := Submodule.mem_map.1 hwTk
    obtain ⟨e₂, he₂V₀, he₂w⟩ := exists_mem_V₀_iota_eq_of_mem_traceSpace c D htV hw'T
    have hw'val : D.ρ k w' = w := by
      have h : (D.ρ k : D.W →ₗ[ZMod 2] D.W) w' = w := by
        simpa only [tautRep_apply] using hw'w
      simpa only [← LinearEquiv.coe_toLinearMap] using h
    have he₂E : e₂ ∈ conjClosure V₀ (conjClosure V H) :=
      le_conjClosure V₀ (conjClosure V H) he₂V₀
    have hk_e₂ : (k : G) * e₂ * (k : G)⁻¹ ∈ conjClosure V₀ (conjClosure V H) := by
      have hnorm : (k : G) ∈
          Subgroup.normalizer (conjClosure V₀ (conjClosure V H) : Set G) :=
        conjClosure_le_normalizer_conjClosure_V₀ (V := V) (H := H) k.2
      exact (Subgroup.mem_normalizer_iff.1 hnorm e₂).1 he₂E
    have hι : D.ι e₁ = D.ι ((k : G) * e₂ * (k : G)⁻¹) := by
      calc D.ι e₁ = w := he₁w
        _ = D.ρ k w' := hw'val.symm
        _ = D.ρ k (D.ι e₂) := by rw [he₂w]
        _ = D.ι ((k : G) * e₂ * (k : G)⁻¹) := D.ρ_ι k e₂ he₂E
    have he₁E : e₁ ∈ conjClosure V₀ (conjClosure V H) :=
      le_conjClosure V₀ (conjClosure V H) he₁V₀
    have he₁_eq : e₁ = (k : G) * e₂ * (k : G)⁻¹ := D.ι_injOn he₁E hk_e₂ hι
    have he₁_inf : e₁ ∈ V₀ ⊓ CFSG.Quasithin.conjSubgroup V₀ ((k : G)⁻¹) := by
      refine ⟨he₁V₀, ?_⟩
      refine (CFSG.Quasithin.mem_conjSubgroup_iff (A := V₀) (g := (k : G)⁻¹)).mpr ?_
      have hconj : (k : G)⁻¹ * ((k : G) * e₂ * (k : G)⁻¹) * (k : G) = e₂ := by group
      rw [inv_inv, he₁_eq, hconj]
      exact he₂V₀
    have hne_inf : V₀ ⊓ CFSG.Quasithin.conjSubgroup V₀ ((k : G)⁻¹) ≠ ⊥ := by
      intro hb
      exact he₁1 (Subgroup.mem_bot.1 (hb ▸ he₁_inf))
    have hkM : (k : G) ∈ M := by
      by_contra hkM
      have hknot : (k : G)⁻¹ ∉ M := fun h => hkM (by simpa using M.inv_mem h)
      exact hne_inf (by rw [inf_comm]; exact c.cex.hyp.conj_inf_eq_bot hknot)
    have hkV : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
      rwa [c.cex.hyp.h6.normalizer_eq]
    have hknorm : φ k ∈ Subgroup.normalizer
        (SevenK.barSub (conjClosure V H) φ V : Set X) := by
      simpa using
        (barSub_mem_normalizer (K := conjClosure V H) (V := V) (φ := φ) k.2 hkV)
    have hY2 : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := by
      simpa using c.shape.1
    have hφtY : φ t ∈ SevenK.barSub (conjClosure V H) φ V :=
      SevenK.mem_barSub.2 ⟨t, htV, rfl⟩
    have hcomm_φ : φ k * φ t * (φ k)⁻¹ = φ t :=
      conj_eq_self_of_mem_normalizer_of_card_two hY2 hknorm hφtY ht1
    have hcommut : φ ⁅k, t⁆ = 1 := by
      rw [map_commutatorElement (f := φ), commutatorElement_def, hcomm_φ]
      group
    have hker' : ((⁅k, t⁆ : ↥(conjClosure V H)) : G) ∈ pCoreOf 2 (conjClosure V H) :=
      (c.bar.ker_iff ⁅k, t⁆).mp hcommut
    have hcent : ((⁅k, t⁆ : ↥(conjClosure V H)) : G) ∈
        centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
      Subgroup.centralizer_le
        (fun _ hx => conjClosure_V₀_conjClosure_le_iSub16 c.five c.std c.cex c.min.1 c.not_le hx)
        (c.pCore_le hker')
    have hρcomm : D.ρ ⁅k, t⁆ = 1 := (D.ρ_eq_one_iff ⁅k, t⁆).mpr hcent
    rw [map_commutatorElement (f := D.ρ)] at hρcomm
    exact commutatorElement_eq_one_iff_mul_comm.mp hρcomm

end ExCfg

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.Quasithin.MS93.S33Bad
public import CFSG.Quasithin.MS93.S38OffHat
public import CFSG.Quasithin.MS93.S38OffV

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem xOffData_of_isHatA6U' (h : PUHyp M T L) (hX : IsHatA6U M T L) : XOffData M T := by
  obtain ⟨-, -, hU, h6⟩ := hX
  refine ⟨fun F₁ F₂ h₁ h₂ => S38H.sup_eq_of_isXOff hU h h6 h₁ h₂, fun F hF => ?_,
    fun F hF => S38H.exists_zc hU h h6 hF⟩
  obtain ⟨-, -, -, hQ4, -, -, hX4⟩ := S38H.offender_facts hU h h6 hF
  rw [hX4, hQ4]

theorem mem_sup_of_hat (h : PUHyp M T L) (hX : IsHatA6U M T L) {F : Subgroup G}
    (hF : IsXOff M T F) {E : Subgroup G} (hEF : E ≤ F) (hEQ : ¬ E ≤ pCoreOf 2 M) {y : G}
    (hyT : y ∈ T) (hyF : y ∈ Subgroup.centralizer (F : Set G))
    (hyR : y ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, hU, h6⟩ := hX
  have hHM := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  obtain ⟨zH, hcen, h3, hfp⟩ := hHM.exists_z
  obtain ⟨hFH, -, -, -, -, -, -⟩ := S38H.offender_facts hU h h6 hF
  set y' := convI hU ⟨y, S38H.le_normalizer_Uq_T h hyT⟩ with hy'
  have hyN : y' ∈ Subgroup.normalizer
      (autI hU L : Set (MulAut (IntMod (Uq M T L) hU))) :=
    S38H.autI_le_normalizer hU h.le_normalizer h.le (convI_mem_autI hU hyT _)
  obtain ⟨e, heE, heQ⟩ := Set.not_subset.1 hEQ
  have heT : e ∈ T := hF.1 (hEF heE)
  have heN := S38H.le_normalizer_Uq_T h heT
  set e' := convI hU ⟨e, heN⟩ with he'
  have he'H : e' ∈ autI hU L := hFH (convI_mem_autI hU (hEF heE) heN)
  have he'z : e' * zH = zH * e' := S38H.HatMod.comm_z_of_mem hcen he'H
  obtain ⟨v, hv⟩ : ∃ v : IntMod (Uq M T L) hU, e' v * v⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : e' = 1 := MulEquiv.ext fun w => by
      have := hall w
      rw [mul_inv_eq_one] at this
      exact this
    exact heQ (S38H.mem_pCoreOf_of_mem_centralizer h heT ((convI_eq_one_iff hU _).1 h1))
  have hfixR : ∀ w : IntMod (Uq M T L) hU, y' (e' w * w⁻¹) = e' w * w⁻¹ := by
    intro w
    apply IntMod.val_injective
    rw [hy', convI_apply_val]
    have hmem : (e' w * w⁻¹).val ∈ ⁅Uq M T L, E⁆ := by
      rw [IntMod.val_mul, IntMod.val_inv, he', convI_apply_val, Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator heE w.val_mem
      rwa [commutatorElement_def] at this
    have hc := Subgroup.mem_centralizer_iff.mp hyR _ hmem
    show y * (e' w * w⁻¹).val * y⁻¹ = (e' w * w⁻¹).val
    rw [← hc, mul_inv_cancel_right]
  have hzr : (zH : MulAut (IntMod (Uq M T L) hU)) (e' v * v⁻¹) =
      e' ((zH : MulAut _) v) * ((zH : MulAut _) v)⁻¹ := by
    rw [map_mul, map_inv]
    congr 1
    exact (congrArg (fun φ : MulAut (IntMod (Uq M T L) hU) => φ v) he'z).symm
  have hz1 : (zH : MulAut (IntMod (Uq M T L) hU)) ≠ 1 := by
    intro h1
    apply hv
    exact hfp _ (by rw [h1, MulAut.one_apply])
  have hyz : y' * zH = zH * y' := by
    rcases HatA6.conj_z_cases hcen h3 hz1 hyN with hc | hc
    · exact hc
    · exfalso
      have h1 := congrArg (fun φ : MulAut (IntMod (Uq M T L) hU) => φ (e' v * v⁻¹)) hc
      simp only [MulAut.mul_apply] at h1
      rw [hfixR v, hzr, hfixR, ← hzr] at h1
      have h2 : e' v * v⁻¹ = (zH : MulAut _) (e' v * v⁻¹) :=
        (zH : MulAut (IntMod (Uq M T L) hU)).injective h1
      exact hv (hfp _ h2.symm)
  exact S38H.mem_sup_of_mem_L hU h h6 hF hyT hyF (hHM.mem_of_comm_z hcen hyN hyz)

@[expose] def S33BadG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 → ⁅Xq M, L⁆ ≤ Uq M T L → IsG2U h.le L →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
    ∀ Y : Subgroup (puAmalgam h.le).Universal, Y ≤ Qv _ (geo _ α' (baseA _) 1) →
      Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) →
      Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) →
      ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
          ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
            ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆

theorem s33Bad_of_g2 (hG2 : S33BadG2) : S33Bad := by
  intro G _ _ M T L h hb2 hXL hbad _ _ α' hc Y hY hYR hYX hn
  rcases hbad with hA | hD2 | hT | hZ | hG
  · exact hn ((commutator_le_of_offData h (xOffData_of_isHatA6U' h hA)
      (fun F hF E hEF hEQ y hyT hyF hyR => mem_sup_of_hat h hA hF hEF hEQ hyT hyF hyR) hc hY hYR
      hYX).trans le_sup_left)
  · exact not_hyp_of_cent h (xOffData_of_isDoubleSL3U' h hD2)
      (fun F hF => h.inf_centralizer_le_of_isDoubleSL3U hD2 hF) hc hY hYR hYX hn
  · exact not_hyp_of_cent h (h.xOffData_of_isSL3TwoU hT) (h.xOffCent_of_isSL3TwoU hT).1 hc hY hYR
      hYX hn
  · exact not_hyp_of_cent h (h.xOffData_of_isSL3TwoZ hZ) (h.xOffCent_of_isSL3TwoZ hZ).1 hc hY hYR
      hYX hn
  · exact hn (hG2 G M T L h hb2 hXL hG α' hc Y hY hYR hYX)

end CFSG.Quasithin.MS93.S33

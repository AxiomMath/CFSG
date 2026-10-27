module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA5
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA10
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA6

public section

open CFSG.Open
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_sol_of_mem_sol_of_mul_eq {W Z L : Subgroup G} (hZW : Z ≤ W) (hZL : Z ≤ L)
    (hZsol : (Z : Set G) * (sol L : Set G) = (kOf L : Set G)) {d : G} (hdL : d ∈ L)
    (hdW : d ∈ sol W) (hdZ : d ∈ Subgroup.normalizer (Z : Set G)) : d ∈ sol L := by
  have hZK : Z ≤ kOf L := fun z hz => by
    have : z ∈ (Z : Set G) * (sol L : Set G) := ⟨z, hz, 1, one_mem _, mul_one z⟩
    rw [hZsol] at this
    exact this
  have hZsolW : Z ≤ Subgroup.normalizer (sol W : Set G) :=
    hZW.trans (Thm41Aux.le_normalizer_sol W)
  have hZsolL : Z ≤ Subgroup.normalizer (sol L : Set G) :=
    hZL.trans (Thm41Aux.le_normalizer_sol L)
  have hR₀ : Z ⊓ sol W ≤ sol L := by
    have hsolW := isSolvable_sol W
    have hR₀sol : Group.IsSolvable ↥(Z ⊓ sol W) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_right : Z ⊓ sol W ≤ sol W))
    have hR₁sol : Group.IsSolvable ↥(sol L ⊔ (Z ⊓ sol W)) :=
      AssocSup.isSolvable_sup (inf_le_left.trans hZsolL) hR₀sol (isSolvable_sol L)
    have hzN : Z ≤ Subgroup.normalizer ((sol L ⊔ (Z ⊓ sol W) : Subgroup G) : Set G) :=
      le_normalizer_sup hZsolL (le_normalizer_inf Subgroup.le_normalizer hZsolW)
    have hn : kOf L ≤ Subgroup.normalizer ((sol L ⊔ (Z ⊓ sol W) : Subgroup G) : Set G) := by
      intro x hx
      have hx' : x ∈ (Z : Set G) * (sol L : Set G) := by rw [hZsol]; exact hx
      obtain ⟨z, hz, s, hs, rfl⟩ := hx'
      exact mul_mem (hzN hz) (Subgroup.le_normalizer (Subgroup.mem_sup_left hs))
    have hle := Thm41Aux.le_sol_of_normal_solvable
      (sup_le (sol_le_kOf L) (inf_le_left.trans hZK)) hn hR₁sol
    rw [Thm41Aux.sol_kOf_eq] at hle
    exact le_sup_right.trans hle
  refine mem_sol_of_commutator_mem_kOf hdL fun x hx => ?_
  have hx' : x ∈ (Z : Set G) * (sol L : Set G) := by rw [hZsol]; exact hx
  obtain ⟨z, hz, s, hs, rfl⟩ := hx'
  have e : ⁅d, z * s⁆ = ⁅d, z⁆ * (z * ⁅d, s⁆ * z⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem ?_ ?_
  · refine hR₀ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : d * z * d⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hdZ z).mp hz
      have e1 : ⁅d, z⁆ = (d * z * d⁻¹) * z⁻¹ := by simp only [commutatorElement_def]
      rw [e1]
      exact mul_mem h1 (inv_mem hz)
    · have h1 : z * d⁻¹ * z⁻¹ ∈ sol W :=
        (Subgroup.mem_normalizer_iff.mp (hZsolW hz) d⁻¹).mp (inv_mem hdW)
      have e1 : ⁅d, z⁆ = d * (z * d⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem hdW h1
  · have h1 : ⁅d, s⁆ ∈ sol L := by
      have hd' : d * s * d⁻¹ ∈ sol L :=
        (Subgroup.mem_normalizer_iff.mp (Thm41Aux.le_normalizer_sol L hdL) s).mp hs
      have e1 : ⁅d, s⁆ = (d * s * d⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
      rw [e1]
      exact mul_mem hd' (inv_mem hs)
    exact (Subgroup.mem_normalizer_iff.mp (hZsolL hz) _).mp h1

theorem false_of_forall_thetaMG_mem
    (h : Counterexample p A θ)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) : False := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨W, hW⟩ := exists_setting h
  have hin : CompInput p W := compInput_of_nearPSolvable hθ.prime hW.mem_mtil.1.2.2.2.1
  obtain ⟨S, hSm, hSsol, hSmax⟩ := exists_ssol hθ h.hyp.card.ge
  have hsolS : sol W ≤ S :=
    hSmax _ (sol_mem_mhat hθ hW.mem_mtil) (isSolvable_sol W)
  have hSW : S ≤ W := ssol_le h hW hI hin hSm hSsol hsolS
  obtain ⟨B, hB, hnot⟩ := h.exists_not_kOf_le_thetaOf hW.mem_mtil.1
  have hBne : B ≠ ⊥ := by
    rintro rfl
    have h2 := hB.2
    rw [Subgroup.card_bot] at h2
    exact (Nat.one_lt_pow (by norm_num) hθ.prime.one_lt).ne h2
  have hZm : WB W B ∈ mhat p A θ := WB_mem_mhat hθ hW.mem_mtil hB.1
  have hZsol : (WB W B : Set G) * (sol W : Set G) = (kOf W : Set G) :=
    WB_mul_sol hθ hW.mem_mtil hin hB
  have hZH : thetaOf θ B ≤ Subgroup.normalizer (WB W B : Set G) :=
    thetaOf_le_normalizer_WB h hW hI hin hB.1
  have hHBm : thetaOf θ B ∈ mtil p A θ := thetaOf_mem_mtil hθ hB.1 hBne
  have hZW : WB W B ≤ W := (WB_le_kOf W B).trans (kOf_le W)
  have hZns : ¬ Group.IsSolvable ↥(WB W B) := by
    intro hZs
    have hZS : WB W B ≤ S := hSmax _ hZm hZs
    have hK : kOf W ≤ S := by
      rw [← WB_sup_sol hθ hW.mem_mtil hin hB]
      exact sup_le hZS hsolS
    have hperf := perfRes_le_kOf h hW hI hin
    have hPs : Group.IsSolvable ↥(perfRes W) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective ((hperf.trans hK).trans (le_refl S)))
    have h1 : perfRes (perfRes W) = ⊥ := (perfRes_eq_bot_iff _).mpr hPs
    rw [perfRes_eq_self_of_isPerfect (isPerfect_perfRes W)] at h1
    exact hW.not_isSolvable ((perfRes_eq_bot_iff W).mp h1)
  have hZne : WB W B ≠ ⊥ := fun hb => hZns (by rw [hb]; infer_instance)
  obtain ⟨L, hL, -, hLmax⟩ := h.isLocallyComplete (WB W B) hZm.1 hZne
  have hHBL : thetaOf θ B ≤ L := hLmax _ hHBm.1 hZH
  have hZL : WB W B ≤ L := hLmax _ hZm.1 Subgroup.le_normalizer
  have hDH : dsub A θ ≤ thetaOf θ B := thetaOf_anti hB.1
  have hDL : dsub A θ ≤ L := hDH.trans hHBL
  have hLt : L ∈ mtil p A θ := ⟨hL, hDL⟩
  have hLm : L ∈ mhat p A θ := mtil_subset_mhat hLt
  have hLns : ¬ Group.IsSolvable ↥L := fun hs =>
    hZns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hZL))
  obtain ⟨M, -, -, hpair, hDsol⟩ := exists_pair_perfRes hθ hLt hLns
  set C := secCenIn (perfRes L ⊔ dsub A θ) (perfRes L) M with hC
  set Y := dsub A θ ⊓ C with hY
  have hYd : Y ∈ dset p A θ := ⟨(perfRes L ⊔ C, C), hpair, rfl⟩
  have hpairY : (perfRes L ⊔ C, C) ∈ pairsY p A θ Y := ⟨hpair, inf_comm _ _⟩
  have hCL : C ≤ L := (inf_le_left : C ≤ perfRes L ⊔ dsub A θ).trans
    (sup_le (perfRes_le L) hDL)
  have hX₁L : perfRes L ⊔ C ≤ L := sup_le (perfRes_le L) hCL
  have hLc : L ∈ cset p A θ Y := ⟨hLt, (perfRes L ⊔ C, C), hpairY, hX₁L⟩
  have hX₁V : perfRes L ⊔ C ≤ thetaMG p A θ Y :=
    (le_iSup₂ (f := fun P (_ : P ∈ pairsYX p A θ Y L) => P.1) (perfRes L ⊔ C, C)
      ⟨hpairY, hX₁L⟩).trans (thetaM_le_thetaMG hLc)
  have hDsolY : dsub A θ ⊓ sol W ≤ Y := fun d hd =>
    Subgroup.mem_inf.mpr ⟨hd.1, hDsol d hd.1 (mem_sol_of_mem_sol_of_mul_eq hZW hZL
      (hW.sol_mul _ hZm L hLm hZsol hZL) (hDL hd.1) hd.2 (hZH (hDH hd.1)))⟩
  have hWsol : W ≤ Subgroup.normalizer (sol W : Set G) := Thm41Aux.le_normalizer_sol W
  have hYD : Y ≤ dsub A θ := inf_le_left
  have hYW : Y ≤ W := hYD.trans hW.mem_mtil.2
  have hCm : C ∈ mhat p A θ := hpair.2.1
  have hYadm : Admits (dsub A θ ⊔ A) Y :=
    Admits.inf (sup_le Subgroup.le_normalizer (admits_dsub hθ))
      (sup_le hCm.2 hCm.1.1)
  have hQadm : Admits (dsub A θ ⊔ A) (sol W ⊔ Y) :=
    Admits.sup (sup_le (hW.mem_mtil.2.trans hWsol)
      (hW.mem_mtil.1.1.trans fun _ hg => Thm41Aux.mem_normalizer_sol_of_mem_normalizer hg))
      hYadm
  have hQm : sol W ⊔ Y ∈ mhat p A θ :=
    mem_mhat_of_le_mtil hθ.prime hW.mem_mtil (sup_le (sol_le W) hYW) hQadm
  have hQD : (sol W ⊔ Y) ⊓ dsub A θ = Y := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hYD)
    obtain ⟨hxQ, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨s, hs, y, hy, rfl⟩ := (mem_sup_iff_mul (hYW.trans hWsol)).mp hxQ
    have hsD : s ∈ dsub A θ := by
      have := mul_mem hxD (inv_mem (hYD hy))
      simpa using this
    exact mul_mem (hDsolY ⟨hsD, hs⟩) hy
  have hQV : sol W ⊔ Y ≤ thetaMG p A θ Y :=
    le_thetaMG_of_mem_mhat hθ h.hyp.card hYd hQm hQD
  have hKV : kOf W ≤ thetaMG p A θ Y := by
    refine (WB_sup_sol hθ hW.mem_mtil hin hB).symm.le.trans (sup_le ?_ ?_)
    · exact (WB_le_perfRes hZL).trans ((le_sup_left : perfRes L ≤ perfRes L ⊔ C).trans hX₁V)
    · exact (le_sup_left : sol W ≤ sol W ⊔ Y).trans hQV
  have hVW : thetaMG p A θ Y ≤ W :=
    hW.le_of_kOf_le _ (thetaMG_mem_mhat hI hYd) hKV
  have hperfH : perfRes (thetaOf θ B) ≤ W :=
    (perfRes_mono hHBL).trans ((le_sup_left : perfRes L ≤ perfRes L ⊔ C).trans (hX₁V.trans hVW))
  have hsolH : sol (thetaOf θ B) ≤ W :=
    (hSmax _ (sol_mem_mhat hθ hHBm) (isSolvable_sol _)).trans hSW
  exact hnot ((kOf_le_perfRes_sup_sol _).trans (sup_le hperfH hsolH))

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near

module

public import CFSG.Quasithin.Background.SmithD321Count
public import CFSG.Quasithin.Background.SmithD321Main
public import CFSG.Quasithin.Background.SmithD321Ext

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Pointwise

section Two

variable {W : Type} [CommGroup W] {M Mp L : Subgroup (MulAut W)}

theorem d321Two_of_family (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hLM : L ≤ M) {V : Subgroup W} (hVZ : V ⊓ fixV L = V ⊓ fixV Mp) (hL3 : IsPSL 3 2 1 ↥L)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (S : Fin 4 → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    (hS : letI := qAct hMp; ∀ i, XMod.IsInv ↥(L.subgroupOf M) (S i) ∧
      XMod.Iso ↥(L.subgroupOf M) (S i) (tilde Mp ⊤ V))
    (hind : ∀ i, S i ⊓ ⨆ (j : Fin 4) (_ : j ≠ i), S j = ⊥)
    (hsup : (⨆ i, S i) = tilde Mp ⊤ (commV L)) (hZ : commV L ⊓ fixV Mp = ⊥) : D321Two L := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  rw [hVZ] at hπ
  refine ⟨hL3, ?_⟩
  have h := directSumOfCopies_of_family hMp hLM hπ
    (fun g hg u hu => B15P4.map_commV_mem (Subgroup.le_normalizer hg) u hu) S hS hind hsup
  rwa [hZ] at h

end Two


section Final

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem sideHyp_of_nat (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hU : commSub (orbSup T V) L = V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hL3 : IsPSL 3 2 1 ↥L)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1) : SideHyp hS.hD.hyp.Mp_normal L V := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hI := hS.irr_L hVt
  have hLoΛ := cases_congr (Subgroup.subgroupOfEquivOfLe hS.L_le)
    (Or.inl hL3 : IsPSL 3 2 1 ↥L ∨ Nonempty (↥L ≃* alternatingGroup (Fin 5)))
  have hiso := iso_of_factorization hI.1 (smul_tildeV_of_mem_T0 hS.toD321Base hU)
    (factorization_of_out_two hS.toD321Base (out_two_of_cases hLoΛ (normalizes_Λ L)))
  obtain ⟨k, hY⟩ := isotypic_of_iso hS.toD321Base hVt hiso
  have hb := nonswap_bound hA21 hB42 h9 hS hVt hAC hAL (q₀ := 1 / 2) (Or.inl rfl)
  have hd0 : 0 < rk ↥(tilde Mp ⊤ V) := Nat.pos_of_ne_zero fun h =>
    hI.2.1.ne' ((rk_eq_zero_iff hS.quot_sq).1 h)
  have hk4 : k ≤ 4 := by
    have h1 : rk ↥(tilde Mp ⊤ (commV L)) ≤ 4 * rk ↥(tilde Mp ⊤ V) := by
      have h2 : ((rk ↥(tilde Mp ⊤ (commV L)) : ℕ) : ℚ) ≤ 4 * (rk ↥(tilde Mp ⊤ V) : ℚ) := by
        linarith
      exact_mod_cast h2
    rw [hY.2.2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hd0
  obtain ⟨rfl, y, hy, hyL, hy5, hymove⟩ := kplus_l32 hS hVt hU hL3 hnat hY hk4
  have hF := sideFL_of hS.toD321Base hVt hS.htop
  have hIc : XMod.commOf ↥(L.subgroupOf M) (tilde Mp ⊤ V) = tilde Mp ⊤ V :=
    commOf_eq_self_of_isIrr hI (hF.moved _ hF.le_Y hF.irr)
  obtain ⟨K, hKf, hKfin, hK, π, hR⟩ := hnat
  refine ⟨hS.L_le, hS.L_le_Mp, hS.hsimp, hS.perfect, ?_, ⟨K, hKf, hKfin, π, hK, hR⟩, hI, hY,
    fun R hRY hR => commOf_eq_of_le_isoComp hI hIc hR (hRY.trans hY.2.1),
    ⟨y, hy, hyL, hy5, hymove⟩⟩
  refine le_antisymm (inf_le_inf_left _ (fixV_anti hS.L_le_Mp)) fun w hw => ⟨hw.1, ?_⟩
  rw [hS.hMp, fixV_sup]
  exact ⟨hw.2, hS.commV_le_fixV hVt hw.1⟩

theorem concl_of_ffSide (hA21 : AsA21SQTKSection)
    (hB42 : AsB42) (h9 : A38B42) (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hff : FFSide hS.hD.hyp.Mp_normal L) : D321Two L ∨ D321Three Mp L := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hMp := hS.hD.hyp.Mp_normal
  have hLM := hS.L_le
  have hVZ := inf_fixV_L hS.toD321Base hVt
  rcases type_of_ffSide hS hVt hff with ⟨n, hn, hnat⟩ | ⟨hL3, hnat⟩ | ⟨hA5, hcard⟩
  · have hL3 : ¬ IsPSL 3 2 1 ↥L := by
      intro h3
      obtain ⟨K, hKf, hKfin, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL hnat
      have : CharP K 2 := charP_two_of_card hK
      have : Fintype K := Fintype.ofFinite K
      exact not_isPSL_two_of_isPSL32 h3 (SmithD37.isPSL_of_mulEquiv hn hK e.symm)
    obtain ⟨S, hS', hind, hsup⟩ := family_of_isotypic hS.toD321Base hVt
      (isotypic_two hA21 hB42 h9 hS hVt hU hAC hAL hL3)
    rw [← hVZ] at hnat
    exact Or.inr (d321Three_of_family hMp hLM hVZ hn hnat S hS' hind hsup)
  · have hSide := sideHyp_of_nat hA21 hB42 h9 hS hVt hU hAC hAL hL3 hnat
    have hSide' := sideHyp_of_nat hA21 hB42 h9 hS.swapV (D321Base.swapV_fix hS.toD321Base hVt)
      (D321Base.swapV_caseIIa hS.toD321Base hU) hAC (le_normalizer_Lt hS hAL)
      (SmithD37.isPSL_transfer (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).symm hL3)
      (binaryNaturalSL_conj hS.toD321Base hnat)
    have hUU : commV L ⊓ commV (conjAutSub t L) ≤ fixV Mp := fun w hw => by
      rw [hS.hMp, fixV_sup]
      exact ⟨hS.commV_Lt_le_fixV hVt hw.2, hS.commV_le_fixV hVt hw.1⟩
    have hA1 : A ≠ ⊥ := fun h => by
      have h1 := hS.rk_pos
      rw [h, rk_bot] at h1
      exact lt_irrefl _ h1
    have hAr : nSec A ⊤ ⊥ ≤ 2 * rk ↥A := by
      have h1 := hS.rkIdx_le
      have h2 := rk_add_rkIdx (fixV A)
      unfold nSec
      rw [secFix_bot, top_inf_eq, rk_top]
      omega
    have hAC' : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓
        Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) = ⊥ := by
      rw [eq_bot_iff]
      rintro a ⟨⟨haA, haL⟩, haLt⟩
      have haL' : ∀ h ∈ L, h * a = a * h :=
        Subgroup.mem_centralizer_iff.1 (haL : a ∈ Subgroup.centralizer (L : Set (MulAut W)))
      have haLt' : ∀ h ∈ conjAutSub t L, h * a = a * h :=
        Subgroup.mem_centralizer_iff.1 (haLt : a ∈ Subgroup.centralizer
          ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)))
      have hcMp : a ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
        refine ⟨haA, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        obtain ⟨b, hb, c, hc, rfl⟩ := hS.exists_mul_of_mem_Mp hx
        rw [mul_assoc, haLt' c hc, ← mul_assoc, haL' b hb, mul_assoc]
      rwa [hAC] at hcMp
    have hZ : commV L ⊓ fixV Mp = ⊥ := commV_inf_fixV_eq_bot hS.exp hS.t_mem rfl hSide hSide'
      hUU hS.A_le hAL (le_normalizer_Lt hS hAL) hS.elemAb.2 hS.elemAb.1 hA1 hAr hAC'
    obtain ⟨S, hS', hind, hsup⟩ := family_of_isotypic hS.toD321Base hVt hSide.homog
    rw [← hVZ] at hnat
    exact Or.inl (d321Two_of_family hMp hLM hVZ hL3 hnat S hS' hind hsup hZ)
  · exfalso
    have hL3 : ¬ IsPSL 3 2 1 ↥L := fun h3 => by
      have e1 := card_eq_168_of_isPSL32 h3
      rw [card_eq_60_of_alt5 hA5] at e1
      norm_num at e1
    exact false_of_alt5 hS hVt hU hA5 hcard (isotypic_two hA21 hB42 h9 hS hVt hU hAC hAL hL3)

end Final

theorem caseIIaStep_holds (hA21 : AsA21SQTKSection)
    (hB42 : AsB42) (h9 : A38B42) : CaseIIaStep := by
  intro W _ _ M Mp T L V t A r hS _ hc hU hAC _
  have hVt := hc.1
  have hAL := le_normalizer_of_count hA21 hB42 h9 hS hVt hAC
  rcases ffSide_or hA21 hB42 h9 hS hVt hAC hAL with hff | hff
  · exact concl_of_ffSide hA21 hB42 h9 hS hVt hU hAC hAL hff
  · rcases concl_of_ffSide hA21 hB42 h9 hS.swapV (D321Base.swapV_fix hS.toD321Base hVt)
        (D321Base.swapV_caseIIa hS.toD321Base hU) hAC (le_normalizer_Lt hS hAL) hff with h | h
    · left
      have h1 := d321Two_conjAutSub h t⁻¹
      rwa [conjAutSub_inv_conjAutSub] at h1
    · right
      have h1 := d321Three_conjAutSub (hS.hD.hyp.Mp_normal (M.inv_mem hS.t_mem)) h
      rwa [conjAutSub_inv_conjAutSub] at h1


end CFSG.Quasithin.SmithD321

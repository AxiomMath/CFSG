module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCoverParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaE
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s168e3_exists_normal_orbit_cover_prime_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hs3 : s15 D.M V₀ V hV L = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ p ∣ Nat.card (Subgroup.center Q)) :
    ∃ C : Subgroup G,
      C ≤ D.M ∧
      (C.subgroupOf D.M).Normal ∧
      barSub V₀ V hV C =
        (⨆ g : ↥(Mbar D.M V₀ V hV),
          (lBar V₀ V hV L).map
            (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom) ∧
      ¬ p ∣ Nat.card ↥(C ⊓ F11.CTilde D.M V₀ V) := by
  classical
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let E : Subgroup G := F11.CTilde D.M V₀ V
  let B : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ g : ↥A, H.map (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have h151 : Hyp151 D V₀ V L := c.setting.hyp151
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMn : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  obtain ⟨Y, hYcalC, hYM, hYbar, hYp⟩ :=
    s168e3_exists_cover_prime_free (B := H) (p := p) c hcomp hsimple hp hp2
      (by simpa [H] using hcover)
  have hs2 : 2 < s15 D.M V₀ V h151.isElemAbelian L := by
    rw [show s15 D.M V₀ V h151.isElemAbelian L = s15 D.M V₀ V hV L from rfl, hs3]
    norm_num
  obtain ⟨x, hxM, y, hyM, hxn, hyn, hxy⟩ := s16h_exists_conj_pair D h151 hs2
  let Y0 : Subgroup G := Y
  let Y1 : Subgroup G := conjSubgroup Y x
  let Y2 : Subgroup G := conjSubgroup Y y
  let C : Subgroup G := Y0 ⊔ Y1 ⊔ Y2
  let gx : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨x, hms hxM⟩
  let gy : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨y, hms hyM⟩
  let B0 : Subgroup (MulAut (Vtil V₀ V hV)) := H
  let B1 : Subgroup (MulAut (Vtil V₀ V hV)) :=
    H.map (MulAut.conj ((gx)⁻¹)).toMonoidHom
  let B2 : Subgroup (MulAut (Vtil V₀ V hV)) :=
    H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) := conjSet H A
  have hgxA : gx ∈ A := actTil_mem_barSub V₀ V hV hxM (hms hxM)
  have hgyA : gy ∈ A := actTil_mem_barSub V₀ V hV hyM (hms hyM)
  have hY0calC : Y0 ∈ calC D.M := hYcalC
  have hY1calC : Y1 ∈ calC D.M := by
    have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := Y) (m := x)
      (Subgroup.le_normalizer (H := D.M)) hYcalC hxM
    simpa [Y1, conjSubgroup, Open.uniqueFourConj] using h
  have hY2calC : Y2 ∈ calC D.M := by
    have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := Y) (m := y)
      (Subgroup.le_normalizer (H := D.M)) hYcalC hyM
    simpa [Y2, conjSubgroup, Open.uniqueFourConj] using h
  have hY0M : Y0 ≤ D.M := hYM
  have hY1M : Y1 ≤ D.M := A3.subnormal_le hY1calC.1
  have hY2M : Y2 ≤ D.M := A3.subnormal_le hY2calC.1
  have hCM : C ≤ D.M := sup_le (sup_le hY0M hY1M) hY2M
  have hY0bar : barSub V₀ V hV Y0 = B0 := by
    change barSub V₀ V hV Y = H
    exact hYbar
  have hY1bar : barSub V₀ V hV Y1 = B1 := by
    change barSub V₀ V hV (conjSubgroup Y x) = B1
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hms hxM) Y, hYbar]
  have hY2bar : barSub V₀ V hV Y2 = B2 := by
    change barSub V₀ V hV (conjSubgroup Y y) = B2
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hms hyM) Y, hYbar]
  have hB1L : barSub V₀ V hV (conjSubgroup L x) = B1 := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hms hxM) L]
    rfl
  have hB2L : barSub V₀ V hV (conjSubgroup L y) = B2 := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hms hyM) L]
    rfl
  have hB01 : B0 ≠ B1 := by
    intro heq
    apply hxn
    rw [s15_Infra_mem_nBar_iff h125 hV hxM]
    calc barSub V₀ V hV (conjSubgroup L x) = B1 := hB1L
      _ = B0 := heq.symm
      _ = barSub V₀ V hV L := rfl
  have hB02 : B0 ≠ B2 := by
    intro heq
    apply hyn
    rw [s15_Infra_mem_nBar_iff h125 hV hyM]
    calc barSub V₀ V hV (conjSubgroup L y) = B2 := hB2L
      _ = B0 := heq.symm
      _ = barSub V₀ V hV L := rfl
  have hB12 : B1 ≠ B2 := by
    intro heq
    exact hxy (hB1L.trans (heq.trans hB2L.symm))
  have hY01 : Y0 ≠ Y1 := fun h => hB01 (by rw [← hY0bar, ← hY1bar, h])
  have hY02 : Y0 ≠ Y2 := fun h => hB02 (by rw [← hY0bar, ← hY2bar, h])
  have hY12 : Y1 ≠ Y2 := fun h => hB12 (by rw [← hY1bar, ← hY2bar, h])
  have hS_card : S.ncard = 3 := by
    change s15 D.M V₀ V hV L = 3
    exact hs3
  have hconj_one_A : (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom =
      MonoidHom.id (MulAut (Vtil V₀ V hV)) := by
    ext z
    simp
  have hconj_one_G : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext z
    simp
  have hB0S : B0 ∈ S := by
    refine ⟨1, A.one_mem, ?_⟩
    rw [hconj_one_A, Subgroup.map_id]
  have hB1S : B1 ∈ S := ⟨(gx)⁻¹, A.inv_mem hgxA, rfl⟩
  have hB2S : B2 ∈ S := ⟨(gy)⁻¹, A.inv_mem hgyA, rfl⟩
  let T : Set (Subgroup (MulAut (Vtil V₀ V hV))) := {B0, B1, B2}
  have hTsub : T ⊆ S := by
    intro Z hZ
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl | rfl
    · exact hB0S
    · exact hB1S
    · exact hB2S
  have hTcard : T.ncard = 3 :=
    Set.ncard_eq_three.2 ⟨B0, B1, B2, hB01, hB02, hB12, rfl⟩
  have hSeq : T = S := by
    refine Set.eq_of_subset_of_ncard_le hTsub ?_ (Set.toFinite S)
    rw [hS_card, hTcard]
  have hm_conj_mem (m : G) (hm : m ∈ D.M) :
      barSub V₀ V hV (conjSubgroup Y m) ∈ S := by
    have hgm : actTil V₀ V hV ⟨m, hms hm⟩ ∈ A := actTil_mem_barSub V₀ V hV hm (hms hm)
    refine ⟨(actTil V₀ V hV ⟨m, hms hm⟩)⁻¹, A.inv_mem hgm, ?_⟩
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hms hm) Y, hYbar]
  have hHperf : ⁅H, H⁆ = H := CFSG.Quasithin.B15P4.perfect_of_isComponentOf hcomp
  have hHne : H ≠ ⊥ := CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf hcomp
  have hB0na : ⁅B0, B0⁆ ≠ ⊥ := by
    change ⁅H, H⁆ ≠ ⊥
    rw [hHperf]
    exact hHne
  have hB1perf : ⁅B1, B1⁆ = B1 := by
    change ⁅H.map (MulAut.conj ((gx)⁻¹)).toMonoidHom,
      H.map (MulAut.conj ((gx)⁻¹)).toMonoidHom⁆ =
        H.map (MulAut.conj ((gx)⁻¹)).toMonoidHom
    rw [← Subgroup.map_commutator, hHperf]
  have hB1ne : B1 ≠ ⊥ := by
    change H.map (MulAut.conj ((gx)⁻¹)).toMonoidHom ≠ ⊥
    intro hbot
    have hle : H ≤ (MulAut.conj ((gx)⁻¹)).toMonoidHom.ker :=
      (Subgroup.map_eq_bot_iff H).1 hbot
    have hker : (MulAut.conj ((gx)⁻¹)).toMonoidHom.ker = ⊥ :=
      MonoidHom.ker_eq_bot _ (MulAut.conj ((gx)⁻¹)).injective
    rw [hker] at hle
    exact hHne (le_bot_iff.mp hle)
  have hB1na : ⁅B1, B1⁆ ≠ ⊥ := by
    rw [hB1perf]
    exact hB1ne
  have hB2perf : ⁅B2, B2⁆ = B2 := by
    change ⁅H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom,
      H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom⁆ =
        H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom
    rw [← Subgroup.map_commutator, hHperf]
  have hB2ne : B2 ≠ ⊥ := by
    change H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom ≠ ⊥
    intro hbot
    have hle : H ≤ (MulAut.conj ((gy)⁻¹)).toMonoidHom.ker :=
      (Subgroup.map_eq_bot_iff H).1 hbot
    have hker : (MulAut.conj ((gy)⁻¹)).toMonoidHom.ker = ⊥ :=
      MonoidHom.ker_eq_bot _ (MulAut.conj ((gy)⁻¹)).injective
    rw [hker] at hle
    exact hHne (le_bot_iff.mp hle)
  have hB2na : ⁅B2, B2⁆ ≠ ⊥ := by
    rw [hB2perf]
    exact hB2ne
  have hconj_eq (m : G) (hm : m ∈ D.M) :
      conjSubgroup Y m = Y0 ∨ conjSubgroup Y m = Y1 ∨ conjSubgroup Y m = Y2 := by
    have hmcalC : conjSubgroup Y m ∈ calC D.M := by
      have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := Y) (m := m)
        (Subgroup.le_normalizer (H := D.M)) hYcalC hm
      simpa [conjSubgroup, Open.uniqueFourConj] using h
    have hBm : barSub V₀ V hV (conjSubgroup Y m) = B0 ∨
        barSub V₀ V hV (conjSubgroup Y m) = B1 ∨
        barSub V₀ V hV (conjSubgroup Y m) = B2 := by
      have h := hm_conj_mem m hm
      rw [← hSeq] at h
      simpa [T] using h
    rcases hBm with h | h | h
    · left
      exact s16h_e3_omega_calC_eq_of_barSub_eq h125 hmcalC hY0calC
        (h.trans hY0bar.symm) (by simpa [h] using hB0na)
    · right; left
      exact s16h_e3_omega_calC_eq_of_barSub_eq h125 hmcalC hY1calC
        (h.trans hY1bar.symm) (by simpa [h] using hB1na)
    · right; right
      exact s16h_e3_omega_calC_eq_of_barSub_eq h125 hmcalC hY2calC
        (h.trans hY2bar.symm) (by simpa [h] using hB2na)
  have hconj_le (m : G) (hm : m ∈ D.M) : conjSubgroup Y m ≤ C := by
    rcases hconj_eq m hm with h | h | h
    · rw [h]; exact le_trans le_sup_left le_sup_left
    · rw [h]; exact le_trans le_sup_right le_sup_left
    · rw [h]; exact le_sup_right
  have hClosure : C = UC22.conjClosure D.M Y := by
    refine le_antisymm ?_ ?_
    · refine sup_le (sup_le ?_ ?_) ?_
      · refine le_iSup₂ (f := fun K (_ : K ∈ conjSetOf D.M Y) => K) Y ?_
        refine ⟨1, D.M.one_mem, ?_⟩
        rw [hconj_one_G, Subgroup.map_id]
      · refine le_iSup₂ (f := fun K (_ : K ∈ conjSetOf D.M Y) => K)
          (conjSubgroup Y x) ?_
        refine ⟨x⁻¹, D.M.inv_mem hxM, ?_⟩
        simp [conjSubgroup]
      · refine le_iSup₂ (f := fun K (_ : K ∈ conjSetOf D.M Y) => K)
          (conjSubgroup Y y) ?_
        refine ⟨y⁻¹, D.M.inv_mem hyM, ?_⟩
        simp [conjSubgroup]
    · refine iSup₂_le fun K hK => ?_
      obtain ⟨g, hg, rfl⟩ := hK
      have h := hconj_le g⁻¹ (D.M.inv_mem hg)
      simpa [conjSubgroup] using h
  have hCnorm : (C.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCM, hClosure]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M Y
  let f : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hms
  let N : Subgroup ↥D.M := f.ker
  let P0 : Subgroup ↥D.M := Y0.subgroupOf D.M
  let P1 : Subgroup ↥D.M := Y1.subgroupOf D.M
  let P2 : Subgroup ↥D.M := Y2.subgroupOf D.M
  have hkerf : f.ker = E.subgroupOf D.M := by
    change (barHom V₀ V hV hms).ker = E.subgroupOf D.M
    rw [ker_barHom V₀ V hV hMn hms]
  have hEM : E ≤ D.M := fun g hg => (mem_cTilde_iff hV hMn).1 hg |>.1
  have hEnorm : D.M ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEM).1
      (s15_Three_cTilde_normal hV hms)
  have hconjE (m : G) (hm : m ∈ D.M) : E.map (MulAut.conj (m⁻¹)).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hEnorm (D.M.inv_mem hm))
  have hkernel_conj (m : G) (hm : m ∈ D.M) :
      ¬ p ∣ Nat.card ↥(conjSubgroup Y m ⊓ E) := by
    have hEq : conjSubgroup Y m ⊓ E =
        (Y ⊓ E).map (MulAut.conj (m⁻¹)).toMonoidHom := by
      rw [conjSubgroup]
      calc Y.map (MulAut.conj (m⁻¹)).toMonoidHom ⊓ E
          = Y.map (MulAut.conj (m⁻¹)).toMonoidHom ⊓
              E.map (MulAut.conj (m⁻¹)).toMonoidHom := by rw [hconjE m hm]
        _ = (Y ⊓ E).map (MulAut.conj (m⁻¹)).toMonoidHom :=
          (Subgroup.map_inf Y E (MulAut.conj (m⁻¹)).toMonoidHom
            (MulAut.conj (m⁻¹)).injective).symm
    rw [hEq, Subgroup.card_map_of_injective (MulAut.conj (m⁻¹)).injective]
    exact hYp
  have hincl (Z : Subgroup G) (hZM : Z ≤ D.M) :
      (Z.subgroupOf D.M).map (Subgroup.inclusion hms) = Z.subgroupOf (stabTil V₀ V) := by
    rw [← Subgroup.comap_inclusion_subgroupOf hms Z]
    refine Subgroup.map_comap_eq_self ?_
    rw [Subgroup.inclusion_range]
    exact Subgroup.subgroupOf_mono (stabTil V₀ V) hZM
  have hP0map : P0.map f = B0 := by
    change (Y0.subgroupOf D.M).map (barHom V₀ V hV hms) = B0
    rw [barHom, ← Subgroup.map_map, hincl Y0 hY0M]
    exact hY0bar
  have hP1map : P1.map f = B1 := by
    change (Y1.subgroupOf D.M).map (barHom V₀ V hV hms) = B1
    rw [barHom, ← Subgroup.map_map, hincl Y1 hY1M]
    exact hY1bar
  have hP2map : P2.map f = B2 := by
    change (Y2.subgroupOf D.M).map (barHom V₀ V hV hms) = B2
    rw [barHom, ← Subgroup.map_map, hincl Y2 hY2M]
    exact hY2bar
  have hPsup : P0 ⊔ P1 ⊔ P2 = C.subgroupOf D.M := by
    change (Y0.subgroupOf D.M) ⊔ (Y1.subgroupOf D.M) ⊔ (Y2.subgroupOf D.M) =
      (Y0 ⊔ Y1 ⊔ Y2).subgroupOf D.M
    rw [Subgroup.subgroupOf_sup (sup_le hY0M hY1M) hY2M,
      Subgroup.subgroupOf_sup hY0M hY1M]
  have hsub (Z : Subgroup G) (hZM : Z ≤ D.M) :
      (Z ⊓ E).subgroupOf D.M = Z.subgroupOf D.M ⊓ f.ker := by
    change (Z ⊓ E).comap D.M.subtype = (Z.subgroupOf D.M) ⊓ f.ker
    rw [Subgroup.comap_inf]
    change Z.comap D.M.subtype ⊓ E.comap D.M.subtype = Z.comap D.M.subtype ⊓ f.ker
    rw [show f.ker = E.comap D.M.subtype from hkerf]
  have hP0sub : (Y0 ⊓ E).subgroupOf D.M = P0 ⊓ N := by
    simpa [P0, N] using hsub Y0 hY0M
  have hP1sub : (Y1 ⊓ E).subgroupOf D.M = P1 ⊓ N := by
    simpa [P1, N] using hsub Y1 hY1M
  have hP2sub : (Y2 ⊓ E).subgroupOf D.M = P2 ⊓ N := by
    simpa [P2, N] using hsub Y2 hY2M
  have hP0p : ¬ p ∣ Nat.card ↥(P0 ⊓ N) := by
    rw [← hP0sub]
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hY0M)).toEquiv]
  have hP1p : ¬ p ∣ Nat.card ↥(P1 ⊓ N) := by
    rw [← hP1sub]
    have hk := hkernel_conj x hxM
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hY1M)).toEquiv]
  have hP2p : ¬ p ∣ Nat.card ↥(P2 ⊓ N) := by
    rw [← hP2sub]
    have hk := hkernel_conj y hyM
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hY2M)).toEquiv]
  have hPnorm_of (Z W : Subgroup G) (hZcalC : Z ∈ calC D.M) (hWcalC : W ∈ calC D.M)
      (hne : Z ≠ W) (hZM : Z ≤ D.M) :
      W.subgroupOf D.M ≤ Subgroup.normalizer ((Z.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    have hle : W ≤ Subgroup.normalizer (Z : Set G) := calC_le_normalizer_of_ne hZcalC hWcalC hne
    have hmono : W.subgroupOf D.M ≤ (Subgroup.normalizer (Z : Set G)).subgroupOf D.M :=
      Subgroup.subgroupOf_mono D.M hle
    rwa [Subgroup.subgroupOf_normalizer_eq hZM] at hmono
  have hPnorm01 : P1 ≤ Subgroup.normalizer (P0 : Set ↥D.M) :=
    hPnorm_of Y0 Y1 hY0calC hY1calC hY01 hY0M
  have hPnorm20 : P2 ≤ Subgroup.normalizer (P0 : Set ↥D.M) :=
    hPnorm_of Y0 Y2 hY0calC hY2calC hY02 hY0M
  have hPnorm21 : P2 ≤ Subgroup.normalizer (P1 : Set ↥D.M) :=
    hPnorm_of Y1 Y2 hY1calC hY2calC hY12 hY1M
  have hnorm01k : P1 ⊓ N ≤
      Subgroup.normalizer ((P0 ⊓ N : Subgroup ↥D.M) : Set ↥D.M) := by
    have h2 : N ≤ Subgroup.normalizer (N : Set ↥D.M) := Subgroup.le_normalizer
    exact (le_inf (inf_le_left.trans hPnorm01) (inf_le_right.trans h2)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := P0) (K := N))
  have hnorm2 : P2 ⊓ N ≤
      Subgroup.normalizer (((P0 ⊓ N) ⊔ (P1 ⊓ N) : Subgroup ↥D.M) : Set ↥D.M) := by
    have h2 : N ≤ Subgroup.normalizer (N : Set ↥D.M) := Subgroup.le_normalizer
    have hk20 : P2 ⊓ N ≤ Subgroup.normalizer ((P0 ⊓ N : Subgroup ↥D.M) : Set ↥D.M) :=
      (le_inf (inf_le_left.trans hPnorm20) (inf_le_right.trans h2)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := P0) (K := N))
    have hk21 : P2 ⊓ N ≤ Subgroup.normalizer ((P1 ⊓ N : Subgroup ↥D.M) : Set ↥D.M) :=
      (le_inf (inf_le_left.trans hPnorm21) (inf_le_right.trans h2)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := P1) (K := N))
    exact (le_inf hk20 hk21).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (P0 ⊓ N) (P1 ⊓ N))
  have hcenterH : Subgroup.center ↥H = ⊥ := by
    have hHsimple : IsSimpleGroup ↥H := hsimple
    have hHperfect : Group.IsPerfect ↥H := ⟨hcomp.2.2.1⟩
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative (G := ↥H))
  have hcenterB2 : Subgroup.center ↥B2 = ⊥ := by
    change Subgroup.center ↥(H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom) = ⊥
    let e2 : ↥H ≃* ↥(H.map (MulAut.conj ((gy)⁻¹)).toMonoidHom) :=
      Subgroup.equivMapOfInjective H (MulAut.conj ((gy)⁻¹)).toMonoidHom
        (MulAut.conj ((gy)⁻¹)).injective
    rw [← Subgroup.map_center_eq e2, hcenterH, Subgroup.map_bot]
  have hcomm_of (Z W : Subgroup G) (hZcalC : Z ∈ calC D.M) (hWcalC : W ∈ calC D.M)
      (hne : Z ≠ W) : ⁅barSub V₀ V hV Z, barSub V₀ V hV W⁆ = ⊥ := by
    have hZcomm : ⁅Z, W⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
      (calC_commutator_le_of_ne hZcalC hWcalC hne).trans
        (inf_le_left.trans (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hZcalC.1))
    have hbar : ⁅barSub V₀ V hV Z, barSub V₀ V hV W⁆ ≤
        barSub V₀ V hV (CFSG.Open.pCoreOf 2 D.M) :=
      (s16h_e3_omega_commutator_barSub_le V₀ V hV Z W).trans
        (barSub_mono V₀ V hV hZcomm)
    rw [barSub_pCoreOf_eq_bot_of_hyp125 h125] at hbar
    exact le_bot_iff.mp hbar
  have hcomm10 : ⁅B1, B0⁆ = ⊥ := by
    rw [← hY1bar, ← hY0bar]
    exact hcomm_of Y1 Y0 hY1calC hY0calC hY01.symm
  have hcomm02 : ⁅B0, B2⁆ = ⊥ := by
    rw [← hY0bar, ← hY2bar]
    exact hcomm_of Y0 Y2 hY0calC hY2calC hY02
  have hcomm12 : ⁅B1, B2⁆ = ⊥ := by
    rw [← hY1bar, ← hY2bar]
    exact hcomm_of Y1 Y2 hY1calC hY2calC hY12
  have hB01bot : B0 ⊓ B1 = ⊥ := by
    have hcent : B1 ≤ Subgroup.centralizer (B0 : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm10
    have hle : B0 ⊓ B1 ≤ B0 ⊓
        Subgroup.centralizer (B0 : Set (MulAut (Vtil V₀ V hV))) :=
      inf_le_inf_left B0 hcent
    rw [s16h_inf_centralizer_eq_bot_of_center_eq_bot hcenterH] at hle
    exact le_bot_iff.mp hle
  have hBsup2 : (B0 ⊔ B1) ⊓ B2 = ⊥ := by
    have hcent0 : B0 ≤ Subgroup.centralizer (B2 : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm02
    have hcent1 : B1 ≤ Subgroup.centralizer (B2 : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm12
    have hcent : B0 ⊔ B1 ≤ Subgroup.centralizer (B2 : Set (MulAut (Vtil V₀ V hV))) :=
      sup_le hcent0 hcent1
    have hle : (B0 ⊔ B1) ⊓ B2 ≤ ⊥ := by
      calc (B0 ⊔ B1) ⊓ B2 ≤
            Subgroup.centralizer (B2 : Set (MulAut (Vtil V₀ V hV))) ⊓ B2 :=
          inf_le_inf_right B2 hcent
        _ = B2 ⊓ Subgroup.centralizer (B2 : Set (MulAut (Vtil V₀ V hV))) :=
          inf_comm _ _
        _ = ⊥ := s16h_inf_centralizer_eq_bot_of_center_eq_bot hcenterB2
    exact le_bot_iff.mp hle
  have himg01 : P0.map f ⊓ P1.map f = ⊥ := by
    rw [hP0map, hP1map, hB01bot]
  have himg2 : (P0 ⊔ P1).map f ⊓ P2.map f = ⊥ := by
    rw [Subgroup.map_sup, hP0map, hP1map, hP2map, hBsup2]
  have hjoin1 : (P0 ⊔ P1) ⊓ N = (P0 ⊓ N) ⊔ (P1 ⊓ N) := by
    have h := CFSG.GroupTheory.ker_sup_eq_of_normalizer f P0 P1 hPnorm01 himg01
    simpa [N] using h
  have hPnorm2sup : P2 ≤
      Subgroup.normalizer ((P0 ⊔ P1 : Subgroup ↥D.M) : Set ↥D.M) :=
    (le_inf hPnorm20 hPnorm21).trans
      (Subgroup.inf_normalizer_le_normalizer_sup P0 P1)
  have hjoin2 : (P0 ⊔ P1 ⊔ P2) ⊓ N = ((P0 ⊓ N) ⊔ (P1 ⊓ N)) ⊔ (P2 ⊓ N) := by
    have h := CFSG.GroupTheory.ker_sup_eq_of_normalizer f (P0 ⊔ P1) P2 hPnorm2sup himg2
    have h1 : (P0 ⊔ P1) ⊓ N = (P0 ⊓ N) ⊔ (P1 ⊓ N) := hjoin1
    simpa [N, h1] using h
  have hsup01 : ¬ p ∣ Nat.card ↥((P0 ⊓ N) ⊔ (P1 ⊓ N)) :=
    CFSG.LocalAnalysis.GLTheoremA.not_dvd_card_sup_of_le_normalizer hp hnorm01k hP0p hP1p
  have hsupfree : ¬ p ∣ Nat.card ↥(((P0 ⊓ N) ⊔ (P1 ⊓ N)) ⊔ (P2 ⊓ N)) :=
    CFSG.LocalAnalysis.GLTheoremA.not_dvd_card_sup_of_le_normalizer hp hnorm2 hsup01 hP2p
  have hCsub : (C ⊓ E).subgroupOf D.M = (C.subgroupOf D.M) ⊓ N := by
    simpa [N] using hsub C hCM
  have hjoinC : (C.subgroupOf D.M) ⊓ N = ((P0 ⊓ N) ⊔ (P1 ⊓ N)) ⊔ (P2 ⊓ N) := by
    rw [← hPsup, hjoin2]
  have hCcard : Nat.card ↥(C ⊓ E) = Nat.card ↥((C.subgroupOf D.M) ⊓ N) := by
    rw [← hCsub]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hCM)).toEquiv).symm
  have hY0stab : Y0 ≤ stabTil V₀ V := fun z hz => hms (hY0M hz)
  have hY1stab : Y1 ≤ stabTil V₀ V := fun z hz => hms (hY1M hz)
  have hY2stab : Y2 ≤ stabTil V₀ V := fun z hz => hms (hY2M hz)
  have hbarC_triple : barSub V₀ V hV C = B0 ⊔ B1 ⊔ B2 := by
    change barSub V₀ V hV (Y0 ⊔ Y1 ⊔ Y2) = B0 ⊔ B1 ⊔ B2
    rw [s16c7_barSub_sup V₀ V hV (sup_le hY0stab hY1stab) hY2stab,
      s16c7_barSub_sup V₀ V hV hY0stab hY1stab]
    rw [hY0bar, hY1bar, hY2bar]
  have htriple_eq_set : B0 ⊔ B1 ⊔ B2 = ⨆ Z ∈ S, Z := by
    rw [← hSeq]
    rw [show T = insert B0 (insert B1 {B2}) from rfl,
      iSup_insert, iSup_insert, iSup_singleton]
    ac_rfl
  have hB_eq_set : B = ⨆ Z ∈ S, Z := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun g => ?_
      exact le_iSup₂ (f := fun Z (_ : Z ∈ S) => Z)
        (H.map (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
        ⟨(g : MulAut (Vtil V₀ V hV)), g.2, rfl⟩
    · refine iSup₂_le fun Z hZ => ?_
      obtain ⟨n, hn, rfl⟩ := hZ
      exact le_iSup (fun g : ↥A => H.map (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
        ⟨n, hn⟩
  have hbarC : barSub V₀ V hV C = B :=
    (hbarC_triple.trans htriple_eq_set).trans hB_eq_set.symm
  refine ⟨C, hCM, hCnorm, ?_, ?_⟩
  · change barSub V₀ V hV C = B
    exact hbarC
  · rw [hCcard, hjoinC]
    exact hsupfree

theorem s168e3_exists_normal_orbit_cover_three_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q)) :
    ∃ C : Subgroup G,
      C ≤ D.M ∧
      (C.subgroupOf D.M).Normal ∧
      barSub V₀ V hV C =
        (⨆ g : ↥(Mbar D.M V₀ V hV),
          (lBar V₀ V hV L).map
            (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom) ∧
      ¬ 3 ∣ Nat.card ↥(C ⊓ F11.CTilde D.M V₀ V) :=
  s168e3_exists_normal_orbit_cover_prime_free (p := 3) c hcomp hsimple hs3
    Nat.prime_three (by norm_num) hcover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

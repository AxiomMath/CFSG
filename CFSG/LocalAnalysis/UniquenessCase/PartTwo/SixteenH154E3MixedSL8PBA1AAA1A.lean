module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionKernelCardinality
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResSum
public import CFSG.Quasithin.Background.SmithD310UCaseI
public import CFSG.Sporadic.HN.PGroupAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_autSub_setup {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
      (FFModel.nat (StatedSL 2 K)).Realizes (autSub L (commSub ⊤ L)) ⊤
        (fixV (autSub L (commSub ⊤ L))) ∧
      commSub ⊤ (autSub L (commSub ⊤ L)) = ⊤ := by
  classical
  obtain ⟨-, hNat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hNat
  refine ⟨K, hKf, hKfin, ?_, ?_, ?_⟩
  · rw [hKcard]; norm_num
  · have hLU : L ≤ stabSub (commSub ⊤ L) := by
      rw [← CFSG.Quasithin.commV_eq_commSub L]
      exact CFSG.Quasithin.le_stabSub_commV_self L
    have hfix : (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) =
        fixV (autSub L (commSub ⊤ L)) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [mem_fixV_autSub]
        intro g hg _
        exact mem_fixV.mp hx.2 g hg
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact ⟨x.2, mem_fixV.mpr fun g hg => mem_fixV_autSub.mp hx g hg (hLU hg)⟩
    have h0 := s16h_realizes_autSub (V := W) (D := FFModel.nat (StatedSL 2 K))
      (H := L) (U := commSub ⊤ L) (I := commSub ⊤ L)
      (Z := commSub ⊤ L ⊓ fixV L) hLU le_rfl inf_le_left hreal
    rw [Subgroup.subgroupOf_self] at h0
    rwa [hfix] at h0
  · have hLU : L ≤ stabSub (commSub ⊤ L) := by
      rw [← CFSG.Quasithin.commV_eq_commSub L]
      exact CFSG.Quasithin.le_stabSub_commV_self L
    have hLU' : ∀ l ∈ L, ∀ w ∈ commSub ⊤ L, l w ∈ commSub ⊤ L :=
      fun l hl w hw => ((mem_stabSub.mp (hLU hl)) w).2 hw
    have hperf : ⁅L, L⁆ = L :=
      Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hc.comp.2.2.1)
    have hcommU : commSub (commSub ⊤ L) L = commSub ⊤ L :=
      CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperf ⊤
    have htop : (⊤ : Subgroup ↥(commSub ⊤ L)).map (commSub ⊤ L).subtype = commSub ⊤ L := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hgen : ∀ l (hl : l ∈ L), ∀ w : ↥(commSub ⊤ L),
        (⟨l (w : W) * (w : W)⁻¹,
          (commSub ⊤ L).mul_mem (hLU' l hl w w.2) ((commSub ⊤ L).inv_mem w.2)⟩ : ↥(commSub ⊤ L)) ∈
          commSub ⊤ (autSub L (commSub ⊤ L)) := by
      intro l hl w
      exact Subgroup.subset_closure ⟨resHom (commSub ⊤ L) ⟨l, hLU hl⟩,
        mem_autSub.mpr ⟨⟨l, hLU hl⟩, hl, rfl⟩, w, Subgroup.mem_top w, by
          apply Subtype.ext
          rfl⟩
    have hle' : commSub (commSub ⊤ L) L ≤
        (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype := by
      show Subgroup.closure {c | ∃ x ∈ L, ∃ w ∈ commSub ⊤ L, x w * w⁻¹ = c} ≤ _
      rw [Subgroup.closure_le]
      rintro c ⟨l, hl, w, hw, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨l w * w⁻¹,
        (commSub ⊤ L).mul_mem (hLU' l hl w hw) ((commSub ⊤ L).inv_mem hw)⟩,
        hgen l hl ⟨w, hw⟩, rfl⟩
    have hmap : (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype =
        commSub ⊤ L := by
      refine le_antisymm ?_ ?_
      · calc (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype
            ≤ (⊤ : Subgroup ↥(commSub ⊤ L)).map (commSub ⊤ L).subtype := Subgroup.map_mono le_top
          _ = commSub ⊤ L := htop
      · exact (le_of_eq hcommU.symm).trans hle'
    refine Subgroup.map_injective (commSub ⊤ L).subtype_injective ?_
    rw [hmap, htop]

theorem s16h_H5_row_SL2_eight_central_eq_bot {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) = ⊥ := by
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZdef
  set H : Subgroup (MulAut ↥U) := autSub L U with hH
  obtain ⟨K, hKf, hKfin, hKcard, hrealH, hcommH⟩ :=
    s16h_H5_row_SL2_eight_autSub_setup (W := W) hc h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hLstab : L ≤ stabSub U := by
    rw [hU, ← CFSG.Quasithin.commV_eq_commSub L]
    exact CFSG.Quasithin.le_stabSub_commV_self L
  have hfixH : Z.subgroupOf U = fixV H := by
    rw [hH]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [mem_fixV_autSub]
      intro g hg _
      exact mem_fixV.mp hx.2 g hg
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, mem_fixV.mpr fun g hg => mem_fixV_autSub.mp hx g hg (hLstab hg)⟩
  by_contra hCne
  have hCne' : (⊤ : Subgroup (MulAut ↥U)) ⊓ Subgroup.centralizer (H : Set (MulAut ↥U)) ≠ ⊥ := by
    rwa [top_inf_eq]
  have hW2U : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hc.elem (u : W))
  obtain ⟨hCcard, hCmodFix⟩ := card_centralizer_eq_and_modFix_eq_bot_of_extension
    (W := ↥U) (A := ⊤) (H := H) (K := K) (M := Fin 2 → K)
    (D := FFModel.nat (StatedSL 2 K))
    (LM := CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 2 K))
    hW2U hrealH hcommH (p := 7) (by norm_num) (by rw [hKcard]) (by norm_num)
    hCne' (fun T hT => CFSG.Quasithin.Vol2.KGNat.commutant_statedSL (n := 2) (by norm_num) T hT)
  have hpres : ∀ d : MulAut ↥U, d ∈ Subgroup.centralizer (H : Set (MulAut ↥U)) →
      ∀ z ∈ fixV H, d z ∈ fixV H := by
    intro d hd z hz
    rw [mem_fixV] at hz ⊢
    intro h hh
    have hcomm : h * d = d * h := Subgroup.mem_centralizer_iff.mp hd h hh
    calc h (d z) = (h * d) z := rfl
      _ = (d * h) z := by rw [hcomm]
      _ = d (h z) := rfl
      _ = d z := by rw [hz h hh]
  have hcardfix : Nat.card ↥(fixV H) ≤ 4 := by
    rw [← hfixH]
    rw [show Nat.card ↥(Z.subgroupOf U) = Nat.card ↥Z from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ≤ U)).toEquiv]
    rw [card_eq_two_pow hc.elem Z]
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hrk
  have hPfix : IsPGroup 2 ↥(fixV H) :=
    isPGroup_two_of_sq_eq_one fun v => by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc.elem (((v : ↥U) : W))
  have hcarddvd : Nat.card ↥(fixV H) ∣ 2 ^ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hPfix
    rw [hn]
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
      (by rw [← hn]; simpa using hcardfix))
  have hGL : ∀ r ≤ 2, ¬ 7 ∣ Nat.card (GL (Fin r) (ZMod 2)) := by
    intro r hr
    rw [Matrix.card_GL_field (n := r)]
    interval_cases r <;> norm_num [Fin.prod_univ_succ, ZMod.card]
  have hfixHle : fixV H ≤
      modFix ((⊤ : Subgroup (MulAut ↥U)) ⊓ Subgroup.centralizer (H : Set (MulAut ↥U))) ⊤ := by
    intro z hz
    refine ⟨Subgroup.mem_top z, ?_⟩
    intro c
    have hcH : (c : MulAut ↥U) ∈ Subgroup.centralizer (H : Set (MulAut ↥U)) :=
      (Subgroup.mem_inf.mp c.2).2
    have hcstab : (c : MulAut ↥U) ∈ stabSub (fixV H) := by
      rw [mem_stabSub]
      intro w
      exact ⟨fun hw => by
        have h1 : (c : MulAut ↥U)⁻¹ ∈ Subgroup.centralizer (H : Set (MulAut ↥U)) :=
          (Subgroup.centralizer (H : Set (MulAut ↥U))).inv_mem hcH
        simpa using hpres _ h1 ((c : MulAut ↥U) w) hw, fun hw => hpres _ hcH w hw⟩
    have hc7 : (c : MulAut ↥U) ^ 7 = 1 := by
      have h1 : (c : ↥((⊤ : Subgroup (MulAut ↥U)) ⊓
          Subgroup.centralizer (H : Set (MulAut ↥U)))) ^ 7 = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp (hCcard ▸ orderOf_dvd_natCard c)
      simpa using congrArg Subtype.val h1
    have hψ7 : (resHom (fixV H) ⟨(c : MulAut ↥U), hcstab⟩) ^ 7 = 1 := by
      rw [← map_pow]
      have h1 : (⟨(c : MulAut ↥U), hcstab⟩ : stabSub (fixV H)) ^ 7 = 1 := by
        apply Subtype.ext
        simpa using hc7
      rw [h1, map_one]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hψ1 : resHom (fixV H) ⟨(c : MulAut ↥U), hcstab⟩ = 1 :=
      CFSG.Sporadic.HN.eq_one_of_pow_eq_one (p := 2) (q := 7) (e := 2) (by norm_num)
        (by norm_num) hPfix hcarddvd hGL hψ7
    have h2 := congrArg (fun f : MulAut ↥(fixV H) => f ⟨z, hz⟩) hψ1
    have h3 : ((resHom (fixV H) ⟨(c : MulAut ↥U), hcstab⟩) ⟨z, hz⟩ : ↥U) =
        (c : MulAut ↥U) z := resHom_apply (fixV H) ⟨_, _⟩ ⟨z, hz⟩
    have hcz : (c : MulAut ↥U) z = z := by
      have h4 := congrArg Subtype.val h2
      rw [h3] at h4
      simpa using h4
    simpa [Subgroup.smul_def, MulAut.smul_def] using hcz
  have hfixbot : fixV H = ⊥ := by
    have hle : fixV H ≤ modFix ((⊤ : Subgroup (MulAut ↥U)) ⊓
        Subgroup.centralizer (H : Set (MulAut ↥U))) ⊤ := hfixHle
    rw [hCmodFix] at hle
    exact le_bot_iff.mp hle
  have hZbot : Z = ⊥ := by
    have h1 : Z.subgroupOf U = ⊥ := by rw [hfixH, hfixbot]
    have h2 := Subgroup.map_subgroupOf_eq_of_le (H := Z) (K := U) (inf_le_left : Z ≤ U)
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  exact hZ hZbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

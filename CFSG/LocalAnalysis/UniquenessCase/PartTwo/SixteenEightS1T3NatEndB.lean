module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.CGT.PushingUpLit.BHS5.QuotAct
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix
open CFSG.RankThree.GF2n.Stroth80

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

private noncomputable def s16t3_quotHom (H : Subgroup (MulAut W)) (Z : Subgroup W)
    (hH : H ≤ stabSub Z) : ↥H →* MulAut (W ⧸ Z) :=
  (CFSG.CGT.PushingUpLit.BHS5.quotAct Z).comp (Subgroup.inclusion hH)
private theorem s16t3_realizes_quotient {D : FFModel} {H : Subgroup (MulAut W)}
    (hH : H ≤ stabSub Z) (h : D.Realizes H U Z) :
    D.Realizes (s16t3_quotHom H Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ := by
  obtain ⟨π, hπ⟩ := h
  have hequiv : ∀ (h : ↥H) (w : W),
      QuotientGroup.mk' Z ((h : MulAut W) w) =
        (((s16t3_quotHom H Z hH).rangeRestrict h : ↥(s16t3_quotHom H Z hH).range) :
            MulAut (W ⧸ Z)) (QuotientGroup.mk' Z w) := by
    intro h w
    show (QuotientGroup.mk ((h : MulAut W) w) : W ⧸ Z) =
      CFSG.CGT.PushingUpLit.BHS5.quotAct Z (Subgroup.inclusion hH h) (QuotientGroup.mk w)
    rw [CFSG.CGT.PushingUpLit.BHS5.quotAct_mk]
    rfl
  have hres := s16k_realizes_map ⟨π, hπ⟩ (QuotientGroup.mk' Z) (QuotientGroup.ker_mk' Z).le
    (s16t3_quotHom H Z hH).rangeRestrict (s16t3_quotHom H Z hH).rangeRestrict_surjective hequiv
  have hbot : (Z.map (QuotientGroup.mk' Z)) = ⊥ :=
    (Subgroup.map_eq_bot_iff Z (f := QuotientGroup.mk' Z)).mpr (QuotientGroup.ker_mk' Z).ge
  rw [hbot] at hres
  exact hres

private theorem s16t3_stable_of_realizes {D : FFModel} {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} (h : D.Realizes H U Z) : StableUnder H U := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hπs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  exact fun x hx u hu => hHU ⟨x, hx⟩ u hu

private theorem s16t3_stableZ_of_realizes {D : FFModel} {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} (h : D.Realizes H U Z) : StableUnder H Z := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hπs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  exact fun x hx z hz => hHZ ⟨x, hx⟩ z hz

private theorem s16t3_quotient_binaryNaturalSL {n a : ℕ} (hH : L ≤ stabSub Z)
    (h : BinaryNaturalSL L U Z n a) :
    BinaryNaturalSL (s16t3_quotHom L Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ n a := by
  obtain ⟨K, hK, hKf, hK2, hR⟩ := h
  exact ⟨K, hK, hKf, hK2, s16t3_realizes_quotient hH hR⟩

private theorem s16t3_quotient_natSpn {n a : ℕ} (hH : L ≤ stabSub Z)
    (h : NatSpn L U Z n a) :
    NatSpn (s16t3_quotHom L Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_realizes_quotient hH hR⟩

private theorem s16t3_quotient_natOmegaPlus {n a : ℕ} (hH : L ≤ stabSub Z)
    (h : NatOmegaPlus L U Z n a) :
    NatOmegaPlus (s16t3_quotHom L Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_realizes_quotient hH hR⟩

private theorem s16t3_quotient_natOmegaMinus {n a : ℕ} (hH : L ≤ stabSub Z)
    (h : NatOmegaMinus L U Z n a) :
    NatOmegaMinus (s16t3_quotHom L Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ n a := by
  obtain ⟨he, K, hK, hKf, b, c, hK2, hirr, hR⟩ := h
  exact ⟨he, K, hK, hKf, b, c, hK2, hirr, s16t3_realizes_quotient hH hR⟩

private theorem s16t3_quotient_alternatingNatural {n : ℕ} (hH : L ≤ stabSub Z)
    (h : AlternatingNatural L U Z n) :
    AlternatingNatural (s16t3_quotHom L Z hH).range (U.map (QuotientGroup.mk' Z)) ⊥ n :=
  s16t3_realizes_quotient hH h

private theorem s16t3_abs_two_cases {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · refine Or.inr ?_
    have hu : Nat.card Fˣ = 1 := by
      have h := Nat.card_units (α := F)
      omega
    haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)

private theorem s16t3_abs_comm_id {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (hF : Nat.card F = 2) (i0 : ι) {X : Subgroup (GL ι F)} (hX : AddCommutantScalar X)
    (g : (ι → F) ≃+ (ι → F))
    (hg : ∀ γ ∈ X, ∀ v : ι → F,
      g ((γ : Matrix ι ι F) *ᵥ v) = (γ : Matrix ι ι F) *ᵥ g v) (v : ι → F) : g v = v := by
  obtain ⟨c, hc⟩ := hX g.toAddMonoidHom hg
  rcases s16t3_abs_two_cases hF c with rfl | rfl
  · exfalso
    have h0 : g (Pi.single i0 1) = g 0 := by
      rw [map_zero]
      exact (hc _).trans (zero_smul _ _)
    have h1 := congrFun (g.injective h0) i0
    simp at h1
  · exact (hc v).trans (one_smul _ _)

private theorem s16t3_endUnits_omegaMinus {H : Subgroup (MulAut W)} {I : Subgroup W} {n : ℕ}
    (hn : 4 ≤ n) (h : NatOmegaMinus H I ⊥ n 1) : Z391.EndUnitsTrivial H I := by
  obtain ⟨-, F, hF, hFf, b, c, hF2, hirr, hreal⟩ := h
  letI := hF
  haveI : Finite F := hFf
  have hF2' : Nat.card F = 2 := by simpa using hF2
  exact s15k_abs_endUnits_of_comm
    (fun g hg v => s16t3_abs_comm_id hF2' (Sum.inr (Sum.inr 0))
      (addCommutantScalar_statedOmegaMinus (m := n / 2) (by omega) hirr) g hg v) hreal

private theorem s16t3_concl (hL : L ≤ stabSub Z) (hU : StableUnder L U)
    (hE : Z391.EndUnitsTrivial (s16t3_quotHom L Z hL).range
      (U.map (QuotientGroup.mk' Z)))
    (φ : ↥U ≃* ↥U)
    (hZ : ∀ u : ↥U, ((φ u : ↥U) : W) ∈ Z ↔ (u : W) ∈ Z)
    (hφ : ∀ l ∈ L, ∀ u : ↥U, ∀ hu : l (u : W) ∈ U,
      ((φ ⟨l (u : W), hu⟩ : ↥U) : W) * (l ((φ u : ↥U) : W))⁻¹ ∈ Z) :
    ∀ u : ↥U, ((φ u : ↥U) : W) * (u : W)⁻¹ ∈ Z := by
  let q : W →* W ⧸ Z := QuotientGroup.mk' Z
  let f : ↥U →* W ⧸ Z := q.comp U.subtype
  have hkerf : f.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' Z (u : W) : W ⧸ Z) = 1 ↔ (u : W) ∈ Z
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hfrange : f.range = U.map q := by
    change (q.comp U.subtype).range = U.map q
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hφZ : (Z.subgroupOf U).map (φ : MulAut ↥U) = Z.subgroupOf U := by
    ext u
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzu⟩
      have hz' : ((z : ↥U) : W) ∈ Z := (Subgroup.mem_subgroupOf).1 hz
      have h2 : ((φ z : ↥U) : W) ∈ Z := (hZ z).2 hz'
      have h3 : ((u : ↥U) : W) ∈ Z := by rw [← hzu]; exact h2
      exact (Subgroup.mem_subgroupOf).2 h3
    · intro hu
      refine ⟨φ.symm u, (Subgroup.mem_subgroupOf).2 ?_, φ.apply_symm_apply u⟩
      exact (hZ (φ.symm u)).1
        (by simpa [φ.apply_symm_apply u] using (Subgroup.mem_subgroupOf).1 hu)
  let φbar : MulAut (↥U ⧸ Z.subgroupOf U) :=
    QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) φ hφZ
  let e : (↥U ⧸ Z.subgroupOf U) ≃* ↥(U.map q) :=
    (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange))
  have he_apply : ∀ u : ↥U, e (QuotientGroup.mk u) =
      (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)) := by
    intro u
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      MulEquiv.subgroupCongr_apply, QuotientGroup.quotientKerEquivRange,
      QuotientGroup.rangeKerLift, QuotientGroup.lift_mk, MonoidHom.rangeRestrict]
    rfl
  let φ' : MulAut (↥(U.map q)) := e.symm.trans (φbar.trans e)
  have hφbar_mk : ∀ u : ↥U, φbar (QuotientGroup.mk u) = QuotientGroup.mk (φ u) :=
    fun u => QuotientGroup.congr_mk (Z.subgroupOf U) (Z.subgroupOf U) φ hφZ u
  have hφ'_apply : ∀ u : ↥U,
      φ' (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)) =
        (⟨q (φ u : ↥U), Subgroup.mem_map_of_mem q (φ u : ↥U).2⟩ : ↥(U.map q)) := by
    intro u
    have hsymm : e.symm (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)) =
        QuotientGroup.mk u := by
      rw [← he_apply u, MulEquiv.symm_apply_apply]
    change e (φbar (e.symm (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)))) =
      (⟨q (φ u : ↥U), Subgroup.mem_map_of_mem q (φ u : ↥U).2⟩ : ↥(U.map q))
    rw [hsymm, hφbar_mk, he_apply]
  have heq : ∀ (l : ↥(s16t3_quotHom L Z hL).range) (x y : ↥(U.map q)),
      l • (x : W ⧸ Z) = (y : W ⧸ Z) →
      l • ((φ' x : ↥(U.map q)) : W ⧸ Z) = ((φ' y : ↥(U.map q)) : W ⧸ Z) := by
    intro l x y hxy
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_map.1 x.2
    let u' : ↥U := ⟨u, hu⟩
    obtain ⟨l₀, hl₀⟩ := MonoidHom.mem_range.1 l.2
    have hx : x = (⟨q u', Subgroup.mem_map_of_mem q u'.2⟩ : ↥(U.map q)) :=
      Subtype.ext hxu.symm
    have hlx : (l : MulAut (W ⧸ Z)) (x : W ⧸ Z) = q ((l₀ : MulAut W) (u' : W)) := by
      rw [show (l : MulAut (W ⧸ Z)) = s16t3_quotHom L Z hL l₀ from hl₀.symm]
      rw [hx]
      show CFSG.CGT.PushingUpLit.BHS5.quotAct Z (Subgroup.inclusion hL l₀)
        (QuotientGroup.mk (u' : W)) = q ((l₀ : MulAut W) (u' : W))
      rw [CFSG.CGT.PushingUpLit.BHS5.quotAct_mk]
      rfl
    have hφx : ((φ' x : ↥(U.map q)) : W ⧸ Z) = q ((φ u' : ↥U) : W) := by
      rw [hx, hφ'_apply u']
    have hy : (y : W ⧸ Z) = q ((l₀ : MulAut W) (u' : W)) := by
      rw [← hxy]
      change (l : MulAut (W ⧸ Z)) (x : W ⧸ Z) = q ((l₀ : MulAut W) (u' : W))
      exact hlx
    have hw' : ((l₀ : MulAut W) (u' : W)) ∈ U := hU l₀ l₀.2 u' u'.2
    have hysub : y = (⟨q ((l₀ : MulAut W) (u' : W)),
        Subgroup.mem_map_of_mem q hw'⟩ : ↥(U.map q)) :=
      Subtype.ext hy
    let w'' : ↥U := ⟨(l₀ : MulAut W) (u' : W), hw'⟩
    have hφy : ((φ' y : ↥(U.map q)) : W ⧸ Z) = q ((φ w'' : ↥U) : W) := by
      rw [hysub, hφ'_apply w'']
    have hleft : (l : MulAut (W ⧸ Z)) (q ((φ u' : ↥U) : W)) =
        q ((l₀ : MulAut W) ((φ u' : ↥U) : W)) := by
      rw [show (l : MulAut (W ⧸ Z)) = s16t3_quotHom L Z hL l₀ from hl₀.symm]
      show CFSG.CGT.PushingUpLit.BHS5.quotAct Z (Subgroup.inclusion hL l₀)
        (QuotientGroup.mk ((φ u' : ↥U) : W)) = q ((l₀ : MulAut W) ((φ u' : ↥U) : W))
      rw [CFSG.CGT.PushingUpLit.BHS5.quotAct_mk]
      rfl
    have hkey : q ((φ w'' : ↥U) : W) = q ((l₀ : MulAut W) ((φ u' : ↥U) : W)) := by
      change (((φ w'' : ↥U) : W) : W ⧸ Z) =
        ((((l₀ : MulAut W) ((φ u' : ↥U) : W)) : W) : W ⧸ Z)
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      exact hφ l₀ l₀.2 u' hw'
    change (l : MulAut (W ⧸ Z)) ((φ' x : ↥(U.map q)) : W ⧸ Z) =
      ((φ' y : ↥(U.map q)) : W ⧸ Z)
    rw [hφx, hleft, hφy, hkey]
  have hid : φ' = MulEquiv.refl _ := hE φ' heq
  intro u
  have h1 : (φ' (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)) : W ⧸ Z) =
      ((⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)) : W ⧸ Z) := by
    have h2 := congrArg
      (fun ψ : MulAut (↥(U.map q)) => ψ (⟨q u, Subgroup.mem_map_of_mem q u.2⟩ : ↥(U.map q)))
      hid
    exact congrArg (fun z : ↥(U.map q) => (z : W ⧸ Z)) h2
  have hqeq : q ((φ u : ↥U) : W) = q ((u : ↥U) : W) := by
    rw [hφ'_apply u] at h1
    simpa using h1
  have hmem : ((φ u : ↥U) : W) / ((u : ↥U) : W) ∈ Z :=
    QuotientGroup.eq_iff_div_mem.mp hqeq
  simpa [div_eq_mul_inv] using hmem

theorem s16t3_eq_of_equivariant (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : SumOfNatShape L U Z 1) (φ : ↥U ≃* ↥U)
    (hZ : ∀ u : ↥U, ((φ u : ↥U) : W) ∈ Z ↔ (u : W) ∈ Z)
    (hφ : ∀ l ∈ L, ∀ u : ↥U, ∀ hu : l (u : W) ∈ U,
      ((φ ⟨l (u : W), hu⟩ : ↥U) : W) * (l ((φ u : ↥U) : W))⁻¹ ∈ Z) :
    ∀ u : ↥U, ((φ u : ↥U) : W) * (u : W)⁻¹ ∈ Z := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOP, hsum⟩ | ⟨hOM, hsum⟩ | ⟨hAlt, hsum⟩
  · obtain hN := s16t3_sumOfNat_one hsum
    have hNkeep := hN
    obtain ⟨K, hK, hKf, hK2, hR⟩ := hN
    have hZ' := s16t3_stableZ_of_realizes hR
    have hU' := s16t3_stable_of_realizes hR
    have hL' : L ≤ stabSub Z := B1.le_stabSub_of_invariant hZ'
    exact s16t3_concl hL' hU'
      (s16c167_endUnits_ln (s16k_three_le_of_isSLn hq hSL)
        (s16t3_quotient_binaryNaturalSL hL' hNkeep)) φ hZ hφ
  · obtain hN := s16t3_sumOfNat_one hsum
    have hNkeep := hN
    obtain ⟨he, K, hK, hKf, hK2, hR⟩ := hN
    have hZ' := s16t3_stableZ_of_realizes hR
    have hU' := s16t3_stable_of_realizes hR
    have hL' : L ≤ stabSub Z := B1.le_stabSub_of_invariant hZ'
    exact s16t3_concl hL' hU'
      (s15k_abs_endUnits_sp (s16k_six_le_of_isSpn hq hSp)
        (s16t3_quotient_natSpn hL' hNkeep)) φ hZ hφ
  · obtain hN := s16t3_sumOfNat_one hsum
    have hNkeep := hN
    obtain ⟨he, K, hK, hKf, hK2, hR⟩ := hN
    have hZ' := s16t3_stableZ_of_realizes hR
    have hU' := s16t3_stable_of_realizes hR
    have hL' : L ≤ stabSub Z := B1.le_stabSub_of_invariant hZ'
    exact s16t3_concl hL' hU'
      (s15k_abs_endUnits_omegaPlus (s16k_six_le_of_isOmegaPlus hq hOP)
        (s16t3_quotient_natOmegaPlus hL' hNkeep)) φ hZ hφ
  · obtain hN := s16t3_sumOfNat_one hsum
    have hNkeep := hN
    obtain ⟨he, K, hK, hKf, b, c, hK2, hirr, hR⟩ := hN
    have hZ' := s16t3_stableZ_of_realizes hR
    have hU' := s16t3_stable_of_realizes hR
    have hL' : L ≤ stabSub Z := B1.le_stabSub_of_invariant hZ'
    exact s16t3_concl hL' hU'
      (s16t3_endUnits_omegaMinus (s16k_four_le_of_isOmegaMinus hq hOM)
        (s16t3_quotient_natOmegaMinus hL' hNkeep)) φ hZ hφ
  · obtain hN := s16t3_sumOfNat_one hsum
    have hZ' := s16t3_stableZ_of_realizes hN
    have hU' := s16t3_stable_of_realizes hN
    have hL' : L ≤ stabSub Z := B1.le_stabSub_of_invariant hZ'
    exact s16t3_concl hL' hU'
      (s16c167_endUnits_alt (s16k_five_le_of_isAlt hq hAlt)
        (s16t3_quotient_alternatingNatural hL' hN)) φ hZ hφ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

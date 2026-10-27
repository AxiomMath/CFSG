module

public import CFSG.Quasithin.Background.FFC7C
public import CFSG.Quasithin.Background.FFC6A
public import CFSG.Quasithin.Background.FFC6N
public import CFSG.Quasithin.Background.FFC7B

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5
open scoped commutatorElement Matrix

namespace B510

section Pipeline

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem le_stabSub_commV {G L : Subgroup (MulAut V)} (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    G ≤ stabSub (commV L) := by
  intro g hg u
  constructor
  · intro h
    have h1 : ∀ x ∈ L, g⁻¹ * x * g⁻¹⁻¹ ∈ L := fun x hx => hn g⁻¹ (G.inv_mem hg) x hx
    have h2 := commV_invariant h1 h
    simpa using h2
  · intro h
    exact commV_invariant (fun x hx => hn g hg x hx) h

theorem sqtk_autSub (hA21 : AsA21SQTKSection) {G L : Subgroup (MulAut V)} {W : Subgroup V}
    (hb : B53Hyp G) (hL : CFSG.Open.IsComponentOf L G) (hLU : L ≤ stabSub W)
    (hfaith : ∀ g ∈ L, (∀ w ∈ W, g w = w) → g = 1) : SQTKGroup ↥(autSub L W) := by
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hSL : SQTKGroup ↥L := FFC.sqtk_of_le hA21 (isQuotientOfSQTKTauCeti_of_b53 hb) hL.1 hLq
  exact B5.sqtk_of_mulEquiv (resEquiv hLU hfaith).symm hSL

omit [Finite V] in
theorem fixV_inf_eq_bot_of_natural {L : Subgroup (MulAut V)} {U : Subgroup V} {d n : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL L U ⊥ d n) : fixV L ⊓ U = ⊥ := by
  have hirr := irr_of_binaryNatural hd h
  have hJ : ∀ x ∈ L, ∀ w ∈ fixV L ⊓ U, x w ∈ fixV L ⊓ U := fun x hx w hw => by
    rw [mem_fixV.mp hw.1 x hx]
    exact hw
  rcases hirr (fixV L ⊓ U) hJ bot_le inf_le_right with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨K, hK, hfin, hc, π, hπ⟩ := h
    obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
    set i0 : Fin d := ⟨0, by omega⟩ with hi0
    set i1 : Fin d := ⟨1, by omega⟩ with hi1
    have hne : i1 ≠ i0 := by simp [hi0, hi1, Fin.ext_iff]
    obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd (Pi.single i0 (1 : K)))
    have huU : (u : V) ∈ fixV L ⊓ U := by rw [h0]; exact u.2
    set γ : ↥(Assembly.LowTwoRank.StatedSL d K) := ⟨tGLn i1 i0 hne 1, tGLn_mem hne 1⟩ with hγ
    have hgu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hπ.2.2.2.1 (π γ) u u.2
    have hfix : ((π γ : ↥L) : MulAut V) (u : V) = u := mem_fixV.mp huU.1 _ (π γ).2
    have h2 : (⟨((π γ : ↥L) : MulAut V) (u : V), hgu⟩ : ↥U) = u := Subtype.ext hfix
    have h1 : f u = natAct _ γ (f u) := (congrArg f h2.symm).trans (hfe γ u hgu)
    rw [hu] at h1
    have h3 : (Pi.single i0 (1 : K) : Fin d → K) =
        Matrix.transvection i1 i0 1 *ᵥ (Pi.single i0 (1 : K) : Fin d → K) :=
      congrArg Multiplicative.toAdd h1
    rw [H.transvection_mulVec] at h3
    have h4 := congrFun h3 i1
    simp [hne] at h4

omit [Finite V] in
theorem not_le_centSub_of_faithful {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLo : CFSG.Open.IsQuasisimple ↥L) (hfaith : ∀ g ∈ L, (∀ w ∈ W, g w = w) → g = 1) :
    ¬ L ≤ centSub W := by
  intro hle
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have : L = ⊥ := eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (hfaith g hg (hle hg))
  exact (Subgroup.nontrivial_iff_ne_bot L).1 hnt this

theorem b51Hyp_W (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1) {G D L : Subgroup (MulAut V)}
    (hb : B53Hyp G) (hL : CFSG.Open.IsComponentOf L G) (hD : IsFFStarOffender G D) (hLD : ⁅L, D⁆ = L)
    (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hfaith : ∀ g ∈ L, (∀ w ∈ commV L, g w = w) → g = 1) (hDnc : ¬ D ≤ centSub (commV L))
    (hcommW : commSub (commV L) L = commV L)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → fixV L ⊓ commV L ≤ J →
      J ≤ commV L → J = fixV L ⊓ commV L ∨ J = commV L) :
    B51Hyp (autSub (L ⊔ D) (commV L)) (autSub L (commV L)) ∧
      ∀ y ∈ autSub (L ⊔ D) (commV L), y ^ 2 ∈ autSub L (commV L) := by
  obtain ⟨hH₀n, hsq, -, -, -, -⟩ := B59.red_basic hV hL hD hLD
  have hGst : G ≤ stabSub (commV L) := le_stabSub_commV hn
  have hLU : L ≤ stabSub (commV L) := hL.1.trans hGst
  have hDU : D ≤ stabSub (commV L) := hD.1.trans hGst
  have hst : L ⊔ D ≤ stabSub (commV L) := sup_le hLU hDU
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLnc : ¬ L ≤ centSub (commV L) := not_le_centSub_of_faithful hLo hfaith
  have hLbq : CFSG.Open.IsQuasisimple ↥(autSub L (commV L)) := B1Red.isQuasisimple_autSub hLU hLo hLnc
  have hLbH : autSub L (commV L) ≤ autSub (L ⊔ D) (commV L) := autSub_mono le_sup_left _
  have hM : ∀ v : ↥(commV L), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  have hLbn : ∀ g ∈ autSub (L ⊔ D) (commV L), ∀ l ∈ autSub L (commV L),
      g * l * g⁻¹ ∈ autSub L (commV L) := fun g hg l hl => autSub_conj_mem hH₀n hg hl
  have hO2b : pCoreOf 2 (autSub (L ⊔ D) (commV L)) = ⊥ :=
    pCore_eq_bot_aut hM hLbq hLbH hLbn (commSub_top_autSub hLU hcommW) (irr_autSub hLU hirr)
  have hHb2 : ∀ y ∈ autSub (L ⊔ D) (commV L), y ^ 2 ∈ autSub L (commV L) := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine mem_autSub.2 ⟨g ^ 2, ?_, by rw [map_pow]⟩
    simpa using hsq _ hgH
  have hFb : quasithinGenFitting (autSub (L ⊔ D) (commV L)) = autSub L (commV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLbH hLbn hLbq hHb2 hO2b
  have hAH₀ : IsFFStarOffender (L ⊔ D) D := ⟨le_sup_right, hD.2.1, hD.2.2.1, hD.2.2.2⟩
  have hoff : IsFFStarOffender (autSub (L ⊔ D) (commV L)) (autSub D (commV L)) :=
    B1Red.isFFStarOffender_autSub hAH₀ (fun a ha w hw => (hst (Subgroup.mem_sup_right ha) w).2 hw) hDnc
  have hcomm : ⁅autSub L (commV L), autSub D (commV L)⁆ = autSub L (commV L) :=
    B1Red.commutator_autSub_eq hLU hDU hLD
  have hsup : autSub (L ⊔ D) (commV L) = autSub L (commV L) ⊔ autSub D (commV L) :=
    B59.autSub_sup hLU hDU
  have hZ : centerOf (autSub (L ⊔ D) (commV L)) ≤ autSub L (commV L) :=
    hFb ▸ B59.centerOf_le_genFitting _
  have hKJ : autSub L (commV L) ≤ ffJ (autSub (L ⊔ D) (commV L)) :=
    B1Red.K_le_ffJ hLbH hoff hcomm
  have hJ : autSub (L ⊔ D) (commV L) = ffJ (autSub (L ⊔ D) (commV L)) :=
    le_antisymm (hsup.le.trans (sup_le hKJ (B6.le_ffJ hoff))) (B6.ffJ_le _)
  exact ⟨⟨by rw [hFb, sup_eq_left.2 hZ], B1Red.isQuasisimple_of_open hLbq,
    sqtk_autSub hA21 hb hL hLU hfaith, hLbH, hO2b, hJ⟩, hHb2⟩

theorem offenders_of_natural
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (h57 : B57Input) {G L : Subgroup (MulAut V)} (hc : B56Counterex G)
    (hL : CFSG.Open.IsComponentOf L G)
    (hnat : (∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n) ∨
      (∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 n)) : B510Offenders G L := by
  intro D hD d hd
  have hV := hc.hV
  have hJ : G = ffJ G := hc.hyp.2.1
  have hnG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B55.normalizes_comp hP4 hV hJ hL
  have hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    B19Aux.conj_mem_of_le_normalizer hnG hg hl
  have hGst : G ≤ stabSub (commV L) := le_stabSub_commV hn
  have hLU : L ≤ stabSub (commV L) := hL.1.trans hGst
  have hfaith : ∀ g ∈ L, (∀ w ∈ commV L, g w = w) → g = 1 := by
    rcases hnat with ⟨n, h⟩ | ⟨n, h⟩
    · exact faithful_of_binaryNatural h
    · exact faithful_of_binaryNatural h
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ⟨hL.2.2.1⟩
  have hcommW : commSub (commV L) L = commV L := commSub_commV_perfect hLperf
  have hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → fixV L ⊓ commV L ≤ J →
      J ≤ commV L → J = fixV L ⊓ commV L ∨ J = commV L := by
    rcases hnat with ⟨n, h⟩ | ⟨n, h⟩
    · exact irr_of_binaryNatural (by norm_num) h
    · exact irr_of_binaryNatural (by norm_num) h
  have hno : ¬ ThreeRank2 ↥L := h57 V G hc L hL
  have hLnc : ¬ L ≤ centSub (commV L) := not_le_centSub_of_faithful hL.2.2 hfaith
  by_cases hDW : D ≤ centSub (commV L)
  · exact ⟨1, L.one_mem, fun w hw => by simpa using hDW hd w hw⟩
  · have hDn : ∀ b ∈ D, ∀ k ∈ L, b * k * b⁻¹ ∈ L := fun b hb k hk => hn b (hD.1 hb) k hk
    rcases B1Red.commutator_eq_or_commute (Or.inl hL.2.2) hDn with hLD | hcent
    · obtain ⟨hb51, hsqX⟩ := b51Hyp_W hA21 hV hc.hyp hL hD hLD hn hfaith hDW hcommW hirr
      have hKX : autSub L (commV L) ≤ autSub (L ⊔ D) (commV L) := autSub_mono le_sup_left _
      have hM : ∀ v : ↥(commV L), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
      have hKq : CFSG.Open.IsQuasisimple ↥(autSub L (commV L)) :=
        B1Red.isQuasisimple_autSub hLU hL.2.2 hLnc
      have hKbot : autSub L (commV L) ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.ComponentClassification.Quasisimple.nontrivial hKq)
      have hne : autSub (L ⊔ D) (commV L) ≠ ⊥ := fun h => hKbot (eq_bot_iff.2 (hKX.trans h.le))
      have hnoK : ¬ ThreeRank2 ↥(autSub L (commV L)) := fun h =>
        hno (h.of_mulEquiv (resEquiv hLU hfaith).symm)
      have hnatK : (∃ n, BinaryNaturalSL (autSub L (commV L)) (commV (autSub L (commV L)))
            (fixV (autSub L (commV L)) ⊓ commV (autSub L (commV L))) 2 n) ∨
          (∃ n, BinaryNaturalSL (autSub L (commV L)) (commV (autSub L (commV L)))
            (fixV (autSub L (commV L)) ⊓ commV (autSub L (commV L))) 3 n) := by
        rcases hnat with ⟨n, h⟩ | ⟨n, h⟩
        · exact Or.inl ⟨n, natural_autSub hLU hfaith hcommW h⟩
        · exact Or.inr ⟨n, natural_autSub hLU hfaith hcommW h⟩
      have hXK := eq_of_natural hB51 hM hb51 hKX hsqX hne hnoK hnatK
      have hdst : d ∈ stabSub (commV L) := hGst (hD.1 hd)
      have hmem : resHom (commV L) ⟨d, hdst⟩ ∈ autSub (L ⊔ D) (commV L) :=
        mem_autSub.2 ⟨⟨d, hdst⟩, Subgroup.mem_sup_right hd, rfl⟩
      rw [hXK] at hmem
      obtain ⟨g', hg'L, hg'r⟩ := mem_autSub.1 hmem
      refine ⟨(g' : MulAut V), hg'L, fun w hw => ?_⟩
      have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨w, hw⟩ : ↥(commV L)) : V)) hg'r
      exact this.symm
    · refine ⟨1, L.one_mem, fun w hw => ?_⟩
      have hq : ∀ x ∈ L, d * x = x * d := fun x hx => hcent d hd x hx
      have hqW : ∀ w ∈ commV L, d w ∈ commV L := fun w hw => (hGst (hD.1 hd) w).2 hw
      have hq2 : ∀ w ∈ commV L, d (d w) = w := by
        intro w _
        have := congrArg (fun g : MulAut V => g w) (hD.2.2.1.2 d hd)
        simpa [pow_two, MulAut.mul_apply] using this
      have := schur_nilp hV (fun x hx w hw => (hLU hx w).2 hw) hcommW hirr hq hqW hq2 w hw
      simpa using this

end Pipeline

end B510

end FFC

end CFSG.Quasithin

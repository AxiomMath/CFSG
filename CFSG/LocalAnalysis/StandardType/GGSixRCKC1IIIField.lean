module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LocalAnalysis.StandardType.GGLabelIsoField
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType

section ModelParameters


theorem lieModel_parameters_of_row_III
    {X : Type} [Group X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J)
    {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hmodel : LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) :
    f = 1 ∧ ((t = .PSp ∧ 3 ≤ n) ∨ (t = .PSU ∧ 4 ≤ n)) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmarked
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  have hadm := CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hmodel
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    obtain ⟨ht', hn', hf'⟩ := CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet
      (markRank lab) _ 1 t n f hm' hadm hmodel
    exact ⟨hf', Or.inl ⟨ht', by omega⟩⟩
  · rw [ht] at hm'
    obtain ⟨ht', hn', hf'⟩ := CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt h4
      _ 1 t n f hm' hadm hmodel
    exact ⟨hf', Or.inr ⟨ht', by omega⟩⟩

theorem not_fieldExtCase_of_row_III
    {X : Type} [Group X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J)
    {t : CFSG.Open.StatedLieTag} {f : ℕ} (hf : 1 ≤ f) :
    ¬ GGSixLSevenFieldExtCase J t f := by
  rintro ⟨t', n, f', hlt, hmodel, -⟩
  have hf' := (lieModel_parameters_of_row_III hrow hmodel).1
  omega

end ModelParameters

section Certificates


theorem two_pow_six_dvd_card_centerQuot_of_row_III
    {X : Type} [Group X] [Finite X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J) :
    2 ^ 6 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmodel
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.SymplecticPilot.card_of_lieModel_PSp_two_pow hm']
    have h9 : 9 ≤ markRank lab * markRank lab := Nat.mul_le_mul h3 h3
    exact (Nat.pow_dvd_pow 2 (by omega : 6 ≤ 1 * (markRank lab * markRank lab))).trans
      (CFSG.SeitzReduction.SymplecticPilot.ordBC_two_pow_bounds (by omega)).1
  · rw [ht] at hm'
    exact CFSG.SeitzReduction.UnitaryPilot.two_pow_six_dvd_card_of_lieModel_PSU h4 hm'

theorem two_pow_six_dvd_card_centerQuot_of_small_field_row
    {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (hrow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J) :
    2 ^ 6 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  rcases hrow with hIII | hIIp
  · exact two_pow_six_dvd_card_centerQuot_of_row_III hIII
  · obtain ⟨e⟩ := RCKK1IIp.rckIIp_iso hIIp
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem not_small_card_centerQuot_of_small_field_row
    {X : Type} [Group X] [Finite X] {J L : Subgroup X}
    (hrow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J) (hJL : J ≤ L) :
    Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 60 ∧
      Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 360 ∧
      Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 6048 := by
  have h64 : 2 ^ 6 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    (two_pow_six_dvd_card_centerQuot_of_small_field_row hrow).trans
      (RCKU33.card_centerQuot_dvd hJL)
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at h64 <;> norm_num at h64

theorem markDeg_eq_one_of_n_eq_one_of_small_field_row_le
    {X : Type} [Group X] [Finite X] {J L : Subgroup X} {lab : LargeEvenLabel}
    (hrow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J) (hJL : J ≤ L) (hn : lab.n = 1)
    (hmodel : MarkedModel lab (↥L ⧸ Subgroup.center ↥L)) : markDeg lab = 1 := by
  have hsmall := not_small_card_centerQuot_of_small_field_row hrow hJL
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at hn
  subst n
  cases tag
  case twD =>
    by_cases h2 : rank = 2
    · subst rank
      have hm : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 2 := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hmodel
      have hc : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 := by
        rw [CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hm]
        decide
      exact (hsmall.1 hc).elim
    · simp [markDeg, h2]
  case B2der =>
    exact (hsmall.2.1 (ggMarkedModel_card_b2der rfl hmodel)).elim
  all_goals rfl

theorem exists_labels_dvd_of_innerDiag_component
    {X : Type} [Group X] [Finite X] {p : ℕ} {B L J : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdB : d ∈ B) (hdp : d ^ p = 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hMark : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer {d})) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ lab.n ∣ labJ.n ∧
      LargeEvenMarking ↥L (fun lab' _ _ I _ θ => lab' = lab ∧
        ∀ b ∈ B, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) := by
  have hM := ggMarking_and_labelAll_dep
    (fun lab hlab => TCJ.ggTCJKnown_holds p hp hp2 lab hlab) hMark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, instR, I, F, _, _, θ, hind, hTC⟩ := largeEvenRawDatum_exists hraw
  letI : Group R := instR
  have hdN : d ∈ Subgroup.normalizer (L : Set X) := hBN hdB
  have hdpAut : L.normalizerMonoidHom ⟨d, hdN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ p = 1 :=
      Subtype.ext (by simpa using hdp)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind d⁻¹ (B.inv_mem hdB)
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    exact (QuotientGroup.eq_one_iff l).mp
      (θ.injective (h0.trans (map_one θ).symm))
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨d, hdN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨d, hdN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨d, hdN⟩ l : ↥L) : X) = d⁻¹⁻¹ * (l : X) * d⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥L ψ hψsurj hψker hperf _ hdpAut hφe (J.subgroupOf L)
      (ggIsComponentOf_ggFixSub_normalizerMonoidHom hdN hJ)
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hhas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
      (Subgroup.map_center_eq _)) hhasJ
  refine ⟨lab, labJ, hlab, hlabJ, hhas, hdvd, hperf, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ', hact, _⟩
  exact ⟨hs, hna, θ', rfl, hact⟩

theorem field_two_marking_of_small_field_row
    {X : Type} [Group X] [Finite X] {p : ℕ} {B D J L : Subgroup X} {x : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2)
    (hDB : D ≤ B) (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hMark : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hLx : L ≤ Subgroup.centralizer {x})
    (hNotCent : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)))
    (hRow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J) :
    LargeEvenMarking ↥L (fun lab _ _ I _ θ => lab.n = 1 ∧
      ∀ b ∈ B, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) := by
  obtain ⟨d, hdD, hdNot⟩ : ∃ d ∈ D, d ∉ Subgroup.centralizer (L : Set X) := by
    by_contra h
    apply hNotCent
    intro d hdD
    by_contra hdNot
    exact h ⟨d, hdD, hdNot⟩
  have hxC : x ∈ Subgroup.centralizer (L : Set X) := by
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hdNotPowers : d ∉ Subgroup.zpowers x :=
    fun hd => hdNot ((Subgroup.zpowers_le.mpr hxC) hd)
  have hgen : Subgroup.closure ({x, d} : Set X) = D :=
    ggClosure_pair_eq hp hDcard hxD hdD hx1 (hD.2 x hxD) hdNotPowers
  have hJd : IsComponentOf J (L ⊓ Subgroup.centralizer {d}) := by
    rw [← hgen, ggInf_centralizer_pair hLx] at hJ
    exact hJ
  obtain ⟨lab, labJ, hlab, hlabJ, hhasJ, hdvd, hm⟩ :=
    exists_labels_dvd_of_innerDiag_component hp hp2 (hDB hdD) (hD.2 d hdD) hBN hMark hJd
  have hMarkJ : LargeEvenMarking ↥J (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .III ∨ ggSixRCKLabelRow lab = .IIp) := by
    rcases hRow with hIII | hIIp
    · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inl h) hIII
    · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inr h) hIIp
  obtain ⟨lab₀, hlab₀, hhas₀, R₀, _, I₀, F₀, θ₀, hrow₀⟩ :=
    largeEvenMarking_exists_hasLabel hMarkJ
  have hdeg₀ : markDeg lab₀ = 1 := (ggSixRCKLabelRow_field_two hlab₀ hrow₀).2
  have hiso : GGLabelIso labJ lab₀ :=
    ggLabelRigidInput_holds labJ lab₀ _ hlabJ hlab₀ hhasJ hhas₀
  have hJone : labJ.n = 1 := Nat.dvd_one.mp
    (hdeg₀ ▸ labelIso_dvd_markDeg hlabJ hiso)
  have hone : lab.n = 1 := Nat.dvd_one.mp (hJone ▸ hdvd)
  refine largeEvenMarking_mono ?_ hm
  intro lab' R _ I F θ h
  refine ⟨?_, h.2⟩
  rw [h.1]
  exact hone

theorem defining_field_two_marking_of_small_field_row
    {X : Type} [Group X] [Finite X] {p : ℕ} {B D J L : Subgroup X} {x : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2)
    (hDB : D ≤ B) (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hMark : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hLx : L ≤ Subgroup.centralizer {x})
    (hNotCent : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)))
    (hRow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J) :
    LargeEvenMarking ↥L (fun lab _ _ I _ θ => markDeg lab = 1 ∧
      ∀ b ∈ B, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) := by
  have hL := field_two_marking_of_small_field_row hp hp2 hD hDcard hDB hxD hx1
    hBN hMark hLx hNotCent hJ hRow
  obtain ⟨hperf, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hL
  obtain ⟨R, _, I, F, _, _, θ, ⟨hn, _⟩, hmodel⟩ := largeEvenRawDatum_exists hraw
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hdeg : markDeg lab = 1 := markDeg_eq_one_of_n_eq_one_of_small_field_row_le hRow hJL hn
    (MarkedModel.of_mulEquiv θ.symm hmodel)
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs, hna, θ', ⟨_, hact⟩, _⟩
  exact ⟨hs, hna, θ', hdeg, hact⟩

theorem ambient_field_eq_one_of_small_field_row
    {X : Type} [Group X] [Finite X] {t : CFSG.Open.StatedLieTag} {n f p : ℕ}
    {G₀ A B D J L : Subgroup X} {x : X}
    (hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f)
    (hRow : GGSixRCKJRow .III J ∨ GGSixRCKJRow .IIp J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hBA : B ≤ A) (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2)
    (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hMarkG : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ))
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hMarkL : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hCompL : IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}))
    (hNotCent : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hCompJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X))) : f = 1 := by
  have hD : IsElemAbelian p D := (hA.mono hBA).mono hDB
  have hL := defining_field_two_marking_of_small_field_row hp hp2 hD hDcard hDB hxD hx1
    hBN hMarkL (hCompL.1.trans inf_le_right) hNotCent hCompJ hRow
  obtain ⟨labG, labL, hΛG, hΛL, hhasL, hdvd, hmG⟩ :=
    exists_labels_dvd_of_innerDiag_component hp hp2 (hBA (hDB hxD))
      (hA.2 x (hBA (hDB hxD))) hAN hMarkG hCompL
  obtain ⟨lab₀, hΛ₀, hhas₀, R₀, _, I₀, F₀, θ₀, hdeg₀, _⟩ :=
    largeEvenMarking_exists_hasLabel hL
  have hIsoL : GGLabelIso labL lab₀ :=
    ggLabelRigidInput_holds labL lab₀ _ hΛL hΛ₀ hhasL hhas₀
  have hnL : labL.n = 1 := Nat.dvd_one.mp
    (hdeg₀ ▸ labelIso_dvd_markDeg hΛL hIsoL)
  have hnG : labG.n = 1 := Nat.dvd_one.mp (hnL ▸ hdvd)
  have hmG' := largeEvenMarking_markedModel hmG
  obtain ⟨_, lab', hΛ', hraw⟩ := hmG'
  obtain ⟨R, _, I, F, _, _, θ, ⟨heq, _⟩, hmodel⟩ := largeEvenRawDatum_exists hraw
  have hhasG : GGHasLabel labG (↥G₀ ⧸ Subgroup.center ↥G₀) := by
    rw [← heq]
    exact largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.2.2.choose⟩) hraw
  have hZ : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    letI : Group.IsPerfect ↥G₀ := ⟨hMarkG.1⟩
    exact Group.IsPerfect.center_quotient_center_eq_bot _
  obtain ⟨labU, hΛU, _, _, _, hfU, hhasU⟩ :=
    exists_label_rawDatum_of_lieModel hZ hLie
  have hJG : J ≤ G₀ :=
    (hCompJ.1.trans inf_le_left).trans (hCompL.1.trans inf_le_left)
  have hdegG : markDeg labG = 1 := markDeg_eq_one_of_n_eq_one_of_small_field_row_le
    hRow hJG hnG (by rw [← heq]; exact MarkedModel.of_mulEquiv θ.symm hmodel)
  have hIsoG : GGLabelIso labU labG :=
    ggLabelRigidInput_holds labU labG _ hΛU hΛG hhasU hhasG
  exact hfU.symm.trans ((TableCRes.markDeg_eq_of_ggLabelIso hIsoG).trans hdegG)

end Certificates

end CFSG.StandardType.RCKC1

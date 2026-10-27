module

public import CFSG.LocalAnalysis.EvenBN.G2.G2LieModelFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem isDirSumOver_autQuot_bot_of_commV {W : Type} [CommGroup W]
    {S : Set (Subgroup (MulAut W))} (h : IsDirSumOver S commV) :
    IsDirSumOver S (fun X => commV (autQuot X (⊥ : Subgroup W))) := by
  have hf : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap : ∀ X : Subgroup (MulAut W),
      commV (autQuot X (⊥ : Subgroup W)) =
        (commV X).map (QuotientGroup.mk' (⊥ : Subgroup W)) :=
    fun X => (map_commV_eq_commV_autQuot X ⊥ (B5.Ln.stabSub_bot_le X)).symm
  obtain ⟨hind, hsup⟩ := h
  refine ⟨?_, ?_⟩
  · rw [funext fun X : S => hmap (X : Subgroup (MulAut W))]
    exact CFSG.LocalCores.iSupIndep_map_of_injective hf hind
  · have hsup' : (⨆ X : S, commV (autQuot (X : Subgroup (MulAut W)) ⊥)) =
        (⨆ X : S, commV (X : Subgroup (MulAut W))).map (QuotientGroup.mk' (⊥ : Subgroup W)) := by
      rw [Subgroup.map_iSup]
      congr 1
      funext X
      exact hmap X
    rw [hsup', hsup,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (⊥ : Subgroup W))]

theorem le_commV_of_mem_irrSet {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hJ : J ∈ irrSet L) : J ≤ commV L := by
  rw [commV_eq_commSub]
  calc J = commSub J L := hJ.1.symm
    _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl

theorem inf_fixV_eq_bot_of_mem_irrSet {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hinf : commV L ⊓ fixV L = ⊥) {J : Subgroup W}
    (hJ : J ∈ irrSet L) : J ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff, ← hinf]
  exact inf_le_inf_right _ (le_commV_of_mem_irrSet hJ)

private theorem commV_inf_fixV_eq_bot_of_basic {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (conjSet L Y) commV) : commV L ⊓ fixV L = ⊥ :=
  commV_inf_fixV_eq_bot_of_isDirSumOver hL hfix (isDirSumOver_autQuot_bot_of_commV hsum)

private theorem irrSpanTrans_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) :
    IrrSpanTrans Y H ∧ (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤ := by
  have hHc : H = ⨆ X ∈ conjSet L Y, X := by
    rw [hH, iSup_conjSet_eq_biSup_conj]
  obtain ⟨h1, -, hHY, -, hnorm, hne⟩ := h_facts hL hHc
  exact (w4Lem12_5_holds W hW Y hO2 hB H hne hHY hnorm).2 L hL h1

theorem mem_irrSet_of_eq_biSup_conj {W : Type} [CommGroup W] [Finite W]
    {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (conjSet L Y) commV)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) {I : Subgroup W}
    (hI : I ∈ irrSet L) : I ∈ irrSet H := by
  have hsum' := isDirSumOver_autQuot_bot_of_commV hsum
  have hLH : L ≤ H := le_of_eq_biSup_conj hH
  have hLmem : L ∈ conjSet L Y := ⟨1, Y.one_mem, by ext x; simp⟩
  have hIc : I ≤ commV L := le_commV_of_mem_irrSet hI
  have hHI : H ≤ stabSub I := by
    rw [hH]
    refine iSup₂_le fun φ hφ => B1.le_stabSub_of_invariant fun x hx u hu => ?_
    by_cases hX : L.map (MulAut.conj φ).toMonoidHom = L
    · rw [hX] at hx
      exact stableUnder_of_mem_irrSet hI x hx u hu
    · rw [fix_commV_of_mem_conjSet_of_ne hL hsum' ⟨φ, hφ, rfl⟩ hLmem hX x hx u (hIc hu)]
      exact hu
  have hstab : StableUnder H I := fun h hh u hu => (mem_stabSub.mp (hHI hh) u).2 hu
  have hIL : I ⊓ fixV L = ⊥ :=
    inf_fixV_eq_bot_of_mem_irrSet (commV_inf_fixV_eq_bot_of_basic hL hfix hsum) hI
  have hIH : I ⊓ fixV H = ⊥ := by
    rw [eq_bot_iff, ← hIL]
    exact inf_le_inf_left I fun v hv x hx => hv x (hLH hx)
  refine ⟨le_antisymm ((Subgroup.closure_le _).mpr ?_)
    (hI.1.symm.le.trans (commSub_mono le_rfl hLH)), ?_⟩
  · rintro _ ⟨h, hh, u, hu, rfl⟩
    exact I.mul_mem (hstab h hh u hu) (I.inv_mem hu)
  · rw [hIH]
    refine ⟨bot_lt_iff_ne_bot.mpr (ne_bot_of_mem_irrSet hI), hstab, fun h _ u hu => ?_,
      fun J hJ _ hJI => ?_⟩
    · rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · have h := hI.2.2.2.2 J (fun x hx => hJ x (hLH hx)) (by rw [hIL]; exact bot_le) hJI
      rwa [hIL] at h

theorem commV_sup_fixV_eq_top_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) :
    commV L ⊔ fixV L = ⊤ := by
  have hspan : (⨆ I ∈ irrSet L, I) ≤ commV L :=
    iSup₂_le fun I hI => le_commV_of_mem_irrSet (W := W) hI
  have htop : (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤ :=
    (irrSpanTrans_of_basic hW hO2 hB hL
      (H := ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) rfl).2
  rw [eq_top_iff]
  intro u _
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top u)
  exact Subgroup.mem_sup.mpr ⟨a, hspan ha, b, hb, rfl⟩

theorem commV_eq_top_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L X : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) :
    commV X = ⊤ := by
  have hHc : X = ⨆ X' ∈ conjSet L Y, X' := by
    rw [hX, iSup_conjSet_eq_biSup_conj]
  exact commV_eq_top (W := W) hW hO2 hB hL hHc

theorem commV_eq_iSup_irrSet_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV) :
    commV L = ⨆ J ∈ irrSet L, J := by
  have htop : (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤ :=
    (irrSpanTrans_of_basic hW hO2 hB hL
      (H := ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) rfl).2
  have hinf := commV_inf_fixV_eq_bot_of_basic hL hfix hsum
  have hle : (⨆ J ∈ irrSet L, J) ≤ commV L := iSup₂_le fun J hJ => le_commV_of_mem_irrSet hJ
  refine le_antisymm (fun u hu => ?_) hle
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top u)
  have hbc : b ∈ commV L := by
    have hab : b = a⁻¹ * (a * b) := by group
    rw [hab]
    exact (commV L).mul_mem ((commV L).inv_mem (hle ha)) hu
  have hb1 : b ∈ commV L ⊓ fixV L := ⟨hbc, hb⟩
  rw [hinf, Subgroup.mem_bot] at hb1
  rw [hb1, mul_one]
  exact ha

theorem exists_sSupIndep_irrSet_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    ∃ s : Set (Subgroup W), I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s ∧ sSup s = commV L := by
  have hinf := commV_inf_fixV_eq_bot_of_basic hL hfix hsum
  have : Finite (Subgroup W) :=
    Finite.of_injective (fun K : Subgroup W => (K : Set W)) SetLike.coe_injective
  obtain ⟨s, hs⟩ := (Set.toFinite
    {s : Set (Subgroup W) | I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s}).exists_maximal
    ⟨{I}, Set.mem_singleton I, Set.singleton_subset_iff.mpr hI, sSupIndep_singleton I⟩
  obtain ⟨hIs, hsL, hsind⟩ := hs.prop
  refine ⟨s, hIs, hsL, hsind,
    le_antisymm (sSup_le fun J hJ => le_commV_of_mem_irrSet (hsL hJ)) ?_⟩
  rw [commV_eq_iSup_irrSet_of_basic hW hO2 hB hL hfix hsum]
  refine iSup₂_le fun J hJ => ?_
  by_contra hJs
  have hstab : StableUnder L (sSup s) := by
    rw [sSup_eq_iSup]
    exact stableUnder_iSup fun K => stableUnder_iSup fun hK =>
      stableUnder_of_mem_irrSet (hsL hK)
  have hJinf : J ⊓ fixV L = ⊥ := inf_fixV_eq_bot_of_mem_irrSet hinf hJ
  rcases hJ.2.2.2.2 (J ⊓ sSup s)
      (stableUnder_inf (stableUnder_of_mem_irrSet hJ) hstab)
      (by rw [hJinf]; exact bot_le) inf_le_left with h | h
  · rw [hJinf] at h
    have hJnot : J ∉ s := fun hm => hJs (le_sSup hm)
    have hmem : insert J s ∈ {s : Set (Subgroup W) | I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s} :=
      ⟨Set.mem_insert_of_mem J hIs, Set.insert_subset hJ hsL,
        sSupIndep_insert_of_disjoint_of_irreducible hsind hJnot (disjoint_iff.mpr h)⟩
    exact hJnot (hs.2 hmem (Set.subset_insert J s) (Set.mem_insert J s))
  · exact hJs (by rw [← h]; exact inf_le_right)

theorem exists_secIsoOn_of_mem_irrSet_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV)
    {I J : Subgroup W} (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L) :
    ∃ g ∈ Y, SecIsoOn L (I.map (g : MulAut W).toMonoidHom) ⊥ J ⊥ := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (MulAut W), H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom :=
    ⟨_, rfl⟩
  have hfixH : fixV H = ⊥ := by
    rw [hH, ← iSup_conjSet_eq_biSup_conj]
    exact hfix
  have hLH : L ≤ H := le_of_eq_biSup_conj hH
  obtain ⟨g, hg, hsec⟩ := (irrSpanTrans_of_basic hW hO2 hB hL hH).1.2 I
    (mem_irrSet_of_eq_biSup_conj hL hfix hsum hH hI) J
    (mem_irrSet_of_eq_biSup_conj hL hfix hsum hH hJ)
  rw [hfixH, sup_bot_eq, sup_bot_eq] at hsec
  obtain ⟨h1, h2, h3, h4, h5, h6, β, hβ1, hβ2, hβ3, hβ4⟩ := hsec
  exact ⟨g, hg, h1, h2, fun x hx => h3 x (hLH hx), fun x hx => h4 x (hLH hx),
    fun x hx => h5 x (hLH hx), fun x hx => h6 x (hLH hx), β, hβ1, hβ2, hβ3,
    fun x hx => hβ4 x (hLH hx)⟩

theorem rk_eq_of_mem_irrSet_of_basic {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV)
    {I J : Subgroup W} (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L) : rk ↥J = rk ↥I := by
  obtain ⟨g, -, hsec⟩ := exists_secIsoOn_of_mem_irrSet_of_basic hW hO2 hB hL hfix hsum hI hJ
  obtain ⟨-, -, -, -, -, -, β, hβ1, hβ2, hβ3, -⟩ := hsec
  have hcard : Nat.card ↥(I.map (g : MulAut W).toMonoidHom) = Nat.card ↥J := by
    refine Nat.card_eq_of_bijective (fun a => ⟨β a, hβ1 a⟩) ⟨fun a b hab => ?_, fun b => ?_⟩
    · have h1 : β (a * b⁻¹) ∈ (⊥ : Subgroup W) := by
        rw [map_mul, map_inv, Subgroup.mem_bot, mul_inv_eq_one]
        exact congrArg Subtype.val hab
      have h2 := (hβ2 (a * b⁻¹)).mp h1
      rw [Subgroup.mem_bot] at h2
      exact mul_inv_eq_one.mp (Subtype.ext h2)
    · obtain ⟨a, ha⟩ := hβ3 b b.2
      rw [Subgroup.mem_bot, mul_inv_eq_one] at ha
      exact ⟨a, Subtype.ext ha⟩
  unfold rk
  rw [← hcard, Subgroup.card_map_of_injective g.injective]

private theorem g2_card_of_isG2 {L : Type} [Group L] {n : ℕ}
    (h : IsG2 L n) : Nat.card L = ordG2 (2 ^ n) := by
  exact CFSG.LocalAnalysis.EvenBN.G2.card_eq_ordG2_of_lieModel_G2 h

theorem not_isL2_of_shape {L : Type} [Group L] {n e : ℕ}
    (h : IsSz L n ∨ IsSp4 L n ∨ IsG2 L n ∨ IsU4 L n ∨ LieModel L .PSU 5 2 2) :
    ¬ IsL2 L e := by
  intro hL2
  rcases h with hSz | hSp4 | hG2 | hU4 | hU5
  · exact (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.three_dvd_card_of_isL2Even hL2)
  · have hcard : Nat.card L = CFSG.RankThree.PartOne.S12K.charTwoOrder .PSp 2 n := by
      rw [hSp4.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
      rfl
    have hcard2 : Nat.card L = ordA 1 (2 ^ e) := by
      rw [hL2.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
      rfl
    exact absurd (CFSG.RankThree.PartOne.S12K.rigid_L (LieModel.admissible hSp4)
      hL2.admissible.2.1 (hcard.symm.trans hcard2)).1 (by decide)
  · have hcard : Nat.card L = ordG2 (2 ^ n) := g2_card_of_isG2 hG2
    have hcard2 : Nat.card L = ordA 1 (2 ^ e) := by
      rw [hL2.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
      rfl
    exact (CFSG.RankThree.PartOne.S12K.ordG2_ne_ordA_one hG2.admissible.2.1
      hL2.admissible.2.1) (hcard.symm.trans hcard2)
  · have hcard : Nat.card L = CFSG.RankThree.PartOne.S12K.charTwoOrder .PSU 4 n := by
      rw [hU4.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0)]
      rfl
    have hcard2 : Nat.card L = ordA 1 (2 ^ e) := by
      rw [hL2.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
      rfl
    exact absurd (CFSG.RankThree.PartOne.S12K.rigid_L (LieModel.admissible hU4)
      hL2.admissible.2.1 (hcard.symm.trans hcard2)).1 (by decide)
  · have hcard : Nat.card L = CFSG.RankThree.PartOne.S12K.charTwoOrder .PSU 5 2 := by
      rw [hU5.card_eq_lieOrd (by norm_num : (5 : ℕ) ≠ 0)]
      rfl
    have hcard2 : Nat.card L = ordA 1 (2 ^ e) := by
      rw [hL2.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
      rfl
    exact absurd (CFSG.RankThree.PartOne.S12K.rigid_L (LieModel.admissible hU5)
      hL2.admissible.2.1 (hcard.symm.trans hcard2)).1 (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain
import CFSG.Quasithin.Background.B15P4Comp
import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

private theorem mk'_bot_injective : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']

private theorem iSupIndep_map_iff {G N : Type*} [Group G] [Group N] {f : G →* N}
    (hf : Function.Injective f) {ι : Type*} (t : ι → Subgroup G) :
    iSupIndep (fun i => (t i).map f) ↔ iSupIndep t := by
  simp only [iSupIndep_def, ← Subgroup.map_iSup, disjoint_iff, ← Subgroup.map_inf_eq _ _ f hf,
    Subgroup.map_eq_bot_iff_of_injective _ hf]

private theorem isDirSumOver_autQuot_bot_iff {S : Set (Subgroup (MulAut W))} :
    IsDirSumOver S (fun X => commV (autQuot X (⊥ : Subgroup W))) ↔ IsDirSumOver S commV := by
  have hmap : ∀ X : Subgroup (MulAut W), commV (autQuot X (⊥ : Subgroup W)) =
      (commV X).map (QuotientGroup.mk' (⊥ : Subgroup W)) :=
    fun X => (map_commV_eq_commV_autQuot X ⊥ (B5.Ln.stabSub_bot_le X)).symm
  simp only [IsDirSumOver, hmap, iSupIndep_map_iff mk'_bot_injective, ← Subgroup.map_iSup]
  rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (⊥ : Subgroup W)),
    (Subgroup.map_injective mk'_bot_injective).eq_iff]

theorem isDirSumOver_commV_of_autQuot_bot {S : Set (Subgroup (MulAut W))}
    (h : IsDirSumOver S (fun X => commV (autQuot X (⊥ : Subgroup W)))) : IsDirSumOver S commV :=
  isDirSumOver_autQuot_bot_iff.mp h

theorem mParam_autSub_autQuot_bot (Y : Subgroup (MulAut W)) (I : Subgroup W) :
    E3.mParam (autSub (autQuot Y (⊥ : Subgroup W)) (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) =
      E3.mParam (autSub Y I) := by
  let e : W ≃* W ⧸ (⊥ : Subgroup W) := (QuotientGroup.quotientBot (G := W)).symm
  have he : ∀ v : W, e v = (v : W ⧸ (⊥ : Subgroup W)) := QuotientGroup.quotientBot_symm_apply
  have hquot : ∀ g : stabSub (⊥ : Subgroup W),
      H.congrHom e (g : MulAut W) = quotHom (⊥ : Subgroup W) g := by
    intro g
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rw [H.congrHom_apply, quotHom_mk, ← he v, e.symm_apply_apply, he]
  have hY : autQuot Y (⊥ : Subgroup W) = Y.map (H.congrHom e) := by
    ext φ
    rw [mem_autQuot, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, hquot g⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, B5.Ln.stabSub_bot_le Y hy⟩, hy, (hquot ⟨y, _⟩).symm⟩
  have hU : ∀ v, v ∈ I ↔ e v ∈ I.map (QuotientGroup.mk' (⊥ : Subgroup W)) := fun v => by
    rw [he]
    exact (Subgroup.mem_map_iff_mem mk'_bot_injective).symm
  rw [hY, H.LU.autSub_map e Y hU, H.mParam_map_congrHom]

theorem rk_commV_autQuot_bot (L : Subgroup (MulAut W)) :
    rk ↥(commV (autQuot L (⊥ : Subgroup W))) = rk ↥(commV L) := by
  rw [← map_commV_eq_commV_autQuot L ⊥ (B5.Ln.stabSub_bot_le L)]
  unfold rk
  rw [Subgroup.card_map_of_injective mk'_bot_injective]

theorem rk_map_mk_bot (I : Subgroup W) :
    rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) = rk ↥I := by
  unfold rk
  rw [Subgroup.card_map_of_injective mk'_bot_injective]

private theorem iSup_conjSet_eq (L Y : Subgroup (MulAut W)) :
    (⨆ X ∈ conjSet L Y, X) = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun X hX => ?_
    obtain ⟨n, hn, rfl⟩ := hX
    exact le_iSup₂_of_le n hn le_rfl
  · exact iSup₂_le fun φ hφ =>
      le_iSup₂_of_le (L.map (MulAut.conj φ).toMonoidHom) ⟨φ, hφ, rfl⟩ le_rfl

private theorem normal_iSup_conj (L Y : Subgroup (MulAut W)) :
    ((⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have key : (⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom).map
      (MulAut.conj (g : MulAut W)).toMonoidHom ≤ ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
    simp only [Subgroup.map_iSup, Subgroup.map_map]
    exact iSup₂_le fun φ hφ => le_iSup₂_of_le ((g : MulAut W) * φ) (Y.mul_mem g.2 hφ) le_rfl
  have h := key ⟨n, hn, rfl⟩
  simpa [MulAut.conj_apply] using h

private theorem le_commV_of_mem_irrSet {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : J ∈ irrSet L) : J ≤ commV L := by
  rw [commV_eq_commSub]
  calc J = commSub J L := hJ.1.symm
    _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl

private theorem inf_fixV_eq_bot_of_mem_irrSet {L : Subgroup (MulAut W)}
    (hinf : commV L ⊓ fixV L = ⊥) {J : Subgroup W} (hJ : J ∈ irrSet L) : J ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff, ← hinf]
  exact inf_le_inf_right _ (le_commV_of_mem_irrSet hJ)

private theorem commV_inf_fixV_eq_bot [Finite W] {Y L : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (conjSet L Y) commV) : commV L ⊓ fixV L = ⊥ :=
  commV_inf_fixV_eq_bot_of_isDirSumOver hL hfix (isDirSumOver_autQuot_bot_iff.mpr hsum)

private theorem lem12_5 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) :
    IrrSpanTrans Y H ∧ (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤ := by
  have hLne : L ≠ ⊥ := B15P4.ne_bot_of_isComponentOf hL
  have hLH : L ≤ H := WeakClosure81.le_of_eq_biSup_conj hH
  have hHY : H ≤ Y := by
    rw [hH]
    refine iSup₂_le fun φ hφ => ?_
    rintro _ ⟨l, hl, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Y.mul_mem (Y.mul_mem hφ (hL.1 hl)) (Y.inv_mem hφ)
  have hHn : (H.subgroupOf Y).Normal := by
    rw [hH]
    exact normal_iSup_conj L Y
  exact (WeakClosure81.w4Lem12_5_holds W hW Y hO2
    (isBasicModule_of_isIrrOn (fun h => hLne (le_bot_iff.mp (h ▸ hL.1))) hirr) H
    (fun h => hLne (le_bot_iff.mp (h ▸ hLH))) hHY hHn).2 L hL hH

private theorem mem_irrSet_of_eq_biSup_conj [Finite W] {Y L H : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    (hsum : IsDirSumOver (conjSet L Y) commV)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) {I : Subgroup W} (hI : I ∈ irrSet L) :
    I ∈ irrSet H := by
  have hsum' := isDirSumOver_autQuot_bot_iff.mpr hsum
  have hLH : L ≤ H := WeakClosure81.le_of_eq_biSup_conj hH
  have hLmem : L ∈ conjSet L Y := ⟨1, Y.one_mem, by ext x; simp⟩
  have hIc : I ≤ commV L := le_commV_of_mem_irrSet hI
  have hHI : H ≤ stabSub I := by
    rw [hH]
    refine iSup₂_le fun φ hφ => B1.le_stabSub_of_invariant fun x hx u hu => ?_
    by_cases hX : L.map (MulAut.conj φ).toMonoidHom = L
    · rw [hX] at hx
      exact WeakClosure81.stableUnder_of_mem_irrSet hI x hx u hu
    · rw [fix_commV_of_mem_conjSet_of_ne hL hsum' ⟨φ, hφ, rfl⟩ hLmem hX x hx u (hIc hu)]
      exact hu
  have hstab : StableUnder H I := fun h hh u hu => (hHI hh u).2 hu
  have hIL : I ⊓ fixV L = ⊥ :=
    inf_fixV_eq_bot_of_mem_irrSet (commV_inf_fixV_eq_bot hL hfix hsum) hI
  have hIH : I ⊓ fixV H = ⊥ := by
    rw [eq_bot_iff, ← hIL]
    exact inf_le_inf_left I fun v hv x hx => hv x (hLH hx)
  refine ⟨le_antisymm ((Subgroup.closure_le _).mpr ?_)
    (hI.1.symm.le.trans (commSub_mono le_rfl hLH)), ?_⟩
  · rintro _ ⟨h, hh, u, hu, rfl⟩
    exact I.mul_mem (hstab h hh u hu) (I.inv_mem hu)
  · rw [hIH]
    refine ⟨bot_lt_iff_ne_bot.mpr (WeakClosure81.ne_bot_of_mem_irrSet hI), hstab,
      fun h _ u hu => ?_, fun J hJ _ hJI => ?_⟩
    · rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · have h := hI.2.2.2.2 J (fun x hx => hJ x (hLH hx)) (by rw [hIL]; exact bot_le) hJI
      rwa [hIL] at h

private theorem secIsoOn_mono {X K : Subgroup (MulAut W)} (hKX : K ≤ X) {A A₀ B B₀ : Subgroup W}
    (h : SecIsoOn X A A₀ B B₀) : SecIsoOn K A A₀ B B₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, β, hβ1, hβ2, hβ3, hβ4⟩ := h
  exact ⟨h1, h2, fun x hx => h3 x (hKX hx), fun x hx => h4 x (hKX hx),
    fun x hx => h5 x (hKX hx), fun x hx => h6 x (hKX hx), β, hβ1, hβ2, hβ3,
    fun x hx => hβ4 x (hKX hx)⟩

private theorem sSupIndep_insert_of_disjoint {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {s : Set α} {a : α} (hs : sSupIndep s) (ha : a ∉ s) (hd : Disjoint a (sSup s)) :
    sSupIndep (insert a s) := by
  intro b hb
  rcases hb with rfl | hb
  · rwa [Set.insert_sdiff_of_mem s (Set.mem_singleton b), Set.diff_singleton_eq_self ha]
  · have hba : a ∉ ({b} : Set α) := fun h => ha (Set.mem_singleton_iff.mp h ▸ hb)
    rw [Set.insert_sdiff_of_notMem s hba, sSup_insert]
    have h2 : Disjoint (b ⊔ sSup (s \ {b})) a :=
      (hd.mono_right (sup_le (le_sSup hb) (sSup_le_sSup Set.diff_subset))).symm
    have h := (hs hb).disjoint_sup_right_of_disjoint_sup_left h2
    rwa [sup_comm] at h

theorem commV_eq_iSup_irrSet [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) (hsum : IsDirSumOver (conjSet L Y) commV) :
    commV L = ⨆ J ∈ irrSet L, J := by
  have hinf := commV_inf_fixV_eq_bot hL hfix hsum
  have htop := (lem12_5 hW hO2 hirr hL rfl).2
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

theorem mem_normalizer_of_mem_stabSub {Y L : Subgroup (MulAut W)}
    (hsum : IsDirSumOver (conjSet L Y) commV)
    {J : Subgroup W} (hJ : J ∈ irrSet L) {y : MulAut W} (hy : y ∈ Y) (hyJ : y ∈ stabSub J) :
    y ∈ normalizer (L : Set (MulAut W)) := by
  have hy0 : y ∈ stabSub (⊥ : Subgroup W) := B5.Ln.stabSub_bot_le Y hy
  have hstab : quotHom (⊥ : Subgroup W) ⟨y, hy0⟩ ∈
      stabSub (J.map (QuotientGroup.mk' (⊥ : Subgroup W))) := by
    refine mem_stabSub.mpr fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [quotHom_mk]
      change QuotientGroup.mk' (⊥ : Subgroup W) (y v) ∈ J.map (QuotientGroup.mk' ⊥) ↔
        QuotientGroup.mk' (⊥ : Subgroup W) v ∈ J.map (QuotientGroup.mk' ⊥)
      rw [Subgroup.mem_map_iff_mem mk'_bot_injective, Subgroup.mem_map_iff_mem mk'_bot_injective]
      exact hyJ v
  have hLy : conjAutSub y L = L := conjAutSub_eq_self_of_isDirSumOver (B5.Ln.stabSub_bot_le L)
    bot_le hJ (isDirSumOver_autQuot_bot_iff.mpr hsum) hy hy0 hstab
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : y * h * y⁻¹ ∈ conjAutSub y L := ⟨h, hh, rfl⟩
    rwa [hLy] at hmem
  · intro hh
    rw [← hLy] at hh
    obtain ⟨l, hl, hle⟩ := hh
    have hlh : l = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hle
      exact mul_left_cancel (mul_right_cancel hle)
    rwa [← hlh]

theorem exists_sSupIndep_irrSet [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) (hsum : IsDirSumOver (conjSet L Y) commV)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    ∃ s : Set (Subgroup W), I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s ∧ sSup s = commV L := by
  have hinf := commV_inf_fixV_eq_bot hL hfix hsum
  have : Finite (Subgroup W) :=
    Finite.of_injective (fun K : Subgroup W => (K : Set W)) SetLike.coe_injective
  obtain ⟨s, hs⟩ := (Set.toFinite
    {s : Set (Subgroup W) | I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s}).exists_maximal
    ⟨{I}, Set.mem_singleton I, Set.singleton_subset_iff.mpr hI, sSupIndep_singleton I⟩
  obtain ⟨hIs, hsL, hsind⟩ := hs.prop
  refine ⟨s, hIs, hsL, hsind, le_antisymm (sSup_le fun J hJ => le_commV_of_mem_irrSet (hsL hJ)) ?_⟩
  rw [commV_eq_iSup_irrSet hW hO2 hirr hL hfix hsum]
  refine iSup₂_le fun J hJ => ?_
  by_contra hJs
  have hstab : StableUnder L (sSup s) := by
    rw [sSup_eq_iSup]
    exact WeakClosure81.stableUnder_iSup fun K => WeakClosure81.stableUnder_iSup fun hK =>
      WeakClosure81.stableUnder_of_mem_irrSet (hsL hK)
  have hJinf : J ⊓ fixV L = ⊥ := inf_fixV_eq_bot_of_mem_irrSet hinf hJ
  rcases hJ.2.2.2.2 (J ⊓ sSup s)
      (WeakClosure81.stableUnder_inf (WeakClosure81.stableUnder_of_mem_irrSet hJ) hstab)
      (by rw [hJinf]; exact bot_le) inf_le_left with h | h
  · rw [hJinf] at h
    have hJnot : J ∉ s := fun hm => hJs (le_sSup hm)
    have hmem : insert J s ∈ {s : Set (Subgroup W) | I ∈ s ∧ s ⊆ irrSet L ∧ sSupIndep s} :=
      ⟨Set.mem_insert_of_mem J hIs, Set.insert_subset hJ hsL,
        sSupIndep_insert_of_disjoint hsind hJnot (disjoint_iff.mpr h)⟩
    exact hJnot (hs.2 hmem (Set.subset_insert J s) (Set.mem_insert J s))
  · exact hJs (by rw [← h]; exact inf_le_right)

theorem exists_secIsoOn_of_mem_irrSet [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) (hsum : IsDirSumOver (conjSet L Y) commV)
    {I J : Subgroup W} (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L) :
    ∃ g ∈ Y, SecIsoOn L (I.map (g : MulAut W).toMonoidHom) ⊥ J ⊥ := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (MulAut W), H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom :=
    ⟨_, rfl⟩
  have hfixH : fixV H = ⊥ := by
    rw [hH, ← iSup_conjSet_eq]
    exact hfix
  obtain ⟨g, hg, hsec⟩ := (lem12_5 hW hO2 hirr hL hH).1.2 I
    (mem_irrSet_of_eq_biSup_conj hL hfix hsum hH hI) J
    (mem_irrSet_of_eq_biSup_conj hL hfix hsum hH hJ)
  rw [hfixH, sup_bot_eq, sup_bot_eq] at hsec
  exact ⟨g, hg, secIsoOn_mono (WeakClosure81.le_of_eq_biSup_conj hH) hsec⟩

theorem rk_eq_of_mem_irrSet [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y)
    (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) (hsum : IsDirSumOver (conjSet L Y) commV)
    {I J : Subgroup W} (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L) : rk ↥J = rk ↥I := by
  obtain ⟨g, -, hsec⟩ := exists_secIsoOn_of_mem_irrSet hW hO2 hirr hL hfix hsum hI hJ
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

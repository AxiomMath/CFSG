module

public import CFSG.Quasithin.Background.FixVLatticeSup
public import CFSG.Quasithin.EmptyFaithful.S151cJ
public import CFSG.Quasithin.Background.D216Blocks
public import CFSG.Quasithin.Background.D2Z20
public import CFSG.Quasithin.Background.D216Group
public import CFSG.Quasithin.EmptyFaithful.S151cSetting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Blocks151c

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_biSup_le (I : Finset (Subgroup (MulAut V))) :
    commV (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, commV L :=
  CFSG.Quasithin.FixVLat.commV_biSup_le I

omit [Finite V] in
theorem le_stabSub_commV (L : Subgroup (MulAut V)) : L ≤ stabSub (commV L) := by
  intro g hg u
  constructor
  · intro hu
    have := mem_of_commV_le216 (le_rfl : commV L ≤ commV L) (L.inv_mem hg) hu
    simpa using this
  · exact mem_of_commV_le216 le_rfl hg

variable {X Tb Xc : Subgroup (MulAut V)}

theorem commV_Jhat_le_v0 (h : Setting151c X Tb Xc) : commV (Jhat X) ≤ commV (fittingOf (Jhat X)) := by
  have hcop := commV_fitting_sup_fixV h.sq h.o2
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨j, hj, v, rfl⟩
  have hv : v ∈ commV (fittingOf (Jhat X)) ⊔ fixV (fittingOf (Jhat X)) := by
    rw [hcop.1]; exact Subgroup.mem_top v
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  have h1 : j (a * c) * (a * c)⁻¹ = j a * a⁻¹ := by
    rw [map_mul, h.central c hc j hj]
    group
  rw [h1]
  exact Subgroup.mul_mem _ (v0_invariant hj ha) (Subgroup.inv_mem _ ha)

open Classical in
theorem suppData_block (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) :
    SuppData L (commV L)
      (fixV (fittingOf (Jhat X)) ⊔ ⨆ L' ∈ I.erase L, commV L') := by
  have hLJ : ∀ L' ∈ I, L' ≤ Jhat X := fun L' hL' =>
    hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L' hL'
  have hcop := commV_fitting_sup_fixV h.sq h.o2
  have hJV0 := commV_Jhat_le_v0 h
  have hLU : commV L ≤ commV (fittingOf (Jhat X)) := (commV_mono216 (hLJ L hL)).trans hJV0
  have hBV₀ : (⨆ L' ∈ I.erase L, commV L') ≤ commV (fittingOf (Jhat X)) :=
    iSup₂_le fun L' hL' => (commV_mono216 (hLJ L' (Finset.mem_of_mem_erase hL'))).trans hJV0
  have hsplit : (⨆ L' ∈ I, commV L') = commV L ⊔ ⨆ L' ∈ I.erase L, commV L' := by
    conv_lhs => rw [← Finset.insert_erase hL]
    rw [Finset.iSup_insert]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply eq_top_iff.mpr
    rw [← hcop.1]
    refine sup_le ?_ ?_
    · have h1 : commV (fittingOf (Jhat X)) ≤ commV (Jhat X) :=
        commV_mono216 (fittingOf_le _)
      have h2 : commV (Jhat X) ≤ ⨆ L' ∈ I, commV L' := by
        have := commV_biSup_le I
        rwa [← hI.sup_eq] at this
      rw [hsplit] at h2
      exact (h1.trans h2).trans (sup_le_sup_left le_sup_right _)
    · exact le_sup_of_le_right le_sup_left
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨c, hc, b, hb, hcb⟩ := Subgroup.mem_sup.mp hxW
    have hcV : c ∈ commV (fittingOf (Jhat X)) := by
      have : c = x * b⁻¹ := by rw [← hcb]; group
      rw [this]
      exact Subgroup.mul_mem _ (hLU hxU) (Subgroup.inv_mem _ (hBV₀ hb))
    have hc1 : c = 1 := by
      have : c ∈ commV (fittingOf (Jhat X)) ⊓ fixV (fittingOf (Jhat X)) := ⟨hcV, hc⟩
      rw [hcop.2] at this
      exact this
    have hxb : x = b := by rw [← hcb, hc1, one_mul]
    have : b ∈ commV L ⊓ ⨆ L' ∈ I.erase L, commV L' := ⟨hxb ▸ hxU, hb⟩
    rw [hI.indepV L hL] at this
    rw [hxb]
    exact this
  · exact le_stabSub_commV L
  · intro g hg w hw
    have hfix : fixV (fittingOf (Jhat X)) ⊔ (⨆ L' ∈ I.erase L, commV L') ≤ fixV L := by
      refine sup_le (fun c hc g' hg' => h.central c hc g' (hLJ L hL hg')) ?_
      refine iSup₂_le fun L' hL' => ?_
      exact hI.triv L' (Finset.mem_of_mem_erase hL') L hL (Finset.ne_of_mem_erase hL')
    exact hfix hw g hg

open Classical in
theorem Jhat_le_stabSub_block {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : Jhat X ≤ stabSub (commV L) := by
  rw [hI.sup_eq]
  refine iSup₂_le fun L' hL' => ?_
  by_cases hLL : L' = L
  · rw [hLL]; exact le_stabSub_commV L
  · intro g hg
    exact centSub_le_stabSub _ (fun w hw => hI.triv L hL L' hL' (Ne.symm hLL) hw g hg)

open Classical in
theorem autSub_Jhat_block {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : autSub (Jhat X) (commV L) = autSub L (commV L) := by
  have hLJ : L ≤ Jhat X := hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L hL
  apply le_antisymm
  · have hJS : Jhat X ≤ extAutSub (commV L) (autSub L (commV L)) := by
      rw [hI.sup_eq]
      refine iSup₂_le fun L' hL' g hg => ?_
      by_cases hLL : L' = L
      · subst hLL
        exact mem_extAutSub.mpr ⟨le_stabSub_commV L' hg,
          mem_autSub.mpr ⟨⟨g, le_stabSub_commV L' hg⟩, hg, rfl⟩⟩
      · have hfix : ∀ w ∈ commV L, g w = w := fun w hw =>
          hI.triv L hL L' hL' (Ne.symm hLL) hw g hg
        have hs : g ∈ stabSub (commV L) := centSub_le_stabSub _ hfix
        refine mem_extAutSub.mpr ⟨hs, ?_⟩
        have : resHom (commV L) ⟨g, hs⟩ = 1 := by
          ext u
          exact hfix u u.2
        rw [this]
        exact (autSub L (commV L)).one_mem
    rintro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨hs, hmem⟩ := mem_extAutSub.mp (hJS hg)
    exact hmem
  · exact autSub_mono hLJ _

theorem exists_rat_qhat (h : Setting151c X Tb Xc) : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ 2 := by
  have hne : qhatOf X ≠ ⊤ := ne_top_of_le_ne_top (by simp) h.qhat
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨r, hr.symm, ?_⟩
  have := h.qhat
  rw [← hr] at this
  have h2 : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := by simpa using this
  exact WithTop.coe_le_coe.mp h2

theorem Jhat_compat {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) :
    qhatOf (Jhat X) = (r : WithTop ℚ) ∧ Jhat (Jhat X) = Jhat X := by
  obtain ⟨A₀, hA₀⟩ := QhatStar_nonempty hr hr2
  exact ⟨qhatOf_eq_of_le216 hr hA₀ (le_Jhat hA₀) (Jhat_le X),
    Jhat_eq_of_gen216 hr hr2 (Q := QhatStar X) subset_rfl ⟨A₀, hA₀⟩ rfl⟩

theorem QhatStar_Jhat {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) :
    QhatStar (Jhat X) = QhatStar X := by
  obtain ⟨A₀, hA₀⟩ := QhatStar_nonempty hr hr2
  rw [QhatStar_of_le216 hr hr2 hA₀ (le_Jhat hA₀) (Jhat_le X)]
  ext A
  exact ⟨fun hA => hA.1, fun hA => ⟨hA, le_Jhat hA⟩⟩

open Classical in
theorem block_qhat {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2)
    {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)}
    (hL : L ∈ I) :
    QhatStar L = {A | A ∈ QhatStar X ∧ A ≤ L} ∧ qhatOf L = (r : WithTop ℚ) := by
  have hqs : QhatStar L = {A | A ∈ QhatStar X ∧ A ≤ L} := by
    rw [hI.qstar L hL, QhatStar_Jhat hr hr2]
  have hLJ : L ≤ Jhat X := hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L hL
  have hLne : L ≠ ⊥ := hI.ne_bot L hL
  have hne : (QhatStar L).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hLne
    have := (hI.indec L hL).1
    rw [this]
    unfold Jhat
    rw [hcon]
    simp
  obtain ⟨A₀, hA₀⟩ := hne
  rw [hqs] at hA₀
  exact ⟨hqs, qhatOf_eq_of_le216 hr hA₀.1 hA₀.2 (hLJ.trans (Jhat_le X))⟩

open Classical in
theorem block_normal_two (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) :
    ∀ A : Subgroup (MulAut V), A ≤ L → (∀ g ∈ L, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      IsPGroup 2 A → A = ⊥ := by
  intro A hAL hAnorm hA2
  have hLJ : ∀ L' ∈ I, L' ≤ Jhat X := fun L' hL' =>
    hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L' hL'
  have hJnorm : Jhat X ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
    rw [hI.sup_eq]
    refine iSup₂_le fun L' hL' g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro a
    by_cases hLL : L' = L
    · subst hLL
      refine ⟨hAnorm g hg a, fun hga => ?_⟩
      have := hAnorm g⁻¹ (L'.inv_mem hg) _ hga
      simpa [mul_assoc] using this
    · have hc : ∀ x ∈ A, g * x * g⁻¹ = x := by
        intro x hx
        have := hI.comm L hL L' hL' (Ne.symm hLL) x (hAL hx) g hg
        calc g * x * g⁻¹ = (g * x) * g⁻¹ := rfl
          _ = (x * g) * g⁻¹ := by rw [← this]
          _ = x := by group
      constructor
      · intro ha
        rw [hc a ha]; exact ha
      · intro hga
        have e : g⁻¹ * (g * a * g⁻¹) * g = g * a * g⁻¹ := by
          calc g⁻¹ * (g * a * g⁻¹) * g
              = g⁻¹ * (g * (g * a * g⁻¹) * g⁻¹) * g := by rw [hc _ hga]
            _ = g * a * g⁻¹ := by group
        have ha' : a = g * a * g⁻¹ := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = g * a * g⁻¹ := e
        rw [ha']
        exact hga
  have hle : A ≤ pCoreOf 2 (Jhat X) :=
    le_pCoreOf_of_le_normalizer 2 (hAL.trans (hLJ L hL)) hJnorm hA2
  rw [pCoreOf_Jhat_eq_bot h.o2, le_bot_iff] at hle
  exact hle

open Classical in
theorem block_d217hyp (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : D217Hyp (autSub L (commV L)) r := by
  have hs := suppData_block h hI hL
  have hLJ : L ≤ Jhat X := hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L hL
  have hLX : L ≤ X := hLJ.trans (Jhat_le X)
  have hLsolv : Group.IsSolvable ↥L := by
    have := h.solv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLX)
  have hXLsolv : Group.IsSolvable ↥(autSub L (commV L)) := hs.isSolvable_autSub hLsolv
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have ho2 : pCoreOf 2 (autSub L (commV L)) = ⊥ := by
    have hQX : pCoreOf 2 (autSub L (commV L)) ≤ autSub L (commV L) := pCoreOf_le 2 _
    refine hs.eq_bot_of_normal_two (block_normal_two h hI hL) hQX ?_ (pCoreOf_isPGroup 2 _)
    intro φ hφ q hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (autSub L (commV L)) hφ) q).mp hq
  have hbq := block_qhat hr hr2 hI hL
  have hodd : Odd (Nat.card (fittingOf (autSub L (commV L)))) := odd_card_fittingOf ho2
  have hfixbot : fixV (fittingOf (autSub L (commV L))) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    have hstab := Jhat_le_stabSub_block hI hL
    have hFL : autSub (fittingOf (Jhat X)) (commV L) ≤ fittingOf (autSub L (commV L)) := by
      have := fittingOf_autSub_le hstab
      rwa [autSub_Jhat_block hI hL] at this
    have hu' : (u : V) ∈ fixV (fittingOf (Jhat X)) := by
      intro f hf
      have hfs : f ∈ stabSub (commV L) := hstab ((fittingOf_le _) hf)
      have := hu (resHom (commV L) ⟨f, hfs⟩)
        (hFL (mem_autSub.mpr ⟨⟨f, hfs⟩, hf, rfl⟩))
      exact congrArg (fun w : ↥(commV L) => (w : V)) this
    have hV0 : (u : V) ∈ commV (fittingOf (Jhat X)) := by
      have hLU : commV L ≤ commV (fittingOf (Jhat X)) :=
        (commV_mono216 hLJ).trans (commV_Jhat_le_v0 h)
      exact hLU u.2
    have hcop := commV_fitting_sup_fixV h.sq h.o2
    have : (u : V) ∈ commV (fittingOf (Jhat X)) ⊓ fixV (fittingOf (Jhat X)) := ⟨hV0, hu'⟩
    rw [hcop.2] at this
    exact Subtype.ext this
  have hcomm : commV (fittingOf (autSub L (commV L))) = ⊤ := by
    have := coprime_decomp hodd hUsq (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
    rw [top_inf_eq, hfixbot, sup_bot_eq] at this
    exact (commV_eq_commSub _).trans this.1
  have hsqtk : IsQuotientOfSQTKTC ↥(autSub L (commV L)) :=
    isQuotientOfSQTK_of_mulEquiv hs.restrictEquiv (isQuotientOfSQTK_of_le hLX h.sqtk)
  exact ⟨hs.qhatOf_eq.trans hbq.2, hr2, by rw [hs.Jhat_autSub, ← (hI.indec L hL).1], hcomm,
    hs.isIndecomposablePair_autSub (hI.indec L hL),
    centralizer_fittingOf_le_of_solvable hXLsolv, ho2, hsqtk⟩

open Classical in
theorem block_d217 (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) :
    QhatStar (autSub L (commV L)) = sylow2Of (autSub L (commV L)) ∧
      D217Concl (autSub L (commV L)) r := by
  have hH := block_d217hyp h hr hr2 hI hL
  exact d217 ↥(commV L) (fun v => Subtype.ext (h.sq v)) (autSub L (commV L)) r hH.qhat hH.le_two
    hH.jhat hH.comm_fitting hH.indecomposable hH.fstar hH.o2 hH.sqtk

end Blocks151c

end CFSG.Quasithin

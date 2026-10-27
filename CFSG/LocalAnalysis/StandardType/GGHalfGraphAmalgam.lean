module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphTheta
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Universal.RootData
public import CFSG.LieType.Steinberg.Presentation
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LargeExtraspecial.A2ModSLModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits

private theorem ggHalfGraphAmalgam_exists_block (m : GGHalfE6Model) (hm : m.Good)
    (J : Finset (Fin (Tag.rank .E6))) (hJ : J.card ≤ 2) :
    ∃ b : GGHalfBlk, ∀ i ∈ J, GGHalfE6Model.simpleRoot i ∈ m.Y b := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := hm
  have hcard : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 := by omega
  rcases hcard with h | h | h
  · have hJ0 : J = ∅ := Finset.card_eq_zero.mp h
    exact ⟨.L, by simp [hJ0]⟩
  · obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨b, hb, -⟩ := i k k
    exact ⟨b, by simpa using hb⟩
  · obtain ⟨k, l, hkl, rfl⟩ := Finset.card_eq_two.mp h
    obtain ⟨b, hb, hb'⟩ := i k l
    refine ⟨b, ?_⟩
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hb
    · exact hb'

private noncomputable def ggHalfGraphAmalgam_block (m : GGHalfE6Model) (hm : m.Good)
    (J : Finset (Fin (Tag.rank .E6))) (hJ : J.card ≤ 2) : GGHalfBlk :=
  Classical.choose (ggHalfGraphAmalgam_exists_block m hm J hJ)

private theorem ggHalfGraphAmalgam_block_spec (m : GGHalfE6Model) (hm : m.Good)
    (J : Finset (Fin (Tag.rank .E6))) (hJ : J.card ≤ 2) :
    ∀ i ∈ J, GGHalfE6Model.simpleRoot i ∈ m.Y (ggHalfGraphAmalgam_block m hm J hJ) :=
  Classical.choose_spec (ggHalfGraphAmalgam_exists_block m hm J hJ)

private theorem ggHalfGraphAmalgam_frameOK (m : GGHalfE6Model) (hm : m.Good)
    (b : GGHalfBlk) : m.FrameOK b := by
  obtain ⟨hL, hK, hM, -⟩ := hm
  cases b with
  | L => exact hL
  | K => exact hK
  | M => exact hM

private theorem ggHalfGraphAmalgam_neg_mem_Y (m : GGHalfE6Model) (b : GGHalfBlk)
    (hb : m.FrameOK b) {r : GGE6Root} (hr : r ∈ m.Y b) : -r ∈ m.Y b := by
  simp only [GGHalfE6Model.Y, Set.mem_setOf_eq] at hr ⊢
  obtain ⟨c, d, hc, hd, hcd, hframe⟩ := hr
  exact ⟨d, c, hd, hc, hcd.symm, by rw [hb.2.1 c d hc hd hcd, hframe]⟩

private theorem ggHalfGraphAmalgam_lab_surj (b : GGHalfBlk) {c : Fin 8} (hc : b.Lab c) :
    ∃ c' : Fin 6, b.lab c' = c := by
  cases b with
  | L =>
    exact ⟨⟨c.val, by simpa [GGHalfBlk.Lab] using hc⟩,
      Fin.ext (by simp [GGHalfBlk.lab, GGHalfBlk.off])⟩
  | K =>
    have hc' : 2 ≤ c.val := by simpa only [GGHalfBlk.Lab] using hc
    refine ⟨⟨c.val - 2, by omega⟩, Fin.ext ?_⟩
    show 2 + (c.val - 2) = c.val
    omega
  | M =>
    have hc' : 2 ≤ c.val := by simpa only [GGHalfBlk.Lab] using hc
    refine ⟨⟨c.val - 2, by omega⟩, Fin.ext ?_⟩
    show 2 + (c.val - 2) = c.val
    omega

private theorem ggHalfGraphAmalgam_exists_labels (m : GGHalfE6Model) (b : GGHalfBlk)
    {r : GGE6Root} (hr : r ∈ m.Y b) :
    ∃ c d : Fin 6, c ≠ d ∧ m.frame b (b.lab c) (b.lab d) = r := by
  simp only [GGHalfE6Model.Y, Set.mem_setOf_eq] at hr
  obtain ⟨c, d, hc, hd, hcd, hframe⟩ := hr
  obtain ⟨c', hc'⟩ := ggHalfGraphAmalgam_lab_surj b hc
  obtain ⟨d', hd'⟩ := ggHalfGraphAmalgam_lab_surj b hd
  refine ⟨c', d', ?_, ?_⟩
  · intro h
    exact hcd (by rw [← hc', ← hd', h])
  · rw [hc', hd', hframe]

private noncomputable def ggHalfGraphAmalgam_theta
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b) :
    SpecialLinearGroup (Fin 6) F2 →* GGE6Two :=
  Classical.choose (m.exists_theta b hb)

private theorem ggHalfGraphAmalgam_theta_injective
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b) :
    Function.Injective (ggHalfGraphAmalgam_theta m b hb) :=
  (Classical.choose_spec (m.exists_theta b hb)).1

private theorem ggHalfGraphAmalgam_theta_slE
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b) (c d : Fin 6) (hcd : c ≠ d) :
    ggHalfGraphAmalgam_theta m b hb (slE c d) =
      ggE6x (m.frame b (b.lab c) (b.lab d)) :=
  (Classical.choose_spec (m.exists_theta b hb)).2 c d hcd

private noncomputable def ggHalfGraphAmalgam_thetaInv
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b) :
    (ggHalfGraphAmalgam_theta m b hb).range →* SpecialLinearGroup (Fin 6) F2 :=
  ((MonoidHom.ofInjective (ggHalfGraphAmalgam_theta_injective m b hb)).symm).toMonoidHom

private theorem ggHalfGraphAmalgam_thetaInv_theta
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b)
    (y : SpecialLinearGroup (Fin 6) F2) :
    ggHalfGraphAmalgam_thetaInv m b hb
      ⟨ggHalfGraphAmalgam_theta m b hb y,
        (MonoidHom.mem_range).mpr ⟨y, rfl⟩⟩ = y := by
  apply (MonoidHom.ofInjective (ggHalfGraphAmalgam_theta_injective m b hb)).injective
  change (MonoidHom.ofInjective (ggHalfGraphAmalgam_theta_injective m b hb))
      ((MonoidHom.ofInjective (ggHalfGraphAmalgam_theta_injective m b hb)).symm _) =
    (MonoidHom.ofInjective (ggHalfGraphAmalgam_theta_injective m b hb)) y
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext rfl

private theorem ggHalfGraphAmalgam_rootGroup_le_theta
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b)
    {γ : GGE6Root} (hγ : γ ∈ m.Y b) :
    (e6Datum (GaloisField 2 1)).rootGroup γ ≤ (ggHalfGraphAmalgam_theta m b hb).range := by
  intro x hx
  obtain ⟨c, rfl⟩ := (Minuscule.MinData.Valid.mem_rootGroup (hV := e6Data_valid)
    (k := GaloisField 2 1) (γ := γ)).mp hx
  have hF2 : Nat.card F2 = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  rcases CFSG.LargeExtraspecial.A2Mod.eq_zero_or_eq_one_of_card_two hF2 c with hc | hc
  · rw [hc, Minuscule.MinData.Valid.xm_zero (hV := e6Data_valid) (k := GaloisField 2 1) γ]
    exact Subgroup.one_mem _
  · rw [hc]
    obtain ⟨c', d', hcd, hframe⟩ := ggHalfGraphAmalgam_exists_labels m b hγ
    refine ⟨slE c' d', ?_⟩
    rw [ggHalfGraphAmalgam_theta_slE m b hb c' d' hcd, hframe]
    rfl

private theorem ggHalfGraphAmalgam_leviAmalgam_le_theta
    (m : GGHalfE6Model) (hm : m.Good) (b : GGHalfBlk) (hb : m.FrameOK b)
    (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2})
    (hJ : ∀ i ∈ J.1, GGHalfE6Model.simpleRoot i ∈ m.Y b) :
    (e6Datum (GaloisField 2 1)).leviAmalgam J ≤ (ggHalfGraphAmalgam_theta m b hb).range := by
  simp only [CFSG.LieType.Universal.UniversalRootDatum.leviAmalgam,
    CFSG.LieType.CurtisTits.levi, CFSG.LieType.CurtisTits.rankOne]
  refine iSup_le fun i => iSup_le fun hi => ?_
  refine sup_le ?_ ?_
  · exact ggHalfGraphAmalgam_rootGroup_le_theta m b hb (hJ i hi)
  · exact ggHalfGraphAmalgam_rootGroup_le_theta m b hb
      (ggHalfGraphAmalgam_neg_mem_Y m b hb (hJ i hi))

private theorem ggHalfGraphAmalgam_rootGroup_eq_closure
    (γ : GGE6Root) :
    (e6Datum (GaloisField 2 1)).rootGroup γ =
      Subgroup.closure ({ggE6x γ} : Set GGE6Two) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := (Minuscule.MinData.Valid.mem_rootGroup (hV := e6Data_valid)
      (k := GaloisField 2 1) (γ := γ)).mp hx
    have hF2 : Nat.card F2 = 2 := by
      rw [GaloisField.card 2 1 (by norm_num), pow_one]
    rcases CFSG.LargeExtraspecial.A2Mod.eq_zero_or_eq_one_of_card_two hF2 c with hc | hc
    · rw [hc, Minuscule.MinData.Valid.xm_zero (hV := e6Data_valid) (k := GaloisField 2 1) γ]
      exact Subgroup.one_mem _
    · rw [hc]
      exact Subgroup.subset_closure rfl
  · rw [Subgroup.closure_le]
    rintro x (rfl : x = ggE6x γ)
    exact Minuscule.MinData.Valid.xm_mem_rootGroup (hV := e6Data_valid)
      (k := GaloisField 2 1) γ 1

private noncomputable def ggHalfGraphAmalgam_blockHom
    {G : Type} [Group G] (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b)
    (Φb : SpecialLinearGroup (Fin 6) F2 →* G) (K : Subgroup GGE6Two)
    (hK : K ≤ (ggHalfGraphAmalgam_theta m b hb).range) : K →* G :=
  Φb.comp ((ggHalfGraphAmalgam_thetaInv m b hb).comp (Subgroup.inclusion hK))

private theorem ggHalfGraphAmalgam_blockHom_apply
    {G : Type} [Group G] (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b)
    (Φb : SpecialLinearGroup (Fin 6) F2 →* G) {K : Subgroup GGE6Two}
    (hK : K ≤ (ggHalfGraphAmalgam_theta m b hb).range)
    {x : GGE6Two} (hx : x ∈ K) {y : SpecialLinearGroup (Fin 6) F2}
    (hy : ggHalfGraphAmalgam_theta m b hb y = x) :
    ggHalfGraphAmalgam_blockHom m b hb Φb K hK ⟨x, hx⟩ = Φb y := by
  change Φb (ggHalfGraphAmalgam_thetaInv m b hb (Subgroup.inclusion hK ⟨x, hx⟩)) = Φb y
  have h1 : (Subgroup.inclusion hK ⟨x, hx⟩ : (ggHalfGraphAmalgam_theta m b hb).range) =
      ⟨ggHalfGraphAmalgam_theta m b hb y,
        (MonoidHom.mem_range).mpr ⟨y, rfl⟩⟩ := Subtype.ext hy.symm
  rw [h1, ggHalfGraphAmalgam_thetaInv_theta]

private noncomputable def ggHalfGraphAmalgam_phi
    {G : Type} [Group G] (m : GGHalfE6Model) (hm : m.Good)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) :
    (e6Datum (GaloisField 2 1)).leviAmalgam J →* G :=
  ggHalfGraphAmalgam_blockHom m (ggHalfGraphAmalgam_block m hm J.1 J.2)
    (ggHalfGraphAmalgam_frameOK m hm (ggHalfGraphAmalgam_block m hm J.1 J.2))
    (Φ (ggHalfGraphAmalgam_block m hm J.1 J.2))
    ((e6Datum (GaloisField 2 1)).leviAmalgam J)
    (ggHalfGraphAmalgam_leviAmalgam_le_theta m hm _ _ J
      (ggHalfGraphAmalgam_block_spec m hm J.1 J.2))

private theorem ggHalfGraphAmalgam_phi_apply
    {G : Type} [Group G] (m : GGHalfE6Model) (hm : m.Good)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2})
    {x : GGE6Two} (hx : x ∈ (e6Datum (GaloisField 2 1)).leviAmalgam J)
    {y : SpecialLinearGroup (Fin 6) F2}
    (hy : ggHalfGraphAmalgam_theta m (ggHalfGraphAmalgam_block m hm J.1 J.2)
      (ggHalfGraphAmalgam_frameOK m hm (ggHalfGraphAmalgam_block m hm J.1 J.2)) y = x) :
    ggHalfGraphAmalgam_phi m hm Φ J ⟨x, hx⟩ =
      Φ (ggHalfGraphAmalgam_block m hm J.1 J.2) y := by
  unfold ggHalfGraphAmalgam_phi
  exact ggHalfGraphAmalgam_blockHom_apply m _ _ _ _ hx hy

private theorem ggHalfGraphAmalgam_phi_gen
    {G : Type} [Group G] (m : GGHalfE6Model) (hm : m.Good)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (hΦ : ∀ (b b' : GGHalfBlk) (c d c' d' : Fin 6), c ≠ d → c' ≠ d' →
      m.frame b (b.lab c) (b.lab d) = m.frame b' (b'.lab c') (b'.lab d') →
      Φ b (slE c d) = Φ b' (slE c' d'))
    (I J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) (hIJ : I ≤ J)
    {γ : GGE6Root} (hγI : γ ∈ m.Y (ggHalfGraphAmalgam_block m hm I.1 I.2))
    (hγJ : γ ∈ m.Y (ggHalfGraphAmalgam_block m hm J.1 J.2))
    (hyK : ggE6x γ ∈ (e6Datum (GaloisField 2 1)).leviAmalgam I) :
    ggHalfGraphAmalgam_phi m hm Φ I ⟨ggE6x γ, hyK⟩ =
      ggHalfGraphAmalgam_phi m hm Φ J
        ⟨ggE6x γ, CFSG.LieType.CurtisTits.levi_mono
          (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hyK⟩ := by
  obtain ⟨cI, dI, hcdI, hfrI⟩ := ggHalfGraphAmalgam_exists_labels m _ hγI
  obtain ⟨cJ, dJ, hcdJ, hfrJ⟩ := ggHalfGraphAmalgam_exists_labels m _ hγJ
  have eI : ggHalfGraphAmalgam_phi m hm Φ I ⟨ggE6x γ, hyK⟩ =
      Φ (ggHalfGraphAmalgam_block m hm I.1 I.2) (slE cI dI) := by
    apply ggHalfGraphAmalgam_phi_apply
    rw [ggHalfGraphAmalgam_theta_slE m _ _ cI dI hcdI, hfrI]
  have eJ : ggHalfGraphAmalgam_phi m hm Φ J
      ⟨ggE6x γ, CFSG.LieType.CurtisTits.levi_mono
        (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hyK⟩ =
      Φ (ggHalfGraphAmalgam_block m hm J.1 J.2) (slE cJ dJ) := by
    apply ggHalfGraphAmalgam_phi_apply
    rw [ggHalfGraphAmalgam_theta_slE m _ _ cJ dJ hcdJ, hfrJ]
  rw [eI, eJ]
  exact hΦ _ _ cI dI cJ dJ hcdI hcdJ (by rw [hfrI, hfrJ])

private theorem ggHalfGraphAmalgam_isCompatible
    {G : Type} [Group G] (m : GGHalfE6Model) (hm : m.Good)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (hΦ : ∀ (b b' : GGHalfBlk) (c d c' d' : Fin 6), c ≠ d → c' ≠ d' →
      m.frame b (b.lab c) (b.lab d) = m.frame b' (b'.lab c') (b'.lab d') →
      Φ b (slE c d) = Φ b' (slE c' d')) :
    IsCompatible (e6Datum (GaloisField 2 1)).leviAmalgam (ggHalfGraphAmalgam_phi m hm Φ) := by
  intro I J hIJ x y hxy
  let T : Set GGE6Two := {z | ∃ i ∈ I.1,
    z = ggE6x (GGHalfE6Model.simpleRoot i) ∨ z = ggE6x (-GGHalfE6Model.simpleRoot i)}
  have hTK : T ⊆ (e6Datum (GaloisField 2 1)).leviAmalgam I := by
    rintro z ⟨i, hi, rfl | rfl⟩
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi (X := (e6Datum (GaloisField 2 1)).rootGroup)
        hi (Subgroup.mem_sup_left (Minuscule.MinData.Valid.xm_mem_rootGroup
          (hV := e6Data_valid) (k := GaloisField 2 1) (GGHalfE6Model.simpleRoot i) 1))
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi (X := (e6Datum (GaloisField 2 1)).rootGroup)
        hi (Subgroup.mem_sup_right (Minuscule.MinData.Valid.xm_mem_rootGroup
          (hV := e6Data_valid) (k := GaloisField 2 1) (-GGHalfE6Model.simpleRoot i) 1))
  have hTK' : Subgroup.closure T ≤ (e6Datum (GaloisField 2 1)).leviAmalgam I :=
    (Subgroup.closure_le _).mpr hTK
  have hKcl : (e6Datum (GaloisField 2 1)).leviAmalgam I ≤ Subgroup.closure T := by
    simp only [CFSG.LieType.Universal.UniversalRootDatum.leviAmalgam,
      CFSG.LieType.CurtisTits.levi, CFSG.LieType.CurtisTits.rankOne]
    refine iSup_le fun i => iSup_le fun hi => sup_le ?_ ?_
    · exact (le_of_eq (ggHalfGraphAmalgam_rootGroup_eq_closure
        (γ := GGHalfE6Model.simpleRoot i))).trans
        (Subgroup.closure_mono (by
          rintro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨i, hi, Or.inl rfl⟩))
    · exact (le_of_eq (ggHalfGraphAmalgam_rootGroup_eq_closure
        (γ := -GGHalfE6Model.simpleRoot i))).trans
        (Subgroup.closure_mono (by
          rintro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨i, hi, Or.inr rfl⟩))
  have hsub : ∀ z : (e6Datum (GaloisField 2 1)).leviAmalgam I,
      ggHalfGraphAmalgam_phi m hm Φ I z =
        ggHalfGraphAmalgam_phi m hm Φ J
          ⟨(z : GGE6Two), CFSG.LieType.CurtisTits.levi_mono
            (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ z.2⟩ := by
    intro z
    let p : ∀ w : GGE6Two, w ∈ Subgroup.closure T → Prop := fun w _ =>
      ∀ hw : w ∈ (e6Datum (GaloisField 2 1)).leviAmalgam I,
        ggHalfGraphAmalgam_phi m hm Φ I ⟨w, hw⟩ =
          ggHalfGraphAmalgam_phi m hm Φ J ⟨w, CFSG.LieType.CurtisTits.levi_mono
            (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hw⟩
    have hp : p z.1 (hKcl z.2) := by
      refine Subgroup.closure_induction (p := p) ?_ ?_ ?_ ?_ (hKcl z.2)
      · rintro w ⟨i, hi, rfl | rfl⟩ hw
        · exact ggHalfGraphAmalgam_phi_gen m hm Φ hΦ I J hIJ
            (ggHalfGraphAmalgam_block_spec m hm I.1 I.2 i hi)
            (ggHalfGraphAmalgam_block_spec m hm J.1 J.2 i (hIJ hi)) hw
        · exact ggHalfGraphAmalgam_phi_gen m hm Φ hΦ I J hIJ
            (ggHalfGraphAmalgam_neg_mem_Y m _ (ggHalfGraphAmalgam_frameOK m hm _)
              (ggHalfGraphAmalgam_block_spec m hm I.1 I.2 i hi))
            (ggHalfGraphAmalgam_neg_mem_Y m _ (ggHalfGraphAmalgam_frameOK m hm _)
              (ggHalfGraphAmalgam_block_spec m hm J.1 J.2 i (hIJ hi))) hw
      · intro hw
        have hI : (⟨(1 : GGE6Two), hw⟩ : (e6Datum (GaloisField 2 1)).leviAmalgam I) = 1 :=
          Subtype.ext rfl
        have hJ : (⟨(1 : GGE6Two), CFSG.LieType.CurtisTits.levi_mono
            (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hw⟩ :
            (e6Datum (GaloisField 2 1)).leviAmalgam J) = 1 := Subtype.ext rfl
        rw [hI, hJ, map_one, map_one]
      · intro a b ha hb ha' hb' hw
        have h1 : (⟨a * b, hw⟩ : (e6Datum (GaloisField 2 1)).leviAmalgam I) =
            ⟨a, hTK' ha⟩ * ⟨b, hTK' hb⟩ := Subtype.ext rfl
        have h2 : (⟨a * b, CFSG.LieType.CurtisTits.levi_mono
              (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hw⟩ :
              (e6Datum (GaloisField 2 1)).leviAmalgam J) =
            ⟨a, CFSG.LieType.CurtisTits.levi_mono
              (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ (hTK' ha)⟩ *
            ⟨b, CFSG.LieType.CurtisTits.levi_mono
              (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ (hTK' hb)⟩ :=
          Subtype.ext rfl
        rw [h1, h2, map_mul, map_mul, ha' (hTK' ha), hb' (hTK' hb)]
      · intro a ha ha' hw
        have h1 : (⟨a⁻¹, hw⟩ : (e6Datum (GaloisField 2 1)).leviAmalgam I) =
            (⟨a, hTK' ha⟩ : (e6Datum (GaloisField 2 1)).leviAmalgam I)⁻¹ :=
          Subtype.ext rfl
        have h2 : (⟨a⁻¹, CFSG.LieType.CurtisTits.levi_mono
              (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ hw⟩ :
              (e6Datum (GaloisField 2 1)).leviAmalgam J) =
            (⟨a, CFSG.LieType.CurtisTits.levi_mono
              (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ (hTK' ha)⟩ :
              (e6Datum (GaloisField 2 1)).leviAmalgam J)⁻¹ :=
          Subtype.ext rfl
        rw [h1, h2, map_inv, map_inv, ha' (hTK' ha)]
    exact hp z.2
  have hy : y = ⟨(x : GGE6Two), CFSG.LieType.CurtisTits.levi_mono
      (X := (e6Datum (GaloisField 2 1)).rootGroup) hIJ x.2⟩ := Subtype.ext hxy.symm
  rw [hy]
  exact hsub x

private theorem ggHalfGraphAmalgam_transvection_ne_one {c d : Fin 6} (hcd : c ≠ d) :
    SpecialLinearGroup.transvection hcd (1 : F2) ≠
      (1 : SpecialLinearGroup (Fin 6) F2) := by
  intro h
  have h2 : ((SpecialLinearGroup.transvection hcd (1 : F2) : SpecialLinearGroup (Fin 6) F2) :
      Matrix (Fin 6) (Fin 6) F2) c d = 1 := by
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply_same,
      Matrix.one_apply_ne hcd, zero_add]
  have h3 : ((1 : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) c d = 0 :=
    Matrix.one_apply_ne hcd
  rw [h, h3] at h2
  exact one_ne_zero h2.symm

private theorem ggHalfGraphAmalgam_slE_ne_one {c d : Fin 6} (hcd : c ≠ d) :
    slE c d ≠ (1 : SpecialLinearGroup (Fin 6) F2) := by
  rw [slE, dif_neg hcd]
  exact ggHalfGraphAmalgam_transvection_ne_one hcd

private theorem ggHalfGraphAmalgam_slInjective {X : Type} [Group X]
    (Ψ : SpecialLinearGroup (Fin 6) F2 →* X) (hnt : ∃ g, Ψ g ≠ 1) :
    Function.Injective Ψ := by
  have hF2 : Nat.card F2 = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have hq : IsQuasisimple (SpecialLinearGroup (Fin 6) F2) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 F2 (by norm_num)
  have hZ : Subgroup.center (SpecialLinearGroup (Fin 6) F2) = ⊥ :=
    CFSG.LargeExtraspecial.A2Mod.sl_center_eq_bot_of_card_two (n := 6) hF2
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq Ψ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff Ψ).mp (le_bot_iff.mp (h.trans (le_of_eq hZ)))
  · obtain ⟨g, hg⟩ := hnt
    exact absurd (Ψ.mem_ker.mp (h ▸ Subgroup.mem_top g)) hg

private theorem ggHalfGraphAmalgam_phi_injective_of_overlap
    {G : Type} [Group G] (m : GGHalfE6Model)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (hΦ : ∀ (b b' : GGHalfBlk) (c d c' d' : Fin 6), c ≠ d → c' ≠ d' →
      m.frame b (b.lab c) (b.lab d) = m.frame b' (b'.lab c') (b'.lab d') →
      Φ b (slE c d) = Φ b' (slE c' d'))
    (b b' : GGHalfBlk) (hL : Function.Injective (Φ b))
    {r : GGE6Root} (hrb : r ∈ m.Y b) (hrb' : r ∈ m.Y b') :
    Function.Injective (Φ b') := by
  apply ggHalfGraphAmalgam_slInjective
  obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphAmalgam_exists_labels m b hrb
  obtain ⟨c', d', hcd', hfr'⟩ := ggHalfGraphAmalgam_exists_labels m b' hrb'
  refine ⟨slE c' d', ?_⟩
  rw [← hΦ b b' c d c' d' hcd hcd' (by rw [hfr, hfr'])]
  exact fun h => ggHalfGraphAmalgam_slE_ne_one hcd (hL (by rw [h, map_one]))



private theorem ggHalfGraphAmalgam_Lab_L {a : Fin 8} (h : a.val < 6) : GGHalfBlk.Lab .L a := h

private theorem ggHalfGraphAmalgam_Lab_K {a : Fin 8} (h : 2 ≤ a.val) : GGHalfBlk.Lab .K a := h

private theorem ggHalfGraphAmalgam_Lab_M {a : Fin 8} (h : 2 ≤ a.val) : GGHalfBlk.Lab .M a := h

private theorem ggHalfGraphAmalgam_lab_mem (b : GGHalfBlk) (c : Fin 6) : b.Lab (b.lab c) := by
  cases b with
  | L => exact ggHalfGraphAmalgam_Lab_L (by simp [GGHalfBlk.lab, GGHalfBlk.off])
  | K => exact ggHalfGraphAmalgam_Lab_K (by simp [GGHalfBlk.lab, GGHalfBlk.off])
  | M => exact ggHalfGraphAmalgam_Lab_M (by simp [GGHalfBlk.lab, GGHalfBlk.off])

private theorem ggHalfGraphAmalgam_lab_ne (b : GGHalfBlk) {c d : Fin 6} (hcd : c ≠ d) :
    b.lab c ≠ b.lab d := by
  intro h
  apply hcd
  apply Fin.ext
  have h' := congrArg Fin.val h
  cases b <;> simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk] at h' <;> omega


private theorem ggHalfGraphAmalgam_ggE6x_mem_singleton
    (m : GGHalfE6Model) (i : Fin (Tag.rank .E6)) (s : Bool) :
    ggE6x (if s then GGHalfE6Model.simpleRoot i else -GGHalfE6Model.simpleRoot i) ∈
      (e6Datum (GaloisField 2 1)).leviAmalgam ⟨{i}, by simp⟩ := by
  haveI : NeZero (Tag.rank .E6) := ⟨by decide⟩
  refine CFSG.LieType.CurtisTits.rankOne_le_levi (X := (e6Datum (GaloisField 2 1)).rootGroup)
    (Finset.mem_singleton_self i) ?_
  cases s with
  | false =>
    exact Subgroup.mem_sup_right (Minuscule.MinData.Valid.xm_mem_rootGroup
      (hV := e6Data_valid) (k := GaloisField 2 1) (-GGHalfE6Model.simpleRoot i) 1)
  | true =>
    exact Subgroup.mem_sup_left (Minuscule.MinData.Valid.xm_mem_rootGroup
      (hV := e6Data_valid) (k := GaloisField 2 1) (GGHalfE6Model.simpleRoot i) 1)

theorem exists_e6_hom_of_frames
    {G : Type} [Group G] (m : GGHalfE6Model) (hm : m.Good)
    (Φ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G)
    (hΦ : ∀ (b b' : GGHalfBlk) (c d c' d' : Fin 6), c ≠ d → c' ≠ d' →
      m.frame b (b.lab c) (b.lab d) = m.frame b' (b'.lab c') (b'.lab d') →
      Φ b (slE c d) = Φ b' (slE c' d'))
    (hnt : ∃ c d : Fin 6, c ≠ d ∧ Φ .L (slE c d) ≠ 1) :
    ∃ φ : GGE6Two →* G, Function.Injective φ ∧
      ∀ (b : GGHalfBlk) (c d : Fin 6) (i : Fin (Tag.rank .E6)), c ≠ d →
        (m.frame b (b.lab c) (b.lab d) = GGHalfE6Model.simpleRoot i ∨
          m.frame b (b.lab c) (b.lab d) = -GGHalfE6Model.simpleRoot i) →
        φ (ggE6x (m.frame b (b.lab c) (b.lab d))) = Φ b (slE c d) := by
  haveI : NeZero (Tag.rank .E6) := ⟨by decide⟩
  have hΦL : Function.Injective (Φ .L) := by
    apply ggHalfGraphAmalgam_slInjective
    obtain ⟨c, d, hcd, hne⟩ := hnt
    exact ⟨slE c d, hne⟩
  have hmG : m.Good := hm
  obtain ⟨hFL, hFK, hFM, hPL, hPK, hPM, hOv, hWe, hpair, hDer⟩ := hm
  obtain ⟨hov1, hov2, hov3, hov4, hov5, hov6⟩ := hOv
  have hYL1 : m.frame .L 2 3 ∈ m.Y .L :=
    ⟨2, 3, ggHalfGraphAmalgam_Lab_L (by decide), ggHalfGraphAmalgam_Lab_L (by decide),
      by decide, rfl⟩
  have hYK : m.frame .L 2 3 ∈ m.Y .K := by
    have hmem : m.frame .L 2 3 ∈ m.Y .L ∩ m.Y .K := by
      rw [hov4]
      exact ⟨2, 3, by decide, by decide, by decide, by decide, by decide, rfl⟩
    exact hmem.2
  have hYL2 : m.frame .M 2 3 ∈ m.Y .L := by
    have hmem : m.frame .M 2 3 ∈ m.Y .L ∩ m.Y .M := by
      rw [hov5]
      exact ⟨2, 3, by decide, by decide, by decide, by decide, by decide, rfl⟩
    exact hmem.1
  have hYM : m.frame .M 2 3 ∈ m.Y .M :=
    ⟨2, 3, ggHalfGraphAmalgam_Lab_M (by decide), ggHalfGraphAmalgam_Lab_M (by decide),
      by decide, rfl⟩
  have hΦK : Function.Injective (Φ .K) :=
    ggHalfGraphAmalgam_phi_injective_of_overlap m Φ hΦ .L .K hΦL hYL1 hYK
  have hΦM : Function.Injective (Φ .M) :=
    ggHalfGraphAmalgam_phi_injective_of_overlap m Φ hΦ .L .M hΦL hYL2 hYM
  have hInj : ∀ b, Function.Injective (Φ b) := by
    intro b; cases b with
    | L => exact hΦL
    | K => exact hΦK
    | M => exact hΦM
  have hcompat := ggHalfGraphAmalgam_isCompatible m hmG Φ hΦ
  have hct := Minuscule.e6Datum_isCTGroupDatum (GaloisField 2 1)
  have hext := Minuscule.e6Datum_steinbergExtras (GaloisField 2 1)
  have hU : IsUniversalCompletion.{0, 0, 0} (e6Datum (GaloisField 2 1)).leviAmalgam :=
    (e6Datum (GaloisField 2 1)).isUniversalCompletion_of_steinbergPresentation hct
      (CFSG.LieType.Steinberg.steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, -⟩ := hU G (ggHalfGraphAmalgam_phi m hmG Φ) hcompat
  have hntψ : ∃ k, ψ k ≠ 1 := by
    let K0 : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} := ⟨{0}, by simp⟩
    have hb : (0 : Fin (Tag.rank .E6)) ∈ ({0} : Finset (Fin (Tag.rank .E6))) := by simp
    have hspec := ggHalfGraphAmalgam_block_spec m hmG K0.1 K0.2 0 hb
    obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphAmalgam_exists_labels m _ hspec
    have hmem : ggE6x (GGHalfE6Model.simpleRoot 0) ∈
        (e6Datum (GaloisField 2 1)).leviAmalgam K0 :=
      ggHalfGraphAmalgam_ggE6x_mem_singleton m 0 true
    have hval : ggHalfGraphAmalgam_phi m hmG Φ K0 ⟨ggE6x (GGHalfE6Model.simpleRoot 0), hmem⟩ =
        Φ (ggHalfGraphAmalgam_block m hmG K0.1 K0.2) (slE c d) := by
      apply ggHalfGraphAmalgam_phi_apply
      rw [ggHalfGraphAmalgam_theta_slE m _ _ c d hcd, hfr]
    have hne : Φ (ggHalfGraphAmalgam_block m hmG K0.1 K0.2) (slE c d) ≠ 1 :=
      fun h => ggHalfGraphAmalgam_slE_ne_one hcd (hInj _ (by rw [h, map_one]))
    refine ⟨ggE6x (GGHalfE6Model.simpleRoot 0), ?_⟩
    have h1 : ψ (ggE6x (GGHalfE6Model.simpleRoot 0)) =
        ggHalfGraphAmalgam_phi m hmG Φ K0 ⟨ggE6x (GGHalfE6Model.simpleRoot 0), hmem⟩ :=
      hψ K0 ⟨ggE6x (GGHalfE6Model.simpleRoot 0), hmem⟩
    rw [h1, hval]
    exact hne
  have hq : IsQuasisimple GGE6Two :=
    CFSG.LieType.CurtisTits.isQuasisimple_e6 (GaloisField 2 1)
  have hcenter : Subgroup.center GGE6Two = ⊥ := by
    have h1 := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (k := GaloisField 2 1)).1
    rw [GaloisField.card 2 1 (by norm_num), pow_one] at h1
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)
  have hker : ψ.ker = ⊥ := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq ψ.ker with h | h
    · exact le_bot_iff.mp (h.trans (le_of_eq hcenter))
    · obtain ⟨k, hk⟩ := hntψ
      exact absurd (ψ.mem_ker.mp (h ▸ Subgroup.mem_top k)) hk
  refine ⟨ψ, (MonoidHom.ker_eq_bot_iff ψ).mp hker, ?_⟩
  intro b c d i hcd hroot
  set γ : GGE6Root := m.frame b (b.lab c) (b.lab d) with hγdef
  let K0 : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} := ⟨{i}, by simp⟩
  have hγb : γ ∈ m.Y b :=
    ⟨b.lab c, b.lab d, ggHalfGraphAmalgam_lab_mem b c, ggHalfGraphAmalgam_lab_mem b d,
      ggHalfGraphAmalgam_lab_ne b hcd, rfl⟩
  have hbase := ggHalfGraphAmalgam_block_spec m hmG K0.1 K0.2 i (Finset.mem_singleton_self i)
  have hγi : γ ∈ m.Y (ggHalfGraphAmalgam_block m hmG K0.1 K0.2) := by
    rcases hroot with h | h
    · rw [h]; exact hbase
    · rw [h]
      exact ggHalfGraphAmalgam_neg_mem_Y m _ (ggHalfGraphAmalgam_frameOK m hmG _) hbase
  obtain ⟨c', d', hcd', hfr'⟩ := ggHalfGraphAmalgam_exists_labels m _ hγi
  have hmem : ggE6x γ ∈ (e6Datum (GaloisField 2 1)).leviAmalgam K0 := by
    rcases hroot with h | h
    · rw [h]; exact ggHalfGraphAmalgam_ggE6x_mem_singleton m i true
    · rw [h]; exact ggHalfGraphAmalgam_ggE6x_mem_singleton m i false
  have hval : ggHalfGraphAmalgam_phi m hmG Φ K0 ⟨ggE6x γ, hmem⟩ =
      Φ (ggHalfGraphAmalgam_block m hmG K0.1 K0.2) (slE c' d') := by
    apply ggHalfGraphAmalgam_phi_apply
    rw [ggHalfGraphAmalgam_theta_slE m _ _ c' d' hcd', hfr']
  have h1 : ψ (ggE6x γ) = ggHalfGraphAmalgam_phi m hmG Φ K0 ⟨ggE6x γ, hmem⟩ :=
    hψ K0 ⟨ggE6x γ, hmem⟩
  have h2 : Φ b (slE c d) = Φ (ggHalfGraphAmalgam_block m hmG K0.1 K0.2) (slE c' d') :=
    hΦ b _ c d c' d' hcd hcd' (by rw [hfr', ← hγdef])
  rw [h1, hval, h2]

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.B69Blk
public import CFSG.Quasithin.Background.B69SolvStruct
public import CFSG.Quasithin.Background.B69Conj
public import CFSG.Quasithin.Background.B69Stab

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def NatShape {V : Type} [CommGroup V] (T M A L : Subgroup (MulAut V)) (W : Subgroup V) :
    Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) ∧
    CFSG.QuasithinUnique.IsSylowTwoOf A L ∧
    M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))

@[expose] def AltShape {V : Type} [CommGroup V] (M A L : Subgroup (MulAut V)) (W : Subgroup V) :
    Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A),
    Function.Surjective π ∧
    (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
    L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
    (∃ i j : Fin (2 * k + 1), i ≠ j ∧
      A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) ∧
    ((M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
      (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
        (⟨0, by omega⟩ : Fin (2 * k + 1))).map π)

theorem compShape_iff {V : Type} [CommGroup V] {T M A L : Subgroup (MulAut V)} {W : Subgroup V} :
    CompShape T M A L W ↔ NatShape T M A L W ∨ AltShape M A L W := Iff.rfl

structure BlkCtx (X T M : Subgroup (MulAut V)) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  hP4 : AsB15Part4
  hctx : ShapeCtx X T M
  hO2 : pCoreOf 2 X = ⊥
  hact : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X →
    ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L
  hffJ : ffJ X ≤ ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), blk X L
  hG1 : ∀ A L : Subgroup (MulAut V), IsFFStarMin X A → CFSG.Open.IsComponentOf L X → ⁅L, A⁆ = L →
    AltShape M A L (commV L) → ∀ A' : Subgroup (MulAut V), IsFFStarMin X A' → ⁅L, A'⁆ = L →
      A' ≤ L ⊔ A

@[expose] def vSigma (X : Subgroup (MulAut V)) : Subgroup V :=
  ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), commV L

omit [Finite V] in
theorem commV_le_vSigma {X L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    commV L ≤ vSigma X :=
  le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X) => commV L)
    L hL le_rfl

omit [Finite V] in
theorem vSigma_invariant (X : Subgroup (MulAut V)) : ∀ g ∈ X, ∀ u ∈ vSigma X, g u ∈ vSigma X := by
  intro g hg u hu
  have : vSigma X ≤ (vSigma X).comap g.toMonoidHom := by
    refine iSup₂_le fun L hL w hw => ?_
    have h1 := map_mem_commV_conj (H := L) g w hw
    have hLg : CFSG.Open.IsComponentOf (B6.conjSub g L) X := B113.isComponentOf_conj hL hg
    exact commV_le_vSigma hLg h1
  exact this hu

variable {X T M : Subgroup (MulAut V)}

omit [Finite V] in
theorem centQuot_mono {U U' : Subgroup V} (h : U ≤ U') : centQuot U ≤ centQuot U' :=
  fun _ hg v => h (hg v)

theorem blk_inf_eq_bot (hB : BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) :
    blk X L ⊓ (⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L), blk X L') =
      ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  have hxX : x ∈ X := blk_le_X hL hx1
  have hxW : ∀ w ∈ commV L, x w = w := by
    have hle : (⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L),
        blk X L') ≤ centSub (commV L) :=
      iSup₂_le fun L' hL' => blk_le_centSub hB.hV hB.hP4 hB.hctx hL'.1 hL (hB.hact L hL) hL'.2
    exact fun w hw => hle hx2 w hw
  have hxU : ∀ u ∈ vSigma X, x u = u := by
    have hle : vSigma X ≤ MonoidHom.eqLocus x.toMonoidHom (MonoidHom.id V) := by
      refine iSup₂_le fun L'' hL'' w hw => ?_
      by_cases hLL : L'' = L
      · subst hLL
        exact hxW w hw
      · exact blk_le_centSub hB.hV hB.hP4 hB.hctx hL hL'' (hB.hact L'' hL'') (Ne.symm hLL) hx1 w hw
    exact fun u hu => hle hu
  have hxQ : ∀ v : V, x v * v⁻¹ ∈ vSigma X := fun v =>
    centQuot_mono (commV_le_vSigma hL) (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL) hx1) v
  exact eq_one_of_stab hB.hV hB.hO2 (vSigma_invariant X) hxX hxU hxQ

omit [Finite V] in
theorem ffJ_eq_blk (hB : BlkCtx X T M) :
    ffJ X = ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), blk X L :=
  le_antisymm hB.hffJ (iSup₂_le fun L hL => blk_le_ffJ hL (hB.hact L hL))

theorem mem_fixV_ffJ (hB : BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) {a : V} (ha : a ∈ commV L) (haL : ∀ y ∈ blk X L, y a = a) :
    a ∈ fixV (ffJ X) := by
  rw [ffJ_eq_blk hB]
  have hle : (⨆ (L'' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L'' X), blk X L'') ≤
      MulAction.stabilizer (MulAut V) a := by
    refine iSup₂_le fun L'' hL'' y hy => ?_
    rw [MulAction.mem_stabilizer_iff]
    by_cases hLL : L'' = L
    · subst hLL
      exact haL y hy
    · exact blk_le_centSub hB.hV hB.hP4 hB.hctx hL'' hL (hB.hact L hL) hLL hy a ha
  exact fun y hy => hle hy

theorem commV_inf_fixV_ffJ (hB : BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) :
    commV L ⊓ fixV (ffJ X) = commV L ⊓ fixV (blk X L) := by
  apply le_antisymm
  · rintro a ⟨ha1, ha2⟩
    exact ⟨ha1, fun y hy => ha2 y (blk_le_ffJ hL (hB.hact L hL) hy)⟩
  · rintro a ⟨ha1, ha2⟩
    exact ⟨ha1, mem_fixV_ffJ hB hL ha1 ha2⟩

theorem directSum_eq (hB : BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) :
    (commV L ⊔ fixV (ffJ X)) ⊓
        ((⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L), commV L') ⊔
          fixV (ffJ X)) = fixV (ffJ X) := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨a, ha, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.1 hx1
    obtain ⟨b, hb, c₂, hc₂, hbc⟩ := Subgroup.mem_sup.1 hx2
    have hbfix : b ∈ fixV (blk X L) := by
      have hle : (⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L),
          commV L') ≤ fixV (blk X L) := by
        refine iSup₂_le fun L' hL' w hw y hy => ?_
        exact blk_le_centSub hB.hV hB.hP4 hB.hctx hL hL'.1 (hB.hact L' hL'.1) (Ne.symm hL'.2) hy w hw
      exact hle hb
    have haeq : a = b * c₂ * c₁⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hbc.symm
    have haL : ∀ y ∈ blk X L, y a = a := by
      intro y hy
      have hy' : y ∈ ffJ X := blk_le_ffJ hL (hB.hact L hL) hy
      rw [haeq, map_mul, map_mul, map_inv, hbfix y hy, hc₂ y hy', hc₁ y hy']
    have hafix : a ∈ fixV (ffJ X) := mem_fixV_ffJ hB hL ha haL
    exact (fixV (ffJ X)).mul_mem hafix hc₁
  · exact le_inf le_sup_right le_sup_right

theorem commV_ffJ_eq (hB : BlkCtx X T M) : commV (ffJ X) = vSigma X := by
  apply le_antisymm
  · have h : ffJ X ≤ centQuot (vSigma X) := by
      rw [ffJ_eq_blk hB]
      exact iSup₂_le fun L hL =>
        (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL)).trans
          (centQuot_mono (commV_le_vSigma hL))
    rw [commV_eq_commSub, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, -, rfl⟩
    exact h hx v
  · refine iSup₂_le fun L hL => ?_
    rw [commV_eq_commSub, commV_eq_commSub]
    exact commSub_mono le_rfl (le_blk_self.trans (blk_le_ffJ hL (hB.hact L hL)))

theorem blk_shape (hB : BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) :
    (∃ e : ℕ, 1 ≤ e ∧
        BinaryNaturalSL (blk X L) (commV (blk X L)) (commV (blk X L) ⊓ fixV (ffJ X)) 2 e ∧
        M ⊓ blk X L =
          blk X L ⊓ Subgroup.normalizer ((T ⊓ blk X L : Subgroup (MulAut V)) : Set (MulAut V))) ∨
      (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(blk X L),
        (FFModel.symDn (2 * k + 1)).RealizesVia (blk X L) (commV (blk X L)) ⊥ π ∧
        (M ⊓ blk X L).subgroupOf (blk X L) =
          (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
            (⟨0, by omega⟩ : Fin (2 * k + 1))).map π) := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := hB.hact L hL
  have hW₀ : commV L ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hB.hV hB.hctx hA₀ hL hLA₀
  have hshape : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
      CompShape T M A L (commV L) := fun A hA hLA => hB.hctx A L hA hL hLA (commV L) hW₀
  by_cases hAlt : ∃ A : Subgroup (MulAut V), IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧ AltShape M A L (commV L)
  · obtain ⟨A, hA, hLA, hAlt⟩ := hAlt
    have hblk : blk X L = L ⊔ A := le_antisymm
      (blk_le_iff.2 ⟨le_sup_left, fun A' hA' hLA' => hB.hG1 A L hA hL hLA hAlt A' hA' hLA'⟩)
      (sup_le le_blk_self (le_blk_of hA hLA))
    have hcomm : commV (L ⊔ A) = commV L := by
      rw [← hblk]
      exact commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL ⟨A₀, hA₀, hLA₀⟩)
    right
    obtain ⟨k, hk, π, -, hreal, -, -, hM⟩ := hAlt
    rw [hblk, hcomm]
    exact ⟨k, hk, π, hreal, hM⟩
  · push Not at hAlt
    have hnat : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
        NatShape T M A L (commV L) := fun A hA hLA =>
      (compShape_iff.1 (hshape A hA hLA)).resolve_right (hAlt A hA hLA)
    have hblk : blk X L = L := le_antisymm
      (blk_le_iff.2 ⟨le_rfl, fun A hA hLA => (hnat A hA hLA).2.1.1⟩) le_blk_self
    obtain ⟨⟨e, he, hbin⟩, -, hMN⟩ := hnat A₀ hA₀ hLA₀
    left
    have h1 := commV_inf_fixV_ffJ hB hL
    rw [hblk] at h1
    rw [hblk, h1]
    exact ⟨e, he, hbin, hMN⟩

theorem blk_ne_of_ne (hB : BlkCtx X T M) {L L' : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L') :
    blk X L ≠ blk X L' := by
  intro heq
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  refine Group.IsPerfect.not_isMulCommutative ↥L
    (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
  have := blk_commute hB.hV hB.hP4 hB.hctx hL hL' hne a (le_blk_self ha) b
    (heq ▸ le_blk_self hb)
  exact this

noncomputable def blkFamily (X : Subgroup (MulAut V)) : Finset (Subgroup (MulAut V)) :=
  (Set.toFinite {H : Subgroup (MulAut V) |
    ∃ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X ∧ H = blk X L}).toFinset

theorem mem_blkFamily {X H : Subgroup (MulAut V)} :
    H ∈ blkFamily X ↔ ∃ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X ∧ H = blk X L := by
  simp [blkFamily]

theorem iSup_commV_blkFamily (hB : BlkCtx X T M) : (⨆ H ∈ blkFamily X, commV H) = vSigma X := by
  apply le_antisymm
  · refine iSup₂_le fun H hH => ?_
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    rw [commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL))]
    exact commV_le_vSigma hL
  · refine iSup₂_le fun L hL => ?_
    have h1 := commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL))
    calc commV L = commV (blk X L) := h1.symm
      _ ≤ ⨆ H ∈ blkFamily X, commV H :=
        le_iSup₂_of_le (f := fun (H : Subgroup (MulAut V)) (_ : H ∈ blkFamily X) => commV H)
          (blk X L) (mem_blkFamily.2 ⟨L, hL, rfl⟩) le_rfl

theorem structConcl_of_blkCtx (hB : BlkCtx X T M) (h : MinParabolic X T M) (hFF : IsFFModule X) :
    StructConcl X T M (blkFamily X) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    exact blk_le_X hL
  · refine le_antisymm ((ffJ_eq_blk hB).le.trans (iSup₂_le fun L hL => ?_)) (iSup₂_le fun H hH => ?_)
    · exact le_iSup₂_of_le (f := fun (H : Subgroup (MulAut V)) (_ : H ∈ blkFamily X) => H)
        (blk X L) (mem_blkFamily.2 ⟨L, hL, rfl⟩) le_rfl
    · obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
      exact blk_le_ffJ hL (hB.hact L hL)
  · intro H hH H' hH' hne a ha b hb
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    obtain ⟨L', hL', rfl⟩ := mem_blkFamily.1 hH'
    exact blk_commute hB.hV hB.hP4 hB.hctx hL hL' (fun e => hne (by rw [e])) a ha b hb
  · intro H hH
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    have hle : (⨆ H' ∈ blkFamily X, ⨆ (_ : H' ≠ blk X L), H') ≤
        ⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L), blk X L' := by
      refine iSup₂_le fun H' hH' => iSup_le fun hne => ?_
      obtain ⟨L', hL', rfl⟩ := mem_blkFamily.1 hH'
      exact le_iSup₂_of_le (f := fun (L' : Subgroup (MulAut V))
        (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L) => blk X L') L'
        ⟨hL', fun e => hne (by rw [e])⟩ le_rfl
    exact le_bot_iff.1 ((inf_le_inf_left _ hle).trans (blk_inf_eq_bot hB hL).le)
  · rw [commV_ffJ_eq hB, iSup_commV_blkFamily hB]
  · intro H hH
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    have h1 := commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL))
    have h2 : (⨆ H' ∈ blkFamily X, ⨆ (_ : H' ≠ blk X L), commV H') =
        ⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L), commV L' := by
      apply le_antisymm
      · refine iSup₂_le fun H' hH' => iSup_le fun hne => ?_
        obtain ⟨L', hL', rfl⟩ := mem_blkFamily.1 hH'
        rw [commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL' (hB.hact L' hL'))]
        exact le_iSup₂_of_le (f := fun (L' : Subgroup (MulAut V))
          (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L) => commV L') L'
          ⟨hL', fun e => hne (by rw [e])⟩ le_rfl
      · refine iSup₂_le fun L' hL' => ?_
        have h3 := commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL'.1 (hB.hact L' hL'.1))
        have hne : blk X L' ≠ blk X L := blk_ne_of_ne hB hL'.1 hL hL'.2
        calc commV L' = commV (blk X L') := h3.symm
          _ ≤ ⨆ H' ∈ blkFamily X, ⨆ (_ : H' ≠ blk X L), commV H' :=
            le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut V)) (_ : H' ∈ blkFamily X) =>
              ⨆ (_ : H' ≠ blk X L), commV H') (blk X L') (mem_blkFamily.2 ⟨L', hL'.1, rfl⟩)
              (le_iSup (f := fun (_ : blk X L' ≠ blk X L) => commV (blk X L')) hne)
    rw [h1, h2]
    exact directSum_eq hB hL
  · intro H hH H' hH' hne
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    obtain ⟨L', hL', rfl⟩ := mem_blkFamily.1 hH'
    have hLL : L ≠ L' := fun e => hne (by rw [e])
    rw [commV_blk_eq (blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL)), commSub_eq_bot_iff]
    intro w hw y hy
    exact blk_le_centSub hB.hV hB.hP4 hB.hctx hL' hL (hB.hact L hL) (Ne.symm hLL) hy w hw
  · intro H hH H' hH'
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    obtain ⟨L', hL', rfl⟩ := mem_blkFamily.1 hH'
    obtain ⟨t, ht, hconj⟩ := exists_conj_component h hL hL'
    exact ⟨t, ht, by rw [conjSub_blk (h.isSylow.1 ht), hconj]⟩
  · exact MinParabolic.eq_sup_ffJ h hB.hO2 hFF
  · intro H hH
    obtain ⟨L, hL, rfl⟩ := mem_blkFamily.1 hH
    exact blk_shape hB hL

end B69

end CFSG.Quasithin

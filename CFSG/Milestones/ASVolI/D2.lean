module

public import CFSG.Milestones.ASVolI.D1
public import CFSG.Quasithin.Background.D2Z20
public import CFSG.Quasithin.Background.F918E2

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

abbrev cmt {G : Type*} [Group G] (H K : Subgroup G) : Subgroup G := ⁅H, K⁆

@[expose] def RleR (X : Subgroup (MulAut V)) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  {A | IsA2 X A ∧ ((rAV A : ℚ) : ℝ) ≤ r}

@[expose] def ReqR (X : Subgroup (MulAut V)) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  {A | IsA2 X A ∧ ((rAV A : ℚ) : ℝ) = r}

@[expose] def RPlusLeR (X : Subgroup (MulAut V)) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  RleR X r ∩ RPlus X

@[expose] def RPlusEqR (X : Subgroup (MulAut V)) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  ReqR X r ∩ RPlus X

@[expose] def kRleR (X : Subgroup (MulAut V)) (k : ℕ) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  {A | A ∈ RleR X r ∧ commSeries A k = ⊥}

@[expose] def kRPlusLeR (X : Subgroup (MulAut V)) (k : ℕ) (r : ℝ) : Set (Subgroup (MulAut V)) :=
  kRleR X k r ∩ RPlus X

@[expose] noncomputable def kqR [Finite V] (X : Subgroup (MulAut V)) (k : ℕ) : WithTop ℝ :=
  (kq X k).map (fun s : ℚ => (s : ℝ))

theorem convReq {Y Z : Subgroup (MulAut V)} {s : ℚ} (h : Z ∈ Req Y s) : Z ∈ ReqR Y (s : ℝ) :=
  ⟨h.1, by rw [h.2]⟩

theorem convRPlusEq {Y Z : Subgroup (MulAut V)} {s : ℚ} (h : Z ∈ RPlusEq Y s) :
    Z ∈ RPlusEqR Y (s : ℝ) := ⟨convReq h.1, h.2⟩

theorem convRle {Y Z : Subgroup (MulAut V)} {s : ℚ} (h : Z ∈ Rle Y s) : Z ∈ RleR Y (s : ℝ) :=
  ⟨h.1, by exact_mod_cast h.2⟩

theorem mRel_add_rk_aux {G : Type} [Group G] [Finite G] {N J : Subgroup G} (h : J ≤ N) :
    mRel N J + rk J = rk N := by
  have h1 := Subgroup.relIndex_mul_card (H := J) (K := N)
  rw [inf_eq_left.mpr h] at h1
  unfold mRel rk
  have h3 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have h2 : J.relIndex N ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [← h1, padicValNat.mul h2 h3]

theorem twoSummands_of_perm_aux [Finite V] {ι : Type} {I : ι → Subgroup V} (hind : iSupIndep I)
    (hsup : ⨆ i, I i = ⊤) (hrank : ∀ i, 2 ≤ rk (I i)) (hcard : Nat.card ι = 2)
    (H : Subgroup (MulAut V)) (hperm : ∀ g ∈ H, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) (i : ι) :
    ∃ j : ι, j ≠ i ∧ TwoSummands H (I i) (I j) := by
  obtain ⟨j, hj, huniq⟩ := (Nat.card_eq_two_iff' i).1 hcard
  have hall : ∀ k, k = i ∨ k = j := fun k => by
    by_cases hk : k = i
    · exact Or.inl hk
    · exact Or.inr (huniq k hk)
  have hdisj : Disjoint (I i) (I j) := hind.pairwiseDisjoint hj.symm
  have hne : ∀ k, I k ≠ ⊥ := fun k hk => by
    have := hrank k
    rw [hk, rk_bot] at this
    omega
  have hIne : I i ≠ I j := fun h => by
    rw [h] at hdisj
    exact hne j (disjoint_self.mp hdisj)
  refine ⟨j, hj, hdisj, ?_, ?_⟩
  · apply top_unique
    rw [← hsup]
    exact iSup_le fun k => by
      rcases hall k with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  · intro g hg
    obtain ⟨k₁, hk₁⟩ := hperm g hg i
    obtain ⟨k₂, hk₂⟩ := hperm g hg j
    have hinj : ∀ X Y : Subgroup V, X.map g.toMonoidHom = Y.map g.toMonoidHom → X = Y :=
      fun X Y h => Subgroup.map_injective (f := g.toMonoidHom) g.injective h
    have hmem : ∀ k, I k = I i ∨ I k = I j := fun k => by
      rcases hall k with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    have e₁ : (I i).map g.toMonoidHom = I i ∨ (I i).map g.toMonoidHom = I j := by
      rw [hk₁]; exact hmem k₁
    have e₂ : (I j).map g.toMonoidHom = I i ∨ (I j).map g.toMonoidHom = I j := by
      rw [hk₂]; exact hmem k₂
    rcases e₁ with e₁ | e₁
    · left
      refine ⟨e₁, ?_⟩
      rcases e₂ with e₂ | e₂
      · exact absurd (hinj _ _ (e₁.trans e₂.symm)) hIne
      · exact e₂
    · right
      refine ⟨e₁, ?_⟩
      rcases e₂ with e₂ | e₂
      · exact e₂
      · exact absurd (hinj _ _ (e₁.trans e₂.symm)) hIne

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_2_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V),
      qOf X = kq X 2 ∧ qhatOf X = kq X 3 ∧
      ((Qset X).Nonempty ↔ qOf X ≤ ((2 : ℚ) : WithTop ℚ)) ∧
      ((Qhat X 2).Nonempty ↔ qhatOf X ≤ ((2 : ℚ) : WithTop ℚ))

theorem as_D_2_1 : D_2_1 := by
  intro V _ _ _ X
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨A, ⟨hA2, hr⟩, hk⟩
    exact CFSG.Quasithin.kq_le_iff.mpr ⟨A, hA2, hk, hr⟩
  · intro h
    obtain ⟨A, hA2, hk, hr⟩ := CFSG.Quasithin.kq_le_iff.mp h
    exact ⟨A, ⟨hA2, hr⟩, hk⟩
  · rintro ⟨A, ⟨hA2, hr⟩, hk⟩
    exact CFSG.Quasithin.kq_le_iff.mpr ⟨A, hA2, hk, hr⟩
  · intro h
    obtain ⟨A, hA2, hk, hr⟩ := CFSG.Quasithin.kq_le_iff.mp h
    exact ⟨A, ⟨hA2, hr⟩, hk⟩

@[expose] def D_2_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℝ), A ∈ RleR X r →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ →
        (∃ ε : ℝ, 0 < ε ∧ autSub A U ∈ RleR (autSub X U) (r - ε)) ∨
        (∃ ε : ℝ, 0 < ε ∧ A ⊓ centSub U ∈ RleR X (r - ε)) ∨
        (A ⊓ centSub U = ⊥ ∧ rAV A = rAV (autSub A U) ∧ U ⊔ fixV A = ⊤) ∨
        (A ∈ ReqR X r ∧ autSub A U ∈ ReqR (autSub X U) r ∧ A ⊓ centSub U ∈ ReqR X r ∧
          fixV (A ⊓ centSub U) = U ⊔ fixV A)

theorem as_D_2_2 : D_2_2 := by
  intro V _ _ hV X A r hA U hU hUA
  obtain ⟨hA2, hAr⟩ := hA
  have h := CFSG.Quasithin.D2_2 hV (X := X) (A := A) (r := rAV A) ⟨hA2, le_rfl⟩ hU hUA
  by_cases hrr : ((rAV A : ℚ) : ℝ) = r
  · subst hrr
    rcases h with ⟨ε, hε, h1⟩ | ⟨ε, hε, h2⟩ | h3 | ⟨h4a, h4b, h4c, h4d⟩
    · exact Or.inl ⟨ε, by exact_mod_cast hε, by simpa using convRle h1⟩
    · exact Or.inr (Or.inl ⟨ε, by exact_mod_cast hε, by simpa using convRle h2⟩)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr ⟨convReq h4a, convReq h4b, convReq h4c, h4d⟩))
  · have hlt : ((rAV A : ℚ) : ℝ) < r := lt_of_le_of_ne hAr hrr
    have hδpos : 0 < r - ((rAV A : ℚ) : ℝ) := sub_pos.mpr hlt
    rcases h with ⟨ε, hε, h1⟩ | ⟨ε, hε, h2⟩ | h3 | ⟨h4a, h4b, h4c, h4d⟩
    · have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
      have hpos : 0 < (ε : ℝ) + (r - ((rAV A : ℚ) : ℝ)) := by linarith
      have h' : ((rAV (autSub A U) : ℚ) : ℝ) ≤ ((rAV A : ℚ) : ℝ) - (ε : ℝ) := by
        exact_mod_cast h1.2
      exact Or.inl ⟨(ε : ℝ) + (r - ((rAV A : ℚ) : ℝ)), hpos, h1.1, by linarith⟩
    · have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
      have hpos : 0 < (ε : ℝ) + (r - ((rAV A : ℚ) : ℝ)) := by linarith
      have h' : ((rAV (A ⊓ centSub U) : ℚ) : ℝ) ≤ ((rAV A : ℚ) : ℝ) - (ε : ℝ) := by
        exact_mod_cast h2.2
      exact Or.inr (Or.inl ⟨(ε : ℝ) + (r - ((rAV A : ℚ) : ℝ)), hpos, h2.1, by linarith⟩)
    · exact Or.inr (Or.inr (Or.inl h3))
    · have h5 := h4b.2
      have h6 : ((rAV (autSub A U) : ℚ) : ℝ) ≤ r - (r - ((rAV A : ℚ) : ℝ)) := by
        rw [h5]; linarith
      exact Or.inl ⟨r - ((rAV A : ℚ) : ℝ), hδpos, h4b.1, h6⟩

@[expose] def D_2_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V),
      (∀ A B : Subgroup (MulAut V), A ∈ RPlus X → B ≠ ⊥ → B ≤ A → rAV A = rAV B → B ∈ RPlus X) ∧
      (∀ (A : Subgroup (MulAut V)) (k : ℕ), IsA2 X A → commSeries A k = ⊥ →
        (rAV A : WithTop ℚ) = kq X k → A ∈ RPlus X)

theorem as_D_2_3 : D_2_3 := by
  intro V _ _ _ X
  exact ⟨fun A B hA hB hBA hr => CFSG.Quasithin.D2_3_1 hA hB hBA hr,
    fun A k hA hk hr => CFSG.Quasithin.D2_3_2 hA hk hr⟩

@[expose] def D_2_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℝ), A ∈ RPlusEqR X r →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ →
        (∃ ε : ℝ, 0 < ε ∧ autSub A U ∈ RleR (autSub X U) (r - ε) ∧ rAV (autSub A U) < rAV A) ∨
        (A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧
          (∀ D : Subgroup (MulAut V), D ≠ ⊥ → D ≤ A →
            rkIdx (fixV (autSub D U)) = rkIdx (fixV D) ∧ rAV (autSub D U) = rAV D ∧
              r ≤ ((rAV D : ℚ) : ℝ)) ∧
          A ∈ RPlusEqR X r ∧ autSub A U ∈ RPlusEqR (autSub X U) r) ∨
        (autSub A U ∈ ReqR (autSub X U) r ∧ A ⊓ centSub U ∈ RPlusEqR X r ∧
          fixV (A ⊓ centSub U) = U ⊔ fixV A)

theorem as_D_2_4 : D_2_4 := by
  intro V _ _ hV X A r hA U hU hUA
  obtain ⟨⟨hA2, hAr⟩, hAplus⟩ := hA
  subst hAr
  have h := CFSG.Quasithin.D2_4 hV (X := X) (A := A) (r := rAV A) ⟨⟨hA2, rfl⟩, hAplus⟩ hU hUA
  rcases h with ⟨ε, hε, h1, h2⟩ | ⟨hB, hW, hD, hAm, hAUm⟩ | ⟨h3, h4, h5⟩
  · refine Or.inl ⟨(ε : ℝ), by exact_mod_cast hε, ?_, h2⟩
    have := convRle h1
    simpa using this
  · refine Or.inr (Or.inl ⟨hB, hW, ?_, convRPlusEq hAm, convRPlusEq hAUm⟩)
    intro D hDne hDA
    obtain ⟨e1, e2, e3⟩ := hD D hDne hDA
    exact ⟨e1, e2, by exact_mod_cast e3⟩
  · exact Or.inr (Or.inr ⟨convReq h3, convRPlusEq h4, h5⟩)

@[expose] def D_2_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℝ), A ∈ RPlusLeR X r →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ →
        autSub A U ∈ RleR (autSub X U) r

theorem as_D_2_5 : D_2_5 := by
  intro V _ _ hV X A r hA U hU hUA
  obtain ⟨⟨hA2, hAr⟩, hAplus⟩ := hA
  obtain ⟨hAU, hle⟩ := CFSG.Quasithin.D2_5 hV (X := X) (A := A) (r := rAV A)
    ⟨⟨hA2, le_rfl⟩, hAplus⟩ hU hUA
  exact ⟨hAU, le_trans (Rat.cast_le.mpr hle) hAr⟩

@[expose] def D_2_6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (k : ℕ) (r : ℝ), A ∈ kRPlusLeR X k r →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ → (r : WithTop ℝ) ≤ kqR (autSub X U) k →
        kqR (autSub X U) k = (r : WithTop ℝ) ∧
        ((A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧ autSub A U ∈ RPlusEqR (autSub X U) r) ∨
         (autSub A U ∈ ReqR (autSub X U) r ∧ A ⊓ centSub U ∈ RPlusEqR X r ∧
          fixV (A ⊓ centSub U) = U ⊔ fixV A))

theorem as_D_2_6 : D_2_6 := by
  intro V _ _ hV X A k r hA U hU hUA hq
  obtain ⟨⟨⟨hA2, hAr⟩, hAk⟩, hAplus⟩ := hA
  have hAmem : A ∈ kRPlusLe X k (rAV A) := ⟨⟨⟨hA2, le_rfl⟩, hAk⟩, hAplus⟩
  have hq' : ((rAV A : ℚ) : WithTop ℚ) ≤ kq (autSub X U) k := by
    unfold kqR at hq
    cases hkq : kq (autSub X U) k with
    | top => exact le_top
    | coe s =>
      rw [hkq] at hq
      have h1 : r ≤ (s : ℝ) := by
        have := hq
        simpa using this
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hAr.trans h1)
  obtain ⟨hkq, hcases⟩ := CFSG.Quasithin.D2_6 hV (X := X) (A := A) (k := k) (r := rAV A) hAmem hU hUA hq'
  have hrr : r = ((rAV A : ℚ) : ℝ) := by
    unfold kqR at hq
    rw [hkq] at hq
    have h1 : r ≤ ((rAV A : ℚ) : ℝ) := by simpa using hq
    exact le_antisymm h1 hAr
  subst hrr
  refine ⟨by unfold kqR; rw [hkq]; rfl, ?_⟩
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, convRPlusEq h3⟩
  · exact Or.inr ⟨convReq h1, convRPlusEq h2, h3⟩

@[expose] def D_2_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → A ∈ QhatStar X →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ →
        A ∈ kRPlusEq X 3 r ∧
        ((∃ ε : ℚ, 0 < ε ∧ autSub A U ∈ Qhat (autSub X U) (r - ε)) ∨
         (A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤))

theorem as_D_2_7 : D_2_7 := by
  intro V _ _ hV X A r hr _ hA U hU hUA
  exact CFSG.Quasithin.D2_7 hV hr hA hU hUA

@[expose] def D_2_8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → A ∈ QhatStar X →
      ∀ U : Subgroup V, A ≤ stabSub U → commSub U A ≠ ⊥ → (r : WithTop ℚ) ≤ qhatOf (autSub X U) →
        qhatOf (autSub X U) = (r : WithTop ℚ) ∧ A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧
          autSub A U ∈ QhatStar (autSub X U)

theorem as_D_2_8 : D_2_8 := by
  intro V _ _ hV X A r hr _ hA U hU hUA hq
  exact CFSG.Quasithin.D2_8 hV hr hA hU hUA hq

@[expose] def D_2_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G A : Subgroup (MulAut V)), A ∈ kRPlusLe G 3 2 →
      ∀ (ι : Type) (I : ι → Subgroup V), iSupIndep I → ⨆ i, I i = ⊤ → (∀ i, 2 ≤ rk (I i)) →
        (∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) →
        ∀ i : ι,
          (A ⊓ stabSub (I i)).relIndex A ≤ 2 ∧
          (A ⊓ stabSub (I i) < A →
            commSub (commSub (I i) (A ⊓ stabSub (I i))) (A ⊓ stabSub (I i)) = ⊥) ∧
          (commSeries A 2 = ⊥ → A ⊓ stabSub (I i) < A →
            rk (I i) = 2 ∧ rAV A = 2 ∧
              (Nat.card A = 2 ∨ A ⊓ stabSub (I i) ∈ kRPlusLe G 2 2)) ∧
          (A ⊓ stabSub (I i) < A → 2 < rk (I i) →
            ∃ ε : ℚ, 0 < ε ∧
              autSub (A ⊓ stabSub (I i)) (I i) ∈ Rle (autSub G (I i)) (rAV A - ε)) ∧
          (Nat.card ι = 2 → A ⊓ stabSub (I i) < A →
            ((∃ (c : V) (hc : c ∈ I i), c ≠ 1 ∧
                (∀ t : MulAut ↥(I i), t ∈ autSub (A ⊓ stabSub (I i)) (I i) ↔
                  IsTransvectionWith t (⟨c, hc⟩ : ↥(I i))) ∧
                (2 < rk (I i) → (∀ g ∈ G, ∀ j, ∃ k, (I j).map g.toMonoidHom = I k) →
                  pCoreOf 2 G ≠ ⊥ ∨ qOf G < (rAV A : WithTop ℚ))) ∨
              (mRel (I i) (I i ⊓ fixV (A ⊓ stabSub (I i))) + 2 = rk (I i) ∧
                rk ↥(A ⊓ stabSub (I i)) + 2 = rk (I i) ∧
                (2 < rk (I i) → rAV (A ⊓ stabSub (I i)) = rAV A ∧ rAV A = 2 ∧
                  A ∉ QhatStar G)))) ∧
          ((∀ g ∈ G, ∀ j, ∃ k, (I j).map g.toMonoidHom = I k) → Nat.card ι = 2 → 2 < rk (I i) →
            pCoreOf 2 G = ⊥ → ∀ A' ∈ QhatStar G, A' ≤ stabSub (I i))

theorem as_D_2_9 : D_2_9 := by
  intro V _ _ hV G A hA ι I hind hsup hrank hperm i
  have hAG : A ≤ G := hA.1.1.1.le
  have hAe : IsElemAbelian2 A := hA.1.1.1.isElemAbelian2
  refine ⟨CFSG.Quasithin.d29_index_le_two hV hA hind hsup hrank hperm i,
    fun hB => CFSG.Quasithin.d29_quadratic hV hA hind hsup hrank hperm i hB,
    fun hq hB => CFSG.Quasithin.d29_quadratic_case hV hA hind hsup hrank hperm i hq hB,
    fun hB hi => CFSG.Quasithin.d29_rank_drop hV hA hind hsup hrank hperm i hB hi, ?_, ?_⟩
  · intro hcard hB
    obtain ⟨j, hji, hSA⟩ := twoSummands_of_perm_aux hind hsup hrank hcard A hperm i
    have hi2 : 2 ≤ rk (I i) := hrank i
    obtain ⟨a, haA, haI⟩ : ∃ a ∈ A, a ∉ stabSub (I i) := by
      by_contra h
      push Not at h
      exact absurd hB (not_lt_of_ge fun g hg => ⟨hg, h g hg⟩)
    rcases CFSG.Quasithin.d29_shape hV hA hSA hi2 hB with
      ⟨c, hc, hc1, hBc, hCI, hrkB, hr1, hfull⟩ | ⟨hrk, hm, hcase⟩
    · left
      refine ⟨c, hc, hc1, fun t => ⟨fun ht => ?_, hfull t⟩, fun h2 hGperm => ?_⟩
      · obtain ⟨⟨b, hb⟩, hbA, rfl⟩ := mem_autSub.mp ht
        refine ⟨hc1 ∘ fun h => congrArg Subtype.val h, fun x => ?_⟩
        rcases hBc b hbA x x.2 with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · obtain ⟨j', hj'i, hSG⟩ := twoSummands_of_perm_aux hind hsup hrank hcard G hGperm i
        rcases CFSG.Quasithin.d29_further hV hSG h2 hAG hAe haA haI hc hc1 hBc hrkB hfull with
          hp | ⟨A₀, hA₀, hq, hr⟩
        · exact Or.inl hp
        · right
          have h1 : qOf G ≤ ((1 : ℚ) : WithTop ℚ) :=
            CFSG.Quasithin.qOf_le_iff.mpr
              ⟨A₀, hA₀, (CFSG.Quasithin.isQuadratic_iff_commSeries_two A₀).mpr hq, hr⟩
          exact lt_of_le_of_lt h1 (WithTop.coe_lt_coe.mpr hr1)
    · right
      have hJ : mRel (I i) (I i ⊓ fixV (A ⊓ stabSub (I i))) + rk ↥(I i ⊓ fixV (A ⊓ stabSub (I i))) =
          rk (I i) := mRel_add_rk_aux inf_le_left
      have hki : rk ↥(I i ⊓ fixV (A ⊓ stabSub (I i))) ≤ rk (I i) := rk_mono inf_le_left
      refine ⟨by omega, by omega, fun h2 => ?_⟩
      obtain ⟨hr, hr2⟩ := hcase h2
      refine ⟨hr, hr2, fun hQ => ?_⟩
      obtain ⟨r, hqr, -, hAk, hmin⟩ := CFSG.Quasithin.QhatStar_spec hQ
      have hBne : A ⊓ stabSub (I i) ≠ ⊥ := by
        intro h
        have : rk ↥(A ⊓ stabSub (I i)) = 0 := by rw [h, rk_bot]
        omega
      have hA2 : IsA2 G A := hA.1.1.1
      have hBA : A ⊓ stabSub (I i) ≤ A := inf_le_left
      have hmem : A ⊓ stabSub (I i) ∈ kRle G 3 r := by
        refine ⟨⟨hA2.mono hBA hBne, ?_⟩, le_bot_iff.mp (hAk.2 ▸ CFSG.Quasithin.commSeries_mono hBA 3)⟩
        rw [hr]
        exact hAk.1.2.le
      have := hmin _ hmem hBA
      exact absurd this (ne_of_lt hB)
  · intro hGperm hcard hi hO2 A' hA'
    obtain ⟨j, hji, hSG⟩ := twoSummands_of_perm_aux hind hsup hrank hcard G hGperm i
    exact CFSG.Quasithin.d29_six hV hSG hi hO2 A' hA'

end CFSG.ASVolI

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

@[expose] def D217Alt1 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  Nonempty (↥X ≃* DihedralGroup 3) ∧ (rk V : ℚ) = 2 * r ∧ (r = 1 ∨ r = 2)

@[expose] def D217Alt2 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  Nonempty (↥X ≃* DihedralGroup 5) ∧ rk V = 4 ∧ r = 2

@[expose] def D217Alt3 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 9 ∧
    (∃ t ∈ X, orderOf t = 2 ∧ (∀ f ∈ fittingOf X, t * f * t⁻¹ = f⁻¹) ∧
      X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 4 ∧ r = 2

@[expose] def D217Alt4 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  Nat.card (fittingOf X) = 27 ∧ (∀ f ∈ fittingOf X, f ^ 3 = 1) ∧
    (∃ f ∈ fittingOf X, ∃ g ∈ fittingOf X, f * g ≠ g * f) ∧
    (∃ t ∈ X, orderOf t = 2 ∧
      (∀ f ∈ fittingOf X, t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf X)).map (fittingOf X).subtype) ∧
      X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 6 ∧ r = 2

@[expose] def D217Alt5 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  rk V = 4 ∧ IsOmegaFourPlus X ∧ Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3) ∧ r = 3 / 2

@[expose] def D217Alt6 (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 27 ∧
    (∃ A : Subgroup (MulAut V), A ≤ X ∧ IsElemAbelian2 A ∧ Nat.card A = 4 ∧
      X = fittingOf X ⊔ A) ∧ rk V = 6 ∧ r = 3 / 2

@[expose] def X1set (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {Y | Y ≤ pCoreOf 3 X ∧ Nat.card Y = 3 ∧ rk (commV Y) = 2}

@[expose] def Yset (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {Y | Y ≤ pCoreOf 3 X ∧ Nat.card Y = 3 ∧ rk (commV Y) = 4}

theorem exists_gen_of_cyclic {G : Type*} [Group G] {Y : Subgroup G} (h : IsCyclic ↥Y) :
    ∃ x : G, Subgroup.zpowers x = Y := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp h

section CycHelpers

variable [Finite V]

theorem Xk_one_false {X : Subgroup (MulAut V)} (c : CycCtx X) (hV : ∀ v : V, v ^ 2 = 1)
    (hX1 : X1set X = ∅) : ∀ Y ∈ Xk X 1, False := by
  have hfit := CFSG.Quasithin.CycCtx.fittingOf_eq hV c
  intro Y hY
  have : Y ∈ X1set X := ⟨by rw [← hfit]; exact hY.1, by simpa using hY.2.1, by simpa using hY.2.2⟩
  rw [hX1] at this
  exact this

theorem zpowers_mem_Yset {X : Subgroup (MulAut V)} (c : CycCtx X) (hV : ∀ v : V, v ^ 2 = 1)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x : MulAut V} (ht : t ∈ TInv X) (hx : x ∈ pCoreOf 3 X)
    (hx1 : x ≠ 1) (hinv : t * x * t⁻¹ = x⁻¹) : Subgroup.zpowers x ∈ Yset X := by
  obtain ⟨h1, h2, -⟩ := CFSG.Quasithin.inverted_data hV c hX1 ht hx hx1 hinv
  exact ⟨Subgroup.zpowers_le.mpr hx, by rw [Nat.card_zpowers, h1], h2⟩

end CycHelpers

section D228Helpers

variable [Finite V]

theorem d228_setup (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hX1 : X1set X = ∅) {Y₀ : Subgroup (MulAut V)} {t : MulAut V}
    (hY₀F : Y₀ ≤ fittingOf X) (hY₀ne : Y₀ ≠ ⊥) (hcyc : IsCyclic ↥Y₀) (ht : t ∈ TInv X)
    (hinv : ∀ y ∈ Y₀, t * y * t⁻¹ = y⁻¹) (h2 : 1 < (Yset X).ncard) :
    ∃ x z : MulAut V, Subgroup.zpowers x = Y₀ ∧ InvPair X t x ∧ Good X t x z ∧
      ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂ := by
  have hfit := CFSG.Quasithin.CycCtx.fittingOf_eq hV c
  have hX1' := Xk_one_false c hV hX1
  obtain ⟨x, hxY⟩ := exists_gen_of_cyclic hcyc
  have hxmem : x ∈ Y₀ := hxY ▸ Subgroup.mem_zpowers x
  have hx1 : x ≠ 1 := fun h => hY₀ne (by rw [← hxY, h, Subgroup.zpowers_one_eq_bot])
  have hxR : x ∈ pCoreOf 3 X := by rw [← hfit]; exact hY₀F hxmem
  have hxinv : t * x * t⁻¹ = x⁻¹ := hinv x hxmem
  have hp : InvPair X t x := ⟨ht, hxR, hx1, hxinv⟩
  have htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂ := by
    by_contra hno
    push Not at hno
    have hY₀inv : Subgroup.zpowers x ∈ Yinv X :=
      CFSG.Quasithin.zpowers_mem_Yinv hV ht hxR hx1 hxinv
    obtain ⟨hiso, -⟩ := CFSG.Quasithin.D2_27 hV c hX1' hY₀inv
      (fun Y hY => hno Y hY _ hY₀inv)
    obtain ⟨e⟩ := hiso
    have hcardX : Nat.card X = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    obtain ⟨Y, Y', hY, hY', hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h2
    have hRle : pCoreOf 3 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 3 X
    have hRdvd : Nat.card (pCoreOf 3 X) ∣ 6 := hcardX ▸ Subgroup.card_dvd_of_le hRle
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X).exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans (hn ▸ hRdvd)
      omega
    have hY3 : Nat.card Y = 3 := hY.2.1
    have hY'3 : Nat.card Y' = 3 := hY'.2.1
    have hYR : Nat.card (pCoreOf 3 X) = 3 := by
      have h1 := Subgroup.card_le_of_le hY.1
      rw [hn] at h1 ⊢
      interval_cases n
      · simp at h1; omega
      · simp
    have e1 : Y = pCoreOf 3 X := Subgroup.eq_of_le_of_card_ge hY.1 (by rw [hY3, hYR])
    have e2 : Y' = pCoreOf 3 X := Subgroup.eq_of_le_of_card_ge hY'.1 (by rw [hY'3, hYR])
    exact hne (e1.trans e2.symm)
  obtain ⟨z, hg⟩ := CFSG.Quasithin.exists_good hV c hX1' htwo hp
  exact ⟨x, z, hxY, hp, hg, htwo⟩

theorem inf_eq_bot_of_card_three_aux {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  by_contra h
  have hdA : Nat.card (A ⊓ B : Subgroup G) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card (A ⊓ B : Subgroup G) = 3 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hdA with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) h
    · exact h3
  have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA, h3])
  have e2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hB, h3])
  exact hne (e1.symm.trans e2)

omit [Finite V] in
theorem inf_centralizer_zpowers_eq_aux (X : Subgroup (MulAut V)) (x : MulAut V) :
    pCoreOf 3 X ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup (MulAut V)) : Set (MulAut V)) = centR X x := by
    ext p
    rw [Subgroup.mem_inf, CFSG.Quasithin.mem_centR, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hpR, hpc⟩
      exact ⟨hpR, (hpc x (Subgroup.mem_zpowers x)).symm⟩
    · rintro ⟨hpR, hpx⟩
      refine ⟨hpR, fun g hg' => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
      have hc : Commute p x := hpx
      exact ((hc.zpow_right k).eq).symm

end D228Helpers

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD
open scoped Pointwise

@[expose] def D_2_11_withOddElement : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (t : MulAut V), t ∈ TInv X →
      ∀ x : MulAut V, x ∈ X → x ≠ 1 → Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ →
        (rk (commV (Subgroup.zpowers t)) = 1 →
          orderOf x = 3 ∧ rk (commV (Subgroup.zpowers x)) = 2) ∧
        (rk (commV (Subgroup.zpowers t)) = 2 →
          (orderOf x = 3 ∨ orderOf x = 5) ∧
            (orderOf x = 5 → rk (commV (Subgroup.zpowers x)) = 4)) ∧
        (rk (commV (Subgroup.zpowers x)) = 2 * rk (commV (Subgroup.zpowers t)) →
          commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t) =
            commV (Subgroup.zpowers t) ∧
          commSub (fixV (Subgroup.zpowers x)) (Subgroup.zpowers t) = ⊥ ∧
          ∀ y ∈ X, y ∈ Subgroup.centralizer ({x} : Set (MulAut V)) →
            y ∈ centSub (commV (Subgroup.zpowers x)) → y * t = t * y) ∧
        Subgroup.zpowers t ∈ Qset X

theorem as_D_2_11_withOddElement : D_2_11_withOddElement := by
  intro V _ _ hV X t ht x hx hx1 hodd hinv
  exact ⟨fun hm => CFSG.Quasithin.D2_11_1 hV ht hm hx hx1 hodd hinv,
    fun hm => CFSG.Quasithin.D2_11_2 hV ht hm hx hx1 hodd hinv,
    fun hm => CFSG.Quasithin.D2_11_3 hV ht hx hx1 hodd hinv hm,
    CFSG.Quasithin.D2_11_4 hV ht⟩

@[expose] def D_2_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (t : MulAut V), t ∈ TInv X →
      (∀ x : MulAut V, x ∈ X → x ≠ 1 → Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ →
        (rk (commV (Subgroup.zpowers t)) = 1 →
          orderOf x = 3 ∧ rk (commV (Subgroup.zpowers x)) = 2) ∧
        (rk (commV (Subgroup.zpowers t)) = 2 →
          (orderOf x = 3 ∨ orderOf x = 5) ∧
            (orderOf x = 5 → rk (commV (Subgroup.zpowers x)) = 4)) ∧
        (rk (commV (Subgroup.zpowers x)) = 2 * rk (commV (Subgroup.zpowers t)) →
          commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t) =
            commV (Subgroup.zpowers t) ∧
          commSub (fixV (Subgroup.zpowers x)) (Subgroup.zpowers t) = ⊥ ∧
          ∀ y ∈ X, y ∈ Subgroup.centralizer ({x} : Set (MulAut V)) →
            y ∈ centSub (commV (Subgroup.zpowers x)) → y * t = t * y)) ∧
      Subgroup.zpowers t ∈ Qset X

theorem as_D_2_11 : D_2_11 := by
  intro V _ _ hV X t ht
  refine ⟨?_, CFSG.Quasithin.D2_11_4 hV ht⟩
  intro x hx hx1 hodd hinv
  have legacy := as_D_2_11_withOddElement V hV X t ht x hx hx1 hodd hinv
  exact ⟨legacy.1, legacy.2.1, legacy.2.2.1⟩

@[expose] def D_2_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (k : ℕ), (k = 1 ∨ k = 2) →
      (CommFamily (Xk X k) ∧ iSupIndep (fun Y : Xk X k => (Y : Subgroup (MulAut V)))) ∧
      (commV (Gk X k) = ⨆ Y ∈ Xk X k, commV Y ∧
        iSupIndep (fun Y : Xk X k => commV (Y : Subgroup (MulAut V)))) ∧
      (∀ t : MulAut V, t ∈ TInv X → rk (commV (Subgroup.zpowers t)) = k →
        (((∀ g ∈ Gk X k, g * t = t * g) ∧
            commSub (commV (Gk X k)) (Subgroup.zpowers t) = ⊥) ∨
          (∃ Y ∈ Xk X k, (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) ∧
            (∀ Z ∈ Xk X k, (∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) → Z = Y) ∧
            commV (Subgroup.zpowers t) = commSub (commV Y) (Subgroup.zpowers t) ∧
            ∀ Z ∈ Xk X k, Z ≠ Y → (∀ z ∈ Z, t * z = z * t) ∧ ∀ w ∈ commV Z, t w = w)) ∧
        (∀ Y ∈ Xk X k, t ∈ Subgroup.normalizer (Y : Set (MulAut V)))) ∧
      (k = 1 → ∀ t : MulAut V, t ∈ TInv X → rk (commV (Subgroup.zpowers t)) = 2 →
        (∀ Y ∈ Xk X 1, t ∈ Subgroup.normalizer (Y : Set (MulAut V))) ∨
          (∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧ conjBy t Y₂ = Y₁ ∧
            commV (Subgroup.zpowers t) = commSub (commV Y₁ ⊔ commV Y₂) (Subgroup.zpowers t) ∧
            ∀ Z ∈ Xk X 1, Z ≠ Y₁ → Z ≠ Y₂ →
              (∀ z ∈ Z, t * z = z * t) ∧ ∀ w ∈ commV Z, t w = w))

theorem as_D_2_12 : D_2_12 := by
  intro V _ _ hV X k hk
  exact ⟨CFSG.Quasithin.D2_12_1 hV hk, CFSG.Quasithin.D2_12_2 hV hk,
    fun t ht hm => ⟨CFSG.Quasithin.D2_12_3 hV hk ht hm, CFSG.Quasithin.D2_12_4 hV hk ht hm⟩,
    fun hk1 t ht hm => by subst hk1; exact CFSG.Quasithin.D2_12_5 hV ht hm⟩

@[expose] def D_2_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → A ∈ QhatStar X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → (cmt (pCoreOf p X) A) ≠ ⊥ →
        (p = 3 ∨ p = 5) ∧
        (p = 5 → r = 2 ∧ rk A = 1 ∧ Nat.card (cmt (pCoreOf p X) A) = 5 ∧ IsCyclic (cmt (pCoreOf p X) A) ∧
          IsDirectSum ⊤ (commV (cmt (pCoreOf p X) A)) (fixV ((cmt (pCoreOf p X) A) ⊔ A)) ∧
          rk (commV (cmt (pCoreOf p X) A)) = 4) ∧
        (rk A = 1 → (r = 1 ∨ r = 2) ∧
          (r = 1 → p = 3 ∧ Nat.card (cmt (pCoreOf p X) A) = 3 ∧ IsCyclic (cmt (pCoreOf p X) A) ∧
            IsDirectSum ⊤ (commV (cmt (pCoreOf p X) A)) (fixV ((cmt (pCoreOf p X) A) ⊔ A)) ∧
            rk (commV (cmt (pCoreOf p X) A)) = 2)) ∧
        (r ≤ 1 → r = 1 ∧ p = 3 ∧ rk A = 1) ∧
        (1 < rk A → p = 3 ∧ ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card A = 2 * Nat.card B →
          (cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A) ≠ ⊥ →
            Nat.card (cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A) = 3 ∧
            IsCyclic (cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A) ∧
            IsDirectSum (fixV B)
              (commSub (fixV B) (cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A))
              (fixV ((cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A) ⊔ A)) ∧
            rk (commSub (fixV B)
              (cmt (pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V))) A)) = 2)

theorem as_D_2_13 : D_2_13 := by
  intro V _ _ hV X A r hr hr2 hA p hp hp2 hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.Quasithin.D2_13 hV hr hA hp2 (D := (cmt (pCoreOf p X) A)) rfl hne
  refine ⟨h1, h2, h3, h4, fun hrk => ?_⟩
  obtain ⟨hp3, h5'⟩ := h5 hrk
  subst hp3
  exact ⟨rfl, fun B hB hcard hne' => h5' B hB hcard _ rfl hne'⟩

end CFSG.ASVolI

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

structure D214Data (X A : Subgroup (MulAut V)) {s : ℕ} (P : Fin s → Subgroup (MulAut V)) : Prop where
  le : ∀ i, P i ≤ pCoreOf 3 X
  card : ∀ i, Nat.card (P i) = 3
  cyclic : ∀ i, IsCyclic (P i)
  comm : ∀ i j, ∀ a ∈ P i, ∀ b ∈ P j, a * b = b * a
  indep : iSupIndep P
  sup : ⨆ i, P i = pCoreOf 3 X
  card_P : Nat.card (pCoreOf 3 X) = 3 ^ s
  comm_eq : cmt (pCoreOf 3 X) A = pCoreOf 3 X
  vsup : commV (pCoreOf 3 X) = ⨆ i, commV (P i)
  vindep : iSupIndep (fun i => commV (P i))
  rk_eq : ∀ i, rk (commV (P i)) = 2

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_2_14 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X A : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → A ∈ QhatStar X →
      ¬ IsCyclic ↥A → (∀ a ∈ A, (∀ y ∈ oddFitting X, a * y = y * a) → a = 1) →
      commV (oddFitting X) = ⊤ → IsQuotientOfSQTKTC ↥X →
        (∀ y ∈ fittingRes23 X, ∀ a ∈ A, a * y = y * a) ∧
        ((∃ P : Fin 2 → Subgroup (MulAut V), D214Data X A P ∧ Case7i X A P) ∨
          (∃ P : Fin 3 → Subgroup (MulAut V), D214Data X A P ∧ Case7ii A P)) ∧
        rk A = 2 ∧
        commSub (fixV (pCoreOf 3 X)) A = ⊥ ∧
        r = 3 / 2

theorem as_D_2_14 : D_2_14 := by
  intro V _ _ hV X A r hr hr2 hA hnc hfaith hcomm hsqtk
  have h : D214Hyp X A r := ⟨hr, hA, hnc, hfaith, hcomm, hsqtk⟩
  refine ⟨CFSG.Quasithin.D2_14_1 hV h, ?_, CFSG.Quasithin.D2_14_4 hV h,
    CFSG.Quasithin.D2_14_5 hV h, CFSG.Quasithin.D2_14_6 hV h⟩
  have hcm := CFSG.Quasithin.commutator_pCoreOf_eq hV h
  have hPc := CFSG.Quasithin.pCoreOf_comm hV h
  rcases CFSG.Quasithin.D2_14_7 hV h with ⟨P, hd, -, hc⟩ | ⟨P, hd, -, hc⟩
  · exact Or.inl ⟨P, ⟨hd.le_P, hd.card_eq, fun i => isCyclic_of_prime_card (hd.card_eq i),
      fun i j a ha b hb => hPc a (hd.le_P i ha) b (hd.le_P j hb), hd.indep, hd.sup_eq, hd.card_P,
      hcm, hd.vsup.symm, hd.vindep, hd.rk_eq⟩, hc⟩
  · exact Or.inr ⟨P, ⟨hd.le_P, hd.card_eq, fun i => isCyclic_of_prime_card (hd.card_eq i),
      fun i j a ha b hb => hPc a (hd.le_P i ha) b (hd.le_P j hb), hd.indep, hd.sup_eq, hd.card_P,
      hcm, hd.vsup.symm, hd.vindep, hd.rk_eq⟩, hc⟩

@[expose] def D_2_17 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → X = Jhat X →
      commV (fittingOf X) = ⊤ → IsIndecomposablePair X →
      X ⊓ Subgroup.centralizer (fittingOf X : Set (MulAut V)) ≤ fittingOf X →
      pCoreOf 2 X = ⊥ → IsQuotientOfSQTKTC ↥X →
        QhatStar X = sylow2Of X ∧
          (D217Alt1 X r ∨ D217Alt2 X r ∨ D217Alt3 X r ∨ D217Alt4 X r ∨ D217Alt5 X r ∨ D217Alt6 X r)

theorem as_D_2_17 : D_2_17 := by
  intro V _ _ hV X r h1 h2 h3 h4 h5 h6 h7 h8
  exact CFSG.Quasithin.D2_17_of_hyp hV ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

@[expose] def D_2_18 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → ∀ A ∈ QhatStar X, Nat.card A = 2 →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (cmt (pCoreOf p X) A) ≠ ⊥) ∧ (r = 1 ∨ r = 2)

theorem as_D_2_18 : D_2_18 := by
  intro V _ _ hV X r h A hA hcard
  exact CFSG.Quasithin.D2_18 hV h hA hcard

@[expose] def D_2_19 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → ∀ A ∈ QhatStar X, 1 < rk A →
      (¬ IsCyclic ↥A ∧ (∀ a ∈ A, (∀ y ∈ oddFitting X, a * y = y * a) → a = 1) ∧
        commV (oddFitting X) = ⊤ ∧ IsQuotientOfSQTKTC ↥X) ∧
      r = 3 / 2 ∧ ∀ B ∈ QhatStar X, ¬ IsCyclic ↥B

theorem as_D_2_19 : D_2_19 := by
  intro V _ _ hV X r h A hA hrk
  obtain ⟨h14, hr, hall⟩ := CFSG.Quasithin.D2_19 hV h hA hrk
  refine ⟨⟨h14.noncyclic, h14.faithful, h14.comm_eq_top, h14.sqtk⟩, hr, fun B hB => ?_⟩
  obtain ⟨r', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := CFSG.Quasithin.QhatStar_spec hB
  exact CFSG.Quasithin.not_isCyclic_of_one_lt_rk hB2.isElemAbelian2 (hall B hB)

@[expose] def D_2_20 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r →
      fixV X = ⊥ ∧ ∀ W : Subgroup V, (∀ A ∈ QhatStar X, W ≤ fixV A) → W = ⊥

theorem as_D_2_20 : D_2_20 := by
  intro V _ _ hV X r h
  exact CFSG.Quasithin.D2_20 hV h

@[expose] def D_2_21 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → ∀ A ∈ QhatStar X,
      (∀ a ∈ A, (∀ y ∈ pCoreOf 3 X, a * y = y * a) → a = 1) →
      ∀ a ∈ A, a ≠ 1 → CFSG.Open.pRank 3 (X ⊓ Subgroup.centralizer ({a} : Set (MulAut V))) ≤ 1

theorem as_D_2_21 : D_2_21 := by
  intro V _ _ hV X r h A hA hfaith a haA ha1
  exact CFSG.Quasithin.D2_21 h hA hfaith haA ha1

@[expose] def D_2_22 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → ∀ A ∈ QhatStar X, ¬ IsCyclic ↥A →
      D217Alt5 X r ∨ D217Alt6 X r

theorem as_D_2_22 : D_2_22 := by
  intro V _ _ hV X r h A hA hnc
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := CFSG.Quasithin.QhatStar_spec hA
  have hrk : 1 < rk A := CFSG.Quasithin.one_lt_rk_of_not_isCyclic hA2.isElemAbelian2 hA2.ne_bot hnc
  obtain ⟨-, hr, -⟩ := CFSG.Quasithin.D2_19 hV h hA hrk
  obtain ⟨-, h6⟩ := CFSG.Quasithin.D2_22 hV h hA hrk
  rcases h6 with h1 | h2 | h3 | h4 | h5 | h6
  · exfalso; rcases h1.2.2 with h | h <;> rw [hr] at h <;> norm_num at h
  · exfalso; have := h2.2.2; rw [hr] at this; norm_num at this
  · exfalso; have := h3.2.2.2.2; rw [hr] at this; norm_num at this
  · exfalso; have := h4.2.2.2.2.2; rw [hr] at this; norm_num at this
  · exact Or.inl h5
  · exact Or.inr h6

@[expose] def D_2_23 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → (∀ B ∈ QhatStar X, Nat.card B = 2) →
      ∀ A ∈ QhatStar X, (cmt (pCoreOf 5 X) A) ≠ ⊥ → D217Alt2 X r

theorem as_D_2_23 : D_2_23 := by
  intro V _ _ hV X r h hcyc A hA hne
  exact CFSG.Quasithin.D2_23 hV h hcyc hA hne

@[expose] def D_2_24 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), D217Hyp X r → (∀ B ∈ QhatStar X, Nat.card B = 2) →
      r = 1 → D217Alt1 X r

theorem as_D_2_24 : D_2_24 := by
  intro V _ _ hV X r h hcyc hr
  obtain ⟨hiso, hrk⟩ := CFSG.Quasithin.D2_24 hV h hcyc hr
  exact ⟨hiso, by rw [hrk, hr]; norm_num, Or.inl hr⟩

@[expose] def D_2_25 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CycCtx X → (X1set X).Nonempty → D217Alt3 X 2

theorem as_D_2_25 : D_2_25 := by
  intro V _ _ hV X c hne
  have hfit := CFSG.Quasithin.CycCtx.fittingOf_eq hV c
  have hne' : (Xk X 1).Nonempty := by
    obtain ⟨Y, hY1, hY2, hY3⟩ := hne
    exact ⟨Y, by rw [hfit]; exact hY1, by simpa using hY2, by simpa using hY3⟩
  obtain ⟨h1, h2, h3, h4⟩ := CFSG.Quasithin.D2_25 hV c hne'
  exact ⟨h1, h2, h3, h4, rfl⟩

@[expose] def D_2_26 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CycCtx X → X1set X = ∅ →
      ∀ (Y₀ : Subgroup (MulAut V)) (t : MulAut V), Y₀ ≤ fittingOf X → Y₀ ≠ ⊥ → IsCyclic ↥Y₀ →
        t ∈ TInv X → (∀ y ∈ Y₀, t * y * t⁻¹ = y⁻¹) →
          Y₀ ∈ Yset X ∧
          (commV (Subgroup.zpowers t) = commSub (commV Y₀) (Subgroup.zpowers t) ∧
            commSub (fixV Y₀) (Subgroup.zpowers t) = ⊥ ∧
            ∀ y ∈ X, (∀ z ∈ Y₀, y * z = z * y) → (∀ u ∈ commV Y₀, y u = u) → y * t = t * y) ∧
          commV (⨆ Y ∈ Yset X, Y) = ⊤

theorem as_D_2_26 : D_2_26 := by
  intro V _ _ hV X c hX1 Y₀ t hY₀F hY₀ne hcyc ht hinv
  have hfit := CFSG.Quasithin.CycCtx.fittingOf_eq hV c
  have hX1' := Xk_one_false c hV hX1
  obtain ⟨x, hxY⟩ := exists_gen_of_cyclic hcyc
  subst hxY
  have hxmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have hx1 : x ≠ 1 := fun h => hY₀ne (by rw [h, Subgroup.zpowers_one_eq_bot])
  have hxR : x ∈ pCoreOf 3 X := by rw [← hfit]; exact hY₀F hxmem
  have hxinv : t * x * t⁻¹ = x⁻¹ := hinv x hxmem
  obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.Quasithin.inverted_data hV c hX1' ht hxR hx1 hxinv
  refine ⟨⟨Subgroup.zpowers_le.mpr hxR, by rw [Nat.card_zpowers, h1], h2⟩, ⟨h5.symm, ?_, ?_⟩, ?_⟩
  · rw [commSub_eq_bot_iff]
    exact fun w hw => CFSG.Quasithin.mem_fixV_zpowers_iff.mpr (h3 w hw)
  · intro y hy hyc hyu
    exact h4 y hy (hyc x hxmem) hyu
  ·
    set H : Subgroup (MulAut V) := ⨆ Y ∈ Yset X, Y with hH
    have hHle : H ≤ pCoreOf 3 X := iSup₂_le fun Y hY => hY.1
    have hodd : Odd (Nat.card H) := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have h3p : IsPGroup 3 ↥(pCoreOf 3 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
      have hP : Odd (Nat.card (pCoreOf 3 X)) := CFSG.Quasithin.odd_card_of_isPGroup_odd (by norm_num) h3p
      exact hP.of_dvd_nat (Subgroup.card_dvd_of_le hHle)
    have hdec := CFSG.Quasithin.coprime_decomp hodd hV (W := (⊤ : Subgroup V))
      (fun _ _ w _ => Subgroup.mem_top _)
    have hfix : fixV H = ⊥ := by
      refine CFSG.Quasithin.eq_bot_of_le_fixV_inverted hV c hX1' (W := fixV H) ?_
      intro y hy hy1 ⟨t', ht', hinv'⟩ w hw
      have hmem : Subgroup.zpowers y ∈ Yset X := zpowers_mem_Yset c hV hX1' ht' hy hy1 hinv'
      have hle : Subgroup.zpowers y ≤ H := le_iSup₂_of_le (Subgroup.zpowers y) hmem le_rfl
      exact CFSG.Quasithin.fixV_anti hle hw
    have := hdec.1
    rw [top_inf_eq, hfix, sup_bot_eq] at this
    rw [CFSG.Quasithin.commV_eq_commSub]
    exact this

@[expose] def D_2_27 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CycCtx X → X1set X = ∅ →
      ∀ (Y₀ : Subgroup (MulAut V)) (t : MulAut V), Y₀ ≤ fittingOf X → Y₀ ≠ ⊥ → IsCyclic ↥Y₀ →
        t ∈ TInv X → (∀ y ∈ Y₀, t * y * t⁻¹ = y⁻¹) →
          (Nat.card (pCoreOf 3 X) = 3 ∨ Yset X = {Y₀}) → D217Alt1 X 2

theorem as_D_2_27 : D_2_27 := by
  intro V _ _ hV X c hX1 Y₀ t hY₀F hY₀ne hcyc ht hinv hcase
  have hfit := CFSG.Quasithin.CycCtx.fittingOf_eq hV c
  have hX1' := Xk_one_false c hV hX1
  obtain ⟨x, hxY⟩ := exists_gen_of_cyclic hcyc
  have hxmem : x ∈ Y₀ := hxY ▸ Subgroup.mem_zpowers x
  have hx1 : x ≠ 1 := fun h => hY₀ne (by rw [← hxY, h, Subgroup.zpowers_one_eq_bot])
  have hxR : x ∈ pCoreOf 3 X := by rw [← hfit]; exact hY₀F hxmem
  have hxinv : t * x * t⁻¹ = x⁻¹ := hinv x hxmem
  have hY₀set : Y₀ ∈ Yset X := by
    have := zpowers_mem_Yset c hV hX1' ht hxR hx1 hxinv
    rwa [hxY] at this
  have hY₀inv : Y₀ ∈ Yinv X := ⟨hY₀set.1, hY₀set.2.1, t, ht, hinv⟩
  have hYinvset : ∀ Y ∈ Yinv X, Y ∈ Yset X := by
    intro Y hY
    obtain ⟨hYR, hYc, t', ht', hinv'⟩ := hY
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨y, hyY, hy1, hyz, hyord⟩ := CFSG.Quasithin.exists_generator_of_prime_card (p := 3) hYc
    have := zpowers_mem_Yset c hV hX1' ht' (hYR hyY) hy1 (hinv' y hyY)
    rwa [hyz] at this
  have hone : ∀ Y ∈ Yinv X, Y = Y₀ := by
    intro Y hY
    rcases hcase with hR | hset
    · have h1 : Y = pCoreOf 3 X :=
        Subgroup.eq_of_le_of_card_ge hY.1 (by rw [hR, hY.2.1])
      have h2 : Y₀ = pCoreOf 3 X :=
        Subgroup.eq_of_le_of_card_ge hY₀set.1 (by rw [hR, hY₀set.2.1])
      rw [h1, h2]
    · have := hYinvset Y hY
      rw [hset] at this
      exact this
  obtain ⟨hiso, hrk⟩ := CFSG.Quasithin.D2_27 hV c hX1' hY₀inv hone
  exact ⟨hiso, by rw [hrk]; norm_num, Or.inr rfl⟩

@[expose] def D_2_28 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CycCtx X → X1set X = ∅ →
      ∀ (Y₀ : Subgroup (MulAut V)) (t : MulAut V), Y₀ ≤ fittingOf X → Y₀ ≠ ⊥ → IsCyclic ↥Y₀ →
        t ∈ TInv X → (∀ y ∈ Y₀, t * y * t⁻¹ = y⁻¹) →
          1 < (Yset X).ncard → Y₀ < pCoreOf 3 X →
            (Y₀ ⊓ (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) ⊓
                Subgroup.centralizer ({t} : Set (MulAut V))) = ⊥ ∧
              Y₀ ⊔ (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) ⊓
                Subgroup.centralizer ({t} : Set (MulAut V))) =
                pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V))) ∧
            (IsElemAbelian 3 (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V))) ∧
              Nat.card ↥(pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V))) = 9) ∧
            (commV (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V))) =
                commV (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) ⊓
                  Subgroup.centralizer ({t} : Set (MulAut V))) ∧
              rk (commV (pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)))) = 6) ∧
            {Y | Y ∈ Yset X ∧ Y ≤ pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V))} =
              {Y | Y ≤ pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) ∧
                Nat.card Y = 3 ∧ Y ≠ pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) ⊓
                  Subgroup.centralizer ({t} : Set (MulAut V))}

theorem as_D_2_28 : D_2_28 := by
  intro V _ _ hV X c hX1 Y₀ t hY₀F hY₀ne hcyc ht hinv h2 hlt
  obtain ⟨x, z, hxY, hp, hg, -⟩ := d228_setup hV c hX1 hY₀F hY₀ne hcyc ht hinv h2
  subst hxY
  have hX1' := Xk_one_false c hV hX1
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := CFSG.Quasithin.Good.E9 hV c hX1' hp hg
  have hP := inf_centralizer_zpowers_eq_aux X x
  have hzP : z ∈ centR X x := hg.hz
  have hE9 := CFSG.Quasithin.E9_data hxo hzo hxz hne
  have hZ : centR X x ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro p hp'
      obtain ⟨hpP, hpt'⟩ := Subgroup.mem_inf.mp hp'
      have hpt : t * p = p * t := (Subgroup.mem_centralizer_singleton_iff.mp hpt').symm
      obtain ⟨i, j, hij⟩ := hE9.2.2 p (hsup ▸ hpP)
      have hti : t * x ^ i * t⁻¹ = (x ^ i)⁻¹ := by
        exact hinv _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i)
      have htz : t * z * t⁻¹ = z := by
        have := hg.tz
        rw [this]; group
      have htj : t * z ^ j * t⁻¹ = z ^ j := by
        rw [← conj_zpow, htz]
      have hpp : t * p * t⁻¹ = p := by
        rw [hpt]; group
      have hai : (x ^ i) = (x ^ i)⁻¹ := by
        have h3 : t * p * t⁻¹ = (x ^ i)⁻¹ * z ^ j := by
          rw [hij]
          calc t * (x ^ i * z ^ j) * t⁻¹ = (t * x ^ i * t⁻¹) * (t * z ^ j * t⁻¹) := by group
            _ = (x ^ i)⁻¹ * z ^ j := by rw [hti, htj]
        rw [hpp, hij] at h3
        exact mul_right_cancel h3
      have hx3 : x ^ i = 1 := by
        have h1 : (x ^ i) ^ 2 = 1 := by
          calc (x ^ i) ^ 2 = x ^ i * x ^ i := by group
            _ = x ^ i * (x ^ i)⁻¹ := by rw [← hai]
            _ = 1 := by group
        have h3 : (x ^ i) ^ 3 = 1 := by
          have := orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i)
          rw [hxo] at this
          exact orderOf_dvd_iff_pow_eq_one.mp this
        calc x ^ i = (x ^ i) ^ 3 * ((x ^ i) ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3, h1]; group
      rw [hij, hx3, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzP,
        Subgroup.mem_centralizer_singleton_iff.mpr hg.tz.symm⟩)
  rw [hP, hZ]
  refine ⟨⟨?_, hsup⟩, ⟨?_, hg.card⟩, ⟨?_, ?_⟩, ?_⟩
  · exact inf_eq_bot_of_card_three_aux (by rw [Nat.card_zpowers, hxo])
      (by rw [Nat.card_zpowers, hzo]) hne
  · exact ⟨⟨⟨fun a b => Subtype.ext (hg.comm a.1 a.2 b.1 b.2)⟩⟩, hg.cube⟩
  · exact hg.hU
  · rw [hg.hU]; exact hg.rk6
  · ext Y
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hYR, hY3, hY4⟩, hYP⟩
      refine ⟨hYP, hY3, fun hYZ => ?_⟩
      rw [hYZ, hg.rk6] at hY4
      omega
    · rintro ⟨hYP, hY3, hYne⟩
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨w, hwY, hw1, hwz, -⟩ := CFSG.Quasithin.exists_generator_of_prime_card (p := 3) hY3
      have hw4 := hg.rk4 w (hYP hwY) hw1 (by rw [hwz]; exact hYne)
      rw [hwz] at hw4
      exact ⟨⟨hYP.trans (inf_le_left : centR X x ≤ pCoreOf 3 X), hY3, hw4⟩, hYP⟩

@[expose] def D_2_29 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CycCtx X → X1set X = ∅ →
      ∀ (Y₀ : Subgroup (MulAut V)) (t : MulAut V), Y₀ ≤ fittingOf X → Y₀ ≠ ⊥ → IsCyclic ↥Y₀ →
        t ∈ TInv X → (∀ y ∈ Y₀, t * y * t⁻¹ = y⁻¹) →
          1 < (Yset X).ncard → Y₀ < pCoreOf 3 X →
            pCoreOf 3 X ⊓ Subgroup.centralizer (Y₀ : Set (MulAut V)) < pCoreOf 3 X

theorem as_D_2_29 : D_2_29 := by
  intro V _ _ hV X c hX1 Y₀ t hY₀F hY₀ne hcyc ht hinv h2 hlt
  obtain ⟨x, z, hxY, hp, hg, htwo⟩ := d228_setup hV c hX1 hY₀F hY₀ne hcyc ht hinv h2
  subst hxY
  have hX1' := Xk_one_false c hV hX1
  rw [inf_centralizer_zpowers_eq_aux X x]
  exact lt_of_le_of_ne inf_le_left (CFSG.Quasithin.D2_29 hV c hX1' hg htwo)

end CFSG.ASVolI

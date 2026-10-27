module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def FiveShape (X : Type) [Group X] : Prop :=
  (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsAlt 5 X ∨ IsPSL 3 2 1 X

@[expose] def FourList (X : Type) [Group X] : Prop :=
  (∃ n, 2 ≤ n ∧ (IsPSL 2 2 n X ∨ IsSz n X ∨ IsPSU 3 2 n X)) ∨ (∃ n, 1 ≤ n ∧ IsPSL 3 2 n X) ∨
    (∃ n, 2 ≤ n ∧ IsPSp4 2 n X) ∨ IsAlt 6 X ∨ (∃ n, 2 ≤ n ∧ IsG2 2 n X) ∨ IsPSU 3 3 1 X ∨
    IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X ∨ IsAlt 7 X ∨ IsSporadic .M22 X

@[expose] def FourListFine (X : Type) [Group X] : Prop :=
  FourList (X ⧸ Subgroup.center X) ∧
    (IsAlt 7 (X ⧸ Subgroup.center X) → ¬ IsHat X ↥(alternatingGroup (Fin 7))) ∧
    (IsSporadic .M22 (X ⧸ Subgroup.center X) →
      IsSporadic .M22 X ∨ IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22))

@[expose] def ModFourRest {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  (V = orbSup T V ∧ IsFFModule (autSec (L ⊔ T) V (fixV Mp))) ∨ D310Two T L V

@[expose] def ModFour {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  M ≤ stabSub V ∨ ModFourRest Mp T L V

@[expose] def ModFiveA {W : Type} [CommGroup W] (Mp L : Subgroup (MulAut W)) (V : Subgroup W) :
    Prop :=
  commV L = V ∧
    ((∃ n, BinaryNaturalSL L V (V ⊓ fixV Mp) 2 n) ∨ BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1 ∨
      (∃ f, BinaryNaturalSz L V (V ⊓ fixV Mp) f) ∨
      (∃ a, 1 ≤ a ∧ BinaryOrthogonalFour L V (V ⊓ fixV Mp) a) ∨
      AlternatingNatural L V (V ⊓ fixV Mp) 5)

@[expose] def ModFiveB {W : Type} [CommGroup W] (T L : Subgroup (MulAut W)) (V : Subgroup W) :
    Prop :=
  IsPSL 3 2 1 ↥L ∧ (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
    (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
      IsIntDirect V (V.map s.toMonoidHom) (commV L)) ∧ Nat.card ↥V = 2 ^ 3

@[expose] def ModFiveIiiAB {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
    commV L ≤ fixV (conjAutSub t L) ∧
    ((ModFiveA Mp L V ∧ FiveShape ↥L) ∨ ModFiveB T L V)

@[expose] def ModFiveIii {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
    commV L ≤ fixV (conjAutSub t L) ∧
    ((ModFiveA Mp L V ∧ FiveShape ↥L) ∨ ModFiveB T L V ∨ D321Two L ∨ D321Three Mp L)

theorem ModFiveIiiAB.toIii {W : Type} [CommGroup W] [Finite W] {Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t : MulAut W} (h : ModFiveIiiAB Mp T L V t) : ModFiveIii Mp T L V t :=
  ⟨h.1, h.2.1, by
    rcases h.2.2 with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)⟩

@[expose] def ModFive {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  (V = ⊤ ∧ M ≤ stabSub V ∧ ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n) ∨
  (V = ⊤ ∧ M ≤ stabSub V ∧ IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V)) ∨
  ModFiveIii Mp T L V t ∨ ModFiveIii Mp T (conjAutSub t L) V t⁻¹

@[expose] def ModFiveTop {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  (V = ⊤ ∧ M ≤ stabSub V ∧ ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n) ∨
  (V = ⊤ ∧ M ≤ stabSub V ∧ IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V)) ∨
  ModFiveIiiAB Mp T L V t ∨ ModFiveIiiAB Mp T (conjAutSub t L) V t⁻¹

theorem ModFiveTop.toModFive {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t : MulAut W} (h : ModFiveTop M Mp T L V t) : ModFive M Mp T L V t := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h.toIii))
  · exact Or.inr (Or.inr (Or.inr h.toIii))

@[expose] def Insp5a : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D31 M Mp T L V → V ∈ IrrPlus Mp (⊤ : Subgroup W) → t ∈ T →
    t ∉ Subgroup.normalizer (L : Set (MulAut W)) → Mp = L ⊔ conjAutSub t L →
    (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) → commV L = V →
    qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) → A38Types ↥L →
    FiveShape ↥L ∧ ModFiveA Mp L V

@[expose] def Insp4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
      qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) →
      FourList (↥L ⧸ Subgroup.center ↥L)

theorem fiveShape_congr {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : FiveShape X) :
    FiveShape Y := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | h | h
  · exact Or.inl ⟨n, isPSL_congr φ h⟩
  · exact Or.inr (Or.inl ⟨n, isSz_congr φ h⟩)
  · exact Or.inr (Or.inr (Or.inl (isAlt_congr φ h)))
  · exact Or.inr (Or.inr (Or.inr (isPSL_congr φ h)))

section Elementary

variable {W : Type} [CommGroup W]

theorem mem_stabSub_top (g : MulAut W) : g ∈ stabSub (⊤ : Subgroup W) := fun _ => Iff.rfl

theorem le_stabSub_top (X : Subgroup (MulAut W)) : X ≤ stabSub (⊤ : Subgroup W) :=
  fun g _ => mem_stabSub_top g

theorem qhatOf_autSub_congr [Finite W] {X : Subgroup (MulAut W)} {U U' : Subgroup W} (h : U = U') :
    qhatOf (autSub X U) = qhatOf (autSub X U') := by
  subst h
  rfl

theorem le_stabSub_commV_self (L : Subgroup (MulAut W)) : L ≤ stabSub (commV L) := by
  intro x hx u
  have key : ∀ y ∈ L, ∀ w ∈ commV L, y w ∈ commV L := by
    intro y hy w hw
    refine Subgroup.closure_induction (p := fun w _ => y w ∈ commV L) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, hl, v, rfl⟩
      have : y (l v * v⁻¹) = (y * l * y⁻¹) (y v) * (y v)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [this]
      exact Subgroup.subset_closure ⟨y * l * y⁻¹, L.mul_mem (L.mul_mem hy hl) (L.inv_mem hy), y v,
        rfl⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commV L).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commV L).inv_mem ha
  exact ⟨fun h => by simpa using key x⁻¹ (L.inv_mem hx) _ h, fun h => key x hx u h⟩

theorem le_stabSub_of_le_fixV {X : Subgroup (MulAut W)} {U : Subgroup W} (h : U ≤ fixV X) :
    X ≤ stabSub U := by
  intro g hg u
  constructor
  · intro hgu
    have h1 : g (g u) = g u := h hgu g hg
    have h2 : g u = u := g.injective h1
    rwa [h2] at hgu
  · intro hu
    rw [h hu g hg]
    exact hu

theorem resHom_top_injective : Function.Injective (resHom (⊤ : Subgroup W)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_resHom, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, mem_centSub] at hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext w
  exact hg w trivial

noncomputable def autSubTopEquiv (L : Subgroup (MulAut W)) : ↥(autSub L (⊤ : Subgroup W)) ≃* ↥L :=
  (Subgroup.equivMapOfInjective (L.subgroupOf (stabSub (⊤ : Subgroup W))) (resHom ⊤)
      resHom_top_injective).symm.trans (Subgroup.subgroupOfEquivOfLe (le_stabSub_top L))

theorem isPSL_of_autSub_top {n p e : ℕ} {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : U = ⊤)
    (h : IsPSL n p e ↥(autSub L U)) : IsPSL n p e ↥L := by
  subst hU
  exact isPSL_congr (autSubTopEquiv L) h

theorem conjAutSub_mem_cComp {M L : Subgroup (MulAut W)} (hL : L ∈ cComp M) {t : MulAut W}
    (ht : t ∈ M) : conjAutSub t L ∈ cComp M := by
  have h1 := cComp_map_mulEquiv (MulAut.conj t) hL
  have h2 : M.map (MulAut.conj t).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  rw [h2] at h1
  exact h1

theorem mem_conjAutSub_iff {L : Subgroup (MulAut W)} {t x : MulAut W} :
    x ∈ conjAutSub t L ↔ t⁻¹ * x * t ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hl
  · intro h
    refine ⟨t⁻¹ * x * t, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conjClosure_conjAutSub {L T : Subgroup (MulAut W)} {t : MulAut W} (ht : t ∈ T) :
    conjClosure (conjAutSub t L) T = conjClosure L T := by
  apply le_antisymm
  · refine conjClosure_le fun s hs z hz => ?_
    rw [mem_conjAutSub_iff] at hz
    have := mem_conjClosure (Z := L) (H := T) (T.mul_mem hs ht) hz
    have e : s * z * s⁻¹ = (s * t) * (t⁻¹ * z * t) * (s * t)⁻¹ := by group
    rw [e]
    exact this
  · refine conjClosure_le fun s hs z hz => ?_
    have hz' : t * z * t⁻¹ ∈ conjAutSub t L := by
      rw [mem_conjAutSub_iff]
      simpa [mul_assoc] using hz
    have := mem_conjClosure (Z := conjAutSub t L) (H := T) (T.mul_mem hs (T.inv_mem ht)) hz'
    have e : s * z * s⁻¹ = (s * t⁻¹) * (t * z * t⁻¹) * (s * t⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem D31.conj {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D31 M Mp T L V)
    {t : MulAut W} (ht : t ∈ T) : D31 M Mp T (conjAutSub t L) V :=
  { hD with
    comp := conjAutSub_mem_cComp hD.comp (hD.sylow.1 ht)
    quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)
      hD.quasi
    Mp_eq := hD.Mp_eq.trans (conjClosure_conjAutSub ht).symm }

theorem a38Types_conjAutSub {L : Subgroup (MulAut W)} (t : MulAut W) (h : A38Types ↥L) :
    A38Types ↥(conjAutSub t L) :=
  a38Types_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective) h

theorem le_stabSub_map {Mp T : Subgroup (MulAut W)} (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    {t : MulAut W} (ht : t ∈ T) {U : Subgroup W} (hU : Mp ≤ stabSub U) :
    Mp ≤ stabSub (U.map t.toMonoidHom) := by
  intro x hx u
  have hx' : t⁻¹ * x * t ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn ht) x).mp hx
  have key : ∀ y ∈ Mp, ∀ w ∈ U, y (t w) ∈ U.map t.toMonoidHom := by
    intro y hy w hw
    have hy' : t⁻¹ * y * t ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn ht) y).mp hy
    refine ⟨(t⁻¹ * y * t) w, (hU hy' w).2 hw, ?_⟩
    simp [MulAut.mul_apply]
  have hinj : ∀ w : W, t⁻¹ w ∈ U ↔ w ∈ U.map t.toMonoidHom := by
    intro w
    constructor
    · intro h
      exact ⟨t⁻¹ w, h, by simp⟩
    · rintro ⟨u', hu', rfl⟩
      simpa using hu'
  constructor
  · intro hxu
    have h1 : t⁻¹ (x u) ∈ U := (hinj _).mpr hxu
    have h2 : t⁻¹ (x u) = (t⁻¹ * x * t) (t⁻¹ u) := by simp [MulAut.mul_apply]
    rw [h2] at h1
    have h3 : t⁻¹ u ∈ U := ((hU hx') (t⁻¹ u)).mp h1
    exact (hinj u).mp h3
  · intro hu
    have h1 : t⁻¹ u ∈ U := (hinj u).mpr hu
    exact (hinj _).mp (by
      have h2 : t⁻¹ (x u) = (t⁻¹ * x * t) (t⁻¹ u) := by simp [MulAut.mul_apply]
      rw [h2]
      exact (hU hx' _).mpr h1)

end Elementary

section FourCore

variable {W : Type} [CommGroup W] [Finite W]

theorem mod4_core (h310 : D310) (h391 : D391) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {A : Subgroup (MulAut W)} (hD : D31 M Mp T L V) (hirr : V ∈ IrrPlusOn Mp (orbSup T V) T)
    (hMp : Mp = L) (hA : QOff Mp T A (orbSup T V)) : ModFour M Mp T L V := by
  have hstd : D3Std M Mp T L V := ⟨hD, hA.qhat_VT hD.exp, hirr⟩
  have hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) := hA.qhat_M hD.sylow.1
  rcases h310 W M Mp T L V hstd hMp hqM with hT | h2
  · have hVT : orbSup T V = V := orbSup_eq_of_stab hT
    rcases h391 W M Mp T L V hMp hstd hqM (Or.inl hVT.symm) A
      ⟨hA.le.trans hD.sylow.1, hA.ne, hA.elem⟩ hA.le
      (commSeries_eq_bot_of_le (by norm_num) hA.quad) hA.rat hA.faithMp with htop | ⟨_, hFF⟩
    · left
      have : V = ⊤ := hVT.symm.trans htop
      rw [this]
      exact le_stabSub_top M
    · exact Or.inr (Or.inl ⟨hVT.symm, hFF⟩)
  · exact Or.inr (Or.inr h2)

end FourCore

section FiveCore

variable {W : Type} [CommGroup W] [Finite W]

theorem modFiveIiiAB_of_D36Concl (hI5 : Insp5a) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) (hVT : orbSup T V = ⊤) (hc : D36Concl Mp T L V t) :
    ModFiveIiiAB Mp T L V t := by
  obtain ⟨hV0, ⟨hsum, hle⟩, hq, hab⟩ := hc
  have hU : commSub (orbSup T V) L = commV L := by rw [hVT, ← commV_eq_commSub]
  have hU' : commSub (⊤ : Subgroup W) L = commV L := (commV_eq_commSub L).symm
  have hsum' : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ := by
    have := hsum
    rw [hVT, top_inf_eq, hU'] at this
    exact this
  have hle' : commV L ≤ fixV (conjAutSub t L) := by
    intro u hu g hg
    exact hle u (hU ▸ hu) g hg
  refine ⟨hsum', hle', ?_⟩
  rcases hab with hUV | ⟨hpsl, hs1, hs2, hcard⟩
  · refine Or.inl ?_
    have hUV' : commV L = V := hU ▸ hUV
    obtain ⟨hshape, hA⟩ := hI5 W M Mp T L V t hD hD.irr htT htL hMp hV0 hUV' (by
      have := hq
      rwa [qhatOf_autSub_congr hUV] at this) hL38
    exact ⟨hA, hshape⟩
  · refine Or.inr ⟨isPSL_of_autSub_top hVT hpsl, hs1, ?_, hcard⟩
    intro s hs hsN hsV
    exact hU ▸ hs2 s hs hsN hsV

omit [Finite W] in
theorem conjAutSub_inv_conjAutSub (L : Subgroup (MulAut W)) (t : MulAut W) :
    conjAutSub t⁻¹ (conjAutSub t L) = L := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : t⁻¹ * (t⁻¹⁻¹ * x * t⁻¹) * t = x := by group
  rw [this]

omit [Finite W] in
theorem not_mem_normalizer_conjAutSub {L : Subgroup (MulAut W)} {t : MulAut W}
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    t⁻¹ ∉ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
  intro hmem
  apply htL
  have h6 : conjAutSub t⁻¹ (conjAutSub t L) = conjAutSub t L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
  rw [conjAutSub_inv_conjAutSub] at h6
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h6.symm

theorem D36cConcl.toD36Concl (hB : D36B48q) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (std : D3Std M Mp T L V) (hlt : V < orbSup T V) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ))
    (hc : D36cConcl Mp T L V t) : D36Concl Mp T L V t := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  refine ⟨h0, h1, h2, ?_⟩
  rcases h3 with hU | ⟨hpsl, hs1, hs2, hcard⟩
  · exact Or.inl hU
  · right
    have hC : V ⊓ fixV Mp = ⊥ := hB W M Mp T L V t std hlt ht htn hMp h0 hq hpsl hs1
    refine ⟨hpsl, hs1, fun s hs hsN hsV => ?_, ?_⟩
    · obtain ⟨hU, hsum⟩ := hs2 s hs hsN hsV
      refine ⟨hU.symm, ?_⟩
      have h1' : V ⊓ V.map s.toMonoidHom ≤ commSub (orbSup T V) L ⊓ fixV Mp := by
        intro x hx
        exact hsum.2 ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
      have h2' : V ⊓ V.map s.toMonoidHom ≤ V ⊓ fixV Mp := fun x hx => ⟨hx.1, (h1' hx).2⟩
      exact le_bot_iff.mp (hC ▸ h2')
    · rw [hC, Subgroup.card_bot, mul_one] at hcard
      exact hcard

theorem mod5_of_top (h36 : D36) (h37 : D37) (hI5 : Insp5a)
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {A : Subgroup (MulAut W)} {t : MulAut W}
    (hD : D31 M Mp T L V) (hirr : V ∈ IrrPlusOn Mp (orbSup T V) T) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) (hA : QOff Mp T A (orbSup T V)) (h1 : orbSup T V = ⊤) :
    ModFiveTop M Mp T L V t := by
  have hstd : D3Std M Mp T L V := ⟨hD, hA.qhat_VT hD.exp, hirr⟩
  have hqq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) := hA.qOf_VT hD.exp
  by_cases hVeq : V = orbSup T V
  · have hVtop : V = ⊤ := hVeq.trans h1
    have hM : M ≤ stabSub V := hVtop ▸ le_stabSub_top M
    rcases h37 W M Mp T L V hstd hVeq t htT htL hMp with ⟨n, hn1, hn2⟩ | ⟨hn1, hn2⟩
    · exact Or.inl ⟨hVtop, hM, n, hn1, hn2⟩
    · exact Or.inr (Or.inl ⟨hVtop, hM, hn1, hn2⟩)
  · have hlt : V < orbSup T V := lt_of_le_of_ne (le_orbSup T V) hVeq
    rcases h36.1 W M Mp T L V hstd hlt t htT htL hMp with hc | hc
    · exact Or.inr (Or.inr (Or.inl (modFiveIiiAB_of_D36Concl hI5 hD htT htL hMp hL38 h1
        (hc.toD36Concl h36.2 hstd hlt htT htL hMp hqq))))
    · have hD' : D31 M Mp T (conjAutSub t L) V := hD.conj htT
      have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
        rw [conjAutSub_inv_conjAutSub, sup_comm]
        exact hMp
      have hstd' : D3Std M Mp T (conjAutSub t L) V := ⟨hD', hstd.qhat, hstd.irrT⟩
      exact Or.inr (Or.inr (Or.inr (modFiveIiiAB_of_D36Concl hI5 hD' (T.inv_mem htT)
        (not_mem_normalizer_conjAutSub htL) hMp' (a38Types_conjAutSub t hL38) h1
        (hc.toD36Concl h36.2 hstd' hlt (T.inv_mem htT) (not_mem_normalizer_conjAutSub htL)
          hMp' hqq))))

theorem mod5_core (h36 : D36) (h37 : D37) (h321 : D321) (hI5 : Insp5a)
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {A : Subgroup (MulAut W)} {t : MulAut W}
    (hD : D31 M Mp T L V) (hirr : V ∈ IrrPlusOn Mp (orbSup T V) T) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) (hA : QOff Mp T A (orbSup T V)) : ModFive M Mp T L V t := by
  have hstd : D3Std M Mp T L V := ⟨hD, hA.qhat_VT hD.exp, hirr⟩
  have hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) := hA.qhat_M hD.sylow.1
  rcases h321 W M Mp T L V hstd t htT htL hMp hqM A hA.le hA.ne hA.elem hA.quad hA.rat
      hA.faithMp hA.faithVT with h1 | ⟨hsum, hle, h2 | h3⟩
  · exact (mod5_of_top h36 h37 hI5 hD hirr htT htL hMp hL38 hA h1).toModFive
  · exact Or.inr (Or.inr (Or.inl ⟨hsum, hle, Or.inr (Or.inr (Or.inl h2))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hsum, hle, Or.inr (Or.inr (Or.inr h3))⟩))

theorem ModFiveIii.fiveShape {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h : ModFiveIii Mp T L V t) : FiveShape ↥L := by
  obtain ⟨-, -, hh⟩ := h
  rcases hh with ⟨-, hs⟩ | hB | hC | hD
  · exact hs
  · exact Or.inr (Or.inr (Or.inr hB.1))
  · exact Or.inr (Or.inr (Or.inr hC.1))
  · obtain ⟨n, hn, -⟩ := hD
    exact Or.inl ⟨n, hn⟩

theorem ModFive.fiveShape {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (h : ModFive M Mp T L V t) : FiveShape ↥L := by
  rcases h with ⟨hV, -, n, hpsl, -⟩ | ⟨hV, -, hpsl, -⟩ | h | h
  · exact Or.inl ⟨n, isPSL_of_autSub_top hV hpsl⟩
  · exact Or.inr (Or.inr (Or.inr (isPSL_of_autSub_top hV hpsl)))
  · exact h.fiveShape
  · exact fiveShape_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm h.fiveShape

end FiveCore

end CFSG.Quasithin

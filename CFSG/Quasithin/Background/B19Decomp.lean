module

public import CFSG.Quasithin.Background.B19Normal

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def FAll (X Φ : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (t) (_ : t ∈ tvSet X Φ), FOf Φ t

@[expose] def GAll (X Φ : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (t) (_ : t ∈ tvSet X Φ), GOf Φ t

theorem FOf_le_FAll {X Φ : Subgroup (MulAut V)} {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    FOf Φ t ≤ FAll X Φ :=
  le_iSup₂_of_le (f := fun (s : MulAut V) (_ : s ∈ tvSet X Φ) => FOf Φ s) t ht le_rfl

theorem GOf_le_GAll {X Φ : Subgroup (MulAut V)} {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ≤ GAll X Φ :=
  le_iSup₂_of_le (f := fun (s : MulAut V) (_ : s ∈ tvSet X Φ) => GOf Φ s) t ht le_rfl

theorem commV_FAll (X Φ : Subgroup (MulAut V)) :
    commV (FAll X Φ) = ⨆ (t) (_ : t ∈ tvSet X Φ), commV (FOf Φ t) := by
  unfold FAll
  rw [commV_iSup]
  congr 1
  ext1 t
  rw [commV_iSup]

theorem Setting.map_conj_FAll_le {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) : (FAll X Φ).map (MulAut.conj g).toMonoidHom ≤ FAll X Φ := by
  unfold FAll
  rw [Subgroup.map_iSup]
  refine iSup_le fun t => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ht => ?_
  rw [hS.FOf_conj hg]
  exact FOf_le_FAll (hS.conj_mem_tvSet hg ht)

theorem Setting.conj_mem_FAll {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) {f : MulAut V} (hf : f ∈ FAll X Φ) : g * f * g⁻¹ ∈ FAll X Φ :=
  hS.map_conj_FAll_le hg ⟨f, hf, rfl⟩

theorem Setting.mem_W {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) : ∀ w ∈ commV (FAll X Φ), g w ∈ commV (FAll X Φ) := by
  rw [commV_eq_commSub]
  exact B1.commSub_smul_mem g (fun y hy => hS.conj_mem_FAll hg hy) (fun _ _ => trivial)

theorem Setting.mem_U {X Φ : Subgroup (MulAut V)} (hS : Setting X Φ) {g : MulAut V}
    (hg : g ∈ X) : ∀ u ∈ fixV (FAll X Φ), g u ∈ fixV (FAll X Φ) := by
  intro u hu
  refine B1.fixV_smul_mem g (fun y hy => ?_) hu
  have := hS.conj_mem_FAll (X.inv_mem hg) hy
  simpa using this

theorem exists_reps (X Φ : Subgroup (MulAut V)) [Finite V] :
    ∃ R : Finset (MulAut V), (∀ r ∈ R, r ∈ tvSet X Φ) ∧
      (∀ r ∈ R, ∀ r' ∈ R, FOf Φ r = FOf Φ r' → r = r') ∧
      ∀ t ∈ tvSet X Φ, ∃ r ∈ R, FOf Φ t = FOf Φ r := by
  obtain ⟨R', hR's, hbij⟩ := Set.exists_subset_bijOn (tvSet X Φ) (FOf Φ)
  refine ⟨(Set.toFinite R').toFinset, fun r hr => hR's ((Set.Finite.mem_toFinset _).1 hr),
    fun r hr r' hr' h => hbij.injOn ((Set.Finite.mem_toFinset _).1 hr)
      ((Set.Finite.mem_toFinset _).1 hr') h, fun t ht => ?_⟩
  obtain ⟨r, hr, hrt⟩ := hbij.surjOn ⟨t, ht, rfl⟩
  exact ⟨r, (Set.Finite.mem_toFinset _).2 hr, hrt.symm⟩

variable [Finite V] {X Φ : Subgroup (MulAut V)}

namespace Setting

variable (hV : ∀ v : V, v ^ 2 = 1) (hS : Setting X Φ)
include hV hS

theorem FAll_le : FAll X Φ ≤ Φ := iSup₂_le fun _ ht => hS.FOf_le hV ht

theorem odd_FAll : Odd (Nat.card (FAll X Φ)) :=
  Odd.of_dvd_nat hS.odd (Subgroup.card_dvd_of_le (hS.FAll_le hV))

theorem decomp_FAll :
    fixV (FAll X Φ) ⊔ commV (FAll X Φ) = ⊤ ∧ fixV (FAll X Φ) ⊓ commV (FAll X Φ) = ⊥ := by
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV (hS.odd_FAll hV) (M := ⊤) (fun _ _ _ _ => trivial)
  rw [commV_eq_commSub]
  simpa using And.intro hsup hinf

theorem GOf_le_centSub_U {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    GOf Φ t ≤ centSub (fixV (FAll X Φ)) := by
  intro g hg u hu
  exact hS.GOf_le_centSub_fixV hV ht hg u (fun y hy => hu y (FOf_le_FAll ht hy))

theorem GAll_le_centSub_U : GAll X Φ ≤ centSub (fixV (FAll X Φ)) :=
  iSup₂_le fun _ ht => hS.GOf_le_centSub_U hV ht

theorem GAll_le : GAll X Φ ≤ X := by
  refine iSup₂_le fun t ht => ?_
  exact sup_le ((hS.FOf_le hV ht).trans hS.le) (Subgroup.zpowers_le.2 ht.1)

theorem exists_match {a : MulAut V}
    (ha : ∀ t ∈ tvSet X Φ, (FOf Φ t).map (MulAut.conj a).toMonoidHom = FOf Φ t) :
    ∃ g ∈ GAll X Φ, (∀ v ∈ commV (FAll X Φ), g v = a v) ∧ ∀ u ∈ fixV (FAll X Φ), g u = u := by
  classical
  obtain ⟨R, hR, hRinj, hRcov⟩ := exists_reps X Φ
  have hpres : ∀ t ∈ tvSet X Φ, ∀ v ∈ commV (FOf Φ t), a v ∈ commV (FOf Φ t) := by
    intro t ht v hv
    have h1 := commV_map_conj a (FOf Φ t)
    rw [ha t ht] at h1
    have : a v ∈ (commV (FOf Φ t)).map a.toMonoidHom := ⟨v, hv, rfl⟩
    rwa [← h1] at this
  have key : ∀ S : Finset (MulAut V), S ⊆ R → ∃ g ∈ ⨆ r ∈ S, GOf Φ r,
      (∀ r ∈ S, ∀ v ∈ commV (FOf Φ r), g v = a v) ∧
      (∀ r ∈ R, r ∉ S → ∀ v ∈ commV (FOf Φ r), g v = v) ∧
      ∀ u ∈ fixV (FAll X Φ), g u = u := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, Subgroup.one_mem _, by simp, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
    | insert r₀ S hr₀ ih =>
      intro hSR
      have hr₀R : r₀ ∈ R := hSR (Finset.mem_insert_self _ _)
      obtain ⟨g, hg, hg1, hg2, hg3⟩ := ih (fun r hr => hSR (Finset.mem_insert_of_mem hr))
      have ht₀ := hR r₀ hr₀R
      have hMa : (commV (FOf Φ r₀)).map a.toMonoidHom = commV (FOf Φ r₀) := by
        rw [← commV_map_conj, ha r₀ ht₀]
      have hast : a ∈ stabSub (commV (FOf Φ r₀)) := by
        intro u
        constructor
        · intro hu
          rw [← hMa] at hu
          obtain ⟨u', hu', hau⟩ := hu
          rw [← a.injective hau]
          exact hu'
        · intro hu
          rw [← hMa]
          exact ⟨u, hu, rfl⟩
      have hmem : resHom (commV (FOf Φ r₀)) ⟨a, hast⟩ ∈
          autSub (GOf Φ r₀) (commV (FOf Φ r₀)) := by
        rw [hS.autSub_GOf hV ht₀]
        trivial
      obtain ⟨g₀, hg₀G, hg₀a⟩ := mem_autSub.1 hmem
      have hg₀v : ∀ v ∈ commV (FOf Φ r₀), (g₀ : MulAut V) v = a v := by
        intro v hv
        have := congrArg (fun φ : MulAut ↥(commV (FOf Φ r₀)) => ((φ ⟨v, hv⟩ : _) : V)) hg₀a
        simpa [resHom_apply] using this
      refine ⟨g * g₀, ?_, ?_, ?_, ?_⟩
      · rw [Finset.iSup_insert]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hg) (Subgroup.mem_sup_left hg₀G)
      · intro r hr v hv
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · rw [MulAut.mul_apply, hg₀v v hv]
          exact hg2 r hr₀R hr₀ _ (hpres r ht₀ v hv)
        · have hrR : r ∈ R := hSR (Finset.mem_insert_of_mem hr)
          have hne : FOf Φ r ≠ FOf Φ r₀ := fun h => hr₀ (hRinj r hrR r₀ hr₀R h ▸ hr)
          rw [MulAut.mul_apply, hS.pair_centSub hV (hR r hrR) ht₀ hne hg₀G v hv]
          exact hg1 r hr v hv
      · intro r hr hrS v hv
        rw [Finset.mem_insert, not_or] at hrS
        have hne : FOf Φ r ≠ FOf Φ r₀ := fun h => hrS.1 (hRinj r hr r₀ hr₀R h)
        rw [MulAut.mul_apply, hS.pair_centSub hV (hR r hr) ht₀ hne hg₀G v hv]
        exact hg2 r hr hrS.2 v hv
      · intro u hu
        rw [MulAut.mul_apply, hS.GOf_le_centSub_U hV ht₀ hg₀G u hu]
        exact hg3 u hu
  obtain ⟨g, hg, hg1, -, hg3⟩ := key R le_rfl
  refine ⟨g, iSup₂_le (fun r hr => GOf_le_GAll (hR r hr)) hg, ?_, hg3⟩
  have hle : commV (FAll X Φ) ≤ MonoidHom.eqLocus g.toMonoidHom a.toMonoidHom := by
    rw [commV_FAll]
    refine iSup₂_le fun t ht v hv => ?_
    obtain ⟨r, hr, hrt⟩ := hRcov t ht
    rw [hrt] at hv
    exact hg1 r hr v hv
  exact fun v hv => hle hv

theorem offender_le {A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    A ≤ GAll X Φ ⊔ ffJP {B | IsFFStarOffender X B}
      (X ⊓ Subgroup.centralizer (FAll X Φ : Set (MulAut V))) := by
  classical
  set W := commV (FAll X Φ) with hW
  set U := fixV (FAll X Φ) with hU
  obtain ⟨hsupUW, hinfUW⟩ := hS.decomp_FAll hV
  have hAX : A ≤ X := hA.1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have hmatch : ∀ a ∈ A, ∃ g ∈ GAll X Φ, (∀ v ∈ W, g v = a v) ∧ ∀ u ∈ U, g u = u :=
    fun a ha => hS.exists_match hV fun t ht => hS.map_conj_FOf hV hA ht ha
  have hdec : ∀ v : V, ∃ u ∈ U, ∃ w ∈ W, u * w = v := fun v =>
    Subgroup.mem_sup.1 (by rw [hsupUW]; trivial)
  have hext : ∀ {f g : MulAut V}, (∀ u ∈ U, f u = g u) → (∀ w ∈ W, f w = g w) → f = g := by
    intro f g hfU hfW
    refine MulEquiv.ext fun v => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := hdec v
    rw [map_mul, map_mul, hfU u hu, hfW w hw]
  let SU : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ X ∧ ∃ a ∈ A, ∀ u ∈ U, g u = a u}
      one_mem' := ⟨X.one_mem, 1, A.one_mem, fun _ _ => rfl⟩
      mul_mem' := by
        rintro g g' ⟨hg, a, ha, hga⟩ ⟨hg', a', ha', hga'⟩
        refine ⟨X.mul_mem hg hg', a * a', A.mul_mem ha ha', fun u hu => ?_⟩
        rw [MulAut.mul_apply, MulAut.mul_apply, hga' u hu, hga _ (hS.mem_U (hAX ha') u hu)]
      inv_mem' := by
        rintro g ⟨hg, a, ha, hga⟩
        refine ⟨X.inv_mem hg, a⁻¹, A.inv_mem ha, fun u hu => ?_⟩
        have h1 : g (a⁻¹ u) = u := by
          rw [hga _ (hS.mem_U (X.inv_mem (hAX ha)) u hu)]
          simp
        calc g⁻¹ u = g⁻¹ (g (a⁻¹ u)) := by rw [h1]
          _ = a⁻¹ u := by simp }
  have hASU : A ≤ SU := fun a ha => ⟨hAX ha, a, ha, fun _ _ => rfl⟩
  have hΓSU : GAll X Φ ≤ SU := fun g hg =>
    ⟨hS.GAll_le hV hg, 1, A.one_mem, fun u hu => hS.GAll_le_centSub_U hV hg u hu⟩
  set Pc := (A ⊔ GAll X Φ) ⊓ centSub W with hPdef
  have hPSU : Pc ≤ SU := inf_le_left.trans (sup_le hASU hΓSU)
  have hPX : Pc ≤ X := fun c hc => (hPSU hc).1
  have hPW : ∀ c ∈ Pc, ∀ w ∈ W, c w = w := fun c hc => hc.2
  have hmatchP : ∀ a ∈ A, ∃ g ∈ GAll X Φ, g⁻¹ * a ∈ Pc ∧ ∀ u ∈ U, (g⁻¹ * a) u = a u := by
    intro a ha
    obtain ⟨g, hg, hgW, hgU⟩ := hmatch a ha
    refine ⟨g, hg, ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hg))
      (Subgroup.mem_sup_left ha), fun w hw => ?_⟩, fun u hu => ?_⟩
    · show g⁻¹ (a w) = w
      rw [← hgW w hw]
      simp
    · show g⁻¹ (a u) = a u
      have h1 : g (a u) = a u := hgU _ (hS.mem_U (hAX ha) u hu)
      calc g⁻¹ (a u) = g⁻¹ (g (a u)) := by rw [h1]
        _ = a u := by simp
  have hAle : A ≤ GAll X Φ ⊔ Pc := by
    intro a ha
    obtain ⟨g, hg, hc, -⟩ := hmatchP a ha
    have : a = g * (g⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hc)
  have hPcent : Pc ≤ Subgroup.centralizer (FAll X Φ : Set (MulAut V)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hcX := hPX hc
    have hfX : f ∈ X := (hS.FAll_le hV).trans hS.le hf
    have hconj : c * f * c⁻¹ = f := by
      refine hext (fun u hu => ?_) (fun w hw => ?_)
      · have h1 : c⁻¹ u ∈ U := hS.mem_U (X.inv_mem hcX) u hu
        show c (f (c⁻¹ u)) = f u
        rw [h1 f hf, hu f hf]
        simp
      · have h1 : c⁻¹ w = w := by
          have := hPW c hc w hw
          calc c⁻¹ w = c⁻¹ (c w) := by rw [this]
            _ = w := by simp
        show c (f (c⁻¹ w)) = f w
        rw [h1, hPW c hc _ (hS.mem_W hfX w hw)]
    calc f * c = c * f * c⁻¹ * c := by rw [hconj]
      _ = c * f := by group
  have hPoff : Pc = ⊥ ∨ IsFFStarOffender X Pc := by
    by_cases hPbot : Pc = ⊥
    · exact Or.inl hPbot
    right
    have hAstab : A ≤ stabSub U := B1.le_stabSub_of_invariant fun a ha => hS.mem_U (hAX ha)
    have hPstab : Pc ≤ stabSub U := B1.le_stabSub_of_invariant fun c hc => hS.mem_U (hPX hc)
    have hPfaith : Pc ⊓ centSub U = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => hext (fun u hu => hc.2 u hu)
        (fun w hw => hPW c hc.1 w hw)
    have hUA : commSub U A ≠ ⊥ := by
      intro h
      rw [commSub_eq_bot_iff] at h
      apply hPbot
      refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => hext (fun u hu => ?_)
        (fun w hw => hPW c hc w hw)
      obtain ⟨-, a, ha, hca⟩ := hPSU hc
      rw [hca u hu, h hu a ha]
      rfl
    have hoffU := B7_1_1 hA (fun a ha => hS.mem_U (hAX ha)) hUA
    have hautEq : autSub Pc U = autSub A U := by
      apply le_antisymm
      · intro φ hφ
        obtain ⟨c, hcP, rfl⟩ := mem_autSub.1 hφ
        obtain ⟨-, a, ha, hca⟩ := hPSU hcP
        refine mem_autSub.2 ⟨⟨a, hAstab ha⟩, ha, ?_⟩
        ext u
        simp only [resHom_apply]
        exact (hca u u.2).symm
      · intro φ hφ
        obtain ⟨a', ha', rfl⟩ := mem_autSub.1 hφ
        obtain ⟨g, -, hc, hcU⟩ := hmatchP a' ha'
        refine mem_autSub.2 ⟨⟨g⁻¹ * a', hPstab hc⟩, hc, ?_⟩
        ext u
        simp only [resHom_apply]
        exact hcU u u.2
    have hPab : IsElemAbelian2 Pc := by
      refine ⟨fun c hc c' hc' => ?_, fun c hc => ?_⟩
      · obtain ⟨-, a, ha, hca⟩ := hPSU hc
        obtain ⟨-, a', ha', hca'⟩ := hPSU hc'
        refine hext (fun u hu => ?_) (fun w hw => ?_)
        · simp only [MulAut.mul_apply]
          rw [hca' u hu, hca _ (hS.mem_U (hAX ha') u hu), hca u hu,
            hca' _ (hS.mem_U (hAX ha) u hu), ← MulAut.mul_apply, ← MulAut.mul_apply,
            hAc a ha a' ha']
        · simp only [MulAut.mul_apply]
          rw [hPW c' hc' w hw, hPW c hc w hw, hPW c' hc' w hw]
      · obtain ⟨-, a, ha, hca⟩ := hPSU hc
        refine hext (fun u hu => ?_) (fun w hw => ?_)
        · rw [pow_two, MulAut.mul_apply, hca u hu, hca _ (hS.mem_U (hAX ha) u hu),
            ← MulAut.mul_apply, ← pow_two, hA2 a ha]
        · rw [pow_two, MulAut.mul_apply, hPW c hc w hw, hPW c hc w hw]
          rfl
    have hcardfix : ∀ B' ≤ Pc, Nat.card B' * Nat.card (fixV B') =
        Nat.card W * (Nat.card (autSub B' U) * Nat.card (fixV (autSub B' U))) := by
      intro B' hB'
      have hB'stab : B' ≤ stabSub U := hB'.trans hPstab
      have hfixB' : fixV B' = W ⊔ (U ⊓ fixV B') := by
        apply le_antisymm
        · intro v hv
          obtain ⟨u, hu, w, hw, rfl⟩ := hdec v
          have hufix : u ∈ fixV B' := by
            intro b hb
            have h1 := hv b hb
            rw [map_mul, hPW b (hB' hb) w hw] at h1
            exact mul_right_cancel h1
          rw [mul_comm]
          exact Subgroup.mul_mem_sup hw ⟨hu, hufix⟩
        · exact sup_le (fun w hw b hb => hPW b (hB' hb) w hw) inf_le_right
      have hinf : W ⊓ (U ⊓ fixV B') = ⊥ :=
        le_bot_iff.1 ((inf_le_inf_left _ inf_le_left).trans (by rw [inf_comm, hinfUW]))
      have h1 := card_sup_mul_card_inf W (U ⊓ fixV B')
      rw [hinf, Subgroup.card_bot, mul_one, ← hfixB'] at h1
      have h2 : Nat.card (fixV (autSub B' U)) = Nat.card ↥(U ⊓ fixV B') := by
        rw [← map_subtype_fixV_autSub hB'stab, Subgroup.card_map_of_injective U.subtype_injective]
      have h3 := card_autSub_mul hB'stab
      have hbot : B' ⊓ centSub U = ⊥ :=
        le_bot_iff.1 ((inf_le_inf_right _ hB').trans hPfaith.le)
      rw [hbot, Subgroup.card_bot, mul_one] at h3
      rw [h1, h2, ← h3]
      ring
    refine ⟨hPX, hPbot, hPab, fun B' hB' => ?_⟩
    rw [hcardfix B' hB', hcardfix Pc le_rfl, hautEq]
    refine Nat.mul_le_mul_left _ (hoffU.card_le ?_)
    rw [← hautEq]
    exact autSub_mono hB' U
  have hPle : Pc ≤ ffJP {B | IsFFStarOffender X B}
      (X ⊓ Subgroup.centralizer (FAll X Φ : Set (MulAut V))) := by
    rcases hPoff with h | h
    · rw [h]
      exact bot_le
    · exact le_ffJP h (le_inf hPX hPcent)
  exact hAle.trans (sup_le le_sup_left (hPle.trans le_sup_right))

theorem ffJ_le : ffJ X ≤ GAll X Φ ⊔ ffJP {B | IsFFStarOffender X B}
    (X ⊓ Subgroup.centralizer (FAll X Φ : Set (MulAut V))) :=
  iSup₂_le fun _ hA => hS.offender_le hV hA

theorem ffJP_cent_le {t : MulAut V} (ht : t ∈ tvSet X Φ) :
    ffJP {B | IsFFStarOffender X B} (X ⊓ Subgroup.centralizer (FAll X Φ : Set (MulAut V))) ≤
      Subgroup.centralizer (GOf Φ t : Set (MulAut V)) ⊓ centSub (commV (FOf Φ t)) := by
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBF => ?_
  intro b hb
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hB.2.2.1.2 b hb
  have hbF : ∀ y ∈ FOf Φ t, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_iff.1 (hBF hb).2 y (FOf_le_FAll ht hy)
  obtain ⟨h1, h2⟩ := hS.comm_of_sq hV ht hb2 hbF
  exact ⟨Subgroup.mem_centralizer_iff.2 h1, h2⟩

theorem ffJP_cent_le_centSub_W :
    ffJP {B | IsFFStarOffender X B} (X ⊓ Subgroup.centralizer (FAll X Φ : Set (MulAut V))) ≤
      centSub (commV (FAll X Φ)) := by
  intro b hb
  have hle : commV (FAll X Φ) ≤ fixV (Subgroup.zpowers b) := by
    rw [commV_FAll]
    refine iSup₂_le fun t ht m hm => ?_
    exact B1.zpowers_fix ((hS.ffJP_cent_le hV ht hb).2 m hm)
  exact fun w hw => hle hw b (Subgroup.mem_zpowers b)

end Setting

end CFSG.Quasithin.B19

module

public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Background.F918J4
public import CFSG.Quasithin.Background.F918Z8Ka
public import CFSG.Quasithin.Background.SmithB45SzRow

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

theorem suz_card_not_three_dvd {X : Type} [Group X]
    (hsz : ∃ n, IsSz n X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨n, -, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hsz
  subst hn
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h4 : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hq : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    rw [pow_succ, pow_mul]; norm_num; ring
  intro h3
  rw [hq] at h3
  have hq3 : (2 * 4 ^ a) % 3 = 2 := by omega
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · omega
  · have h5 : ((2 * 4 ^ a) ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hq3]
    omega

theorem d321s_card_eq_of_surj_simple {G H : Type} [Group G] [Group H] [IsSimpleGroup G]
    [Nontrivial H] (π : G →* H) (hπ : Function.Surjective π) : Nat.card G = Nat.card H := by
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne H
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have hx : π x = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
      have hy : π y = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
      exact hab (by rw [hx, hy])
  exact Nat.card_congr (MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hker, hπ⟩).toEquiv

section Suz

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem suz_natural
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ) :
    ∃ f, BinaryNaturalSz (autSub Λ V) ⊤ ⊥ f := by
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  obtain ⟨e⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have : IsSimpleGroup ↥(autSub Λ V) := e.symm.isSimpleGroup
  have : Nontrivial ↥(autSub Λ V) := inferInstance
  have hexp : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simp [h.std.hyp.exp])
  have hq : qhatOf (autSub (Λ ⊔ S) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have := h.std.qhat
    rwa [← h.VS] at this
  have h3 : ¬ 3 ∣ Nat.card ↥(autSub Λ V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact suz_card_not_three_dvd hsz
  obtain ⟨-, hrows⟩ := insp5a_rows hB45 hF hX hexp (loc_qsec h) (loc_sqtk hA21 h) hq
    (a38Types_congr e h.a38)
  rcases hrows with (⟨n, hn, hnat⟩ | hnat3 | halt) | (⟨m, hm, horth⟩ | ⟨f, hf⟩)
  · exfalso
    obtain ⟨F, _, _, hF2, ⟨e'⟩⟩ := hnat.exists_equiv
    apply h3
    rw [← Nat.card_congr e'.toEquiv, Vol2.Ch10.SecA.card_statedSL,
      Vol2.Ch10.SecA.card_SL_two_pow hF2]
    exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow 4 1 n) _
  · exfalso
    obtain ⟨F, _, _, hF2, ⟨e'⟩⟩ := hnat3.exists_equiv
    apply h3
    rw [← Nat.card_congr e'.toEquiv, Vol2.Ch10.SecA.card_statedSL,
      Vol2.Ch10.SecA.card_SL_three_pow hF2]
    norm_num
  · exfalso
    obtain ⟨π₀, hπ⟩ := halt
    let π : ↥(alternatingGroup (Fin 5)) →* ↥(autSub Λ V) := π₀
    have hS : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have := d321s_card_eq_of_surj_simple π hπ.1
    apply h3
    rw [← this, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · exfalso
    obtain ⟨F, _, _, _, hF2, π₀, hR⟩ := horth
    let π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) →* ↥(autSub Λ V) := π₀
    have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      Vol2.Ch11.SecA.isSimpleGroup_SL2 (n := 2 * m) (by omega) hF2
    have hs' : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
      (specialLinearGroupEquivStatedSL 2 F).symm.isSimpleGroup
    have := d321s_card_eq_of_surj_simple π hR.1
    apply h3
    rw [← this, Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_two_pow hF2]
    refine Dvd.dvd.mul_left ?_ _
    have h16 : 4 ^ (2 * m) = 16 ^ m := by rw [pow_mul]; norm_num
    rw [h16]
    have := Nat.sub_dvd_pow_sub_pow 16 1 m
    simp only [one_pow] at this
    exact (show 3 ∣ 16 - 1 by norm_num).trans this
  · exact ⟨f, hf⟩

omit [Finite Y] in
theorem d321s_autSub_le_normalizer_of_normal {H : Subgroup (MulAut Y)}
    (hHΛ : ∀ a ∈ H, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ) :
    autSub H V ≤ Subgroup.normalizer ((autSub Λ V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
  have key : ∀ φ ∈ autSub H V, ∀ ψ ∈ autSub Λ V, φ * ψ * φ⁻¹ ∈ autSub Λ V := by
    intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    obtain ⟨l, hl, rfl⟩ := mem_autSub.1 hψ
    refine mem_autSub.2 ⟨⟨g.1 * l.1 * g.1⁻¹, ?_⟩, hHΛ _ hg _ hl, ?_⟩
    · exact (stabSub V).mul_mem ((stabSub V).mul_mem g.2 l.2) ((stabSub V).inv_mem g.2)
    · have e : (⟨g.1 * l.1 * g.1⁻¹, (stabSub V).mul_mem ((stabSub V).mul_mem g.2 l.2)
          ((stabSub V).inv_mem g.2)⟩ : stabSub V) = g * l * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact key φ hφ ψ hψ
  · intro hψ
    have := key φ⁻¹ ((autSub H V).inv_mem hφ) _ hψ
    have e : φ⁻¹ * (φ * ψ * φ⁻¹) * φ⁻¹⁻¹ = ψ := by group
    rwa [e] at this

theorem suz_qhat
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ) :
    qhatOf (autSub Γ V) = ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨f, hf⟩ := suz_natural hB45 hA21 hF hX h hsz
  have hΛΓ : Λ ≤ Γ := le_of_mem_cComp h.std.hyp.comp
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  exact (B45Sz.qOf_qhatOf_eq_two (autSub_mono hΛΓ V)
    (d321s_autSub_le_normalizer_of_normal hgn) hf).2

theorem suz_comm_of_trivial_on_V (h : LocCfg Γ Λ S V)
    {A : Subgroup (MulAut Y)} (hAΓ : A ≤ Γ) (hfix : ∀ a ∈ A, ∀ v ∈ V, a v = v) :
    ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a := by
  intro a ha x hx
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have hfaith := loc_faithful h
  have hax : a * x * a⁻¹ ∈ Λ := hgn a (hAΓ ha) x hx
  have hcomm : a * x * a⁻¹ * x⁻¹ ∈ Λ ⊓ centSub V := by
    refine ⟨Λ.mul_mem hax (Λ.inv_mem hx), fun v hv => ?_⟩
    have hw : x⁻¹ v ∈ V := (loc_irr_data h).1 x⁻¹ (Λ.inv_mem hx) v hv
    have h1 : a (x⁻¹ v) = x⁻¹ v := hfix a ha _ hw
    have h2 : a⁻¹ (x⁻¹ v) = x⁻¹ v := by
      calc a⁻¹ (x⁻¹ v) = a⁻¹ (a (x⁻¹ v)) := by rw [h1]
        _ = x⁻¹ v := by simp
    have h3 : x (x⁻¹ v) = v := by simp
    show a (x (a⁻¹ (x⁻¹ v))) = v
    rw [h2, h3]
    exact hfix a ha v hv
  rw [hfaith, Subgroup.mem_bot] at hcomm
  have : a * x * a⁻¹ = x := by
    have := congrArg (· * x) hcomm
    simpa using this
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [this]

theorem suz_Y_eq_V (h : LocCfg Γ Λ S V)
    {A : Subgroup (MulAut Y)} (hAΓ : A ≤ Γ) (hAV : ∀ a ∈ A, ∀ v ∈ V, a v ∈ V)
    (hVF : V ⊔ fixV A = ⊤) {a₀ : MulAut Y} (ha₀ : a₀ ∈ A) {x₀ : MulAut Y} (hx₀ : x₀ ∈ Λ)
    (hne : a₀ * x₀ ≠ x₀ * a₀) : False := by
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have hΛV : ∀ l ∈ Λ, ∀ v ∈ V, l v ∈ V := (loc_irr_data h).1
  have hA_triv : ∀ a ∈ A, ∀ y : Y, a y * y⁻¹ ∈ V := by
    intro a ha y
    have hy : y ∈ V ⊔ fixV A := by rw [hVF]; trivial
    obtain ⟨v, hv, f, hf, rfl⟩ := Subgroup.mem_sup.1 hy
    have haf : a f = f := hf a ha
    rw [map_mul, haf]
    have : a v * f * (v * f)⁻¹ = a v * v⁻¹ := by group
    rw [this]
    exact V.mul_mem (hAV a ha v hv) (V.inv_mem hv)
  have key : ∀ a ∈ A, ∀ l ∈ Λ, ∀ y : Y, ((l * a * l⁻¹ * a⁻¹ : MulAut Y) y) * y⁻¹ ∈ V := by
    intro a ha l hl y
    have h1 : y * (a⁻¹ y)⁻¹ ∈ V := by
      have := hA_triv a ha (a⁻¹ y)
      simpa using this
    have h3 := hA_triv a ha (l⁻¹ (a⁻¹ y))
    have h4 := hΛV l hl _ h3
    have e : l (a (l⁻¹ (a⁻¹ y)) * (l⁻¹ (a⁻¹ y))⁻¹) =
        ((l * a * l⁻¹ * a⁻¹ : MulAut Y) y) * (a⁻¹ y)⁻¹ := by
      rw [map_mul, map_inv, MulAut.apply_inv_self]
      rfl
    rw [e] at h4
    have := V.mul_mem h4 (V.inv_mem h1)
    have e2 : ((l * a * l⁻¹ * a⁻¹ : MulAut Y) y) * (a⁻¹ y)⁻¹ * (y * (a⁻¹ y)⁻¹)⁻¹ =
        ((l * a * l⁻¹ * a⁻¹ : MulAut Y) y) * y⁻¹ := by group
    rwa [e2] at this
  let Λ₀ : Subgroup ↥Λ :=
    { carrier := {l | ∀ y : Y, (l : MulAut Y) y * y⁻¹ ∈ V}
      mul_mem' := by
        intro l₁ l₂ h₁ h₂ y
        have e : ((l₁ * l₂ : ↥Λ) : MulAut Y) y * y⁻¹ =
            ((l₁ : MulAut Y) ((l₂ : MulAut Y) y) * ((l₂ : MulAut Y) y)⁻¹) *
              ((l₂ : MulAut Y) y * y⁻¹) := by
          show (l₁ : MulAut Y) ((l₂ : MulAut Y) y) * y⁻¹ = _
          group
        rw [e]
        exact V.mul_mem (h₁ _) (h₂ y)
      one_mem' := by
        intro y
        simp
      inv_mem' := by
        intro l hl y
        have := hl (((l⁻¹ : ↥Λ) : MulAut Y) y)
        have e : ((l⁻¹ : ↥Λ) : MulAut Y) y * y⁻¹ =
            ((l : MulAut Y) (((l⁻¹ : ↥Λ) : MulAut Y) y) * (((l⁻¹ : ↥Λ) : MulAut Y) y)⁻¹)⁻¹ := by
          have e1 : (l : MulAut Y) (((l⁻¹ : ↥Λ) : MulAut Y) y) = y := by
            show (l : MulAut Y) (((l : MulAut Y))⁻¹ y) = y
            simp
          rw [e1]
          group
        rw [e]
        exact V.inv_mem this }
  have hnormal : Λ₀.Normal := by
    refine ⟨fun l hl g y => ?_⟩
    have hl' : ∀ y : Y, (l : MulAut Y) y * y⁻¹ ∈ V := hl
    show ((g * l * g⁻¹ : ↥Λ) : MulAut Y) y * y⁻¹ ∈ V
    have e : ((g * l * g⁻¹ : ↥Λ) : MulAut Y) y * y⁻¹ =
        (g : MulAut Y) ((l : MulAut Y) ((g : MulAut Y)⁻¹ y) * ((g : MulAut Y)⁻¹ y)⁻¹) := by
      show ((g : MulAut Y) * (l : MulAut Y) * (g : MulAut Y)⁻¹) y * y⁻¹ = _
      rw [map_mul, map_inv]
      simp [MulAut.mul_apply]
    rw [e]
    exact hΛV _ g.2 _ (hl' _)
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  have hΛ0top : Λ₀ = ⊤ := by
    have := hnormal
    rcases hsimp.eq_bot_or_eq_top_of_normal Λ₀ with hbot | htop
    · exfalso
      have hc : x₀ * a₀ * x₀⁻¹ * a₀⁻¹ ∈ Λ := by
        have := Λ.mul_mem hx₀ (hgn a₀ (hAΓ ha₀) x₀⁻¹ (Λ.inv_mem hx₀))
        simpa [mul_assoc] using this
      have hc0 : (⟨x₀ * a₀ * x₀⁻¹ * a₀⁻¹, hc⟩ : ↥Λ) ∈ Λ₀ := fun y => key a₀ ha₀ x₀ hx₀ y
      rw [hbot, Subgroup.mem_bot] at hc0
      apply hne
      have h1 : x₀ * a₀ * x₀⁻¹ * a₀⁻¹ = 1 := congrArg Subtype.val hc0
      have h2 : x₀ * a₀ = a₀ * x₀ := by
        have := congrArg (· * (a₀ * x₀)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    · exact htop
  have hΛtriv : ∀ l ∈ Λ, ∀ y : Y, l y * y⁻¹ ∈ V := fun l hl y => by
    have : (⟨l, hl⟩ : ↥Λ) ∈ Λ₀ := by rw [hΛ0top]; trivial
    exact this y
  have hcommV : commSub V Λ = V := (mem_irrPlus_top_iff.1 h.std.hyp.irr).2.1
  have hgV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V := by
    intro g hg v hv
    rw [← hcommV] at hv
    induction hv using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨l, hl, w, hw, rfl⟩ := hc
      have e : g (l w * w⁻¹) = ((g * l * g⁻¹ : MulAut Y) (g w)) * (g w)⁻¹ := by
        rw [map_mul, map_inv]
        simp [MulAut.mul_apply]
      rw [e]
      exact hΛtriv _ (hgn g hg l hl) _
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact V.mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact V.inv_mem hx
  apply h.ne
  rw [eq_top_iff, ← h.std.hyp.gen]
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hgV g hg v hv

theorem suz_central
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ)
    {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ) (hAS : A ≤ S) :
    ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hAΓ : A ≤ Γ := hA2.1
  have hAs : A ≤ stabSub V := le_stabSub_of_forall_mem fun a ha => loc_S_inv h a (hAS ha)
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, x₀, hx₀, hne⟩ := hcon
  have hVA : commSub V A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    exact hne (suz_comm_of_trivial_on_V h hAΓ (fun a ha v hv => hbot hv a ha) a₀ ha₀ x₀ hx₀)
  have hq : (r : WithTop ℚ) ≤ qhatOf (autSub Γ V) := by
    rw [suz_qhat hB45 hA21 hF hX h hsz]
    exact_mod_cast hr2
  obtain ⟨-, -, hVF, -⟩ := D2_8 h.std.hyp.exp hr hA hAs hVA hq
  exact suz_Y_eq_V h hAΓ (fun a ha v hv => (hAs ha v).2 hv) hVF ha₀ hx₀ hne

end Suz

end CFSG.Quasithin

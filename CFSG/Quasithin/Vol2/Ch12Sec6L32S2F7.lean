module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_noFFK_of_isFFInt {X C K₀ F E : Subgroup G}
    (hFN : X ≤ Subgroup.normalizer (F : Set G)) (hEN : X ≤ Subgroup.normalizer (E : Set G))
    (hEF : E ≤ Subgroup.normalizer (F : Set G))
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (F : Set G)) F E))
    (hC : ∀ x ∈ X ⊓ C, ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F)
    (hK : ∀ k ∈ X, k ∈ K₀ → (∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) →
      ∀ k' ∈ K₀, k * k' * k⁻¹ * k'⁻¹ ∈ C)
    (hFF : IsFFInt (secImg (Subgroup.normalizer (F : Set G)) F X)
      (secImg (Subgroup.normalizer (F : Set G)) F E) hE) :
    ¬ NoFFK X C K₀ := by
  intro hNo
  let S : Subgroup (SecQuot (Subgroup.normalizer (F : Set G)) F) :=
    secImg (Subgroup.normalizer (F : Set G)) F E
  let _ : CommGroup ↥S := commGroupOfElemAbelian hE
  let f : ↥X →* SecQuot (Subgroup.normalizer (F : Set G)) F :=
    (secMk (Subgroup.normalizer (F : Set G)) F).comp (Subgroup.inclusion hFN)
  have hf : ∀ x : ↥X,
      f x ∈ Subgroup.normalizer (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)) :=
    fun x => secMk_mem_normalizer_secImg (X := E) (a := ⟨x, hFN x.2⟩) (hEN x.2)
  let ρ : ↥X →* MulAut ↥S := (conjAct S).comp (f.codRestrict _ hf)
  have hsq : ∀ w : ↥S, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hE.2 w w.2)
  have hρ : ∀ (x : ↥X) (e : G) (he : e ∈ E),
      ((ρ x ⟨secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩,
          secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := E)
            (x := ⟨e, hEF he⟩) he⟩ : ↥S) : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        f x * secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩ * (f x)⁻¹ := fun x e he =>
    conjAct_apply_coe' S ⟨f x, hf x⟩ _
  have hker : ∀ x : ↥X, (x : G) ∈ C → ρ x = 1 := by
    intro x hxC
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    apply Subtype.ext
    obtain ⟨e, he, hew⟩ := mem_secImg.mp w.2
    have hcomm : secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ *
        secMk (Subgroup.normalizer (F : Set G)) F e =
        secMk (Subgroup.normalizer (F : Set G)) F e *
        secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ :=
      secMk_comm_of_commutator_mem (hC x ⟨x.2, hxC⟩ e he)
    have hw : (w : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        secMk (Subgroup.normalizer (F : Set G)) F e := hew.symm
    have h1 : ((ρ x w : ↥S) : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        f x * (w : SecQuot (Subgroup.normalizer (F : Set G)) F) * (f x)⁻¹ :=
      conjAct_apply_coe' S ⟨f x, hf x⟩ w
    rw [h1, hw]
    change secMk _ F ⟨x, hFN x.2⟩ * secMk _ F e * (secMk _ F ⟨x, hFN x.2⟩)⁻¹ = secMk _ F e
    rw [hcomm]; group
  have hK' : ∀ x : ↥X, (x : G) ∈ K₀ → ρ x = 1 → ∀ k ∈ K₀, x * k * x⁻¹ * k⁻¹ ∈ C := by
    intro x hxK hx1
    have hxE : ∀ e ∈ E, (x : G) * e * (x : G)⁻¹ * e⁻¹ ∈ F := by
      intro e he
      have h2 := congrArg (fun a : ↥S => (a : SecQuot (Subgroup.normalizer (F : Set G)) F))
        (congrArg (fun r : MulAut ↥S => r ⟨secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩,
          secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := E)
            (x := ⟨e, hEF he⟩) he⟩) hx1)
      simp only [MulAut.one_apply] at h2
      rw [hρ x e he] at h2
      have h3 := mul_inv_eq_iff_eq_mul.mp h2
      exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (F : Set G)) (B := F)
        (x := ⟨x, hFN x.2⟩) (y := ⟨e, hEF he⟩) h3
    exact fun k hk => hK x x.2 hxK hxE k hk
  have hNo' := hNo ↥S hsq ρ hker hK'
  have hrange : ρ.range = autOn (secImg (Subgroup.normalizer (F : Set G)) F X) S := by
    ext a
    rw [mem_autOn_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hfx : f x = secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ := rfl
      refine ⟨⟨f x, hf x⟩, ?_, rfl⟩
      show f x ∈ secImg (Subgroup.normalizer (F : Set G)) F X
      rw [hfx]
      exact secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := X)
        (x := ⟨(x : G), hFN x.2⟩) x.2
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hys⟩ := mem_secImg.mp (hs : (s : SecQuot (Subgroup.normalizer (F : Set G)) F) ∈
        secImg (Subgroup.normalizer (F : Set G)) F X)
      refine ⟨⟨y, hy⟩, ?_⟩
      have : (⟨f ⟨y, hy⟩, hf ⟨y, hy⟩⟩ : ↥(Subgroup.normalizer
          (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)))) = s := Subtype.ext hys
      show (conjAct S) _ = conjAct S s
      rw [← this]
      rfl
  rw [hrange] at hNo'
  exact hNo' hFF

theorem leafF7_holds : LeafF7 := by
  intro G _ _ T V L V₁ Vp H K h I hI₁ hIU hI hNo
  have h1 := h.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hIHU
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure Vp H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (h1.commutator_conjClosure_le e he x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hWK := h.tilde_commutator_conjClosure hIU hI
  have hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
    intro hbot
    have hIV₁ : I ≤ V₁ := by
      intro i hi
      have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ (hUH (hIU hi))
      have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
          tildeOf V₁ (conjClosure I H) :=
        secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
      rw [hbot] at this
      have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
      exact secMk_eq_one_iff.mp h2
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (hUH (hIU hi)), fun k hk => ?_⟩
      have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (h.K₀_le_H hk)) i⁻¹).mp
          (V₁.inv_mem (hIV₁ hi))
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [e]
      exact V₁.mul_mem (hIV₁ hi) h3
    exact (not_le_of_gt hI.2.2.1) hIC
  obtain ⟨B, ⟨hBL, -, hfaith⟩, -⟩ := h.F918_2
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  by_contra hne
  have hnt1 : ¬ ∀ k ∈ conjClosure K T, ∀ w ∈ conjClosure I H, k * w * k⁻¹ * w⁻¹ ∈ V₁ := by
    intro hall
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun w hw k hk => ?_
      have := V₁.inv_mem (hall k hk w hw)
      have e : (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hW0
    rw [← hWK]
    exact tildeOf_eq_bot_of_le hle
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H,
      k * u * k⁻¹ * u⁻¹ ∈ conjClosure I H := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure I H := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := (conjClosure I H).inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hne
    refine le_antisymm ?_ (secImg_mono hle)
    rw [← hWK]
    exact secImg_mono (Subgroup.commutator_mono hIHU le_rfl)
  obtain ⟨hK1, -⟩ := h.central_kernel_and_faithful hBT hfaith h.K₀T_le_normalizer_V₁ hIHN hnt1
  obtain ⟨hK2, -⟩ := h.central_kernel_and_faithful hBT hfaith hIHN h.K₀T_le_normalizer_U hnt2
  have hFF1 : ∀ hFF : IsFFInt (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure I H))
      (h.isElemAbelian_tilde_of_le hIHU), False := fun hFF =>
    not_noFFK_of_isFFInt (X := conjClosure K T ⊔ T) (C := pCoreOf 2 H) (K₀ := conjClosure K T)
      (F := V₁) (E := conjClosure I H) h.K₀T_le_normalizer_V₁ hIHN
      (hIHU.trans (hUH.trans h1.H_normalizes_V₁)) (h.isElemAbelian_tilde_of_le hIHU)
      (fun x hx e he => hQV₁ x hx.2 e (hIHU he)) (fun k _ hk => hK1 k hk) hFF hNo
  have hFF2 : ∀ hFF : IsFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure Vp H)) (h.isElemAbelian_quotient (conjClosure I H)), False := fun hFF =>
    not_noFFK_of_isFFInt (X := conjClosure K T ⊔ T) (C := pCoreOf 2 H) (K₀ := conjClosure K T)
      (F := conjClosure I H) (E := conjClosure Vp H) hIHN h.K₀T_le_normalizer_U hUW
      (h.isElemAbelian_quotient (conjClosure I H))
      (fun x hx e he => le_conjClosure I H (hI₁ (hQV₁ x hx.2 e he)))
      (fun k _ hk => hK2 k hk) hFF hNo
  rcases h.F918_6 (le_trans hI₁ (le_conjClosure I H)) hIHU hIHN hW0 hWK with
    ha | ⟨hb1, -⟩ | hc
  · exact hne ha
  · exact (hFF1 hb1).elim
  · rcases hc with hc | hc
    · exact (hFF1 (F9.IsStrongFFInt.isFFInt hc)).elim
    · exact (hFF2 (F9.IsStrongFFInt.isFFInt hc)).elim

end CFSG.Quasithin.H13.L1232S2

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin
open scoped Pointwise commutatorElement

section Section

variable {G : Type} [Group G] [Finite G]

theorem mem_Qset_autOn_secImg_of_isElemAbelian2 {K E X' B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hX'K : X' ≤ Subgroup.normalizer (K : Set G))
    (hX'E : X' ≤ Subgroup.normalizer (E : Set G)) (hBX' : B ≤ X')
    (hAel : @IsElemAbelian2 ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
      (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E)))
    (hnt : ¬ ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ K)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ e ∈ E,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ ∈ K)
    (hr : (centralizerMod K E B).relIndex E ≤ ((centralizerMod K B E).relIndex B) ^ 2) :
    autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E) ∈
      @Qset ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
        (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
          (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBX'.trans hX'K
  have hBE : B ≤ Subgroup.normalizer (E : Set G) := hBX'.trans hX'E
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  have hA2 : IsA2 (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
      (secImg (Subgroup.normalizer (K : Set G)) K E))
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
    refine ⟨autOn_le_autOn _ (secImg_mono hBX'), ?_, hAel⟩
    refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hBK hb⟩) hb))
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨e, hEK he⟩)
      (secMk_mem_secImg (x := ⟨e, hEK he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hBK hb⟩) (y := ⟨e, hEK he⟩) this.symm
  refine ⟨⟨hA2, ?_⟩, ?_⟩
  · rw [rAV_le_two_iff (fun w => Subtype.ext (by simpa using hE.2 w w.2)) hA2]
    have c1 := card_autOn_secImg hBK hEK hBE
    have c2 := card_fixV_autOn_eq hE hn
    have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
    have hmul := Subgroup.relIndex_mul_card
      (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
      (secImg (Subgroup.normalizer (K : Set G)) K E)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    rw [c1, c2]
    calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
        = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
            (secImg (Subgroup.normalizer (K : Set G)) K E) *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
      _ ≤ ((centralizerMod K B E).relIndex B) ^ 2 *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
        rw [c3]; exact Nat.mul_le_mul_right _ hr
  · rw [← isQuadratic_iff_commSeries_two]
    refine isQuadratic_autOn_of_forall hE ?_
    intro s₁ hs₁ s₂ hs₂ w hw
    obtain ⟨b₁, hb₁, rfl⟩ := mem_secImg.mp hs₁
    obtain ⟨b₂, hb₂, rfl⟩ := mem_secImg.mp hs₂
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
    have h1 : secMk (Subgroup.normalizer (K : Set G)) K
        (b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹) = 1 :=
      secMk_eq_one_iff.mpr (by simpa using hquad b₁ hb₁ b₂ hb₂ u hu)
    simpa [map_mul, map_inv] using h1

theorem relIndex_le_sq_of_mem_Qset {K E B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBE : B ≤ Subgroup.normalizer (E : Set G))
    {X : Subgroup (MulAut ↥(secImg (Subgroup.normalizer (K : Set G)) K E))}
    (hA : autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E) ∈
      @Qset ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE) X) :
    (centralizerMod K E B).relIndex E ≤ ((centralizerMod K B E).relIndex B) ^ 2 := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  obtain ⟨⟨hA2, hr⟩, -⟩ := hA
  have hrc := (rAV_le_two_iff (fun w => Subtype.ext (by simpa using hE.2 w w.2)) hA2).mp hr
  have c1 := card_autOn_secImg hBK hEK hBE
  have c2 := card_fixV_autOn_eq hE hn
  have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
  have hmul := Subgroup.relIndex_mul_card
    (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
      (secImg (Subgroup.normalizer (K : Set G)) K B :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
    (secImg (Subgroup.normalizer (K : Set G)) K E)
  rw [inf_eq_left.mpr inf_le_left] at hmul
  rw [c1, c2] at hrc
  rw [← hmul, c3] at hrc
  have hpos : 0 < Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
      (secImg (Subgroup.normalizer (K : Set G)) K B :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right hrc hpos

section Transfer

variable {Γ : Type*} [Group Γ]

theorem isElemAbelian2_autOn_of_le {S W W' : Subgroup Γ} (hW : IsElemAbelian 2 W)
    (hW' : IsElemAbelian 2 W') (hWW' : W ≤ W')
    (hSW : S ≤ Subgroup.normalizer (W : Set Γ)) (hSW' : S ≤ Subgroup.normalizer (W' : Set Γ))
    (hA : @IsElemAbelian2 ↥W' (commGroupOfElemAbelian hW') (autOn S W')) :
    @IsElemAbelian2 ↥W (commGroupOfElemAbelian hW) (autOn S W) := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  let _ : CommGroup ↥W' := commGroupOfElemAbelian hW'
  constructor
  · intro a ha b hb
    obtain ⟨s₁, hs₁, rfl⟩ := mem_autOn_iff.mp ha
    obtain ⟨s₂, hs₂, rfl⟩ := mem_autOn_iff.mp hb
    have h1 := hA.1 (conjAct W' ⟨(s₁ : Γ), hSW' hs₁⟩)
      (mem_autOn_iff.mpr ⟨⟨(s₁ : Γ), hSW' hs₁⟩, hs₁, rfl⟩)
      (conjAct W' ⟨(s₂ : Γ), hSW' hs₂⟩) (mem_autOn_iff.mpr ⟨⟨(s₂ : Γ), hSW' hs₂⟩, hs₂, rfl⟩)
    refine MulEquiv.ext fun w => Subtype.ext ?_
    have h2 := congrArg (fun φ : MulAut ↥W' => ((φ ⟨(w : Γ), hWW' w.2⟩ : ↥W') : Γ)) h1
    simpa [MulAut.mul_apply, conjAct_apply_coe'] using h2
  · intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_autOn_iff.mp ha
    have h1 := hA.2 (conjAct W' ⟨(s : Γ), hSW' hs⟩)
      (mem_autOn_iff.mpr ⟨⟨(s : Γ), hSW' hs⟩, hs, rfl⟩)
    refine MulEquiv.ext fun w => Subtype.ext ?_
    have h2 := congrArg (fun φ : MulAut ↥W' => ((φ ⟨(w : Γ), hWW' w.2⟩ : ↥W') : Γ)) h1
    simpa [pow_two, MulAut.mul_apply, conjAct_apply_coe'] using h2

end Transfer

section Quadratic

variable {G : Type} [Group G]

theorem commutator_commutator_mem_of_isQuadratic {K E B : Subgroup G}
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hq : @IsQuadratic ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
      (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E))) :
    ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ e ∈ E,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ ∈ K := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  intro b₁ hb₁ b₂ hb₂ e he
  set W := secImg (Subgroup.normalizer (K : Set G)) K E with hW
  set S := secImg (Subgroup.normalizer (K : Set G)) K B with hS
  let a₁ : ↥(Subgroup.normalizer (K : Set G)) := ⟨b₁, hBK hb₁⟩
  let a₂ : ↥(Subgroup.normalizer (K : Set G)) := ⟨b₂, hBK hb₂⟩
  let x : ↥(Subgroup.normalizer (K : Set G)) := ⟨e, hEK he⟩
  have hs₁ : secMk (Subgroup.normalizer (K : Set G)) K a₁ ∈ S := secMk_mem_secImg hb₁
  have hs₂ : secMk (Subgroup.normalizer (K : Set G)) K a₂ ∈ S := secMk_mem_secImg hb₂
  have hn₁ : secMk (Subgroup.normalizer (K : Set G)) K a₁ ∈
      Subgroup.normalizer (W : Set (SecQuot (Subgroup.normalizer (K : Set G)) K)) :=
    secMk_mem_normalizer_secImg (hBE hb₁)
  have hn₂ : secMk (Subgroup.normalizer (K : Set G)) K a₂ ∈
      Subgroup.normalizer (W : Set (SecQuot (Subgroup.normalizer (K : Set G)) K)) :=
    secMk_mem_normalizer_secImg (hBE hb₂)
  have hw : secMk (Subgroup.normalizer (K : Set G)) K x ∈ W := secMk_mem_secImg he
  let A := autOn S W
  have hA₁ : conjAct W ⟨_, hn₁⟩ ∈ A := mem_autOn_iff.mpr ⟨⟨_, hn₁⟩, hs₁, rfl⟩
  have hA₂ : conjAct W ⟨_, hn₂⟩ ∈ A := mem_autOn_iff.mpr ⟨⟨_, hn₂⟩, hs₂, rfl⟩
  have hfix := hq (Subgroup.subset_closure ⟨conjAct W ⟨_, hn₁⟩, hA₁, ⟨_, hw⟩, rfl⟩)
    (conjAct W ⟨_, hn₂⟩) hA₂
  have h3 := congrArg (fun y : ↥W => (y : SecQuot (Subgroup.normalizer (K : Set G)) K)) hfix
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe'] at h3
  have h3' : secMk (Subgroup.normalizer (K : Set G)) K a₂ *
        (secMk (Subgroup.normalizer (K : Set G)) K a₁ * secMk (Subgroup.normalizer (K : Set G)) K x *
          (secMk (Subgroup.normalizer (K : Set G)) K a₁)⁻¹ *
          (secMk (Subgroup.normalizer (K : Set G)) K x)⁻¹) *
        (secMk (Subgroup.normalizer (K : Set G)) K a₂)⁻¹ =
      secMk (Subgroup.normalizer (K : Set G)) K a₁ * secMk (Subgroup.normalizer (K : Set G)) K x *
        (secMk (Subgroup.normalizer (K : Set G)) K a₁)⁻¹ *
        (secMk (Subgroup.normalizer (K : Set G)) K x)⁻¹ := by
    refine Eq.trans ?_ h3
    group
  have h4 : secMk (Subgroup.normalizer (K : Set G)) K
      (a₂ * (a₁ * x * a₁⁻¹ * x⁻¹) * a₂⁻¹ * (a₁ * x * a₁⁻¹ * x⁻¹)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h3']
    group
  have := secMk_eq_one_iff.mp h4
  simpa using this

end Quadratic

section Main

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem F918_3_general (h : HypF918 T V L V₁ Vp H K) {I B X : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hBL : B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T))
    (hfaith : ∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      b ∈ pCoreOf 2 H)
    (hQ : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H))
        (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))))
    (hX : X = T ∨ X = H) :
    (∀ k ∈ conjClosure K T, (∀ i ∈ conjClosure I X, k * i * k⁻¹ * i⁻¹ ∈ V₁) →
        ∀ k' ∈ conjClosure K T, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ b ∈ B, (∀ i ∈ conjClosure I X, b * i * b⁻¹ * i⁻¹ ∈ V₁) → b ∈ pCoreOf 2 H) ∧
      ∃ hX' : IsElemAbelian 2 (tildeOf V₁ (conjClosure I X)),
        autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure I X)) (commGroupOfElemAbelian hX')
            (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) ∧
        qInt (tildeOf V₁ (K ⊔ T)) (tildeOf V₁ (conjClosure I X)) hX' ≤ 2 := by
  have h1 := h.toHypF98.toHypF91
  obtain ⟨hTX, hXH, hXK₀⟩ := h.T_le_of_cases hX
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  have hBH : B ≤ H := hBT.trans h.T_le_H
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) := hI.1
  have hnt_I : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁ := by
    intro hall
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (pCoreOf_le 2 H (h1.conjClosure_Vp_le_pCoreOf (hIU hi))),
        fun k hk => ?_⟩
      have := V₁.inv_mem (hall k hk i hi)
      have e : (k * i * k⁻¹ * i⁻¹)⁻¹ = i * k * i⁻¹ * k⁻¹ := by group
      rwa [e] at this
    exact (not_le_of_gt hI.2.2.1) hIC
  have hIX_U : conjClosure I X ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU hXH
  have hIXN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I X : Set G) :=
    sup_le (le_normalizer_conjClosure_of_le hKI hXK₀) (hTX.trans (le_normalizer_conjClosure I X))
  have hnt_IX : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure I X, k * e * k⁻¹ * e⁻¹ ∈ V₁ :=
    fun hall => hnt_I fun k hk i hi => hall k hk i (le_conjClosure I X hi)
  obtain ⟨hcentral, hfaithIX⟩ :=
    h.central_kernel_and_faithful hBT hfaith h.K₀T_le_normalizer_V₁ hIXN hnt_IX
  have hBN : B ≤ Subgroup.normalizer (V₁ : Set G) := hBH.trans h1.H_normalizes_V₁
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    h1.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans h1.H_normalizes_V₁)
  have hIX_N : conjClosure I X ≤ Subgroup.normalizer (V₁ : Set G) := hIX_U.trans hUN
  have hBU : B ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    hBH.trans (le_normalizer_conjClosure Vp H)
  have hBIX : B ≤ Subgroup.normalizer (conjClosure I X : Set G) :=
    hBT.trans (le_sup_right.trans hIXN)
  have hhC : centralizerMod V₁ B (conjClosure I X) = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf le_rfl hBN hIX_U hfaithIX
  have hE : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) := h1.isElemAbelian_tilde
  have hfU : ∀ b ∈ B, (∀ e ∈ conjClosure Vp H, b * e * b⁻¹ * e⁻¹ ∈ V₁) → b ∈ pCoreOf 2 H := by
    intro b hb hall
    rw [h1.pCoreOf_eq_centralizerMod]
    exact ⟨hBH hb, hBN hb, hall⟩
  have hCU : centralizerMod V₁ B (conjClosure Vp H) = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf le_rfl hBN le_rfl hfU
  have hrU : (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := by
    have := relIndex_le_sq_of_mem_Qset (K := V₁) (E := conjClosure Vp H) (B := B) hE hUN hBN hBU hQ
    rwa [hCU] at this
  have hr1 : (centralizerMod V₁ (conjClosure I X) B).relIndex (conjClosure I X) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 :=
    (HypF918.relIndex_centralizerMod_le V₁ (conjClosure Vp H) (conjClosure I X) B hIX_U).trans hrU
  have hquadU : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ e ∈ conjClosure Vp H,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ ∈ V₁ := by
    letI : CommGroup ↥(secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure Vp H)) :=
      commGroupOfElemAbelian hE
    exact commutator_commutator_mem_of_isQuadratic (K := V₁) (E := conjClosure Vp H)
      (B := B) hUN hBN hBU hE ((isQuadratic_iff_commSeries_two _).mpr hQ.2)
  have hX' : IsElemAbelian 2 (tildeOf V₁ (conjClosure I X)) :=
    h.isElemAbelian_tilde_conjClosure hIU hX
  have hAel : @IsElemAbelian2 ↥(tildeOf V₁ (conjClosure I X)) (commGroupOfElemAbelian hX')
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X))) :=
    isElemAbelian2_autOn_of_le hX' hE (secImg_mono hIX_U)
      (secImg_le_normalizer_secImg hBIX) (secImg_le_normalizer_secImg hBU) hQ.1.1.2.2
  have hnt_B : ¬ ∀ b ∈ B, ∀ e ∈ conjClosure I X, b * e * b⁻¹ * e⁻¹ ∈ V₁ := by
    intro hall
    have hBQ : B ≤ pCoreOf 2 H := fun b hb => hfaithIX b hb (hall b hb)
    have hcent : tildeOf V₁ B ≤ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := by
      have := h1.tilde_inf_centralizer_pCoreOf hBH
      rw [inf_eq_left.mpr hBQ] at this
      exact inf_eq_left.mp this
    exact hQ.1.1.2.1 (AutOn.autOn_eq_bot_of_le_centralizer hcent)
  have hmem : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure I X)) (commGroupOfElemAbelian hX')
        (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) := by
    refine mem_Qset_autOn_secImg_of_isElemAbelian2 (K := V₁) (E := conjClosure I X)
      (X' := conjClosure K T ⊔ T) (B := B) hX' hIX_N h.K₀T_le_normalizer_V₁ hIXN
      (hBT.trans le_sup_right) hAel hnt_B (fun b₁ hb₁ b₂ hb₂ e he => hquadU b₁ hb₁ b₂ hb₂ e (hIX_U he)) ?_
    rw [hhC]
    simpa [hhC] using hr1
  refine ⟨hcentral, hfaithIX, hX', hmem, ?_⟩
  refine @qOf_le_two_of_mem_Qset _ (commGroupOfElemAbelian hX') inferInstance
    (autOn (tildeOf V₁ (K ⊔ T)) (tildeOf V₁ (conjClosure I X)))
    (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X))) ?_
  exact @mem_Qset_of_le _ (commGroupOfElemAbelian hX') _ _ _ hmem
    (autOn_le_autOn _ (secImg_mono (hBT.trans le_sup_right)))

end Main

end Section

end CFSG.Quasithin.RonanF918

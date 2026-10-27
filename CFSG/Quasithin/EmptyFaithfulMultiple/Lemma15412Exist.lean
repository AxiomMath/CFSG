module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Two
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Psi

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setup

variable (h : Setup T M) {𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))}
include h

theorem pCoreOf_sup_ne_bot {X : Subgroup G} (hXM : X ≤ M) : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
  intro hbot
  apply h.pCoreOf_ne_bot
  rw [eq_bot_iff, ← hbot]
  exact h.pCoreOf_le_pCoreOf le_sup_right (sup_le hXM h.T_le)

theorem commutator_sup_zpowers_thompsonJ (B : E2.Blocks h.elem M 𝓗 I)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I)
    {f₁ f₂ : MulAut (IntMod (VZ T M) h.elem)} (hf₁ : f₁ ∈ L₁) (hf₂ : f₂ ∈ L₂)
    (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) :
    ⁅Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂, autI h.elem (thompsonJ T)⁆ =
      Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha j hj
    have e1 := h.conjAut_zpowers_of_thompsonJ B hL₁ hf₁ h3₁ hj
    have e2 := h.conjAut_zpowers_of_thompsonJ B hL₂ hf₂ h3₂ hj
    have e3 : B1.conjAut j (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) =
        Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
      have hs : B1.conjAut j (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) =
          B1.conjAut j (Subgroup.zpowers f₁) ⊔ B1.conjAut j (Subgroup.zpowers f₂) := by
        simp only [conjAut_eq_map]
        exact Subgroup.map_sup _ _ _
      rw [hs, e1, e2]
    have hjN := mem_normalizer_iff_conjAut.mpr e3
    have h0 := (Subgroup.mem_normalizer_iff.mp hjN a⁻¹).mp (Subgroup.inv_mem _ ha)
    have e : ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ha h0
  · refine sup_le ?_ ?_
    · calc Subgroup.zpowers f₁ = ⁅Subgroup.zpowers f₁, autI h.elem (thompsonJ T)⁆ :=
            (h.commutator_zpowers_thompsonJ B hL₁ hf₁ h3₁).symm
        _ ≤ _ := Subgroup.commutator_mono le_sup_left le_rfl
    · calc Subgroup.zpowers f₂ = ⁅Subgroup.zpowers f₂, autI h.elem (thompsonJ T)⁆ :=
            (h.commutator_zpowers_thompsonJ B hL₂ hf₂ h3₂).symm
        _ ≤ _ := Subgroup.commutator_mono le_sup_right le_rfl

theorem isYFamily_one (B : E2.Blocks h.elem M 𝓗 I) {L : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
    (hL : L ∈ I) {f : MulAut (IntMod (VZ T M) h.elem)} (hf : f ∈ L) (hf3 : orderOf f = 3)
    (hfix : ∀ x ∈ autI h.elem T, B1.conjAut x L = L) :
    IsYFamily T (h.ps (Subgroup.zpowers f)) := by
  have hp : f ^ 3 = 1 := by rw [← hf3]; exact pow_orderOf_eq_one f
  have hZM : Subgroup.zpowers f ≤ autI h.elem M := Subgroup.zpowers_le.mpr (B.le_autI hL hf)
  have ho := odd_orderOf_of_isElemAbelian (isElemAbelian_zpowers hp)
  have hc : Nat.card (Subgroup.zpowers f) = 3 := by rw [Nat.card_zpowers, hf3]
  have hTN : T ≤ Subgroup.normalizer (h.ps (Subgroup.zpowers f) : Set G) := fun t ht =>
    mem_normalizer_psi h.elem h.le_normalizer (h.T_le ht)
      (conjAut_zpowers_eq B.hb (B.sub hL) (hfix _ (convI_mem_autI h.elem ht _)) hf hf hf3 hf3)
  refine ⟨Or.inr ⟨psi_eq_oTwoUpper h.elem h.le_normalizer _, hTN,
    ⟨le_sup_right, h.pCoreOf_sup_ne_bot (h.ps_le _)⟩, 3, Nat.prime_three, by norm_num, ?_⟩, ?_⟩
  · rw [h.relIndex_ps hZM ho (by rw [hc]; decide), hc]
  · exact h.commutator_thompsonJ_ps hZM ho ((thompsonJ_le_self T).trans hTN)
      (h.commutator_zpowers_thompsonJ B hL hf hf3)

theorem isYFamily_two (B : E2.Blocks h.elem M 𝓗 I)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I)
    (h12 : L₁ ≠ L₂) (hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂)
    {f₁ f₂ : MulAut (IntMod (VZ T M) h.elem)} (hf₁ : f₁ ∈ L₁) (hf₂ : f₂ ∈ L₂)
    (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) {x : MulAut (IntMod (VZ T M) h.elem)}
    (hx : x ∈ autI h.elem T) (hxL : B1.conjAut x L₁ = L₂) :
    IsYFamily T (h.ps (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂)) := by
  set D := Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ with hDdef
  have s₁ := B.sub hL₁
  have s₂ := B.sub hL₂
  have hel := comm_of_mem_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂
  have hDM : D ≤ autI h.elem M :=
    sup_le (Subgroup.zpowers_le.mpr (B.le_autI hL₁ hf₁))
      (Subgroup.zpowers_le.mpr (B.le_autI hL₂ hf₂))
  have ho := odd_orderOf_of_isElemAbelian hel
  have hc : Nat.card D = 9 := card_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂
  have hodd : Odd (Nat.card D) := by rw [hc]; decide
  have hnorm := conjAut_sup_zpowers B hL₁ hL₂ h12 hI' hf₁ hf₂ h3₁ h3₂
  have hTN : T ≤ Subgroup.normalizer (h.ps D : Set G) := fun t ht =>
    mem_normalizer_psi h.elem h.le_normalizer (h.T_le ht)
      (hnorm _ (convI_mem_autI h.elem (h.T_le ht) _))
  set X := h.ps D with hX
  have hXM : X ≤ M := h.ps_le D
  have hAX : autI h.elem X = D := h.autI_ps hDM ho
  have hO2 := h.pCoreOf_ps hDM ho hodd
  have hcomm : ⁅X, X⁆ ≤ pCoreOf 2 X := by
    rw [hO2]
    refine h.commutator_le_inf_centralizer hXM fun a ha b hb => ?_
    have := hel.1
    rw [hAX] at ha hb
    exact setLike_mul_comm ha hb
  have hsup : ⁅X, X⁆ ⊔ pCoreOf 2 X = pCoreOf 2 X := sup_eq_right.mpr hcomm
  refine ⟨Or.inl ⟨psi_eq_oTwoUpper h.elem h.le_normalizer _, hTN, h.pCoreOf_sup_ne_bot hXM, 3,
    Nat.prime_three, by norm_num, fun y hy => h.pow_three_mem_ps hDM ho hodd hel.2 hy,
    Or.inl (by rw [h.relIndex_ps hDM ho hodd, hc]; norm_num), fun Y' h1 h2 h3 => ?_⟩, ?_⟩
  · rw [hsup] at h1 ⊢
    have hY'N : Y' ≤ Subgroup.normalizer (VZ T M : Set G) := h2.trans (hXM.trans h.le_normalizer)
    have hTD : ∀ t ∈ autI h.elem T, t ∈ Subgroup.normalizer ((autI h.elem Y' : Subgroup _) :
        Set (MulAut (IntMod (VZ T M) h.elem))) := by
      intro t ht
      obtain ⟨g, hgT, rfl⟩ := (mem_autI h.elem).1 ht
      rw [mem_normalizer_iff_conjAut, conjAut_eq_map]
      have e := autI_cjSub h.elem g.2 Y'
      rw [show (⟨(g : G), g.2⟩ : Subgroup.normalizer (VZ T M : Set G)) = g from rfl] at e
      rw [e, cjSub_eq_of_mem_normalizer (h3 hgT)]
    obtain ⟨t₁, ht₁L, ht₁T, -, ht₁2⟩ := B.exists_orderOf_eq_two h.red h.sylowM hL₁
    obtain ⟨t₂, ht₂L, ht₂T, -, ht₂2⟩ := B.exists_orderOf_eq_two h.red h.sylowM hL₂
    have hi₁ := conj_eq_inv (B.card_eq hL₁) hf₁ ht₁L h3₁ (B.mul_ne_mul hL₁ ht₁L hf₁ ht₁2 h3₁)
    have hi₂ := conj_eq_inv (B.card_eq hL₂) hf₂ ht₂L h3₂ (B.mul_ne_mul hL₂ ht₂L hf₂ ht₂2 h3₂)
    have hY'D : autI h.elem Y' ≤ D := hAX ▸ autI_mono h.elem h2
    have hxL₂ : B1.conjAut x L₂ = L₁ := (hI' _ (B.conjAut_mem (autI_mono h.elem h.T_le hx)
      hL₂)).resolve_right fun e => h12 (conjAut_injective x (hxL.trans e.symm))
    have hx₁ : B1.conjAut x (Subgroup.zpowers f₁) = Subgroup.zpowers f₂ :=
      conjAut_zpowers_eq B.hb s₂ hxL hf₁ hf₂ h3₁ h3₂
    have hx₂ : B1.conjAut x (Subgroup.zpowers f₂) = Subgroup.zpowers f₁ :=
      conjAut_zpowers_eq B.hb s₁ hxL₂ hf₂ hf₁ h3₂ h3₁
    have hne : Subgroup.zpowers f₁ ≠ Subgroup.zpowers f₂ := by
      intro e
      have hm : f₂ ∈ L₁ ⊓ L₂ := ⟨Subgroup.zpowers_le.mpr hf₁ (e ▸ Subgroup.mem_zpowers f₂), hf₂⟩
      rw [inf_eq_bot_of_ne B.hb s₁ s₂ h12, Subgroup.mem_bot] at hm
      rw [hm, orderOf_one] at h3₂
      norm_num at h3₂
    have hxY' : B1.conjAut x (autI h.elem Y') = autI h.elem Y' :=
      mem_normalizer_iff_conjAut.mp (hTD x hx)
    rcases eq_of_le_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂ ht₁L ht₂L hi₁ hi₂ (hTD t₁ ht₁T)
      (hTD t₂ ht₂T) hY'D with e | e | e | e
    ·
      left
      refine le_antisymm ?_ h1
      rw [hO2]
      refine le_inf h2 ?_
      rw [← autI_eq_bot_iff h.elem hY'N]
      exact e
    · exfalso
      rw [e, hx₁] at hxY'
      exact hne hxY'.symm
    · exfalso
      rw [e, hx₂] at hxY'
      exact hne hxY'
    ·
      right
      refine le_antisymm h2 fun y hy => ?_
      have hyM := hXM hy
      have hyD : convI h.elem ⟨y, h.le_normalizer hyM⟩ ∈ autI h.elem Y' := by
        rw [e, ← hDdef, ← hAX]
        exact h.convI_mem_autI' hy hyM
      obtain ⟨y', hy', c, hc, hcy⟩ := exists_mul_of_convI_mem h.elem h.le_normalizer
        (h2.trans hXM) hyM hyD
      have hcX : c ∈ X := by
        have := X.mul_mem (X.inv_mem (h2 hy')) hy
        rw [hcy] at this
        simpa using this
      have hcO : c ∈ pCoreOf 2 X := by
        rw [hO2]
        exact ⟨hcX, hc.2⟩
      rw [hcy]
      exact Y'.mul_mem hy' (h1 hcO)
  · exact h.commutator_thompsonJ_ps hDM ho ((thompsonJ_le_self T).trans hTN)
      (h.commutator_sup_zpowers_thompsonJ B hL₁ hL₂ hf₁ hf₂ h3₁ h3₂)

theorem exists_mem : ∃ Y : Subgroup G, IsYFamily T Y ∧ Y ≤ M := by
  classical
  obtain ⟨𝓗, I, B, hI2⟩ := h.exists_blocks
  have hpos := (B.nonempty h.sylowM h.red h.notJ).card_pos
  by_cases hfix : ∃ L ∈ I, ∀ x ∈ autI h.elem T, B1.conjAut x L = L
  · obtain ⟨L, hL, hLfix⟩ := hfix
    obtain ⟨f, hf, -, hf3⟩ := B.exists_orderOf_eq_three hL
    exact ⟨_, h.isYFamily_one B hL hf hf3 hLfix, h.ps_le _⟩
  · push Not at hfix
    rcases (by omega : I.card = 1 ∨ I.card = 2) with h1 | h2
    · exfalso
      obtain ⟨L₁, hI⟩ := Finset.card_eq_one.mp h1
      have hL₁ : L₁ ∈ I := by rw [hI]; exact Finset.mem_singleton_self _
      obtain ⟨x, hx, hxL⟩ := hfix L₁ hL₁
      apply hxL
      have := B.conjAut_mem (autI_mono h.elem h.T_le hx) hL₁
      rw [hI] at this
      exact Finset.mem_singleton.mp this
    · obtain ⟨L₁, L₂, h12, hI⟩ := Finset.card_eq_two.mp h2
      have hL₁ : L₁ ∈ I := by rw [hI]; simp
      have hL₂ : L₂ ∈ I := by rw [hI]; simp
      have hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂ := fun L hL => by rw [hI] at hL; simpa using hL
      obtain ⟨x, hx, hxL⟩ := hfix L₁ hL₁
      have hxL₂ : B1.conjAut x L₁ = L₂ :=
        (hI' _ (B.conjAut_mem (autI_mono h.elem h.T_le hx) hL₁)).resolve_left hxL
      obtain ⟨f₁, hf₁, -, h3₁⟩ := B.exists_orderOf_eq_three hL₁
      obtain ⟨f₂, hf₂, -, h3₂⟩ := B.exists_orderOf_eq_three hL₂
      exact ⟨_, h.isYFamily_two B hL₁ hL₂ h12 hI' hf₁ hf₂ h3₁ h3₂ hx hxL₂, h.ps_le _⟩

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple

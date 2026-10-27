module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Setup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section Orders

variable {W : Type*} [CommGroup W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

theorem card_sup_zpowers (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) {f₁ f₂ : MulAut W} (hf₁ : f₁ ∈ L₁)
    (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) :
    Nat.card ↥(Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) = 9 := by
  have hZ₁ : Subgroup.zpowers f₁ ≤ L₁ := Subgroup.zpowers_le.mpr hf₁
  have hZ₂ : Subgroup.zpowers f₂ ≤ L₂ := Subgroup.zpowers_le.mpr hf₂
  have c12 : ∀ a ∈ Subgroup.zpowers f₁, ∀ b ∈ Subgroup.zpowers f₂, a * b = b * a :=
    fun a ha b hb' => hb.comm L₁ h₁ L₂ h₂ hne a (hZ₁ ha) b (hZ₂ hb')
  have h := card_sup_mul_card_inf_of_commute c12
  have hinf : Subgroup.zpowers f₁ ⊓ Subgroup.zpowers f₂ = ⊥ :=
    le_bot_iff.1 ((inf_le_inf hZ₁ hZ₂).trans (inf_eq_bot_of_ne hb h₁ h₂ hne).le)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, h3₁, h3₂] at h
  exact h

theorem comm_of_mem_sup_zpowers (hb : IsTransvectionBlocks J 𝓗) {L₁ L₂ : Subgroup (MulAut W)}
    (h₁ : L₁ ∈ 𝓗) (h₂ : L₂ ∈ 𝓗) (hne : L₁ ≠ L₂) {f₁ f₂ : MulAut W} (hf₁ : f₁ ∈ L₁)
    (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3) :
    IsElemAbelian 3 (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) := by
  have hp : ∀ {f : MulAut W}, orderOf f = 3 → f ^ 3 = 1 := fun hf => by
    rw [← hf]
    exact pow_orderOf_eq_one _
  exact isElemAbelian_sup (isElemAbelian_zpowers (hp h3₁)) (isElemAbelian_zpowers (hp h3₂))
    fun a ha b hb' => hb.comm L₁ h₁ L₂ h₂ hne a (Subgroup.zpowers_le.mpr hf₁ ha) b
      (Subgroup.zpowers_le.mpr hf₂ hb')

end Orders

theorem odd_orderOf_of_isElemAbelian {K : Type*} [Group K] {D : Subgroup K}
    (hD : IsElemAbelian 3 D) : ∀ x ∈ D, Odd (orderOf x) := fun x hx => by
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 x hx)
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h <;> rw [h] <;> decide

namespace Setup

variable (h : Setup T M) {𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))}

theorem convI_mem_autI' {Y : Subgroup G} {y : G} (hy : y ∈ Y) (hyM : y ∈ M) :
    convI h.elem ⟨y, h.le_normalizer hyM⟩ ∈ autI h.elem Y :=
  convI_mem_autI h.elem hy (h.le_normalizer hyM)

theorem commutator_le_inf_centralizer {Y : Subgroup G} (hYM : Y ≤ M)
    (hab : ∀ a ∈ autI h.elem Y, ∀ b ∈ autI h.elem Y, a * b = b * a) :
    ⁅Y, Y⁆ ≤ Y ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine ⟨Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb), ?_⟩
  set N := Subgroup.normalizer (VZ T M : Set G)
  have haN : a ∈ N := h.le_normalizer (hYM ha)
  have hbN : b ∈ N := h.le_normalizer (hYM hb)
  have hcN : a * b * a⁻¹ * b⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem haN hbN) (N.inv_mem haN)) (N.inv_mem hbN)
  have key : convI h.elem ⟨a * b * a⁻¹ * b⁻¹, hcN⟩ = 1 := by
    have e : (⟨a * b * a⁻¹ * b⁻¹, hcN⟩ : N) =
        (⟨a, haN⟩ : N) * ⟨b, hbN⟩ * (⟨a, haN⟩ : N)⁻¹ * (⟨b, hbN⟩ : N)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      hab _ (h.convI_mem_autI' ha (hYM ha)) _ (h.convI_mem_autI' hb (hYM hb))]
    group
  exact (convI_eq_one_iff h.elem _).1 key


theorem exists_mem_of_mem_autI {Y : Subgroup G} {x : MulAut (IntMod (VZ T M) h.elem)}
    (hx : x ∈ autI h.elem Y) :
    ∃ y ∈ Y, ∃ hy : y ∈ Subgroup.normalizer (VZ T M : Set G), convI h.elem ⟨y, hy⟩ = x := by
  obtain ⟨g, hg, rfl⟩ := (mem_autI h.elem).1 hx
  exact ⟨g, hg, g.2, rfl⟩

theorem le_normalizer_preI {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
    (hD : ∀ x ∈ autI h.elem T, B1.conjAut x D = D) :
    T ≤ Subgroup.normalizer (preI h.elem M h.le_normalizer D : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_cjSub_eq, cjSub_preI h.elem h.le_normalizer (h.T_le ht),
    hD _ (convI_mem_autI h.elem ht (h.T_le_normalizer ht))]

theorem classify (B : E2.Blocks h.elem M 𝓗 I) (hI2 : I.card ≤ 2) {Y : Subgroup G}
    (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    (∃ L ∈ I, ∃ f ∈ L, orderOf f = 3 ∧ autI h.elem Y = Subgroup.zpowers f ∧
        ∀ g ∈ autI h.elem M, B1.conjAut g L = L) ∨
      (∃ L₁ ∈ I, ∃ L₂ ∈ I, L₁ ≠ L₂ ∧ (∀ L ∈ I, L = L₁ ∨ L = L₂) ∧
        ∃ f₁ ∈ L₁, ∃ f₂ ∈ L₂, orderOf f₁ = 3 ∧ orderOf f₂ = 3 ∧
          autI h.elem Y = Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ∧
          ∃ x ∈ autI h.elem T, B1.conjAut x L₁ = L₂) := by
  rcases shape B h.red h.sylowM h.notJ hI2 (h.autI_le_thompsonJ hY hYM)
    (h.autI_eq_oTwoUpper hY hYM) (h.autI_le_normalizer hY) (h.autI_ne_bot hY hYM) with hA | hB
  · exact Or.inl hA
  obtain ⟨L₁, hL₁, L₂, hL₂, h12, hI', f₁, hf₁, f₂, hf₂, h3₁, h3₂, hD⟩ := hB
  refine Or.inr ⟨L₁, hL₁, L₂, hL₂, h12, hI', f₁, hf₁, f₂, hf₂, h3₁, h3₂, hD, ?_⟩
  by_contra hcon
  push Not at hcon
  have hfix : ∀ x ∈ autI h.elem T, B1.conjAut x L₁ = L₁ := fun x hx =>
    (hI' _ (B.conjAut_mem (autI_mono h.elem h.T_le hx) hL₁)).resolve_right (hcon x hx)
  have hel := comm_of_mem_sup_zpowers B.hb (B.sub hL₁) (B.sub hL₂) h12 hf₁ hf₂ h3₁ h3₂
  have hcard : Nat.card (autI h.elem Y) = 9 := by
    rw [hD]
    exact card_sup_zpowers B.hb (B.sub hL₁) (B.sub hL₂) h12 hf₁ hf₂ h3₁ h3₂
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans h.le_normalizer
  have h2Y : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    h.isPGroup_inf.to_le (inf_le_inf_right _ hYM)
  have hodd : Odd (Nat.card (autI h.elem Y)) := by rw [hcard]; decide
  have hO2 := pCoreOf_eq_inf_centralizer h.elem hYN hodd h2Y
  have hidx : (pCoreOf 2 Y).relIndex Y = 9 := by
    rw [relIndex_pCoreOf_eq h.elem hYN hodd h2Y, hcard]
  rcases hY.1 with hXi | hxi
  ·
    obtain ⟨-, -, -, p, -, -, -, -, hirr⟩ := hXi
    set P := preI h.elem M h.le_normalizer (Subgroup.zpowers f₁) with hP
    have hcomm : ⁅Y, Y⁆ ≤ pCoreOf 2 Y := by
      rw [hO2]
      refine h.commutator_le_inf_centralizer hYM fun a ha b hb => ?_
      have := hel.1
      rw [hD] at ha hb
      exact setLike_mul_comm ha hb
    have hO2Y' : pCoreOf 2 Y ≤ Y ⊓ P := by
      rw [hO2]
      exact le_inf inf_le_left ((inf_le_inf_right _ hYM).trans (inf_centralizer_le_preI h.elem))
    have hTP : T ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_preI fun x hx =>
      conjAut_zpowers_eq B.hb (B.sub hL₁) (hfix x hx) hf₁ hf₁ h3₁ h3₁
    have hTY' : T ≤ Subgroup.normalizer ((Y ⊓ P : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf (basic hY).2.1 hTP
    have hsup : ⁅Y, Y⁆ ⊔ pCoreOf 2 Y = pCoreOf 2 Y := sup_eq_right.mpr hcomm
    rcases hirr (Y ⊓ P) (hsup.symm ▸ hO2Y') inf_le_left hTY' with he | he
    · rw [hsup, hO2] at he
      obtain ⟨y, hyY, hyN, hyx⟩ := h.exists_mem_of_mem_autI
        (hD ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers f₁) : f₁ ∈ autI h.elem Y)
      have hyP : y ∈ P := (mem_preI h.elem).2 ⟨hYM hyY, by
        show convI h.elem ⟨y, hyN⟩ ∈ Subgroup.zpowers f₁
        rw [hyx]
        exact Subgroup.mem_zpowers f₁⟩
      have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) :=
        (he.le (⟨hyY, hyP⟩ : y ∈ Y ⊓ P)).2
      have h1 : f₁ = 1 := by
        rw [← hyx]
        exact (convI_eq_one_iff h.elem _).2 hyC
      rw [h1, orderOf_one] at h3₁
      norm_num at h3₁
    · obtain ⟨y, hyY, hyN, hyx⟩ := h.exists_mem_of_mem_autI
        (hD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers f₂) : f₂ ∈ autI h.elem Y)
      have hyP : y ∈ P := (he.symm.le hyY).2
      obtain ⟨hyM, hyZ⟩ := (mem_preI h.elem).1 hyP
      have hf₂Z : f₂ ∈ Subgroup.zpowers f₁ := by
        rw [← hyx]
        exact hyZ
      have hm : f₂ ∈ L₁ ⊓ L₂ := ⟨Subgroup.zpowers_le.mpr hf₁ hf₂Z, hf₂⟩
      rw [inf_eq_bot_of_ne B.hb (B.sub hL₁) (B.sub hL₂) h12, Subgroup.mem_bot] at hm
      rw [hm, orderOf_one] at h3₂
      norm_num at h3₂
  ·
    obtain ⟨-, -, -, p, hp, -, hidx'⟩ := hxi
    rw [hidx] at hidx'
    rw [← hidx'] at hp
    norm_num at hp

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple

module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Data

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setup

variable (h : Setup T M) {𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))}

theorem conjAut_zpowers_of_thompsonJ (B : E2.Blocks h.elem M 𝓗 I)
    {L : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL : L ∈ I)
    {f : MulAut (IntMod (VZ T M) h.elem)} (hf : f ∈ L) (hf3 : orderOf f = 3)
    {x : MulAut (IntMod (VZ T M) h.elem)} (hx : x ∈ autI h.elem (thompsonJ T)) :
    B1.conjAut x (Subgroup.zpowers f) = Subgroup.zpowers f := by
  have hxJ : x ∈ autI h.elem (thompsonJ M) :=
    autI_mono h.elem (thompsonJ_le_thompsonJ_of_isSylowTwoOf h.sylowM) hx
  have hxL : B1.conjAut x L = L := mem_normalizer_iff_conjAut.mp (B.le_normalizer hL hxJ)
  exact conjAut_zpowers_eq B.hb (B.sub hL) hxL hf hf hf3 hf3

theorem commutator_zpowers_thompsonJ (B : E2.Blocks h.elem M 𝓗 I)
    {L : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL : L ∈ I)
    {f : MulAut (IntMod (VZ T M) h.elem)} (hf : f ∈ L) (hf3 : orderOf f = 3) :
    ⁅Subgroup.zpowers f, autI h.elem (thompsonJ T)⁆ = Subgroup.zpowers f := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha x hx
    have hxN : x ∈ Subgroup.normalizer ((Subgroup.zpowers f : Subgroup _) :
        Set (MulAut (IntMod (VZ T M) h.elem))) :=
      mem_normalizer_iff_conjAut.mpr (h.conjAut_zpowers_of_thompsonJ B hL hf hf3 hx)
    rw [commutatorElement_def]
    have h0 : x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers f :=
      (Subgroup.mem_normalizer_iff.mp hxN a⁻¹).mp ((Subgroup.zpowers f).inv_mem ha)
    have := (Subgroup.zpowers f).mul_mem ha h0
    simpa [mul_assoc] using this
  · obtain ⟨t, htL, htJ, ht2, -⟩ := h.exists_inv_fix B hL
    have hinv := conj_eq_inv (B.card_eq hL) hf htL hf3 (B.mul_ne_mul hL htL hf ht2 hf3)
    have hf3' : f ^ 3 = 1 := by rw [← hf3]; exact pow_orderOf_eq_one f
    have hmem : f * f ∈ ⁅Subgroup.zpowers f, autI h.elem (thompsonJ T)⁆ := by
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers f) htJ
      have e : ⁅f, t⁆ = f * f := by
        rw [commutatorElement_def]
        calc f * t * f⁻¹ * t⁻¹ = f * (t * f * t⁻¹)⁻¹ := by group
          _ = f * f := by rw [hinv, inv_inv]
      rwa [e] at hc
    rw [Subgroup.zpowers_le]
    have e : f = (f * f)⁻¹ := eq_inv_mul_self hf3'
    have hinvm := Subgroup.inv_mem _ hmem
    rwa [← e] at hinvm

theorem conjAut_baum (B : E2.Blocks h.elem M 𝓗 I)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I)
    (h12 : L₁ ≠ L₂) (hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂)
    {x : MulAut (IntMod (VZ T M) h.elem)} (hx : x ∈ autI h.elem (baum T)) :
    B1.conjAut x L₁ = L₁ := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨t₁, ht₁L, -, ht₁2, ht₁fix⟩ := h.exists_inv_fix B hL₁
  obtain ⟨c, hcL, hc1, htc⟩ := exists_fix hW B.hb (B.sub hL₁) ht₁L ht₁2
  have hxc : x c = c := E2.baum_fix h.red h.sylowM hx ((ht₁fix c hcL).mpr htc)
  have hxM : x ∈ autI h.elem M := autI_mono h.elem (inf_le_left.trans h.T_le) hx
  refine (hI' _ (B.conjAut_mem hxM hL₁)).resolve_right fun he => hc1 ?_
  have hmap := IsTransvectionBlocks.map_commSub_conjAut L₁ x
  rw [he] at hmap
  have hcL₂ : c ∈ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L₂ := by
    rw [← hmap, ← hxc]
    exact ⟨c, hcL, rfl⟩
  have hm : c ∈ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L₁ ⊓ commSub ⊤ L₂ := ⟨hcL, hcL₂⟩
  rw [commSub_inf_eq_bot_of_ne hW B.hb (B.sub hL₁) (B.sub hL₂) h12, Subgroup.mem_bot] at hm
  exact hm

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple

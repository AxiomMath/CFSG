module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S153Odd
public import CFSG.Quasithin.EmptyFaithful.S153Sub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd

theorem exists_mulEquiv_sup_perm {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)}
    {tb : MulAut W} (hS : OfourStruct X L₁ L₂ tb) :
    ∃ e : ↥(L₁ ⊔ L₂) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      (∀ (l : MulAut W) (hl : l ∈ L₁), (e ⟨l, Subgroup.mem_sup_left hl⟩).2 = 1) ∧
      (∀ (l : MulAut W) (hl : l ∈ L₂), (e ⟨l, Subgroup.mem_sup_right hl⟩).1 = 1) := by
  obtain ⟨e₁⟩ := nonempty_equiv_perm hS.nat₁
  obtain ⟨e₂⟩ := nonempty_equiv_perm hS.nat₂
  have hcomm : ∀ (a : ↥L₁) (b : ↥L₂), Commute (L₁.subtype a) (L₂.subtype b) :=
    fun a b => hS.comm a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm).2
      ⟨L₁.subtype_injective, L₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hS.Linf
  have hrange : (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm).range = L₁ ⊔ L₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  let Φ : (↥L₁ × ↥L₂) ≃* ↥(L₁ ⊔ L₂) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hΦ : ∀ (a : ↥L₁) (b : ↥L₂), ((Φ (a, b) : ↥(L₁ ⊔ L₂)) : MulAut W) = (a : MulAut W) * b := by
    intro a b
    rfl
  refine ⟨Φ.symm.trans (MulEquiv.prodCongr e₁ e₂), ?_, ?_⟩
  · intro l hl
    have h : Φ.symm ⟨l, Subgroup.mem_sup_left hl⟩ = (⟨l, hl⟩, 1) := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by rw [hΦ]; simp)
    simp only [MulEquiv.trans_apply, h]
    exact map_one e₂
  · intro l hl
    have h : Φ.symm ⟨l, Subgroup.mem_sup_right hl⟩ = (1, ⟨l, hl⟩) := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by rw [hΦ]; simp)
    simp only [MulEquiv.trans_apply, h]
    exact map_one e₁

theorem autI_sup_nS_eq {G : Type} [Group G] [Finite G] {V M T Y : Subgroup G}
    (hV : IsElemAbelian 2 V) {L₁ L₂ : Subgroup (MulAut (IntMod V hV))}
    {tb : MulAut (IntMod V hV)} (hS : OfourStruct (autI hV M) L₁ L₂ tb)
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) (hTM : T ≤ M) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hYM : Y ≤ M) (hY : autI hV Y = oTwoUpper (autI hV M)) :
    autI hV (Y ⊔ (T ⊓ Subgroup.normalizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G))) = L₁ ⊔ L₂ := by
  have hSN : T ⊓ Subgroup.normalizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (hTM.trans hMV)
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYM.trans hMV
  rw [autI_sup hV hYN hSN, hY, autI_nS hV hS hTM]
  have hle : oTwoUpper (autI hV M) ⊔ (autI hV T ⊓ (L₁ ⊔ L₂)) ≤ L₁ ⊔ L₂ :=
    sup_le hS.oTwoUpper_le_sup inf_le_right
  refine le_antisymm hle ?_
  have h9 : 9 ∣ Nat.card ↥(oTwoUpper (autI hV M) ⊔ (autI hV T ⊓ (L₁ ⊔ L₂))) := by
    rw [← hS.card_oTwoUpper hsyl]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h4 : 4 ∣ Nat.card ↥(oTwoUpper (autI hV M) ⊔ (autI hV T ⊓ (L₁ ⊔ L₂))) := by
    rw [← hS.card_S hsyl]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h36 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9 h4
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [hS.card_sup]
    exact Nat.le_of_dvd Nat.card_pos h36)).ge

end SBd

end CFSG.Quasithin

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.P4InspSpEmbed
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspSp

theorem exists_commutator_equiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] {Sp : Subgroup G₁}
    {S : Subgroup G₂} (c : ↥Sp ≃* ↥S) {L : Subgroup G₁} (hL : L = ⁅Sp, Sp⁆) :
    ∃ φ : ↥L ≃* ↥⁅S, S⁆, ∀ (l : ↥L) (hl : (l : G₁) ∈ Sp),
      ((φ l : ↥⁅S, S⁆) : G₂) = ((c ⟨l, hl⟩ : ↥S) : G₂) := by
  let ι₁ : ↥Sp →* G₁ := Sp.subtype
  let ι₂ : ↥Sp →* G₂ := S.subtype.comp c.toMonoidHom
  have hι₂ : Function.Injective ι₂ := Subtype.val_injective.comp c.injective
  let P : Subgroup ↥Sp := ⁅(⊤ : Subgroup ↥Sp), ⊤⁆
  have h1 : L = P.map ι₁ := by
    rw [hL, Subgroup.map_commutator]
    simp [ι₁, ← MonoidHom.range_eq_map]
  have h2 : ⁅S, S⁆ = P.map ι₂ := by
    rw [Subgroup.map_commutator]
    have : (⊤ : Subgroup ↥Sp).map ι₂ = S := by
      rw [← MonoidHom.range_eq_map]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (c y).2
      · intro hx
        exact ⟨c.symm ⟨x, hx⟩, by simp [ι₂]⟩
    rw [this]
  have hmem' : ∀ x ∈ L, ∃ p ∈ P, ι₁ p = x := fun x hx =>
    (SetLike.ext_iff.mp h1 x).mp hx
  have hLle : L ≤ Sp := fun x hx => by
    obtain ⟨p, -, hp⟩ := hmem' x hx
    rw [← hp]; exact p.2
  have hmem : ∀ l : ↥L, ∃ p ∈ P, ι₁ p = l := fun l => hmem' l l.2
  have hLSp : ∀ l : ↥L, (l : G₁) ∈ Sp := fun l => hLle l.2
  let f : ↥L →* ↥⁅S, S⁆ :=
    (ι₂.comp (Subgroup.inclusion hLle)).codRestrict ⁅S, S⁆ (fun l => by
      obtain ⟨p, hpP, hp⟩ := hmem l
      have : p = ⟨l, hLSp l⟩ := Subtype.ext hp
      rw [h2]
      exact ⟨p, hpP, by rw [this]; rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      have h3 : ι₂ ⟨a, hLSp a⟩ = ι₂ ⟨b, hLSp b⟩ := this
      have h4 := congrArg Subtype.val (hι₂ h3)
      exact Subtype.ext h4
    · intro y
      have hy := (SetLike.ext_iff.mp h2 (y : G₂)).mp y.2
      obtain ⟨p, hpP, hp⟩ := hy
      have hpL : (p : G₁) ∈ L := by
        rw [h1]; exact ⟨p, hpP, rfl⟩
      exact ⟨⟨p, hpL⟩, Subtype.ext hp⟩
  exact ⟨MulEquiv.ofBijective f hf, fun l hl => rfl⟩

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_commutator_spSub [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B)
    (hd : Module.finrank (ZMod 2) V = 4) {L : Subgroup (GLV V)} (hL : L ≤ spSub B)
    (hperf : ⁅L, L⁆ = L) (hcard : Nat.card L = 360) :
    L = ⁅spSub B, spSub B⁆ ∧ ∀ m ∈ spSub B, ∀ k ∈ L, m * k * m⁻¹ ∈ L := by
  obtain ⟨Mo⟩ := p4inspsp_exists_model h hd
  obtain ⟨ρ, hinj, hmem, -, hrange⟩ := p4inspsp_exists_embedding h hd Mo
  have hrange' : ρ.range = spSub B := le_antisymm (by rintro _ ⟨σ, rfl⟩; exact hmem σ) hrange
  have hPcomm : ⁅spSub B, spSub B⁆ = Subgroup.map ρ (alternatingGroup (Fin 6)) := by
    rw [← hrange']
    exact p4inspsp_commutator_range (by norm_num) ρ
  have hKP : L ≤ Subgroup.map ρ (alternatingGroup (Fin 6)) :=
    p4inspsp_perfect_le_map_alt (by norm_num) ρ (hrange' ▸ hL) hperf
  have hPcard : Nat.card (Subgroup.map ρ (alternatingGroup (Fin 6))) = 360 := by
    rw [Subgroup.card_map_of_injective hinj, card_alt_six]
  have hLeq : L = Subgroup.map ρ (alternatingGroup (Fin 6)) := by
    have : Finite ↥(Subgroup.map ρ (alternatingGroup (Fin 6))) :=
      Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hKP (by rw [hcard, hPcard])
  refine ⟨hLeq.trans hPcomm.symm, fun m hm k hk => ?_⟩
  rw [← hrange'] at hm
  obtain ⟨σ, rfl⟩ := hm
  rw [hLeq] at hk ⊢
  obtain ⟨a, ha, rfl⟩ := hk
  exact ⟨σ * a * σ⁻¹, (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha σ, by simp⟩

end CFSG.Quasithin.G11.Harris.Alt6

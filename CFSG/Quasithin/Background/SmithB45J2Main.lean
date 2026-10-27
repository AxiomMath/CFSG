module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.SmithB45J2Dim
public import CFSG.Quasithin.Background.SmithB45J2Holds

public section

namespace CFSG.Quasithin

open J2Model J2Row CFSG.Quasithin.H CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint
open CFSG.QuasithinUnique.Setup.X1

namespace J2Row

section Transport

variable {V : Type} [CommGroup V] (e : V ≃* W6)

theorem card_map_congr (A : Subgroup (MulAut V)) :
    Nat.card ↥(A.map (MulAut.congr e).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.congr e).injective

theorem card_fixV_map_congr (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV (A.map (MulAut.congr e).toMonoidHom)) = Nat.card ↥(fixV A) := by
  rw [show A.map (MulAut.congr e).toMonoidHom = A.map (congrHom e) from rfl,
    fixV_map_congrHom, Subgroup.card_map_of_injective e.injective]

theorem isA2_map_congr {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    IsA2 (X.map (MulAut.congr e).toMonoidHom) (A.map (MulAut.congr e).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hA.le, ?_, ?_, ?_⟩
  · intro h
    apply hA.ne_bot
    rw [← Subgroup.map_bot (MulAut.congr e).toMonoidHom] at h
    exact Subgroup.map_injective (MulAut.congr e).injective h
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.isElemAbelian2.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.isElemAbelian2.2 a ha, map_one]

theorem quad_map_congr {A : Subgroup (MulAut V)} (hq : commSeries A 2 = ⊥) :
    commSeries (A.map (MulAut.congr e).toMonoidHom) 2 = ⊥ := by
  rw [CFSG.Quasithin.commSeries_map_mulAutCongr, hq, Subgroup.map_bot]

end Transport

end J2Row

theorem asB45J2_of_small
    (hSmall : J2SmallModules) : AsB45J2 := by
  intro V _ _ hV G L hHyp hT _ h2
  right
  have hcard : Nat.card V < 2 ^ 24 := card_lt_of_j2 hV hHyp hT h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  obtain ⟨π, hπ⟩ := hSmall V hV L ⟨θ⟩ hHyp.2.2.2 hcard
  obtain ⟨e, he⟩ := exists_equiv_of_zornQ hπ
  have hL6 : L.map (MulAut.congr e).toMonoidHom = L6 := map_congr_eq_L6 hπ.1 e he
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr : IsIrrOn L :=
    CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hHyp.2.2.2
  have hperf : Group.IsPerfect ↥L := hHyp.2.2.1.1
  have hGN := B42L2.le_normalizer_of_b4Hyp hHyp
  let φ : ↥L ≃* ↥L6 := ((MulAut.congr e).subgroupMap L).trans (MulEquiv.subgroupCongr hL6)
  have hJ2 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have hcardL6 : Nat.card ↥L6 = 604800 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr θ.toEquiv, hJ2]
  have hcardΓ : Nat.card ↥Γ₆ = 604800 := by
    have hinj : Function.Injective (natAut Γ₆) := matHom_injective.comp Subtype.val_injective
    rw [← hcardL6]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6 := by
    obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
    have h1 : Nat.card (MulAut ↥L6) = Nat.card (MulAut (NativeSporadic.Carrier .J2)) :=
      Nat.card_congr (MulAut.congr (φ.symm.trans θ)).toEquiv
    have h2 : Nat.card (MulAut (NativeSporadic.Carrier .J2)) = 1209600 := by
      rw [← Nat.card_congr Φ.toEquiv, CFSG.QuasithinUnique.Bridge.J2Excl.card_j2R]
    rw [h1, h2, hcardL6]
  have hZ6 : Subgroup.center ↥L6 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : φ.symm z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (φ y)]
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply φ z, hz', map_one]
  set G' := G.map (MulAut.congr e).toMonoidHom with hG'
  have hXN : G' ≤ natNorm Γ₆ := by
    have h := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hGN
    rw [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hL6] at h
    exact h
  have hrank : ∀ A : Subgroup (MulAut W6), A ≤ G' → IsElemAbelian2 A → Nat.card A ≤ 16 := by
    intro A hA hAel
    obtain ⟨A₀, hA₀G, rfl⟩ := exists_eq_map_congrHom e hA
    have hA₀el : IsElemAbelian2 A₀ := by
      refine ⟨fun a ha b hb => (MulAut.congr e).injective ?_, fun a ha =>
        (MulAut.congr e).injective ?_⟩
      · rw [map_mul, map_mul]
        exact hAel.1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      · rw [map_pow, map_one]
        exact hAel.2 _ ⟨a, ha, rfl⟩
    rw [show A₀.map (congrHom e) = A₀.map (MulAut.congr e).toMonoidHom from rfl,
      card_map_congr]
    exact card_le_sixteen hW hperf hirr hZ θ (hA₀G.trans hGN) hA₀el
  have hcardV : Nat.card V = 4096 := by rw [Nat.card_congr e.toEquiv, card_W6]
  have hqhat : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf G := by
    unfold qhatOf
    rw [le_kq_iff]
    intro A hA _
    rw [two_le_rAV_iff hV hA, hcardV]
    have h := (card_bound hcardΓ hAut hZ6 hXN hrank (isA2_map_congr e hA)).1
    rwa [card_map_congr, card_fixV_map_congr] at h
  have hq : ((2 : ℚ) : WithTop ℚ) < qOf G := by
    unfold qOf
    rw [lt_kq_iff]
    intro A hA hAq
    rw [two_lt_rAV_iff hV hA, hcardV]
    have h := (card_bound hcardΓ hAut hZ6 hXN hrank (isA2_map_congr e hA)).2
      (quad_map_congr e hAq)
    rwa [card_map_congr, card_fixV_map_congr] at h
  refine ⟨le_antisymm h2 hqhat, hq, Or.inr ⟨⟨θ⟩, ?_, ?_⟩⟩
  · rw [hcardV]
    norm_num
  · exact ⟨FieldFour, inferInstance, inferInstance, j2Γ₀, FieldFour.natCard_eq,
      j2Γ₀_le_quasithinG2, ⟨π, hπ⟩⟩

theorem asB45J2_holds :
    AsB45J2 :=
  asB45J2_of_small J2Mod.j2SmallModules_holds

end CFSG.Quasithin

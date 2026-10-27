module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique

section Iso

variable {Q Y : Type} [Group Q] [Group Y]

theorem isPSU_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsPSU 3 3 1 B) :
    IsPSU 3 3 1 A := by
  obtain ⟨hadm, K, hK, hKf, hKc, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hKc, ⟨e.trans e'⟩⟩

theorem isG2Two_of_equiv (Φ : Q ≃* Y) (h : IsG2Two Y) : IsG2Two Q := by
  obtain ⟨hc, hz, D, hDn, hDi, hDp⟩ := h
  refine ⟨?_, ?_, D.map Φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Nat.card_congr Φ.toEquiv]
    exact hc
  · ext z
    rw [Subgroup.mem_bot]
    constructor
    · intro hz'
      have : Φ z ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨q, rfl⟩ := Φ.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz' q]
      rw [hz, Subgroup.mem_bot] at this
      exact Φ.injective (by rw [this, map_one])
    · rintro rfl
      exact Subgroup.one_mem _
  · exact Subgroup.Normal.map hDn _ Φ.symm.surjective
  · exact (Subgroup.index_map_equiv D Φ.symm).trans hDi
  · exact isPSU_of_equiv (D.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).symm hDp

theorem map_map_symm (Φ : Q ≃* Y) (P : Subgroup Q) :
    (P.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = P := by
  rw [Subgroup.map_map]
  have : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id Q := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem map_symm_map (Φ : Q ≃* Y) (P : Subgroup Y) :
    (P.map Φ.symm.toMonoidHom).map Φ.toMonoidHom = P := by
  rw [Subgroup.map_map]
  have : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id Y := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem isParabolic2_map (Φ : Q ≃* Y) {P : Subgroup Q} (h : IsParabolic2 (⊤ : Subgroup Q) P) :
    IsParabolic2 (⊤ : Subgroup Y) (P.map Φ.toMonoidHom) := by
  obtain ⟨-, S, hS, hN⟩ := h
  refine ⟨le_top, S.map Φ.toMonoidHom, ?_, ?_⟩
  · have htop : (⊤ : Subgroup Y) = (⊤ : Subgroup Q).map Φ.toMonoidHom :=
      (Subgroup.map_top_of_surjective _ Φ.surjective).symm
    rw [htop]
    exact (QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv Φ).2 hS
  · intro y hy
    have hy' : Φ.symm y ∈ (⊤ : Subgroup Q) ⊓ normalizer (S : Set Q) := by
      refine ⟨trivial, Subgroup.mem_normalizer_iff.2 fun s => ?_⟩
      have h1 := Subgroup.mem_normalizer_iff.1 hy.2 (Φ s)
      constructor
      · intro hs
        have := h1.1 ⟨s, hs, rfl⟩
        obtain ⟨t, ht, hts⟩ := this
        have : Φ (Φ.symm y * s * (Φ.symm y)⁻¹) = Φ t := by simp [← hts]
        rw [Φ.injective this]
        exact ht
      · intro hs
        have : y * Φ s * y⁻¹ ∈ S.map Φ.toMonoidHom :=
          ⟨_, hs, by simp⟩
        obtain ⟨t, ht, hts⟩ := h1.2 this
        have hst : t = s := Φ.injective hts
        rw [← hst]
        exact ht
    have := hN hy'
    exact ⟨_, this, by simp⟩

theorem isMaxParabolic2_of_equiv (Φ : Q ≃* Y) {P : Subgroup Y}
    (h : IsMaxParabolic2 (⊤ : Subgroup Y) P) :
    IsMaxParabolic2 (⊤ : Subgroup Q) (P.map Φ.symm.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isParabolic2_map Φ.symm h1, fun htop => h2 ?_, fun Q' hQ' hQ'top hle => ?_⟩
  · have := congrArg (Subgroup.map Φ.toMonoidHom) htop
    rwa [map_symm_map, Subgroup.map_top_of_surjective _ Φ.surjective] at this
  · have hQ'Y : IsParabolic2 (⊤ : Subgroup Y) (Q'.map Φ.toMonoidHom) := isParabolic2_map Φ hQ'
    have hne : Q'.map Φ.toMonoidHom ≠ ⊤ := fun htop => hQ'top (by
      have := congrArg (Subgroup.map Φ.symm.toMonoidHom) htop
      rwa [map_map_symm, Subgroup.map_top_of_surjective _ Φ.symm.surjective] at this)
    have hle' : P ≤ Q'.map Φ.toMonoidHom := by
      intro y hy
      have : Φ.symm y ∈ Q' := hle ⟨y, hy, rfl⟩
      exact ⟨_, this, by simp⟩
    have := h3 _ hQ'Y hne hle'
    have h4 := congrArg (Subgroup.map Φ.symm.toMonoidHom) this
    rwa [map_map_symm] at h4

end Iso

end CFSG.Quasithin.H13.U3.GC137

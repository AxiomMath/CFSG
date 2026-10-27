module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

noncomputable def s16h_l3MatImage (C : s16h_L3Coord L U) (I : Subgroup W) :
    AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  carrier := {m | ∃ u : ↥U, (u : W) ∈ I ∧ C.ψ u = Multiplicative.ofAdd m}
  zero_mem' := ⟨1, I.one_mem, by simp⟩
  add_mem' := by
    rintro m₁ m₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
    refine ⟨u₁ * u₂, I.mul_mem hu₁ hu₂, ?_⟩
    have h : C.ψ (u₁ * u₂) = C.ψ u₁ * C.ψ u₂ := map_mul _ _ _
    rw [h, h₁, h₂, ← ofAdd_add]
  neg_mem' := by
    rintro m ⟨u, hu, h⟩
    refine ⟨u⁻¹, I.inv_mem hu, ?_⟩
    have h' : C.ψ u⁻¹ = (C.ψ u)⁻¹ := map_inv _ _
    rw [h', h, ← ofAdd_neg]

noncomputable def s16h_l3Preimage (C : s16h_L3Coord L U)
    (J : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) : Subgroup W where
  carrier := {w | ∃ hw : w ∈ U, Multiplicative.toAdd (C.ψ ⟨w, hw⟩) ∈ J}
  one_mem' := ⟨U.one_mem, by
    have h : C.ψ (⟨1, U.one_mem⟩ : ↥U) = 1 := map_one _
    rw [h, toAdd_one]
    exact J.zero_mem⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩
    refine ⟨U.mul_mem hw₁ hw₂, ?_⟩
    have h : C.ψ (⟨w₁ * w₂, U.mul_mem hw₁ hw₂⟩ : ↥U) =
        C.ψ (⟨w₁, hw₁⟩ * ⟨w₂, hw₂⟩) := rfl
    rw [h, map_mul, toAdd_mul]
    exact J.add_mem h₁ h₂
  inv_mem' := by
    rintro w ⟨hw, h⟩
    refine ⟨U.inv_mem hw, ?_⟩
    have h' : C.ψ (⟨w⁻¹, U.inv_mem hw⟩ : ↥U) = C.ψ (⟨w, hw⟩)⁻¹ := rfl
    rw [h', map_inv, toAdd_inv]
    exact J.neg_mem h

theorem s16h_l3MatImage_mem_iff (C : s16h_L3Coord L U) {I : Subgroup W}
    {m : Matrix (Fin 3) (Fin 3) (ZMod 2)} :
    m ∈ s16h_l3MatImage C I ↔
      ∃ u : ↥U, (u : W) ∈ I ∧ C.ψ u = Multiplicative.ofAdd m :=
  Iff.rfl

theorem s16h_l3Preimage_mem_iff (C : s16h_L3Coord L U)
    {J : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))} {w : W} :
    w ∈ s16h_l3Preimage C J ↔
      ∃ hw : w ∈ U, Multiplicative.toAdd (C.ψ ⟨w, hw⟩) ∈ J :=
  Iff.rfl

theorem s16h_l3MatImage_mono (C : s16h_L3Coord L U) {I₁ I₂ : Subgroup W} (h : I₁ ≤ I₂) :
    s16h_l3MatImage C I₁ ≤ s16h_l3MatImage C I₂ := by
  rintro m ⟨u, hu, hψ⟩
  exact ⟨u, h hu, hψ⟩

theorem s16h_l3MatImage_bot (C : s16h_L3Coord L U) : s16h_l3MatImage C ⊥ = ⊥ := by
  ext m
  rw [s16h_l3MatImage_mem_iff]
  constructor
  · rintro ⟨u, hu, hψ⟩
    have hu1 : (u : W) = 1 := by simpa using hu
    have hu' : u = 1 := Subtype.ext hu1
    have : Multiplicative.ofAdd m = 1 := by rw [← hψ, hu', map_one]
    have : m = 0 := by
      have := congrArg Multiplicative.toAdd this
      simpa using this
    simpa using this
  · intro hm
    rw [AddSubgroup.mem_bot] at hm
    subst hm
    exact ⟨1, by simp, by simp⟩

theorem s16h_l3Preimage_bot (C : s16h_L3Coord L U) : s16h_l3Preimage C ⊥ = ⊥ := by
  ext w
  rw [s16h_l3Preimage_mem_iff]
  constructor
  · rintro ⟨hw, h⟩
    have h0 : Multiplicative.toAdd (C.ψ ⟨w, hw⟩) = 0 := by simpa using h
    have h1 : C.ψ (⟨w, hw⟩ : ↥U) = 1 := by
      calc C.ψ ⟨w, hw⟩ = Multiplicative.ofAdd (Multiplicative.toAdd (C.ψ ⟨w, hw⟩)) :=
            (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd 0 := by rw [h0]
        _ = 1 := by rw [ofAdd_zero]
    have hsub : (⟨w, hw⟩ : ↥U) = 1 := C.ψ.injective (by simpa using h1)
    simpa using congrArg Subtype.val hsub
  · intro hw
    rw [Subgroup.mem_bot] at hw
    subst hw
    exact ⟨U.one_mem, by simp⟩

theorem s16h_l3MatImage_preimage (C : s16h_L3Coord L U)
    (J : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    s16h_l3MatImage C (s16h_l3Preimage C J) = J := by
  ext m
  rw [s16h_l3MatImage_mem_iff]
  constructor
  · rintro ⟨u, hu, hψ⟩
    rw [s16h_l3Preimage_mem_iff] at hu
    obtain ⟨hwu, hJ⟩ := hu
    have hsub : (⟨(u : W), hwu⟩ : ↥U) = u := Subtype.ext rfl
    rw [hsub, hψ] at hJ
    simpa using hJ
  · intro hm
    let u : ↥U := C.ψ.symm (Multiplicative.ofAdd m)
    refine ⟨u, ?_, C.ψ.apply_symm_apply (Multiplicative.ofAdd m)⟩
    rw [s16h_l3Preimage_mem_iff]
    refine ⟨u.2, ?_⟩
    have hsub : (⟨(u : W), u.2⟩ : ↥U) = u := Subtype.ext rfl
    rw [hsub, C.ψ.apply_symm_apply]
    simpa using hm

theorem s16h_l3Preimage_image (C : s16h_L3Coord L U) {I : Subgroup W} (hI : I ≤ U) :
    s16h_l3Preimage C (s16h_l3MatImage C I) = I := by
  ext w
  rw [s16h_l3Preimage_mem_iff]
  constructor
  · rintro ⟨hw, hJ⟩
    rw [s16h_l3MatImage_mem_iff] at hJ
    obtain ⟨u, huI, hψ⟩ := hJ
    have hsub : u = (⟨w, hw⟩ : ↥U) := by
      apply C.ψ.injective
      rw [hψ]
      simp
    rw [hsub] at huI
    exact huI
  · intro hwI
    refine ⟨hI hwI, ?_⟩
    rw [s16h_l3MatImage_mem_iff]
    exact ⟨⟨w, hI hwI⟩, hwI, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

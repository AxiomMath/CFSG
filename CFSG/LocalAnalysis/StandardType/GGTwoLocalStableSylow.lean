module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.StandardType.TwoLocalAt

theorem exists_stable_two_subgroup {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (V : Subgroup R) (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (E : Subgroup (MulAut L')) (hE : ∀ e ∈ E, ∀ w : L', ψ w ∈ V → ψ (e w) ∈ V) :
    ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ e ∈ E, ∀ u ∈ U, e u ∈ U := by
  classical
  haveI : Finite R := Finite.of_surjective ψ hψ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Subgroup L' := V.comap ψ
  have hW : ∀ w : L', w ∈ W ↔ ψ w ∈ V := fun w => Subgroup.mem_comap
  let f : W →* V := ψ.subgroupComap V
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨w, hw⟩ := hψ (v : R)
    refine ⟨⟨w, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hw]
      exact v.2
    · apply Subtype.ext
      exact hw
  have hkerf : f.ker ≤ Subgroup.center W := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : ψ (x : L') = 1 := by
      have hval : ((f x : V) : R) = 1 := by
        simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have hcoe : ((f x : V) : R) = ψ (x : L') := rfl
      rwa [hcoe] at hval
    have hxc : (x : L') ∈ Subgroup.center L' := by
      exact hker (by simpa [MonoidHom.mem_ker] using hx1)
    exact Subgroup.mem_center_iff.mp hxc (y : L')
  haveI : Group.IsNilpotent ↥V := IsPGroup.isNilpotent (p := 2) hV2
  haveI : Group.IsNilpotent ↥W := isNilpotent_of_ker_le_center f hkerf
  let P : Sylow 2 W := default
  have hPnormal : P.Normal := inferInstance
  have hPchar : P.Characteristic := Sylow.characteristic_of_normal P hPnormal
  have hVcard : Nat.card V ≠ 1 := by
    intro h
    exact hV1 (Subgroup.card_eq_one.mp h)
  have h2V : 2 ∣ Nat.card V := (hV2.card_eq_or_dvd).resolve_left hVcard
  have h2W : 2 ∣ Nat.card W :=
    h2V.trans (Subgroup.card_dvd_of_surjective (f := f) hf_surj)
  have hPbot : (P : Subgroup W) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h2W
  let U : Subgroup L' := (P : Subgroup W).map W.subtype
  refine ⟨U, ?_, ?_, ?_⟩
  · intro hU
    apply hPbot
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup W) W.subtype_injective).mp hU
  · exact (P.isPGroup').map W.subtype
  · intro e he u hu
    let φ : W →* W :=
      { toFun := fun w => ⟨e (w : L'), (hW (e (w : L'))).mpr (hE e he (w : L') ((hW (w : L')).mp w.2))⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp }
    have hφinj : Function.Injective φ := by
      intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h)
    let φe : W ≃* W := MulEquiv.ofBijective φ hφinj.bijective_of_finite
    have hmap : (P : Subgroup W).map φe.toMonoidHom = (P : Subgroup W) :=
      (Subgroup.characteristic_iff_map_eq.mp hPchar) φe
    rw [Subgroup.mem_map] at hu
    obtain ⟨w, hwP, hwu⟩ := hu
    rw [← hwu]
    have hφmem : φe w ∈ (P : Subgroup W) := by
      have h1 : φe w ∈ (P : Subgroup W).map φe.toMonoidHom :=
        Subgroup.mem_map_of_mem φe.toMonoidHom hwP
      rwa [hmap] at h1
    have hcoe : W.subtype (φe w) = e (w : L') := by
      simp [φe, φ]
    have h2 : W.subtype (φe w) ∈ U := Subgroup.mem_map_of_mem W.subtype hφmem
    rwa [hcoe] at h2

end CFSG.StandardType.TwoLocalAt

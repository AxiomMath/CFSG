module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthFive
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthThree
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthTransport
import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem eq_of_mem_of_reflModel {X : Type} [Group X] {L S : Subgroup X} {p m : ℕ}
    [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
    (e : ↥L ≃* ↥(Subgroup.closure (orthReflSet p m f)))
    (he : ∀ d ∈ {x : ↥L | (x : X) ∈ S ∧ x ≠ 1},
      ((e d : GL (Fin m) (ZMod p))) ∈ orthReflSet p m f)
    {d₀ x : ↥L} (hd₀S : (d₀ : X) ∈ S) (hxS : (x : X) ∈ S) (hx1 : x ≠ 1)
    (hd₀_sq : d₀ * d₀ = 1) {a : Fin m → ZMod p} (ha : f a a = -2)
    (hda : ((e d₀ : ↥(Subgroup.closure (orthReflSet p m f))) :
      GL (Fin m) (ZMod p)) = orthRefl f a) :
    x = d₀ := by
  by_contra hxd
  have hxd1 : x * d₀ ≠ 1 := by
    intro h
    apply hxd
    have h' : x * d₀ * d₀ = 1 * d₀ := by rw [h]
    simpa [mul_assoc, hd₀_sq] using h'
  have hxmulS : ((x * d₀ : ↥L) : X) ∈ S := by
    simpa using S.mul_mem hxS hd₀S
  have hdetx : ((e x : GL (Fin m) (ZMod p)) :
      Matrix (Fin m) (Fin m) (ZMod p)).det = -1 := by
    obtain ⟨v₁, hv₁, hv₁e⟩ := exists_eq_orthRefl_of_mem f (he x ⟨hxS, hx1⟩)
    rw [hv₁e]
    exact orthRefl_det f hv₁
  have hdetd : ((e d₀ : GL (Fin m) (ZMod p)) :
      Matrix (Fin m) (Fin m) (ZMod p)).det = -1 := by
    rw [hda]
    exact orthRefl_det f ha
  have hdetmul : ((e (x * d₀) : GL (Fin m) (ZMod p)) :
      Matrix (Fin m) (Fin m) (ZMod p)).det = 1 := by
    rw [map_mul]
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdetx, hdetd]
    ring
  have hdet2 : ((e (x * d₀) : GL (Fin m) (ZMod p)) :
      Matrix (Fin m) (Fin m) (ZMod p)).det = -1 := by
    obtain ⟨v₂, hv₂, hv₂e⟩ := exists_eq_orthRefl_of_mem f (he (x * d₀) ⟨hxmulS, hxd1⟩)
    rw [hv₂e]
    exact orthRefl_det f hv₂
  rw [hdet2] at hdetmul
  apply h2
  have htwo : (1 : ZMod p) + 1 = 0 := by
    have := congrArg (fun t : ZMod p => t + 1) hdetmul
    simpa using this.symm
  simpa [one_add_one_eq_two] using htwo

theorem exists_orthRefl_of_reflModel {X : Type} [Group X] {L S : Subgroup X} {p m : ℕ}
    [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
    (e : ↥L ≃* ↥(Subgroup.closure (orthReflSet p m f))) (hSL : S ≤ L) (hS : S ≠ ⊥)
    (he : ∀ d ∈ {x : ↥L | (x : X) ∈ S ∧ x ≠ 1}, ((e d : GL (Fin m) (ZMod p))) ∈ orthReflSet p m f) :
    ∃ a, f a a = -2 ∧ ∀ x : ↥L, (x : X) ∈ S ↔
      ((e x : ↥(Subgroup.closure (orthReflSet p m f))) : GL (Fin m) (ZMod p)) ∈
        Subgroup.zpowers (orthRefl f a) := by
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  let d₀ : ↥L := ⟨(s : X), hSL s.2⟩
  have hd₀S : (d₀ : X) ∈ S := s.2
  have hd₀1 : d₀ ≠ 1 := by
    intro h
    exact hs1 (Subtype.ext (by simpa [d₀] using congrArg Subtype.val h))
  obtain ⟨a, ha, hda⟩ := exists_eq_orthRefl_of_mem f (he d₀ ⟨hd₀S, hd₀1⟩)
  have hd₀_sq : d₀ * d₀ = 1 := by
    refine e.injective ?_
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, hda, orthRefl_mul_self f ha]
    rfl
  have key : ∀ x : ↥L, (x : X) ∈ S → x ≠ 1 → x = d₀ :=
    fun x hxS hx1 => eq_of_mem_of_reflModel h2 e he hd₀S hxS hx1 hd₀_sq ha hda
  refine ⟨a, ha, fun x => ⟨?_, ?_⟩⟩
  · intro hxS
    by_cases hx1 : x = 1
    · simpa [hx1] using Subgroup.one_mem (Subgroup.zpowers (orthRefl f a))
    · have hxd : x = d₀ := key x hxS hx1
      rw [hxd, hda]
      exact Subgroup.mem_zpowers (orthRefl f a)
  · intro hx
    have hmap : (Subgroup.zpowers d₀).map
        ((Subgroup.subtype (Subgroup.closure (orthReflSet p m f))).comp e.toMonoidHom) =
        Subgroup.zpowers (orthRefl f a) := by
      rw [MonoidHom.map_zpowers]
      simpa using congrArg Subgroup.zpowers hda
    have hx' : (e x : GL (Fin m) (ZMod p)) ∈ (Subgroup.zpowers d₀).map
        ((Subgroup.subtype (Subgroup.closure (orthReflSet p m f))).comp e.toMonoidHom) := by
      rwa [hmap]
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have hyx' : y = x := e.injective (Subtype.ext hyx)
    have hd₀S' : d₀ ∈ S.subgroupOf L := Subgroup.mem_subgroupOf.mpr s.2
    have hle : Subgroup.zpowers d₀ ≤ S.subgroupOf L := Subgroup.zpowers_le.mpr hd₀S'
    have hyS : (y : X) ∈ S := Subgroup.mem_subgroupOf.mp (hle hy)
    rwa [← hyx']

theorem orthReflParabolic_holds : OrthReflParabolic := by
  intro X _ _ L S hSL hS hG
  rcases hG with ⟨f, hf, hnd, hW, e, he⟩ | ⟨f, hf, hnd, ⟨e, he⟩ | ⟨e, he⟩⟩
  · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨a, ha, hSa⟩ :=
      exists_orthRefl_of_reflModel (p := 5) (m := 4) (f := f) (by decide) e hSL hS he
    obtain ⟨F, rfl⟩ := exists_orthFrameFive f hf hnd hW ha
    exact ⟨5, _, _, F.sevenNineConfig.of_mulEquiv e hSL
      (Subgroup.zpowers_le.mpr F.refl_mem_closure) hSa⟩
  · obtain ⟨a, ha, hSa⟩ :=
      exists_orthRefl_of_reflModel (p := 3) (m := 6) (f := f) (by decide) e hSL hS he
    obtain ⟨F, rfl⟩ := exists_orthFrameThree f hf hnd ha
    exact ⟨3, _, _, F.sevenNineConfig.of_mulEquiv e hSL
      (Subgroup.zpowers_le.mpr F.refl_mem_closure) hSa⟩
  · obtain ⟨Y, Z, hc⟩ := exists_sevenNineConfig_of_reflQuot hSL hS hf hnd e he
    exact ⟨3, Y, Z, hc⟩

end CFSG.LocalAnalysis.WeakClosure81

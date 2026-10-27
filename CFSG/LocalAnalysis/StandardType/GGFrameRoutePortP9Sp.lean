module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoTorus
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Norm
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCent

public section

namespace CFSG.StandardType

open Module CFSG.Open
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrameRoute

private theorem p9Sp_card {K : Type} [Field K] [Finite K] [CharP K 2] {a : ℕ} {L : Type}
    [Field L] [Algebra K L] [Module.Finite K L] {ζ : L} {E : Subgroup (StatedSp a K)}
    (hLdim : finrank K L = 2) (F : ChoiceTwo.SpFrame K a ζ E) (hζo : IsPrimitiveRoot ζ 3) :
    F.s = a ∧ Nat.card E = 3 ^ a := by
  classical
  have hTorInj : Function.Injective F.tor := F.tor_injective hζo
  let e : (Fin F.s → ZMod 3) ≃ E :=
    Equiv.ofBijective (fun f => (⟨F.tor f, F.tor_mem f⟩ : E))
      ⟨fun f f' h => hTorInj (Subtype.ext_iff.mp h),
        fun Y => let ⟨f, hf⟩ := F.mem_tor Y.1 Y.2; ⟨f, Subtype.ext hf⟩⟩
  have hcard : Nat.card E = 3 ^ F.s := by
    have he : Nat.card (Fin F.s → ZMod 3) = Nat.card E := Nat.card_congr e
    rw [← he, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hFs : F.s = a := A6InsideSp.s_eq F hLdim
  exact ⟨hFs, by rw [hcard, hFs]⟩

private theorem p9Sp_fixed {K : Type} [Field K] {a : ℕ} {L : Type} [Field L] [Algebra K L]
    {ζ : L} {E : Subgroup (StatedSp a K)}
    (F : ChoiceTwo.SpFrame K a ζ E) (hζo : IsPrimitiveRoot ζ 3) :
    ∀ v : Fin a ⊕ Fin a → K,
      (∀ Y ∈ E, ((Y : GL (Fin a ⊕ Fin a) K) :
        Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) K) *ᵥ v = v) → v = 0 := by
  intro v hv
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have hd : d = 0 := by
    funext i
    have h1 : CFSG.RankThree.Classical.spEnd (F.tor (Pi.single i 1)) (F.Φ d) = F.Φ d :=
      hv _ (F.tor_mem _)
    rw [F.tor_acts] at h1
    have h2 : ChoiceTwo.torE ζ (Pi.single i 1) d = d := F.Φ.injective h1
    have h3 : ζ * d i = d i := by
      have h4 := congrFun h2 i
      simpa [ChoiceTwo.torE_apply, ZMod.val_one''] using h4
    have hz : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζo.ne_one (by norm_num))
    have hmul : (ζ - 1) * d i = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact h3
    exact (mul_eq_zero.mp hmul).resolve_left hz
  rw [hd, map_zero]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_spFrame_of_selfCent_two (hK : Nat.card K = 2) {a : ℕ}
    {E : Subgroup (StatedSp a K)} (hE : IsElemAbelian 3 E)
    (hsc : ∀ Z : StatedSp a K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E) :
    (∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L) (ζ : L)
        (F : ChoiceTwo.SpFrame K a ζ E),
        finrank K L = 2 ∧ IsPrimitiveRoot ζ 3 ∧ F.s = a) ∧
      Nat.card E = 3 ^ a ∧
      (∀ v : Fin a ⊕ Fin a → K,
        (∀ Y ∈ E, ((Y : GL (Fin a ⊕ Fin a) K) : Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) K) *ᵥ v =
          v) → v = 0) ∧
      Subgroup.centralizer (E : Set (StatedSp a K)) = E := by
  classical
  obtain ⟨L, hLfield, hLalg, hLfin, ζ, hLdim, hζo, ⟨F⟩⟩ :=
    A6InsideSp.exists_frame_two hK hE hsc
  obtain ⟨hFs, hcard⟩ := p9Sp_card hLdim F hζo
  refine ⟨⟨L, hLfield, hLalg, hLfin, ζ, F, hLdim, hζo, hFs⟩, hcard, p9Sp_fixed F hζo, ?_⟩
  refine le_antisymm (centralizer_le_of_selfCent_spTwo hK hE hsc) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact IsElemAbelian.comm hE hy hx

end FrameRoute

namespace ChoiceTwo.SpFrame

variable {K : Type} [Field K] {n : ℕ} {L : Type} [Field L] [Algebra K L] {ζ : L}
  {E : Subgroup (StatedSp n K)}

theorem exists_conj_iff_moveExp (hζ : IsPrimitiveRoot ζ 3) (F : SpFrame K n ζ E)
    (φ : (Fin F.s → ZMod 3) → (Fin F.s → ZMod 3)) :
    (∃ g : StatedSp n K, ∀ f, g * F.tor f * g⁻¹ = F.tor (φ f)) ↔
      ∃ (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool), φ = moveExp π η := by
  constructor
  · rintro ⟨g, hg⟩
    have hg' : ∀ f, ∃ f', (g : GL (Fin n ⊕ Fin n) K) * (F.tor f : GL (Fin n ⊕ Fin n) K) *
        (g : GL (Fin n ⊕ Fin n) K)⁻¹ = (F.tor f' : GL (Fin n ⊕ Fin n) K) := by
      intro f
      refine ⟨φ f, ?_⟩
      have h := congrArg (fun x : StatedSp n K => (x : GL (Fin n ⊕ Fin n) K)) (hg f)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    obtain ⟨π, η, hπ⟩ := F.exists_moveExp_of_conj hζ hg'
    refine ⟨π, η, ?_⟩
    funext f
    apply F.tor_injective hζ
    apply Subtype.ext
    have h := congrArg (fun x : StatedSp n K => (x : GL (Fin n ⊕ Fin n) K)) (hg f)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h.symm.trans (hπ f)
  · rintro ⟨π, η, rfl⟩
    exact ⟨F.move π η, fun f => F.move_conj hζ.pow_eq_one π η f⟩

end ChoiceTwo.SpFrame

end CFSG.StandardType

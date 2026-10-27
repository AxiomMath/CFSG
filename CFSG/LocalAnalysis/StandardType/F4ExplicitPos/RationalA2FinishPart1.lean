module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Attach
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2Part2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.Open CFSG.LieType.Chevalley.RootOps

open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4

open CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.RationalA2

open CFSG.StandardType.F4ExplicitPos.UnitaryPair

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem card_range_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

section UnitaryPairAll

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

theorem algebraMap_pow_eq_self {k : Type} [Field k] [Finite k] [Algebra k Ω] {f : ℕ}
    (hk : Nat.card k = 2 ^ f) (t : k) :
    (algebraMap k Ω t) ^ (2 ^ f) = algebraMap k Ω t := by
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hk
  calc (algebraMap k Ω t) ^ (2 ^ f) = algebraMap k Ω (t ^ (2 ^ f)) := (map_pow _ _ _).symm
    _ = algebraMap k Ω t := by
      rw [← hcard]
      exact congrArg (algebraMap k Ω) (FiniteField.pow_card t)

theorem kappaSU_pair_all
    {k : Type} [Field k] [Finite k] [Algebra k Ω] {f : ℕ} (hk : Nat.card k = 2 ^ f)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω))
    {r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hrootPlus : ∃ ε02 : Ωˣ, ∀ t : Ω,
      ρ (xPlus t) = pinnedX Tag.F4 Ω (r 0 2) ((ε02 : Ω) * t))
    (hrootMinus : ∃ ε20 : Ωˣ, ∀ t : Ω,
      ρ (xMinus t) = pinnedX Tag.F4 Ω (r 2 0) ((ε20 : Ω) * t))
    (F : Subfield Ω) (μ : Ω)
    (hmemPlus : ∀ t : Ω,
      P μ * xPlus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔ t ^ (2 ^ f) = t)
    (hmemMinus : ∀ t : Ω,
      P μ * xMinus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔ t ^ (2 ^ f) = t) :
    ∃ ε02 ε20 : Ωˣ, ∀ t : k,
      (∃ Y : StatedSU 3 (2 ^ f) F,
        kappaSU ρ H F 2 f Y =
          ρ (H * P μ) * pinnedX Tag.F4 Ω (r 0 2) ((ε02 : Ω) * algebraMap k Ω t) *
            (ρ (H * P μ))⁻¹) ∧
      (∃ Y : StatedSU 3 (2 ^ f) F,
        kappaSU ρ H F 2 f Y =
          ρ (H * P μ) * pinnedX Tag.F4 Ω (r 2 0) ((ε20 : Ω) * algebraMap k Ω t) *
            (ρ (H * P μ))⁻¹) := by
  obtain ⟨ε02, hε02⟩ := hrootPlus
  obtain ⟨ε20, hε20⟩ := hrootMinus
  refine ⟨ε02, ε20, fun t => ?_⟩
  have hfix := algebraMap_pow_eq_self (Ω := Ω) (f := f) hk t
  constructor
  · obtain ⟨Y, hY⟩ := (hmemPlus (algebraMap k Ω t)).mpr hfix
    refine ⟨Y, ?_⟩
    simp only [kappaSU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hY]
    simp only [map_mul, map_inv]
    rw [hε02 (algebraMap k Ω t)]
    group
  · obtain ⟨Y, hY⟩ := (hmemMinus (algebraMap k Ω t)).mpr hfix
    refine ⟨Y, ?_⟩
    simp only [kappaSU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hY]
    simp only [map_mul, map_inv]
    rw [hε20 (algebraMap k Ω t)]
    group

end UnitaryPairAll

section FiniteRootGroups

variable {Ω : Type} [Field Ω] {k : Type} [Field k] [Algebra k Ω]

def scaleAlgebraHom (ε : Ωˣ) : Multiplicative k →* Multiplicative Ω where
  toFun t := Multiplicative.ofAdd ((ε : Ω) * algebraMap k Ω (Multiplicative.toAdd t))
  map_one' := by
    apply Multiplicative.ofAdd.injective
    simp
  map_mul' a b := by
    apply Multiplicative.ofAdd.injective
    simp [map_add, mul_add]

theorem scaleAlgebraHom_injective (ε : Ωˣ) :
    Function.Injective (scaleAlgebraHom (k := k) (Ω := Ω) ε) := by
  intro a b h
  have h' : (ε : Ω) * algebraMap k Ω (Multiplicative.toAdd a) =
      (ε : Ω) * algebraMap k Ω (Multiplicative.toAdd b) := by
    have := congrArg (fun x : Multiplicative Ω => (Multiplicative.toAdd x : Ω)) h
    exact this
  have h'' : algebraMap k Ω (Multiplicative.toAdd a) =
      algebraMap k Ω (Multiplicative.toAdd b) :=
    mul_left_cancel₀ (Units.ne_zero ε) h'
  exact Multiplicative.toAdd.injective ((algebraMap k Ω).injective h'')

def conjugatedRootRange
    (w : ModGL Tag.F4 Ω) (α : Fin Tag.F4.rank → ℤ) (ε : Ωˣ) :
    Subgroup (ModGL Tag.F4 Ω) :=
  ((MulAut.conj w).toMonoidHom.comp
    ((pinnedHom Tag.F4 Ω α).comp (scaleAlgebraHom (k := k) (Ω := Ω) ε))).range

theorem mem_conjugatedRootRange_iff
    (w : ModGL Tag.F4 Ω) (α : Fin Tag.F4.rank → ℤ)
    (ε : Ωˣ) (y : ModGL Tag.F4 Ω) :
    y ∈ conjugatedRootRange (k := k) w α ε ↔
      ∃ t : k, y = w * pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω t) * w⁻¹ := by
  rw [conjugatedRootRange, MonoidHom.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.toAdd t, ?_⟩
    change w * pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω (Multiplicative.toAdd t)) * w⁻¹ =
      w * pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω (Multiplicative.toAdd t)) * w⁻¹
    rfl
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    change w * pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω t) * w⁻¹ =
      w * pinnedX Tag.F4 Ω α ((ε : Ω) * algebraMap k Ω t) * w⁻¹
    rfl

theorem conjugatedRootRange_card
    (w : ModGL Tag.F4 Ω) (α : Fin Tag.F4.rank → ℤ) (ε : Ωˣ) :
    Nat.card (conjugatedRootRange (k := k) w α ε) = Nat.card k := by
  rw [conjugatedRootRange, card_range_of_injective]
  · exact (Nat.card_congr (Multiplicative.ofAdd (α := k))).symm
  · exact (MulAut.conj w).injective.comp
      ((pinnedHom_injective Tag.F4 Ω α).comp (scaleAlgebraHom_injective (k := k) (Ω := Ω) ε))

theorem kappaSU_pair_all_rootRange_le
    [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Finite k] [Algebra k Ω] {f : ℕ} (hk : Nat.card k = 2 ^ f)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω))
    {r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hrootPlus : ∃ ε02 : Ωˣ, ∀ t : Ω,
      ρ (xPlus t) = pinnedX Tag.F4 Ω (r 0 2) ((ε02 : Ω) * t))
    (hrootMinus : ∃ ε20 : Ωˣ, ∀ t : Ω,
      ρ (xMinus t) = pinnedX Tag.F4 Ω (r 2 0) ((ε20 : Ω) * t))
    (F : Subfield Ω) (μ : Ω)
    (hmemPlus : ∀ t : Ω,
      P μ * xPlus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔ t ^ (2 ^ f) = t)
    (hmemMinus : ∀ t : Ω,
      P μ * xMinus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔ t ^ (2 ^ f) = t) :
    ∃ ε02 ε20 : Ωˣ,
      conjugatedRootRange (k := k) (ρ (H * P μ)) (r 0 2) ε02 ≤ (kappaSU ρ H F 2 f).range ∧
      conjugatedRootRange (k := k) (ρ (H * P μ)) (r 2 0) ε20 ≤ (kappaSU ρ H F 2 f).range := by
  obtain ⟨ε02, ε20, hpair⟩ :=
    kappaSU_pair_all (Ω := Ω) (f := f) hk ρ H hrootPlus hrootMinus F μ hmemPlus hmemMinus
  refine ⟨ε02, ε20, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, rfl⟩ :=
      (mem_conjugatedRootRange_iff (k := k) (ρ (H * P μ)) (r 0 2) ε02 y).mp hy
    exact MonoidHom.mem_range.mpr (hpair t).1
  · intro y hy
    obtain ⟨t, rfl⟩ :=
      (mem_conjugatedRootRange_iff (k := k) (ρ (H * P μ)) (r 2 0) ε20 y).mp hy
    exact MonoidHom.mem_range.mpr (hpair t).2

end FiniteRootGroups

section Quasisimplicity

variable {Ω : Type} [Field Ω]

theorem isQuasisimple_kappaSL_range {k : Type} [Field k] [Algebra k Ω]
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω)) (hρinj : Function.Injective ρ) :
    CFSG.IsQuasisimple ↥(kappaSL (k := k) ρ H).range :=
  CFSG.IsQuasisimple.of_mulEquiv
    (MonoidHom.ofInjective (kappaSL_injective (k := k) ρ H hρinj)).symm
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := k) (n := 3) (by norm_num))

section Unitary

variable [IsAlgClosed Ω] [CharP Ω 2]

theorem isQuasisimple_kappaSU_range {F : Subfield Ω} {f : ℕ} (hf : 2 ≤ f)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω)) (hρinj : Function.Injective ρ) :
    CFSG.IsQuasisimple ↥(kappaSU ρ H F 2 f).range := by
  have hnq : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 := (Prod.mk.injEq 3 (2 ^ f) 3 2).mp h |>.2
    have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [h2] at hle
    norm_num at hle
  have : CharP ↥F 2 := (RingHom.charP_iff F.subtype F.subtype.injective 2).mpr inferInstance
  have : Finite ↥F :=
    Nat.finite_of_card_ne_zero (by rw [hFcard]; exact pow_ne_zero 2 (pow_ne_zero f (by norm_num)))
  have hqs := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := ↥F) (p := 2) (f := f) hFcard (n := 3) (by norm_num) hnq
  exact CFSG.IsQuasisimple.of_mulEquiv
    (MonoidHom.ofInjective (kappaSU_injective ρ H F 2 f hρinj)).symm hqs.1

theorem isSolvable_kappaSU_range_one {F : Subfield Ω}
    (hFcard : Nat.card F = (2 ^ 1) ^ 2)
    (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω)) (hρinj : Function.Injective ρ) :
    Group.IsSolvable ↥(kappaSU ρ H F 2 1).range := by
  have : CharP ↥F 2 := (RingHom.charP_iff F.subtype F.subtype.injective 2).mpr inferInstance
  have : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  have hs := CFSG.Quasithin.isSolvable_statedSU_one (F := ↥F) hFcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (MonoidHom.ofInjective (kappaSU_injective ρ H F 2 1 hρinj)).symm.toMonoidHom)
    (MonoidHom.ofInjective (kappaSU_injective ρ H F 2 1 hρinj)).symm.injective

end Unitary

end Quasisimplicity

end CFSG.StandardType.F4ExplicitPos.RationalA2Finish
end

end

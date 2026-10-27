module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Attach
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB3Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalB3
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.B3Exact CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  C3Range C3Algebraic B2Finite
  CFSG.StandardType.F4ExplicitPos.B3Algebraic
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.F4ExplicitPos.RationalC3
open scoped Matrix

theorem map_PhiB_c3RootSubgroup
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Finite K] [CharP K 2]
    [Algebra K Ω] (n z : ModGL .F4 Ω) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ).map (PhiB (K := K) Ω n z) =
      (finitePinnedRootF4 (K := K) Ω (F4.dualRoot (c3ToF4 γ))).map
        (MulAut.conj (z * n)).toMonoidHom := by
  have hset : ((fun g => PhiB (K := K) Ω n z g) '' Set.range (Sp.x 3 K γ)) =
      (MulAut.conj (z * n)).toMonoidHom '' Set.range (fun c : K =>
        pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ)) (algebraMap K Ω c)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      refine ⟨pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (algebraMap K Ω (c ^ F4.exponent (pinnedData .F4 (c3ToF4 γ)).1)),
        ⟨c ^ F4.exponent (pinnedData .F4 (c3ToF4 γ)).1, rfl⟩, ?_⟩
      change (MulAut.conj (z * n))
          (pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
            (algebraMap K Ω (c ^ F4.exponent (pinnedData .F4 (c3ToF4 γ)).1))) =
        PhiB (K := K) Ω n z (Sp.x 3 K γ c)
      rw [PhiB_x_pinned (Ω := Ω) (hγ := hγ) (c := c), MulAut.conj_apply, map_pow]
      group
    · rintro ⟨p, ⟨d, rfl⟩, rfl⟩
      rcases CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exponent_F4_eq_one_or_two
        (pinnedData .F4 (c3ToF4 γ)).1 with he | he
      · refine ⟨Sp.x 3 K γ d, ⟨d, rfl⟩, ?_⟩
        change PhiB (K := K) Ω n z (Sp.x 3 K γ d) =
          (MulAut.conj (z * n))
            (pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ)) (algebraMap K Ω d))
        rw [PhiB_x_pinned (Ω := Ω) (hγ := hγ) (c := d), MulAut.conj_apply, he, pow_one]
        group
      · obtain ⟨c, hc⟩ :=
          CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exists_sq_eq_charTwo_narrow (K := K) d
        refine ⟨Sp.x 3 K γ c, ⟨c, rfl⟩, ?_⟩
        change PhiB (K := K) Ω n z (Sp.x 3 K γ c) =
          (MulAut.conj (z * n))
            (pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ)) (algebraMap K Ω d))
        rw [PhiB_x_pinned (Ω := Ω) (hγ := hγ) (c := c), MulAut.conj_apply, he]
        have hpow : ((algebraMap K Ω c) ^ 2 : Ω) = algebraMap K Ω d := by
          rw [← map_pow, hc]
        rw [hpow]
        group
  unfold finitePinnedRootF4
  rw [C3Range.c3RootSubgroup, MonoidHom.map_closure, MonoidHom.map_closure, hset]

theorem component_eq_range_PhiB_of_le_cent
    (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K Ω]
    (D : LangDatum .F4 Ω) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n z : ModGL .F4 Ω) (hn_adj : n ∈ adjointGroup .F4 Ω)
    (hz_adj : z ∈ adjointGroup .F4 Ω)
    (hn : bcGL (τ := .F4) Fr n = n)
    (hzH : ∀ g, g ∈ MonoidHom.range (conjBM Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjBM Ω n))
    (hzF : ∀ g ∈ MonoidHom.range (conjBM Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := .F4) Fr g * z⁻¹)
    {C Ccent : Subgroup (ModGL .F4 Ω)} (hC : C = D.Γ ⊓ Ccent)
    (hHcent : MonoidHom.range (conjBM Ω n) ≤ Ccent)
    {P : Subgroup (ModGL .F4 Ω)}
    (hP : CFSG.Assembly.IsComponentOf P C)
    (hPleH : P ≤ MonoidHom.range (conjBM Ω n)) :
    P = MonoidHom.range (PhiB (K := K) Ω n z) := by
  set N : Subgroup (ModGL .F4 Ω) := MonoidHom.range (PhiB (K := K) Ω n z) with hN
  have hrange := range_PhiB_eq_inf_model (Ω := Ω) (K := K) D Fr hFr n z hn_adj hz_adj hn hzH hzF
  have hNdef : N = MonoidHom.range (conjBM Ω n) ⊓ D.model := by
    rw [hN]; exact hrange
  have hNq : CFSG.IsQuasisimple ↥N := by
    rw [hN]
    exact isQuasisimple_range_PhiB (Ω := Ω) (K := K) n z
  have hperf : Group.IsPerfect ↥N := by
    rw [hN]
    exact isPerfect_range_PhiB (Ω := Ω) (K := K) n z
  have hNleM : N ≤ D.model := by
    rw [hNdef]; exact inf_le_right
  have hNΓ : N ≤ D.Γ := by
    have : Group.IsPerfect ↥N := hperf
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅D.model, D.model⁆ := Subgroup.commutator_mono hNleM hNleM
      _ = D.Γ := rfl
  have hNcent : N ≤ Ccent := by
    rw [hNdef]; exact inf_le_left.trans hHcent
  have hNleC : N ≤ C := by
    rw [hC]; exact le_inf hNΓ hNcent
  have hΓleM : D.Γ ≤ D.model := Subgroup.commutator_le_self D.model
  have hKleΓ : P ≤ D.Γ := by
    have h := hP.1
    rw [hC] at h
    exact h.trans inf_le_left
  have hPN : P = N :=
    RationalC3Attach.eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
      (C := C) (M := D.model) (Γ := D.Γ) (H := MonoidHom.range (conjBM Ω n))
      (N := N) (K := P) hNdef hΓleM hNleC hNq hP hPleH hKleΓ hP.2.2
  exact hPN.trans hN

theorem conjBM_eq
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) :
    conjBM Ω n =
      (MulAut.conj n).toMonoidHom.comp ((adjointGroup .F4 Ω).subtype.comp (iBΩ Ω)) := by
  rw [conjBM]

theorem PhiB_eq
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) :
    PhiB (K := K) Ω n z =
      ((MulAut.conj z).toMonoidHom.comp (conjBM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3) := by
  rw [PhiB]

end CFSG.StandardType.F4ExplicitPos.RationalB3

end

end

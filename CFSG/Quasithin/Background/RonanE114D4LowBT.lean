module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.Open CFSG.LieType.BorelTits

theorem exists_invariant_parabolic {X : Type*} [Group X] [Finite X]
    (hBT : Holds X 2) (Φ : Subgroup (MulAut X)) {R₀ : Subgroup X} (hR₀ : R₀ ≠ ⊥)
    (hR₀2 : IsPGroup 2 R₀) (hΦR₀ : ∀ φ ∈ Φ, R₀.map φ.toMonoidHom = R₀) :
    ∃ (P : Subgroup X) (S : Sylow 2 X), P ≠ ⊤ ∧ (∀ φ ∈ Φ, P.map φ.toMonoidHom = P) ∧
      Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P := by
  set 𝒮 : Set (Subgroup X) :=
    {R | R₀ ≤ R ∧ IsPGroup 2 R ∧ ∀ φ ∈ Φ, R.map φ.toMonoidHom = R}
  have hR₀mem : R₀ ∈ 𝒮 := ⟨le_rfl, hR₀2, hΦR₀⟩
  obtain ⟨R, ⟨hR₀R, hR2, hRΦ⟩, hmax⟩ :=
    WellFounded.has_min (wellFounded_gt : WellFounded (· > · : Subgroup X → Subgroup X → Prop))
      𝒮 ⟨R₀, hR₀mem⟩
  have hRne : R ≠ ⊥ := by
    intro h
    apply hR₀
    rw [h] at hR₀R
    exact le_bot_iff.mp hR₀R
  have hNΦ : ∀ φ ∈ Φ, (Subgroup.normalizer (R : Set X)).map φ.toMonoidHom =
      Subgroup.normalizer (R : Set X) := by
    intro φ hφ
    rw [Subgroup.map_equiv_normalizer_eq, hRΦ φ hφ]
  have hRN : R ≤ pCoreOf 2 (Subgroup.normalizer (R : Set X)) := le_pCoreOf_normalizer 2 R hR2
  have hR'Φ : ∀ φ ∈ Φ, (pCoreOf 2 (Subgroup.normalizer (R : Set X))).map φ.toMonoidHom =
      pCoreOf 2 (Subgroup.normalizer (R : Set X)) := by
    intro φ hφ
    rw [← pCoreOf_map_mulEquiv 2 φ, hNΦ φ hφ]
  have hR'mem : pCoreOf 2 (Subgroup.normalizer (R : Set X)) ∈ 𝒮 :=
    ⟨hR₀R.trans hRN, pCoreOf_isPGroup 2 _, hR'Φ⟩
  have hR'eq : pCoreOf 2 (Subgroup.normalizer (R : Set X)) = R := by
    by_contra hne
    exact hmax _ hR'mem (lt_of_le_of_ne hRN (Ne.symm hne))
  obtain ⟨S, P, hP, hN, -, hRP, hS⟩ := hBT R hRne hR2
  have hNQ : Subgroup.normalizer (R : Set X) ≤
      Subgroup.normalizer ((pCoreOf 2 P : Subgroup X) : Set X) :=
    hN.trans (le_normalizer_pCoreOf 2 P)
  have hkey : Subgroup.normalizer (R : Set X) ⊓ pCoreOf 2 P ≤ R := by
    have hnorm : Subgroup.normalizer (R : Set X) ≤
        Subgroup.normalizer ((Subgroup.normalizer (R : Set X) ⊓ pCoreOf 2 P : Subgroup X) :
          Set X) :=
      (le_inf Subgroup.le_normalizer hNQ).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hle := le_pCoreOf_of_le_normalizer 2 (inf_le_left :
      Subgroup.normalizer (R : Set X) ⊓ pCoreOf 2 P ≤ Subgroup.normalizer (R : Set X)) hnorm
      (IsPGroup.to_le (pCoreOf_isPGroup 2 P) inf_le_right)
    rw [hR'eq] at hle
    exact hle
  have hRQ : R ≤ pCoreOf 2 P := hRP
  have hle' : Subgroup.normalizer ((R.subgroupOf (pCoreOf 2 P) : Subgroup (pCoreOf 2 P)) :
      Set (pCoreOf 2 P)) ≤ R.subgroupOf (pCoreOf 2 P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRQ]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hkey (Subgroup.mem_inf.mpr ⟨hx, x.2⟩)
  haveI : Group.IsNilpotent (pCoreOf 2 P : Subgroup X) :=
    IsPGroup.isNilpotent (pCoreOf_isPGroup 2 P)
  have hnc := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (pCoreOf 2 P : Subgroup X)))
  have htop : R.subgroupOf (pCoreOf 2 P) = ⊤ := hnc _ (le_antisymm hle' Subgroup.le_normalizer)
  have hQeq : pCoreOf 2 P = R := le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hRP
  have hPN : P = Subgroup.normalizer (R : Set X) := by
    apply le_antisymm _ hN
    have h := le_normalizer_pCoreOf 2 P
    rwa [hQeq] at h
  refine ⟨P, S, hP, ?_, hS⟩
  intro φ hφ
  rw [hPN]
  exact hNΦ φ hφ

end CFSG.Quasithin.RonanE114Low

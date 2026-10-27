module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem map_conj_centralizer {c s e : G} (hsc : s * c * s⁻¹ = e) (hce : e = c ∨ e = c⁻¹) :
    (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj s).toMonoidHom =
      Subgroup.centralizer ({c} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  change s⁻¹ * y * s * c = c * (s⁻¹ * y * s) ↔ y * c = c * y
  have h1 : s⁻¹ * y * s * c = c * (s⁻¹ * y * s) ↔ y * e = e * y := by
    rw [← hsc]
    constructor
    · intro h
      calc y * (s * c * s⁻¹) = s * (s⁻¹ * y * s * c) * s⁻¹ := by group
        _ = s * (c * (s⁻¹ * y * s)) * s⁻¹ := by rw [h]
        _ = (s * c * s⁻¹) * y := by group
    · intro h
      calc s⁻¹ * y * s * c = s⁻¹ * (y * (s * c * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * c * s⁻¹) * y) * s := by rw [h]
        _ = c * (s⁻¹ * y * s) := by group
  rw [h1]
  rcases hce with rfl | rfl
  · exact Iff.rfl
  · exact Commute.inv_right_iff

theorem thetaComponentsIn_eq_of_perfect_le {H L₁ L₂ P : Subgroup G}
    (h₁ : L₁ ∈ thetaComponentsIn H) (h₂ : L₂ ∈ thetaComponentsIn H) (hP1 : P ≠ ⊥)
    (hP : Group.IsPerfect P) (hP₁ : P ≤ L₁) (hP₂ : P ≤ L₂) : L₁ = L₂ := by
  obtain ⟨hL₁H, hL₁⟩ := mem_thetaComponentsIn_iff.mp h₁
  obtain ⟨hL₂H, hL₂⟩ := mem_thetaComponentsIn_iff.mp h₂
  have hPH : P ≤ H := hP₁.trans hL₁H
  have hP1' : P.subgroupOf H ≠ ⊥ := by
    intro h
    apply hP1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hPperf : Group.IsPerfect (P.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have heq := theta_component_eq_of_perfect_le Nat.prime_three hL₁ hL₂ hP1' hPperf
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hP₁ (Subgroup.mem_subgroupOf.mp hx)))
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hP₂ (Subgroup.mem_subgroupOf.mp hx)))
  rw [Subgroup.subgroupOf_inj] at heq
  rwa [inf_of_le_left hL₁H, inf_of_le_left hL₂H] at heq

theorem map_conj_eq_of_image {K D : Subgroup G} {c s e : G}
    (hD : D ∈ thetaComponentsIn (K ⊓ Subgroup.centralizer ({c} : Set G)))
    (hsK : s ∈ K) (hsc : s * c * s⁻¹ = e) (hce : e = c ∨ e = c⁻¹)
    (himg : ∀ x ∈ D, ∃ y ∈ D,
      y⁻¹ * (s * x * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    D.map (MulAut.conj s).toMonoidHom = D := by
  set M := K ⊓ Subgroup.centralizer ({c} : Set G) with hM
  have hKs : K.map (MulAut.conj s).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsK)
  have hMs : M.map (MulAut.conj s).toMonoidHom = M := by
    rw [hM, Subgroup.map_inf _ _ _ (MulAut.conj s).injective, hKs, map_conj_centralizer hsc hce]
  have hD' : D.map (MulAut.conj s).toMonoidHom ∈ thetaComponentsIn M := by
    have := map_mem_thetaComponentsIn (MulAut.conj s) hD
    rwa [hMs] at this
  have hDp : Group.IsPerfect D := isPerfect_of_mem_thetaComponentsIn hD
  have hDp' : Group.IsPerfect (D.map (MulAut.conj s).toMonoidHom) :=
    Group.IsPerfect.ofSurjective
      (f := (D.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
        ).toMonoidHom) (MulEquiv.surjective _)
  have hDM : D ≤ M := le_of_mem_thetaComponentsIn hD
  have hD'M : D.map (MulAut.conj s).toMonoidHom ≤ M := le_of_mem_thetaComponentsIn hD'
  have hMK : M ≤ K := inf_le_left
  have hle : D.map (MulAut.conj s).toMonoidHom ≤ D := by
    refine Sec6.le_of_isPerfect_of_le_sup_theta hD hDp' ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyθ⟩ := himg x hx
    have hsx : s * x * s⁻¹ ∈ M := hD'M ⟨x, hx, rfl⟩
    have hmem : y⁻¹ * (s * x * s⁻¹) ∈ M :=
      M.mul_mem (M.inv_mem (hDM hy)) hsx
    have h1 : y⁻¹ * (s * x * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) M :=
      PartOne.Sec9A.inf_inSubgroup_theta_le Nat.prime_three hMK ⟨hmem, hyθ⟩
    have : s * x * s⁻¹ = y * (y⁻¹ * (s * x * s⁻¹)) := by group
    change s * x * s⁻¹ ∈ _
    rw [this]
    exact Subgroup.mul_mem_sup hy h1
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj s).injective])

theorem mem_normalizer_of_map_conj_eq {L D : Subgroup G} {c s e : G}
    (hL : L ∈ thetaComponentsAt 3 c) (hDL : D ≤ L) (hD1 : D ≠ ⊥) (hDp : Group.IsPerfect D)
    (hsD : D.map (MulAut.conj s).toMonoidHom = D) (hsc : s * c * s⁻¹ = e)
    (hce : e = c ∨ e = c⁻¹) : s ∈ Subgroup.normalizer (L : Set G) := by
  have hL' : L.map (MulAut.conj s).toMonoidHom ∈ thetaComponentsAt 3 e := by
    have := map_mem_thetaComponentsAt (MulAut.conj s) hL
    rwa [show (MulAut.conj s) c = e from hsc] at this
  have hec : thetaComponentsAt 3 e = thetaComponentsAt 3 c := by
    rcases hce with rfl | rfl
    · rfl
    · rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn]
      have : Subgroup.centralizer ({c⁻¹} : Set G) = Subgroup.centralizer ({c} : Set G) := by
        ext y
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
        exact Commute.inv_right_iff
      rw [this]
  rw [hec, thetaComponentsAt_eq_thetaComponentsIn] at hL'
  rw [thetaComponentsAt_eq_thetaComponentsIn] at hL
  have hDL' : D ≤ L.map (MulAut.conj s).toMonoidHom := by
    rw [← hsD]
    exact Subgroup.map_mono hDL
  have := thetaComponentsIn_eq_of_perfect_le hL hL' hD1 hDp hDL hDL'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm

end CFSG.RankThree.PartTwo.Sec8.Hering611

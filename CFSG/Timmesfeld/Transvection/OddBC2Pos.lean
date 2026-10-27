module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.OddLocal
public import CFSG.Timmesfeld.Transvection.PresSU
public import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.OddBC2Hom
import CFSG.Timmesfeld.Transvection.OddBC2Comm
import CFSG.Timmesfeld.Transvection.OddPairsCone
import CFSG.Timmesfeld.Transvection.OddPairsModel
import CFSG.Timmesfeld.Transvection.OddModelPairs
import CFSG.Timmesfeld.Transvection.OddModelBC2Struct
public import CFSG.Timmesfeld.ARS.ConfigTransfer
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec8Levi
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Timmesfeld.Transvection.PlaneGroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

section Abstract

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

local notation "X" γ:max => CFSG.LieType.Universal.Unitary.rootGroup
  (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r + 1) γ
local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2)))

namespace OddFrameCompatible

private structure Bc2Values
    (φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H) : Prop where
  onQ0 : ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
      X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
    x ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr →
      ∀ y : SU (unitaryInvolution F 2 n) (2 * r),
        oddEmb (unitaryInvolution F 2 n) r y = x → φ ⟨x, hx⟩ = Ψ₀ y
  onHeis : ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
      X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
    x ∈ X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
      ∀ A : SU (unitaryInvolution F 2 n) 3,
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcPrevIdx r hr) A = x →
          φ ⟨x, hx⟩ = oddPrevLift hFn hr Ψ₀ θ A
  onLast : ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
      X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
    x ∈ X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
      ∀ A : SU (unitaryInvolution F 2 n) 3,
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr)) A = x →
          φ ⟨x, hx⟩ = θ A

variable {hFn hr Ψ₀ θ}

private theorem eq_oddFrameMap_of_mem_bc2Q0
    {φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφ : Bc2Values hFn hr Ψ₀ θ φ)
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hev : Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))))
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (hx0 : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr) :
    φ ⟨x, hx⟩ = oddFrameMap hFn hr Ψ₀ θ γ x := by
  obtain ⟨y, hy⟩ := bc2Q0_le_range_oddEmb
    (σ := unitaryInvolution F 2 n) (hσ := unitaryInvolution_involutive hFn) (hr := hr) hx0
  exact (hφ.onQ0 x hx hx0 y hy).trans (oddFrameMap_eq_of_even hFn hr Ψ₀ θ hev x y hy).symm

private theorem eq_oddFrameMap_of_mem_last
    {φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφ : Bc2Values hFn hr Ψ₀ θ φ)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    φ ⟨x, hx⟩ =
      oddFrameMap hFn hr Ψ₀ θ (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) x := by
  have hγne : ¬Even ((Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.single_eq_same]
    exact Int.not_even_one
  have hP0 : (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcPrevIdx r hr) = 0 := by
    rw [Pi.single_eq_of_ne (bcPrevIdx_ne_bcLastIdx hr)]
  have hmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))).range :=
    rootGroup_le_range_su3Emb (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r)
      (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) (toStd_bc2 hr).2.1 x.2
  obtain ⟨A, hA⟩ := hmem
  exact (hφ.onLast x hx x.2 A hA).trans
    (oddFrameMap_eq_of_last hFn hr Ψ₀ θ hγne hP0 x A hA).symm

private theorem eq_oddFrameMap_of_mem_two_smul_last
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφ : Bc2Values hFn hr Ψ₀ θ φ)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    φ ⟨x, hx⟩ =
      oddFrameMap hFn hr Ψ₀ θ (2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) x := by
  obtain ⟨c, hc0, hxc⟩ := (mem_rootGroup_iff_suLong_odd
    (unitaryInvolution_involutive hFn) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
    (toStd_bc2 hr).2.2.1 x).mp x.2
  have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
  have hxL : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
    rw [← hxc, ← suHeis_zero_left (σ := unitaryInvolution F 2 n)
      (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
      (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c]
    exact suHeis_mem (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
      (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) (toStd_bc2 hr).2.1 0 c
  have hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr))
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) = x := by
    rw [su3Emb_suLong_inl, hxc]
  have hev : Even ((2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.smul_apply, Pi.single_eq_same]
    exact ⟨1, by norm_num⟩
  have hy : oddEmb (unitaryInvolution F 2 n) r
      (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) c) = x := by
    rw [oddEmb_suLong, sCast_inl, finCastOdd_cLastIdx, hxc]
  exact (hφ.onLast x hx hxL
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) hA).trans
    ((oddFrameMap_eq_of_even hFn hr Ψ₀ θ hev x _ hy).trans (hd.long_last c hc).1).symm

private theorem eq_oddFrameMap_of_mem_heis_prev
    {φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφ : Bc2Values hFn hr Ψ₀ θ φ)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    φ ⟨x, hx⟩ = oddFrameMap hFn hr Ψ₀ θ
      (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) x := by
  have hmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcPrevIdx r hr)).range :=
    rootGroup_le_range_su3Emb (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r)
      (a := Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.1 x.2
  obtain ⟨A, hA⟩ := hmem
  exact (hφ.onHeis x hx x.2 A hA).trans
    (oddFrameMap_eq_of_toStd_prev hFn hr Ψ₀ θ
      (a := Sum.inl (bcPrevIdx r hr)) rfl (toStd_bc2 hr).2.2.2.1 x A hA).symm

private theorem eq_oddFrameMap_of_mem_bc2U
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφ : Bc2Values hFn hr Ψ₀ θ φ)
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
      (CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    φ ⟨x, hx⟩ = oddFrameMap hFn hr Ψ₀ θ γ x := by
  obtain ⟨a, b, hab, hγe⟩ :=
    (mem_pairRoots_bc2_pos (p := 2) (f := n) hFn hr).1 hγ
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [one_smul, zero_smul, add_zero] at hγe
    subst hγe
    have hev : Even ((Pi.single (bcPrevIdx r hr) 1 : Fin ((2 * r + 1) / 2) → ℤ)
        (bcLastIdx r (Nat.one_le_of_lt hr))) := by
      rw [Pi.single_apply, if_neg (bcPrevIdx_ne_bcLastIdx hr).symm]
      exact ⟨0, by norm_num⟩
    have hx0 : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        bc2Q0 (unitaryInvolution_involutive hFn) hr := by
      rw [bc2Q0]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left x.2)
    exact eq_oddFrameMap_of_mem_bc2Q0 hφ hev x hx hx0
  · simp only [one_smul, zero_smul, zero_add] at hγe
    subst hγe
    exact eq_oddFrameMap_of_mem_last hφ x hx
  · simp only [zero_smul, zero_add] at hγe
    subst hγe
    exact eq_oddFrameMap_of_mem_two_smul_last hd hφ x hx
  · simp only [one_smul] at hγe
    subst hγe
    exact eq_oddFrameMap_of_mem_heis_prev hφ x hx
  · simp only [one_smul] at hγe
    subst hγe
    have hev : Even (((Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) :
          Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg (bcPrevIdx_ne_bcLastIdx hr).symm, if_pos rfl]
      exact ⟨1, by norm_num⟩
    have hx0 : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        bc2Q0 (unitaryInvolution_involutive hFn) hr := by
      rw [bc2Q0]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right x.2)
    exact eq_oddFrameMap_of_mem_bc2Q0 hφ hev x hx hx0
  · subst hγe
    have hev : Even (((2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) :
          Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg (bcPrevIdx_ne_bcLastIdx hr).symm, if_pos rfl]
      exact ⟨1, by norm_num⟩
    have hx0 : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        bc2Q0 (unitaryInvolution_involutive hFn) hr := by
      rw [bc2Q0]
      exact Subgroup.mem_sup_right x.2
    exact eq_oddFrameMap_of_mem_bc2Q0 hφ hev x hx hx0

theorem extendsToHom_pairRoots_bc2_pos
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hprev_inr : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
    (hprev_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    (hlast_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ =
          Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n u * u')))
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s), θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr Ψ₀ θ
              (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
            Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
              (s * unitaryInvolution F 2 n v))) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
          (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
        (CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
      (oddFrameMap hFn hr Ψ₀ θ) := by
  obtain ⟨φ, hφQ0, hφP, hφL⟩ :=
    hd.exists_hom_bc2U hprev_inr hprev_inl hlast_inl hheis hshort
  refine ⟨_, φ, fun γ hγ x => ?_⟩
  exact ⟨rootGroup_le_bc2U (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (hr := hr) (p := 2) (f := n) hFn hγ x.2,
    eq_oddFrameMap_of_mem_bc2U hd ⟨hφQ0, hφP, hφL⟩ hγ x _⟩

end OddFrameCompatible

end Abstract

section Frame

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2)))

theorem SURelations.HasFrameImages.extendsToHom_pairRoots_bc2_pos_toHom
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsFrame Δ P Q) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθ'r : (oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ).range =
      residueGroup Δ P Q (cPrevIdx r hr))
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v),
          oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ (heis₃ u' v')⁆ =
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n u * u'))
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s, θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
              (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
              (s * unitaryInvolution F 2 n v)) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
          (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
        (CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
      (oddFrameMap hFn hr (R.toHom hFn (even_two_mul r) hm) θ) := by
  have hPL : cPrevIdx r hr ≠ cLastIdx r hr := by
    intro e
    exact bcPrevIdx_ne_bcLastIdx hr
      (by rw [← finCastOdd_cPrevIdx hr, e, finCastOdd_cLastIdx hr])
  obtain ⟨hθt, hθb⟩ := hR.map_su3Top_of_suLong (cLastIdx r hr) fun c hc =>
    ⟨(hd.long_last c hc).1.symm.trans
        (R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cLastIdx r hr)) hc),
      (hd.long_last c hc).2.symm.trans
        (R.toHom_suLong hFn (even_two_mul r) hm (Sum.inr (cLastIdx r hr)) hc)⟩
  obtain ⟨hθ't, hθ'b⟩ := hR.map_su3Top_of_suLong (cPrevIdx r hr) fun c hc =>
    ⟨(hd.oddPrevLift_suLong_inl hc).trans
        (R.toHom_suLong hFn (even_two_mul r) hm (Sum.inl (cPrevIdx r hr)) hc),
      (hd.oddPrevLift_suLong_inr hc).trans
        (R.toHom_suLong hFn (even_two_mul r) hm (Sum.inr (cPrevIdx r hr)) hc)⟩
  have hB' := hR.commute_map_suHeis_short h hML hq hF hFn hcard hθ'r hθ't hθ'b hPL.symm
  have hB := hR.commute_map_suHeis_short h hML hq hF hFn hcard hθr hθt hθb hPL
  refine hd.extendsToHom_pairRoots_bc2_pos
    (fun u v _ c => ?_) (fun u v _ c => ?_) (fun u v _ c => ?_)
    (fun u v u' v' h₁ h₂ => ?_) (fun s u v h₁ => ?_)
  · rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inr (cLastIdx r hr)) hPL]
    exact (hB' u v c).1
  · rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inl (cLastIdx r hr)) hPL]
    exact (hB' u v c).2.1
  · rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inl (cLastIdx r hr)) hPL]
    exact (hB u v c).2.2
  · rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inl (cLastIdx r hr)) hPL]
    exact hheis u v u' v' h₁ h₂
  · rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inr (cLastIdx r hr)) hPL]
    rw [R.toHom_suElt hFn (even_two_mul r) hm (a := Sum.inl (cPrevIdx r hr))
      (b := Sum.inl (cLastIdx r hr)) hPL]
    exact hshort s u v h₁

end Frame

end CFSG.Timmesfeld.Transvection

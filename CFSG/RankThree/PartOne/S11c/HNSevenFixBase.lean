
module

public import CFSG.RankThree.PartOne.S11c.HNCoverAbstract
public import CFSG.RankThree.PartOne.S11c.HNSevenInputs
public import CFSG.Sporadic.HNOddCore.InvRow2
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

@[expose] public noncomputable section

namespace CFSG.RankThree.PartOne.HNRed

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native
open CFSG.RankThree.PartOne.HNRed.Native

section Abstract

variable {G X S : Type*} [Group G] [MulAction G X] [Group S]

theorem smul_eq_of_mem_centralizer {u : G} {x : X} (hux : u • x = x)
    (hfix : ∀ y : X, u • y = y → y = x) {c : G} (hc : c ∈ centralizer ({u} : Set G)) :
    c • x = x := by
  have hcomm : c * u = u * c := mem_centralizer_singleton_iff.1 hc
  apply hfix
  rw [← mul_smul, ← hcomm, mul_smul, hux]

theorem card_centralizer_dvd_of_embedding {H₀ : Subgroup G} (θ : H₀ →* S)
    (hθ : Function.Injective θ) {u : G} (hu : u ∈ H₀) (hle : centralizer ({u} : Set G) ≤ H₀) :
    Nat.card (centralizer ({u} : Set G)) ∣ Nat.card (centralizer ({θ ⟨u, hu⟩} : Set S)) := by
  let φ : centralizer ({u} : Set G) →* S := θ.comp (Subgroup.inclusion hle)
  have hφ : Function.Injective φ := hθ.comp (Subgroup.inclusion_injective hle)
  have hrange : φ.range ≤ centralizer ({θ ⟨u, hu⟩} : Set S) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm : (c : G) * u = u * c := mem_centralizer_singleton_iff.1 c.2
    have h1 : (⟨c, hle c.2⟩ : H₀) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨c, hle c.2⟩ := Subtype.ext hcomm
    calc φ c * θ ⟨u, hu⟩ = θ ((⟨c, hle c.2⟩ : H₀) * ⟨u, hu⟩) := by rw [map_mul]; rfl
      _ = θ (⟨u, hu⟩ * ⟨c, hle c.2⟩) := by rw [h1]
      _ = θ ⟨u, hu⟩ * φ c := by rw [map_mul]; rfl
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact Subgroup.card_dvd_of_le hrange

theorem orderOf_coe_of_equiv {H₀ : Subgroup G} (θ : H₀ ≃* S) (h : H₀) {n : ℕ}
    (hn : orderOf (θ h) = n) : orderOf (h : G) = n := by
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ, hn]

end Abstract

@[expose] def sigma7 : Perm (Fin 12) := List.formPerm [(1 : Fin 12), 4, 3, 7, 6, 2, 11]

theorem sigma7_isCycle : sigma7.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem sigma7_support_card : sigma7.support.card = 7 := by
  rw [sigma7, List.support_formPerm_of_nodup _ (by decide) (by decide)]
  decide

theorem sigma7_cycleType : sigma7.cycleType = {7} := by
  rw [sigma7_isCycle.cycleType, sigma7_support_card]

theorem orderOf_sigma7 : orderOf sigma7 = 7 := by
  rw [sigma7_isCycle.orderOf, sigma7_support_card]

theorem card_centralizer_sigma7 :
    Nat.card (centralizer ({sigma7} : Set (Perm (Fin 12)))) = 840 := by
  rw [Equiv.Perm.nat_card_centralizer, sigma7_cycleType]
  simp [Nat.factorial]

theorem prep_sigma7 : PRep 12 (natArr cyc7) sigma7 := by
  unfold PRep
  decide

abbrev sevenJ : JH := hWordJ sevenWord

theorem thetaHom_injective :
    Function.Injective thetaHom :=
  Subtype.val_injective.comp thetaJ.injective

end CFSG.RankThree.PartOne.HNRed

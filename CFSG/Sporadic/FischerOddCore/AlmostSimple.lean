module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem oddCore_eq_bot_of_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hle : CFSG.oddCore G ≤ M) (hM : CFSG.oddCore M = ⊥) : CFSG.oddCore G = ⊥ := by
  have hN : ((CFSG.oddCore G).subgroupOf M).Normal :=
    Subgroup.Normal.subgroupOf inferInstance M
  have hc : Nat.card ((CFSG.oddCore G).subgroupOf M) = Nat.card (CFSG.oddCore G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h := le_oddCore_of_normal hN (hc ▸ odd_card_oddCore)
  rw [hM, le_bot_iff, Subgroup.subgroupOf_eq_bot] at h
  exact disjoint_self.1 (h.mono_right hle)

theorem odd_orderOf_of_mem_oddCore {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ CFSG.oddCore G) : Odd (orderOf x) := by
  have h := Subgroup.orderOf_dvd_natCard (CFSG.oddCore G) hx
  exact Odd.of_dvd_nat odd_card_oddCore h

variable {X : Type*} [Group X] {S : Subgroup X} [S.Normal] {Q : Type*} [Group Q]

@[expose] def conjTransport (θ : S ≃* Q) : X →* MulAut Q where
  toFun x := (θ.symm.trans (MulAut.conjNormal x)).trans θ
  map_one' := by
    ext q
    simp
  map_mul' x y := by
    ext q
    simp [map_mul, MulAut.mul_apply]

theorem conjTransport_apply (θ : S ≃* Q) (x : X) (q : Q) :
    conjTransport θ x q = θ (MulAut.conjNormal x (θ.symm q)) :=
  rfl

theorem conjTransport_apply_map (θ : S ≃* Q) (x : X) (s : S) :
    conjTransport θ x (θ s) = θ (MulAut.conjNormal x s) := by
  rw [conjTransport_apply, MulEquiv.symm_apply_apply]

theorem conjTransport_of_mem (θ : S ≃* Q) (s : S) :
    conjTransport θ (s : X) = MulAut.conj (θ s) := by
  ext q
  rw [conjTransport_apply, MulAut.conj_apply]
  have e : MulAut.conjNormal (s : X) (θ.symm q) = s * θ.symm q * s⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conjTransport_injective (θ : S ≃* Q) (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    Function.Injective (conjTransport θ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 := conjTransport_apply_map θ x ⟨s, hs⟩
  rw [hx, MulAut.one_apply] at h1
  have h2 := congrArg Subtype.val (θ.injective h1)
  rw [MulAut.conjNormal_apply] at h2
  change s = x * s * x⁻¹ at h2
  calc s * x = x * s * x⁻¹ * x := by rw [← h2]
    _ = x * s := by group

theorem centralizer_eq_bot_of_center_eq_bot {F : Subgroup X}
    (hle : Subgroup.centralizer (F : Set X) ≤ F) (hZ : Subgroup.center F = ⊥) :
    Subgroup.centralizer (F : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxF := hle hx
  have hz : (⟨x, hxF⟩ : F) ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)
  rw [hZ, Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hz

theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro h
    rw [← e.apply_symm_apply h, ← map_mul, ← map_mul, hz]
  rw [hH, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
  rw [Subgroup.mem_bot]
  exact this

theorem centralizer_generalizedFitting_eq_bot_of_center [Finite X]
    (hZ : Subgroup.center (CFSG.generalizedFitting X) = ⊥) :
    Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
  centralizer_eq_bot_of_center_eq_bot (CFSG.centralizer_generalizedFitting_le X) hZ

end CFSG.Sporadic.FischerOddCore

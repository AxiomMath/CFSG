module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Inner rotation torus in an index-two subgroup

A reflected cyclic subgroup crossing a normal index-two subgroup has an
inner half-sized rotation subgroup.  An aligned inner reflector recovers the
involution centralizer inside the index-two subgroup, and the rotation
subgroup is characteristic there.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Transport a reflected full torus through a normal index-two subgroup.
The resulting rotation torus has half the order, has an inner reflector, and
is characteristic in the inner involution centralizer. -/
public theorem innerRotationTorus_data_of_reflected_index_two
    {G : Type u} [Group G] [Finite G]
    (H U : Subgroup G) (hHindex : H.index = 2)
    (hUcyc : IsCyclic U) (m : ℕ) (hm3 : 3 ≤ m)
    (hUcard : Nat.card U = 2 * m) (hUnot : ¬ U ≤ H)
    (s : G) (hsU : s ∈ U) (hsI : IsInvolution s)
    (w : G) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hcent : Subgroup.centralizer ({s} : Set G) =
      U ⊔ Subgroup.zpowers w)
    (hjoinCard : Nat.card (U ⊔ Subgroup.zpowers w : Subgroup G) =
      2 * Nat.card U) :
    let T := U ⊓ H
    let C := Subgroup.centralizer ({s} : Set G) ⊓ H
    ∃ v : G,
      IsCyclic T ∧ Nat.card T = m ∧
      v ∈ H ∧ v ∉ U ∧ v * v = 1 ∧
      (∀ x : G, x ∈ U → v * x * v⁻¹ = x⁻¹) ∧
      C = T ⊔ Subgroup.zpowers v ∧
      (T.subgroupOf C).Characteristic := by
  classical
  let T : Subgroup G := U ⊓ H
  let C : Subgroup G := Subgroup.centralizer ({s} : Set G) ⊓ H
  letI : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  have hTcyc : IsCyclic T := by
    letI : IsCyclic U := hUcyc
    exact Subgroup.isCyclic_of_le (H := T) (H' := U) inf_le_left
  have hTcard : Nat.card T = m := by
    let TU : Subgroup U := H.subgroupOf U
    have hTUindex : TU.index = 2 := by
      have hdvd : TU.index ∣ 2 := by
        change H.relIndex U ∣ 2
        simpa [hHindex] using
          (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := U))
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
      · exfalso
        have htop : TU = ⊤ := Subgroup.index_eq_one.mp hone
        apply hUnot
        intro x hxU
        have hx : (⟨x, hxU⟩ : U) ∈ TU := by
          rw [htop]
          trivial
        exact hx
      · exact htwo
    have hTUcard : Nat.card TU = m := by
      have hmul := TU.card_mul_index
      rw [hTUindex, hUcard] at hmul
      omega
    let eT : T ≃* TU :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
        invFun := fun x => ⟨x, ⟨x.1.2, x.2⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_mul' := by intro x y; rfl }
    rw [Nat.card_congr eT.toEquiv, hTUcard]
  obtain ⟨a, haU, haH⟩ : ∃ a : G, a ∈ U ∧ a ∉ H := by
    by_contra h
    apply hUnot
    intro x hx
    by_contra hxH
    exact h ⟨x, hx, hxH⟩
  let v : G := if hwH : w ∈ H then w else w * a
  have hvH : v ∈ H := by
    dsimp [v]
    split_ifs with hwH
    · exact hwH
    · have hiff := Subgroup.mul_mem_iff_of_index_two hHindex
        (a := w) (b := a)
      exact hiff.mpr ⟨fun hw => False.elim (hwH hw),
        fun ha => False.elim (haH ha)⟩
  have hvU : v ∉ U := by
    dsimp [v]
    split_ifs with hwH
    · exact hwU
    · intro hv
      apply hwU
      have : w = (w * a) * a⁻¹ := by group
      rw [this]
      exact U.mul_mem hv (U.inv_mem haU)
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
  have hv_sq : v * v = 1 := by
    dsimp [v]
    split_ifs with hwH
    · exact hwsq
    · calc
        (w * a) * (w * a) = (w * a * w⁻¹) * a := by
          rw [hw_inv]
          group
        _ = a⁻¹ * a := by rw [hwinv a haU]
        _ = 1 := by simp
  have hv_inv : ∀ x : G, x ∈ U → v * x * v⁻¹ = x⁻¹ := by
    intro x hx
    dsimp [v]
    split_ifs with hwH
    · exact hwinv x hx
    · have hcomm : a * x = x * a := by
        letI : IsCyclic U := hUcyc
        letI : CommGroup U := IsCyclic.commGroup
        let aU : U := ⟨a, haU⟩
        let xU : U := ⟨x, hx⟩
        exact congrArg Subtype.val (mul_comm aU xU)
      calc
        (w * a) * x * (w * a)⁻¹ =
            w * (a * x * a⁻¹) * w⁻¹ := by group
        _ = w * x * w⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hcomm]
        _ = x⁻¹ := hwinv x hx
  obtain ⟨D, hDeq, hDleH, _hTindex, hDcard, _hDequiv⟩ :=
    exists_dihedral_subgroup_le_index_two_of_reflected_cyclic
      H U hHindex hUcyc m hUcard hUnot v hvH hvU hv_sq hv_inv
  have hDdef : D = T ⊔ Subgroup.zpowers v := by
    simpa [T] using hDeq
  have hDleC : D ≤ C := by
    rw [hDdef]
    apply le_inf
    · apply sup_le
      · intro x hxT
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxU : x ∈ U := hxT.1
        letI : IsCyclic U := hUcyc
        letI : CommGroup U := IsCyclic.commGroup
        let xU : U := ⟨x, hxU⟩
        let sU : U := ⟨s, hsU⟩
        exact congrArg Subtype.val (mul_comm xU sU)
      · apply Subgroup.zpowers_le.mpr
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hvS := hv_inv s hsU
        have hsInv : s⁻¹ = s :=
          inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)
        have hconj : v * s * v⁻¹ = s := by simpa [hsInv] using hvS
        exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hconj)
    · simpa [hDdef] using hDleH
  have hCcard : Nat.card C = Nat.card U := by
    let E : Subgroup G := Subgroup.centralizer ({s} : Set G)
    let CE : Subgroup E := H.subgroupOf E
    have hEcard : Nat.card E = 2 * Nat.card U := by
      dsimp [E]
      rw [hcent]
      exact hjoinCard
    have haE : a ∈ E := by
      change a ∈ Subgroup.centralizer ({s} : Set G)
      rw [hcent]
      exact (le_sup_left : U ≤ U ⊔ Subgroup.zpowers w) haU
    have haCE : (⟨a, haE⟩ : E) ∉ CE := haH
    have hCEindex : CE.index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨⟨a, haE⟩, haCE, ?_⟩
      intro b
      by_cases hbH : (b : G) ∈ H
      · right
        exact hbH
      · left
        have hiff := Subgroup.mul_mem_iff_of_index_two hHindex
          (a := (b : G)) (b := a)
        exact hiff.mpr ⟨fun hb => False.elim (hbH hb),
          fun ha => False.elim (haH ha)⟩
    have hCEcard : Nat.card CE = Nat.card U := by
      have hmul := CE.card_mul_index
      rw [hCEindex, hEcard] at hmul
      omega
    let eC : C ≃* CE :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
        invFun := fun x => ⟨x, ⟨x.1.2, x.2⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_mul' := by intro x y; rfl }
    rw [Nat.card_congr eC.toEquiv, hCEcard]
  have hDC : D = C := by
    apply Subgroup.eq_of_le_of_card_ge hDleC
    rw [hDcard, hCcard]
  have hvT : v ∉ T := fun hv => hvU hv.1
  have hcharD : (T.subgroupOf (T ⊔ Subgroup.zpowers v)).Characteristic :=
    reflectedCyclic_characteristic_in_join T v hTcyc (by omega) hvT hv_sq
      (fun x hx => hv_inv x hx.1)
  have hCeq : C = T ⊔ Subgroup.zpowers v := hDC.symm.trans hDdef
  have hcharC : (T.subgroupOf C).Characteristic := by
    rw [hCeq]
    exact hcharD
  exact ⟨v, hTcyc, hTcard, hvH, hvU, hv_sq, hv_inv, hCeq, hcharC⟩

end CFSG.GorensteinWalter

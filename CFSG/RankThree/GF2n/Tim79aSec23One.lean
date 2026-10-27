module

public import CFSG.RankThree.GF2n.Tim79aSec23Min
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Tim79aSec22Class

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem commute_of_mem_P {p v : G} (hp : p ∈ P) (hv : v ∈ V) : v * p = p * v := by
  have hp' : p ∈ Q ⊓ Subgroup.centralizer (V : Set G) := hc.hP ▸ hp
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp').2 v hv

theorem barOf_V_comm {u w : Hbar V H} (hu : u ∈ barOf V H V) (hw : w ∈ barOf V H V) :
    u * w = w * u := by
  obtain ⟨a, ha, rfl⟩ := mem_barOf_iff.mp hu
  obtain ⟨b, hb, rfl⟩ := mem_barOf_iff.mp hw
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc.elemAb.comm ha hb)

theorem barOf_V_sq {u : Hbar V H} (hu : u ∈ barOf V H V) : u ^ 2 = 1 := by
  obtain ⟨a, ha, rfl⟩ := mem_barOf_iff.mp hu
  rw [← map_pow]
  have : a ^ 2 = 1 := Subtype.ext (by simpa using hc.elemAb.2 _ ha)
  rw [this, map_one]

theorem card_barOf_V_eq_two
    (hV1 : ∀ a ∈ barOf V H V, ∀ b ∈ barOf V H V, a ≠ 1 → b ≠ 1 → a = b) :
    Nat.card (barOf V H V) = 2 := by
  obtain ⟨d, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hdH : d ∈ H := hc.V_le_H hdV
  have hd1 : piBar V H ⟨d, hdH⟩ ≠ 1 := fun h => hdW ((piBar_eq_one_iff _).1 h)
  have hdm : piBar V H ⟨d, hdH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hdV, rfl⟩
  rw [Nat.card_eq_two_iff' (1 : ↥(barOf V H V))]
  have hd1' : (⟨piBar V H ⟨d, hdH⟩, hdm⟩ : ↥(barOf V H V)) ≠ 1 :=
    fun h => hd1 (congrArg Subtype.val h)
  refine ⟨⟨piBar V H ⟨d, hdH⟩, hdm⟩, hd1', fun y hy => ?_⟩
  exact Subtype.ext (hV1 y.1 y.2 _ hdm (fun h => hy (Subtype.ext h)) hd1)

theorem xBar_le_sup_of_sup_eq {S : Subgroup (Hbar V H)} [S.Normal]
    (hsup : preimOf V H S ⊔ P = H) : barOf V H (xOf V H) ≤ S ⊔ barOf V H V := by
  rw [← hc.closure_dbarOf]
  refine (Subgroup.closure_le _).2 fun y hy => ?_
  obtain ⟨a, ha, v, hv, rfl⟩ := hc.exists_conj_of_mem_dbarOf hy
  obtain ⟨x, hx, rfl⟩ := mem_barOf_iff.mp ha
  have hxH : (x : G) ∈ preimOf V H S ⊔ P := by rw [hsup]; exact x.2
  obtain ⟨n, hn, p, hp, hnp⟩ := exists_mul_of_mem_sup
    (fun p hp => normalizer_preimOf (hc.PleH hp)) hxH
  obtain ⟨n', rfl, hnS⟩ := mem_preimOf.mp hn
  have hx' : x = n' * ⟨p, hc.PleH hp⟩ := Subtype.ext hnp
  have hpv : Commute (piBar V H ⟨p, hc.PleH hp⟩) v := by
    obtain ⟨v', hv', rfl⟩ := mem_barOf_iff.mp hv
    refine Commute.symm ?_
    show piBar V H v' * piBar V H ⟨p, hc.PleH hp⟩ = piBar V H ⟨p, hc.PleH hp⟩ * piBar V H v'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc.commute_of_mem_P hp hv')
  have hy : piBar V H x * v * (piBar V H x)⁻¹ = piBar V H n' * v * (piBar V H n')⁻¹ := by
    rw [hx', map_mul]
    have := hpv.eq
    calc piBar V H n' * piBar V H ⟨p, hc.PleH hp⟩ * v *
          (piBar V H n' * piBar V H ⟨p, hc.PleH hp⟩)⁻¹
        = piBar V H n' * (piBar V H ⟨p, hc.PleH hp⟩ * v) * (piBar V H ⟨p, hc.PleH hp⟩)⁻¹ *
            (piBar V H n')⁻¹ := by group
      _ = piBar V H n' * (v * piBar V H ⟨p, hc.PleH hp⟩) * (piBar V H ⟨p, hc.PleH hp⟩)⁻¹ *
            (piBar V H n')⁻¹ := by rw [this]
      _ = piBar V H n' * v * (piBar V H n')⁻¹ := by group
  rw [hy]
  have hS : ⁅piBar V H n', v⁆ ∈ S := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact S.mul_mem hnS (by simpa [mul_assoc] using
      Subgroup.Normal.conj_mem ‹S.Normal› _ (S.inv_mem hnS) v)
  have : piBar V H n' * v * (piBar V H n')⁻¹ = ⁅piBar V H n', v⁆ * v := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact Subgroup.mul_mem_sup hS hv

theorem case_one_of_sup_eq {S : Subgroup (Hbar V H)} [S.Normal]
    (hSX : S ≤ barOf V H (xOf V H)) (hodd : Odd (Nat.card S))
    (hsup : preimOf V H S ⊔ P = H) :
    Nat.card (barOf V H V) = 2 ∧ barOf V H (xOf V H) = S ⊔ barOf V H V := by
  have hXS : barOf V H (xOf V H) = S ⊔ barOf V H V :=
    le_antisymm (hc.xBar_le_sup_of_sup_eq hsup) (sup_le hSX (barOf_V_le V H))
  refine ⟨?_, hXS⟩
  have hV1 : ∀ a ∈ barOf V H V, ∀ b ∈ barOf V H V, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨x, hx, hxab⟩ := hc.barOf_V_conj ha hb ha1 hb1
    rw [hXS] at hx
    obtain ⟨s, hs, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hva : v * a = a * v := hc.barOf_V_comm hv ha
    have hb' : b = s * a * s⁻¹ := by
      rw [← hxab]
      calc s * v * a * (s * v)⁻¹ = s * (v * a) * v⁻¹ * s⁻¹ := by group
        _ = s * (a * v) * v⁻¹ * s⁻¹ := by rw [hva]
        _ = s * a * s⁻¹ := by group
    have hg : b * a⁻¹ ∈ S := by
      have : b * a⁻¹ = ⁅s, a⁆ := by rw [hb']; rfl
      rw [this, commutatorElement_def, mul_assoc, mul_assoc]
      exact S.mul_mem hs (by simpa [mul_assoc] using
        Subgroup.Normal.conj_mem ‹S.Normal› _ (S.inv_mem hs) a)
    have ha2 : a * a = 1 := by
      have := hc.barOf_V_sq ha
      rwa [pow_two] at this
    have hb2 : b * b = 1 := by
      have := hc.barOf_V_sq hb
      rwa [pow_two] at this
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hab : a * b = b * a := hc.barOf_V_comm ha hb
    have hg2 : (b * a⁻¹) ^ 2 = 1 := by
      rw [hai, pow_two]
      calc b * a * (b * a) = b * (a * b) * a := by simp only [mul_assoc]
        _ = b * (b * a) * a := by rw [hab]
        _ = (b * b) * (a * a) := by simp only [mul_assoc]
        _ = 1 := by rw [ha2, hb2, one_mul]
    have hd1 : orderOf (b * a⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    have hd2 : orderOf (b * a⁻¹) ∣ Nat.card S := by
      have := orderOf_dvd_natCard (⟨b * a⁻¹, hg⟩ : S)
      simpa [Subgroup.orderOf_mk] using this
    have hcop : Nat.Coprime 2 (Nat.card S) := Nat.coprime_two_left.mpr hodd
    have h1' : orderOf (b * a⁻¹) = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
    have := orderOf_eq_one_iff.mp h1'
    exact (mul_inv_eq_one.mp this).symm
  exact hc.card_barOf_V_eq_two hV1

theorem case_one (h : ¬ CFSG.oddCore (Xbar V H) ≤ Subgroup.center (Xbar V H)) :
    Nat.card (barOf V H V) = 2 ∧ barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V := by
  haveI := normal_oddCoreX V H
  rcases hc.sup_eq_or_central_of_odd (oddCoreX_le V H) (odd_card_oddCoreX V H) with hsup | hcen
  · exact hc.case_one_of_sup_eq (oddCoreX_le V H) (odd_card_oddCoreX V H) hsup
  · exact absurd ((oddCoreX_central_iff V H).1 hcen) h

theorem pCore_two_le_center :
    CFSG.pCore 2 (Xbar V H) ≤ Subgroup.center (Xbar V H) := by
  haveI := normal_barOf_xOf V H
  haveI : ((CFSG.pCore 2 (Xbar V H)).map (barOf V H (xOf V H)).subtype).Normal :=
    normal_map_subtype_of_characteristic _
  set T' := (CFSG.pCore 2 (Xbar V H)).map (barOf V H (xOf V H)).subtype with hT'
  have hT'X : T' ≤ barOf V H (xOf V H) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h2 : ∀ s ∈ T', ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Xbar V H)) ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have h3 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simpa using congrArg Subtype.val h3
  have hW2 : IsPGroup 2 (wOf V H) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  have hN2 := isPGroup_preimOf h2 hW2
  have hNX := preimOf_le_xOf hT'X
  have hNle : preimOf V H T' ≤ inSubgroup (pCore 2) (xOf V H) :=
    Tim78.le_inSubgroup_pCore hNX (fun x hx => normalizer_preimOf (xOf_le_H hc.V_le_H hx)) hN2
  intro t ht
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : (t : Hbar V H) ∈ barOf V H (inSubgroup (pCore 2) (xOf V H)) := by
    have : (t : Hbar V H) ∈ T' := ⟨t, ht, rfl⟩
    rw [← barOf_preimOf V H T'] at this
    exact barOf_mono hNle this
  exact Subtype.ext (hc.oBar_central _ h1 y.1 y.2).symm

end MinCex

end CFSG.RankThree.GF2n.Tim79a

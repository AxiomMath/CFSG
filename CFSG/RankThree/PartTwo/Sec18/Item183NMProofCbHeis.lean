module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec18.Item183KSL
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183NMProof

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isElemAbelian_sup_zpowers_and_card {Z : Subgroup X}
    (hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z) (hZ3 : Nat.card Z = 3)
    (hZe : ∀ z ∈ Z, z ^ 3 = 1) {x : X} (hx : x ∉ Z) (hx3 : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Z ⊔ Subgroup.zpowers x) ∧
      Nat.card (Z ⊔ Subgroup.zpowers x : Subgroup X) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZab : CFSG.Assembly.IsElemAbelian 3 Z :=
    ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b)⟩⟩, hZe⟩
  have hc : ∀ z ∈ Z, ∀ y ∈ Subgroup.zpowers x, z * y = y * z := fun z hz y _ => hZc z hz y
  refine ⟨Sec13.isElemAbelian_sup hZab (Sec13.isElemAbelian_zpowers hx3) hc, ?_⟩
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Z.one_mem)
  have hxo : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z (Subgroup.zpowers x) hc).1
  have hinf : Nat.card (Z ⊓ Subgroup.zpowers x : Subgroup X) = 1 := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right : Z ⊓ Subgroup.zpowers x ≤ _)
    rw [hxo] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hxo])
      have hxm : x ∈ Z ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hx hxm.1
  rw [hinf, mul_one, hZ3, hxo] at h1
  exact h1

theorem mem_sup_zpowers_of_commute {U Z : Subgroup X} (hU : Sec4.IsHeisThree U) (hZU : Z ≤ U)
    (hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z) (hZ3 : Nat.card Z = 3) {u u' : X} (hu : u ∈ U)
    (hu' : u' ∈ U) (huZ : u ∉ Z) (hc : u' * u = u * u') : u' ∈ Z ⊔ Subgroup.zpowers u := by
  have hU3 : ∀ y ∈ U, y ^ 3 = 1 := by
    intro y hy
    have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : U)
    rw [hU.2.2] at h
    simpa using congrArg Subtype.val h
  obtain ⟨hab, h9⟩ :=
    isElemAbelian_sup_zpowers_and_card hZc hZ3 (fun z hz => hU3 z (hZU hz)) huZ (hU3 u hu)
  by_contra hnot
  have hcomm : ∀ e ∈ Z ⊔ Subgroup.zpowers u, e * u' = u' * e := by
    have hle : Z ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({u'} : Set X) := sup_le
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hZc z hz u'))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm))
    exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hE := isE27_sup_zpowers hab h9 hnot (hU3 u' hu') hcomm
  have hEU : Z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers u' ≤ U :=
    sup_le (sup_le hZU (Subgroup.zpowers_le.mpr hu)) (Subgroup.zpowers_le.mpr hu')
  have heq : Z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers u' = U :=
    Subgroup.eq_of_le_of_card_ge hEU (by rw [hU.2.1, hE.2])
  have hcen : Subgroup.center U = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [Subgroup.mem_center_iff]
    intro b
    have ha : (a : X) ∈ Z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers u' := heq ▸ a.2
    have hb : (b : X) ∈ Z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers u' := heq ▸ b.2
    have h1 : (b : X) * a = a * b :=
      congrArg Subtype.val (hE.1.1.is_comm.comm ⟨_, hb⟩ ⟨_, ha⟩)
    exact Subtype.ext h1
  have h3 := hU.1.2.2.2
  rw [hcen, Subgroup.card_top, hU.2.1] at h3
  norm_num at h3

theorem exists_conj_not_mem_of_heis {U V : Subgroup X} (hsup : U ⊔ V = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : Sec4.IsHeisThree U)
    (eV : V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) {B D : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB27 : Nat.card B = 27)
    (hnoB : ∀ W : Subgroup X, W ≤ B → Nat.card W = 9 → ¬ W ≤ U) (hZB : U ⊓ V ≤ B)
    (hDB : D ≤ B) (hD3 : Nat.card D = 3) (hDU : ¬ D ≤ U) :
    ∃ w ∈ V, (∀ β ∈ B, w * β * w⁻¹ ∈ B) ∧ ∃ x ∈ D, w * x * w⁻¹ ∉ D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := U ⊓ V with hZdef
  have hZU : Z ≤ U := inf_le_left
  have hZV : Z ≤ V := inf_le_right
  have hdec := KFacts.L34.exists_mul_eq_of_sup_eq_top hsup hUV
  have hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z := by
    intro z hz x
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
    have h1 : z * u = u * z := (hUV u hu z hz.2).symm
    have h2 : z * v = v * z := hUV z hz.1 v hv
    calc z * (u * v) = z * u * v := (mul_assoc _ _ _).symm
      _ = u * (z * v) := by rw [h1, mul_assoc]
      _ = u * v * z := by rw [h2, mul_assoc]
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    have h := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : U)
    rw [hU.2.2] at h
    simpa using congrArg Subtype.val h
  have hcommZ : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ Z := by
    intro u hu u' hu'
    have hmem : ⁅(⟨u, hu⟩ : U), ⟨u', hu'⟩⁆ ∈ commutator U := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at hmem
    rw [hZdef, KFacts.L34.inf_eq_map_center_left hUV hU h3]
    exact ⟨_, hmem, by simp [commutatorElement_def]⟩
  have hZe : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => hU3 z hz.1
  have hE9 := fun {x : X} (hx : x ∉ Z) (hx3 : x ^ 3 = 1) =>
    isElemAbelian_sup_zpowers_and_card hZc h3 hZe hx hx3
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  have hBU : ∀ x ∈ B ⊓ U, x ∈ Z := by
    have hle : Nat.card (B ⊓ U : Subgroup X) ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have hp : IsPGroup 3 (B ⊓ U : Subgroup X) := hB3.to_le inf_le_left
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have hk2 : 2 ≤ k := by
        by_contra hk2
        push Not at hk2
        interval_cases k <;> simp_all
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
        (by rw [hk]; exact pow_dvd_pow 3 hk2)
      exact hnoB (K.map (B ⊓ U).subtype) ((Subgroup.map_subtype_le K).trans inf_le_left)
        (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]; norm_num)
        ((Subgroup.map_subtype_le K).trans inf_le_right)
    have heq : Z = B ⊓ U := Subgroup.eq_of_le_of_card_ge (le_inf hZB hZU) (by rw [h3]; exact hle)
    intro x hx
    rw [heq]
    exact hx
  have hBV : ∀ v ∈ B ⊓ V, v ∈ Z := by
    intro v hv
    by_contra hvZ
    have hBV' : ¬ B ≤ V := by
      intro hle
      have hB' := isE27_subgroupOf ⟨hB, hB27⟩ hle
      exact Item183K.card_ne_of_SL34 eV hB'.1 hB'.2
    obtain ⟨y, hyB, hyV⟩ := Set.not_subset.mp hBV'
    obtain ⟨uy, huy, vy, hvy, rfl⟩ := hdec y
    have huyZ : uy ∉ Z := fun h => hyV (V.mul_mem (hZV h) hvy)
    have hyv : uy * vy * v = v * (uy * vy) :=
      congrArg Subtype.val (hB.1.is_comm.comm ⟨uy * vy, hyB⟩ ⟨v, hv.1⟩)
    have huyv : uy * v = v * uy := hUV uy huy v hv.2
    have hvyv : vy * v = v * vy := by
      have h1 : uy * (vy * v) = uy * (v * vy) := by
        calc uy * (vy * v) = uy * vy * v := (mul_assoc _ _ _).symm
          _ = v * (uy * vy) := hyv
          _ = v * uy * vy := (mul_assoc _ _ _).symm
          _ = uy * v * vy := by rw [huyv]
          _ = uy * (v * vy) := mul_assoc _ _ _
      exact mul_left_cancel h1
    have hvy3 : vy ^ 3 = 1 := by
      have h1 : (uy * vy) ^ 3 = uy ^ 3 * vy ^ 3 :=
        (show Commute uy vy from hUV uy huy vy hvy).mul_pow 3
      rw [hB.2 _ hyB, hU3 uy huy, one_mul] at h1
      exact h1.symm
    obtain ⟨hWab, hW9⟩ := hE9 hvZ (hB.2 v hv.1)
    have hWB : Z ⊔ Subgroup.zpowers v ≤ B := sup_le hZB (Subgroup.zpowers_le.mpr hv.1)
    have hvyW : vy ∉ Z ⊔ Subgroup.zpowers v := by
      intro hmem
      apply huyZ
      refine hBU uy ⟨?_, huy⟩
      have h1 := B.mul_mem hyB (B.inv_mem (hWB hmem))
      rwa [mul_inv_cancel_right] at h1
    have hcomm : ∀ e ∈ Z ⊔ Subgroup.zpowers v, e * vy = vy * e := by
      have hle : Z ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer ({vy} : Set X) := sup_le
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hZc z hz vy))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvyv.symm))
      exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)
    have hE := isE27_sup_zpowers hWab hW9 hvyW hvy3 hcomm
    have hEV : Z ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers vy ≤ V :=
      sup_le (sup_le hZV (Subgroup.zpowers_le.mpr hv.2)) (Subgroup.zpowers_le.mpr hvy)
    have hE' := isE27_subgroupOf hE hEV
    exact Item183K.card_ne_of_SL34 eV hE'.1 hE'.2
  obtain ⟨d, hdD, hdU⟩ := Set.not_subset.mp hDU
  have hdB : d ∈ B := hDB hdD
  have hd3 : d ^ 3 = 1 := hB.2 d hdB
  have hd1 : d ≠ 1 := fun h => hdU (h ▸ U.one_mem)
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hDd : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD)
      (by rw [hD3, Nat.card_zpowers, hdo])).symm
  obtain ⟨ud, hud, vd, hvd, hdeq⟩ := hdec d
  have hudZ : ud ∉ Z := by
    intro hudZ
    apply hdU
    have hdV : d ∈ V := hdeq ▸ V.mul_mem (hZV hudZ) hvd
    exact hZU (hBV d ⟨hdB, hdV⟩)
  obtain ⟨u', hu', v', hv', he, hu'ud⟩ :
      ∃ u' ∈ U, ∃ v' ∈ V, u' * v' ∈ B ∧ u' * ud ≠ ud * u' := by
    by_contra hall
    push Not at hall
    have hBle : B ≤ Z ⊔ Subgroup.zpowers d := by
      intro e heB
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec e
      have hmem := mem_sup_zpowers_of_commute hU hZU hZc h3 hud hu hudZ (hall u hu v hv heB)
      have hc : ∀ z ∈ Z, ∀ y ∈ Subgroup.zpowers ud, z * y = y * z := fun z hz y _ => hZc z hz y
      have hmem' : u ∈ ((Z ⊔ Subgroup.zpowers ud : Subgroup X) : Set X) := hmem
      rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z _ hc).2] at hmem'
      obtain ⟨z, hz, w', hw', hzw⟩ := Set.mem_mul.mp hmem'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have ha : ud ^ i ∈ U := U.zpow_mem hud i
      have hb : v * (vd ^ i)⁻¹ ∈ V := V.mul_mem hv (V.inv_mem (V.zpow_mem hvd i))
      have hab : ud ^ i * (v * (vd ^ i)⁻¹) = (v * (vd ^ i)⁻¹) * ud ^ i := hUV _ ha _ hb
      have hdi : d ^ i = ud ^ i * vd ^ i := by
        rw [← hdeq]
        exact (show Commute ud vd from hUV ud hud vd hvd).mul_zpow i
      have e1 : u * v * (d ^ i)⁻¹ = z * (v * (vd ^ i)⁻¹) := by
        rw [← hzw, hdi]
        calc z * ud ^ i * v * (ud ^ i * vd ^ i)⁻¹ =
            z * (ud ^ i * (v * (vd ^ i)⁻¹) * (ud ^ i)⁻¹) := by group
          _ = z * (v * (vd ^ i)⁻¹) := by rw [hab]; group
      have hmemZ : u * v * (d ^ i)⁻¹ ∈ Z := by
        refine hBV _ ⟨B.mul_mem heB (B.inv_mem (B.zpow_mem hdB i)), ?_⟩
        rw [e1]
        exact V.mul_mem (hZV hz) hb
      have e2 : u * v = u * v * (d ^ i)⁻¹ * d ^ i := by group
      rw [e2]
      exact Subgroup.mul_mem_sup hmemZ (Subgroup.zpow_mem_zpowers d i)
    have h9 := Subgroup.card_le_of_le hBle
    rw [hB27, (hE9 (fun h => hdU (hZU h)) hd3).2] at h9
    omega
  have hconj : ∀ u ∈ U, ∀ v ∈ V, u * v ∈ B →
      v' * (u * v) * v'⁻¹ = (u'⁻¹ * u * u' * u⁻¹) * (u * v) := by
    intro u hu v hv huvB
    have heβ : u' * v' * (u * v) = u * v * (u' * v') :=
      congrArg Subtype.val (hB.1.is_comm.comm ⟨_, he⟩ ⟨_, huvB⟩)
    have hvu' : v * u' = u' * v := (hUV u' hu' v hv).symm
    calc v' * (u * v) * v'⁻¹ = u'⁻¹ * ((u' * v') * (u * v) * (u' * v')⁻¹) * u' := by group
      _ = u'⁻¹ * (u * v) * u' := by rw [heβ]; group
      _ = u'⁻¹ * u * (v * u') := by group
      _ = u'⁻¹ * u * (u' * v) := by rw [hvu']
      _ = (u'⁻¹ * u * u' * u⁻¹) * (u * v) := by group
  have hcZ : ∀ u ∈ U, u'⁻¹ * u * u' * u⁻¹ ∈ Z := by
    intro u hu
    have h1 := hcommZ u'⁻¹ (U.inv_mem hu') u hu
    rwa [inv_inv] at h1
  refine ⟨v', hv', fun β hβ => ?_, d, hdD, ?_⟩
  · obtain ⟨uβ, huβ, vβ, hvβ, rfl⟩ := hdec β
    rw [hconj uβ huβ vβ hvβ hβ]
    exact B.mul_mem (hZB (hcZ uβ huβ)) hβ
  · rw [hDd]
    intro hmem
    rw [← hdeq, hconj ud hud vd hvd (hdeq ▸ hdB), hdeq] at hmem
    have hc := hcZ ud hud
    have hcd : u'⁻¹ * ud * u' * ud⁻¹ ∈ Subgroup.zpowers d := by
      have h1 := (Subgroup.zpowers d).mul_mem hmem
        ((Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d))
      rwa [mul_inv_cancel_right] at h1
    have hc1 : u'⁻¹ * ud * u' * ud⁻¹ ≠ 1 := by
      intro h1
      apply hu'ud
      have key : ud * u' = u' * (u'⁻¹ * ud * u' * ud⁻¹) * ud := by group
      rw [key, h1, mul_one]
    have hco : orderOf (u'⁻¹ * ud * u' * ud⁻¹) = 3 :=
      orderOf_eq_prime (hU3 _ (hZU hc)) hc1
    have heq : Subgroup.zpowers (u'⁻¹ * ud * u' * ud⁻¹) = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcd)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hco, hdo])
    apply hdU
    have hdc : d ∈ Subgroup.zpowers (u'⁻¹ * ud * u' * ud⁻¹) := heq ▸ Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr (hZU hc)) hdc

end CFSG.RankThree.PartTwo.Sec18.Item183NMProof

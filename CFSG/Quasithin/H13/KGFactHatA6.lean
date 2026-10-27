module

public import CFSG.Quasithin.H13.NQS134HatInputs
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Quasithin.H13.KGHatA6

open Subgroup
open scoped commutatorElement

theorem pow_index_eq_one_of_mem_center {G : Type*} [Group G] (hG : commutator G = ⊤)
    {H : Subgroup G} [H.FiniteIndex] (hH : IsMulCommutative H) {z : G} (hz : z ∈ center G) :
    z ^ H.index = 1 := by
  let _ : CommGroup H :=
    { (inferInstance : Group H) with mul_comm := fun a b => hH.is_comm.comm a b }
  have hτ := MonoidHom.transfer_eq_pow (MonoidHom.id H) z fun k g₀ _ => by
    have hc := Subgroup.mem_center_iff.mp (pow_mem hz k) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hker : z ∈ (MonoidHom.transfer (MonoidHom.id H)).ker :=
    Abelianization.commutator_subset_ker _ (hG ▸ Subgroup.mem_top z)
  rw [MonoidHom.mem_ker, hτ] at hker
  exact congrArg Subtype.val hker

theorem commutatorElement_mul_left_of_mem_center {G : Type*} [Group G] {z : G}
    (hz : z ∈ center G) (u w : G) : ⁅u * z, w⁆ = ⁅u, w⁆ := by
  have hzw : z * w = w * z := (Subgroup.mem_center_iff.mp hz w).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc u * z * w * (z⁻¹ * u⁻¹) * w⁻¹ = u * (z * w) * z⁻¹ * u⁻¹ * w⁻¹ := by group
    _ = u * (w * z) * z⁻¹ * u⁻¹ * w⁻¹ := by rw [hzw]
    _ = u * w * u⁻¹ * w⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center {G : Type*} [Group G] {z : G}
    (hz : z ∈ center G) (u w : G) : ⁅u, w * z⁆ = ⁅u, w⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center hz, commutatorElement_inv]

private def p012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def p345 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private def tau6 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

private theorem p012_mul_p345 : p012 * p345 = p345 * p012 := by decide

private theorem tau6_conj_p345 : tau6⁻¹ * p345 * tau6 = p012 := by decide

private theorem tau6_conj_p012 : tau6⁻¹ * p012 * tau6 = p345 := by decide

private theorem p012_pow_three : p012 ^ 3 = 1 := by decide

private theorem p345_pow_three : p345 ^ 3 = 1 := by decide

private theorem p012_three : p012 (3 : Fin 6) = 3 := by decide

private theorem p345_three : p345 (3 : Fin 6) ≠ 3 := by decide

private theorem p012_zero : p012 (0 : Fin 6) ≠ 0 := by decide

private theorem sign_tau6 : Equiv.Perm.sign tau6 = -1 := by
  simp [tau6, Equiv.Perm.sign_mul]

private theorem p012_mem : p012 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [p012, Equiv.Perm.sign_mul]

private theorem p345_mem : p345 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [p345, Equiv.Perm.sign_mul]

private theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem card_sup_zpowers :
    Nat.card ↥(zpowers (⟨p012, p012_mem⟩ : alternatingGroup (Fin 6)) ⊔
      zpowers (⟨p345, p345_mem⟩ : alternatingGroup (Fin 6))) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : alternatingGroup (Fin 6) := ⟨p012, p012_mem⟩ with ha
  set b : alternatingGroup (Fin 6) := ⟨p345, p345_mem⟩ with hb
  have ha3 : a ^ 3 = 1 := Subtype.ext p012_pow_three
  have hb3 : b ^ 3 = 1 := Subtype.ext p345_pow_three
  have ha1 : a ≠ 1 := fun h => p012_zero (by
    have := congrArg (fun g : alternatingGroup (Fin 6) => (g : Equiv.Perm (Fin 6)) 0) h
    exact this)
  have hb1 : b ≠ 1 := fun h => p345_three (by
    have := congrArg (fun g : alternatingGroup (Fin 6) => (g : Equiv.Perm (Fin 6)) 3) h
    exact this)
  have hab : Commute a b := Subtype.ext p012_mul_p345
  have hpa : IsPGroup 3 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime ha3 ha1)
  have hpb : IsPGroup 3 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hb3 hb1)
  have hnorm : zpowers a ≤ normalizer (zpowers b : Set (alternatingGroup (Fin 6))) := by
    refine (zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (hab.symm.zpow_left k).eq
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hpa.to_sup_of_normal_right' hpb hnorm)
  have hdvd := Subgroup.card_subgroup_dvd_card (zpowers a ⊔ zpowers b)
  rw [hn, card_alternatingGroup_six] at hdvd
  have hn2 : n ≤ 2 := by
    by_contra h
    have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h27.trans hdvd
    norm_num at this
  have hle : zpowers a ≤ zpowers a ⊔ zpowers b := le_sup_left
  have hca : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime ha3 ha1
  interval_cases n
  · have := Subgroup.card_dvd_of_le hle
    rw [hn, hca] at this
    norm_num at this
  · exfalso
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hn, hca]; norm_num)
    have hbm : b ∈ zpowers a := heq ▸ (le_sup_right : zpowers b ≤ zpowers a ⊔ zpowers b)
      (mem_zpowers b)
    have hst : zpowers a ≤ MulAction.stabilizer (alternatingGroup (Fin 6)) (3 : Fin 6) := by
      rw [zpowers_le, MulAction.mem_stabilizer_iff]
      exact p012_three
    exact p345_three (MulAction.mem_stabilizer_iff.mp (hst hbm))
  · rw [hn]; norm_num

section Hat

variable {X : Type*} [Group X] [Finite X]

private theorem lifts_not_commute (hX : commutator X = ⊤) (hZ : Nat.card (center X) = 3)
    (ψ : X →* alternatingGroup (Fin 6)) (hψs : Function.Surjective ψ) (hker : ψ.ker ≤ center X)
    {xh yh : X} (hx : ψ xh = ⟨p012, p012_mem⟩) (hy : ψ yh = ⟨p345, p345_mem⟩) :
    xh * yh ≠ yh * xh := by
  intro hcomm
  let k : Set X := {xh, yh} ∪ (center X : Set X)
  have hk : k.Pairwise Commute := by
    intro u hu v hv _
    rcases hu with hu | hu
    · rcases hv with hv | hv
      · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact Commute.refl _
        · exact hcomm
        · exact hcomm.symm
        · exact Commute.refl _
      · exact Subgroup.mem_center_iff.mp hv u
    · exact (Subgroup.mem_center_iff.mp hu v).symm
  have hHc : IsMulCommutative (closure k) := Subgroup.isMulCommutative_closure hk
  have hZH : center X ≤ closure k := fun z hz => subset_closure (Or.inr hz)
  have hxH : xh ∈ closure k := subset_closure (Or.inl (Set.mem_insert _ _))
  have hyH : yh ∈ closure k := subset_closure (Or.inl (Set.mem_insert_of_mem _ rfl))
  have haM : (⟨p012, p012_mem⟩ : alternatingGroup (Fin 6)) ∈ (closure k).map ψ :=
    hx ▸ mem_map_of_mem ψ hxH
  have hbM : (⟨p345, p345_mem⟩ : alternatingGroup (Fin 6)) ∈ (closure k).map ψ :=
    hy ▸ mem_map_of_mem ψ hyH
  have h9 : 9 ∣ Nat.card ((closure k).map ψ) :=
    card_sup_zpowers ▸ Subgroup.card_dvd_of_le (sup_le (zpowers_le.mpr haM) (zpowers_le.mpr hbM))
  have hidx : ((closure k).map ψ).index = (closure k).index :=
    Subgroup.index_map_eq (closure k) hψs (hker.trans hZH)
  have hmul := Subgroup.card_mul_index ((closure k).map ψ)
  rw [card_alternatingGroup_six, hidx] at hmul
  have h3 : ¬ 3 ∣ (closure k).index := by
    rintro ⟨j, hj⟩
    obtain ⟨m, hm⟩ := h9
    rw [hm, hj] at hmul
    have h27 : (27 : ℕ) ∣ 360 := ⟨m * j, by rw [← hmul]; ring⟩
    norm_num at h27
  have hcop : Nat.Coprime 3 (closure k).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hz1 : ∀ z ∈ center X, z = 1 := by
    intro z hz
    have h1 : z ^ (closure k).index = 1 := pow_index_eq_one_of_mem_center hX hHc hz
    have h2 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨z, hz⟩ : center X))
      rw [hZ] at this
      exact congrArg Subtype.val this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h1))
  rw [(Subgroup.eq_bot_iff_forall _).mpr hz1, Subgroup.card_bot] at hZ
  omega

omit [Finite X] in
private theorem map_commutator_eq_inv (ψ : X →* alternatingGroup (Fin 6))
    (hψs : Function.Surjective ψ) (hker : ψ.ker ≤ center X) (α : MulAut X)
    (σ : Equiv.Perm (Fin 6)) (hσ : Equiv.Perm.sign σ = -1)
    (hα : ∀ x : X, (ψ (α x) : Equiv.Perm (Fin 6)) = σ * (ψ x : Equiv.Perm (Fin 6)) * σ⁻¹)
    {xh yh : X} (hx : ψ xh = ⟨p012, p012_mem⟩) (hy : ψ yh = ⟨p345, p345_mem⟩)
    (hz0 : ⁅xh, yh⁆ ∈ center X) : α ⁅xh, yh⁆ = ⁅xh, yh⁆⁻¹ := by
  have hρ : σ * tau6⁻¹ ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hσ, sign_tau6]
    rfl
  obtain ⟨r, hr⟩ := hψs ⟨σ * tau6⁻¹, hρ⟩
  have hr' : (ψ r : Equiv.Perm (Fin 6)) = σ * tau6⁻¹ := congrArg Subtype.val hr
  have hx' : (ψ xh : Equiv.Perm (Fin 6)) = p012 := congrArg Subtype.val hx
  have hy' : (ψ yh : Equiv.Perm (Fin 6)) = p345 := congrArg Subtype.val hy
  have hlift : ∀ u v : X, (ψ (α u) : Equiv.Perm (Fin 6)) = ψ (r * v * r⁻¹) →
      ∃ w ∈ center X, α u = r * v * r⁻¹ * w := by
    intro u v huv
    refine ⟨(r * v * r⁻¹)⁻¹ * α u, hker ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact (Subtype.ext huv).symm
  obtain ⟨w₁, hw₁, e₁⟩ := hlift xh yh (by
    rw [hα, hx', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hr', hy', ← tau6_conj_p345]
    group)
  obtain ⟨w₂, hw₂, e₂⟩ := hlift yh xh (by
    rw [hα, hy', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hr', hx', ← tau6_conj_p012]
    group)
  rw [map_commutatorElement, e₁, e₂, commutatorElement_mul_left_of_mem_center hw₁,
    commutatorElement_mul_right_of_mem_center hw₂]
  have hc : ⁅r * yh * r⁻¹, r * xh * r⁻¹⁆ = r * ⁅yh, xh⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hc, ← commutatorElement_inv, Subgroup.mem_center_iff.mp (inv_mem hz0) r]
  group

end Hat

theorem hatA6OddInverts_holds : NQS134.HatA6OddInverts := by
  intro X _ _ hP hZ e α σ hσ hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : X →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ center X := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hw' : e (w : X ⧸ center X) = 1 := hw
    rw [MulEquiv.map_eq_one_iff] at hw'
    exact (QuotientGroup.eq_one_iff w).mp hw'
  obtain ⟨xh, hx⟩ := hψs ⟨p012, p012_mem⟩
  obtain ⟨yh, hy⟩ := hψs ⟨p345, p345_mem⟩
  have hz0 : ⁅xh, yh⁆ ∈ center X := by
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, hx, hy, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext p012_mul_p345
  have hne : ⁅xh, yh⁆ ≠ 1 := by
    rw [Ne, commutatorElement_eq_one_iff_mul_comm]
    exact lifts_not_commute hP.commutator_eq_top hZ ψ hψs hker hx hy
  have hinv := map_commutator_eq_inv ψ hψs hker α σ hσ (fun x => hα x) hx hy hz0
  have h3 : ⁅xh, yh⁆ ^ 3 = 1 := by
    have := pow_card_eq_one' (x := (⟨_, hz0⟩ : center X))
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hzp : zpowers ⁅xh, yh⁆ = center X :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz0)
      (by rw [hZ, Nat.card_zpowers, orderOf_eq_prime h3 hne])
  intro z hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hzp ▸ hz : z ∈ zpowers ⁅xh, yh⁆)
  rw [map_zpow, hinv, inv_zpow]

end CFSG.Quasithin.H13.KGHatA6

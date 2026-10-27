module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.AutA5

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open scoped commutatorElement

private def a5g0 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap (1 : Fin 5) 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5A1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5B1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5C1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 3 * Equiv.swap (1 : Fin 5) 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5C2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5A2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5D2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 4 * Equiv.swap (1 : Fin 5) 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private abbrev a5Kl1 (x : alternatingGroup (Fin 5)) : Prop :=
  x = 1 ∨ x = a5A1 ∨ x = a5B1 ∨ x = a5C1

private abbrev a5Kl2 (x : alternatingGroup (Fin 5)) : Prop :=
  x = 1 ∨ x = a5C2 ∨ x = a5A2 ∨ x = a5D2

private theorem a5_kl1_one : a5Kl1 1 := Or.inl rfl

private theorem a5_kl2_one : a5Kl2 1 := Or.inl rfl

private theorem a5_kl1_A1 : a5Kl1 a5A1 := Or.inr (Or.inl rfl)

private theorem a5_kl1_C1 : a5Kl1 a5C1 := Or.inr (Or.inr (Or.inr rfl))

private theorem a5_kl2_C2 : a5Kl2 a5C2 := Or.inr (Or.inl rfl)

private theorem a5_kl2_D2 : a5Kl2 a5D2 := Or.inr (Or.inr (Or.inr rfl))

private theorem a5_kl1_mul :
    ∀ x y : alternatingGroup (Fin 5), a5Kl1 x → a5Kl1 y → a5Kl1 (x * y) := by
  decide +kernel

private theorem a5_kl1_inv : ∀ x : alternatingGroup (Fin 5), a5Kl1 x → a5Kl1 x⁻¹ := by
  decide +kernel

private theorem a5_kl2_mul :
    ∀ x y : alternatingGroup (Fin 5), a5Kl2 x → a5Kl2 y → a5Kl2 (x * y) := by
  decide +kernel

private theorem a5_kl2_inv : ∀ x : alternatingGroup (Fin 5), a5Kl2 x → a5Kl2 x⁻¹ := by
  decide +kernel

private theorem a5_kl1_conj :
    ∀ m : alternatingGroup (Fin 5), a5Kl1 m ↔ a5Kl1 (a5g0 * m * a5g0⁻¹) := by
  decide +kernel

private theorem a5_kl2_conj :
    ∀ m : alternatingGroup (Fin 5), a5Kl2 m ↔ a5Kl2 (a5g0 * m * a5g0⁻¹) := by
  decide +kernel

private theorem a5_kl1_no_three :
    ∀ m : alternatingGroup (Fin 5), a5Kl1 m → m ^ 3 = 1 → m = 1 := by
  decide +kernel

private theorem a5_kl2_no_three :
    ∀ m : alternatingGroup (Fin 5), a5Kl2 m → m ^ 3 = 1 → m = 1 := by
  decide +kernel

private theorem a5_comm_A1 : ⁅a5A1, a5g0⁆ = a5B1 := by decide +kernel

private theorem a5_comm_C1 : ⁅a5C1, a5g0⁆ = a5A1 := by decide +kernel

private theorem a5_comm_D2 : ⁅a5D2, a5g0⁆ = a5C2 := by decide +kernel

private theorem a5_comm_C2 : ⁅a5C2, a5g0⁆ = a5A2 := by decide +kernel

private theorem a5_C1_eq : a5C1 = a5A1 * a5B1 := by decide +kernel

private theorem a5_p3 : (a5A1 * a5C2) ^ 3 = 1 := by decide +kernel

private theorem a5_p3_ne : a5A1 * a5C2 ≠ 1 := by decide +kernel

private theorem a5_p5 : (a5A1 * a5A2) ^ 5 = 1 := by decide +kernel

private theorem a5_p5_ne : a5A1 * a5A2 ≠ 1 := by decide +kernel

private theorem a5_conj_g0 :
    ∀ g : alternatingGroup (Fin 5), g ^ 3 = 1 → g ≠ 1 →
      ∃ s : alternatingGroup (Fin 5), s * a5g0 * s⁻¹ = g := by
  decide +kernel

private def a5W1 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | a5Kl1 x}
  mul_mem' := fun {a b} ha hb => a5_kl1_mul a b ha hb
  one_mem' := a5_kl1_one
  inv_mem' := fun {x} hx => a5_kl1_inv x hx

private theorem a5_card_W1 : Nat.card ↥a5W1 = 4 := by
  change Nat.card {x : alternatingGroup (Fin 5) // a5Kl1 x} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def a5W2 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | a5Kl2 x}
  mul_mem' := fun {a b} ha hb => a5_kl2_mul a b ha hb
  one_mem' := a5_kl2_one
  inv_mem' := fun {x} hx => a5_kl2_inv x hx

private theorem a5_centralizer_three :
    ∀ p : Equiv.Perm (Fin 5), p ^ 3 = 1 → p ≠ 1 →
      ∀ y : alternatingGroup (Fin 5),
        p * (y : Equiv.Perm (Fin 5)) * p⁻¹ = (y : Equiv.Perm (Fin 5)) → y ^ 3 = 1 := by
  decide +kernel

private theorem a5_not_three_dvd {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    (h : ∀ x ∈ V, x ^ 3 = 1 → x = 1) : ¬ 3 ∣ Nat.card V := by
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 3 h3
  have hx3 : (x : G) ^ 3 = 1 := by
    have h' : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val h'
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have h0 : x = 1 := Subtype.ext h1
    rw [h0, orderOf_one] at hx
    norm_num at hx
  exact hx1 (h _ x.2 hx3)

private theorem a5_prime_dvd {G : Type*} [Group G] [Finite G] {H : Subgroup G} {x : G} {p : ℕ}
    [Fact p.Prime] (hx : x ∈ H) (hp : x ^ p = 1) (hx1 : x ≠ 1) : p ∣ Nat.card H := by
  have hp' : (⟨x, hx⟩ : H) ^ p = 1 := Subtype.ext (by simpa using hp)
  have hne : (⟨x, hx⟩ : H) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord : orderOf (⟨x, hx⟩ : H) = p := orderOf_eq_prime hp' hne
  rw [← hord]
  exact orderOf_dvd_natCard _

private def a5ConjSub {X : Type} [Group X] {K : Subgroup X} {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) : MulAut K :=
  { toFun := fun k => ⟨e * (k : X) * e⁻¹, (Subgroup.mem_set_normalizer_iff.mp heK (k : X)).mp k.2⟩
    invFun := fun k =>
      ⟨e⁻¹ * (k : X) * e, (Subgroup.mem_set_normalizer_iff''.mp heK (k : X)).mp k.2⟩
    left_inv := fun k => by ext; simp only [Subgroup.coe_mk]; group
    right_inv := fun k => by ext; simp only [Subgroup.coe_mk]; group
    map_mul' := fun k l => by ext; simp only [Subgroup.coe_mk, Subgroup.coe_mul]; group }

private theorem a5_conjSub_apply {X : Type} [Group X] {K : Subgroup X} {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) (k : ↥K) :
    ((a5ConjSub heK k : ↥K) : X) = e * (k : X) * e⁻¹ :=
  rfl

private theorem a5_conjSub_cube {X : Type} [Group X] {K : Subgroup X} {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) (he3 : e ^ 3 = 1) (k : ↥K) :
    a5ConjSub heK (a5ConjSub heK (a5ConjSub heK k)) = k := by
  apply Subtype.ext
  rw [a5_conjSub_apply, a5_conjSub_apply, a5_conjSub_apply]
  have h : e * (e * (e * (k : X) * e⁻¹) * e⁻¹) * e⁻¹ = (e * (e * e)) * k * (e * (e * e))⁻¹ := by
    group
  rw [h, ← pow_three, he3, inv_one, one_mul, mul_one]

private def a5ConjA5 {X : Type} [Group X] {K : Subgroup X} {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) (φ : ↥K ≃* alternatingGroup (Fin 5)) :
    MulAut (alternatingGroup (Fin 5)) :=
  (φ.symm.trans (a5ConjSub heK)).trans φ

private theorem a5_conjA5_apply {X : Type} [Group X] {K : Subgroup X} {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) (φ : ↥K ≃* alternatingGroup (Fin 5))
    (y : alternatingGroup (Fin 5)) :
    a5ConjA5 heK φ y = φ (a5ConjSub heK (φ.symm y)) :=
  rfl

theorem pow_three_eq_one_of_commute_a5 {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (φ : ↥K ≃* alternatingGroup (Fin 5)) {e : X} (heK : e ∈ Subgroup.normalizer (K : Set X))
    (he3 : e ^ 3 = 1) (he : ∃ k ∈ K, e * k ≠ k * e) {x : X} (hxK : x ∈ K)
    (hxe : x * e = e * x) : x ^ 3 = 1 := by
  have hτ3 : a5ConjA5 heK φ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply, a5_conjA5_apply,
      MulEquiv.symm_apply_apply, a5_conjSub_cube heK he3, MulEquiv.apply_symm_apply]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 (a5ConjA5 heK φ)
  have hπ3 : π ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hπ, hτ3, map_one]
  have hπ1 : π ≠ 1 := by
    intro hπ1'
    obtain ⟨k, hk, hne⟩ := he
    have hid : a5ConjA5 heK φ (φ ⟨k, hk⟩) = φ ⟨k, hk⟩ := by
      rw [← hπ, hπ1']
      simp
    rw [a5_conjA5_apply, MulEquiv.symm_apply_apply] at hid
    have h2 : a5ConjSub heK ⟨k, hk⟩ = ⟨k, hk⟩ := φ.injective hid
    have h3 := congrArg Subtype.val h2
    rw [a5_conjSub_apply, mul_inv_eq_iff_eq_mul] at h3
    exact hne h3
  have hc : a5ConjSub heK ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
    apply Subtype.ext
    rw [a5_conjSub_apply]
    show e * x * e⁻¹ = x
    rw [← hxe, mul_inv_cancel_right]
  have hfix : a5ConjA5 heK φ (φ ⟨x, hxK⟩) = φ ⟨x, hxK⟩ := by
    rw [a5_conjA5_apply, MulEquiv.symm_apply_apply, hc]
  have hπx : π * ((φ ⟨x, hxK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * π⁻¹ =
      ((φ ⟨x, hxK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
    have h1 : (MulAut.conjNormal (H := alternatingGroup (Fin 5)) π) (φ ⟨x, hxK⟩) =
        φ ⟨x, hxK⟩ := by
      rw [hπ]
      exact hfix
    have h2 := congrArg Subtype.val h1
    rwa [MulAut.conjNormal_apply] at h2
  have h3 : φ ⟨x, hxK⟩ ^ 3 = 1 := a5_centralizer_three π hπ3 hπ1 _ hπx
  have h4 : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := φ.injective (by rw [map_pow, h3, map_one])
  simpa using congrArg Subtype.val h4

theorem eq_top_of_forall_commutator_le_a5 {K : Type} [Group K] [Finite K]
    (φ : K ≃* alternatingGroup (Fin 5)) {j : K} (hj1 : j ≠ 1) (hj3 : j ^ 3 = 1)
    {H : Subgroup K}
    (hH : ∀ V : Subgroup K, ¬ 3 ∣ Nat.card V → j ∈ Subgroup.normalizer (V : Set K) →
      ⁅V, Subgroup.zpowers j⁆ ≤ H) : H = ⊤ := by
  have hgj1 : φ j ≠ 1 := fun h => hj1 (φ.injective (by rw [h, map_one]))
  have hgj3 : φ j ^ 3 = 1 := by rw [← map_pow, hj3, map_one]
  obtain ⟨σ, hσ⟩ := a5_conj_g0 (φ j) hgj3 hgj1
  let ψ : K ≃* alternatingGroup (Fin 5) := φ.trans (MulAut.conj σ⁻¹)
  have hψj : ψ j = a5g0 := by
    show MulAut.conj σ⁻¹ (φ j) = a5g0
    rw [MulAut.conj_apply, ← hσ]
    group
  let V1 : Subgroup K := a5W1.comap ψ.toMonoidHom
  let V2 : Subgroup K := a5W2.comap ψ.toMonoidHom
  have hmem1 : ∀ x : K, x ∈ V1 ↔ a5Kl1 (ψ x) := fun x => Iff.rfl
  have hmem2 : ∀ x : K, x ∈ V2 ↔ a5Kl2 (ψ x) := fun x => Iff.rfl
  have hmemV1 : ∀ m : alternatingGroup (Fin 5), a5Kl1 m → ψ.symm m ∈ V1 := by
    intro m hm
    rw [hmem1, MulEquiv.apply_symm_apply]
    exact hm
  have hmemV2 : ∀ m : alternatingGroup (Fin 5), a5Kl2 m → ψ.symm m ∈ V2 := by
    intro m hm
    rw [hmem2, MulEquiv.apply_symm_apply]
    exact hm
  have hnorm1 : j ∈ Subgroup.normalizer (V1 : Set K) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun n => ?_
    show n ∈ V1 ↔ j * n * j⁻¹ ∈ V1
    rw [hmem1, hmem1, map_mul, map_mul, map_inv, hψj]
    exact a5_kl1_conj (ψ n)
  have hnorm2 : j ∈ Subgroup.normalizer (V2 : Set K) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun n => ?_
    show n ∈ V2 ↔ j * n * j⁻¹ ∈ V2
    rw [hmem2, hmem2, map_mul, map_mul, map_inv, hψj]
    exact a5_kl2_conj (ψ n)
  have hnd1 : ¬ 3 ∣ Nat.card V1 := by
    refine a5_not_three_dvd V1 fun x hx h3 => ?_
    have h3' : ψ x ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have h1 : ψ x = 1 := a5_kl1_no_three (ψ x) ((hmem1 x).mp hx) h3'
    exact ψ.injective (by rw [h1, map_one])
  have hnd2 : ¬ 3 ∣ Nat.card V2 := by
    refine a5_not_three_dvd V2 fun x hx h3 => ?_
    have h3' : ψ x ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have h1 : ψ x = 1 := a5_kl2_no_three (ψ x) ((hmem2 x).mp hx) h3'
    exact ψ.injective (by rw [h1, map_one])
  have hcomm : ∀ V : Subgroup K, ¬ 3 ∣ Nat.card V → j ∈ Subgroup.normalizer (V : Set K) →
      ∀ m : alternatingGroup (Fin 5), ψ.symm m ∈ V → ⁅m, a5g0⁆ ∈ H.map ψ.toMonoidHom := by
    intro V hV hjV m hm
    have h1 : ⁅ψ.symm m, j⁆ ∈ H :=
      hH V hV hjV (Subgroup.commutator_mem_commutator hm (Subgroup.mem_zpowers j))
    have h2 : ψ (⁅ψ.symm m, j⁆) ∈ H.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom h1
    have e : ψ (⁅ψ.symm m, j⁆) = ⁅m, a5g0⁆ := by
      simp only [commutatorElement_def, map_mul, map_inv, MulEquiv.apply_symm_apply, hψj]
    rwa [e] at h2
  have hB1 : a5B1 ∈ H.map ψ.toMonoidHom := by
    have h := hcomm V1 hnd1 hnorm1 a5A1 (hmemV1 a5A1 a5_kl1_A1)
    rwa [a5_comm_A1] at h
  have hA1 : a5A1 ∈ H.map ψ.toMonoidHom := by
    have h := hcomm V1 hnd1 hnorm1 a5C1 (hmemV1 a5C1 a5_kl1_C1)
    rwa [a5_comm_C1] at h
  have hC2 : a5C2 ∈ H.map ψ.toMonoidHom := by
    have h := hcomm V2 hnd2 hnorm2 a5D2 (hmemV2 a5D2 a5_kl2_D2)
    rwa [a5_comm_D2] at h
  have hA2 : a5A2 ∈ H.map ψ.toMonoidHom := by
    have h := hcomm V2 hnd2 hnorm2 a5C2 (hmemV2 a5C2 a5_kl2_C2)
    rwa [a5_comm_C2] at h
  set H' : Subgroup (alternatingGroup (Fin 5)) := H.map ψ.toMonoidHom
  have hp3 : 3 ∣ Nat.card H' := a5_prime_dvd (mul_mem hA1 hC2) a5_p3 a5_p3_ne
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5 : 5 ∣ Nat.card H' := a5_prime_dvd (mul_mem hA1 hA2) a5_p5 a5_p5_ne
  have hW1 : a5W1 ≤ H' := by
    intro x hx
    have hx' : a5Kl1 x := hx
    rcases hx' with h | h | h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact hA1
    · rw [h]
      exact hB1
    · rw [h, a5_C1_eq]
      exact mul_mem hA1 hB1
  have hp4 : 4 ∣ Nat.card H' := by
    have h := Subgroup.card_dvd_of_le hW1
    rwa [a5_card_W1] at h
  have hdvd : Nat.card H' ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card H'
    rwa [CFSG.EvenSporadicStandard.HSStd.InvCent.card_alt5] at h
  have hle : Nat.card H' ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card H' := Nat.card_pos
  have h60 : Nat.card H' = 60 := by omega
  have htop : H' = ⊤ :=
    Subgroup.eq_top_of_card_eq H' (by rw [h60, CFSG.EvenSporadicStandard.HSStd.InvCent.card_alt5])
  rw [Subgroup.eq_top_iff']
  intro k
  have hk : ψ k ∈ H' := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hhk⟩ := Subgroup.mem_map.mp hk
  have hhk' : h = k := ψ.injective hhk
  rwa [hhk'] at hh

end CFSG.RankThree.PartTwo.Sec14.Ronan148J


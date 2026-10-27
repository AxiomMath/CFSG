module

public import CFSG.Goldschmidt.Steps.Rank2List
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Gen
import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin.H13.Cor332

open Equiv

theorem pow_apply_injOn_of_prime {Ω : Type*} {x : Perm Ω} {r : ℕ} (hr : r.Prime)
    (hxr : x ^ r = 1) {c : Ω} (hc : x c ≠ c) :
    ∀ i j : ℕ, i < r → j < r → (x ^ i) c = (x ^ j) c → i = j := by
  have key : ∀ i j : ℕ, i ≤ j → j < r → (x ^ i) c = (x ^ j) c → i = j := by
    intro i j hij hjr h
    by_contra hne
    set k := j - i with hk
    have hk0 : 0 < k := by omega
    have hkr : k < r := by omega
    have hxk : (x ^ k) c = c := by
      have : (x ^ j) c = (x ^ i) ((x ^ k) c) := by
        rw [← Perm.mul_apply, ← pow_add]; congr 2; omega
      rw [this] at h
      exact ((x ^ i).injective h).symm
    have : Fact r.Prime := ⟨hr⟩
    have hx1 : x ≠ 1 := fun h => hc (by rw [h]; rfl)
    have hord : orderOf x = r := orderOf_eq_prime hxr hx1
    have hcop : Nat.Coprime k (orderOf x) := by
      rw [hord]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).mpr
        (Nat.not_dvd_of_pos_of_lt hk0 hkr)))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hfix : ∀ n : ℕ, ((x ^ k) ^ n) c = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Perm.mul_apply, hxk, ih]
    apply hc
    rw [← hm]
    exact hfix m
  intro i j hi hj h
  rcases le_total i j with hij | hji
  · exact key i j hij hj h
  · exact (key j i hji hi h.symm).symm

theorem eq_one_of_commute_involution {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ x : Perm Ω}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hσ : σ * σ = 1) (hc : x * σ = σ * x)
    (hxr : x ^ r = 1) (hF : (Finset.univ.filter fun a => σ a = a).card < r)
    (hΩ : Fintype.card Ω < 2 * r + (Finset.univ.filter fun a => σ a = a).card) : x = 1 := by
  by_contra hx1
  obtain ⟨c, hc1⟩ : ∃ c, x c ≠ c := by
    by_contra h
    exact hx1 (Perm.ext fun a => by_contra fun hne => h ⟨a, hne⟩)
  have hinj := pow_apply_injOn_of_prime hr hxr hc1
  set F : Finset Ω := Finset.univ.filter fun a => σ a = a with hFdef
  have hcomm : ∀ n : ℕ, ∀ a, (x ^ n) (σ a) = σ ((x ^ n) a) := by
    intro n a
    have h : x ^ n * σ = σ * x ^ n := (Commute.pow_left (show Commute x σ from hc) n).eq
    exact congrFun (congrArg DFunLike.coe h) a
  let S : Finset Ω := (Finset.range r).image fun i => (x ^ i) c
  have hS : S.card = r := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have hmemS : ∀ a, a ∈ S ↔ ∃ i < r, (x ^ i) c = a := by
    intro a
    simp [S]
  by_cases hcF : σ c = c
  · have hsub : S ⊆ F := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := (hmemS a).mp ha
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hcomm, hcF]
    have := Finset.card_le_card hsub
    omega
  · have hnotF : ∀ a ∈ S, a ∉ F := by
      intro a ha haF
      obtain ⟨i, -, rfl⟩ := (hmemS a).mp ha
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and] at haF
      rw [← hcomm] at haF
      exact hcF ((x ^ i).injective haF)
    let S' : Finset Ω := S.image σ
    have hS' : S'.card = r := by rw [Finset.card_image_of_injective _ σ.injective, hS]
    by_cases hdisj : Disjoint S S'
    · exfalso
      have hU : (S ∪ S').card = 2 * r := by
        rw [Finset.card_union_of_disjoint hdisj, hS, hS']; ring
      have hnotF' : ∀ a ∈ S ∪ S', a ∉ F := by
        intro a ha haF
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hnotF a ha haF
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          have hbF := hnotF b hb
          simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and] at haF hbF
          have hσσ : σ (σ b) = b := by
            have := congrFun (congrArg DFunLike.coe hσ) b
            simpa using this
          rw [hσσ] at haF
          exact hbF haF.symm
      have hdisj2 : Disjoint (S ∪ S') F := Finset.disjoint_left.mpr hnotF'
      have hle := Finset.card_le_univ (S ∪ S' ∪ F)
      rw [Finset.card_union_of_disjoint hdisj2, hU] at hle
      omega
    · obtain ⟨a, haS, haS'⟩ := Finset.not_disjoint_iff.mp hdisj
      obtain ⟨j, hj, rfl⟩ := (hmemS a).mp haS
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haS'
      obtain ⟨i, hi, rfl⟩ := (hmemS b).mp hb
      have h1 : (x ^ i) (σ c) = (x ^ j) c := by rw [hcomm]; exact hba
      obtain ⟨t, ht, hσt⟩ : ∃ t < r, σ c = (x ^ t) c := by
        rcases lt_trichotomy i j with hij | hij | hji
        · refine ⟨j - i, by omega, ?_⟩
          apply (x ^ i).injective
          rw [h1, ← Perm.mul_apply, ← pow_add]
          congr 2
          omega
        · subst hij
          exact absurd ((x ^ i).injective h1) hcF
        · refine ⟨r - (i - j), by omega, ?_⟩
          have h2 : (x ^ (i - j)) (σ c) = c := by
            apply (x ^ j).injective
            rw [← Perm.mul_apply, ← pow_add]
            have : j + (i - j) = i := by omega
            rw [this, h1]
          have h3 : (x ^ (r - (i - j))) ((x ^ (i - j)) (σ c)) = σ c := by
            rw [← Perm.mul_apply, ← pow_add]
            have : r - (i - j) + (i - j) = r := by omega
            rw [this, hxr]; rfl
          rw [h2] at h3
          exact h3.symm
      have h4 : (x ^ (t + t)) c = c := by
        have hσσc : σ (σ c) = c := by
          have := congrFun (congrArg DFunLike.coe hσ) c
          simpa using this
        have : σ ((x ^ t) c) = (x ^ t) (σ c) := (hcomm t c).symm
        rw [hσt] at hσσc
        rw [this, hσt] at hσσc
        rw [pow_add, Perm.mul_apply]
        exact hσσc
      have hmod : (x ^ ((t + t) % r)) c = (x ^ 0) c := by
        rw [← pow_eq_pow_mod (t + t) hxr, h4]; rfl
      have hs : (t + t) % r = 0 :=
        hinj _ 0 (Nat.mod_lt _ hr.pos) hr.pos hmod
      have hdvd : r ∣ 2 * t := by
        have := Nat.dvd_of_mod_eq_zero hs
        rwa [← two_mul] at this
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
      · have : t = 0 := Nat.eq_zero_of_dvd_of_lt h ht
        rw [this] at hσt
        exact hcF hσt

section M11

open CFSG.QuasithinUnique.Unc25M11 CFSG.Goldschmidt.Rank2List CFSG.Open

theorem card_fixedPoints_sb : (Finset.univ.filter fun a : Fin 11 => sb a = a).card = 3 := by
  decide +kernel

theorem not_orderOf_commute_involution_nativeM11
    (x z : CFSG.Blueprint.NativeSporadic.M11) (hz : orderOf z = 2) (hxz : x * z = z * x)
    {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) : orderOf x ≠ r := by
  intro hxo
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_isConj_sb z hz)
  set x' := g * x * g⁻¹ with hx'
  have hx'o : orderOf x' = r := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [hx', MulAut.conj_apply] using this.trans hxo
  have hcomm : x' * ⟨sb, pw_mem _⟩ = ⟨sb, pw_mem _⟩ * x' := by
    rw [← hg]
    simp only [hx']
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hxz]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
  have h1 : (x' : Equiv.Perm (Fin 11)) * sb = sb * (x' : Equiv.Perm (Fin 11)) :=
    congrArg Subtype.val hcomm
  have h2 : (x' : Equiv.Perm (Fin 11)) ^ r = 1 := by
    rw [← Subgroup.coe_pow, ← hx'o, pow_orderOf_eq_one]; rfl
  have h3 := eq_one_of_commute_involution hr (by omega) (by decide +kernel) h1 h2
    (by rw [card_fixedPoints_sb]; omega)
    (by rw [card_fixedPoints_sb, Fintype.card_fin]; omega)
  have h4 : x' = 1 := Subtype.ext h3
  rw [h4, orderOf_one] at hx'o
  omega

theorem card_le_eight_of_isElemAbelian_nativeM11
    (E : Subgroup CFSG.Blueprint.NativeSporadic.M11) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ 3 := by
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  have hdvd : 2 ^ n ∣ 7920 := by
    rw [← hn, ← CFSG.Semidihedral.GL2Recognition.card_nativeM11]
    exact Subgroup.card_subgroup_dvd_card E
  by_contra hlt
  have hn4 : 4 ≤ n := by
    by_contra h
    have : n ≤ 3 := by omega
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hn4' : n ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
    have := h5.trans hdvd
    omega
  have hn16 : Nat.card E = 16 := by rw [hn, show n = 4 by omega]; norm_num
  have hindE : E.index = 495 := by
    have h := E.card_mul_index
    rw [hn16, CFSG.Semidihedral.GL2Recognition.card_nativeM11] at h
    omega
  have hP : IsPGroup 2 m11SylowTwo :=
    IsPGroup.of_card (n := 4) (by rw [card_m11SylowTwo]; norm_num)
  have hindP : m11SylowTwo.index = 495 := by
    have h := m11SylowTwo.card_mul_index
    rw [card_m11SylowTwo, CFSG.Semidihedral.GL2Recognition.card_nativeM11] at h
    omega
  have hsE : ¬ 2 ∣ E.index := by rw [hindE]; decide
  have hsP : ¬ 2 ∣ m11SylowTwo.index := by rw [hindP]; decide
  let SE : Sylow 2 CFSG.Blueprint.NativeSporadic.M11 := hEp.toSylow hsE
  let SP : Sylow 2 CFSG.Blueprint.NativeSporadic.M11 := hP.toSylow hsP
  let e : (SE : Subgroup CFSG.Blueprint.NativeSporadic.M11) ≃*
      (SP : Subgroup CFSG.Blueprint.NativeSporadic.M11) := Sylow.equiv SE SP
  obtain ⟨h1, h2, -, h4⟩ := m11_pair
  have hsa : sa ∈ CFSG.Blueprint.NativeSporadic.M11 := pw_mem _
  have hsb : sb ∈ CFSG.Blueprint.NativeSporadic.M11 := pw_mem _
  let x : CFSG.Blueprint.NativeSporadic.M11 := ⟨sb, hsb⟩
  let y : CFSG.Blueprint.NativeSporadic.M11 := ⟨sa ^ 2 * sb, mul_mem (pow_mem hsa 2) hsb⟩
  have hxP : x ∈ (SP : Subgroup CFSG.Blueprint.NativeSporadic.M11) := sb_mem_P0L
  have hy' : sa ^ 2 * sb ∈ P0L := mem_P0L_iff.mpr ⟨2, by norm_num, 1, by norm_num, by simp⟩
  have hyP : y ∈ (SP : Subgroup CFSG.Blueprint.NativeSporadic.M11) := hy'
  have hcomm : e.symm ⟨x, hxP⟩ * e.symm ⟨y, hyP⟩ = e.symm ⟨y, hyP⟩ * e.symm ⟨x, hxP⟩ :=
    hE.1.is_comm.comm _ _
  have := congrArg (fun z => (e z : CFSG.Blueprint.NativeSporadic.M11)) hcomm
  simp only [map_mul, MulEquiv.apply_symm_apply] at this
  exact h4 (congrArg Subtype.val this)

theorem twoLocalsSolvable_nativeM11 :
    TwoLocalsSolvable CFSG.Blueprint.NativeSporadic.M11 := by
  refine twoLocalsSolvable_of 3 card_le_eight_of_isElemAbelian_nativeM11 ?_ ?_
  · intro r hr h5 hrG d hd1 hdk h
    rw [CFSG.Semidihedral.GL2Recognition.card_nativeM11] at hrG
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h8 : 2 ^ d ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hdk
    have : r ≤ 7 := by omega
    interval_cases r <;> interval_cases d <;> omega
  · intro x z hz hxz r hr h5
    exact not_orderOf_commute_involution_nativeM11 x z hz hxz hr h5

theorem twoLocalsSolvable_catalogM11 :
    TwoLocalsSolvable CFSG.Open.M11 :=
  TwoLocalsSolvable.of_mulEquiv
    (CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.symm.trans
      (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11))
    twoLocalsSolvable_nativeM11

end M11

end CFSG.Quasithin.H13.Cor332

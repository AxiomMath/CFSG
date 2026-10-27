module

public import CFSG.RankThree.PartOne.S12.Sec1210
import CFSG.RankThree.PartOne.S12.Sec1212Aut
import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S12.Sec13Base
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

@[expose] def Node1212a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → torusWeylHasPCore p E →
      ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) ∨ (p = 5 ∧ RowModel p L 12)

namespace Sec1212

@[expose] def conjAut {M : Type*} [Group M] (Γ : Subgroup M) (φ : M)
    (h1 : ∀ x ∈ Γ, φ * x * φ⁻¹ ∈ Γ) (h2 : ∀ x ∈ Γ, φ⁻¹ * x * φ ∈ Γ) : MulAut ↥Γ where
  toFun x := ⟨φ * x * φ⁻¹, h1 x x.2⟩
  invFun x := ⟨φ⁻¹ * x * φ, h2 x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by
    show φ * ((x : M) * (y : M)) * φ⁻¹ = (φ * (x : M) * φ⁻¹) * (φ * (y : M) * φ⁻¹)
    group)

theorem coe_conjAut {M : Type*} [Group M] (Γ : Subgroup M) (φ : M)
    (h1 : ∀ x ∈ Γ, φ * x * φ⁻¹ ∈ Γ) (h2 : ∀ x ∈ Γ, φ⁻¹ * x * φ ∈ Γ) (x : ↥Γ) :
    ((conjAut Γ φ h1 h2 x : ↥Γ) : M) = φ * x * φ⁻¹ := rfl

theorem conjAut_pow_eq_one {M : Type*} [Group M] (Γ : Subgroup M) (φ : M)
    (h1 : ∀ x ∈ Γ, φ * x * φ⁻¹ ∈ Γ) (h2 : ∀ x ∈ Γ, φ⁻¹ * x * φ ∈ Γ) {p : ℕ} (hφ : φ ^ p = 1) :
    conjAut Γ φ h1 h2 ^ p = 1 := by
  have key : ∀ (k : ℕ) (x : ↥Γ),
      (((conjAut Γ φ h1 h2 ^ k) x : ↥Γ) : M) = φ ^ k * x * (φ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, coe_conjAut, ih x]
      group
  ext x
  rw [key p x, hφ]
  simp

section Hypotheses

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem torusImage_conj_mem (h122b : Node122b) (h : Sec12Hyp G p A c L E) {φ ψ : MulAut ↥E}
    (hφ : φ ∈ torusImage E (cNormalizer c)) (hψ : ψ ∈ torusImage E L) :
    φ * ψ * φ⁻¹ ∈ torusImage E L := by
  obtain ⟨w, hwH, hwE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hφ
  obtain ⟨x, hxL, hxE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hψ
  have hwL : w ∈ Subgroup.normalizer (L : Set G) := h122b G p A c L E h ⟨hwH, hwE⟩
  have hxE' : w * x * w⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    mul_mem (mul_mem hwE hxE) (inv_mem hwE)
  refine Sec12Three.mem_torusImage_iff.2 ⟨w * x * w⁻¹, ?_, hxE', ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hwL x).1 hxL
  · rw [← map_inv, ← map_mul, ← map_mul]
    rfl

theorem fixes_c_of_pow_eq_one (h : Sec12Hyp G p A c L E) (hcE : c ∈ E) {φ : MulAut ↥E}
    (hφH : φ ∈ torusImage E (cNormalizer c)) (hφp : φ ^ p = 1) :
    φ ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := exists_zpow_of_mem_torusImage hcE hφH
  have hiter : ∀ m : ℕ, (φ ^ m) ⟨c, hcE⟩ = (⟨c, hcE⟩ : ↥E) ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ' φ m, MulAut.mul_apply, ih, map_zpow, hk, ← zpow_mul, pow_succ' k m]
  have h1 : (⟨c, hcE⟩ : ↥E) ^ (k ^ p) = ⟨c, hcE⟩ := by
    rw [← hiter p, hφp]
    rfl
  have hord : orderOf (⟨c, hcE⟩ : ↥E) = p := by
    rw [Subgroup.orderOf_mk]
    exact Sec12Three.orderOf_c h
  have hpow : (⟨c, hcE⟩ : ↥E) ^ p = 1 :=
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h hcE)
  have h2 : (⟨c, hcE⟩ : ↥E) ^ (k ^ p - 1) = 1 := by
    rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rwa [hord] at this
  have h4 : (p : ℤ) ∣ k - 1 := by
    have h5 : (k : ZMod p) ^ p = (k : ZMod p) := ZMod.pow_card _
    have h6 : (((k ^ p - 1 : ℤ)) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
    push_cast at h6
    rw [h5] at h6
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) p).1 (by push_cast; exact h6)
  have h7 : (⟨c, hcE⟩ : ↥E) ^ k = ⟨c, hcE⟩ := by
    obtain ⟨t, ht⟩ := h4
    have hk' : k = 1 + p * t := by linarith
    rw [hk', zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, mul_one, zpow_one]
  rw [hk, h7]

theorem eq_one_of_commute (h122b : Node122b) (h124 : Node124) (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p * Nat.card ↥(E ⊓ L)) (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    {φ : MulAut ↥E} (hφH : φ ∈ torusImage E (cNormalizer c)) (hφp : φ ^ p = 1)
    (hcomm : ∀ ψ ∈ torusImage E L, φ * ψ = ψ * φ) : φ = 1 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup ↥E, B = (E ⊓ L).subgroupOf E := ⟨_, rfl⟩
  have hmemB : ∀ b : ↥E, b ∈ B ↔ (b : G) ∈ L := by
    intro b
    rw [hBdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  have hBH : ∀ ξ : MulAut ↥E, ξ ∈ torusImage E (cNormalizer c) → ∀ b ∈ B, ξ b ∈ B := by
    intro ξ hξ b hb
    obtain ⟨w, hwH, hwE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hξ
    have hwL : w ∈ Subgroup.normalizer (L : Set G) := h122b G p A c L E h ⟨hwH, hwE⟩
    rw [hmemB, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.1 hwL b).1 ((hmemB b).1 hb)
  have hBΓ : ∀ ψ ∈ torusImage E L, ∀ b ∈ B, ψ b ∈ B := by
    intro ψ hψ b hb
    obtain ⟨x, hxL, hxE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hψ
    rw [hmemB, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact L.mul_mem (L.mul_mem hxL ((hmemB b).1 hb)) (L.inv_mem hxL)
  have hBiff : ∀ b : ↥E, φ b ∈ B ↔ b ∈ B := by
    intro b
    refine ⟨fun hb => ?_, hBH φ hφH b⟩
    simpa using hBH φ⁻¹ (inv_mem hφH) _ hb
  have hpB : p ∣ Nat.card B := by
    have hBcard : Nat.card B = Nat.card ↥(E ⊓ L) := by
      rw [hBdef]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hBcard]
    have h3 : p ^ 3 ∣ Nat.card E := h.pow_three_dvd_card_E
    rw [hcard] at h3
    have h4 : p * p ^ 2 ∣ p * Nat.card ↥(E ⊓ L) := by
      rw [← pow_succ']
      exact h3
    exact dvd_trans (dvd_pow_self p (by norm_num)) (Nat.dvd_of_mul_dvd_mul_left hp.pos h4)
  have : Fintype ↥B := Fintype.ofFinite _
  let f : Equiv.Perm ↥B := (MulAut.toPerm (↥E) φ).subtypePerm hBiff
  have hf : f ^ p ^ 1 = 1 := by
    have h1 : f ^ p = ((MulAut.toPerm (↥E) φ) ^ p).subtypePerm _ :=
      Equiv.Perm.subtypePerm_pow _ _ _
    rw [pow_one, h1]
    ext x
    simp [← map_pow, hφp]
  have hf1 : f 1 = 1 := Subtype.ext (map_one φ)
  obtain ⟨b0, hb0f, hb01⟩ := Equiv.Perm.exists_fixed_point_of_prime' (σ := f) (a := 1)
    (by rw [← Nat.card_eq_fintype_card]; exact hpB) hf hf1
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup ↥E, D = B ⊓ autFixed E φ := ⟨_, rfl⟩
  have hmemD : ∀ e : ↥E, e ∈ D ↔ e ∈ B ∧ φ e = e := by
    intro e
    rw [hDdef, Subgroup.mem_inf]
    exact Iff.rfl
  have hDinv : ∀ ψ ∈ torusImage E L, ∀ s ∈ D, ψ s ∈ D := by
    intro ψ hψ s hs
    obtain ⟨hsB, hsφ⟩ := (hmemD s).1 hs
    refine (hmemD _).2 ⟨hBΓ ψ hψ s hsB, ?_⟩
    have h1 := congrArg (fun m : MulAut ↥E => m s) (hcomm ψ hψ)
    simp only [MulAut.mul_apply] at h1
    rw [h1, hsφ]
  have hD0 : D ≠ ⊥ := by
    intro hbot
    have hb0D : (b0 : ↥E) ∈ D := (hmemD _).2 ⟨b0.2, congrArg Subtype.val hb0f⟩
    rw [hbot, Subgroup.mem_bot] at hb0D
    exact hb01 (Subtype.ext hb0D)
  have hD1 : D ≠ ⊤ := by
    intro htop
    have hcD : (⟨c, hcE⟩ : ↥E) ∈ D := htop ▸ Subgroup.mem_top _
    exact hcL ((hmemB _).1 ((hmemD _).1 hcD).1)
  have hB₁L : ⁅E, L ⊓ torusNormalizer E⁆ ≤ L := commutator_le_L h122b h
  have hB₁E : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E := Sec12Three.commutator_le_left E L
  have hsplit : E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ := by
    rcases (h124 G p A c L E h).2 with ⟨hsup, -⟩ | ⟨-, hEE⟩
    · exact hsup
    · exact absurd (hB₁L (hEE.ge hcE)) hcL
  rcases Sec13Base.invariant_cases h124 h hDinv hD0 hD1 with hc | hc
  · exfalso
    have hcD : c ∈ D.map E.subtype := hc ▸ Subgroup.mem_zpowers c
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 hcD
    have hd' : d = ⟨c, hcE⟩ := Subtype.ext hdc
    exact hcL ((hmemB _).1 ((hmemD _).1 (hd' ▸ hd)).1)
  · have hfixc : φ ⟨c, hcE⟩ = ⟨c, hcE⟩ := fixes_c_of_pow_eq_one h hcE hφH hφp
    have hcomm' : ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ ⁅E, L ⊓ torusNormalizer E⁆, k * l = l * k :=
      fun k hk l hl => zpowers_comm_E h k hk l (hB₁E hl)
    refine MulEquiv.ext fun e => ?_
    rw [MulAut.one_apply]
    obtain ⟨z, hz, b, hb, hzb⟩ := exists_mul_of_mem_sup_of_commute hcomm' (hsplit.le e.2)
    have hzE : z ∈ E := hsplit ▸ (Subgroup.mem_sup_left hz)
    have hbE : b ∈ E := hB₁E hb
    have he : e = ⟨z, hzE⟩ * ⟨b, hbE⟩ := Subtype.ext hzb
    have hz' : φ ⟨z, hzE⟩ = ⟨z, hzE⟩ := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have : (⟨c ^ j, hzE⟩ : ↥E) = (⟨c, hcE⟩ : ↥E) ^ j := rfl
      rw [this, map_zpow, hfixc]
    have hb' : φ ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
      obtain ⟨d, hd, hdb⟩ := Subgroup.mem_map.1 (hc.ge hb)
      have hd' : d = ⟨b, hbE⟩ := Subtype.ext hdb
      rw [← hd']
      exact ((hmemD d).1 hd).2
    rw [he, map_mul, hz', hb']

end Hypotheses

end Sec1212

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem not_dvd_card_torusImage_cNormalizer (h122b : Node122b) (h124 : Node124)
    (h : Sec12Hyp G p A c L E) (hcard : Nat.card E = p * Nat.card ↥(E ⊓ L))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    (hAut : ∀ σ : MulAut ↥(torusImage E L), σ ^ p = 1 → σ = 1) :
    ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) := by
  intro hdvd
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hφp : (φ : MulAut ↥E) ^ p = 1 := by
    have h1 : φ ^ p = 1 := hφord ▸ pow_orderOf_eq_one φ
    simpa using congrArg Subtype.val h1
  have h1 : ∀ x ∈ torusImage E L, (φ : MulAut ↥E) * x * (φ : MulAut ↥E)⁻¹ ∈ torusImage E L :=
    fun x hx => Sec1212.torusImage_conj_mem h122b h φ.2 hx
  have h2 : ∀ x ∈ torusImage E L, (φ : MulAut ↥E)⁻¹ * x * (φ : MulAut ↥E) ∈ torusImage E L := by
    intro x hx
    simpa using Sec1212.torusImage_conj_mem h122b h (inv_mem φ.2) hx
  have hσ := hAut (Sec1212.conjAut _ (φ : MulAut ↥E) h1 h2)
    (Sec1212.conjAut_pow_eq_one _ _ h1 h2 hφp)
  have hcomm : ∀ ψ ∈ torusImage E L, (φ : MulAut ↥E) * ψ = ψ * (φ : MulAut ↥E) := by
    intro ψ hψ
    have h3 := congrArg (fun m : MulAut ↥(torusImage E L) => ((m ⟨ψ, hψ⟩ : ↥(torusImage E L)) :
      MulAut ↥E)) hσ
    simp only [Sec1212.coe_conjAut, MulAut.one_apply] at h3
    calc (φ : MulAut ↥E) * ψ = ((φ : MulAut ↥E) * ψ * (φ : MulAut ↥E)⁻¹) * (φ : MulAut ↥E) := by
          group
      _ = ψ * (φ : MulAut ↥E) := by rw [h3]
  have hone := Sec1212.eq_one_of_commute h122b h124 h hcard hZ φ.2 hφp hcomm
  have hφ1 : φ = 1 := Subtype.ext hone
  rw [hφ1, orderOf_one] at hφord
  exact hp.one_lt.ne hφord

theorem node1212a_of_inputs (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h1210 : Node1210) : Node1212a := by
  intro G _ _ p A c L E h hT hX
  obtain ⟨-, hcard, hZ⟩ := h1210 G p A c L E h hT hX
  obtain ⟨-, r, hr1, hr12, hmodel, hweyl, -, -⟩ := h123 G p A c L E h
  have hp := h.prime
  have h5 : 5 ≤ p := Sec12Three.five_le h
  by_cases hr10 : r ≤ 10
  · exact Or.inl (not_dvd_card_torusImage_cNormalizer h122b h124 h hcard hZ
      fun σ hσ => rowWeylIso_mulAut_pow_eq_one hr1 hr10 hweyl hp h5 σ hσ)
  · right
    have h1112 : r = 11 ∨ r = 12 := by omega
    rcases h1112 with rfl | rfl
    · exfalso
      obtain ⟨hp5, hcenter, -⟩ := hmodel
      exact hZ (by rw [hcenter, hp5])
    · exact ⟨hmodel.1, hmodel⟩

end Main

end CFSG.RankThree.PartOne

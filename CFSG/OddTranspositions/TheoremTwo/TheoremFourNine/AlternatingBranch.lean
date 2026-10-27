module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRankThree
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Helpers
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Recognition
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Transfer

public section

namespace CFSG.OddTranspositions.QZ

open Equiv

theorem cycleType_of_odd_involution {π : Perm (Fin 7)} (h2 : π * π = 1)
    (hs : Perm.sign π = -1) : π.cycleType = {2} ∨ π.cycleType = {2, 2, 2} := by
  have hall : ∀ n ∈ π.cycleType, n = 2 := by
    intro n hn
    have h1 := Perm.dvd_of_mem_cycleType hn
    have h2' : orderOf π ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h2])
    have h3 := Perm.two_le_of_mem_cycleType hn
    have := Nat.le_of_dvd (by norm_num) (h1.trans h2')
    omega
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card π.cycleType = k := ⟨_, rfl⟩
  have hrep : π.cycleType = Multiset.replicate k 2 := hk ▸ Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : π.cycleType.sum = 2 * k := by rw [hrep, Multiset.sum_replicate, smul_eq_mul]; ring
  have hle : 2 * k ≤ 7 := by
    have := Perm.sum_cycleType_le π
    rw [hsum] at this; simpa using this
  have hsign := Perm.sign_of_cycleType π
  rw [hs, hsum, hk] at hsign
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · exact absurd hsign (by decide)
  · left; rw [hrep]; rfl
  · exact absurd hsign (by decide)
  · right; rw [hrep]; rfl

theorem card_centralizer_triple {π : Perm (Fin 7)} (h : π.cycleType = {2, 2, 2}) :
    Nat.card (Subgroup.centralizer ({π} : Set (Perm (Fin 7)))) = 48 := by
  rw [Perm.nat_card_centralizer, h]
  decide

@[expose] def piA : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5
@[expose] def piB : Perm (Fin 7) := swap 0 2 * swap 1 3 * swap 4 6

theorem piA_sq : piA * piA = 1 := by decide
theorem piA_sign : Perm.sign piA = -1 := by
  simp [piA, Perm.sign_mul, Perm.sign_swap]
theorem piA_support : piA.support.card = 6 := by decide
theorem piA_cycleType : piA.cycleType = {2, 2, 2} := by
  rcases cycleType_of_odd_involution piA_sq piA_sign with h | h
  · have := Perm.sum_cycleType piA
    rw [h, piA_support] at this; simp at this
  · exact h
theorem piA_conj_piB : IsConj piA piB :=
  isConj_iff.mpr ⟨swap 1 2 * swap 5 6, by
    simp only [mul_inv_rev, swap_inv]
    ext i; fin_cases i <;> rfl⟩
set_option maxRecDepth 20000 in
theorem piAB_pow_six : (piA * piB) ^ 6 = 1 := by decide
set_option maxRecDepth 20000 in
theorem piAB_pow_two : (piA * piB) ^ 2 ≠ 1 := by
  intro h
  have h1 : ((piA * piB) ^ 2) 4 = 5 := by simp only [pow_succ, pow_zero, one_mul]; rfl
  rw [h] at h1
  exact absurd h1 (by decide)
set_option maxRecDepth 20000 in
theorem piAB_pow_three : (piA * piB) ^ 3 ≠ 1 := by
  intro h
  have h1 : ((piA * piB) ^ 3) 0 = 3 := by simp only [pow_succ, pow_zero, one_mul]; rfl
  rw [h] at h1
  exact absurd h1 (by decide)

variable {G : Type} [Group G] [Finite G]
variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem Config.false_of_A7 (hQ : Config D u w v z a K₁ S') {L : Subgroup G} [hL : L.Normal]
    (hL2 : L.index = 2) (hzL : z ∉ L) (hK₁L : K₁ ≤ L) (hDL : ∀ d ∈ D, d ∉ L)
    (e7 : L ≃* alternatingGroup (Fin 7)) : False := by
  classical
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, hz1, -, -, -, hzD⟩ := hQ.z_facts
  have hZ : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    have hc : e7 x ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨y, rfl⟩ := e7.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
      MulEquiv.map_eq_one_iff] at hc
    rw [hc]; exact one_mem _
  have hC := centralizer_eq_bot_of_odd_relIndex (N₀ := L) hL2 le_rfl
    (by rw [Subgroup.relIndex_self]; decide) hZ hQ.rad hQ.center
  let ρ : G →* Perm (Fin 7) :=
    (CFSG.ComponentClassification.AutL2Facts.a7AutEquiv.symm.toMonoidHom.comp
      (MulAut.congr e7).toMonoidHom).comp MulAut.conjNormal
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : (MulAut.conjNormal g : MulAut L) = MulAut.conjNormal 1 := by
      rw [map_one]
      apply (MulAut.congr e7).injective
      rw [map_one]
      apply CFSG.ComponentClassification.AutL2Facts.a7AutEquiv.symm.injective
      rw [map_one]
      exact hg
    exact Subgroup.mem_bot.mpr (eq_of_conjNormal_eq hC h1)
  have hcard : Nat.card G = Nat.card (Perm (Fin 7)) := by
    rw [← L.index_mul_card, hL2, Nat.card_congr e7.toEquiv, two_mul_nat_card_alternatingGroup]
  have hbij : Function.Bijective ρ :=
    (Function.Injective.bijective_of_nat_card_le hρinj hcard.ge)
  let E : G ≃* Perm (Fin 7) := MulEquiv.ofBijective ρ hbij
  have hEL : L.map (E : G →* Perm (Fin 7)) = alternatingGroup (Fin 7) := by
    apply Perm.eq_alternatingGroup_of_index_eq_two
    rw [Subgroup.index_map_equiv, hL2]
  have hsign : ∀ g : G, g ∉ L → Perm.sign (E g) = -1 := by
    intro g hg
    rcases Int.units_eq_one_or (Perm.sign (E g)) with h | h
    · exfalso; apply hg
      have : E g ∈ L.map (E : G →* Perm (Fin 7)) := by rw [hEL]; exact h
      obtain ⟨x, hx, hxg⟩ := this
      rwa [E.injective hxg] at hx
    · exact h
  have hsq : ∀ g : G, g * g = 1 → E g * E g = 1 := fun g h => by rw [← map_mul, h, map_one]
  have hzC : 120 ≤ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have h60 : 60 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
      have := Subgroup.card_dvd_of_le hQ.K₁_comm
      rwa [Nat.card_congr eK.toEquiv,
        show Nat.card (alternatingGroup (Fin 5)) = 60 by rw [Nat.card_eq_fintype_card]; rfl]
        at this
    have hlt : K₁ < Subgroup.centralizer ({z} : Set G) :=
      lt_of_le_of_ne hQ.K₁_comm fun h => hQ.z_not_mem_K₁
        (h ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_congr eK.toEquiv,
      show Nat.card (alternatingGroup (Fin 5)) = 60 by rw [Nat.card_eq_fintype_card]; rfl] at h1
    obtain ⟨k, hk⟩ := h60
    rw [hk] at h1 ⊢
    have : 2 ≤ k := by omega
    omega
  have hEzC : 120 ≤ Nat.card (Subgroup.centralizer ({E z} : Set (Perm (Fin 7)))) := by
    refine hzC.trans ?_
    rw [← Subgroup.card_map_of_injective (f := (E : G →* Perm (Fin 7))) E.injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    show E x * E z = E z * E x
    rw [← map_mul, ← map_mul, hx']
  have hzt : (E z).cycleType = {2} := by
    rcases cycleType_of_odd_involution (hsq z hz2) (hsign z hzL) with h | h
    · exact h
    · rw [card_centralizer_triple h] at hEzC; omega
  obtain ⟨d, hd⟩ := hQ.setup.nonempty
  have hDd := hQ.setup.eq_setOf_isConj hd
  have hd2 := hQ.mul_self_of_mem_D hd
  rcases cycleType_of_odd_involution (hsq d hd2) (hsign d (hDL d hd)) with h | h
  ·
    apply hzD
    have hc : IsConj (E d) (E z) := Perm.isConj_iff_cycleType_eq.mpr (h.trans hzt.symm)
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    rw [hDd]
    refine isConj_iff.mpr ⟨E.symm c, E.injective ?_⟩
    simp [hc]
  ·
    have hc : IsConj piA (E d) := Perm.isConj_iff_cycleType_eq.mpr (piA_cycleType.trans h.symm)
    obtain ⟨τ, hτ⟩ := isConj_iff.mp hc
    set e : G := E.symm (τ * piB * τ⁻¹)
    have he : e ∈ D := by
      rw [hDd]
      obtain ⟨σ, hσ⟩ := isConj_iff.mp piA_conj_piB
      refine isConj_iff.mpr ⟨E.symm (τ * σ * τ⁻¹), E.injective ?_⟩
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, e]
      rw [← hτ, ← hσ]; group
    have hEde : E (d * e) = τ * (piA * piB) * τ⁻¹ := by
      simp only [map_mul, MulEquiv.apply_symm_apply, e]
      rw [← hτ]; group
    have hpow : ∀ n : ℕ, (d * e) ^ n = 1 ↔ (piA * piB) ^ n = 1 := by
      intro n
      rw [← E.map_eq_one_iff, map_pow, hEde, conj_pow]
      constructor
      · intro h1
        have := congrArg (fun x => τ⁻¹ * x * τ) h1
        simpa [mul_assoc] using this
      · intro h1; rw [h1]; group
    rcases hQ.setup.oddT.2 d hd e he with h2 | hodd
    · exact piAB_pow_two ((hpow 2).mp (orderOf_dvd_iff_pow_eq_one.mp h2))
    · have h6 : orderOf (d * e) ∣ 6 := orderOf_dvd_of_pow_eq_one ((hpow 6).mpr piAB_pow_six)
      have h3 : orderOf (d * e) ∣ 3 := by
        have : Nat.Coprime (orderOf (d * e)) 2 := Nat.Coprime.symm
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (Nat.not_even_iff_odd.mpr hodd ∘
            even_iff_two_dvd.mpr))
        exact this.dvd_of_dvd_mul_left (by simpa [show (6 : ℕ) = 2 * 3 from rfl] using h6)
      exact piAB_pow_three ((hpow 3).mp (orderOf_dvd_iff_pow_eq_one.mp h3))

theorem pPrimeCore_eq_bot_of_rad {L : Subgroup G} [hL : L.Normal]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    CFSG.pPrimeCore 2 L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
  have hsolv : Group.IsSolvable (CFSG.pPrimeCore 2 L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  set M : Subgroup G := (CFSG.pPrimeCore 2 L).map L.subtype
  haveI : M.Normal := inferInstance
  have hMs : Group.IsSolvable M := solvable_of_solvable_injective
    (f := (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm.injective
  have := hrad M inferInstance hMs
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp this

end CFSG.OddTranspositions.QZ

module

public import CFSG.Quasithin.EmptyFaithful.S1421QA22Datum
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Alt7
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Defs
public import CFSG.Quasithin.EmptyFaithful.R3c6Psl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.action_cases (c : Core3Ctx T M H K1 L M₁)
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hcases : Lemma115Cases L z) :
    (∃ t : ↥L ⧸ CFSG.pCore 2 ↥L, t ≠ 1 ∧ t * t = 1 ∧ ∀ g ∈ modO2Image L K1, g * t = t * g) ∨
      (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∧
        ∃ (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
          σ.IsSwap ∧ ∀ g ∈ modO2Image L K1,
            ((ψ g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * σ =
              σ * ((ψ g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) ∨
      (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 ∧
        ∃ (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 7)) (σ : Equiv.Perm (Fin 7)),
          σ.cycleType = {2, 2, 2} ∧ ∀ g ∈ modO2Image L K1,
            ((ψ g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * σ =
              σ * ((ψ g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) := by
  have inner : InducesInner z L → ∃ t : ↥L ⧸ CFSG.pCore 2 ↥L, t ≠ 1 ∧ t * t = 1 ∧
      ∀ g ∈ modO2Image L K1, g * t = t * g := fun hin =>
    c.exists_inv_centralizing hc hz hz2 hLz hin
  rcases hcases with ⟨-, -, hin⟩ | ⟨-, -, -, hin⟩ | ⟨φ, σ, -, hsw, hact⟩ |
      ⟨φ, σ, -, hcyc, hact⟩ | ⟨-, hin⟩ | ⟨-, l, hl, hact, -⟩
  · exact Or.inl (inner hin)
  · exact Or.inl (inner hin)
  · obtain ⟨ψ, hψ⟩ := c.perm_datum hc hz hact
    refine Or.inr (Or.inl ⟨?_, ψ, σ, hsw, hψ⟩)
    have := Vol2.Ch11.SecA.card_alt6 (Y := ↥L ⧸ CFSG.pCore 2 ↥L) ⟨ψ⟩
    rw [this]
    norm_num
  · obtain ⟨ψ, hψ⟩ := c.perm_datum hc hz hact
    refine Or.inr (Or.inr ⟨?_, ψ, σ, hcyc, hψ⟩)
    have := Vol2.Ch11.SecA.card_alt7 (Y := ↥L ⧸ CFSG.pCore 2 ↥L) ⟨ψ⟩
    rw [this]
    norm_num
  · exact Or.inl (inner hin)
  · exact Or.inl (inner ⟨l, hl, hact⟩)

omit [Finite G] in
theorem exists_mem_orderOf_five {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (h5 : 5 ∣ Nat.card J) : ∃ g ∈ J, orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 h5
  exact ⟨g, g.2, by rw [Subgroup.orderOf_coe]; exact hg⟩

omit [Finite G] in
theorem false_of_alt6_perm {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (h5 : 5 ∣ Nat.card J) (ψ : X ≃* alternatingGroup (Fin 6)) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ.IsSwap) (hc : ∀ g ∈ J, ((ψ g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * σ =
      σ * ((ψ g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) : False := by
  obtain ⟨g, hgJ, hg⟩ := exists_mem_orderOf_five h5
  have hψ : orderOf (ψ g) = 5 := by rw [MulEquiv.orderOf_eq]; exact hg
  exact Alt7.false_of_alt6_swap hσ hψ (hc g hgJ)

omit [Finite G] in
theorem false_of_alt7_perm {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (h5 : 5 ∣ Nat.card J) (ψ : X ≃* alternatingGroup (Fin 7)) {σ : Equiv.Perm (Fin 7)}
    (hσ : σ.cycleType = {2, 2, 2}) (hc : ∀ g ∈ J,
      ((ψ g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * σ =
        σ * ((ψ g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) : False := by
  obtain ⟨g, hgJ, hg⟩ := exists_mem_orderOf_five h5
  have hψ : orderOf (ψ g) = 5 := by rw [MulEquiv.orderOf_eq]; exact hg
  exact Alt7.false_of_alt7_cycle hσ hψ (hc g hgJ)

theorem Core3Ctx.exists_inv_of_five_dvd (c : Core3Ctx T M H K1 L M₁)
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hcases : Lemma115Cases L z)
    (h5 : 5 ∣ Nat.card ↥(modO2Image L K1)) :
    (∃ t : ↥L ⧸ CFSG.pCore 2 ↥L, t ≠ 1 ∧ t * t = 1 ∧
      ∀ g ∈ modO2Image L K1, g * t = t * g) := by
  rcases c.action_cases hc hz hz2 hLz hcases with h | ⟨-, ψ, σ, hσ, hcomm⟩ |
      ⟨-, ψ, σ, hσ, hcomm⟩
  · exact h
  · exact (false_of_alt6_perm h5 ψ hσ hcomm).elim
  · exact (false_of_alt7_perm h5 ψ hσ hcomm).elim

theorem Core3Ctx.false_of_l3 (hL3 : L3InvCentSolvable) (c : Core3Ctx T M H K1 L M₁)
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hcases : Lemma115Cases L z) {n : ℕ}
    (hn : 2 ≤ n)
    (hX : IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSL3 (2 ^ n) (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have hcard : ∃ g r : ℕ, (g = 1 ∨ g = 3) ∧
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * g = (2 ^ n) ^ 3 * r := by
    rcases hX with hX | hX
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
      exact ⟨_, _, (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left _ _), hN⟩
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
      have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
          (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toEquiv,
          CFSG.QuasithinUnique.Bridge.Alt57.card_sl3_field, hK]
        ring
      exact ⟨1, _, Or.inl rfl, by rw [mul_one, hN]⟩
  obtain ⟨g, r, hg, hgr⟩ := hcard
  have h64 : 64 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * g := by
    rw [hgr]
    refine Dvd.dvd.mul_right ?_ r
    have h1 : 2 ^ 6 ∣ 2 ^ (n * 3) := pow_dvd_pow 2 (by omega)
    rw [← pow_mul]
    simpa using h1
  rcases c.action_cases hc hz hz2 hLz hcases with ⟨t, ht1, ht2, hcomm⟩ | ⟨h360, -⟩ |
      ⟨h2520, -⟩
  · have hsolv := hL3 n _ (by omega) hX t ht1 ht2
    have hle : modO2Image L K1 ≤ Subgroup.centralizer ({t} : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm x hx).symm
    have hs : Group.IsSolvable ↥(modO2Image L K1) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact c.not_isSolvable_modO2Image hs
  · rw [h360] at h64
    rcases hg with rfl | rfl <;> omega
  · rw [h2520] at h64
    rcases hg with rfl | rfl <;> omega

end S1421

end CFSG.Quasithin

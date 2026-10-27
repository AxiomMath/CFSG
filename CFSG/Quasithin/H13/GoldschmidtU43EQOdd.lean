module

public import CFSG.Quasithin.H13.GoldschmidtU43EQQuat

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

@[expose] def Vg : Subgroup G := (CFSG.oddCore ↥S.Cg1).map S.Cg1.subtype

omit [Finite G] in
theorem mem_Vg {x : G} :
    x ∈ S.Vg ↔ ∃ hx : x ∈ S.Cg1, (⟨x, hx⟩ : ↥S.Cg1) ∈ CFSG.oddCore ↥S.Cg1 := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hx, hv⟩
    exact ⟨⟨x, hx⟩, hv, rfl⟩

omit [Finite G] in
theorem Vg_le_Cg1 : S.Vg ≤ S.Cg1 := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

omit [Finite G] in
theorem conj_mem_Vg {c v : G} (hc : c ∈ S.Cg1) (hv : v ∈ S.Vg) : c * v * c⁻¹ ∈ S.Vg := by
  obtain ⟨hvC, hv'⟩ := S.mem_Vg.mp hv
  refine S.mem_Vg.mpr ⟨mul_mem (mul_mem hc hvC) (inv_mem hc), ?_⟩
  have hN : (CFSG.oddCore ↥S.Cg1).Normal := inferInstance
  exact hN.conj_mem ⟨v, hvC⟩ hv' ⟨c, hc⟩

theorem odd_orderOf_Vg {x : G} (hx : x ∈ S.Vg) : Odd (orderOf x) := by
  obtain ⟨hxC, hx'⟩ := S.mem_Vg.mp hx
  have := CFSG.Adapters.odd_orderOf_of_mem_oddCore hx'
  rwa [Subgroup.orderOf_mk] at this

omit [Finite G] in
theorem σ₁_mem_Cg1 : (S.σ₁ : G) ∈ S.Cg1 := by
  rw [Cg1]
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

omit [Finite G] in
theorem σ₁_mem_Vg : (S.σ₁ : G) ∈ S.Vg := by
  refine S.mem_Vg.mpr ⟨S.σ₁_mem_Cg1, ?_⟩
  set s : ↥S.Cg1 := ⟨(S.σ₁ : G), S.σ₁_mem_Cg1⟩ with hs
  have hcen : ∀ g : ↥S.Cg1, Commute g s := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hN : (Subgroup.zpowers s).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (s ^ k) := (hcen g).zpow_right k
    have e : g * s ^ k * g⁻¹ = s ^ k := by
      rw [hc.eq]
      group
    rw [e]
    exact hn⟩
  have h3 : (S.σ₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.jw.r1
    simpa using this
  have hs3 : s ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have hs1 : s ≠ 1 := fun h => by
    have h' : (S.σ₁ : G) = 1 := congrArg (fun x : ↥S.Cg1 => (x : G)) h
    exact S.σ₁_ne_one (Subtype.ext h')
  have hodd : Odd (Nat.card (Subgroup.zpowers s)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1]
    decide
  exact CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ hN hodd (Subgroup.mem_zpowers s)

theorem Vg_inf_Yg (hAU : (S.A : G) ∈ Uz z) {c : G} (hc : c ∈ S.Vg) (hcY : c ∈ S.Yg) :
    c = 1 := by
  have hodd := S.odd_orderOf_Vg hc
  have hdvd : orderOf c ∣ 8 := by
    have := orderOf_dvd_natCard (⟨c, hcY⟩ : ↥S.Yg)
    rw [Subgroup.orderOf_mk, S.card_Yg_eq hAU] at this
    exact this
  have h1 : orderOf c = 1 := by
    have hmem : orderOf c ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
    · rw [h] at hodd
      exact absurd hodd (by decide)
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem mem_zpowers_σ₁_of_comm_a₂ {r : ↥(Hz z)} (hr : r ∈ S.R) (hc : r * S.a₂ = S.a₂ * r) :
    r ∈ Subgroup.zpowers S.σ₁ := by
  set Rc : Subgroup ↥(Hz z) := S.R ⊓ Subgroup.centralizer ({S.a₂} : Set ↥(Hz z)) with hRc
  have hσ1 : S.σ₁ ∈ Rc :=
    ⟨S.hσR, Subgroup.mem_centralizer_singleton_iff.mpr S.a₂_comm_σ₁.symm⟩
  have hσ2 : S.σ₂ ∉ Rc := fun h =>
    S.a₂_not_comm_σ₂ (Subgroup.mem_centralizer_singleton_iff.mp h.2).symm
  have hle : Subgroup.zpowers S.σ₁ ≤ Rc := Subgroup.zpowers_le.mpr hσ1
  have hRcR : Rc ≤ S.R := inf_le_left
  have hcard3 : Nat.card (Subgroup.zpowers S.σ₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime S.jw.r1 S.σ₁_ne_one
  have hdvd : Nat.card Rc ∣ 9 := by
    have := Subgroup.card_dvd_of_le hRcR
    rwa [S.hR.card] at this
  have h3 : 3 ∣ Nat.card Rc := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard3] at this
  have hne9 : Nat.card Rc ≠ 9 := by
    intro h9
    have : Rc = S.R := Subgroup.eq_of_le_of_card_ge hRcR (by rw [h9, S.hR.card])
    exact hσ2 (by rw [this]; exact S.σ₂_mem)
  have hcRc : Nat.card Rc = 3 := by
    have hmem : Nat.card Rc ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h] at h3
      omega
    · exact h
    · exact absurd h hne9
  have heq : Subgroup.zpowers S.σ₁ = Rc :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcRc, hcard3])
  rw [heq]
  exact ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩

end JWSetup

end CFSG.Quasithin.H13.U43

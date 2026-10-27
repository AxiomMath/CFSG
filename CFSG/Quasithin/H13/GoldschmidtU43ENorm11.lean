module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm5

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem card_Nbar_ne_168 : Nat.card S.Nbar ≠ 168 := by
  classical
  intro h168
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set MK : Subgroup ↥S.Ng := S.Mg.subgroupOf S.Ng with hMK
  have hMKc : Nat.card MK = 81 := by
    rw [hMK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Mg_le_Ng).toEquiv]
    exact S.card_Mg_eq_81
  have hcardN : Nat.card ↥S.Ng = 168 * 81 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup MK, hMKc]
    show Nat.card S.Nbar * 81 = 168 * 81
    rw [h168]
  obtain ⟨r, hr7⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hcardN]; norm_num)
  have hr1 : r ^ 7 = 1 := by
    rw [← hr7]
    exact pow_orderOf_eq_one r
  have : Fintype ↥MK := Fintype.ofFinite _
  set φ : MulAut ↥MK := MulAut.conjNormal r with hφ
  have hφ7 : φ ^ 7 = 1 := by
    rw [hφ, ← map_pow, hr1, map_one]
  have hσ : (MulAut.toPerm ↥MK φ) ^ 7 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hφ7, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 7) (n := 1) hσ
  set Fm : Subgroup ↥MK := MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥MK) with hFm
  have hfix : (MulAut.toPerm ↥MK φ).supportᶜ.card = Nat.card Fm := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [hfix, Fintype.card_eq_nat_card, hMKc] at hmod
  have hdvd : Nat.card Fm ∣ 3 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card Fm
    rw [hMKc] at this
    simpa using this
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk4 : k = 4 := by
    have key : ∀ k ≤ 4, 3 ^ k ≡ 81 [MOD 7] → k = 4 := by decide
    exact key k hk (hkc ▸ hmod)
  have hFm81 : Nat.card Fm = 81 := by
    rw [hkc, hk4]
    norm_num
  have hFmtop : Fm = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hFm81, hMKc]
  have hcent : ∀ m ∈ S.Mg, m * (r : G) = (r : G) * m := by
    intro m hm
    have hx : (⟨⟨m, S.Mg_le_Ng hm⟩, hm⟩ : ↥MK) ∈ Fm := by
      rw [hFmtop]
      trivial
    have h1 : φ ⟨⟨m, S.Mg_le_Ng hm⟩, hm⟩ = ⟨⟨m, S.Mg_le_Ng hm⟩, hm⟩ := hx
    have h2 : (r : G) * m * (r : G)⁻¹ = m := by
      have := congrArg (fun y : ↥MK => ((y : ↥S.Ng) : G)) h1
      simpa [hφ, MulAut.conjNormal_apply] using this
    calc m * (r : G) = ((r : G) * m * (r : G)⁻¹) * r := by rw [h2]
      _ = (r : G) * m := by group
  have hrM : (r : G) ∈ S.Mg := S.centralizer_Mg hcent
  have hdvd7 : 7 ∣ 81 := by
    have := orderOf_dvd_natCard (⟨(r : G), hrM⟩ : ↥S.Mg)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hr7, S.card_Mg_eq_81] at this
    exact this
  omega

end JWSetup

end CFSG.Quasithin.H13.U43

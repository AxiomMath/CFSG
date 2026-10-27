module

public import CFSG.Quasithin.H13.A5S1327zc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem five_dvd_card_L : 5 ∣ Nat.card ↥L := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L)
  rw [h, S.card_oTwoQuot_L]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem eq_two_of_isL2Quot {f : ℕ} (hf : 1 ≤ f) (h : IsL2Quot f (oTwoQuot ↥L)) : f = 2 := by
  have h1 := h.card hf
  rw [S.card_oTwoQuot_L] at h1
  rcases Nat.lt_or_ge f 3 with h3 | h3
  · interval_cases f
    · norm_num at h1
    · rfl
  · have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem not_isLin2Type_of_setting (f : ℕ) : ¬ IsLin2Type L f := by
  classical
  rintro ⟨F, _, _, hF, α, -, hαker, β, -, hβker, hβ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨g, hgL₁, hg⟩ := S.exists_L1_c3p
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hlL : ((g : G) ^ 2 ^ k) ∈ L := L.pow_mem (S.L1_le_L hgL₁) _
  have hodd : Odd (orderOf ((g : G) ^ 2 ^ k)) := by
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    rw [orderOf_pow' _ h2k, Subgroup.orderOf_coe, hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hρl : S.frame.ρ (g ^ 2 ^ k) = c3p ^ 2 ^ k := by rw [map_pow, hg]
  have hρl1 : S.frame.ρ (g ^ 2 ^ k) ≠ 1 := by
    rw [hρl]
    intro h
    have h3 : orderOf c3p = 3 := orderOf_eq_prime c3p_cube (by decide)
    have hdvd : orderOf c3p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hlz : ((g : G) ^ 2 ^ k) * S.z * ((g : G) ^ 2 ^ k)⁻¹ = S.z := by
    have := (S.conj_eq_iff (g ^ 2 ^ k) ⟨S.z, S.z_mem_V⟩).2 (by
      rw [S.psi_z, hρl]
      refine pact_W4 ?_
      have : ∀ n : ℕ, (c3p ^ n) 4 = 4 := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, c3p_four, ih]
      exact this _)
    simpa using this
  have hVU : V ≤ blockU L := by
    calc V = ⁅V, L⁆ := S.irr.2.2.2.1.symm
      _ ≤ blockU L := Subgroup.commutator_mono S.V_le_pCoreOf_L le_rfl
  set u : ↥(blockU L) := ⟨S.z, hVU S.z_mem_V⟩ with hu
  set l : ↥L := ⟨(g : G) ^ 2 ^ k, hlL⟩ with hldef
  have hβu : Multiplicative.toAdd (β u) ≠ 0 := by
    intro h0
    have h1 : β u = 1 := by rw [← ofAdd_toAdd (β u), h0, ofAdd_zero]
    have h2 : u ∈ β.ker := h1
    rw [hβker, Subgroup.mem_subgroupOf] at h2
    have hzb : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h2.2⟩
    rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzb
    exact S.z_ne_one hzb
  have hfix := hβ l u u (by rw [hu, hldef]; exact hlz.symm)
  have hαodd : Odd (orderOf (α l)) := by
    refine Odd.of_dvd_nat hodd ?_
    refine (orderOf_map_dvd _ _).trans ?_
    rw [hldef, Subgroup.orderOf_mk]
  have hα1 : α l = 1 := SL2_eq_one_of_fix_of_odd (α l) hαodd hβu hfix.symm
  have hlQ : l ∈ CFSG.pCore 2 ↥L := by rw [← hαker]; exact hα1
  have hlQ' : l ∈ CFSG.Open.pCore 2 ↥L := by
    exact hlQ
  have hlP : ((g : G) ^ 2 ^ k) ∈ pCoreOf 2 L := ⟨l, hlQ', rfl⟩
  have hlP' : ((g : G) ^ 2 ^ k) ∈ pCoreOf 2 (L ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 L) hlP
    exact sup_le (le_normalizer_pCoreOf 2 L)
      (S.T_le_NL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  rw [← S.cLT] at hlP'
  exact hρl1 (S.frame.rho_eq_one_of_mem _ hlP'.2)

theorem not_f112ListC_of_vertex_exclusion {K VH : Subgroup G}
    (S' : Setting G T K VH) {Y : Subgroup G}
    (hSpecial : ¬ IsSpecialPow 2 4 2 ↥(pCoreOf 2 (L ⊔ bigB L K Y))) :
    ¬ F112ListC L K Y := by
  intro h
  unfold F112ListC at h
  dsimp only at h
  rcases h with ⟨f, hf, -, ⟨-, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩⟩ |
      ⟨f, hf, -, ⟨-, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩⟩ | ⟨f, hf, -, hq1, -, hsp, -⟩ | ⟨f, hf, -, hq1, -⟩ | ⟨a, -, -, -, hq2, -⟩ |
      ⟨f, hf, -, hq1, -, -, hq2, -⟩ | ⟨-, -, -, hq2, -⟩ | ⟨-, hq1, -⟩ | ⟨-, -, -, hq2, -⟩ |
      ⟨-, -, -, hq2, -⟩ | ⟨-, -, -, ⟨e2⟩, -⟩ | ⟨-, hq1, -⟩ | ⟨-, hq1, -⟩
  · exact S.not_isLin2Type_of_setting f hlin
  · have h5 : 5 ∣ Nat.card ↥(L ⊔ Y) :=
      S.five_dvd_card_L.trans (Subgroup.card_dvd_of_le le_sup_left)
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h5
    norm_num [Nat.factorial] at h5
  · exact S.not_isLin2Type_of_setting f hlin
  · have h5 : 5 ∣ Nat.card ↥(L ⊔ Y) :=
      S.five_dvd_card_L.trans (Subgroup.card_dvd_of_le le_sup_left)
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h5
    norm_num [Nat.factorial] at h5
  · have hf2 := S.eq_two_of_isL2Quot hf hq1
    subst hf2
    exact hSpecial hsp
  · have := S.eq_two_of_isL2Quot (by omega) hq1
    omega
  · have := S'.eq_two_of_isL2Quot (by omega) hq2
    omega
  · have h1 := S.eq_two_of_isL2Quot hf hq1
    have h2 := S'.eq_two_of_isL2Quot (by omega) hq2
    omega
  · have := S'.eq_two_of_isL2Quot (by norm_num) hq2
    omega
  · have := S.eq_two_of_isL2Quot le_rfl hq1
    omega
  · have := S'.eq_two_of_isL2Quot le_rfl hq2
    omega
  · have := S'.eq_two_of_isL2Quot le_rfl hq2
    omega
  · have h6 := S'.card_oTwoQuot_L
    rw [Nat.card_congr e2.toEquiv, Nat.card_perm, Nat.card_fin] at h6
    norm_num at h6
  · have := S.eq_two_of_isL2Quot le_rfl hq1
    omega
  · have := S.eq_two_of_isL2Quot le_rfl hq1
    omega

end Setting

end CFSG.Quasithin.H13.A5

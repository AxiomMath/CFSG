module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block
public import CFSG.Quasithin.H13.A5S1327r

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open Equiv
open scoped commutatorElement Pointwise

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_alt5 : ∃ φ : ↥L →* alternatingGroup (Fin 5), Function.Surjective φ ∧
    φ.ker = CFSG.pCore 2 ↥L := by
  obtain ⟨φ, hφ, hker⟩ := S.a5
  exact ⟨φ, hφ, hker.trans (openPCore_eq_pCore' 2 ↥L)⟩

theorem card_of_surj {K : Type*} [Group K] (α : ↥L →* K) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : Nat.card K = 60 := by
  obtain ⟨φ, hφ, hφk⟩ := S.exists_alt5
  have h1 : Nat.card K = Nat.card (↥L ⧸ α.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv).symm
  have h2 : Nat.card (alternatingGroup (Fin 5)) = Nat.card (↥L ⧸ φ.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  rw [h1, hker, ← hφk, ← h2]
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem V_le_L : V ≤ L := by
  calc V = ⁅V, L⁆ := S.irr.2.2.2.1.symm
    _ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 : v * l * v⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (S.T_le_NL (S.V_le_T hv)) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem h1 (L.inv_mem hl)

theorem V_le_pCoreOf_L : V ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 S.V_le_L S.frame.L_le S.isPGroup_V

theorem blockU_eq_V (hL : IsShort2 L) : blockU L = V := by
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  have hle : ⁅V, L⁆ ≤ blockU L := Subgroup.commutator_mono S.V_le_pCoreOf_L le_rfl
  have hne : ⁅V, L⁆ ≠ ⊥ := by
    rw [hcomm]
    exact S.irr.2.1
  have h := L246C127.blockU_le_commutator_of_ne_bot hL S.frame.L_le S.isPGroup_V hle hne
  rw [hcomm] at h hle
  exact le_antisymm h hle

theorem blockZ_eq_bot (hL : IsShort2 L) : blockZ L = ⊥ := by
  show blockU L ⊓ Subgroup.centralizer (L : Set G) = ⊥
  rw [S.blockU_eq_V hL]
  exact S.V_inf_centralizer_L

theorem exists_odd_fix_z : ∃ l ∈ L, Odd (orderOf l) ∧ l * S.z * l⁻¹ = S.z ∧ l ∉ pCoreOf 2 L := by
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
  refine ⟨_, hlL, hodd, hlz, fun hlO => hρl1 ?_⟩
  have hl1 : (g : G) ^ 2 ^ k = 1 := by
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hlO⟩
    have hb' : ((g : G) ^ 2 ^ k) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    exact eq_one_of_pow_coprime hb' (pow_orderOf_eq_one _)
      (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hodd))
  have : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hl1)
  rw [this, map_one]

theorem not_isLin2Type (hL : IsShort2 L) {n : ℕ} (h : IsLin2Type L n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hcard, α, hα, hker, β, hβ, hβker, hequiv⟩ := h
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  obtain ⟨l, hlL, hlodd, hlz, hlO⟩ := S.exists_odd_fix_z
  have hzU : S.z ∈ blockU L := by rw [S.blockU_eq_V hL]; exact S.z_mem_V
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, S.blockZ_eq_bot hL, Subgroup.bot_subgroupOf]
  have hfix := hequiv ⟨l, hlL⟩ ⟨S.z, hzU⟩ ⟨S.z, hzU⟩ hlz.symm
  have hne : Multiplicative.toAdd (β ⟨S.z, hzU⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨S.z, hzU⟩ = 1 := by
      rw [← ofAdd_toAdd (β ⟨S.z, hzU⟩), h0, ofAdd_zero]
    have h2 : (⟨S.z, hzU⟩ : ↥(blockU L)) = 1 := hinj (h1.trans (map_one β).symm)
    exact S.z_ne_one (congrArg Subtype.val h2)
  have hodd : Odd (orderOf (α ⟨l, hlL⟩)) := by
    refine Odd.of_dvd_nat hlodd ((orderOf_map_dvd _ _).trans ?_)
    rw [Subgroup.orderOf_mk]
  have h1 := SL2_eq_one_of_fix_of_odd (α ⟨l, hlL⟩) hodd hne hfix.symm
  have h2 : (⟨l, hlL⟩ : ↥L) ∈ α.ker := h1
  rw [hker] at h2
  exact hlO ((AppC.mem_pCore_iff_mem_blockQ _).1 h2)

theorem eq_five_of_isAltType {m : ℕ} (hm3 : 3 ≤ m) (h : IsAltType L m) : m = 5 := by
  obtain ⟨α, hα, hker, -⟩ := h
  have h1 := S.card_of_surj α hα hker
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  by_contra hm5
  by_cases h6 : m ≤ 6
  · interval_cases m
    all_goals first
      | exact hm5 rfl
      | (revert h1; decide)
  · have h7 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le (by omega)
    have h8 : Nat.factorial 7 = 5040 := rfl
    omega

end Setting

end CFSG.Quasithin.H13.A5

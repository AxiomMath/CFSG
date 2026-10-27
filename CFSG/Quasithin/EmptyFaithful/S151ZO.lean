module

public import CFSG.Quasithin.EmptyFaithful.S151ZD
public import CFSG.Quasithin.EmptyFaithful.A38cBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem chi0_isAltType_three [Finite G] {H K : Subgroup G} {m : ℕ} (hK : IsChi0Block H K)
    (hH : Nat.card ↥H ∣ 2 ^ m * 21 ∨ Nat.card ↥H ∣ 2 ^ m * 9) : IsAltType K 3 := by
  have hKH : Nat.card ↥K ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hK.1.2.1
  have hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  have hqH : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 2 ^ m * 21 ∨
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 2 ^ m * 9 := by
    rcases hH with h | h
    · exact Or.inl ((hq.trans hKH).trans h)
    · exact Or.inr ((hq.trans hKH).trans h)
  rcases hK.2 with ⟨n, hn, hL2⟩ | hA3 | hA5
  · exfalso
    rw [card_quotPCore_of_isLin2Type hL2] at hqH
    obtain ⟨x, hx⟩ : ∃ x, x = 4 ^ n := ⟨_, rfl⟩
    have h4n : 16 ≤ x := by
      rw [hx]
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hev : Even x := by
      rw [hx]
      exact Nat.even_pow.mpr ⟨by decide, by omega⟩
    have hmod : x % 2 = 0 := Nat.even_iff.mp hev
    have h4dvd : 4 ∣ x := by
      rw [hx]
      exact dvd_pow_self 4 (by omega)
    rw [← hx] at hqH
    have hd2 : Nat.Coprime (x - 1) 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      omega
    have hdm : Nat.Coprime (x - 1) (2 ^ m) := Nat.Coprime.pow_right m hd2
    rcases hqH with h | h
    · have h1 : x - 1 ∣ 2 ^ m * 21 := (Dvd.intro_left _ rfl).trans h
      have h2 : x - 1 ∣ 21 := Nat.Coprime.dvd_of_dvd_mul_left hdm h1
      have h3 : x - 1 ≤ 21 := Nat.le_of_dvd (by norm_num) h2
      have h5 : x ≤ 22 := by omega
      interval_cases x <;> omega
    · have h1 : x - 1 ∣ 2 ^ m * 9 := (Dvd.intro_left _ rfl).trans h
      have h2 : x - 1 ∣ 9 := Nat.Coprime.dvd_of_dvd_mul_left hdm h1
      have h3 : x - 1 ≤ 9 := Nat.le_of_dvd (by norm_num) h2
      omega
  · exact hA3
  · exfalso
    rw [card_quotPCore_of_isAltType (by norm_num) hA5] at hqH
    have h60 : Nat.factorial 5 / 2 = 60 := by decide
    rw [h60] at hqH
    have h5 : (5 : ℕ) ∣ 2 ^ m * 21 ∨ (5 : ℕ) ∣ 2 ^ m * 9 := by
      rcases hqH with h | h
      · exact Or.inl ((by norm_num : 5 ∣ 60).trans h)
      · exact Or.inr ((by norm_num : 5 ∣ 60).trans h)
    rcases h5 with h | h
    · rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
      · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
        omega
      · omega
    · rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
      · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
        omega
      · omega

theorem not_C126Third_of_parBig [Finite G] {L S P : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hPL : P ≤ L)
    (hBP : S ⊓ L ≤ P) (hL : CharTwo L) (hbig : ParBig L P)
    (hA3 : ∀ K : Subgroup G, IsChi0Block (P ⊔ S) K → IsAltType K 3) :
    ¬ C126Third (P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, -, hres, -, -⟩
  have hHN : P ⊔ S ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSP
  have hTR : twoResidual (P ⊔ S) ≤ P :=
    twoResidual_le_of_isTwoQuotient le_sup_left hHN (zb_two_pow hSP hS2)
  have hK₀ := hK ⟨0, hr⟩
  set K₀ : Subgroup G := K ⟨0, hr⟩ with hK₀def
  have hA3₀ : IsAltType K₀ 3 := hA3 K₀ hK₀.1
  have hshort : IsShort2 K₀ := hK₀.1.1.1
  have hresK : K₀ ≤ twoResidual (P ⊔ S) :=
    calc K₀ ≤ ⨆ j, K j := le_iSup K _
      _ = twoResidual (P ⊔ S) := hres.symm
  obtain ⟨x, hxK, hx3⟩ := zb_exists_orderOf_three hA3₀
  have hxP : x ∈ P := hTR (hresK hxK)
  have hKP : K₀ ≤ P := hresK.trans hTR
  set X : Subgroup G := pCoreOf 2 P with hXdef
  have hXp : IsPGroup 2 ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hXP : X ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hHX : P ⊔ S ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) ?_
    exact fun s hs => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hSP hs)
  have hKU : K₀ ≤ Subgroup.normalizer (X : Set G) := hKP.trans (le_sup_left.trans hHX)
  have hXH : X ≤ pCoreOf 2 (P ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hXP.trans le_sup_left) hHX hXp
  have hUK : X ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => C1Pack.conj_mem_block_of_mem_pCoreOf hK₀.1.1 (hXH hy) hk
    · intro hk
      have := C1Pack.conj_mem_block_of_mem_pCoreOf hK₀.1.1 (hXH (X.inv_mem hy)) hk
      simpa [mul_assoc] using this
  obtain ⟨hcard, hdisj⟩ := zb_commutator_card_le hXp hKU hUK hshort hA3₀ hxK hx3
  set Px : Subgroup G := Subgroup.zpowers x with hPx
  have hPxK : Px ≤ K₀ := by rw [hPx, Subgroup.zpowers_le]; exact hxK
  have hPxN : Px ≤ Subgroup.normalizer (X : Set G) := hPxK.trans hKU
  have hcop : Nat.Coprime (Nat.card ↥Px) (Nat.card ↥X) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    rw [hPx, Nat.card_zpowers, hx3, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hXsolv : Group.IsSolvable ↥X := by
    have hnil : Group.IsNilpotent ↥X := hXp.isNilpotent
    infer_instance
  have e1 : ⁅⁅X, Px⁆, Px⁆ = ⁅X, Px⁆ := zb_commutator_double_eq_self Px X hPxN hcop hXsolv
  have hW : ⁅⁅⁅X, Px⁆, Px⁆, Px⁆ = ⁅X, Px⁆ := by rw [e1, e1]
  rw [hW] at hcard hdisj
  set QL : Subgroup G := pCoreOf 2 L with hQLdef
  have hQLp : IsPGroup 2 ↥QL := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hQLP : QL ≤ P := (hsyl.pCoreOf_le).trans hBP
  have hPQL : P ≤ Subgroup.normalizer (QL : Set G) :=
    hPL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hQLX : QL ≤ X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQLP hPQL hQLp
  have hPxQL : Px ≤ Subgroup.normalizer (QL : Set G) := (hPxK.trans hKP).trans hPQL
  set Y : Subgroup G := ⁅QL, Px⁆ with hYdef
  have hYQL : Y ≤ QL := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPxQL
  have hYX : Y ≤ ⁅X, Px⁆ := Subgroup.commutator_mono hQLX le_rfl
  have hYp : IsPGroup 2 ↥Y := hQLp.to_le hYQL
  have hxL : x ∈ L := hPL hxP
  have hY0 : Y ≠ ⊥ := by
    intro hY
    have hxC : x ∈ Subgroup.centralizer (QL : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : ⁅q, x⁆ ∈ Y := Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
      rw [hY] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
    exact zb_not_mem_of_orderOf_three hQLp (hL ⟨hxL, hxC⟩) hx3
  have hYx : x ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPxQL (Subgroup.mem_zpowers x)
  have hYC : Y ⊓ Subgroup.centralizer (Px : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hYX).trans hdisj.le)
  have hY4 : 4 ≤ Nat.card ↥Y := zb_card_ge_four hYp hYx hY0 hYC
  have hYeq : Y = ⁅X, Px⁆ := Subgroup.eq_of_le_of_card_ge hYX (hcard.trans hY4)
  apply hbig x hxP hx3
  rw [← hXdef, ← hPx, ← hYeq]
  exact hYQL

end CFSG.Quasithin

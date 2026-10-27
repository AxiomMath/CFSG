module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch1ModO2
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.B69Iso
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.SBd17

open CFSG.Blueprint
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

section Orders

variable {X : Type} [Group X]

private theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) :
    Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

private theorem card_of_isHat {S : Type} [Group S] (h : IsHat X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

private theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

private theorem card_of_isSL2 {p : ℕ} (hp : p.Prime) (h : IsSL2 p X) :
    Nat.card X = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num),
    Nat.card_zmod]
  simp

private theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one

private theorem eleven_dvd_card_M22 : 11 ∣ Nat.card ↥NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg, hg11, hg1⟩ : ∃ g ∈ NativeSporadic.M22, g ^ 11 = 1 ∧ g ≠ 1 := by
    refine ⟨_, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have ho : orderOf (⟨g, hg⟩ : ↥NativeSporadic.M22) = 11 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg11 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

private theorem card_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem card_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) :
    ∃ k, Nat.card X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

private theorem four_le_card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) : 4 ≤ Nat.card X := by
  obtain ⟨Z, -, hZ, -⟩ := h
  rw [← hZ]
  exact Subgroup.card_le_card_group Z

private theorem isE2_pGroup {m : ℕ} (hm : 2 ≤ m) :
    ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, 2 ≤ k ∧ Nat.card V = 2 ^ k :=
  fun _ _ _ hV => ⟨m, hm, card_isE2 hV⟩

private theorem isExtraspecial2_pGroup {m : ℕ} (hm : 1 ≤ m) :
    ∀ (V : Type) [Group V] [Finite V], IsExtraspecial2 m V → ∃ k, 2 ≤ k ∧ Nat.card V = 2 ^ k :=
  fun _ _ _ hV => ⟨1 + 2 * m, by omega, hV.2⟩

private theorem isZ4StarExtra2_pGroup :
    ∀ (V : Type) [Group V] [Finite V], IsZ4StarExtra2 V → ∃ k, 2 ≤ k ∧ Nat.card V = 2 ^ k := by
  intro V _ _ hV
  obtain ⟨k, hk⟩ := card_isZ4StarExtra2 hV
  have h4 := four_le_card_isZ4StarExtra2 hV
  refine ⟨k, ?_, hk⟩
  by_contra hk2
  have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem isZ4Cubed_pGroup :
    ∀ (V : Type) [Group V] [Finite V], IsZ4Cubed V → ∃ k, 2 ≤ k ∧ Nat.card V = 2 ^ k :=
  fun _ _ _ hV => ⟨6, by norm_num, card_isZ4Cubed hV⟩

private theorem card_alt5 (h : IsAlt 5 X) : Nat.card X = 60 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_alt6 (h : IsAlt 6 X) : Nat.card X = 360 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_hat6 (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  rw [card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_L32 (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

private theorem card_L34 (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

private theorem false_of_isPSL_three_two_two_of_isPSL_four_two_one (h3 : IsPSL 3 2 2 X)
    (h4 : IsPSL 4 2 1 X) : False := by
  obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h3
  obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := h4
  exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
    (by rw [hK3]; norm_num) e4 e3

private theorem not_isPGroup_two_of_card (hc : Nat.card X = 20160) : ¬ IsPGroup 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [hc] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

private theorem two_mul_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 X) :
    2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp hp2 h

private theorem false_of_isPSL_two_two {m : ℕ} (h : IsPSL 2 2 m X) (hc : Nat.card X = 20160) :
    False := by
  have hm : 1 ≤ m := h.1.2.1
  have hform := card_of_isPSL (by norm_num) h
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [hg, Nat.div_one] at hform
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hform
  rw [hc] at hform
  rcases Nat.lt_or_ge m 5 with hlt | hge
  · interval_cases m <;> omega
  · have h5 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : 32 * 1023 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      refine Nat.mul_le_mul (by simpa using h5) ?_
      have : 32 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (by simpa using h5) 2
      omega
    omega

private theorem false_of_isSz {f : ℕ} (h : IsSz f X)
    (hc : Nat.card X = 20160) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hc
  rcases Nat.lt_or_ge a 2 with hlt | hge
  · obtain rfl : a = 1 := by omega
    norm_num at hc
  · have h5 : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * a + 1) = q at h5 hc
    have hq : 32 ≤ q := by simpa using h5
    have h1 : 32 * 32 ≤ q ^ 2 := by nlinarith
    have h2 : 31 ≤ q - 1 := by omega
    have h3 : 1025 ≤ q ^ 2 + 1 := by omega
    have h4 : 1024 * 31 * 1025 ≤ q ^ 2 * (q - 1) * (q ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

private theorem no_sl2_card {p : ℕ}
    (h : p * (p ^ 2 - 1) = 20160 ∨ p * (p ^ 2 - 1) = 40320 ∨ p * (p ^ 2 - 1) = 80640) : False := by
  rcases Nat.lt_or_ge p 44 with hlt | hge
  · interval_cases p <;> omega
  · have h1 : 44 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hge 2
    have : 44 * 1935 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
    omega

private theorem pCore_eq_of_simple_quotient {Y : Type} [Group Y] (Z : Subgroup Y) [Z.Normal]
    (hZ : IsPGroup 2 ↥Z) (hs : IsSimpleGroup (Y ⧸ Z)) (hnp : ¬ IsPGroup 2 (Y ⧸ Z)) :
    CFSG.pCore 2 Y = Z := by
  have hP : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  apply le_antisymm
  · have hPn : ((CFSG.pCore 2 Y).map (QuotientGroup.mk' Z)).Normal :=
      hP.map _ (QuotientGroup.mk'_surjective Z)
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 Y).map (QuotientGroup.mk' Z)) with h | h
    · have := (Subgroup.map_eq_bot_iff _).mp h
      rwa [QuotientGroup.ker_mk'] at this
    · exfalso
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 Y).map (QuotientGroup.mk' Z)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := Y)).map _
      rw [h] at hp
      exact hnp (hp.of_equiv Subgroup.topEquiv)
  · exact le_sSup ⟨inferInstance, hZ⟩

end Orders

section Simple

structure L34Row {Q : Type} [Group Q] (B : Subgroup Q) : Prop where
  perfect : Group.IsPerfect ↥B
  shape : (Nat.card ↥B = 20160 ∧ IsSimpleGroup ↥B ∧ IsPSL 3 2 2 ↥B) ∨
    (Nat.card ↥B = 40320 ∧ ∃ (Z : Subgroup ↥B) (_ : Z.Normal), Z ≤ Subgroup.center ↥B ∧
      Nat.card ↥Z = 2 ∧ IsPSL 3 2 2 (↥B ⧸ Z))

variable {Q : Type} [Group Q] {B : Subgroup Q}

theorem L34Row.card_cases (hD : L34Row B) : Nat.card ↥B = 20160 ∨ Nat.card ↥B = 40320 := by
  rcases hD.shape with ⟨hc, -⟩ | ⟨hc, -⟩
  · exact Or.inl hc
  · exact Or.inr hc

private theorem L34Row.exists_Z (hD : L34Row B) :
    ∃ (Z : Subgroup ↥B) (_ : Z.Normal), (Nat.card ↥Z = 1 ∨ Nat.card ↥Z = 2) ∧
      Nat.card ↥B = Nat.card ↥Z * 20160 ∧ IsPSL 3 2 2 (↥B ⧸ Z) := by
  rcases hD.shape with ⟨hc, -, hB⟩ | ⟨hc, Z, hZn, -, hZ, hq⟩
  · refine ⟨⊥, inferInstance, Or.inl (Subgroup.card_bot), ?_, ?_⟩
    · rw [Subgroup.card_bot, hc]
    · exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        (QuotientGroup.quotientBot : (↥B ⧸ (⊥ : Subgroup ↥B)) ≃* ↥B) hB
  · exact ⟨Z, hZn, Or.inr hZ, by omega, hq⟩

private theorem L34Row.pCore_data (hD : L34Row B) :
    ∃ (Z : Subgroup ↥B) (_ : Z.Normal), CFSG.pCore 2 ↥B = Z ∧
      (Nat.card ↥Z = 1 ∨ Nat.card ↥Z = 2) ∧ IsPSL 3 2 2 (↥B ⧸ Z) := by
  obtain ⟨Z, hZn, hZc, -, hq⟩ := hD.exists_Z
  refine ⟨Z, hZn, ?_, hZc, hq⟩
  have hZ2 : IsPGroup 2 ↥Z := by
    rcases hZc with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  have hs : IsSimpleGroup (↥B ⧸ Z) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hq).2
  exact pCore_eq_of_simple_quotient Z hZ2 hs (not_isPGroup_two_of_card (card_L34 hq))

theorem L34Row.card_pCore_le (hD : L34Row B) : Nat.card ↥(CFSG.pCore 2 ↥B) ≤ 2 := by
  obtain ⟨Z, hZn, hpc, hZc, -⟩ := hD.pCore_data
  rw [hpc]
  omega

theorem L34Row.isPSL_modO2 (hD : L34Row B) : IsPSL 3 2 2 (ModO2 B) := by
  obtain ⟨Z, hZn, hpc, -, hq⟩ := hD.pCore_data
  have hN : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpc) hq

theorem L34Row.card_modO2 (hD : L34Row B) : Nat.card (ModO2 B) = 20160 :=
  card_L34 hD.isPSL_modO2

theorem L34Row.odd_normal (hD : L34Row B) {N : Subgroup ↥B} (hN : N.Normal)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  have := hN
  obtain ⟨Z, hZn, -, hZc, hq⟩ := hD.pCore_data
  have hs : IsSimpleGroup (↥B ⧸ Z) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hq).2
  have hNn : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · have hle : N ≤ Z := by
      have := (Subgroup.map_eq_bot_iff _).mp h
      rwa [QuotientGroup.ker_mk'] at this
    have h1 : Nat.card ↥N ∣ Nat.card ↥Z := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥N = 1 := by
      obtain ⟨k, hk⟩ := hodd
      rcases hZc with hz | hz
      · rw [hz] at h1
        exact Nat.dvd_one.mp h1
      · rw [hz] at h1
        have := Nat.le_of_dvd (by norm_num) h1
        omega
    exact Subgroup.eq_bot_of_card_eq _ h2
  · exfalso
    have hdvd : Nat.card (↥B ⧸ Z) ∣ Nat.card ↥N := by
      have h1 : Nat.card ↥(N.map (QuotientGroup.mk' Z)) ∣ Nat.card ↥N :=
        Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) N)
      rwa [h, Subgroup.card_top] at h1
    rw [card_L34 hq] at hdvd
    obtain ⟨k, hk⟩ := hodd
    omega

theorem L34Row.false_of_ext [Finite Q] (hD : L34Row B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, 2 ≤ k ∧ Nat.card V = 2 ^ k) : False := by
  obtain ⟨V, hVn, hPV', -⟩ := h
  obtain ⟨k, hk2, hk⟩ := hPV _ hPV'
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card hk
  have hle : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hV2⟩
  have h1 : Nat.card ↥V ≤ Nat.card ↥(CFSG.pCore 2 ↥B) := Subgroup.card_le_of_le hle
  have h2 := hD.card_pCore_le
  rw [hk] at h1
  have h3 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  omega

end Simple

section Rows

variable {Q : Type} [Group Q] {B L : Subgroup Q}

theorem L34Row.false_C2 (hD : L34Row B) (h : A312C2 B L) : False := by
  obtain ⟨⟨m, hm⟩, -⟩ := h
  exact false_of_isPSL_two_two hm hD.card_modO2

theorem L34Row.false_C3 (hD : L34Row B) (h : A312C3 B L) : False := by
  obtain ⟨f, hf, -⟩ := h
  exact false_of_isSz hf hD.card_modO2

theorem L34Row.false_C4 (hD : L34Row B) (h : A312C4 B L) : False := by
  have h1 := card_L32 h.1
  have h2 := hD.card_modO2
  omega

theorem L34Row.false_C5 (hD : L34Row B) (h : A312C5 B L) : False :=
  false_of_isPSL_three_two_two_of_isPSL_four_two_one hD.isPSL_modO2 h.1

theorem L34Row.false_C6 (hD : L34Row B) (h : A312C6 B L) : False := by
  have hc := hD.card_cases
  obtain ⟨hB | hB, -⟩ := h
  · have := card_alt5 hB
    omega
  · have := card_L32 hB
    omega

theorem L34Row.false_C7 (hD : L34Row B) (h : A312C7 B L) : False := by
  have hc := hD.card_cases
  rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
  · have := card_alt6 hB
    omega
  · have := card_hat6 hB
    omega

theorem L34Row.false_C8 (hD : L34Row B) (h : A312C8 B L) : False := by
  have hc := hD.card_cases
  rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    exact no_sl2_card (p := p) (by omega)
  · have := card_alt5 hB
    omega

theorem L34Row.false_C9 (hD : L34Row B) (h : A312C9 B L) : False := by
  have hc := hD.card_cases
  rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · have h2 := card_of_isSL2 hp hB
    exact no_sl2_card (p := p) (by omega)
  · have := card_alt6 hB
    omega
  · have := card_hat6 hB
    omega

theorem L34Row.false_C10 (hD : L34Row B) (h : A312C10 B L) : False := by
  obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card ↥V = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod p) = p ^ 2
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hodd : Odd (Nat.card ↥V) := by
    rw [hcard]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hbot := hD.odd_normal hV hodd
  rw [hbot, Subgroup.card_bot] at hcard
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

theorem L34Row.false_C11 (hD : L34Row B) (h : A312C11 B L) : False := by
  have hc := hD.card_cases
  have := card_alt6 h.1
  omega

theorem L34Row.false_C12 [Finite Q] (hD : L34Row B) (h : A312C12 B L) : False := by
  rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
  · exact hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))

theorem L34Row.of_C13 [Finite Q] (hD : L34Row B) (h : A312C13 B L) :
    IsPSL 3 2 2 ↥B ∧ IsSporadic .M23 ↥L := by
  obtain ⟨hB, hL⟩ := h
  refine ⟨?_, hL⟩
  rcases hB with hB | hB | hB | hB | hB | hB | hB
  · exfalso
    obtain ⟨e⟩ := hB
    have h11 : 11 ∣ Nat.card ↥B := by
      rw [Nat.card_congr e.toEquiv]
      exact eleven_dvd_card_M22
    have hc := hD.card_cases
    omega
  · exact hB
  · exact (hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))).elim
  · exact (hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))).elim
  · exact (hD.false_of_ext hB (isE2_pGroup (m := 3) (by norm_num))).elim
  · exact (hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))).elim
  · exact (hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))).elim

theorem L34Row.false_C14 [Finite Q] (hD : L34Row B) (h : A312C14 B L) : False := by
  obtain ⟨hB | hB | hB | hB, -⟩ := h
  · exact hD.false_of_ext hB (isE2_pGroup (m := 4) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 6) (by norm_num))
  · exact hD.false_of_ext hB (isExtraspecial2_pGroup (m := 3) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 6) (by norm_num))

theorem L34Row.false_C15 (hD : L34Row B) (h : A312C15 B L) : False := by
  have hc := hD.card_cases
  have := card_alt5 h.1
  omega

theorem L34Row.false_C16 [Finite Q] (hD : L34Row B) (h : A312C16 B L) : False :=
  hD.false_of_ext h.1 (isExtraspecial2_pGroup (m := 2) (by norm_num))

theorem L34Row.false_C17 [Finite Q] (hD : L34Row B) (h : A312C17 B L) : False := by
  have h3 := hD.card_modO2
  obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
  · exact hD.false_of_ext hB (isExtraspecial2_pGroup (m := 6) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 11) (by norm_num))
  · have := card_alt5 hB
    omega
  · have := card_hat6 hB
    omega
  · exact false_of_isPSL_three_two_two_of_isPSL_four_two_one hD.isPSL_modO2 hB
  · have := card_L32 hB
    omega

theorem L34Row.false_C18 [Finite Q] (hD : L34Row B) (h : A312C18 B L) : False := by
  obtain ⟨hB | hB, -⟩ := h
  · exact hD.false_of_ext hB isZ4StarExtra2_pGroup
  · exact hD.false_of_ext hB isZ4Cubed_pGroup

theorem L34Row.false_C19 [Finite Q] (hD : L34Row B) (h : A312C19 B L) : False := by
  obtain ⟨hB | hB, -⟩ := h
  · exact hD.false_of_ext hB (isExtraspecial2_pGroup (m := 3) (by norm_num))
  · exact hD.false_of_ext hB (isE2_pGroup (m := 6) (by norm_num))

theorem L34Row.false_C20 (hD : L34Row B) (h : A312C20 B L) : False := by
  have h3 := hD.card_modO2
  obtain ⟨hB | hB, -⟩ := h
  · have := card_alt5 hB
    omega
  · have := card_L32 hB
    omega

private theorem relIndex_sup_eq_of_le_normalizer {A D : Subgroup Q}
    (h : A ≤ Subgroup.normalizer (D : Set Q)) : D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

theorem L34Row.card_sup_eq (hD : L34Row B) {O : Subgroup Q}
    (hBO : B ≤ Subgroup.normalizer (O : Set Q)) (hO : Odd (Nat.card ↥O)) :
    Nat.card ↥(B ⊔ O) = Nat.card ↥B * Nat.card ↥O := by
  have hN : (O.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBO hb, Subgroup.le_normalizer hb⟩
  have hc : Nat.card ↥(O.subgroupOf B) = Nat.card ↥(O ⊓ B) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hodd : Odd (Nat.card ↥(O.subgroupOf B)) := by
    rw [hc]
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := hD.odd_normal hN hodd
  have hOB : O ⊓ B = ⊥ := by
    rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  have h2 := Subgroup.relIndex_mul_card O B
  rw [hOB, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card O (B ⊔ O)
  rw [relIndex_sup_eq_of_le_normalizer hBO, h2, inf_eq_left.mpr le_sup_right] at h3
  exact h3.symm

theorem L34Row.false_of_nonquasi [Finite Q] (hD : L34Row B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    False := by
  have hc := hD.card_cases
  have hOLL : (CFSG.oddCore ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hLO :
      L ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup Q) : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOLL).mp ?_
    have he : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [he]
    infer_instance
  have hOcard : Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) = Nat.card ↥(CFSG.oddCore ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hOodd : Odd (Nat.card ↥((CFSG.oddCore ↥L).map L.subtype)) := by
    rw [hOcard]
    exact A37.odd_card_oddCore _
  have h1 := hD.card_sup_eq (hBL.trans hLO) hOodd
  have hpos : 0 < Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := Nat.card_pos
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  · rw [← hLB] at h1
    have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    have hB : Nat.card ↥B = p * (p ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    exact no_sl2_card (p := p) (by omega)
  · have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hB : Nat.card ↥B = 5 * (5 ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    omega

end Rows

theorem row_l34_case {Q : Type} [Group Q] [Finite Q] {B B' : Subgroup Q}
    (hD : L34Row B) (_hBB' : B ≤ B') (h : A312Case B B') : IsPSL 3 2 2 ↥B ∧ IsSporadic .M23 ↥B' := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.false_C2 h).elim
  · exact (hD.false_C3 h).elim
  · exact (hD.false_C4 h).elim
  · exact (hD.false_C5 h).elim
  · exact (hD.false_C6 h).elim
  · exact (hD.false_C7 h).elim
  · exact (hD.false_C8 h).elim
  · exact (hD.false_C9 h).elim
  · exact (hD.false_C10 h).elim
  · exact (hD.false_C11 h).elim
  · exact (hD.false_C12 h).elim
  · exact hD.of_C13 h
  · exact (hD.false_C14 h).elim
  · exact (hD.false_C15 h).elim
  · exact (hD.false_C16 h).elim
  · exact (hD.false_C17 h).elim
  · exact (hD.false_C18 h).elim
  · exact (hD.false_C19 h).elim
  · exact (hD.false_C20 h).elim

theorem row_l34_nonquasi {Q : Type} [Group Q] [Finite Q] {B B' : Subgroup Q}
    (hD : L34Row B) (hBB' : B ≤ B') (h : A312Nonquasi B B') : False :=
  hD.false_of_nonquasi hBB' h

section Image

theorem l34Row_range {L Q : Type} [Group L] [Finite L] [Group Q] (φ : L →* Q)
    (hperf : Group.IsPerfect L) (hZ : Nat.card ↥(Subgroup.center L) = 4)
    (hmod : IsPSL 3 2 2 (L ⧸ Subgroup.center L))
    (hker : φ.ker ≤ Subgroup.center L) (hker2 : 2 ≤ Nat.card ↥φ.ker) : L34Row φ.range := by
  have := hperf
  have hLcard : Nat.card L = 80640 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
    rw [card_L34 hmod, hZ] at h1
    omega
  have hKdvd : Nat.card ↥φ.ker ∣ 4 := hZ ▸ Subgroup.card_dvd_of_le hker
  have hK : Nat.card ↥φ.ker = 2 ∨ Nat.card ↥φ.ker = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hKdvd
    generalize Nat.card ↥φ.ker = k at hKdvd hker2 hle ⊢
    interval_cases k <;> omega
  have hBK := Subgroup.card_ker_mul_card_range φ
  refine ⟨Group.IsPerfect.range φ, ?_⟩
  rcases hK with hK | hK
  ·
    right
    have hBc : Nat.card ↥φ.range = 40320 := by
      rw [hK, hLcard] at hBK
      omega
    obtain ⟨ψ, hψ, hψker⟩ : ∃ ψ : L →* ↥φ.range, Function.Surjective ψ ∧ ψ.ker = φ.ker :=
      ⟨φ.rangeRestrict, φ.rangeRestrict_surjective, φ.ker_rangeRestrict⟩
    have hZ'n : ((Subgroup.center L).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hθ : Function.Surjective ((QuotientGroup.mk' ((Subgroup.center L).map ψ)).comp ψ) :=
      (QuotientGroup.mk'_surjective _).comp hψ
    have hθker : ((QuotientGroup.mk' ((Subgroup.center L).map ψ)).comp ψ).ker = Subgroup.center L := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have h1 : z⁻¹ * x ∈ φ.ker := by
          rw [← hψker, MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
        have h2 : z * (z⁻¹ * x) ∈ Subgroup.center L := Subgroup.mul_mem _ hz (hker h1)
        simpa using h2
      · intro hx
        exact ⟨x, hx, rfl⟩
    have e : (↥φ.range ⧸ (Subgroup.center L).map ψ) ≃* (L ⧸ Subgroup.center L) :=
      (QuotientGroup.quotientKerEquivOfSurjective _ hθ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hθker)
    have hq : IsPSL 3 2 2 (↥φ.range ⧸ (Subgroup.center L).map ψ) :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod
    have hZ'c : Nat.card ↥((Subgroup.center L).map ψ) = 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Subgroup.center L).map ψ)
      rw [card_L34 hq, hBc] at h1
      omega
    have hZ'z : (Subgroup.center L).map ψ ≤ Subgroup.center ↥φ.range := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨l, rfl⟩ := hψ b
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    exact ⟨hBc, (Subgroup.center L).map ψ, hZ'n, hZ'z, hZ'c, hq⟩
  ·
    left
    have hKZ : φ.ker = Subgroup.center L := Subgroup.eq_of_le_of_card_ge hker (by omega)
    have e : ↥φ.range ≃* (L ⧸ Subgroup.center L) :=
      (QuotientGroup.quotientKerEquivRange φ).symm.trans (QuotientGroup.quotientMulEquivOfEq hKZ)
    have hpsl : IsPSL 3 2 2 ↥φ.range := CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod
    exact ⟨card_L34 hpsl, (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hpsl).2, hpsl⟩

private theorem mem_pCore_iff {X : Type} [Group X] {H : Subgroup X} (y : ↥H) :
    y ∈ CFSG.pCore 2 ↥H ↔ (y : X) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff y).symm

theorem l34Row_modO2Image {X : Type} [Group X] [Finite X] {H L : Subgroup X} (hLH : L ≤ H)
    (hperf : Group.IsPerfect ↥L) (hZ : Nat.card ↥(Subgroup.center ↥L) = 4)
    (hmod : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L))
    (hker : (L ⊓ pCoreOf 2 H).subgroupOf L ≤ Subgroup.center ↥L)
    (hker2 : 2 ≤ Nat.card ↥(L ⊓ pCoreOf 2 H)) : L34Row (modO2Image H L) := by
  have hN : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  let φ : ↥L →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)
  have hrange : φ.range = modO2Image H L := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hφker : φ.ker = (L ⊓ pCoreOf 2 H).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_pCore_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard : Nat.card ↥φ.ker = Nat.card ↥(L ⊓ pCoreOf 2 H) := by
    rw [hφker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hrange]
  exact l34Row_range φ hperf hZ hmod (by rw [hφker]; exact hker) (by rw [hcard]; exact hker2)

end Image

end CFSG.Quasithin.SBd17

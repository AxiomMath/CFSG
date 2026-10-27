module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem527
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Swap

variable {X : Type} [Group X]

@[expose] noncomputable def ofSubgroupsIsoSwap {Y : Type} [Group Y] {A B : Subgroup X}
    {M₁ M₂ : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    (RankTwoAmalgam.ofSubgroups B A).Iso (RankTwoAmalgam.ofSubgroups M₂ M₁) where
  φ1 := e.φ2
  φ12 := (MulEquiv.subgroupCongr (inf_comm B A)).trans
    (e.φ12.trans (MulEquiv.subgroupCongr (inf_comm M₁ M₂)))
  φ2 := e.φ1
  comm1 g := by
    have h := e.comm2 (MulEquiv.subgroupCongr (inf_comm B A) g)
    exact Subtype.ext (congrArg Subtype.val h)
  comm2 g := by
    have h := e.comm1 (MulEquiv.subgroupCongr (inf_comm B A) g)
    exact Subtype.ext (congrArg Subtype.val h)

theorem IsYAmalgamPair.swap {Y : Type} [Group Y] {T M₁ M₂ : Subgroup Y}
    (h : IsYAmalgamPair T M₁ M₂) : IsYAmalgamPair T M₂ M₁ :=
  ⟨h.1, h.2.1.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem isYAmalgam_ofSubgroups_swap {Y : Type} [Group Y] {A B : Subgroup X} {T : Subgroup Y}
    (h : IsYAmalgam (RankTwoAmalgam.ofSubgroups A B) T) :
    IsYAmalgam (RankTwoAmalgam.ofSubgroups B A) T := by
  obtain ⟨M₁, M₂, hp, ⟨e⟩⟩ := h
  exact ⟨M₂, M₁, IsYAmalgamPair.swap hp, ⟨ofSubgroupsIsoSwap e⟩⟩

theorem isAmalgamOfGroup_ofSubgroups_swap {A B : Subgroup X} {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups A B) P) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups B A) P := by
  obtain ⟨Y, _, hP, T, hT⟩ := h
  exact ⟨Y, inferInstance, hP, T, isYAmalgam_ofSubgroups_swap hT⟩

theorem isU4ExtTwo_ofSubgroups_swap {A B : Subgroup X} {f : ℕ}
    (h : IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups A B)) :
    IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups B A) := by
  obtain ⟨Y, _, Ŷ, _, ι, hY, hι, hidx, T, hT⟩ := h
  exact ⟨Y, inferInstance, Ŷ, inferInstance, ι, hY, hι, hidx, T, isYAmalgam_ofSubgroups_swap hT⟩

end Swap

theorem IsAmalgamOfGroup.mono {α : RankTwoAmalgam.{0}} {P Q : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup α P) (hPQ : ∀ (Y : Type) [Group Y], P Y → Q Y) :
    IsAmalgamOfGroup α Q := by
  obtain ⟨Y, _, hP, T, hT⟩ := h
  exact ⟨Y, inferInstance, hPQ Y hP, T, hT⟩

theorem two_pow_mul_four_pow_sub_one_lt {a b : ℕ} (hab : a < b) :
    2 ^ a * (4 ^ a - 1) < 2 ^ b * (4 ^ b - 1) := by
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : 4 ^ a < 4 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h3 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  calc 2 ^ a * (4 ^ a - 1) ≤ 2 ^ a * (4 ^ b - 1) := Nat.mul_le_mul_left _ (by omega)
    _ < 2 ^ b * (4 ^ b - 1) := Nat.mul_lt_mul_of_pos_right h1 (by omega)

theorem eq_of_two_pow_mul_four_pow_sub_one_eq {a b : ℕ}
    (h : 2 ^ a * (4 ^ a - 1) = 2 ^ b * (4 ^ b - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (two_pow_mul_four_pow_sub_one_lt hab).ne
  · exact hab
  · exact absurd h (two_pow_mul_four_pow_sub_one_lt hab).ne'

theorem IsL2Quot.of_mulEquiv {f : ℕ} {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : IsL2Quot f X) : IsL2Quot f X' := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem eq_of_isL2Quot {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {X : Type*} [Group X]
    (h₁ : IsL2Quot a X) (h₂ : IsL2Quot b X) : a = b :=
  eq_of_two_pow_mul_four_pow_sub_one_eq ((h₁.card ha).symm.trans (h₂.card hb))

variable {G : Type} [Group G]

theorem isL2Quot_oTwoQuot_of_lieModel {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) : IsL2Quot n (oTwoQuot ↥L) :=
  IsL2Quot.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L))
    (isL2Quot_of_lieModel hn h)

theorem card_oTwoQuot_of_isLin2Type {L : Subgroup G} {f : ℕ} (h : IsLin2Type L f) :
    Nat.card (oTwoQuot ↥L) = 2 ^ f * (4 ^ f - 1) := by
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := h
  have e : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [hker])).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two,
    Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm f 2, pow_mul]
  norm_num

theorem card_sz_mod_three (a : ℕ) : Nat.card (Sz a) % 3 = 2 := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  set q := 2 ^ (2 * a + 1) with hq
  have hq3 : q % 3 = 2 := by
    rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rw [hk, show 3 * k + 2 - 1 = 3 * k + 1 by omega]
  have e : (3 * k + 2) ^ 2 * ((3 * k + 2) ^ 2 + 1) * (3 * k + 1) =
      3 * (81 * k ^ 5 + 243 * k ^ 4 + 297 * k ^ 3 + 183 * k ^ 2 + 56 * k + 6) + 2 := by ring
  rw [e]
  omega

theorem three_dvd_card_of_isL2Quot' {n : ℕ} (hn : 1 ≤ n) {X : Type*} [Group X]
    (h : IsL2Quot n X) : 3 ∣ Nat.card X := by
  rw [h.card hn]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : 4 ^ n % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem not_mulEquiv_sz_of_isL2Quot {n a : ℕ} (hn : 1 ≤ n)
    {X : Type*} [Group X] (h : IsL2Quot n X) (e : X ≃* ↥(Sz a)) : False := by
  have h3 := three_dvd_card_of_isL2Quot' hn h
  rw [Nat.card_congr e.toEquiv] at h3
  have := card_sz_mod_three a
  omega

theorem charP_two_of_card_sixteen {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4 ^ 2) :
    CharP F 2 := by
  classical
  have := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h0
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  have h4 : ((2 : ℕ) : F) ^ 4 = 0 := by
    rw [← Nat.cast_pow]
    exact h0
  exact pow_eq_zero_iff (by norm_num) |>.mp h4

theorem not_mulEquiv_su34_of_isL2Quot {n : ℕ} (hn : 1 ≤ n) {X : Type*} [Group X]
    (h : IsL2Quot n X) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4 ^ 2)
    (e : X ≃* ↥(CFSG.Open.StatedSU 3 4 F)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_sixteen hF
  have hF' : Nat.card F = (2 ^ 2) ^ 2 := by rw [hF]; norm_num
  have hSU := CFSG.SectionRank.OddCover.card_statedSU_three (p := 2) (f := 2) hF'
  have hEq : CFSG.Open.StatedSU 3 4 F = CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 2) F := rfl
  have hX := h.card hn
  rw [Nat.card_congr (e.trans (MulEquiv.subgroupCongr hEq)).toEquiv, hSU] at hX
  norm_num at hX
  have hlt : n < 7 := by
    by_contra hge
    have := two_pow_mul_four_pow_sub_one_lt (show 6 < n by omega)
    norm_num at this
    omega
  interval_cases n <;> norm_num at hX

theorem pCoreOf_sup_of_odd [Finite G] {L X : Subgroup G}
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hX : Odd (Nat.card X)) :
    pCoreOf 2 (L ⊔ X) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ⊔ X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hXL
  obtain ⟨P, hP, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ L)
    (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup G))
  have hodd : ¬ 2 ∣ L.relIndex (L ⊔ X) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hX (relIndex_sup_dvd_card_of_le_normalizer hXL)))
      (even_iff_two_dvd.mpr h2)
  have hPLX : IsSylowTwoOf P (L ⊔ X) := by
    refine F7.isSylowTwoOf_of_relIndex (hP.1.trans le_sup_left) hP.2.1 fun h2 => ?_
    rw [← Subgroup.relIndex_mul_relIndex P L (L ⊔ X) hP.1 le_sup_left] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hP.2.2 (by rwa [Subgroup.relIndex] at h)
    · exact hodd h
  apply le_antisymm
  · have hOL : pCoreOf 2 (L ⊔ X) ≤ L := (F7.isSylowTwoOf_pCoreOf_le hPLX).trans hP.1
    exact le_pCoreOf_of_le_normalizer 2 hOL (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (hLN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

end CFSG.Quasithin.H13

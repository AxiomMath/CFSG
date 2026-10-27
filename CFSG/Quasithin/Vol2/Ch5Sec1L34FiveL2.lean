module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveRed
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513 CFSG.GorensteinWalter
open scoped Pointwise

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

theorem quot_psl2_of_isPSL {X : Type} [Group X] {p f : ℕ} (h : IsPSL 2 p f X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Subgroup.center X = ⊥ ∧ Nonempty (X ⧸ Subgroup.center X ≃* PSL2 K) := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
  let e₁ : X ≃* PSL2 K :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  obtain ⟨hZ, he⟩ := nonempty_quotCenter_equiv e₁ (psl2_center_eq_bot K)
  exact ⟨K, inferInstance, inferInstance, hK, hZ, he⟩

variable {Y : Type} [Group Y] [Finite Y] {L T D B : Subgroup Y}

theorem le_normalizer_of_psl2_prime
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (h5 : p ^ 2 % 5 = 1) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* PSL2 K) (hZ : Subgroup.center ↥L = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hD : Nat.card D = 5)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hBL : B ≤ L)
    (hB : ⁅B, B⁆ = B) (hA5 : IsAlt 5 ↥B) (hTB : IsSylowTwoOf (T ⊓ B) B) {b : Y} (hbB : b ∈ B)
    (hb3 : orderOf b = 3) (hbT : b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y))
    (hbD : ∀ d ∈ D, d * b = b * d) : D ≤ Subgroup.normalizer (B : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp11 := eleven_le hp h5 h8
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have hcen := psl2_center_eq_bot K
  have hinn : FiveInner (PSL2 K) := fiveInner_of_oddInner
    (inner_of_odd_psl2 hodd (ringAut_mul_self hp le_rfl (by norm_num) (by rw [hK, pow_one])))
  rcases eq_one_or_card_iPart e hcen hinn hD hDN with h1 | ⟨hinn', hD₁⟩
  · exact le_normalizer_of_pImg L e hBL hB hDN fun d hd y hy => by
      rw [h1 d hd, MulAut.one_apply]
      exact hy
  have hsyl := isSylowTwoOf_pImg e hT hTN
  have hmax : ∀ X : Subgroup (PSL2 K), IsPGroup 2 X → pImg L e (T ⊓ L) ≤ X →
      X = pImg L e (T ⊓ L) := fun X hX hle =>
    le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2 X le_top hX hle) hle
  have hperm := inner_perm L e hTN hDN hDT hT.2.1 hinn' (conj_injective_of_center hcen) hmax
  have hinj : Function.Injective (toP L e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toP, hZ]
  obtain ⟨u, hu, hPu, -⟩ := psl2_card_four_mul hp hK h8
  have hTL4 : Nat.card ↥(T ⊓ L) ≤ 4 := by
    have h1 := card_le_four_of_isPGroup hu hPu _ (isPGroup_pImg L e inf_le_right hT.2.1.to_inf_left)
    rwa [pImg, Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
  have hB60 : Nat.card ↥B = 2 ^ 2 * 15 := by
    obtain ⟨eB⟩ := hA5
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hTB4 : Nat.card ↥(T ⊓ B) = 2 ^ 2 := by
    have h4 := card_eq_of_isSylowTwoOf_top
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hTB) hB60 (by decide)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h4
  have hTLB : T ⊓ L = T ⊓ B :=
    (Subgroup.eq_of_le_of_card_ge (inf_le_inf_left T hBL) (by rw [hTB4]; exact hTL4)).symm
  obtain ⟨eA⟩ := hA5
  obtain ⟨eL⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  let eR : ↥(pImg L e B) ≃* L24 :=
    ((Subgroup.equivMapOfInjective (B.subgroupOf L) (toP L e) hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hBL)).trans (eA.trans eL.symm)
  have hb3' : orderOf (toP L e ⟨b, hBL hbB⟩) = 3 := by
    rw [orderOf_injective (toP L e) hinj, Subgroup.orderOf_mk, hb3]
  have hbD' : toP L e ⟨b, hBL hbB⟩ ∈ Subgroup.normalizer (iPart L e D : Set (PSL2 K)) :=
    mem_normalizer_of_commute fun x hx => toP_commute_iPart e hcen (hBL hbB) hbD hx
  have hbT' : toP L e ⟨b, hBL hbB⟩ ∈
      Subgroup.normalizer (pImg L e (T ⊓ L) : Set (PSL2 K)) := by
    rw [hTLB]
    exact toP_mem_normalizer_pImg e (inf_le_right.trans hBL) (hBL hbB) hbT
  have hTR : pImg L e (T ⊓ L) ≤ pImg L e B := by
    rw [hTLB]
    exact pImg_mono L e inf_le_right
  obtain ⟨hT2, hTi⟩ := isSylowTwoOf_top_index hsyl
  have hcore := core_psl2_prime_le hK h8 hp11 (hT2.toSylow hTi) (isCyclic_of_prime_card hD₁)
    (by rw [hD₁]; decide) hperm eR hTR (toP_mem_pImg L e (hBL hbB) hbB) hb3' hbD' hbT'
  exact le_normalizer_of_iPart_le e hBL hB hDN hinn' fun x hx =>
    Subgroup.le_normalizer (hcore hx).1

theorem le_normalizer_of_psl2_25 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ 2) (e : ↥L ⧸ Subgroup.center ↥L ≃* PSL2 K)
    (hZ : Subgroup.center ↥L = ⊥) (hT : IsSylowTwoOf T ⊤)
    (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hD : Nat.card D = 5)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hBL : B ≤ L)
    (hB : ⁅B, B⁆ = B) {b : Y} (hbL : b ∈ L) (hb3 : orderOf b = 3)
    (hbD : ∀ d ∈ D, d * b = b * d) : D ≤ Subgroup.normalizer (B : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK⟩
  have hcen := psl2_center_eq_bot K
  have hinn : FiveInner (PSL2 K) := fiveInner_of_oddInner
    (inner_of_odd_psl2 hodd (ringAut_mul_self (by norm_num) (by norm_num) le_rfl hK))
  rcases eq_one_or_card_iPart e hcen hinn hD hDN with h1 | ⟨hinn', hD₁⟩
  · exact le_normalizer_of_pImg L e hBL hB hDN fun d hd y hy => by
      rw [h1 d hd, MulAut.one_apply]
      exact hy
  exfalso
  have hsyl := isSylowTwoOf_pImg e hT hTN
  have hmax : ∀ X : Subgroup (PSL2 K), IsPGroup 2 X → pImg L e (T ⊓ L) ≤ X →
      X = pImg L e (T ⊓ L) := fun X hX hle =>
    le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2 X le_top hX hle) hle
  have hperm := inner_perm L e hTN hDN hDT hT.2.1 hinn' (conj_injective_of_center hcen) hmax
  have hinj : Function.Injective (toP L e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toP, hZ]
  obtain ⟨hT2, hTi⟩ := isSylowTwoOf_top_index hsyl
  have hb3' : orderOf (toP L e ⟨b, hbL⟩) = 3 := by
    rw [orderOf_injective (toP L e) hinj, Subgroup.orderOf_mk, hb3]
  have hB3 : Nat.card (Subgroup.zpowers (toP L e ⟨b, hbL⟩)) = 3 := by
    rw [Nat.card_zpowers, hb3']
  have hBD : Subgroup.zpowers (toP L e ⟨b, hbL⟩) ≤
      Subgroup.normalizer (iPart L e D : Set (PSL2 K)) :=
    Subgroup.zpowers_le.mpr
      (mem_normalizer_of_commute fun x hx => toP_commute_iPart e hcen hbL hbD hx)
  have hle := core_psl2_25 hK (hT2.toSylow hTi) (isCyclic_of_prime_card hD₁)
    (by rw [hD₁]; decide) hperm hB3 hBD
  have h1 := Subgroup.card_dvd_of_le hle
  rw [hD₁, hB3] at h1
  norm_num at h1

end CFSG.Quasithin.H13.FiveNorm

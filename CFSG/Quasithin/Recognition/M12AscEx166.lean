module

public import CFSG.Quasithin.Recognition.M12AscEx166B
public import CFSG.Quasithin.Recognition.M12AscEx166A
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open Subgroup CFSG.GorensteinWalter

variable {X : Type} [Group X] [Finite X] {V : Subgroup X} {z y : X}

namespace KleinCore

omit [Finite X] in
theorem card_involutions_alt :
    Nat.card {a : alternatingGroup (Fin 4) // a * a = 1 ∧ a ≠ 1} = 3 ∧
      Nat.card {a : alternatingGroup (Fin 5) // a * a = 1 ∧ a ≠ 1} = 15 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

omit [Finite X] in
theorem card_involutions_equiv {G A : Type*} [Group G] [Group A] (e : G ≃* A) :
    Nat.card {x : G // x * x = 1 ∧ x ≠ 1} = Nat.card {a : A // a * a = 1 ∧ a ≠ 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv (fun x => by
    have h1 : e x * e x = 1 ↔ x * x = 1 := by
      rw [← map_mul]
      exact map_eq_one_iff e e.injective
    have h2 : e x = 1 ↔ x = 1 := map_eq_one_iff e e.injective
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ne_eq, h1, h2]))

theorem linear_branch
    (h : KleinCore (⊤ : Subgroup X) V z y) {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {L : Subgroup X} [L.Normal] (hL : Odd L.index)
    (hLm : Nonempty (↥L ≃* PSL2 F) ∨ Nonempty (↥L ≃* PGL2 F)) :
    Nonempty (X ≃* alternatingGroup (Fin 4)) ∨ Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  rcases hLm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  swap
  · exact (h.not_pgl2 hF e).elim
  rcases h.card_field_le_five hF e with hq | hq
  ·
    left
    have : Fintype F := Fintype.ofFinite F
    let eF : ZMod 3 ≃+* F :=
      ZMod.ringEquivOfPrime F Nat.prime_three (by rw [← Nat.card_eq_fintype_card]; exact hq)
    let eL : ↥L ≃* alternatingGroup (Fin 4) :=
      e.trans ((psl2RingEquiv eF).symm.trans psl2_three_equiv_alternatingGroup)
    have hcard : Nat.card L = 4 * 3 := by
      rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hinv : Nat.card {x : ↥L // x * x = 1 ∧ x ≠ 1} ≤ 3 := by
      rw [card_involutions_equiv eL, card_involutions_alt.1]
    have htop : L = ⊤ := h.eq_top_of_involution_count hL 3 hcard hinv
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eL⟩
  ·
    right
    have h60 : Nat.card (PSL2 F) = 60 := by
      rw [psl2_card_formula F hF, hq]
      norm_num
    have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hq]; norm_num)
    obtain ⟨eA⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h60
    let eL : ↥L ≃* alternatingGroup (Fin 5) := e.trans eA
    have hcard : Nat.card L = 4 * 15 := by
      rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hinv : Nat.card {x : ↥L // x * x = 1 ∧ x ≠ 1} ≤ 15 := by
      rw [card_involutions_equiv eL, card_involutions_alt.2]
    have htop : L = ⊤ := h.eq_top_of_involution_count hL 15 hcard hinv
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eL⟩

theorem exists_alt_equiv_top
    (h : KleinCore (⊤ : Subgroup X) V z y) :
    Nonempty (X ≃* alternatingGroup (Fin 4)) ∨ Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  have hdih := h.hasDihedralSylowTwo
  have hbot := h.pPrimeCore_eq_bot
  have hGW := GorensteinWalter.gorensteinWalter X hdih
  have e0 : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hy1 : y ≠ 1 := by
    intro e
    apply h.y_ne
    rw [e]
    group
  have hy3 : y ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h.y_cube
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  rcases hGW with ⟨hS, hP⟩ | ⟨hS, e7⟩ | ⟨hS, F, hF, L, hLn, hLi, hLm⟩
  ·
    exfalso
    have hP' : IsPGroup 2 X := IsPGroup.of_equiv hP e0
    obtain ⟨k, hk⟩ := hP' y
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [hyo] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  ·
    exfalso
    obtain ⟨e7'⟩ := e7
    have hX : Nat.card X = 2520 := by
      rw [Nat.card_congr (e0.symm.trans e7').toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup]
      decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 3)
      (by rw [hX]; norm_num)
    have hWp : IsPGroup 2 W := IsPGroup.of_card hW
    have := h.syl W le_top hWp
    rw [hW] at this
    omega
  ·
    have hL'n : (L.map e0.toMonoidHom).Normal := hLn.map e0.toMonoidHom e0.surjective
    have hL'i : Odd (L.map e0.toMonoidHom).index := by
      rw [Subgroup.index_map_of_bijective e0.bijective]
      exact hLi
    let eL : ↥L ≃* ↥(L.map e0.toMonoidHom) :=
      Subgroup.equivMapOfInjective L e0.toMonoidHom e0.injective
    have hLm' : Nonempty (↥(L.map e0.toMonoidHom) ≃* PSL2 F) ∨
        Nonempty (↥(L.map e0.toMonoidHom) ≃* PGL2 F) := by
      rcases hLm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact Or.inl ⟨eL.symm.trans e⟩
      · exact Or.inr ⟨eL.symm.trans e⟩
    exact h.linear_branch hF hL'i hLm'

end KleinCore

theorem exists_alt_equiv_of_kleinCore
    {I : Type} [Group I] [Finite I] {K V : Subgroup I} {z y : I}
    (h : KleinCore K V z y) :
    Nonempty (↥K ≃* ↥(alternatingGroup (Fin 4))) ∨ Nonempty (↥K ≃* ↥(alternatingGroup (Fin 5))) :=
  KleinCore.exists_alt_equiv_top h.toTop

end CFSG.Quasithin

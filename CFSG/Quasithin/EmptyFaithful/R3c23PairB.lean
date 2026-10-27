module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
import CFSG.Quasithin.Background.G64RealizeSec
import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Assembly.LowTwoRank

section Orders

private theorem pairB_card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

private theorem pairB_card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

private theorem pairB_card_statedSL_two_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥(StatedSL 2 F) = 2 ^ n * (2 ^ (2 * n) - 1) := by
  rw [pairB_card_statedSL_two, hF, pow_mul' 2 2 n]

private theorem pairB_card_statedSL_three_two {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) : Nat.card ↥(StatedSL 3 K) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two h

private theorem pairB_card_statedSL_three_ge {F : Type} [Field F] [Finite F] :
    168 ≤ Nat.card ↥(StatedSL 3 F) := by
  rw [pairB_card_statedSL_three]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hq ⊢
  have h2 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  calc 168 = 8 * (3 * 7) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

private theorem pairB_card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

end Orders

section Arith

private theorem pairB_two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have hu' : ¬ 2 ∣ u := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hu
  have hw' : ¬ 2 ∣ w := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hw
  have h1 : padicValNat 2 (2 ^ a * u) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hu.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu', add_zero]
  have h2 : padicValNat 2 (2 ^ b * w) = b := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hw.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw', add_zero]
  rw [← h1, ← h2, h]

private theorem pairB_odd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h odd_one

private theorem pairB_arith_psl2 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : 2 ^ n * (2 ^ (2 * n) - 1) = 2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) :
    False := by
  have hu : Odd (2 ^ (2 * n) - 1) := pairB_odd_two_pow_sub_one (by omega)
  have hw : Odd ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) :=
    (pairB_odd_two_pow_sub_one (by omega)).mul (pairB_odd_two_pow_sub_one (by omega))
  have hn3 : n = 3 * m := pairB_two_pow_mul_odd_inj hu hw h
  subst hn3
  have hpos : 0 < 2 ^ (3 * m) := by positivity
  have h2 : 2 ^ (2 * (3 * m)) - 1 = (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1) :=
    Nat.eq_of_mul_eq_mul_left hpos h
  have hx : 2 ^ (2 * (3 * m)) = 2 ^ (3 * m) * 2 ^ (3 * m) := by
    rw [← pow_add]; congr 1; omega
  have hxy : 2 ^ (2 * m) ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hx2 : 2 ≤ 2 ^ (3 * m) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  rw [hx] at h2
  generalize 2 ^ (3 * m) = x at *
  generalize 2 ^ (2 * m) = y at *
  have h3 : (y - 1) * (x - 1) ≤ (x - 1) * (x - 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hxy 1)
  have h4 : (x - 1) * (x - 1) < x * x - 1 := by
    obtain ⟨z, rfl⟩ : ∃ z, x = z + 2 := ⟨x - 2, by omega⟩
    have e1 : z + 2 - 1 = z + 1 := by omega
    have e2 : (z + 2) * (z + 2) - 1 = z * z + 4 * z + 3 := by
      have : (z + 2) * (z + 2) = z * z + 4 * z + 4 := by ring
      omega
    rw [e1, e2]
    nlinarith
  omega

private theorem pairB_two_pow_mul_ne (n : ℕ) :
    2 ^ n * (2 ^ (2 * n) - 1) ≠ 120 ∧ 2 ^ n * (2 ^ (2 * n) - 1) ≠ 168 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num
  · have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_mul' 2 2 n]
    generalize 2 ^ n = t at *
    have h256 : 256 ≤ t ^ 2 := by
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ t ^ 2 := Nat.pow_le_pow_left h16 2
    have h4080 : 16 * 255 ≤ t * (t ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)
    constructor <;> intro h' <;> omega

end Arith

section Realize

variable {V : Type} [CommGroup V]

private theorem pairB_card_eq_of_nat_realizes {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} (h : (FFModel.nat Γ).Realizes L U Z) : Nat.card ↥L = Nat.card ↥Γ := by
  obtain ⟨π, hπ⟩ := h
  exact (Nat.card_congr (Equiv.ofBijective π
    ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful Γ) hπ, hπ.1⟩)).symm

private theorem pairB_card_eq_of_perm_five {G : Subgroup (MulAut V)}
    (e : Nonempty (↥G ≃* Equiv.Perm (Fin 5))) : Nat.card ↥G = 120 := by
  obtain ⟨e⟩ := e
  rw [Nat.card_congr e.toEquiv]
  exact pairB_card_perm_five

private theorem pairB_card_of_lin2Cover {L : Type} [Group L] (hK : Lin2Cover L) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card L = 2 ^ n * (2 ^ (2 * n) - 1) := by
  obtain ⟨F, _, _, n, hn, hF, ⟨e⟩⟩ := hK
  exact ⟨n, hn, by rw [Nat.card_congr e.toEquiv]; exact pairB_card_statedSL_two_pow hF⟩

private theorem pairB_not_isPerfect_perm_five : ¬ Group.IsPerfect (Equiv.Perm (Fin 5)) := by
  intro h
  have h1 : commutator (Equiv.Perm (Fin 5)) ≤ alternatingGroup (Fin 5) :=
    alternatingGroup.commutator_perm_le
  rw [h.commutator_eq_top] at h1
  have h2 : Equiv.swap (0 : Fin 5) 1 ∈ alternatingGroup (Fin 5) := h1 (Subgroup.mem_top _)
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at h2
  exact absurd h2 (by decide)

end Realize

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

private theorem pairB_sym5_false_of_perfect [Group.IsPerfect ↥L] {U Z : Subgroup V}
    (h : SymmetricNatural L U Z 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful (by norm_num)) hπ
  have hP : Group.IsPerfect (FFModel.symDn 5).Gam :=
    Group.IsPerfect.ofSurjective
      (f := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm.toMonoidHom)
      (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm.surjective
  exact pairB_not_isPerfect_perm_five hP

private theorem pairB_lin2_false_of_sl3 (hK : Lin2Cover ↥L) {F : Type} [Field F] [Finite F]
    {m : ℕ} (hm : Nat.card F = 2 ^ m) {U Z : Subgroup V}
    (h : (FFModel.nat (StatedSL 3 F)).Realizes L U Z) : False := by
  obtain ⟨n, hn2, hn⟩ := pairB_card_of_lin2Cover hK
  have hm1 : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := F)
    rw [pow_zero] at hm
    omega
  have hLc : Nat.card ↥L = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
    rw [pairB_card_eq_of_nat_realizes h, pairB_card_statedSL_three, hm]
  refine pairB_arith_psl2 (m := m) (n := n) hm1 (by omega) ?_
  rw [← hn, hLc, pow_mul' 2 3 m, pow_mul' 2 2 m]

private theorem pairB_lin2_false_of_sl3_two (hK : Lin2Cover ↥L)
    (e : Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2)))) : False := by
  obtain ⟨n, -, hn⟩ := pairB_card_of_lin2Cover hK
  obtain ⟨e⟩ := e
  have h1 : Nat.card ↥L = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact pairB_card_statedSL_three_two (Nat.card_zmod 2)
  exact (pairB_two_pow_mul_ne n).2 (hn.symm.trans h1)

theorem pairB_piece_of_self {W C : Subgroup V} (hperf : Group.IsPerfect ↥L) (hK : Lin2Cover ↥L)
    (h : B56Piece L W C) : W = commV L ⊔ C ∧ ∃ m, BinaryNaturalSL L W C 2 m := by
  rcases h with ⟨hW, h⟩ | ⟨-, m, F, hF, hFin, hm, hd⟩ | ⟨e, -, -, -, -⟩
  · refine ⟨hW, ?_⟩
    rcases h with ⟨n, hn⟩ | hS | ⟨m, F, hF, hFin, hm, hR⟩
    · exact ⟨n, hn⟩
    · exact (pairB_sym5_false_of_perfect hS).elim
    · exact (pairB_lin2_false_of_sl3 hK hm hR).elim
  · obtain ⟨I, π, -, -, -, hreal⟩ := hd
    exact (pairB_lin2_false_of_sl3 hK hm ⟨π, hreal ⟨0, by norm_num⟩⟩).elim
  · exact (pairB_lin2_false_of_sl3_two hK e).elim

theorem pairB_piece_of_sym {W C : Subgroup V} {G : Subgroup (MulAut V)}
    (e : Nonempty (↥G ≃* Equiv.Perm (Fin 5))) (h : B56Piece G W C) :
    W = commV G ⊔ C ∧ SymmetricNatural G W C 5 := by
  have h120 := pairB_card_eq_of_perm_five e
  rcases h with ⟨hW, h⟩ | ⟨-, m, F, hF, hFin, hm, hd⟩ | ⟨e', -, -, -, -⟩
  · refine ⟨hW, ?_⟩
    rcases h with ⟨n, F, hF, hFin, hn, hR⟩ | hS | ⟨m, F, hF, hFin, hm, hR⟩
    · exfalso
      refine (pairB_two_pow_mul_ne n).1 ?_
      rw [← pairB_card_statedSL_two_pow hn, ← pairB_card_eq_of_nat_realizes hR]
      exact h120
    · exact hS
    · exfalso
      have h1 := pairB_card_eq_of_nat_realizes hR
      have h2 := pairB_card_statedSL_three_ge (F := F)
      omega
  · exfalso
    obtain ⟨I, π, -, -, -, hreal⟩ := hd
    have h1 := pairB_card_eq_of_nat_realizes
      (⟨π, hreal ⟨0, by norm_num⟩⟩ : (FFModel.nat (StatedSL 3 F)).Realizes G (I 0) C)
    have h2 := pairB_card_statedSL_three_ge (F := F)
    omega
  · exfalso
    obtain ⟨e'⟩ := e'
    have h1 : Nat.card ↥G = 168 := by
      rw [Nat.card_congr e'.toEquiv]
      exact pairB_card_statedSL_three_two (Nat.card_zmod 2)
    omega

end Excl

structure PairBPiece {V : Type} [CommGroup V] (L G : Subgroup (MulAut V)) (W C : Subgroup V) :
    Prop where
  eq_comm : W = commV G ⊔ C
  natCount : NatCount G W C
  le : C ≤ W
  ne : ∃ w ∈ W, w ∉ C
  free : ∀ w ∈ W, (∀ l ∈ L, l w * w⁻¹ ∈ C) → w ∈ C
  gen : W ≤ commMod L W ⊔ C

theorem pairB_pieceFacts {V : Type} [CommGroup V] [Finite V] (h₁ : SL2PieceFacts)
    (h₂ : Sym5PieceFacts) {L G : Subgroup (MulAut V)} {W C : Subgroup V}
    (hperf : Group.IsPerfect ↥L) (hK : Lin2Cover ↥L) (hLG : L ≤ G)
    (hG : G = L ∨ (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L = 60))
    (h : B56Piece G W C) : PairBPiece L G W C := by
  rcases hG with rfl | ⟨e, h60⟩
  · obtain ⟨hW, m, hm⟩ := pairB_piece_of_self hperf hK h
    obtain ⟨hN, hCW, hne, hfree, hgen⟩ := h₁ V _ W C m hm
    exact ⟨hW, hN, hCW, hne, hfree, hgen⟩
  · obtain ⟨hW, hS⟩ := pairB_piece_of_sym e h
    obtain ⟨hN, hCW, hne, hfree, hgen⟩ := h₂ V G L W C hS hLG h60
    exact ⟨hW, hN, hCW, hne, hfree, hgen⟩

end R3c23

end CFSG.Quasithin

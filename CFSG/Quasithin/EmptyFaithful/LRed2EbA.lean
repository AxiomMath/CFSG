module

public import CFSG.Quasithin.EmptyFaithful.R3cSL2
public import CFSG.Quasithin.Background.FFC4Small1

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

private theorem lred2_det_eq_one {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ StatedSL n K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem lred2_card_L {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (hL : Nonempty (↥L ≃* ↥(StatedSL 2 K))) :
    Nat.card ↥L = 2 ^ e * (4 ^ e - 1) := by
  obtain ⟨f⟩ := hL
  rw [Nat.card_congr f.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_two_pow hK]

private theorem lred2_odd_four_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (4 ^ e - 1) := by
  have h : 4 ^ e = 2 ^ (2 * e) := by rw [pow_mul]; norm_num
  rw [h]
  exact CFSG.Quasithin.Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega)

theorem lred2_false_sl3 {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {K : Type} [Field K] [Finite K] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (hL : Nonempty (↥L ≃* ↥(StatedSL 2 K))) {K' : Type} [Field K'] [Finite K'] {n : ℕ}
    (hK' : Nat.card K' = 2 ^ n) {π : ↥(StatedSL 3 K') →* ↥L}
    (hπ : (FFModel.nat (StatedSL 3 K')).RealizesVia L U Z π) : False := by
  have hn : 1 ≤ n := FFC.one_le_of_card_field hK'
  have hcard : Nat.card ↥(StatedSL 3 K') = Nat.card ↥L :=
    Nat.card_congr (MulEquiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩).toEquiv
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL, CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_three_pow hK',
    lred2_card_L hK hL] at hcard
  have hodd1 : Odd ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
    (CFSG.Quasithin.Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega)).mul
      (CFSG.Quasithin.Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega))
  obtain ⟨he3, heq⟩ := CFSG.Quasithin.Vol2.Ch10.SecA.two_pow_mul_odd_inj hodd1
    (lred2_odd_four_pow_sub_one (by omega)) hcard
  subst he3
  have h1 := CFSG.Quasithin.Vol2.Ch10.SecA.mul_two_pow_sub_one_lt (3 * n) (2 * n)
  have h2 : 4 ^ (3 * n) = 2 ^ (6 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  have h3 : 2 ^ (6 * n) = 2 ^ (3 * n + 2 * n) * 2 ^ n := by rw [← pow_add]; ring_nf
  have h4 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h5 : 1 ≤ 2 ^ (3 * n + 2 * n) := Nat.one_le_two_pow
  rw [h2, h3] at heq
  have hab : 2 * 2 ^ (3 * n + 2 * n) ≤ 2 ^ (3 * n + 2 * n) * 2 ^ n := by nlinarith
  generalize 2 ^ (3 * n + 2 * n) * 2 ^ n = ab at heq hab
  generalize 2 ^ (3 * n + 2 * n) = a at h1 h5 hab
  omega

theorem lred2_not_threeRank2_sl2 {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
    {e : ℕ} (hK : Nat.card K = 2 ^ e) (hL : Nonempty (↥L ≃* ↥(StatedSL 2 K))) :
    ¬ FFC.ThreeRank2 ↥L := by
  intro h
  obtain ⟨f⟩ := hL
  have h1 : FFC.ThreeRank2 ↥(StatedSL 2 K) := h.of_injective f.toMonoidHom f.injective
  have h2 := h1.pRank_two_le
  have h3 := R3c.pRank_three_le_one_of_noElemNine (R3c.noElemNine_statedSL_two hK)
  omega

theorem lred2_fixed_zero {K : Type} [Field K] [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 1) (h3 : A * A * A = 1) (hA : A ≠ 1) (v : Fin 2 → K)
    (hv : A.mulVec v = v) : v = 0 := by
  by_contra hv0
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hsing : (A - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, by rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet hsing
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff,
    not_false_eq_true, sub_zero, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one] at hsing
  apply hA
  have had : A 1 1 = - A 0 0 := by linear_combination hdet - hsing + h2
  have hbc : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    have : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := hdet
    rw [had] at this
    linear_combination -this - h2
  have hA2 : A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, had] <;>
      first | ring1 | linear_combination hbc
  have := congrArg (fun M => A * M) hA2
  simp only [mul_one] at this
  rw [← mul_assoc, h3] at this
  exact this.symm

theorem lred2_natural_fixed {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z π)
    {y : MulAut V} (hyL : y ∈ L) (hy3 : orderOf y = 3) {u : V} (hu : u ∈ U) (hyu : y u = u) :
    u ∈ Z := by
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 2 K), π γ = ⟨y, hyL⟩ := hπ.1 ⟨y, hyL⟩
  have hγy : ((π γ : ↥L) : MulAut V) = y := congrArg Subtype.val hγ
  have hγ3 : γ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hγ, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show y ^ 3 = 1
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hγ1 : γ ≠ 1 := by
    intro h
    rw [h, map_one] at hγ
    have : y = 1 := (congrArg Subtype.val hγ).symm
    rw [this, orderOf_one] at hy3
    omega
  obtain ⟨-, -, -, hHU, -, hsec, -, β, -, hβk, hβe⟩ := hπ
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
  have hu' : ((π γ : ↥L) : MulAut V) u ∈ U := hHU (π γ) u hu
  have hact : (FFModel.nat (StatedSL 2 K)).act γ (m : (FFModel.nat (StatedSL 2 K)).Amb) ∈
      (FFModel.nat (StatedSL 2 K)).sec := hsec γ m m.2
  have h1 := hβe γ ⟨u, hu⟩ m hu' hact hm.symm
  have hsub : (⟨((π γ : ↥L) : MulAut V) u, hu'⟩ : ↥U) = ⟨u, hu⟩ :=
    Subtype.ext (show ((π γ : ↥L) : MulAut V) u = u by rw [hγy]; exact hyu)
  have h1' : β ⟨u, hu⟩ = QuotientGroup.mk ⟨(FFModel.nat (StatedSL 2 K)).act γ
      (m : (FFModel.nat (StatedSL 2 K)).Amb), hact⟩ := (congrArg β hsub).symm.trans h1
  have h3 := QuotientGroup.eq.mp (hm.trans h1')
  have h4 := Subgroup.mem_subgroupOf.mp h3
  have h4' : ((m : (FFModel.nat (StatedSL 2 K)).Amb))⁻¹ *
      (FFModel.nat (StatedSL 2 K)).act γ (m : (FFModel.nat (StatedSL 2 K)).Amb) = 1 :=
    Subgroup.mem_bot.mp h4
  have h5 : natAct (StatedSL 2 K) γ (m.1 : Multiplicative (Fin 2 → K)) = (m.1 : Multiplicative (Fin 2 → K)) :=
    inv_mul_eq_one.mp h4' |>.symm
  have h6 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd (m.1 : Multiplicative (Fin 2 → K))) =
      Multiplicative.toAdd (m.1 : Multiplicative (Fin 2 → K)) := congrArg Multiplicative.toAdd h5
  have hdet := lred2_det_eq_one γ.2
  have hA3 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun g : ↥(StatedSL 2 K) => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hγ3
    simpa [pow_succ] using this
  have hA1 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    hγ1 (Subtype.ext (Units.ext (by simpa using h)))
  have h7 := lred2_fixed_zero _ hdet hA3 hA1 _ h6
  have hm1 : (m.1 : Multiplicative (Fin 2 → K)) = 1 :=
    Multiplicative.toAdd.injective (h7.trans (toAdd_one (α := Fin 2 → K)).symm)
  have hβ1 : β ⟨u, hu⟩ = 1 := by
    rw [← hm]
    have : m = 1 := Subtype.ext hm1
    rw [this]
    rfl
  exact (hβk ⟨u, hu⟩).mp hβ1

end CFSG.Quasithin

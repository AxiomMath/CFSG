module

public import CFSG.Quasithin.Background.F918Z4c1Sz
public import CFSG.Quasithin.SteinbergBSEvenExponentPrimitive
public import CFSG.Timmesfeld.Orders.BangGL
public import CFSG.Quasithin.H13.QRCFourFamilyBounds
public import CFSG.ClassicalInvolution.AschTight.E3OddAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped commutatorElement

theorem three_not_dvd_card_of_isSz' {S : Type} [Group S] {n : ℕ}
    (hS : CFSG.Quasithin.IsSz n S) : ¬ 3 ∣ Nat.card S := by
  have hcard := CFSG.Quasithin.card_of_isSz hS
  obtain ⟨-, a, ha, K, -, -, hf, hK, ⟨e⟩⟩ := hS
  subst hf
  rw [hcard]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    CFSG.RankThree.PartTwo.KFacts.KP7.not_three_dvd_order a

theorem not_dvd_card_isSz_gl_two {S : Type} [Group S] {n d : ℕ} (hn : 3 ≤ n)
    (hS : CFSG.Quasithin.IsSz n S) (hd : d ≤ 7) :
    ¬ Nat.card S ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  obtain ⟨ℓ, hℓ, hℓ2, hord, hℓdvd⟩ :=
    CFSG.Quasithin.SteinbergBS.qrc_binary_even_exponent_primitive_divisor.1 (4 * n)
      (by omega) ⟨2 * n, by ring⟩ (by omega)
  have hℓS : ℓ ∣ Nat.card S := by
    rw [CFSG.Quasithin.card_of_isSz hS]
    have h1 : ℓ ∣ (2 ^ n) ^ 2 + 1 := by
      have hpow : 2 ^ (4 * n / 2) = (2 ^ n) ^ 2 := by
        rw [show 4 * n / 2 = n * 2 by omega, pow_mul]
      rwa [hpow] at hℓdvd
    have h2 := h1.mul_right ((2 ^ n) ^ 2 * (2 ^ n - 1))
    simpa [mul_assoc] using h2
  intro h
  have hℓGL : ℓ ∣ Nat.card (GL (Fin d) (ZMod 2)) := hℓS.trans h
  apply CFSG.Timmesfeld.Bang.not_dvd_card_GL_of_orderOf_two_eq_mul
    (K := ZMod 2) (b := 1) (c := 4 * n) (k := d) (by norm_num) (by norm_num)
    hℓ (by simpa using hord) (by omega) hℓGL

@[expose] noncomputable def criticalKernelFixing (Q : Type) [Group Q] : Subgroup (MulAut Q) :=
  ((CFSG.ClassicalInvolution.Disconnected.AschTight.centerQuotientAut Q).ker :
      Subgroup (MulAut Q)) ⊓
    fixingSubgroup (MulAut Q) (Subgroup.center Q : Set Q)

theorem isPGroup_criticalKernelFixing {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) :
    IsPGroup p ↥(criticalKernelFixing Q) := by
  classical
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rw [IsPGroup.iff_orderOf]
  intro α
  have hmem := α.2
  have hαker : CFSG.ClassicalInvolution.Disconnected.AschTight.centerQuotientAut Q α.1 = 1 :=
    MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hmem).1
  have hαfix : α.1 ∈ fixingSubgroup (MulAut Q) (Subgroup.center Q : Set Q) :=
    (Subgroup.mem_inf.mp hmem).2
  have hfix : ∀ z ∈ Subgroup.center Q, α.1 z = z := by
    intro z hz
    exact (mem_fixingSubgroup_iff _).1 hαfix z hz
  have hdisp : ∀ x : Q, α.1 x * x⁻¹ ∈ Subgroup.center Q := by
    intro x
    have h1 := congrArg (fun f : MulAut (Q ⧸ Subgroup.center Q) => f (QuotientGroup.mk x)) hαker
    rw [CFSG.ClassicalInvolution.Disconnected.AschTight.centerQuotientAut_mk] at h1
    simp only [MulAut.one_apply] at h1
    have hz : (α.1 x)⁻¹ * x ∈ Subgroup.center Q := QuotientGroup.eq.mp h1
    have hz' : x⁻¹ * α.1 x ∈ Subgroup.center Q := by
      have := Subgroup.inv_mem _ hz
      simpa [mul_inv_rev, inv_inv] using this
    have heq : α.1 x * x⁻¹ = x⁻¹ * α.1 x := by
      calc α.1 x * x⁻¹ = x * (x⁻¹ * α.1 x) * x⁻¹ := by group
        _ = (x⁻¹ * α.1 x) * x * x⁻¹ := by rw [Subgroup.mem_center_iff.mp hz' x]
        _ = x⁻¹ * α.1 x := by group
    rwa [heq]
  have hpow : ∀ (m : ℕ) (x : Q), (α.1 ^ m) x = (α.1 x * x⁻¹) ^ m * x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix _ (hdisp x), pow_succ,
        mul_assoc, inv_mul_cancel_right]
  have hpowcard : α.1 ^ Nat.card Q = 1 := by
    apply MulEquiv.ext
    intro x
    rw [hpow]
    have hz : (α.1 x * x⁻¹) ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hz, one_mul]
    rfl
  have hpow' : α ^ Nat.card Q = 1 := by
    apply Subtype.ext
    exact hpowcard
  have hdvd : orderOf α ∣ Nat.card Q := orderOf_dvd_of_pow_eq_one hpow'
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact ⟨j, hj⟩

theorem eq_one_of_isSz_card_not_dvd {H S A : Type} [Group H] [Finite H] [Group S]
    [Group A] {n : ℕ} {π : H →* S} (hπ : Function.Surjective π)
    (hmin : ∀ K : Subgroup H, K.map π = ⊤ → K = ⊤)
    (hS : CFSG.Quasithin.IsSz n S) (φ : H →* MulAut A)
    (hcard : ¬ Nat.card S ∣ Nat.card (MulAut A)) : φ = 1 := by
  classical
  have : Finite S := CFSG.LieType.Simplicity.fam_suzuki_finiteness S 2 n hS
  have : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_2b2_simplicity S 2 n hS).2
  by_contra hφ
  have hkerne : φ.ker ≠ ⊤ := by
    intro h
    exact hφ (MonoidHom.ker_eq_top_iff.mp h)
  have hNnormal : (φ.ker.map π).Normal := (inferInstance : φ.ker.Normal).map π hπ
  have : (φ.ker.map π).Normal := hNnormal
  have hNbot_or_top : φ.ker.map π = ⊥ ∨ φ.ker.map π = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map π)
  have hNbot : φ.ker.map π = ⊥ := by
    rcases hNbot_or_top with h | h
    · exact h
    · exact absurd (hmin _ h) hkerne
  have hKN : φ.ker ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hNbot
  have hidx : π.ker.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hKN
  have hSidx : Nat.card S = π.ker.index := by
    rw [Subgroup.index_ker π, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top]
  have hXidx : Nat.card φ.range = φ.ker.index := by
    rw [Subgroup.index_ker φ]
  have hdvd : Nat.card S ∣ Nat.card φ.range := by
    rw [hSidx, hXidx]
    exact hidx
  exact hcard (hdvd.trans (Subgroup.card_subgroup_dvd_card φ.range))


private theorem not_dvd_two_pow_mul_odd {a k m : ℕ} (hm : Odd m) (hk : k < a) :
    ¬ 2 ^ a ∣ 2 ^ k * m := by
  intro h
  have := CFSG.Quasithin.H13.QRC.le_of_two_pow_dvd hm h
  omega


private theorem not_dvd_two_pow_card_GL {p d n K M : ℕ}
    (hfac : Nat.card (GL (Fin d) (ZMod p)) = 2 ^ K * M) (hM : Odd M) (hK : K < 2 * n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin d) (ZMod p)) := by
  rw [hfac]
  exact not_dvd_two_pow_mul_odd hM hK

private theorem not_dvd_two_pow_GL_five_two {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin 2) (ZMod 5)) := by
  apply not_dvd_two_pow_card_GL (K := 5) (M := 15)
  · rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  · norm_num
  · omega

private theorem not_dvd_two_pow_GL_five_three {n : ℕ} (hn : 4 ≤ n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin 3) (ZMod 5)) := by
  apply not_dvd_two_pow_card_GL (K := 7) (M := 11625)
  · rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
    norm_num
  · norm_num
  · omega

private theorem not_dvd_two_pow_GL_seven_two {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin 2) (ZMod 7)) := by
  apply not_dvd_two_pow_card_GL (K := 5) (M := 63)
  · rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  · norm_num
  · omega

private theorem not_dvd_two_pow_GL_eleven_two {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin 2) (ZMod 11)) := by
  apply not_dvd_two_pow_card_GL (K := 4) (M := 825)
  · rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  · norm_num
  · omega

private theorem not_dvd_two_pow_GL_thirteen_two {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ (2 * n) ∣ Nat.card (GL (Fin 2) (ZMod 13)) := by
  apply not_dvd_two_pow_card_GL (K := 5) (M := 819)
  · rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  · norm_num
  · omega

theorem not_dvd_card_isSz_gl_odd {S : Type} [Group S] {n p d : ℕ} (hn : 3 ≤ n)
    (hS : CFSG.Quasithin.IsSz n S) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hd2 : 2 ≤ d) (hpd : p ^ d ≤ 169) :
    ¬ Nat.card S ∣ Nat.card (GL (Fin d) (ZMod p)) := by
  have hp5 : 5 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    have hp3le : 3 ≤ p := by
      by_contra h
      have : p = 2 := by omega
      exact hp2 this
    have hp4le : 4 ≤ p := by
      by_contra h
      have : p = 3 := by omega
      exact hp3 this
    by_contra h
    have : p = 4 := by omega
    subst this
    norm_num at hp
  have hp13 : p ≤ 13 := by
    have h2 : p ^ 2 ≤ p ^ d := Nat.pow_le_pow_right (by omega) hd2
    have h3 : p ^ 2 ≤ 13 ^ 2 := by
      calc p ^ 2 ≤ p ^ d := h2
        _ ≤ 169 := hpd
        _ = 13 ^ 2 := by norm_num
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp h3
  have hd3 : d ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ d := by omega
    have h1 : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp5 4
    have h2 : p ^ 4 ≤ p ^ d := Nat.pow_le_pow_right (by omega) h4
    have h3 : 5 ^ 4 ≤ 169 := h1.trans (h2.trans hpd)
    norm_num at h3
  intro h
  have h2S : 2 ^ (2 * n) ∣ Nat.card S := by
    rw [CFSG.Quasithin.card_of_isSz hS]
    have h1 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      calc (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul]
        _ = 2 ^ (2 * n) := by rw [mul_comm]
    rw [← h1]
    have h2 : (2 ^ n) ^ 2 ∣ ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 :=
      dvd_mul_of_dvd_right (dvd_refl ((2 ^ n) ^ 2)) ((2 ^ n) ^ 2 + 1)
    have h3 : (2 ^ n) ^ 2 ∣ ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
      simp [mul_assoc, mul_comm]
    exact h3
  have h2GL : 2 ^ (2 * n) ∣ Nat.card (GL (Fin d) (ZMod p)) := h2S.trans h
  by_cases hspecial : p = 5 ∧ d = 3 ∧ n = 3
  · obtain ⟨rfl, rfl, rfl⟩ := hspecial
    have hcard : Nat.card S = 29120 := by
      simpa using CFSG.Quasithin.card_of_isSz hS
    rw [hcard] at h
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    rw [Matrix.card_GL_field] at h
    norm_num [Fin.prod_univ_three, ZMod.card] at h
  · have h2GL : 2 ^ (2 * n) ∣ Nat.card (GL (Fin d) (ZMod p)) := h2S.trans h
    interval_cases d
    · interval_cases p
      all_goals norm_num at hp
      all_goals first
        | exact (not_dvd_two_pow_GL_five_two hn) h2GL
        | exact (not_dvd_two_pow_GL_seven_two hn) h2GL
        | exact (not_dvd_two_pow_GL_eleven_two hn) h2GL
        | exact (not_dvd_two_pow_GL_thirteen_two hn) h2GL
    · have hp_eq : p = 5 := by
        by_contra hne
        have h6 : 6 ≤ p := by omega
        have h1 : 6 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h6 3
        have h2 : p ^ 3 ≤ 169 := hpd
        norm_num at h1
        omega
      subst hp_eq
      have hn4 : 4 ≤ n := by
        by_contra hlt
        have hn3 : n = 3 := by omega
        exact hspecial ⟨rfl, rfl, hn3⟩
      exact (not_dvd_two_pow_GL_five_three hn4) h2GL

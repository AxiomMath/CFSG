module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofCase3
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped Pointwise

namespace Proof1413

variable {G : Type} [Group G]

theorem exists_conj_of_mem_wStar {A : Subgroup G} {τ : MulAut ↥A} (hτ : τ ∈ wStar A) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), ∀ a : ↥A, ((τ a : ↥A) : G) = w * a * w⁻¹ := by
  obtain ⟨h, hN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  exact ⟨h, hN, fun a => Sec4.normalizerMonoidHom_apply_coe hN a⟩

theorem normalizerMonoidHom_mem_wStar {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) : A.normalizerMonoidHom ⟨x, hx⟩ ∈ wStar A :=
  Sec4.mem_autIn_iff.mpr ⟨x, hx, Subgroup.mem_top x, rfl⟩

theorem oThreeWStar_le (A : Subgroup G) : oThreeWStar A ≤ wStar A :=
  Subgroup.map_subtype_le _

theorem conj_mem_oThreeWStar {A : Subgroup G} {σ τ : MulAut ↥A} (hσ : σ ∈ wStar A)
    (hτ : τ ∈ oThreeWStar A) : σ * τ * σ⁻¹ ∈ oThreeWStar A := by
  obtain ⟨τ', hτ', rfl⟩ := hτ
  have hN : (CFSG.pCore 3 ↥(wStar A)).Normal := CFSG.pCore_normal
  exact ⟨⟨σ, hσ⟩ * τ' * ⟨σ, hσ⟩⁻¹, hN.conj_mem τ' hτ' ⟨σ, hσ⟩, rfl⟩

variable [Finite G]

theorem fixes_of_irreducible {A B X : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hBW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn X B))
    (hP9 : Nat.card (oThreeWStar A) = 9) :
    ∀ τ ∈ oThreeWStar A, ∀ (b : G) (hb : b ∈ B), ((τ ⟨b, hBA hb⟩ : ↥A) : G) = b := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinv : ∀ τ ∈ oThreeWStar A, ∀ b (hb : b ∈ B), ((τ ⟨b, hBA hb⟩ : ↥A) : G) ∈ B := by
    intro τ hτ b hb
    obtain ⟨w, hw, hwτ⟩ := exists_conj_of_mem_wStar (oThreeWStar_le A hτ)
    rw [hwτ]
    exact (Subgroup.mem_normalizer_iff.mp (hBW hw) b).mp hb
  let C : Subgroup ↥B :=
    { carrier := {b | ∀ τ ∈ oThreeWStar A, ((τ ⟨(b : G), hBA b.2⟩ : ↥A) : G) = b}
      mul_mem' := by
        intro x y hx hy τ hτ
        have h := map_mul τ ⟨(x : G), hBA x.2⟩ ⟨(y : G), hBA y.2⟩
        have h' : ((τ ⟨((x * y : ↥B) : G), hBA (x * y).2⟩ : ↥A) : G) =
            ((τ ⟨(x : G), hBA x.2⟩ : ↥A) : G) * ((τ ⟨(y : G), hBA y.2⟩ : ↥A) : G) :=
          congrArg Subtype.val h
        rw [h', hx τ hτ, hy τ hτ]
        rfl
      one_mem' := by
        intro τ _
        have h := map_one τ
        exact congrArg Subtype.val h
      inv_mem' := by
        intro x hx τ hτ
        have h := map_inv τ ⟨(x : G), hBA x.2⟩
        have h' : ((τ ⟨((x⁻¹ : ↥B) : G), hBA x⁻¹.2⟩ : ↥A) : G) =
            ((τ ⟨(x : G), hBA x.2⟩ : ↥A) : G)⁻¹ := congrArg Subtype.val h
        rw [h', hx τ hτ]
        rfl }
  have hmemC : ∀ b : ↥B, b ∈ C ↔ ∀ τ ∈ oThreeWStar A, ((τ ⟨(b : G), hBA b.2⟩ : ↥A) : G) = b :=
    fun b => Iff.rfl
  have hPp : IsPGroup 3 ↥(oThreeWStar A) := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  let _ : MulAction ↥(oThreeWStar A) ↥B :=
    { smul := fun τ b => ⟨((τ : MulAut ↥A) ⟨(b : G), hBA b.2⟩ : G), hinv τ τ.2 b b.2⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have hmod := hPp.card_modEq_card_fixedPoints ↥B
  have hfix0 : Nat.card (MulAction.fixedPoints ↥(oThreeWStar A) ↥B) ≡ 0 [MOD 3] := by
    refine hmod.symm.trans ?_
    rw [hB9]
    rfl
  have h1 : (1 : ↥B) ∈ MulAction.fixedPoints ↥(oThreeWStar A) ↥B := by
    intro τ
    apply Subtype.ext
    show (((τ : MulAut ↥A) 1 : ↥A) : G) = 1
    rw [map_one]
    rfl
  have hcard : 1 < Nat.card (MulAction.fixedPoints ↥(oThreeWStar A) ↥B) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥(oThreeWStar A) ↥B) :=
      Nat.card_pos_iff.mpr ⟨⟨1, h1⟩, inferInstance⟩
    have h3 : 3 ∣ Nat.card (MulAction.fixedPoints ↥(oThreeWStar A) ↥B) :=
      (Nat.modEq_zero_iff_dvd).mp hfix0
    have := Nat.le_of_dvd hpos h3
    omega
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ : ∃ x : MulAction.fixedPoints ↥(oThreeWStar A) ↥B,
      x ≠ ⟨1, h1⟩ := by
    have : Nontrivial (MulAction.fixedPoints ↥(oThreeWStar A) ↥B) :=
      Finite.one_lt_card_iff_nontrivial.mp hcard
    exact exists_ne _
  have hb₀C : b₀ ∈ C := by
    intro τ hτ
    exact congrArg Subtype.val (hb₀ ⟨τ, hτ⟩)
  have hC0 : C ≠ ⊥ := by
    intro h0
    apply hb₀1
    have : b₀ = 1 := by
      have := hb₀C
      rw [h0, Subgroup.mem_bot] at this
      exact this
    exact Subtype.ext this
  have hstep : ∀ x (hxX : x ∈ X) (hxN : x ∈ Subgroup.normalizer (B : Set G)), ∀ b ∈ C,
      B.normalizerMonoidHom ⟨x, hxN⟩ b ∈ C := by
    intro x hxX hxN b hb τ hτ
    have hxA := hXA hxX
    set σ := A.normalizerMonoidHom ⟨x, hxA⟩ with hσ
    have hσW : σ ∈ wStar A := normalizerMonoidHom_mem_wStar hxA
    have hτ' : σ⁻¹ * τ * σ⁻¹⁻¹ ∈ oThreeWStar A := conj_mem_oThreeWStar (inv_mem hσW) hτ
    rw [inv_inv] at hτ'
    have hfixb := hb _ hτ'
    have hxb : (⟨((B.normalizerMonoidHom ⟨x, hxN⟩ b : ↥B) : G),
        hBA (B.normalizerMonoidHom ⟨x, hxN⟩ b).2⟩ : ↥A) = σ ⟨(b : G), hBA b.2⟩ := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe hxN, hσ, Sec4.normalizerMonoidHom_apply_coe hxA]
    have hfix' : (σ⁻¹ * τ * σ) ⟨(b : G), hBA b.2⟩ = ⟨(b : G), hBA b.2⟩ := Subtype.ext hfixb
    have key : τ (σ ⟨(b : G), hBA b.2⟩) = σ ⟨(b : G), hBA b.2⟩ := by
      have h2 := congrArg σ hfix'
      simp only [MulAut.mul_apply, MulAut.apply_inv_self] at h2
      exact h2
    show ((τ ⟨((B.normalizerMonoidHom ⟨x, hxN⟩ b : ↥B) : G), _⟩ : ↥A) : G) =
      ((B.normalizerMonoidHom ⟨x, hxN⟩ b : ↥B) : G)
    rw [hxb, key, ← hxb]
  have hCinv : ∀ φ ∈ Sec4.autIn X B, C.map φ.toMonoidHom = C := by
    intro φ hφ
    obtain ⟨x, hxN, hxX, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hstep x hxX hxN b hb
    · intro b hb
      have hxN' : x⁻¹ ∈ Subgroup.normalizer (B : Set G) := inv_mem hxN
      refine ⟨B.normalizerMonoidHom ⟨x⁻¹, hxN'⟩ b, hstep x⁻¹ (inv_mem hxX) hxN' b hb, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom]
      rw [Sec4.normalizerMonoidHom_apply_coe hxN, Sec4.normalizerMonoidHom_apply_coe hxN']
      group
  rcases hirr C hCinv with h | h
  · exact absurd h hC0
  · intro τ hτ b hb
    have hbC : (⟨b, hb⟩ : ↥B) ∈ C := h ▸ Subgroup.mem_top _
    exact hbC τ hτ

theorem exists_transvection {A B X : Subgroup G} (hA : IsE27 A) {c : G} (hcA : c ∈ A)
    (hcB : c ∉ B) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hBW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn X B))
    (hPe : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (hP9 : Nat.card (oThreeWStar A) = 9) :
    ∀ d ∈ B, ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∀ b ∈ B, w * b * w⁻¹ = b) ∧ w * c * w⁻¹ = c * d := by
  have hfix := fixes_of_irreducible hBA hB9 hBW hXA hirr hP9
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hc3 : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA3 c hcA) (fun h1 => hcB (h1 ▸ one_mem B))
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hAc x ((Subgroup.zpowers_le.mpr hcA) hx) y (hBA hy)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hdisj : Subgroup.zpowers c ⊓ B = ⊥ := by
    rw [inf_comm]
    exact Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcB
  rw [hdisj, Subgroup.card_bot, mul_one, hB9, Nat.card_zpowers, hc3] at hcard
  have hAeq : A = Subgroup.zpowers c ⊔ B :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA) hBA)
      (by rw [hcard, hA.2])).symm
  have hdec : ∀ a ∈ A, ∃ k : ℕ, ∃ b ∈ B, a = c ^ k * b := by
    intro a ha
    rw [hAeq] at ha
    have ha' : a ∈ ((Subgroup.zpowers c : Set G) * (B : Set G)) := by
      rw [← hset]
      exact ha
    obtain ⟨z, hz, b, hb, rfl⟩ := ha'
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    exact ⟨k, b, hb, rfl⟩
  have hext : ∀ τ ∈ oThreeWStar A, ∀ σ ∈ oThreeWStar A,
      ((τ ⟨c, hcA⟩ : ↥A) : G) = ((σ ⟨c, hcA⟩ : ↥A) : G) → τ = σ := by
    intro τ hτ σ hσ hτσ
    ext ⟨a, ha⟩
    obtain ⟨k, b, hb, rfl⟩ := hdec a ha
    have hsplit : (⟨c ^ k * b, ha⟩ : ↥A) = ⟨c, hcA⟩ ^ k * ⟨b, hBA hb⟩ := Subtype.ext (by simp)
    rw [hsplit, map_mul, map_mul, map_pow, map_pow]
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    rw [hτσ, hfix τ hτ b hb, hfix σ hσ b hb]
  have hcoset : ∀ τ ∈ oThreeWStar A, ((τ ⟨c, hcA⟩ : ↥A) : G) * c⁻¹ ∈ B := by
    intro τ hτ
    obtain ⟨k, b', hb', hk⟩ := hdec _ (τ ⟨c, hcA⟩).2
    have hk3 : c ^ k = c ^ (k % 3) := by
      conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hA3 c hcA, one_pow, mul_one]
    rw [hk3] at hk
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hkm : k % 3
    ·
      exfalso
      rw [pow_zero, one_mul] at hk
      have h2 : τ ⟨c, hcA⟩ = τ ⟨b', hBA hb'⟩ := Subtype.ext (by rw [hk, hfix τ hτ b' hb'])
      have h3 : c = b' := congrArg Subtype.val (τ.injective h2)
      rw [h3] at hcB
      exact hcB hb'
    · rw [pow_one] at hk
      rw [hk, show c * b' * c⁻¹ = b' by rw [hAc c hcA b' (hBA hb')]; group]
      exact hb'
    ·
      exfalso
      have hτ2 : τ * τ = 1 := by
        refine hext (τ * τ) (mul_mem hτ hτ) 1 (one_mem _) ?_
        simp only [MulAut.mul_apply, MulAut.one_apply]
        have hc2 : (⟨c ^ 2 * b', by rw [← hk]; exact (τ ⟨c, hcA⟩).2⟩ : ↥A) = τ ⟨c, hcA⟩ :=
          Subtype.ext hk.symm
        rw [← hc2]
        have hsplit : (⟨c ^ 2 * b', by rw [← hk]; exact (τ ⟨c, hcA⟩).2⟩ : ↥A) =
            ⟨c, hcA⟩ ^ 2 * ⟨b', hBA hb'⟩ := Subtype.ext (by simp)
        rw [hsplit, map_mul, map_pow]
        simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
        rw [← hc2, hfix τ hτ b' hb']
        simp only
        have hcb : Commute (c ^ 2) b' :=
          (show Commute c b' from hAc c hcA b' (hBA hb')).pow_left 2
        rw [hcb.mul_pow, ← pow_mul, mul_assoc, ← pow_succ, show 2 * 2 = 3 + 1 by norm_num,
          pow_add, hA3 c hcA, one_mul, pow_one, show 2 + 1 = 3 by norm_num, hA3 b' (hBA hb'),
          mul_one]
      have hτ3 : τ ^ 3 = 1 := hPe.2 τ hτ
      have hτ1 : τ = 1 := by
        rw [pow_succ, pow_two, hτ2, one_mul] at hτ3
        exact hτ3
      rw [hτ1, MulAut.one_apply] at hk
      apply hcB
      have : b' = c⁻¹ := by
        have h1 : c = c ^ 2 * b' := hk
        calc b' = (c ^ 2)⁻¹ * (c ^ 2 * b') := by group
          _ = (c ^ 2)⁻¹ * c := by rw [← h1]
          _ = c⁻¹ := by group
      rw [← inv_inv c, ← this]
      exact inv_mem hb'
  let Φ : ↥(oThreeWStar A) → ↥B := fun τ => ⟨((τ.1 ⟨c, hcA⟩ : ↥A) : G) * c⁻¹, hcoset τ.1 τ.2⟩
  have hΦ : Function.Injective Φ := by
    intro τ σ hτσ
    have h := congrArg Subtype.val hτσ
    simp only [Φ, mul_left_inj] at h
    exact Subtype.ext (hext τ.1 τ.2 σ.1 σ.2 h)
  have hΦs : Function.Surjective Φ :=
    (hΦ.bijective_of_nat_card_le (by rw [hP9, hB9])).2
  intro d hd
  obtain ⟨τ, hτd⟩ := hΦs ⟨d, hd⟩
  have hτc : ((τ.1 ⟨c, hcA⟩ : ↥A) : G) = c * d := by
    have h := congrArg Subtype.val hτd
    simp only [Φ] at h
    rw [show c * d = d * c from (hAc c hcA d (hBA hd)), ← h]
    group
  obtain ⟨w, hw, hwτ⟩ := exists_conj_of_mem_wStar (oThreeWStar_le A τ.2)
  refine ⟨w, hw, fun b hb => ?_, ?_⟩
  · rw [← hwτ ⟨b, hBA hb⟩]
    exact hfix τ.1 τ.2 b hb
  · rw [← hwτ ⟨c, hcA⟩]
    exact hτc

end Proof1413

theorem step1422TransvR_of
    (h133 : Item133) (hNW : Step1422NotWHR) : Step1422TransvR := by
  intro G _ _ A c L hR hfail c' hc' L' hL' hM d hd
  have hS : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := hS.toSec13Data
  obtain ⟨φ⟩ := hM
  obtain ⟨hirr, hBW, hPe, hP9, -, -, -, ⟨ψ⟩, -⟩ := Proof1413.case3_of_m22 h133 hD hS.hypS_or_hypT
    φ (hNW G A c L hR hfail c' hc' L' hL' ⟨φ⟩)
  have hperf : Group.IsPerfect (Sec12.lBar c' L') := by
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    have := (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt).1
    exact Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective
  have h9 : Nat.card (A ⊓ L' : Subgroup G) = 9 := Sec13.card_inf_eq_nine hD hperf ψ
  have hM22s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcL : c' ∉ L' := Proof1413.not_mem_of_mulEquiv_simple hD
    (by rw [KFacts.KS14.card_nativeM22]; norm_num) φ
  obtain ⟨w, hw, hwB, hwc⟩ := Proof1413.exists_transvection hS.isE27 hD.mem_A
    (fun h : c' ∈ A ⊓ L' => hcL (Subgroup.mem_inf.mp h).2) inf_le_left h9 hBW
    (inf_le_right : L' ⊓ Subgroup.normalizer (A : Set G) ≤ _) hirr hPe hP9 d hd
  refine ⟨w, hw, ?_, hwc⟩
  have h1 := hwB d hd
  calc w * d = w * d * w⁻¹ * w := by group
    _ = d * w := by rw [h1]

end CFSG.RankThree.PartTwo.Sec14

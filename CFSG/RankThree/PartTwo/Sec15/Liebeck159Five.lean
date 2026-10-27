module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6Proof159
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159Point
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159Act
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159BJ
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159Hessian
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159CardL
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159HessImg
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159Omega
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

section Certs

private theorem exists_sylow_ge {p : ℕ} [Fact p.Prime] {K P : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R K ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (show (⟨x, hPK hx⟩ : ↥K) ∈ P.subgroupOf K from hx), rfl⟩

private theorem not_three_dvd_of_not_modNine_two {n m : ℕ}
    (h : ¬ (2 ^ (n * m) % 9 = 1 ∨ 2 ^ (n * m) % 9 = 8)) : ¬ 3 ∣ n := by
  rintro ⟨k, rfl⟩
  apply h
  have key : ∀ j : ℕ, 2 ^ (3 * j) % 9 = 1 ∨ 2 ^ (3 * j) % 9 = 8 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 3 * (j + 1) = 3 * j + 3 by ring, pow_add, Nat.mul_mod]
      rcases ih with h | h <;> simp [h]
  rw [show 3 * k * m = 3 * (k * m) by ring]
  exact key _

theorem false_of_case148Five_data (h138 : Item138N) (h41 : Sec4.Item4_1LargePrime)
    {A L₀ : Subgroup G} {c₀ : G} (ctx : Ctx159 G A c₀ L₀) {w : G} (hw : IsW159 A L₀ w)
    {J : Subgroup G} (hJ : J ∈ scriptY0 A (lB A)) (hJΔ : J = deltaZero A (lB A) J)
    (hwJ : w ∈ Subgroup.normalizer (J : Set G)) [(ker148 A J).Normal]
    {c : G} (hcA : c ∈ A) {L K : Subgroup G} {n m : ℕ}
    (hΩc : Subgroup.zpowers c ∈ omegaA A) (hL : L ∈ lA A c) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hX : Sec4.IsoLThreePi ↥(img148 A J (deltaZero A (lB A) J)) 2 (3 * n))
    (hsplit : img148 A J (deltaZero A (lB A) J ⊔ A) =
      img148 A J (deltaZero A (lB A) J) ⊔ Subgroup.zpowers (alpha148 A J c hcA))
    (hfield : KFacts.InducesStdKind (img148 A J (deltaZero A (lB A) J)) (alpha148 A J c hcA)
      .field)
    (hLε : IsLThreeEpsAt (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 (n * m))
    (hKLJ : K ≤ L ⊓ J) (hKn : Sec4.IsoLThreePi ↥(img148 A J K) 2 n) : False := by
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ.1.1.2
  obtain ⟨hRc, hBL, hAeq, -, ⟨eL⟩⟩ := ctx159_point ctx hΩc hL
  have hA9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by rw [hBL]; exact ctx.card_inf
  have hnm : 1 ≤ n * m := Nat.mul_pos hn hm
  have hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 (n * m) :=
    isoLThreePi_two_of_ctx159 ctx eL hnm hLε
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hRc.isElemAbelian
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g.1 g.2)⟩
  have hcN : ∀ a ∈ A, a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro a ha
    have hcomm : Commute a c := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
    have hx : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ k := fun k => by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hcomm.zpow_right k).eq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
      rw [hx k]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
    · intro hx'
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
      have : x = c ^ k := by
        calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
          _ = a⁻¹ * c ^ k * a := by rw [← hk]
          _ = a⁻¹ * (a * c ^ k * a⁻¹) * a := by rw [hx k]
          _ = c ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  have hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (J : Set G) :=
    fun a ha => ⟨hcN a ha, hAJ ha⟩
  obtain ⟨P, hP, hAP⟩ := exists_sylow_ge hAN hA3
  have hΩ : A ≠ omegaOneThree P :=
    leaf2_omega_ne hRc hcA hAJ hJΔ hn hX hsplit hfield hKLJ hKn hP hAP
  obtain ⟨hmod9, hL9⟩ := leaf2_card_L h138 h41 hRc hnm hL3 hJ hP hAP hΩ hA9 hAeq
  have hn3 : ¬ 3 ∣ n := not_three_dvd_of_not_modNine_two hmod9
  have hLN : A ≤ Subgroup.normalizer (L : Set G) := (mem_lA_iff.mp hL).2.1
  have hBJ : A ⊓ L ≤ J := leaf2_B_le_J hn hAJ hLN hKLJ hKn hL9 hA9
  obtain ⟨E, hEe, hE9, htr, hEmap⟩ := leaf2_hessian_img hKLJ hBJ hKn hn3 hL9 hA9 hAe
  have hX' : Sec4.IsoLThreePi ↥(img148 A J J) 2 (3 * n) := by
    have h := hX
    rw [← hJΔ] at h
    exact h
  have hZ : Subgroup.center ↥(img148 A J J) = ⊥ := center_img148_eq_bot (by omega) hX'
  obtain ⟨act, hact⟩ := exists_act_img148 hAJ
  obtain ⟨hfix, hinner⟩ := act_facts hAJ hBJ act hact hEmap
  have hcN' : c ∈ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
    ⟨hAJ hcA, Subgroup.le_normalizer hcA⟩
  have hwN' : w ∈ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
    ⟨hwJ, hw.1⟩
  obtain ⟨hbB, hb1⟩ := commutator_mem_inf ctx hw hΩc
  rw [← hBL] at hbB
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hb3 : (c * w * c⁻¹ * w⁻¹) ^ 3 = 1 := hAe.2 _ hbB.1
  have hcB : ∀ b ∈ A ⊓ L, c * b = b * c := fun b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨b, hb.1⟩)
  have hwB : ∀ b ∈ A ⊓ L, w * b = b * w := fun b hb => hw.2.2.1 b (hBL ▸ hb)
  obtain ⟨e₀, he₀, he₀1, hcomm⟩ :=
    hinner (⟨c, hcN'⟩ * ⟨w, hwN'⟩ * ⟨c, hcN'⟩⁻¹ * ⟨w, hwN'⟩⁻¹) hbB hb1 hb3
  refine false_of_commutator_hessian (p := 2) (e := 3 * n) (by omega) hX' hZ hEe hE9 htr act
    (c := ⟨c, hcN'⟩) (w := ⟨w, hwN'⟩) ⟨1, ?_⟩ (by simpa using hw.2.1) (hfix _ hcB) (hfix _ hwB)
    he₀ he₀1 hcomm
  apply Subtype.ext
  simpa using hc3

theorem step159FiveR_of (h134 : Item134) (h48 : Sec4.Item4_8) (h138 : Item138N)
    (h41 : Sec4.Item4_1LargePrime) : Step159FiveR := by
  intro G _ _ A c₀ L₀ ctx w hw J hJ hwJ h5
  have h14 := ctx.toSec15R.toSec14Std
  have hJ4 := hJ.1
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ4.1.2
  have hJΔ0 : J = deltaZero A (lB A) J :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      h14 hAJ hJ4.2.1 hJ4.2.2.1
  letI := ker148_normal hAJ
  obtain ⟨c, hcA, L, n, m, hΩc, hL, hn, hm, hX, hsplit, -, hfield, hLε, -, K, hKLJ, hKn, -, -⟩ := h5
  exact false_of_case148Five_data h138 h41 ctx hw hJ hJΔ0 hwJ hcA hΩc hL hn hm hX hsplit hfield
    hLε hKLJ hKn

end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck159

module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofMeet
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156 CFSG.RankThree.PartTwo.Sec15.Proof155w
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155w

theorem le_centralizer_of_pCoreOf_le_centralizer {X Y : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hXY : X ≤ Y) (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y)
    (hdX : ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X)
    (hO : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({d} : Set G)) :
    Y ≤ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXO := pCoreOf_le_pCoreOf_of_eq_sup hXY hY
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hdXc : ∀ x ∈ X, d * x = x * d := by
    intro x hx
    set u := d * x * d⁻¹ * x⁻¹ with hu
    have huO : u ∈ CFSG.Open.pCoreOf 2 Y := hXO (hdX x hx)
    have hud : u * d = d * u := Subgroup.mem_centralizer_singleton_iff.mp (hO huO)
    have hconj : ∀ n : ℕ, d ^ n * x * (d ^ n)⁻¹ = u ^ n * x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hc : Commute d (u ^ n) := (show Commute d u from hud.symm).pow_right n
        calc d ^ (n + 1) * x * (d ^ (n + 1))⁻¹ = d * (d ^ n * x * (d ^ n)⁻¹) * d⁻¹ := by
              rw [pow_succ']
              group
          _ = d * (u ^ n * x) * d⁻¹ := by rw [ih]
          _ = u ^ n * (d * x * d⁻¹) := by
              rw [show d * (u ^ n * x) * d⁻¹ = (d * u ^ n) * x * d⁻¹ by group, hc.eq]
              group
          _ = u ^ (n + 1) * x := by
              rw [show d * x * d⁻¹ = u * x by rw [hu]; group, pow_succ]
              group
    have h3 := hconj 3
    rw [hd3, one_mul, inv_one, mul_one] at h3
    have hu3 : u ^ 3 = 1 := by
      have := congrArg (· * x⁻¹) h3
      simpa using this.symm
    obtain ⟨k, hk⟩ := hO2 ⟨u, huO⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hco : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have hu1 : u = 1 := by
      have h1 := (pow_gcd_eq_one (a := u)).mpr ⟨hk', hu3⟩
      rwa [hco.gcd_eq_one, pow_one] at h1
    have : d * x * d⁻¹ = x := by
      have := hu ▸ hu1
      rw [mul_inv_eq_one] at this
      exact this
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [this]
  intro y hy
  have hy' : y ∈ ((X ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := hY ▸ hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _
    (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy'
  obtain ⟨x, hx, o, ho, rfl⟩ := hy'
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hod : o * d = d * o := Subgroup.mem_centralizer_singleton_iff.mp (hO ho)
  calc x * o * d = x * (d * o) := by rw [mul_assoc, hod]
    _ = d * (x * o) := by rw [← mul_assoc, ← hdXc x hx, mul_assoc]

end Proof155w

@[expose] def Step156CQA5DFaith (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) →
      Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y →
      (∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ∀ (f : G) (Lf : Subgroup G), Subgroup.zpowers f ∈ omegaA A →
          f ∈ Subgroup.closure ({c₀, d} : Set G) → Lf ∈ lA A f →
          Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) →
            CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ⊓
              Sec4.thetaQuotCentralizer Lf = ⊥) →
        CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({d} : Set G) ∧
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≠ ⊥

@[expose] noncomputable def Step156CQA5DFaithR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQA5DFaith A (lB A)

theorem step156CQA5D_of_faith
    (h142 : Item142AllS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) (hw : Item155w A (lB A))
    (hrest : Step156CQA5DFaith A (lB A)) : Step156CQA5D A (lB A) := by
  intro Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX
  obtain ⟨hO, hO2⟩ := hrest Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX
    fun M hM f Lf hfΩ hfcd hLf hJf =>
      inf_thetaQuotCentralizer_eq_bot h142 h h152 h153 hw hY (Or.inl hY5) D hM hfΩ hfcd hLf hJf
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hdsc : d ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact ⟨le_centralizer_of_pCoreOf_le_centralizer (hA.1.2 d D.mem_d) D.le_x hYX hdsc.2 hO, hO2⟩

theorem step156CQA5DR_of_faith
    (h142 : Item142AllS14) (h152 : Item152R)
    (h153 : Item153MainR) (hw : Item155wR) (hrest : Step156CQA5DFaithR) : Step156CQA5DR :=
  fun G _ _ A c L hR => step156CQA5D_of_faith h142 hR.toSec14Std (h152 G A c L hR)
    (h153 G A c L hR) (hw G A c L hR) (hrest G A c L hR)

theorem item156R_of_twin5
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hw : Item155wR)
    (hrest : Step156CQA5DFaithR) : Item156R := by
  have h153 : Item153MainR := item153MainR_of_char h148 h149 h152
    (claim153CharR_of_twin h315 h316 h149 (claim153TwinR_of_items h148 h149 h152) hpush)
  exact item156R_of_twin3_meet h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush
      (step156ONKR_of h148 h134 h48) (step156CQA5DR_of_faith h142 h152 h153 hw hrest)
      (step156QThetaMeetR_of h142 h152 h153 hw)

theorem claim153NormalR_of_twin5
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hw : Item155wR)
    (hrest : Step156CQA5DFaithR) : Claim153NormalR := by
  have h153 : Item153MainR := item153MainR_of_char h148 h149 h152
    (claim153CharR_of_twin h315 h316 h149 (claim153TwinR_of_items h148 h149 h152) hpush)
  exact claim153NormalR_of_twin3_meet h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush
    (step156CQA5DR_of_faith h142 h152 h153 hw hrest) (step156QThetaMeetR_of h142 h152 h153 hw)

theorem item155R_of_twin5
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hw : Item155wR)
    (hrest : Step156CQA5DFaithR) : Item155R :=
  item155R_of_item155wR (step155NR_of_claim153NormalR h149
    (claim153NormalR_of_twin5 h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush hw hrest)) hw

end CFSG.RankThree.PartTwo.Sec15

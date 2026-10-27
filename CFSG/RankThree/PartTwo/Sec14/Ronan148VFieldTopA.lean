module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VFieldTop
import CFSG.RankThree.PartTwo.Sec4.Ronan148VElation
import CFSG.RankThree.PartTwo.Sec4.Ronan148VUnitaryHom
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSubfieldCore

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open scoped commutatorElement

section Certificates


theorem exists_fieldAut_model_linear {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {σ : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hK : Sec4.IsoLThreePi ↥K 2 n) :
    ∃ (χ : ↥X ≃* projectiveSL 3 (GaloisField 2 (3 * n)))
      (τ : GaloisField 2 (3 * n) ≃+* GaloisField 2 (3 * n)), orderOf τ = 3 ∧
      ∀ x : ↥X, χ (X.normalizerMonoidHom ⟨σ, hσN⟩ x) = fieldAut 3 _ τ (χ x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨hq', -⟩
  swap
  · omega
  set F := GaloisField 2 (3 * n) with hFdef
  have hcardF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 F
  set χ₀ : ↥X ≃* projectiveSL 3 F := e.trans φ with hχ₀
  set α := X.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨σ, hσN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hσ3)
    rw [this, map_one]
  have hout := not_isInnerAut_of_inducesStdKind_field148 hind hσN
  have hαk : ∀ k : ↥X, (k : Γ) ∈ K → α k = k := by
    intro k hk
    apply Subtype.ext
    show σ * (k : Γ) * σ⁻¹ = k
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm, mul_inv_cancel_right]
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn hK
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  set t : ↥X := ⟨k₀, hKX k₀.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have : (k₀ : Γ) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hk₀, pow_orderOf_eq_one, Subgroup.coe_one]
    exact this
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : ((t : ↥X) : Γ) = 1 := congrArg Subtype.val h1
    have hk1 : k₀ = 1 := Subtype.ext h2
    rw [hk1, orderOf_one] at hk₀
    norm_num at hk₀
  have hαt : α t = t := hαk t k₀.2
  set β := MulAut.congr χ₀ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr χ₀ α).mp hb)
  have hβt : β (χ₀ t) = χ₀ t := by
    change χ₀ (α (χ₀.symm (χ₀ t))) = χ₀ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hχt2 : (χ₀ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hχt1 : χ₀ t ≠ 1 := fun h1 => ht1 (χ₀.injective (h1.trans (map_one χ₀).symm))
  have hlin : β ∉ linearAutGroup 3 F := by
    intro hl
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hl
    apply hβout
    rw [← hA]
    have h9 : 9 ∣ Nat.card F - 1 := by
      rw [hcardF]
      exact (Item148Res5.nine_dvd_of_two_pow_three_mul n).1 hq
    exact Sec19.Item19Res2Proof.isInnerAut_of_conjAut_fix_involution h9 (by rw [hA]; exact hβ3)
      hχt2 hχt1 (by rw [hA]; exact hβt)
  obtain ⟨τ, hτ, H, hβH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl β hβ3 hlin
  refine ⟨χ₀.trans ((conjAut 3 F H)⁻¹ : MulAut (projectiveSL 3 F)), τ, hτ, fun x => ?_⟩
  have h1 : β (χ₀ x) = χ₀ (α x) := by
    change χ₀ (α (χ₀.symm (χ₀ x))) = _
    rw [MulEquiv.symm_apply_apply]
  change (conjAut 3 F H)⁻¹ (χ₀ (α x)) = fieldAut 3 F τ ((conjAut 3 F H)⁻¹ (χ₀ x))
  rw [← h1, hβH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

theorem exists_twist_of_homology_linear {X : Type} [Group X] [Finite X] {J K E : Subgroup X}
    {σ : X} {n : ℕ} (hn : 1 ≤ n) (hJ : Sec4.IsoLThreePi ↥J 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) (hind : KFacts.InducesStdKind J σ .field) (hσ3 : σ ^ 3 = 1)
    (hKJ : K ≤ J) (hKC : K ≤ Subgroup.centralizer ({σ} : Set X))
    (hK : Sec4.IsoLThreePi ↥K 2 n) (hEJ : E ≤ J) (hEC : E ≤ Subgroup.centralizer ({σ} : Set X))
    (hEc : IsMulCommutative ↥E) {z : X} (hz : z ∈ E) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (h2 : 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X))) :
    ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
      Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
      ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσN : σ ∈ Subgroup.normalizer (J : Set X) := KFacts.InducesStdKind.mem_normalizer hind
  obtain ⟨χ, τ, hτ, hχ⟩ := exists_fieldAut_model_linear hn hJ hq hind hσ3 hσN hKJ hKC hK
  set α := J.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hαapp : ∀ x : ↥J, ((α x : ↥J) : X) = σ * x * σ⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe hσN x
  have hzσ : z * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.mp (hEC hz)
  have hEcomm : ∀ x ∈ E, x * z = z * x := fun x hx =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  obtain ⟨zJ, hzJ⟩ : ∃ y : ↥J, (y : X) = z := ⟨⟨z, hEJ hz⟩, rfl⟩
  have hαz : α zJ = zJ := by
    apply Subtype.ext
    rw [hαapp, hzJ, ← hzσ, mul_inv_cancel_right]
  have hτz : fieldAut 3 _ τ (χ zJ) = χ zJ := by rw [← hχ, hαz]
  have hz3' : (χ zJ) ^ 3 = 1 := by
    rw [← map_pow]
    have : zJ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hzJ, hz3, Subgroup.coe_one])
    rw [this, map_one]
  have hz1' : χ zJ ≠ 1 := by
    intro h1
    apply hz1
    have : zJ = 1 := χ.injective (h1.trans (map_one χ).symm)
    rw [← hzJ, this, Subgroup.coe_one]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set tJ : ↥J := ⟨t, t.2.1⟩ with htJ
  have htz : (t : X) * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp t.2.2
  have ht2 : (χ tJ) ^ 2 = 1 := by
    rw [← map_pow]
    have : tJ ^ 2 = 1 := by
      apply Subtype.ext
      have h1 := pow_orderOf_eq_one t
      rw [ht] at h1
      have h2 := congrArg Subtype.val h1
      simpa [htJ] using h2
    rw [this, map_one]
  have ht1 : χ tJ ≠ 1 := by
    intro h1
    have h2 : tJ = 1 := χ.injective (h1.trans (map_one χ).symm)
    have h4 : ((tJ : ↥J) : X) = ((1 : ↥J) : X) := congrArg Subtype.val h2
    have h3 : t = 1 := Subtype.ext h4
    rw [h3, orderOf_one] at ht
    norm_num at ht
  have hzt : χ zJ * χ tJ = χ tJ * χ zJ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzJ]
    exact htz.symm
  obtain ⟨U, hU2, hUC, hUτ, ⟨u₀, hu₀U, hu₀fix, hu₀1⟩, hUcomm⟩ :=
    Sec4.Ronan148V.exists_elation_model hτ hz3' hz1' ht2 ht1 hzt hτz
  set U' : Subgroup X := (U.comap χ.toMonoidHom).map J.subtype with hU'
  have hmemU' : ∀ x : ↥J, (x : X) ∈ U' ↔ χ x ∈ U := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hU'J : U' ≤ J := Subgroup.map_subtype_le _
  set V : Subgroup X := U' ⊓ Subgroup.centralizer ({σ * z} : Set X) with hV
  have hσzC : ∀ g : X, g * σ = σ * g → g * z = z * g → g * (σ * z) = (σ * z) * g := by
    intro g h1 h2
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  refine ⟨V, inf_le_inf_right _ hU'J, ?_, ?_, ?_⟩
  · intro h3
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hvJ : (v : X) ∈ J := hU'J v.2.1
    have hvU : χ ⟨v, hvJ⟩ ∈ U := (hmemU' ⟨v, hvJ⟩).mp v.2.1
    have hv2 : (v : X) * v = 1 := by
      have h1 := hU2 _ hvU
      rw [← map_mul] at h1
      have h2 : (⟨v, hvJ⟩ : ↥J) * ⟨v, hvJ⟩ = 1 := χ.injective (h1.trans (map_one χ).symm)
      exact congrArg Subtype.val h2
    have hv2' : v ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two, hv2, Subgroup.coe_one]
    have := orderOf_dvd_of_pow_eq_one hv2'
    rw [hv] at this
    norm_num at this
  · have hconjV : ∀ g : X, g * σ = σ * g → g * z = z * g →
        (∀ x : ↥J, χ x ∈ U → ∃ hg : g * x * g⁻¹ ∈ J, χ ⟨g * x * g⁻¹, hg⟩ ∈ U) →
        g ∈ Subgroup.normalizer (V : Set X) := by
      intro g hgσ hgz hgU
      apply Subgroup.mem_normalizer_fintype
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_inf] at hh ⊢
      obtain ⟨hhU, hhC⟩ := hh
      have hhJ : h ∈ J := hU'J hhU
      obtain ⟨hg, hgU'⟩ := hgU ⟨h, hhJ⟩ ((hmemU' ⟨h, hhJ⟩).mp hhU)
      refine ⟨(hmemU' ⟨_, hg⟩).mpr hgU', ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hhC ⊢
      have hgc := hσzC g hgσ hgz
      have hgc' : g⁻¹ * (σ * z) = (σ * z) * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgc, mul_inv_cancel_right]
      calc g * h * g⁻¹ * (σ * z) = g * h * ((σ * z) * g⁻¹) := by rw [mul_assoc, hgc']
        _ = g * (h * (σ * z)) * g⁻¹ := by group
        _ = g * ((σ * z) * h) * g⁻¹ := by rw [hhC]
        _ = (g * (σ * z)) * h * g⁻¹ := by group
        _ = (σ * z) * (g * h * g⁻¹) := by rw [hgc]; group
    refine sup_le (Subgroup.zpowers_le.mpr ?_) fun x hx => ?_
    · refine hconjV σ rfl hzσ.symm fun x hx => ⟨(α x).2, ?_⟩
      have : (⟨σ * x * σ⁻¹, (α x).2⟩ : ↥J) = α x := Subtype.ext (hαapp x).symm
      rw [this, hχ]
      exact hUτ _ hx
    · have hxσ : x * σ = σ * x := Subgroup.mem_centralizer_singleton_iff.mp (hEC hx)
      refine hconjV x hxσ (hEcomm x hx) fun y hy => ⟨J.mul_mem (J.mul_mem (hEJ hx) y.2)
        (J.inv_mem (hEJ hx)), ?_⟩
      have : (⟨x * y * x⁻¹, J.mul_mem (J.mul_mem (hEJ hx) y.2) (J.inv_mem (hEJ hx))⟩ : ↥J) =
          ⟨x, hEJ hx⟩ * y * (⟨x, hEJ hx⟩ : ↥J)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      refine hUC _ ?_ _ hy
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hzJ]
      exact hEcomm x hx
  · intro hle
    obtain ⟨uJ, hχu⟩ : ∃ y : ↥J, χ y = u₀ := ⟨χ.symm u₀, MulEquiv.apply_symm_apply χ u₀⟩
    have huU' : (uJ : X) ∈ U' := (hmemU' uJ).mpr (by rw [hχu]; exact hu₀U)
    have huC : (uJ : X) * (σ * z) = (σ * z) * uJ := by
      have h1 : α (zJ * uJ * zJ⁻¹) = uJ := by
        apply χ.injective
        rw [hχ, map_mul χ, map_mul χ, map_inv χ, hχu]
        exact hu₀fix
      have h2 := congrArg Subtype.val h1
      rw [hαapp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzJ] at h2
      conv_lhs => rw [← h2]
      group
    have huV : (uJ : X) ∈ V := ⟨huU', Subgroup.mem_centralizer_singleton_iff.mpr huC⟩
    have hw : ⁅(uJ : X), z⁆ ∈ K :=
      hle (Subgroup.commutator_mem_commutator huV (Subgroup.mem_sup_right hz))
    have hwσ : ⁅(uJ : X), z⁆ * σ = σ * ⁅(uJ : X), z⁆ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKC hw)
    have hzC : z ∈ Subgroup.centralizer ({σ * z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hσzC z hzσ rfl)
    have huCm : (uJ : X) ∈ Subgroup.centralizer ({σ * z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr huC
    have hwσz : ⁅(uJ : X), z⁆ * (σ * z) = (σ * z) * ⁅(uJ : X), z⁆ :=
      Subgroup.mem_centralizer_singleton_iff.mp (by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huCm hzC)
          (Subgroup.inv_mem _ huCm)) (Subgroup.inv_mem _ hzC))
    have hwz : ⁅(uJ : X), z⁆ * z = z * ⁅(uJ : X), z⁆ := by
      have e1 : z = σ⁻¹ * (σ * z) := by group
      calc ⁅(uJ : X), z⁆ * z = ⁅(uJ : X), z⁆ * σ⁻¹ * (σ * z) := by rw [mul_assoc, ← e1]
        _ = σ⁻¹ * (⁅(uJ : X), z⁆ * (σ * z)) := by
            rw [show ⁅(uJ : X), z⁆ * σ⁻¹ = σ⁻¹ * ⁅(uJ : X), z⁆ by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, hwσ, inv_mul_cancel_left]]
            group
        _ = z * ⁅(uJ : X), z⁆ := by rw [hwσz]; group
    have hwz' : ⁅u₀, χ zJ⁆ * χ zJ = χ zJ * ⁅u₀, χ zJ⁆ := by
      rw [← hχu, ← map_commutatorElement, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv, hzJ]
      simpa only [commutatorElement_def] using hwz
    exact hu₀1 (hUcomm u₀ hu₀U hwz')

@[expose] def KF148FieldTopTwistRUnitaryOrOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J K E : Subgroup X) (σ : X) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥J 2 (3 * n) → KFacts.InducesStdKind J σ .field → σ ^ 3 = 1 →
    K ≤ J → K ≤ Subgroup.centralizer ({σ} : Set X) → IsSimpleGroup ↥K →
    Sec4.IsoLThreePi ↥K 2 n → E ≤ J → E ≤ Subgroup.centralizer ({σ} : Set X) →
    IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    ∀ z ∈ E, z ≠ 1 →
    (2 ^ (3 * n) % 3 = 2 ∨ ¬ 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X))) →
    ∀ R : Subgroup X, R ≤ K ⊓ Subgroup.centralizer ({z} : Set X) →
      ¬ 3 ∣ Nat.card R → Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X) →
      R = ⁅R, Subgroup.zpowers σ ⊔ E⁆ → R ≠ ⊥ →
      ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
        Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
        ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K

theorem kf148FieldTopTwistR_of_unitaryOrOdd (h : KF148FieldTopTwistRUnitaryOrOdd) :
    KF148FieldTopTwistR := by
  intro X _ _ J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 R hRK hR3 hRN
    hRc hR1
  by_cases hcase : 2 ^ (3 * n) % 3 = 2 ∨ ¬ 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X))
  · exact h X J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 hcase R hRK hR3
      hRN hRc hR1
  · push Not at hcase
    obtain ⟨hq, h2⟩ := hcase
    have h0 : 2 ^ (3 * n) % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ (3 * n) := Nat.dvd_of_mod_eq_zero h0
      have := Nat.prime_three.dvd_of_dvd_pow h3
      norm_num at this
    exact exists_twist_of_homology_linear hn hJ (by omega) hind hσ3 hKJ hKC hK hEJ hEC hEc hz
      (hE3 z hz) hz1 h2


theorem eq_bot_of_homology_unitary {X : Type} [Group X] [Finite X]
    {J K E R : Subgroup X} {σ : X} {n : ℕ} (hJ : Sec4.IsoLThreePi ↥J 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 2) (hKJ : K ≤ J) (hKC : K ≤ Subgroup.centralizer ({σ} : Set X))
    (hEJ : E ≤ J) (hEC : E ≤ Subgroup.centralizer ({σ} : Set X)) (hEc : IsMulCommutative ↥E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) {z : X} (hz : z ∈ E) (hz1 : z ≠ 1)
    (h2 : 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X)))
    (hRK : R ≤ K ⊓ Subgroup.centralizer ({z} : Set X)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hRN : Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X))
    (hRc : R = ⁅R, Subgroup.zpowers σ ⊔ E⁆) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hJ with ⟨hq', -⟩ | ⟨-, ⟨e⟩⟩
  · omega
  have hf : Odd (3 * n) := by
    rcases Nat.even_or_odd (3 * n) with ⟨k, hk⟩ | hodd
    · exfalso
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at hq
      norm_num at hq
    · exact hodd
  have h3n : 1 ≤ 3 * n := by
    obtain ⟨k, hk⟩ := hf
    omega
  set F := GaloisField 2 (2 * (3 * n)) with hFdef
  have hcardF : Nat.card F = 2 ^ (2 * (3 * n)) := GaloisField.card 2 _ (by omega)
  have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, h3n, hcardF⟩
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
  set χ : ↥J ≃* unitaryPSU hU 3 := e.trans φ.symm with hχ
  have hRJ : R ≤ J := (hRK.trans inf_le_left).trans hKJ
  have hzσ : z * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.mp (hEC hz)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨zJ, hzJ⟩ : ∃ y : ↥J, (y : X) = z := ⟨⟨z, hEJ hz⟩, rfl⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨tJ, htJ⟩ : ∃ y : ↥J, (y : X) = t := ⟨⟨t, t.2.1⟩, rfl⟩
  have htz : (t : X) * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp t.2.2
  have hcommJ : ∀ a b : ↥J, (a : X) * b = b * a → χ a * χ b = χ b * χ a := by
    intro a b hab
    rw [← map_mul, ← map_mul]
    exact congrArg χ (Subtype.ext hab)
  have hz3' : χ zJ ^ 3 = 1 := by
    rw [← map_pow]
    have : zJ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hzJ, hE3 z hz, Subgroup.coe_one])
    rw [this, map_one]
  have hz1' : χ zJ ≠ 1 := by
    intro h1
    apply hz1
    have : zJ = 1 := χ.injective (h1.trans (map_one χ).symm)
    rw [← hzJ, this, Subgroup.coe_one]
  have ht2' : χ tJ ^ 2 = 1 := by
    rw [← map_pow]
    have : tJ ^ 2 = 1 := by
      apply Subtype.ext
      have h1 := pow_orderOf_eq_one t
      rw [ht] at h1
      have h3 : (t : X) ^ 2 = 1 := by
        have := congrArg Subtype.val h1
        simpa using this
      rw [← htJ] at h3
      simpa using h3
    rw [this, map_one]
  have ht1' : χ tJ ≠ 1 := by
    intro h1
    have h3 : tJ = 1 := χ.injective (h1.trans (map_one χ).symm)
    have h4 : (t : X) = 1 := by rw [← htJ, h3, Subgroup.coe_one]
    have h5 : t = 1 := Subtype.ext h4
    rw [h5, orderOf_one] at ht
    norm_num at ht
  have hzt' : χ zJ * χ tJ = χ tJ * χ zJ := hcommJ zJ tJ (by rw [hzJ, htJ]; exact htz.symm)
  obtain ⟨L, hLc, hLx⟩ :=
    Sec4.Ronan148V.exists_levi_of_homology_unitary hf hU hz3' hz1' ht2' ht1' hzt'
  set T : Subgroup X := (L.comap χ.toMonoidHom).map J.subtype with hT
  have hmemT : ∀ y : ↥J, (y : X) ∈ T ↔ χ y ∈ L := by
    intro y
    constructor
    · rintro ⟨w, hw, hwy⟩
      have : w = y := Subtype.ext hwy
      rw [← this]
      exact hw
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRK hr).2
  have hcommT : ∀ r ∈ R, ∀ y ∈ E, ⁅r, y⁆ ∈ T := by
    intro r hr y hy
    have h1 : ⁅r, y⁆ = ((⁅(⟨r, hRJ hr⟩ : ↥J), ⟨y, hEJ hy⟩⁆ : ↥J) : X) := by
      simp [commutatorElement_def]
    rw [h1, hmemT, map_commutatorElement]
    refine hLc _ _ (hcommJ _ zJ ?_) (hcommJ _ zJ ?_)
    · rw [hzJ]
      exact hRz r hr
    · rw [hzJ]
      exact hEcomm y hy z hz
  have hσE : Subgroup.zpowers σ ≤ Subgroup.normalizer (E : Set X) := by
    have hc : ∀ w ∈ E, σ * w * σ⁻¹ = w := fun w hw => by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC hw), mul_inv_cancel_right]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun y hy => by
      rw [hc y hy]
      exact hy)
  have hRT : R ≤ T := by
    refine hRc.le.trans ?_
    rw [Subgroup.commutator_le]
    intro r hr h hh
    have hmem : h ∈ ((Subgroup.zpowers σ ⊔ E : Subgroup X) : Set X) := hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hσE] at hmem
    obtain ⟨a, ha, y, hy, rfl⟩ := hmem
    have haC : ∀ w ∈ K, a * w = w * a := by
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hwσ : w * σ = σ * w := Subgroup.mem_centralizer_singleton_iff.mp (hKC hw)
      exact ((Commute.zpow_left (Commute.symm hwσ) k))
    have hry : ⁅r, y⁆ ∈ R := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine R.mul_mem hr ?_
      have := (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_right hy)) r⁻¹).mp
        (R.inv_mem hr)
      rw [← mul_assoc]
      exact this
    have h1 : ⁅r, a * y⁆ = ⁅r, y⁆ := by
      have har : a * r = r * a := haC r ((hRK hr).1)
      have hac : a * ⁅r, y⁆ = ⁅r, y⁆ * a := haC _ (hRK hry).1
      calc ⁅r, a * y⁆ = a * ⁅r, y⁆ * a⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]
            have : r * (a * y) * r⁻¹ * (a * y)⁻¹ = (r * a) * y * r⁻¹ * y⁻¹ * a⁻¹ := by group
            rw [this, ← har]
            group
        _ = ⁅r, y⁆ := by rw [hac, mul_inv_cancel_right]
    rw [h1]
    exact hcommT r hr y hy
  set R' : Subgroup (unitaryPSU hU 3) := (R.subgroupOf J).map χ.toMonoidHom with hR'
  have hmemR' : ∀ y : ↥J, χ y ∈ R' ↔ (y : X) ∈ R := by
    intro y
    constructor
    · rintro ⟨w, hw, hwy⟩
      have : w = y := χ.injective hwy
      rw [← this]
      exact hw
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hR'L : R' ≤ L := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmemT w).mp (hRT hw)
  have hR'3 : ¬ 3 ∣ Nat.card R' := by
    rw [hR', Subgroup.card_map_of_injective χ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv]
    exact hR3
  have hEcent : ∀ y ∈ E, ∀ r ∈ R, r * y = y * r := by
    intro y hy
    set yJ : ↥J := ⟨y, hEJ hy⟩ with hyJ
    have hyz : χ yJ * χ zJ = χ zJ * χ yJ := hcommJ yJ zJ (by rw [hzJ]; exact hEcomm y hy z hz)
    have hy3 : χ yJ ^ 3 = 1 := by
      rw [← map_pow]
      have : yJ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 y hy)
      rw [this, map_one]
    have hyN : χ yJ ∈ Subgroup.normalizer (R' : Set (unitaryPSU hU 3)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      obtain ⟨w', rfl⟩ := χ.surjective w
      rw [← map_inv, ← map_mul, ← map_mul, hmemR', hmemR']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyJ]
      exact Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_right hy)) w'
    have hc := hLx (χ yJ) hyz hy3 R' hR'L hR'3 hyN
    intro r hr
    have h1 := hc (χ ⟨r, hRJ hr⟩) ((hmemR' _).mpr hr)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (χ.injective h1)
  have hcent : Subgroup.zpowers σ ⊔ E ≤ Subgroup.centralizer (R : Set X) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) fun y hy => ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hRK hr).1))
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hEcent y hy r hr
  have hbot : ⁅R, Subgroup.zpowers σ ⊔ E⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact hcent
  rw [hRc, hbot]

@[expose] def KF148FieldTopTwistROdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J K E : Subgroup X) (σ : X) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥J 2 (3 * n) → KFacts.InducesStdKind J σ .field → σ ^ 3 = 1 →
    K ≤ J → K ≤ Subgroup.centralizer ({σ} : Set X) → IsSimpleGroup ↥K →
    Sec4.IsoLThreePi ↥K 2 n → E ≤ J → E ≤ Subgroup.centralizer ({σ} : Set X) →
    IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    ∀ z ∈ E, z ≠ 1 → ¬ 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X)) →
    ∀ R : Subgroup X, R ≤ K ⊓ Subgroup.centralizer ({z} : Set X) →
      ¬ 3 ∣ Nat.card R → Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X) →
      R = ⁅R, Subgroup.zpowers σ ⊔ E⁆ → R ≠ ⊥ →
      ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
        Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
        ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K

theorem kf148FieldTopTwistRUnitaryOrOdd_of_odd
    (h : KF148FieldTopTwistROdd) : KF148FieldTopTwistRUnitaryOrOdd := by
  intro X _ _ J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 hcase R hRK hR3
    hRN hRc hR1
  by_cases h2 : 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X))
  · have hq : 2 ^ (3 * n) % 3 = 2 := hcase.resolve_right (not_not.mpr h2)
    exact absurd (eq_bot_of_homology_unitary hJ hq hKJ hKC hEJ hEC hEc hE3 hz hz1 h2 hRK hR3 hRN
      hRc) hR1
  · exact h X J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 h2 R hRK hR3 hRN
      hRc hR1

theorem kf148FieldTopTwistR_of_odd (h : KF148FieldTopTwistROdd) :
    KF148FieldTopTwistR :=
  kf148FieldTopTwistR_of_unitaryOrOdd (kf148FieldTopTwistRUnitaryOrOdd_of_odd h)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V

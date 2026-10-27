module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.Open.Defs
import CFSG.RankThree.GF2n.Smith81.InspKSpCard
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
import CFSG.RankThree.PartOne.S12K.OrdRigidL
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact
import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
import CFSG.OddTranspositions.PartFour.Fourteen.TableSp
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
import CFSG.Timmesfeld.Bridge.Asc72Theorem
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81

private theorem card_quotient_center_of_isSymplecticTransvection {X : Type} [Group X] {m f : ℕ}
    {s : X} (hf : 1 ≤ f) (h : SevenK.IsSymplecticTransvection X m f s) :
    ∃ k : ℕ, m = 2 * k ∧ Nat.card (X ⧸ Subgroup.center X) = ordBC k (2 ^ f) := by
  obtain ⟨k, hm, F, _, _, hcard, e, -⟩ := h
  refine ⟨k, hm, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.GF2n.Smith81.Insp.KFact.card_statedSp_eq_ordBC hf hcard k

private theorem ordBC_one_eq_ordA_one (q : ℕ) : ordBC 1 q = ordA 1 q := by
  simp [ordBC, ordA]

theorem isSymplecticTransvection_rigid {X : Type} [Group X] {s s' : X} {m f m' f' : ℕ}
    (hf : 2 ≤ f) (hf' : 2 ≤ f') (hm : 2 ≤ m) (hm' : 2 ≤ m')
    (h : SevenK.IsSymplecticTransvection X m f s)
    (h' : SevenK.IsSymplecticTransvection X m' f' s') : m = m' ∧ f = f' := by
  obtain ⟨k, rfl, hk⟩ := card_quotient_center_of_isSymplecticTransvection (by omega) h
  obtain ⟨k', rfl, hk'⟩ := card_quotient_center_of_isSymplecticTransvection (by omega) h'
  have heq : ordBC k (2 ^ f) = ordBC k' (2 ^ f') := hk.symm.trans hk'
  rcases Nat.lt_or_ge k 2 with hk2 | hk2 <;> rcases Nat.lt_or_ge k' 2 with hk2' | hk2'
  · obtain rfl : k = 1 := by omega
    obtain rfl : k' = 1 := by omega
    rw [ordBC_one_eq_ordA_one, ordBC_one_eq_ordA_one, CFSG.RankThree.PartOne.S12K.ordA_one_eq
      (by omega), CFSG.RankThree.PartOne.S12K.ordA_one_eq (by omega)] at heq
    exact ⟨rfl, CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega))
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega)) heq⟩
  · obtain rfl : k = 1 := by omega
    rw [ordBC_one_eq_ordA_one] at heq
    exact absurd heq.symm (CFSG.RankThree.PartOne.S12K.ordBC_ne_ordA_one hk2' (by omega)
      (by omega))
  · obtain rfl : k' = 1 := by omega
    rw [ordBC_one_eq_ordA_one] at heq
    exact absurd heq (CFSG.RankThree.PartOne.S12K.ordBC_ne_ordA_one hk2 (by omega) (by omega))
  · obtain ⟨rfl, rfl⟩ := CFSG.SeitzReduction.SymplecticPilot.ordBC_eq_ordBC hk2 (by omega) hk2'
      (by omega) heq
    exact ⟨rfl, rfl⟩

theorem isPerfect_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hf : 2 ≤ f)
    (h : SevenK.IsSymplecticTransvection X m f s) : Group.IsPerfect X := by
  obtain ⟨k, -, F, _, _, hcard, e, -⟩ := h
  have hF : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := CFSG.SeitzReduction.SymplecticPilot.isPerfect_statedSp_of_four_le hF k
  let eX : X ≃* StatedSp k F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e
  exact Group.IsPerfect.ofSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective

theorem not_nonempty_mulEquiv_l2Wreath_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hf : 2 ≤ f)
    (h : SevenK.IsSymplecticTransvection X m f s) {f' n : ℕ} (hn : 2 ≤ n) :
    ¬ Nonempty (X ≃* CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f' n) := by
  rintro ⟨φ⟩
  have hperf := isPerfect_of_isSymplecticTransvection hZ hf h
  exact CFSG.Timmesfeld.Bridge.Asc72.commutator_ne_top_of_l2Wreath hn φ
    hperf.commutator_eq_top

section Five

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open TableE1Five

local notation "refl" => TableE1Five.refl

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem perp_or_refl_eq_of_commutator_eq_pm_one (hsym : ∀ x y, b x y = b y x) (hn : 3 ≤ n)
    {v w : Fin n → ZMod 5} (hv : b v v = 1) (hw : b w w = 1)
    (h : (refl b w * refl b v) * (refl b w * refl b v) = 1 ∨
      (refl b w * refl b v) * (refl b w * refl b v) = -1) :
    b v w = 0 ∨ refl b v = refl b w := by
  have hiv := refl_mem_isomGroup hsym v
  have hiw := refl_mem_isomGroup hsym w
  have h1 : (refl b w * refl b v) * (refl b w * refl b v) = 1 := by
    rcases h with h | h
    · exact h
    · exfalso
      have h2 : refl b v * refl b w * refl b v = -refl b w := by
        calc refl b v * refl b w * refl b v
            = refl b w * ((refl b w * refl b v) * (refl b w * refl b v)) := by
              simp only [← mul_assoc, refl_mul_self, one_mul]
          _ = -refl b w := by rw [h, mul_neg_one]
      have h3 : refl b v * refl b w * refl b v = refl b (act (refl b v) w) := by
        simpa only [refl_inv] using conj_refl hiv w
      exact refl_ne_neg_refl hn w (act (refl b v) w) (h3.symm.trans h2)
  have h4 : refl b v * refl b w = refl b w * refl b v := by
    have h5 := inv_eq_of_mul_eq_one_right h1
    rwa [mul_inv_rev, refl_inv, refl_inv] at h5
  rcases act_eq_or_of_commute hiw hv h4 with h6 | h6
  · left
    rw [act_refl hw] at h6
    have h7 : (-2 * b v w) • w = 0 := by linear_combination (norm := module) h6
    rcases smul_eq_zero.1 h7 with h8 | h8
    · exact (by decide : ∀ c : ZMod 5, -2 * c = 0 → c = 0) _ h8
    · exact absurd h8 (ne_zero_of_norm_ne_zero (b := b) (by rw [hw]; decide))
  · right
    rw [act_refl hw] at h6
    have h7 : v = b v w • w := by
      have h8 : (2 : ZMod 5) • (v - b v w • w) = 0 := by
        linear_combination (norm := module) h6
      exact sub_eq_zero.1 ((smul_eq_zero.1 h8).resolve_left (by decide))
    have hc : b v w * b v w = 1 := by
      have h9 : b v v = b v w * b v w := by
        calc b v v = b (b v w • w) (b v w • w) := by rw [← h7]
          _ = b v w * b v w := by
            simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw]
            ring
      rw [← h9, hv]
    have hc' : b v w = 1 ∨ b v w = -1 := by
      revert hc; generalize b v w = c; revert c; decide
    rcases hc' with hc' | hc'
    · rw [hc', one_smul] at h7
      rw [h7]
    · rw [hc', neg_one_smul] at h7
      rw [h7, refl_neg]

private theorem not_refl_mul_refl_eq_pm_refl (hsym : ∀ x y, b x y = b y x) (hn : 4 ≤ n)
    {v₁ v₂ v₃ : Fin n → ZMod 5} (h₁ : b v₁ v₁ = 1) (h₂ : b v₂ v₂ = 1) (h₃ : b v₃ v₃ = 1)
    (h12 : b v₁ v₂ = 0) :
    ¬ (refl b v₂ * refl b v₁ * refl b v₃ = 1 ∨ refl b v₂ * refl b v₁ * refl b v₃ = -1) := by
  intro h
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_perp (b := b) (k := 3) (by omega) ![v₁, v₂, v₃]
  have hy1 : b y v₁ = 0 := by simpa using hy 0
  have hy2 : b y v₂ = 0 := by simpa using hy 1
  have hy3 : b y v₃ = 0 := by simpa using hy 2
  have hone : refl b v₂ * refl b v₁ * refl b v₃ = 1 := by
    rcases h with h | h
    · exact h
    · exfalso
      have h1 : act (refl b v₂ * refl b v₁ * refl b v₃) y = y := by
        simp only [act_mul, act_refl_of_perp h₁ hy1, act_refl_of_perp h₂ hy2,
          act_refl_of_perp h₃ hy3]
      rw [h, neg_act, act_one] at h1
      have h2 : (2 : ZMod 5) • y = 0 := by linear_combination (norm := module) -h1
      exact hy0 ((smul_eq_zero.1 h2).resolve_left (by decide))
  have h3eq : refl b v₃ = refl b v₁ * refl b v₂ := by
    have := eq_inv_of_mul_eq_one_right hone
    rwa [mul_inv_rev, refl_inv, refl_inv] at this
  have h21 : b v₂ v₁ = 0 := by rw [hsym]; exact h12
  have hv1 : act (refl b v₃) v₁ = -v₁ := by
    rw [h3eq, act_mul, act_refl_of_perp h₂ h12, act_refl_self h₁]
  have hv2 : act (refl b v₃) v₂ = -v₂ := by
    rw [h3eq, act_mul, act_refl_self h₂, act_neg, act_refl_of_perp h₁ h21]
  have e1 : v₁ = b v₁ v₃ • v₃ := by
    rw [act_refl h₃] at hv1
    have h8 : (2 : ZMod 5) • (v₁ - b v₁ v₃ • v₃) = 0 := by
      linear_combination (norm := module) hv1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h8).resolve_left (by decide))
  have e2 : v₂ = b v₂ v₃ • v₃ := by
    rw [act_refl h₃] at hv2
    have h8 : (2 : ZMod 5) • (v₂ - b v₂ v₃ • v₃) = 0 := by
      linear_combination (norm := module) hv2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h8).resolve_left (by decide))
  have k1 : b v₁ v₃ * b v₁ v₃ = 1 := by
    calc b v₁ v₃ * b v₁ v₃ = b (b v₁ v₃ • v₃) (b v₁ v₃ • v₃) := by
          simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h₃]
          ring
      _ = 1 := by rw [← e1, h₁]
  have k2 : b v₂ v₃ * b v₂ v₃ = 1 := by
    calc b v₂ v₃ * b v₂ v₃ = b (b v₂ v₃ • v₃) (b v₂ v₃ • v₃) := by
          simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h₃]
          ring
      _ = 1 := by rw [← e2, h₂]
  have k3 : b v₁ v₂ = b v₁ v₃ * b v₂ v₃ := by
    calc b v₁ v₂ = b (b v₁ v₃ • v₃) (b v₂ v₃ • v₃) := by rw [← e1, ← e2]
      _ = b v₁ v₃ * b v₂ v₃ := by
          simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h₃]
          ring
  rw [k3] at h12
  revert k1 k2 h12
  generalize b v₁ v₃ = c
  generalize b v₂ v₃ = d
  revert c d
  decide

theorem not_meetsSq_of_fischerCentralQuotientModel_five {X : Type} [Group X] {E : Set X}
    {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ¬ ∃ u ∈ E, ∃ v ∈ E, u ≠ v ∧ Commute u v ∧ u * v ∈ E := by
  obtain ⟨φ, hφ⟩ := hM
  rintro ⟨u, hu, v, hv, hne, hcomm, huv⟩
  obtain ⟨g₁, hg₁, hφu⟩ := (hφ u).1 hu
  obtain ⟨g₂, hg₂, hφv⟩ := (hφ v).1 hv
  obtain ⟨g₃, hg₃, hφuv⟩ := (hφ (u * v)).1 huv
  obtain ⟨v₁, hv₁, hr₁⟩ := mem_reflSet_iff.1 hg₁
  obtain ⟨v₂, hv₂, hr₂⟩ := mem_reflSet_iff.1 hg₂
  obtain ⟨v₃, hv₃, hr₃⟩ := mem_reflSet_iff.1 hg₃
  have hcom : (g₁ * g₂)⁻¹ * (g₂ * g₁) ∈ Subgroup.center _ := by
    apply QuotientGroup.eq.1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hφu, ← hφv, ← map_mul, ← map_mul,
      hcomm.eq]
  have hmul : (g₁ * g₂)⁻¹ * g₃ ∈ Subgroup.center _ := by
    apply QuotientGroup.eq.1
    rw [QuotientGroup.mk_mul, ← hφu, ← hφv, ← hφuv, ← map_mul]
  have hne' : refl b v₁ ≠ refl b v₂ := by
    intro h
    apply hne
    apply φ.injective
    rw [hφu, hφv, Subtype.ext (hr₁.symm.trans (h.trans hr₂))]
  have hc := coe_eq_of_mem_center hsym hnd hn hv₁ hcom
  have hm := coe_eq_of_mem_center hsym hnd hn hv₁ hmul
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hr₁, ← hr₂, ← hr₃, mul_inv_rev,
    refl_inv] at hc hm
  rcases perp_or_refl_eq_of_commutator_eq_pm_one hsym (by omega) hv₁ hv₂ hc with hperp | heq
  · exact not_refl_mul_refl_eq_pm_refl hsym hn hv₁ hv₂ hv₃ hperp hm
  · exact hne' heq

end Five

theorem not_fischerCentralQuotientModel_five_of_isSymplecticTransvection {X : Type} [Group X]
    {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥)
    {s : X} (hs : s ∈ E) {m f : ℕ} (hf : 2 ≤ f) (h : SevenK.IsSymplecticTransvection X m f s)
    {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ¬ CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) :=
  fun hM => not_meetsSq_of_fischerCentralQuotientModel_five hn hsym hnd hM
    (Fourteen.meetsSq_of_isSymplecticTransvection hcls hZ hs hf h)

theorem not_isFiveReflectionModel_of_isSymplecticTransvection {X : Type} [Group X]
    {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥)
    {s : X} (hs : s ∈ E) {m f : ℕ} (hf : 2 ≤ f) (h : SevenK.IsSymplecticTransvection X m f s)
    {k : ℕ} (hk : 3 ≤ k) {ε π : Bool} : ¬ PartThree.IsFiveReflectionModel k ε π E := by
  intro hM
  obtain ⟨b, hsym, hnd, hM'⟩ := PartThree.fischerModel_of_isFiveReflectionModel hM
  exact not_fischerCentralQuotientModel_five_of_isSymplecticTransvection hcls hZ hs hf h
    (by omega) hsym hnd hM'

end CFSG.OddTranspositions.PartFour

end

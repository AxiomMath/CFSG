module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bReduced
public import CFSG.Quasithin.H13.A6S1372L74e

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6L74

variable {G : Type} [Group G]

@[expose] def tr3 (c u : G) : G := u * (c * u * c⁻¹) * (c * c * u * c⁻¹ * c⁻¹)

section Norm

variable {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c : G}
  (hc : c ∈ Subgroup.normalizer (A : Set G))

omit hA in
include hc in
theorem tr3_mem {u : G} (hu : u ∈ A) : tr3 c u ∈ A := by
  have h1 : c * u * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hc u).mp hu
  have h2 : c * c * u * c⁻¹ * c⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hc _).mp h1
    simpa [mul_assoc] using this
  exact A.mul_mem (A.mul_mem hu h1) h2

include hA hc in
theorem tr3_mul {u w : G} (hu : u ∈ A) (hw : w ∈ A) : tr3 c (u * w) = tr3 c u * tr3 c w := by
  have h1 : ∀ x ∈ A, c * x * c⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.mp hc x).mp hx
  have h2 : ∀ x ∈ A, c * c * x * c⁻¹ * c⁻¹ ∈ A := fun x hx => by
    have := h1 _ (h1 x hx)
    simpa [mul_assoc] using this
  have e1 : c * (u * w) * c⁻¹ = (c * u * c⁻¹) * (c * w * c⁻¹) := by group
  have e2 : c * c * (u * w) * c⁻¹ * c⁻¹ = (c * c * u * c⁻¹ * c⁻¹) * (c * c * w * c⁻¹ * c⁻¹) := by
    group
  unfold tr3
  rw [e1, e2]
  set a := c * u * c⁻¹
  set b := c * w * c⁻¹
  set a' := c * c * u * c⁻¹ * c⁻¹
  set b' := c * c * w * c⁻¹ * c⁻¹
  have ha : a ∈ A := h1 u hu
  have hb : b ∈ A := h1 w hw
  have ha' : a' ∈ A := h2 u hu
  have hb' : b' ∈ A := h2 w hw
  calc u * w * (a * b) * (a' * b') = u * (w * a) * b * (a' * b') := by group
    _ = u * (a * w) * b * (a' * b') := by rw [hA w hw a ha]
    _ = u * a * (w * b) * (a' * b') := by group
    _ = u * a * (w * b * a') * b' := by group
    _ = u * a * (a' * (w * b)) * b' := by rw [hA _ (A.mul_mem hw hb) a' ha']
    _ = u * a * a' * (w * b * b') := by group

include hA hc in
theorem tr3_inv {u : G} (hu : u ∈ A) : tr3 c u⁻¹ = (tr3 c u)⁻¹ := by
  have h := tr3_mul hA hc hu (A.inv_mem hu)
  rw [mul_inv_cancel] at h
  have h1 : tr3 c 1 = 1 := by unfold tr3; group
  rw [h1] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

include hA hc in
theorem conj_tr3 (h3 : ∀ x ∈ A, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x) {u : G} (hu : u ∈ A) :
    c * tr3 c u * c⁻¹ = tr3 c u := by
  have h1 : ∀ x ∈ A, c * x * c⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.mp hc x).mp hx
  have h2 : ∀ x ∈ A, c * c * x * c⁻¹ * c⁻¹ ∈ A := fun x hx => by
    have := h1 _ (h1 x hx)
    simpa [mul_assoc] using this
  unfold tr3
  have e : c * (u * (c * u * c⁻¹) * (c * c * u * c⁻¹ * c⁻¹)) * c⁻¹ =
      (c * u * c⁻¹) * (c * c * u * c⁻¹ * c⁻¹) * (c * c * c * u * c⁻¹ * c⁻¹ * c⁻¹) := by group
  rw [e, h3 u hu]
  have ha := h1 u hu
  have ha' := h2 u hu
  calc c * u * c⁻¹ * (c * c * u * c⁻¹ * c⁻¹) * u
      = u * (c * u * c⁻¹ * (c * c * u * c⁻¹ * c⁻¹)) := hA _ (A.mul_mem ha ha') u hu
    _ = u * (c * u * c⁻¹) * (c * c * u * c⁻¹ * c⁻¹) := by group

include hA hc in
theorem tr3_conj_pow (h3 : ∀ x ∈ A, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x) {u : G} (hu : u ∈ A)
    (j : ℕ) : tr3 c (c ^ j * u * (c ^ j)⁻¹) = tr3 c u := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : c ^ (j + 1) * u * (c ^ (j + 1))⁻¹ = c * (c ^ j * u * (c ^ j)⁻¹) * c⁻¹ := by
      rw [pow_succ']
      group
    have e2 : ∀ x : G, tr3 c (c * x * c⁻¹) = c * tr3 c x * c⁻¹ := fun x => by
      unfold tr3
      group
    rw [e, e2, ih, conj_tr3 hA hc h3 hu]

include hA hc in
theorem tr3_comm_pow (h3 : ∀ x ∈ A, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x) {u : G} (hu : u ∈ A)
    (j : ℕ) : tr3 c (c ^ j * u * (c ^ j)⁻¹ * u⁻¹) = 1 := by
  have hm : c ^ j * u * (c ^ j)⁻¹ ∈ A := by
    have hcj : c ^ j ∈ Subgroup.normalizer (A : Set G) := (Subgroup.normalizer _).pow_mem hc j
    exact (Subgroup.mem_normalizer_iff.mp hcj u).mp hu
  rw [tr3_mul hA hc hm (A.inv_mem hu), tr3_inv hA hc hu, tr3_conj_pow hA hc h3 hu, mul_inv_cancel]

omit hA hc in
theorem eq_mul_of_tr3 {u v : G} (hu2 : u * u = 1) (hv2 : v * v = 1) (hcu : c * u * c⁻¹ = u * v)
    (hcv : c * v * c⁻¹ = v) (huv : u * v = v * u) : tr3 c u = u * v := by
  unfold tr3
  have e : c * c * u * c⁻¹ * c⁻¹ = c * (c * u * c⁻¹) * c⁻¹ := by group
  have e2 : c * (u * v) * c⁻¹ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
  rw [e, hcu, e2, hcu, hcv]
  calc u * (u * v) * (u * v * v) = (u * u) * v * (u * (v * v)) := by group
    _ = v * u := by rw [hu2, hv2]; group
    _ = u * v := huv.symm

include hA hc in
theorem exists_tr3Pre (B : Subgroup G) :
    ∃ P : Subgroup G, ∀ u, u ∈ P ↔ u ∈ A ∧ tr3 c u ∈ B := by
  refine ⟨{ carrier := {u | u ∈ A ∧ tr3 c u ∈ B}
            one_mem' := ⟨A.one_mem, by
              have h1 : tr3 c 1 = 1 := by unfold tr3; group
              rw [h1]
              exact B.one_mem⟩
            mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
              show tr3 c (a * b) ∈ B
              rw [tr3_mul hA hc ha.1 hb.1]
              exact B.mul_mem ha.2 hb.2⟩
            inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
              show tr3 c a⁻¹ ∈ B
              rw [tr3_inv hA hc ha.1]
              exact B.inv_mem ha.2⟩ }, fun u => Iff.rfl⟩

end Norm

variable [Finite G]

theorem exists_minimal_reduced {K X X' W : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXX' : X ≤ X')
    (hX'X : X' ≤ Subgroup.normalizer (X : Set G)) (hX'W : X' ≤ Subgroup.normalizer (W : Set G))
    (hWe : IsElemAbelian 2 W) (hW1 : W ≠ ⊥) (hK : ¬ K ≤ pCoreOf 2 K)
    (hfpf : ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ → X' ≤ Subgroup.normalizer (U : Set G) →
      K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K) :
    ∃ U : Subgroup G, U ≤ W ∧ U ≠ ⊥ ∧ X' ≤ Subgroup.normalizer (U : Set G) ∧
      pCoreOf 2 X ≤ Subgroup.centralizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, -, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun U' : Subgroup G => U' ≤ W ∧ U' ≠ ⊥ ∧ X' ≤ Subgroup.normalizer (U' : Set G)) W
    ⟨le_rfl, hW1, hX'W⟩
  obtain ⟨⟨hUW, hU1, hX'U⟩, hmin'⟩ := hmin
  refine ⟨U, hUW, hU1, hX'U, ?_⟩
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := hXX'.trans hX'U
  have hUe : IsElemAbelian 2 U := A1b.isElemAbelian_of_le hUW hWe
  have hX'O : X' ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hX'X.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hD : ∀ d ∈ pCoreOf 2 X, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (U : Set G) := by
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  have hkey := A1b.centralizer_inf_centralizer_eq hKX hXK hXU hUe (hfpf U hUW hU1 hX'U)
    (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X) hD
  have hne : U ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≠ ⊥ := by
    intro h
    rw [h] at hkey
    apply hK
    rw [← hkey]
    intro k hk
    refine ⟨hk, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  have hX'C : X' ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf_of (hX'U hg) (InternalSec.le_normalizer_centralizer hX'O hg)
  have hle := hmin' ⟨inf_le_left.trans hUW, hne, hX'C⟩ inf_le_left
  exact Subgroup.le_centralizer_iff.mp (hle.trans inf_le_right)

theorem exists_pow_of_card_three {K : Subgroup G} (h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3)
    {k : G} (hk : k ∈ K) (hkO : k ∉ pCoreOf 2 K) {g : G} (hg : g ∈ K) :
    ∃ i : ℕ, (k ^ i)⁻¹ * g ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk1 : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => hkO ((mem_pCoreOf_iff _).2 h)
  have hord : orderOf (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    refine orderOf_eq_prime ?_ hk1
    rw [← h3]
    exact pow_card_eq_one'
  have htop : Subgroup.zpowers (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, h3]
  have hmem : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨k, hk⟩) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hmem)
  refine ⟨i, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hi
  have h := (mem_pCoreOf_iff _).2 hi
  simpa using h

end A6L74

end CFSG.Quasithin.H13.A6

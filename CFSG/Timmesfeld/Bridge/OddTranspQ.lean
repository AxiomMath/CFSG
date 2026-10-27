module

public import CFSG.Timmesfeld.Bridge.OddTranspThird
public import CFSG.Timmesfeld.Bridge.OddTranspSimple
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

namespace ThirdKindHyp

variable {S : Sylow 2 G} {a b c : G} {n : ℕ} (h : ThirdKindHyp G D S a b c n)
include h

omit h in
theorem conj_mem_sylowCommutator {q y : G} (hq : q ∈ CFSG.pCore 2 G)
    (hy : y ∈ sylowCommutator D S) : q * y * q⁻¹ ∈ sylowCommutator D S := by
  refine Asc72.conj_mem_closure ?_ hy
  rintro w ⟨v, hv, hw⟩
  refine ⟨v, hv, ?_⟩
  have hn := Subgroup.normalizer_commutator_ge_left (H₁ := CFSG.pCore 2 G)
    (H₂ := Subgroup.zpowers v) hq
  exact (Subgroup.mem_normalizer_iff.mp hn w).mp hw

theorem exists_mul_of_commute [Finite G] {v y : G} (hv : v ∈ D ∩ (S : Set G))
    (hy : y ∈ CFSG.pCore 2 G) (hyv : Commute y v) :
    ∃ x ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆, ∃ w ∈ CFSG.pCore 2 G ⊓ Subgroup.center G,
      y = x * w := by
  obtain ⟨x, hx, w, hwQ, hwv, hwb, rfl⟩ := exists_commutator_mul_of_commute h.oddT h.normal
    isPGroup_pCore hv.1 h.b_mem (h.not_commute_b hv) hy hyv
  refine ⟨x, hx, w, ⟨hwQ, ?_⟩, rfl⟩
  exact h.mem_center_of_commute hwb.symm fun u hu => (h.commute_of_commute hv hu hwQ hwv).symm

theorem commute_of_commute_a [Finite G] {y y' : G} (hy : y ∈ CFSG.pCore 2 G)
    (hy' : y' ∈ CFSG.pCore 2 G) (hya : Commute y a) (hy'a : Commute y' a) : Commute y y' := by
  obtain ⟨x, hx, w, hw, rfl⟩ := h.exists_mul_of_commute h.a_mem' hy hya
  obtain ⟨x', hx', w', hw', rfl⟩ := h.exists_mul_of_commute h.a_mem' hy' hy'a
  have hxx' : Commute x x' :=
    commute_of_mem_commutator_self h.oddT h.normal isPGroup_pCore h.tri.1 hx hx'
  have hwc := Subgroup.mem_center_iff.mp hw.2
  have hw'c := Subgroup.mem_center_iff.mp hw'.2
  exact (hxx'.mul_right (show Commute x w' from hw'c x)).mul_left
    ((show Commute w x' from (hwc x').symm).mul_right (show Commute w w' from hw'c w))

theorem commute_of_mem_sylowCommutator' [Finite G] {y y' : G} (hy : y ∈ sylowCommutator D S)
    (hy' : y' ∈ sylowCommutator D S) : Commute y y' :=
  h.commute_of_commute_a (sylowCommutator_le hy) (sylowCommutator_le hy')
    (h.commute_of_mem_sylowCommutator h.a_mem' hy).symm
    (h.commute_of_mem_sylowCommutator h.a_mem' hy').symm

theorem mem_center_of_mem_inf [Finite G] {y : G}
    (hy : y ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) :
    y ∈ Subgroup.center G ∧ ∀ v ∈ D ∩ (S : Set G), y ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆ := by
  have hyb : Commute b y :=
    commute_of_mem_commutator h.oddT h.normal isPGroup_pCore h.b_mem h.b_mem (Commute.refl b)
      hy.2
  refine ⟨h.mem_center_of_commute hyb fun v hv => h.commute_of_mem_sylowCommutator hv hy.1,
    fun v hv => ?_⟩
  exact mem_commutator_of_commute h.oddT h.normal isPGroup_pCore hv.1 h.b_mem
    (h.not_commute_b hv) hy.2 (h.commute_of_mem_sylowCommutator hv hy.1).symm

omit h in
theorem commutatorElement_mem_inf {u w : G} (hu : u ∈ sylowCommutator D S)
    (hw : w ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) :
    ⁅u, w⁆ ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ ∧
      ⁅w, u⁆ ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ := by
  have huQ : u ∈ CFSG.pCore 2 G := sylowCommutator_le hu
  have hwQ : w ∈ CFSG.pCore 2 G := Subgroup.commutator_le_left _ _ hw
  have hnb := Subgroup.normalizer_commutator_ge_left (H₁ := CFSG.pCore 2 G)
    (H₂ := Subgroup.zpowers b) huQ
  have h1 : ⁅u, w⁆ ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ := by
    constructor
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      have := conj_mem_sylowCommutator hwQ (Subgroup.inv_mem _ hu)
      exact Subgroup.mul_mem _ hu (by simpa [mul_assoc] using this)
    · rw [commutatorElement_def]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hnb w).mp hw)
        (Subgroup.inv_mem _ hw)
  refine ⟨h1, ?_⟩
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h1

theorem commutator_mem [Finite G] {p q : G} (hp : p ∈ CFSG.pCore 2 G)
    (hq : q ∈ CFSG.pCore 2 G) :
    ⁅p, q⁆ ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ := by
  have hz := Subgroup.mem_center_iff.mp h.z_mem_center
  have hcl : ∀ x y : G, ⁅x * (a * c * b) ^ n, y⁆ = ⁅x, y⁆ := by
    intro x y
    rw [commutatorElement_def, commutatorElement_def, mul_assoc x _ y, ← hz y, ← mul_assoc]
    group
  have hcr : ∀ x y : G, ⁅x, y * (a * c * b) ^ n⁆ = ⁅x, y⁆ := by
    intro x y
    rw [← commutatorElement_inv, hcl, commutatorElement_inv]
  have hred : ∀ p₀ ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q₀ ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      ⁅p₀, q₀⁆ ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ := by
    intro p₀ hp₀ q₀ hq₀
    have hnorm : sylowCommutator D S ≤
        Subgroup.normalizer ((⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ : Subgroup G) : Set G) :=
      sylowCommutator_le.trans (Subgroup.normalizer_commutator_ge_left _ _)
    have hprod := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
    rw [h.commutator_top_eq] at hp₀ hq₀
    have hp₀' : p₀ ∈ (↑(sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) : Set G) := hp₀
    have hq₀' : q₀ ∈ (↑(sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) : Set G) := hq₀
    rw [hprod] at hp₀' hq₀'
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Set.mem_mul.mp hp₀'
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hq₀'
    have hM : ∀ m ∈ sylowCommutator D S ⊓ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆, ∀ g : G,
        g * m = m * g := fun m hm g =>
      Subgroup.mem_center_iff.mp (h.mem_center_of_mem_inf hm).1 g
    have h1 := (commutatorElement_mem_inf (D := D) (S := S) hx₁ hy₂).1
    have h2 := (commutatorElement_mem_inf (D := D) (S := S) hx₂ hy₁).2
    have hxx : ⁅x₁, x₂⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
      (h.commute_of_mem_sylowCommutator' hx₁ hx₂)
    have hyy : ⁅y₁, y₂⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
      (commute_of_mem_commutator_self h.oddT h.normal isPGroup_pCore h.b_mem hy₁ hy₂)
    have e1 : ⁅y₁, x₂ * y₂⁆ = ⁅y₁, x₂⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hyy, mul_one, mul_inv_cancel_right]
    have e2 : ⁅x₁, x₂ * y₂⁆ = ⁅x₁, y₂⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hxx, one_mul, hM _ h1 x₂,
        mul_inv_cancel_right]
    have e : ⁅x₁ * y₁, x₂ * y₂⁆ = ⁅y₁, x₂⁆ * ⁅x₁, y₂⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, e1, e2, hM _ h2 x₁, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ h2 h1
  rcases h.mem_or_mul_mem hp with hp₀ | hp₀ <;> rcases h.mem_or_mul_mem hq with hq₀ | hq₀
  · exact hred p hp₀ q hq₀
  · have := hred p hp₀ _ hq₀
    rwa [hcr] at this
  · have := hred _ hp₀ q hq₀
    rwa [hcl] at this
  · have := hred _ hp₀ _ hq₀
    rwa [hcl, hcr] at this

theorem mem_sylowCommutator_of_commute [Finite G] {w₀ : G}
    (hw₀ : w₀ ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆) (hw₀a : Commute w₀ a) :
    w₀ ∈ sylowCommutator D S := by
  have hnorm : sylowCommutator D S ≤
      Subgroup.normalizer ((⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ : Subgroup G) : Set G) :=
    sylowCommutator_le.trans (Subgroup.normalizer_commutator_ge_left _ _)
  rw [h.commutator_top_eq] at hw₀
  have hw₀' : w₀ ∈ (↑(sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) : Set G) :=
    hw₀
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hw₀'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hw₀'
  have hya : Commute y a := by
    have e : y = x⁻¹ * (x * y) := by group
    rw [e]
    exact (h.commute_of_mem_sylowCommutator h.a_mem' hx).symm.inv_left.mul_left hw₀a
  have hyQa := mem_commutator_of_commute h.oddT h.normal isPGroup_pCore h.tri.1 h.b_mem
    (h.not_commute_b h.a_mem') hy hya
  exact Subgroup.mul_mem _ hx (Subgroup.subset_closure ⟨a, h.a_mem', hyQa⟩)

omit h in
theorem sylowCommutator_le_iSup :
    sylowCommutator D S ≤ ⨆ v ∈ D ∩ (S : Set G), ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆ := by
  rw [sylowCommutator, Subgroup.closure_le]
  rintro y ⟨v, hv, hy⟩
  exact Subgroup.mem_iSup_of_mem v (Subgroup.mem_iSup_of_mem hv hy)

theorem center_le_iSup [Finite G] (hperf : commutator G = ⊤) :
    CFSG.pCore 2 G ⊓ Subgroup.center G ≤
      ⨆ v ∈ D ∩ (S : Set G), ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆ := by
  rintro w ⟨hwQ, hwc⟩
  have hQQ : CFSG.pCore 2 G ≤ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ := by
    have h1 := h.npc ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ inferInstance
      (Subgroup.commutator_le_left _ _) le_rfl
    rw [hperf, inf_top_eq] at h1
    exact h1
  exact sylowCommutator_le_iSup (h.mem_sylowCommutator_of_commute (hQQ hwQ)
    (Subgroup.mem_center_iff.mp hwc a).symm)

theorem commute_of_mem_of_abelian [Finite G]
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {p q : G} (hp : p ∈ CFSG.pCore 2 G) (hq : q ∈ CFSG.pCore 2 G) :
    Commute p q := by
  have hz := Subgroup.mem_center_iff.mp h.z_mem_center
  have hzc : ∀ g : G, Commute ((a * c * b) ^ n)⁻¹ g := fun g =>
    (show Commute g ((a * c * b) ^ n) from hz g).symm.inv_left
  have hl : ∀ x y : G, Commute (x * (a * c * b) ^ n) y → Commute x y := by
    intro x y hxy
    have e : x = x * (a * c * b) ^ n * ((a * c * b) ^ n)⁻¹ := by group
    rw [e]
    exact hxy.mul_left (hzc y)
  have hr : ∀ x y : G, Commute x (y * (a * c * b) ^ n) → Commute x y := fun x y hxy =>
    (hl y x hxy.symm).symm
  rcases h.mem_or_mul_mem hp with h0 | h0 <;> rcases h.mem_or_mul_mem hq with h0' | h0'
  · exact hQab _ h0 _ h0'
  · exact hr _ _ (hQab _ h0 _ h0')
  · exact hl _ _ (hQab _ h0 _ h0')
  · exact hl _ _ (hr _ _ (hQab _ h0 _ h0'))

theorem mul_self_eq_one_of_mem_commutator [Finite G] {v y : G} (hv : v ∈ D)
    (hy : y ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆) : y * y = 1 := by
  have hcomm : ∀ y₁ ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆,
      ∀ y₂ ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆, Commute y₁ y₂ := fun y₁ hy₁ y₂ hy₂ =>
    commute_of_mem_commutator_self h.oddT h.normal isPGroup_pCore hv hy₁ hy₂
  have hv2 := h.oddT.mul_self_eq_one hv
  rw [Subgroup.commutator_def] at hcomm hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q, hq, t, ht, rfl⟩ := hx
    rcases (mem_zpowers_of_mul_self hv2).mp ht with h1 | h1
    · rw [h1, commutatorElement_one_right, mul_one]
    · rw [h1]
      have hc := commute_conj_of_mem h.oddT h.normal isPGroup_pCore hv hq
        (CFSG.pCore 2 G).one_mem
      simp only [one_mul, inv_one, mul_one] at hc
      rw [commutatorElement_def, h.oddT.inv_eq hv]
      calc q * v * q⁻¹ * v * (q * v * q⁻¹ * v) = q * v * q⁻¹ * (v * (q * v * q⁻¹)) * v := by
            group
        _ = q * v * q⁻¹ * (q * v * q⁻¹) * (v * v) := by rw [← hc.eq]; group
        _ = 1 := by
          rw [hv2, mul_one]
          calc q * v * q⁻¹ * (q * v * q⁻¹) = q * (v * v) * q⁻¹ := by group
            _ = 1 := by rw [hv2, mul_one, mul_inv_cancel]
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    rw [show x * y * (x * y) = x * x * (y * y) by
      rw [mul_assoc x y, ← mul_assoc y x, ← (hcomm x hx y hy).eq]; group, ihx, ihy, mul_one]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

theorem mul_self_eq_one_of_abelian [Finite G]
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {q : G} (hq : q ∈ CFSG.pCore 2 G) : q * q = 1 := by
  have hcQ : ∀ {p q : G}, p ∈ CFSG.pCore 2 G → q ∈ CFSG.pCore 2 G → Commute p q :=
    fun hp hq => h.commute_of_mem_of_abelian hQab hp hq
  have hQ₁ : ∀ y ∈ sylowCommutator D S, y * y = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hx⟩ := hx
      exact h.mul_self_eq_one_of_mem_commutator hv.1 hx
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      rw [show x * y * (x * y) = x * x * (y * y) by
        rw [mul_assoc x y, ← mul_assoc y x, ← (hcQ (sylowCommutator_le hx)
          (sylowCommutator_le hy)).eq]; group, ihx, ihy, mul_one]
    | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]
  have hred : ∀ q₀ ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, q₀ * q₀ = 1 := by
    intro q₀ hq₀
    have hnorm : sylowCommutator D S ≤
        Subgroup.normalizer ((⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆ : Subgroup G) : Set G) :=
      sylowCommutator_le.trans (Subgroup.normalizer_commutator_ge_left _ _)
    rw [h.commutator_top_eq] at hq₀
    have hq₀' : q₀ ∈ (↑(sylowCommutator D S ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers b⁆) : Set G) :=
      hq₀
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hq₀'
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hq₀'
    have hxy : Commute x y := hcQ (sylowCommutator_le hx) (Subgroup.commutator_le_left _ _ hy)
    rw [show x * y * (x * y) = x * x * (y * y) by
      rw [mul_assoc x y, ← mul_assoc y x, ← hxy.eq]; group, hQ₁ x hx,
      h.mul_self_eq_one_of_mem_commutator h.b_mem hy, mul_one]
  obtain ⟨hzz, -⟩ := h.z_spec
  have hz := Subgroup.mem_center_iff.mp h.z_mem_center
  rcases h.mem_or_mul_mem hq with h0 | h0
  · exact hred q h0
  · have h1 := hred _ h0
    have e : q * q = q * (a * c * b) ^ n * (q * (a * c * b) ^ n) := by
      rw [show q * (a * c * b) ^ n * (q * (a * c * b) ^ n) =
          q * ((a * c * b) ^ n * q) * (a * c * b) ^ n by group, ← hz q]
      rw [show q * (q * (a * c * b) ^ n) * (a * c * b) ^ n =
          q * q * ((a * c * b) ^ n * (a * c * b) ^ n) by group, hzz, mul_one]
    rw [e, h1]

theorem exists_eq_commutatorElement [Finite G]
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {d x : G} (hd : d ∈ D) (hx : x ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers d⁆) :
    ∃ q ∈ CFSG.pCore 2 G, x = ⁅d, q⁆ := by
  have hcQ : ∀ {p q : G}, p ∈ CFSG.pCore 2 G → q ∈ CFSG.pCore 2 G → Commute p q :=
    fun hp hq => h.commute_of_mem_of_abelian hQab hp hq
  have hdQ : ∀ q ∈ CFSG.pCore 2 G, d * q * d⁻¹ ∈ CFSG.pCore 2 G := fun q hq =>
    (CFSG.pCore_normal (p := 2) (G := G)).conj_mem q hq d
  have hmul : ∀ q₁ ∈ CFSG.pCore 2 G, ∀ q₂ ∈ CFSG.pCore 2 G,
      ⁅d, q₁⁆ * ⁅d, q₂⁆ = ⁅d, q₁ * q₂⁆ := by
    intro q₁ hq₁ q₂ hq₂
    simp only [commutatorElement_def]
    have h1 : Commute q₁⁻¹ (d * q₂ * d⁻¹) := hcQ (Subgroup.inv_mem _ hq₁) (hdQ q₂ hq₂)
    have h2 : Commute q₁⁻¹ q₂⁻¹ := hcQ (Subgroup.inv_mem _ hq₁) (Subgroup.inv_mem _ hq₂)
    calc d * q₁ * d⁻¹ * q₁⁻¹ * (d * q₂ * d⁻¹ * q₂⁻¹) =
        d * q₁ * d⁻¹ * (q₁⁻¹ * (d * q₂ * d⁻¹)) * q₂⁻¹ := by group
      _ = d * q₁ * d⁻¹ * ((d * q₂ * d⁻¹) * q₁⁻¹) * q₂⁻¹ := by rw [h1.eq]
      _ = d * (q₁ * q₂) * d⁻¹ * (q₁⁻¹ * q₂⁻¹) := by group
      _ = d * (q₁ * q₂) * d⁻¹ * (q₁ * q₂)⁻¹ := by rw [h2.eq, mul_inv_rev]
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q, hq, t, ht, rfl⟩ := hy
    rcases (mem_zpowers_of_mul_self (h.oddT.mul_self_eq_one hd)).mp ht with h1 | h1
    · exact ⟨1, Subgroup.one_mem _, by rw [h1]; simp⟩
    · refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_⟩
      rw [h1]
      have h2 : Commute q (d * q⁻¹ * d⁻¹) := hcQ hq (hdQ _ (Subgroup.inv_mem _ hq))
      simp only [commutatorElement_def, inv_inv]
      calc q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) := by group
        _ = d * q⁻¹ * d⁻¹ * q := h2.eq
  | one => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨q₁, hq₁, rfl⟩ := ihx
    obtain ⟨q₂, hq₂, rfl⟩ := ihy
    exact ⟨q₁ * q₂, Subgroup.mul_mem _ hq₁ hq₂, hmul q₁ hq₁ q₂ hq₂⟩
  | inv x _ ih =>
    obtain ⟨q, hq, rfl⟩ := ih
    refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    have h1 := hmul q hq q⁻¹ (Subgroup.inv_mem _ hq)
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact (eq_inv_of_mul_eq_one_right h1).symm

omit h in
theorem mem_pCore_of_mem_center {g : G}
    (hg : QuotientGroup.mk' (CFSG.pCore 2 G) g ∈ Subgroup.center (G ⧸ CFSG.pCore 2 G))
    (hg2 : g * g ∈ CFSG.pCore 2 G) : g ∈ CFSG.pCore 2 G := by
  set r := QuotientGroup.mk' (CFSG.pCore 2 G) g with hrdef
  have hr2 : r * r = 1 := by
    rw [hrdef, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg2
  have hle : Subgroup.zpowers r ≤ Subgroup.center (G ⧸ CFSG.pCore 2 G) :=
    Subgroup.zpowers_le.mpr hg
  have hn : (Subgroup.zpowers r).Normal := Subgroup.normal_of_le_center hle
  have h2 : IsPGroup 2 (Subgroup.zpowers r) := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases (mem_zpowers_of_mul_self hr2).mp hy with rfl | rfl
    · simp
    · simp [pow_two, hr2]
  have hbot := eq_bot_of_isPGroup_quotient_pCore _ hn h2
  have hr1 : r = 1 := by
    have := Subgroup.mem_zpowers r
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact (QuotientGroup.eq_one_iff g).mp hr1

theorem exists_mul_of_involution [Finite G] (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G))
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {s : G} (hsS : s ∈ S) (hs2 : orderOf s = 2) (hsQ : s ∉ CFSG.pCore 2 G) :
    ∃ d ∈ D ∩ (S : Set G), ∃ w ∈ CFSG.pCore 2 G ⊓ Subgroup.center G, s = d * w := by
  have hs1 : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hsZ : s ∉ zStar G := fun hs => hsQ (mem_pCore_of_mem_center hs
    (by rw [hs1]; exact Subgroup.one_mem _))
  have hDZ : ∀ d ∈ D, d ∉ zStar G := by
    rcases h.setup.subset_or_disjoint (zStar G) with h' | h'
    · exfalso
      have htop := h.setup.eq_top_of_subset _ h'
      have := (IsBenderGroup.isSimpleGroup hB).toNontrivial
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (G ⧸ zStar G)
      apply hxy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zStar G) x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (zStar G) y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact htop ▸ Subgroup.mem_top _
    · exact h'
  set π := QuotientGroup.mk' (zStar G) with hπdef
  have hord : ∀ g : G, g * g = 1 → g ∉ zStar G → orderOf (π g) = 2 := by
    intro g hg hgZ
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hg, map_one]
    · intro h1
      exact hgZ ((QuotientGroup.eq_one_iff g).mp h1)
  obtain ⟨d₀, hd₀⟩ := h.setup.nonempty
  obtain ⟨cq, hcq⟩ := isConj_iff.mp (Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB
    (hord d₀ (h.oddT.mul_self_eq_one hd₀) (hDZ d₀ hd₀)) (hord s hs1 hsZ))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zStar G) cq
  set d := g * d₀ * g⁻¹ with hddef
  have hd : d ∈ D := h.setup.conj_mem g hd₀
  have hdsZ : d⁻¹ * s ∈ zStar G := by
    have hπd : π d = π s := by rw [hddef, map_mul, map_mul, map_inv]; exact hcq
    have h1 : π (d⁻¹ * s) = 1 := by rw [map_mul, map_inv, hπd, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hdi : d⁻¹ = d := h.oddT.inv_eq hd
  have hrQ : d⁻¹ * s ∈ CFSG.pCore 2 G := by
    refine mem_pCore_of_mem_center hdsZ ?_
    set ρ := QuotientGroup.mk' (CFSG.pCore 2 G) with hρdef
    have hc := Subgroup.mem_center_iff.mp hdsZ
    have h1 : ρ (d * (d⁻¹ * s) * (d * (d⁻¹ * s))) = 1 := by
      rw [show d * (d⁻¹ * s) * (d * (d⁻¹ * s)) = s * s by group, hs1, map_one]
    have h2 : ρ (d * (d⁻¹ * s) * (d * (d⁻¹ * s))) = ρ (d * d) * ρ ((d⁻¹ * s) * (d⁻¹ * s)) := by
      generalize d⁻¹ * s = r at hc ⊢
      rw [map_mul ρ (d * r) (d * r), map_mul ρ d r, map_mul ρ d d, map_mul ρ r r,
        mul_assoc (ρ d) (ρ r), ← mul_assoc (ρ r) (ρ d), ← hc (ρ d)]
      simp only [hρdef]
      group
    rw [h2, h.oddT.mul_self_eq_one hd, map_one, one_mul] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hdS : d ∈ S := by
    have h1 := S.mul_mem hsS (S.inv_mem (pCore_le hrQ))
    have e : s * (d⁻¹ * s)⁻¹ = d := by group
    rw [e] at h1
    exact h1
  have hy2 := h.mul_self_eq_one_of_abelian hQab hrQ
  have hd2 := h.oddT.mul_self_eq_one hd
  have hyi : (d⁻¹ * s)⁻¹ = d⁻¹ * s := inv_eq_of_mul_eq_one_right hy2
  have h1 : d * (d⁻¹ * s) * d * (d⁻¹ * s) = 1 := by
    rw [show d * (d⁻¹ * s) * d * (d⁻¹ * s) = s * d * (d⁻¹ * s) by group,
      show s * d * (d⁻¹ * s) = s * s by group, hs1]
  have h2 : d * (d⁻¹ * s) * d = d⁻¹ * s := by
    have := eq_inv_of_mul_eq_one_left h1
    rwa [hyi] at this
  have hyd : Commute (d⁻¹ * s) d := by
    show d⁻¹ * s * d = d * (d⁻¹ * s)
    calc d⁻¹ * s * d = d * (d⁻¹ * s) * d * d := by rw [h2]
      _ = d * (d⁻¹ * s) := by rw [mul_assoc (d * (d⁻¹ * s)), hd2, mul_one]
  obtain ⟨x, hx, w, hw, hyxw⟩ := h.exists_mul_of_commute ⟨hd, hdS⟩ hrQ hyd
  obtain ⟨q, hq, rfl⟩ := h.exists_eq_commutatorElement hQab hd hx
  refine ⟨q * d * q⁻¹, ⟨h.normal q d hd, S.mul_mem (S.mul_mem (pCore_le hq) hdS)
    (S.inv_mem (pCore_le hq))⟩, w, hw, ?_⟩
  calc s = d * (d⁻¹ * s) := by group
    _ = d * (⁅d, q⁆ * w) := by rw [hyxw]
    _ = d * d * q * d⁻¹ * q⁻¹ * w := by rw [commutatorElement_def]; group
    _ = q * d * q⁻¹ * w := by rw [hd2, one_mul, hdi]

theorem center_le_sup_of_closure [Finite G] (hperf : commutator G = ⊤)
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {α β x : G} (hα : α ∈ D ∩ (S : Set G)) (hβ : β ∈ D ∩ (S : Set G)) (hx : x ∈ D)
    (hgen : Subgroup.closure {α, β, x} ⊔ CFSG.pCore 2 G = ⊤) :
    CFSG.pCore 2 G ⊓ Subgroup.center G ≤
      ⁅CFSG.pCore 2 G, Subgroup.zpowers α⁆ ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers β⁆ := by
  have hQ : IsPGroup 2 (CFSG.pCore 2 G) := isPGroup_pCore
  have hcQ : ∀ {p q : G}, p ∈ CFSG.pCore 2 G → q ∈ CFSG.pCore 2 G → Commute p q :=
    fun hp hq => h.commute_of_mem_of_abelian hQab hp hq
  have hQ2 : ∀ {q : G}, q ∈ CFSG.pCore 2 G → q * q = 1 :=
    fun hq => h.mul_self_eq_one_of_abelian hQab hq
  set Q := CFSG.pCore 2 G with hQdef
  set Qα := ⁅Q, Subgroup.zpowers α⁆ with hQαdef
  set Qβ := ⁅Q, Subgroup.zpowers β⁆ with hQβdef
  set Qx := ⁅Q, Subgroup.zpowers x⁆ with hQxdef
  have hQαQ : Qα ≤ Q := Subgroup.commutator_le_left _ _
  have hQβQ : Qβ ≤ Q := Subgroup.commutator_le_left _ _
  have hQxQ : Qx ≤ Q := Subgroup.commutator_le_left _ _
  have hQQ : Q ≤ ⁅Q, (⊤ : Subgroup G)⁆ := by
    have h1 := h.npc ⁅Q, (⊤ : Subgroup G)⁆ inferInstance (Subgroup.commutator_le_left _ _) le_rfl
    rw [hperf, inf_top_eq] at h1
    exact h1
  have hT : Subgroup.closure ({α, β, x} ∪ (Q : Set G)) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, hgen]
  have hle : ⁅Q, (⊤ : Subgroup G)⁆ ≤ Qα ⊔ Qβ ⊔ Qx := by
    refine commutator_le_of_closure (sup_le (sup_le hQαQ hQβQ) hQxQ) hT ?_ ?_
    · rintro t (ht | ht)
      · rcases ht with rfl | rfl | rfl
        · exact h.oddT.mul_self_eq_one hα.1
        · exact h.oddT.mul_self_eq_one hβ.1
        · exact h.oddT.mul_self_eq_one hx
      · exact hQ2 ht
    · rintro t (ht | ht) q hq
      · rcases ht with rfl | rfl | rfl
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
            (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _)))
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
            (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _)))
        · exact Subgroup.mem_sup_right
            (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers _))
      · rw [commutatorElement_eq_one_iff_commute.mpr (hcQ hq ht)]
        exact Subgroup.one_mem _
  have hαx : ¬ Commute α x := by
    intro hc
    have hab := h.commute_of_mem hα hβ
    have hCG : ∀ g : G, ∃ q ∈ Q, ∃ k : G, Commute k α ∧ g = q * k := by
      intro g
      have hg : g ∈ Subgroup.closure {α, β, x} ⊔ Q := hgen ▸ Subgroup.mem_top g
      have hnorm : Subgroup.closure ({α, β, x} : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
        fun k _ => Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy =>
          (CFSG.pCore_normal (p := 2) (G := G)).conj_mem y hy k, fun hy => by
            have := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ hy k⁻¹
            simpa [mul_assoc] using this⟩
      have hg' : g ∈ (↑(Subgroup.closure ({α, β, x} : Set G) ⊔ Q) : Set G) := hg
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hg'
      obtain ⟨k, hk, q, hq, rfl⟩ := Set.mem_mul.mp hg'
      refine ⟨k * q * k⁻¹, (CFSG.pCore_normal (p := 2) (G := G)).conj_mem q hq k, k, ?_, by group⟩
      refine Asc72.commute_of_mem_closure (S := {α, β, x}) (T := {α}) ?_ hk
        (Subgroup.subset_closure rfl)
      intro u hu w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
      rw [hw]
      rcases hu with h1 | h1 | h1
      · rw [h1]
      · rw [h1]
        exact hab.symm
      · rw [h1]
        exact hc.symm
    obtain ⟨g, hg⟩ := isConj_iff.mp (h.setup.isConj hα.1 h.b_mem)
    obtain ⟨q, hq, k, hk, rfl⟩ := hCG g
    have hb : b = q * α * q⁻¹ := by
      rw [← hg, mul_inv_rev, show q * k * α * (k⁻¹ * q⁻¹) = q * (k * α * k⁻¹) * q⁻¹ by group,
        hk.eq, mul_inv_cancel_right]
    have hαb : α * b⁻¹ ∈ Q := by
      rw [hb, mul_inv_rev, mul_inv_rev, inv_inv, h.oddT.inv_eq hα.1]
      have := Q.mul_mem ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ hq α) (Q.inv_mem hq)
      rw [h.oddT.inv_eq hα.1] at this
      simpa [mul_assoc] using this
    exact h.not_commute_b hα (commute_of_mul_inv_mem h.oddT hQ hα.1 h.b_mem hαb)
  rintro w ⟨hwQ, hwc⟩
  have hw : w ∈ Qα ⊔ Qβ ⊔ Qx := hle (hQQ hwQ)
  have hn1 : Qα ≤ Subgroup.normalizer (Qβ : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => by
      rw [(hcQ (hQαQ hg) (hQβQ hy)).eq, mul_inv_cancel_right]; exact hy, fun hy => by
      have := hcQ (hQαQ hg) (hQβQ hy)
      have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [e, (hcQ (Q.inv_mem (hQαQ hg)) (hQβQ hy)).eq, inv_mul_cancel_right]; exact hy⟩
  have hn2 : Qα ⊔ Qβ ≤ Subgroup.normalizer (Qx : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => by
      rw [(hcQ (sup_le hQαQ hQβQ hg) (hQxQ hy)).eq, mul_inv_cancel_right]; exact hy, fun hy => by
      have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [e, (hcQ (Q.inv_mem (sup_le hQαQ hQβQ hg)) (hQxQ hy)).eq, inv_mul_cancel_right]
      exact hy⟩
  have hw' : w ∈ (↑(Qα ⊔ Qβ ⊔ Qx) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn2] at hw'
  obtain ⟨y₁, hy₁, y₃, hy₃, rfl⟩ := Set.mem_mul.mp hw'
  have hy₁α : Commute y₁ α := by
    have hy₁' : y₁ ∈ (↑(Qα ⊔ Qβ) : Set G) := hy₁
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn1] at hy₁'
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy₁'
    exact ((commute_of_mem_commutator h.oddT h.normal hQ hα.1 hα.1 (Commute.refl α)
      hu).symm).mul_left
      (commute_of_mem_commutator h.oddT h.normal hQ hβ.1 hα.1 (h.commute_of_mem hα hβ) hv).symm
  have hy₃α : Commute y₃ α := by
    have e : y₃ = y₁⁻¹ * (y₁ * y₃) := by group
    rw [e]
    exact hy₁α.inv_left.mul_left (Subgroup.mem_center_iff.mp hwc α).symm
  have hy₃Qα := mem_commutator_of_commute h.oddT h.normal hQ hα.1 hx hαx hy₃ hy₃α
  have hy₁' : y₁ ∈ (↑(Qα ⊔ Qβ) : Set G) := hy₁
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn1] at hy₁'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy₁'
  rw [mul_assoc, (hcQ (hQβQ hv) (hQαQ hy₃Qα)).eq, ← mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ hu hy₃Qα))
    (Subgroup.mem_sup_right hv)

end ThirdKindHyp

namespace OddTransp

theorem oddTranspCommutatorQ :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G) (S : Sylow 2 G) (a b c : G) (n : ℕ),
      ThirdKindHyp G D S a b c n →
      (∀ p ∈ CFSG.pCore 2 G, ∀ q ∈ CFSG.pCore 2 G, ⁅p, q⁆ ∈ Subgroup.center G) ∧
      ∀ v ∈ D ∩ (S : Set G), ∀ p ∈ CFSG.pCore 2 G, ∀ q ∈ CFSG.pCore 2 G,
        ⁅p, q⁆ ∈ ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆ := by
  intro G _ _ D S a b c n h
  refine ⟨fun p hp q hq => (h.mem_center_of_mem_inf (h.commutator_mem hp hq)).1,
    fun v hv p hp q hq => (h.mem_center_of_mem_inf (h.commutator_mem hp hq)).2 v hv⟩

theorem oddTranspCenterSup :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G) (S : Sylow 2 G) (a b c : G) (n : ℕ),
      ThirdKindHyp G D S a b c n → commutator G = ⊤ →
      CFSG.pCore 2 G ⊓ Subgroup.center G ≤
        ⨆ v ∈ D ∩ (S : Set G), ⁅CFSG.pCore 2 G, Subgroup.zpowers v⁆ :=
  fun _ _ _ _ _ _ _ _ _ h hperf =>
  h.center_le_iSup hperf

end OddTransp

end CFSG.Timmesfeld.Bridge

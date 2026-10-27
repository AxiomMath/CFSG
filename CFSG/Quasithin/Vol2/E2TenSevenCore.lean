module

public import CFSG.Quasithin.Vol2.E2TenSix
public import CFSG.Quasithin.Background.E2TenKG3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

theorem sl2_eq_one_or_neg_one_of_mul_self {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) F} (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have hA' := congrArg
    (fun B : Matrix.SpecialLinearGroup (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F)) hA
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hA'
  have hdet := A.2
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  have e00 : a * a + b * c = 1 := by
    have := congrFun (congrFun hA' 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : a * b + b * d = 0 := by
    have := congrFun (congrFun hA' 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : c * a + d * c = 0 := by
    have := congrFun (congrFun hA' 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : c * b + d * d = 1 := by
    have := congrFun (congrFun hA' 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have ed : a * d - b * c = 1 := by
    rw [Matrix.det_fin_two] at hdet; exact hdet
  by_cases had : a + d = 0
  · exfalso
    have hd : d = -a := by linear_combination had
    have : (2 : F) = 0 := by
      rw [hd] at ed
      linear_combination -(e00 + ed)
    exact h2 this
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h had
    have ha2 : a * a = 1 := by rw [hb, zero_mul, add_zero] at e00; exact e00
    have had' : a * d = 1 := by rw [hb, zero_mul, sub_zero] at ed; exact ed
    have hda : d = a := by
      have : a * (d - a) = 0 := by linear_combination had' - ha2
      rcases mul_eq_zero.1 this with h | h
      · rw [h, mul_zero] at ha2; exact absurd ha2 zero_ne_one
      · linear_combination h
    have ha : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination ha2
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases ha with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, hda, ha] at *
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, hda, ha] at *

section Core

variable {Q : Type} [Group Q] (J₀ : Subgroup Q) [J₀.Normal]

theorem commutator_sup_eq_top (hS : commutator (Q ⧸ J₀) = ⊤) : commutator Q ⊔ J₀ = ⊤ := by
  have hmap : (commutator Q).map (QuotientGroup.mk' J₀) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective J₀), ← commutator_def]
    exact hS
  rw [eq_top_iff]
  intro q _
  have hq : (QuotientGroup.mk' J₀ q) ∈ (commutator Q).map (QuotientGroup.mk' J₀) := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨l, hl, hlq⟩ := hq
  have hj : l⁻¹ * q ∈ J₀ := QuotientGroup.eq.1 hlq
  have : q = l * (l⁻¹ * q) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hl hj

theorem commutatorElement_mul_central_left {x y j : Q} (hj : j ∈ Subgroup.center Q) :
    ⁅x * j, y⁆ = ⁅x, y⁆ := by
  have h : j * y = y * j := (Subgroup.mem_center_iff.1 hj y).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * j * y * (x * j)⁻¹ * y⁻¹ = x * (j * y) * j⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * j) * j⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {x y j : Q} (hj : j ∈ Subgroup.center Q) :
    ⁅x, y * j⁆ = ⁅x, y⁆ := by
  have h : j * x⁻¹ = x⁻¹ * j := (Subgroup.mem_center_iff.1 hj x⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * j) * x⁻¹ * (y * j)⁻¹ = x * y * (j * x⁻¹) * j⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * j) * j⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutator_eq_of_sup_central {L : Subgroup Q} (hJc : J₀ ≤ Subgroup.center Q)
    (hLJ : L ⊔ J₀ = ⊤) : commutator Q = ⁅L, L⁆ := by
  rw [commutator_def]
  apply le_antisymm _ (Subgroup.commutator_mono le_top le_top)
  rw [Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ L ⊔ J₀ := hLJ ▸ Subgroup.mem_top x
  have hy : y ∈ L ⊔ J₀ := hLJ ▸ Subgroup.mem_top y
  obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  obtain ⟨l', hl', j', hj', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
  rw [commutatorElement_mul_central_left (hJc hj), commutatorElement_mul_central_right (hJc hj')]
  exact Subgroup.commutator_mem_commutator hl hl'

theorem map_center_commutator_eq (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) :
    (Subgroup.center (commutator Q)).map (commutator Q).subtype = commutator Q ⊓ J₀ := by
  have hLJ := commutator_sup_eq_top J₀ hS
  have hZ : Subgroup.center (Q ⧸ J₀) = ⊥ := by
    rcases (Subgroup.center (Q ⧸ J₀)).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    have hzc : (QuotientGroup.mk' J₀ (z : Q)) ∈ Subgroup.center (Q ⧸ J₀) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective J₀ s
      have hq : q ∈ commutator Q ⊔ J₀ := hLJ ▸ Subgroup.mem_top q
      obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hq
      have hlz : (⟨l, hl⟩ : commutator Q) * z = z * ⟨l, hl⟩ :=
        Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
      have hlz' : l * (z : Q) = (z : Q) * l := congrArg Subtype.val hlz
      have hjc : j * (z : Q) = (z : Q) * j := (Subgroup.mem_center_iff.1 (hJc hj) z).symm
      rw [← map_mul, ← map_mul]
      congr 1
      calc l * j * (z : Q) = l * (j * z) := by group
        _ = l * (z * j) := by rw [hjc]
        _ = (l * z) * j := by group
        _ = (z * l) * j := by rw [hlz']
        _ = z * (l * j) := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzc
    exact hzc
  · rintro x ⟨hxL, hxJ⟩
    refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hJc hxJ) y)

theorem surjective_restrict_commutator (hS : commutator (Q ⧸ J₀) = ⊤) :
    Function.Surjective ((QuotientGroup.mk' J₀).comp (commutator Q).subtype) := by
  have hLJ := commutator_sup_eq_top J₀ hS
  intro s
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective J₀ s
  have hq : q ∈ commutator Q ⊔ J₀ := hLJ ▸ Subgroup.mem_top q
  obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hq
  refine ⟨⟨l, hl⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : l⁻¹ * (l * j) = j := by group
  rw [this]
  exact hj

theorem ker_restrict_commutator (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) :
    ((QuotientGroup.mk' J₀).comp (commutator Q).subtype).ker =
      Subgroup.center (commutator Q) := by
  have h := map_center_commutator_eq J₀ hJc hS hsimp hna
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    have : (x : Q) ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype :=
      h ▸ ⟨x.2, hx⟩
    obtain ⟨y, hy, hyx⟩ := this
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  · intro hx
    exact (h ▸ ⟨x, hx, rfl⟩ : (x : Q) ∈ commutator Q ⊓ J₀).2

theorem quasisimple_commutator (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) :
    CFSG.IsQuasisimple (commutator Q) ∧
      Nonempty (commutator Q ⧸ Subgroup.center (commutator Q) ≃* Q ⧸ J₀) := by
  set φ := (QuotientGroup.mk' J₀).comp (commutator Q).subtype with hφ
  have hsurj := surjective_restrict_commutator J₀ hS
  have hker := ker_restrict_commutator J₀ hJc hS hsimp hna
  let e : commutator Q ⧸ Subgroup.center (commutator Q) ≃* Q ⧸ J₀ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨e⟩⟩
  ·
    have hLL : commutator Q = ⁅commutator Q, commutator Q⁆ :=
      commutator_eq_of_sup_central J₀ hJc (commutator_sup_eq_top J₀ hS)
    refine ⟨?_⟩
    have hmap : (commutator (commutator Q)).map (commutator Q).subtype = commutator Q := by
      rw [Subgroup.map_subtype_commutator, ← hLL]
    rw [eq_top_iff]
    intro x _
    have hx : (x : Q) ∈ (commutator (commutator Q)).map (commutator Q).subtype := by
      rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show x = y from Subtype.ext hyx.symm]
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hna
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

theorem center_le_of_simple (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a)
    (hsimp : IsSimpleGroup (Q ⧸ J₀)) : Subgroup.center Q ≤ J₀ := by
  have hZ : Subgroup.center (Q ⧸ J₀) = ⊥ := by
    rcases (Subgroup.center (Q ⧸ J₀)).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  intro z hz
  have : QuotientGroup.mk' J₀ z ∈ Subgroup.center (Q ⧸ J₀) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective J₀ s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

theorem sq_mem_center_commutator (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1)
    (htop : (⊤ : Subgroup Q) = commutator Q ⊔ V₀) {z : Q} (hz : z ∈ Subgroup.center Q) :
    z * z ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype := by
  rw [map_center_commutator_eq J₀ hJc hS hsimp hna]
  have hzq : z ∈ commutator Q ⊔ V₀ := htop ▸ Subgroup.mem_top z
  obtain ⟨l, hl, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hzq
  have hv2 := hV₀ v hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hlv : l * v = v * l := by
    have h1 := Subgroup.mem_center_iff.1 hz v
    have : v * l * v = l * v * v := by rw [mul_assoc v l v]; exact h1
    calc l * v = v⁻¹ * (v * l * v) := by group
      _ = v⁻¹ * (l * v * v) := by rw [this]
      _ = v⁻¹ * l * (v * v) := by group
      _ = v * l := by rw [hv2, mul_one, hvi]
  have hsq : l * v * (l * v) = l * l := by
    calc l * v * (l * v) = l * (v * l) * v := by group
      _ = l * (l * v) * v := by rw [hlv]
      _ = l * l * (v * v) := by group
      _ = l * l := by rw [hv2, mul_one]
  rw [hsq]
  refine ⟨Subgroup.mul_mem _ hl hl, ?_⟩
  have hzJ : l * v ∈ J₀ := center_le_of_simple J₀ hna hsimp hz
  have hzc := Subgroup.mem_center_iff.1 (hJc hzJ)
  have e : l * l = (l * v) * (l * v) * (v * v)⁻¹ := by
    calc l * l = (l * v) * (v⁻¹ * (l * v)) * v⁻¹ := by group
      _ = (l * v) * ((l * v) * v⁻¹) * v⁻¹ := by rw [hzc v⁻¹]
      _ = (l * v) * (l * v) * (v * v)⁻¹ := by group
  rw [e, hv2, inv_one, mul_one]
  exact J₀.mul_mem hzJ hzJ

theorem exists_sq_eq_of_mem_center (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1)
    (htop : (⊤ : Subgroup Q) = commutator Q ⊔ V₀) {z : Q} (hz : z ∈ Subgroup.center Q) :
    ∃ l ∈ commutator Q, z * z = l * l ∧
      l * l ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype := by
  have hzq : z ∈ commutator Q ⊔ V₀ := htop ▸ Subgroup.mem_top z
  obtain ⟨l, hl, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hzq
  refine ⟨l, hl, ?_, ?_⟩
  · have hv2 := hV₀ v hv
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hlv : l * v = v * l := by
      have h1 := Subgroup.mem_center_iff.1 hz v
      have : v * l * v = l * v * v := by rw [mul_assoc v l v]; exact h1
      calc l * v = v⁻¹ * (v * l * v) := by group
        _ = v⁻¹ * (l * v * v) := by rw [this]
        _ = v⁻¹ * l * (v * v) := by group
        _ = v * l := by rw [hv2, mul_one, hvi]
    calc l * v * (l * v) = l * (v * l) * v := by group
      _ = l * (l * v) * v := by rw [hlv]
      _ = l * l * (v * v) := by group
      _ = l * l := by rw [hv2, mul_one]
  · have h := sq_mem_center_commutator J₀ hJc hS hsimp hna hV₀ htop hz
    have hv2 := hV₀ v hv
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hlv : l * v = v * l := by
      have h1 := Subgroup.mem_center_iff.1 hz v
      have : v * l * v = l * v * v := by rw [mul_assoc v l v]; exact h1
      calc l * v = v⁻¹ * (v * l * v) := by group
        _ = v⁻¹ * (l * v * v) := by rw [this]
        _ = v⁻¹ * l * (v * v) := by group
        _ = v * l := by rw [hv2, mul_one, hvi]
    have e : l * v * (l * v) = l * l := by
      calc l * v * (l * v) = l * (v * l) * v := by group
        _ = l * (l * v) * v := by rw [hlv]
        _ = l * l * (v * v) := by group
        _ = l * l := by rw [hv2, mul_one]
    rwa [e] at h

theorem sq_eq_one_of_mem_center (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1)
    (htop : (⊤ : Subgroup Q) = commutator Q ⊔ V₀)
    (hlift : ∀ l ∈ commutator Q,
      l * l ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype → l * l = 1)
    {z : Q} (hz : z ∈ Subgroup.center Q) : z * z = 1 := by
  obtain ⟨l, hl, e, hll⟩ := exists_sq_eq_of_mem_center J₀ hJc hS hsimp hna hV₀ htop hz
  rw [e]
  exact hlift l hl hll

theorem lift_of_center_eq_bot (h : Subgroup.center (commutator Q) = ⊥) :
    ∀ l ∈ commutator Q,
      l * l ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype → l * l = 1 := by
  intro l _ hl
  rw [h, Subgroup.map_bot, Subgroup.mem_bot] at hl
  exact hl

theorem lift_of_involutions_lift
    (hZ2 : ∀ c ∈ Subgroup.center (commutator Q), c * c = 1)
    (hinv : ∀ x : commutator Q ⧸ Subgroup.center (commutator Q), orderOf x = 2 →
      ∃ y : commutator Q, orderOf y = 2 ∧ (y : commutator Q ⧸ Subgroup.center (commutator Q)) = x) :
    ∀ l ∈ commutator Q,
      l * l ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype → l * l = 1 := by
  intro l hl hll
  obtain ⟨c, hc, hcl⟩ := hll
  set k : commutator Q := ⟨l, hl⟩ with hk
  have hkk : k * k ∈ Subgroup.center (commutator Q) := by
    have : k * k = c := Subtype.ext hcl.symm
    rw [this]; exact hc
  by_cases hk1 : (k : commutator Q ⧸ Subgroup.center (commutator Q)) = 1
  · have hkZ : k ∈ Subgroup.center (commutator Q) := (QuotientGroup.eq_one_iff k).1 hk1
    exact congrArg Subtype.val (hZ2 k hkZ)
  · have hord : orderOf (k : commutator Q ⧸ Subgroup.center (commutator Q)) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]; exact hkk
      · exact hk1
    obtain ⟨y, hy2, hyk⟩ := hinv _ hord
    have hyk' : y⁻¹ * k ∈ Subgroup.center (commutator Q) := QuotientGroup.eq.1 hyk
    set c' := y⁻¹ * k with hc'
    have hk' : k = y * c' := by rw [hc']; group
    have hyy : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
    have hcc : c' * c' = 1 := hZ2 c' hyk'
    have : k * k = 1 := by
      rw [hk']
      calc y * c' * (y * c') = y * (c' * y) * c' := by group
        _ = y * (y * c') * c' := by rw [Subgroup.mem_center_iff.1 hyk' y]
        _ = (y * y) * (c' * c') := by group
        _ = 1 := by rw [hyy, hcc, one_mul]
    exact congrArg Subtype.val this

theorem center_eq_bot_of_unique_central (hJc : J₀ ≤ Subgroup.center Q)
    (hS : commutator (Q ⧸ J₀) = ⊤) (hsimp : IsSimpleGroup (Q ⧸ J₀))
    (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a) {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1)
    (hinvc : ∀ y ∈ commutator Q, y * y = 1 →
      y ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype)
    {c : Q} (hcZ : ∀ z ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype,
      z = 1 ∨ z = c)
    {v₁ v₂ : Q} (hv₁ : v₁ ∈ V₀) (hv₂ : v₂ ∈ V₀)
    (h₁ : QuotientGroup.mk' J₀ v₁ ≠ 1) (h₂ : QuotientGroup.mk' J₀ v₂ ≠ 1)
    (h₁₂ : QuotientGroup.mk' J₀ v₁ ≠ QuotientGroup.mk' J₀ v₂) :
    (Subgroup.center (commutator Q)).map (commutator Q).subtype = ⊥ := by
  have hLJ := commutator_sup_eq_top J₀ hS
  have hZ := map_center_commutator_eq J₀ hJc hS hsimp hna
  have key : ∀ v ∈ V₀, QuotientGroup.mk' J₀ v ≠ 1 → ∀ l ∈ commutator Q, ∀ z ∈ J₀, v = l * z →
      l * l = c := by
    intro v hv hv1 l hl z hz hvlz
    have hzc := Subgroup.mem_center_iff.1 (hJc hz)
    have hll : l * l ∈ commutator Q ⊓ J₀ := by
      refine ⟨Subgroup.mul_mem _ hl hl, ?_⟩
      have hv2 := hV₀ v hv
      rw [hvlz] at hv2
      have e : l * l = (z * z)⁻¹ := by
        have : l * z * (l * z) = l * l * (z * z) := by
          calc l * z * (l * z) = l * (z * l) * z := by group
            _ = l * (l * z) * z := by rw [hzc l]
            _ = l * l * (z * z) := by group
        rw [this] at hv2
        exact eq_inv_of_mul_eq_one_left hv2
      rw [e]; exact J₀.inv_mem (J₀.mul_mem hz hz)
    rw [← hZ] at hll
    rcases hcZ _ hll with h1 | h1
    · exfalso
      have hlZ := hinvc l hl h1
      rw [hZ] at hlZ
      apply hv1
      rw [hvlz, map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff l).2 hlZ.2, (QuotientGroup.eq_one_iff z).2 hz, one_mul]
    · exact h1
  have hv₁q : v₁ ∈ commutator Q ⊔ J₀ := hLJ ▸ Subgroup.mem_top v₁
  have hv₂q : v₂ ∈ commutator Q ⊔ J₀ := hLJ ▸ Subgroup.mem_top v₂
  obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv₁q
  obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv₂q
  have e₁ := key _ hv₁ h₁ l₁ hl₁ z₁ hz₁ rfl
  have e₂ := key _ hv₂ h₂ l₂ hl₂ z₂ hz₂ rfl
  have hz₁c := Subgroup.mem_center_iff.1 (hJc hz₁)
  have hz₂c := Subgroup.mem_center_iff.1 (hJc hz₂)
  have h12 : QuotientGroup.mk' J₀ (l₁ * z₁ * (l₂ * z₂)) ≠ 1 := by
    rw [map_mul]
    intro h
    apply h₁₂
    have hsq := hV₀ _ hv₂
    have : QuotientGroup.mk' J₀ (l₂ * z₂) * QuotientGroup.mk' J₀ (l₂ * z₂) = 1 := by
      rw [← map_mul, hsq, map_one]
    calc QuotientGroup.mk' J₀ (l₁ * z₁)
        = QuotientGroup.mk' J₀ (l₁ * z₁) * QuotientGroup.mk' J₀ (l₂ * z₂) *
            QuotientGroup.mk' J₀ (l₂ * z₂) := by rw [mul_assoc, this, mul_one]
      _ = QuotientGroup.mk' J₀ (l₂ * z₂) := by rw [h, one_mul]
  have e₁₂ := key _ (V₀.mul_mem hv₁ hv₂) h12 (l₁ * l₂) (Subgroup.mul_mem _ hl₁ hl₂) (z₁ * z₂)
    (J₀.mul_mem hz₁ hz₂) (by
      calc l₁ * z₁ * (l₂ * z₂) = l₁ * (z₁ * l₂) * z₂ := by group
        _ = l₁ * (l₂ * z₁) * z₂ := by rw [hz₁c l₂]
        _ = l₁ * l₂ * (z₁ * z₂) := by group)
  have hz1 : z₁ * z₁ = c⁻¹ := by
    have hv := hV₀ _ hv₁
    have : l₁ * z₁ * (l₁ * z₁) = l₁ * l₁ * (z₁ * z₁) := by
      calc l₁ * z₁ * (l₁ * z₁) = l₁ * (z₁ * l₁) * z₁ := by group
        _ = l₁ * (l₁ * z₁) * z₁ := by rw [hz₁c l₁]
        _ = l₁ * l₁ * (z₁ * z₁) := by group
    rw [this, e₁] at hv
    exact eq_inv_of_mul_eq_one_right hv
  have hz2 : z₂ * z₂ = c⁻¹ := by
    have hv := hV₀ _ hv₂
    have : l₂ * z₂ * (l₂ * z₂) = l₂ * l₂ * (z₂ * z₂) := by
      calc l₂ * z₂ * (l₂ * z₂) = l₂ * (z₂ * l₂) * z₂ := by group
        _ = l₂ * (l₂ * z₂) * z₂ := by rw [hz₂c l₂]
        _ = l₂ * l₂ * (z₂ * z₂) := by group
    rw [this, e₂] at hv
    exact eq_inv_of_mul_eq_one_right hv
  have hz12 : (z₁ * z₂) * (z₁ * z₂) = c⁻¹ := by
    have hv := hV₀ _ (V₀.mul_mem hv₁ hv₂)
    have hzz := Subgroup.mem_center_iff.1 (hJc (J₀.mul_mem hz₁ hz₂))
    have : l₁ * z₁ * (l₂ * z₂) * (l₁ * z₁ * (l₂ * z₂)) =
        (l₁ * l₂) * (l₁ * l₂) * ((z₁ * z₂) * (z₁ * z₂)) := by
      have e : l₁ * z₁ * (l₂ * z₂) = l₁ * l₂ * (z₁ * z₂) := by
        calc l₁ * z₁ * (l₂ * z₂) = l₁ * (z₁ * l₂) * z₂ := by group
          _ = l₁ * (l₂ * z₁) * z₂ := by rw [hz₁c l₂]
          _ = l₁ * l₂ * (z₁ * z₂) := by group
      rw [e]
      calc l₁ * l₂ * (z₁ * z₂) * (l₁ * l₂ * (z₁ * z₂))
          = l₁ * l₂ * ((z₁ * z₂) * (l₁ * l₂)) * (z₁ * z₂) := by group
        _ = l₁ * l₂ * ((l₁ * l₂) * (z₁ * z₂)) * (z₁ * z₂) := by rw [hzz (l₁ * l₂)]
        _ = (l₁ * l₂) * (l₁ * l₂) * ((z₁ * z₂) * (z₁ * z₂)) := by group
    rw [this, e₁₂] at hv
    exact eq_inv_of_mul_eq_one_right hv
  have hprod : (z₁ * z₂) * (z₁ * z₂) = (z₁ * z₁) * (z₂ * z₂) := by
    calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [hz₁c z₂]
      _ = z₁ * z₁ * (z₂ * z₂) := by group
  have : c⁻¹ = c⁻¹ * c⁻¹ := by
    calc c⁻¹ = (z₁ * z₂) * (z₁ * z₂) := hz12.symm
      _ = (z₁ * z₁) * (z₂ * z₂) := hprod
      _ = c⁻¹ * c⁻¹ := by rw [hz1, hz2]
  have hc1 : c = 1 := by
    have : c⁻¹ = 1 := by
      calc c⁻¹ = c⁻¹ * c⁻¹ * (c⁻¹)⁻¹ := by group
        _ = c⁻¹ * (c⁻¹)⁻¹ := by rw [← this]
        _ = 1 := by group
    exact inv_eq_one.1 this
  rw [eq_bot_iff]
  intro z hz
  rcases hcZ z hz with h | h
  · exact h
  · rw [h, hc1]; exact Subgroup.one_mem _

theorem exists_two_of_simple {S : Type*} [Group S] (hsimp : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {A : Subgroup S} (hA : ∀ a ∈ A, a * a = 1) (s : S)
    (hgen : A ⊔ A.map (MulAut.conj s).toMonoidHom = ⊤) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  by_contra hno
  push Not at hno
  obtain ⟨x₀, y₀, hxy⟩ := hna
  have hcyc : ∀ c : S, Subgroup.zpowers c = ⊤ → False := by
    intro c hc
    apply hxy
    obtain ⟨i, hi⟩ :=
      Subgroup.mem_zpowers_iff.1 (hc ▸ Subgroup.mem_top x₀ : x₀ ∈ Subgroup.zpowers c)
    obtain ⟨j, hj⟩ :=
      Subgroup.mem_zpowers_iff.1 (hc ▸ Subgroup.mem_top y₀ : y₀ ∈ Subgroup.zpowers c)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  by_cases hA1 : A = ⊥
  · apply hcyc 1
    rw [Subgroup.zpowers_one_eq_bot, ← hgen, hA1, Subgroup.map_bot, sup_bot_eq]
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have hAa : ∀ x ∈ A, x = 1 ∨ x = (a : S) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hno x hx a a.2 hx1 (by simpa using ha1))
  set b := s * (a : S) * s⁻¹ with hb
  have ha2 : (a : S) * a = 1 := hA a a.2
  have hb2 : b * b = 1 := by
    have : b * b = s * ((a : S) * a) * s⁻¹ := by rw [hb]; group
    rw [this, ha2]; group
  have hgen' : Subgroup.closure ({(a : S), b} : Set S) = ⊤ := by
    rw [eq_top_iff, ← hgen, sup_le_iff]
    constructor
    · intro x hx
      rcases hAa x hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rintro _ ⟨y, hy, rfl⟩
      rcases hAa y hy with rfl | rfl
      · simp
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set N := Subgroup.zpowers ((a : S) * b) with hN
  have hnorm : ∀ x : S, (x = a ∨ x = b) → x ∈ Subgroup.normalizer (N : Set S) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 fun e => ⟨fun he => ?_, fun he => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact Subgroup.mem_zpowers_iff.2 ⟨-k, (conj_zpow_eq ha2 hb2 hx k).symm⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
      have hx' : x⁻¹ = x := by
        rcases hx with rfl | rfl
        · exact inv_eq_of_mul_eq_one_right ha2
        · exact inv_eq_of_mul_eq_one_right hb2
      have : e = x * ((a : S) * b) ^ k * x⁻¹ := by
        calc e = x⁻¹ * (x * e * x⁻¹) * x := by group
          _ = x * ((a : S) * b) ^ k * x⁻¹ := by rw [← hk, hx']
      rw [this, conj_zpow_eq ha2 hb2 hx k]
      exact Subgroup.mem_zpowers_iff.2 ⟨-k, rfl⟩
  have hNn : N.Normal := by
    have hle : Subgroup.closure ({(a : S), b} : Set S) ≤ Subgroup.normalizer (N : Set S) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hnorm _ (Or.inl rfl)
      · exact hnorm _ (Or.inr rfl)
    rw [hgen', top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.1 hle
  rcases hNn.eq_bot_or_eq_top with h | h
  ·
    have hab : (a : S) * b = 1 := by
      have : (a : S) * b ∈ N := Subgroup.mem_zpowers _
      rwa [h, Subgroup.mem_bot] at this
    have hba : b = a := by
      have := eq_inv_of_mul_eq_one_right hab
      rw [this, inv_eq_of_mul_eq_one_right ha2]
    apply hcyc a
    rw [eq_top_iff, ← hgen', Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · rw [hba]; exact Subgroup.mem_zpowers _
  · exact hcyc _ h

theorem sl2_center_eq_one_or_neg_one {F : Type*} [Field F] {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 this with h | h
  · left
    have hr1 : r = 1 := by linear_combination h
    ext i j
    rw [← hrA, hr1]
    simp
  · right
    have hr1 : r = -1 := by linear_combination h
    ext i j
    rw [← hrA, hr1]
    fin_cases i <;> fin_cases j <;> simp

theorem center_commutator_eq_bot_of_alt_five [Finite Q] (hKG3 : KGI22One)
    (hJc : J₀ ≤ Subgroup.center Q) (hS : commutator (Q ⧸ J₀) = ⊤)
    (hsimp : IsSimpleGroup (Q ⧸ J₀)) (hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a)
    (e5 : Q ⧸ J₀ ≃* alternatingGroup (Fin 5)) (hZ2 : IsPGroup 2 (Subgroup.center (commutator Q)))
    {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1) {v₁ v₂ : Q} (hv₁ : v₁ ∈ V₀) (hv₂ : v₂ ∈ V₀)
    (h₁ : QuotientGroup.mk' J₀ v₁ ≠ 1) (h₂ : QuotientGroup.mk' J₀ v₂ ≠ 1)
    (h₁₂ : QuotientGroup.mk' J₀ v₁ ≠ QuotientGroup.mk' J₀ v₂) :
    Subgroup.center (commutator Q) = ⊥ := by
  by_contra hne
  obtain ⟨hL, ⟨eL⟩⟩ := quasisimple_commutator J₀ hJc hS hsimp hna
  obtain ⟨eS⟩ := (hKG3 (commutator Q) hL hne hZ2).1 ⟨eL.trans e5⟩
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcen : ∀ y : commutator Q, y ∈ Subgroup.center (commutator Q) ↔
      eS y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro B
      obtain ⟨x, rfl⟩ := eS.surjective B
      rw [← map_mul, ← map_mul, hy x]
    · intro hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro x
      apply eS.injective
      rw [map_mul, map_mul, hy (eS x)]
  set c : Q := ((eS.symm (-1) : commutator Q) : Q) with hc
  have hinvc : ∀ y ∈ commutator Q, y * y = 1 →
      y ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype := by
    intro y hy hyy
    refine ⟨⟨y, hy⟩, (hcen _).2 ?_, rfl⟩
    have : eS ⟨y, hy⟩ * eS ⟨y, hy⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hy⟩ : commutator Q) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
      rw [this, map_one]
    rcases sl2_eq_one_or_neg_one_of_mul_self h2 this with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_center_iff.2 fun B => by rw [mul_neg, neg_mul, mul_one, one_mul]
  have hcZ : ∀ z ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype, z = 1 ∨ z = c := by
    rintro _ ⟨y, hy, rfl⟩
    rcases sl2_center_eq_one_or_neg_one ((hcen y).1 hy) with h | h
    · left
      have : y = 1 := eS.injective (by rw [h, map_one])
      rw [this]; rfl
    · right
      have : y = eS.symm (-1) := by rw [← h, MulEquiv.symm_apply_apply]
      rw [this, hc]
      rfl
  have hbot := center_eq_bot_of_unique_central J₀ hJc hS hsimp hna hV₀ hinvc hcZ hv₁ hv₂ h₁ h₂
    h₁₂
  apply hne
  exact (Subgroup.map_eq_bot_iff_of_injective _ (commutator Q).subtype_injective).1 hbot

end Core

end E2

end CFSG.Quasithin

module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Maximal

variable {G : Type*} [Group G]

theorem mem_of_maximal_of_commute {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {x : G}
    (hx3 : x ^ 3 = 1) (hxA : ∀ a ∈ A, a * x = x * a) : x ∈ A := by
  obtain ⟨⟨hAc, hA3⟩, hAmax⟩ := hA
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxk : ∀ a ∈ A, ∀ k : ℤ, a * x ^ k = x ^ k * a := fun a ha k =>
    (Commute.zpow_right (hxA a ha) k).eq
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ k : ℤ, g = a * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, rfl⟩ ⟨a', ha', k', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', k + k', ?_⟩
        rw [_root_.zpow_add]
        calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
          _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
          _ = a * a' * (x ^ k * x ^ k') := by group
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, k, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, -k, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg]
        exact (hxk a⁻¹ (A.inv_mem ha) (-k)).symm }
  have hPcomm : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
    rintro _ ⟨a, ha, k, rfl⟩ _ ⟨a', ha', k', rfl⟩
    calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
      _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
      _ = (a * a') * (x ^ k * x ^ k') := by group
      _ = (a' * a) * (x ^ k' * x ^ k) := by
          rw [hAcomm a ha a' ha', ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
      _ = a' * (a * x ^ k') * x ^ k := by group
      _ = a' * (x ^ k' * a) * x ^ k := by rw [hxk a ha k']
      _ = a' * x ^ k' * (a * x ^ k) := by group
  have hP3 : ∀ g ∈ P, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, k, rfl⟩
    rw [(Commute.zpow_right (hxA a ha) k).mul_pow, hA3 a ha, one_mul, ← zpow_natCast,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3, _root_.one_zpow]
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 0, by simp⟩
  have hPel : CFSG.Assembly.IsElemAbelian 3 P :=
    ⟨⟨⟨fun g h => Subtype.ext (hPcomm g g.2 h h.2)⟩⟩, hP3⟩
  have hPA := hAmax hPel hAP
  exact hPA ⟨1, A.one_mem, 1, by simp⟩

end Maximal

section Lifts

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mem_normalizer_of_normal (g : G) : g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

@[expose] def IsPGLAt (e : L ≃* slPi π 3 (p ^ f) K) (g : G) (y : GL (Fin 3) K) : Prop :=
  y ∈ glPi π 3 (p ^ f) K ∧ ∀ s : slPi π 3 (p ^ f) K,
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      y * s * y⁻¹

variable (e : L ≃* slPi π 3 (p ^ f) K)

theorem coe_slAct_eq (g : G) (s : slPi π 3 (p ^ f) K) :
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      (e ⟨g * (e.symm s : G) * g⁻¹, hLn.conj_mem _ (e.symm s).2 g⟩ : GL (Fin 3) K) :=
  rfl

theorem slAct_mul_apply (g h : G) (s : slPi π 3 (p ^ f) K) :
    slAct e ⟨g * h, mem_normalizer_of_normal _⟩ s =
      slAct e ⟨g, mem_normalizer_of_normal g⟩ (slAct e ⟨h, mem_normalizer_of_normal h⟩ s) := by
  have : (⟨g * h, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨g, mem_normalizer_of_normal g⟩ * ⟨h, mem_normalizer_of_normal h⟩ := rfl
  rw [this, map_mul, MulAut.mul_apply]

theorem isPGLAt_mul {g h : G} {y z : GL (Fin 3) K} (hg : IsPGLAt e g y) (hh : IsPGLAt e h z) :
    IsPGLAt e (g * h) (y * z) := by
  refine ⟨mul_mem hg.1 hh.1, fun s => ?_⟩
  rw [slAct_mul_apply, hg.2, hh.2]
  group

theorem isPGLAt_one_iff {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) :
    IsPGLAt e (1 : G) y ↔ ∀ s : slPi π 3 (p ^ f) K, y * (s : GL (Fin 3) K) * y⁻¹ = s := by
  refine and_iff_right_iff_imp.mpr ?_ |>.trans ?_
  · intro _
    exact hy
  · refine forall_congr' fun s => ?_
    have h1 : ((slAct e ⟨1, mem_normalizer_of_normal 1⟩ s : slPi π 3 (p ^ f) K) :
        GL (Fin 3) K) = s := by
      rw [coe_slAct_eq]
      simp
    rw [h1, eq_comm]

theorem isPGLAt_of_mem (hπ : π = false → UnitaryFieldData p f K) {l : G} (hl : l ∈ L) :
    IsPGLAt e l (e ⟨l, hl⟩ : GL (Fin 3) K) := by
  refine ⟨slPi_le_glPi hπ (e ⟨l, hl⟩).2, fun s => ?_⟩
  rw [coe_slAct_eq]
  have : (⟨l * (e.symm s : G) * l⁻¹, hLn.conj_mem _ (e.symm s).2 l⟩ : L) =
      ⟨l, hl⟩ * e.symm s * (⟨l, hl⟩ : L)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem isPGLAt_of_mem_centralizer {g : G} (hg : g ∈ Subgroup.centralizer (L : Set G)) :
    IsPGLAt e g 1 := by
  refine ⟨one_mem _, fun s => ?_⟩
  rw [coe_slAct_eq, one_mul, inv_one, mul_one]
  have : (⟨g * (e.symm s : G) * g⁻¹, hLn.conj_mem _ (e.symm s).2 g⟩ : L) = e.symm s := by
    apply Subtype.ext
    change g * (e.symm s : G) * g⁻¹ = e.symm s
    rw [(Subgroup.mem_centralizer_iff.mp hg _ (e.symm s).2).symm, mul_inv_cancel_right]
  rw [this, MulEquiv.apply_symm_apply]

variable {e}

theorem isPGLAt_inv_mul_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {g : G}
    {y z : GL (Fin 3) K} (hy : IsPGLAt e g y) (hz : IsPGLAt e g z) :
    y⁻¹ * z ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
  have h1 := hy.2 ⟨x, hx⟩
  have h2 := hz.2 ⟨x, hx⟩
  rw [h1] at h2
  change y * x * y⁻¹ = z * x * z⁻¹ at h2
  calc y⁻¹ * z * x = y⁻¹ * (z * x * z⁻¹) * z := by group
    _ = y⁻¹ * (y * x * y⁻¹) * z := by rw [h2]
    _ = x * (y⁻¹ * z) := by group

theorem mem_centralizer_of_isPGLAt_scalar {g : G} {y : GL (Fin 3) K} (hy : IsPGLAt e g y)
    (hys : y ∈ StatedScalars (Fin 3) K) : g ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hy.2 (e ⟨l, hl⟩)
  rw [coe_slAct_eq] at h1
  simp only [MulEquiv.symm_apply_apply] at h1
  have hc : y * (e ⟨l, hl⟩ : GL (Fin 3) K) * y⁻¹ = e ⟨l, hl⟩ := by
    rw [← commute_of_mem_statedScalars hys (e ⟨l, hl⟩ : GL (Fin 3) K), mul_inv_cancel_right]
  have h2 := e.injective (Subtype.ext (h1.trans hc))
  have h3 : g * l * g⁻¹ = l := congrArg Subtype.val h2
  calc l * g = g * l * g⁻¹ * g := by rw [h3]
    _ = g * l := by group

theorem isPGLAt_commutator_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {g h : G}
    (hgh : g * h = h * g) {y z : GL (Fin 3) K} (hy : IsPGLAt e g y) (hz : IsPGLAt e h z) :
    y * z * y⁻¹ * z⁻¹ ∈ StatedScalars (Fin 3) K := by
  have h1 := isPGLAt_mul e hy hz
  have h2 := isPGLAt_mul e hz hy
  rw [← hgh] at h2
  obtain ⟨c, hc⟩ := isPGLAt_inv_mul_mem hK hq h2 h1
  have hyz : y * z = z * y * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  have hcomm := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (y⁻¹ * z⁻¹)
  refine ⟨c, ?_⟩
  calc GeneralLinearGroup.scalar (Fin 3) c = z * y * (GeneralLinearGroup.scalar (Fin 3) c *
      (y⁻¹ * z⁻¹)) := by rw [← hcomm.eq]; group
    _ = y * z * y⁻¹ * z⁻¹ := by rw [← mul_assoc, ← hyz]; group

end Lifts

section PglHom

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool} {e : L ≃* slPi π 3 (p ^ f) K}

@[expose] noncomputable def pglHom (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (A' : Subgroup G) (hA' : ∀ a ∈ A', ∃ y, IsPGLAt e a y) :
    A' →* GL (Fin 3) K ⧸ StatedScalars (Fin 3) K where
  toFun a :=
    ((Classical.choose (hA' a a.2) : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)
  map_one' := by
    have h1 := Classical.choose_spec (hA' 1 A'.one_mem)
    have h2 : IsPGLAt e (1 : G) 1 := isPGLAt_of_mem_centralizer e (Subgroup.one_mem _)
    have h3 := isPGLAt_inv_mul_mem hK hq h2 h1
    rw [inv_one, one_mul] at h3
    exact (QuotientGroup.eq_one_iff _).mpr h3
  map_mul' a b := by
    have ha := Classical.choose_spec (hA' a a.2)
    have hb := Classical.choose_spec (hA' b b.2)
    have hab := Classical.choose_spec (hA' (a * b) (a * b).2)
    have h := isPGLAt_mul e ha hb
    have h3 := isPGLAt_inv_mul_mem hK hq h hab
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := inv_mem h3
    rwa [_root_.mul_inv_rev, inv_inv] at this

variable {hK : PiField π p f K} {hq : ModThree π (p ^ f)} {A' : Subgroup G}
  {hA' : ∀ a ∈ A', ∃ y, IsPGLAt e a y}

theorem pglHom_apply (a : A') {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    pglHom hK hq A' hA' a = (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
  change ((Classical.choose (hA' a a.2) : GL (Fin 3) K) :
    GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = y
  rw [QuotientGroup.eq]
  exact isPGLAt_inv_mul_mem hK hq (Classical.choose_spec (hA' a a.2)) hy

theorem pglHom_eq_one_iff (a : A') :
    pglHom hK hq A' hA' a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨y, hy⟩ := hA' a a.2
  rw [pglHom_apply a hy, QuotientGroup.eq_one_iff]
  constructor
  · exact mem_centralizer_of_isPGLAt_scalar hy
  · intro hc
    have h1 := isPGLAt_inv_mul_mem hK hq (isPGLAt_of_mem_centralizer e hc) hy
    rwa [inv_one, one_mul] at h1

theorem ker_pglHom :
    (pglHom hK hq A' hA').ker = (Subgroup.centralizer (L : Set G)).subgroupOf A' := by
  ext a
  rw [MonoidHom.mem_ker, pglHom_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_eq_card_inf_mul_card_range :
    Nat.card A' = Nat.card (A' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
      Nat.card (pglHom hK hq A' hA').range := by
  rw [← Subgroup.index_ker (pglHom hK hq A' hA'),
    ← Subgroup.card_mul_index (pglHom hK hq A' hA').ker,
    ker_pglHom, ← Subgroup.inf_subgroupOf_left]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem range_pglHom_comm (hcomm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) :
    ∀ x ∈ (pglHom hK hq A' hA').range, ∀ y ∈ (pglHom hK hq A' hA').range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm a a.2 b b.2)

theorem range_pglHom_pow (h3 : ∀ a ∈ A', a ^ 3 = 1) :
    ∀ x ∈ (pglHom hK hq A' hA').range, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h3 a a.2, Subgroup.coe_one])
  rw [this, map_one]

theorem mk_mem_range_pglHom {a : G} (ha : a ∈ A') {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A' hA').range :=
  ⟨⟨a, ha⟩, pglHom_apply ⟨a, ha⟩ hy⟩

theorem exists_isPGLAt_of_mk_mem {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hmem : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A' hA').range) :
    ∃ a ∈ A', IsPGLAt e a y := by
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨z, hz⟩ := hA' a a.2
  rw [pglHom_apply a hz, QuotientGroup.eq] at ha
  obtain ⟨c, hc⟩ := ha
  refine ⟨a, a.2, hy, fun s => ?_⟩
  have hyz : y = z * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  rw [hz.2, hyz]
  have hcs := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (s : GL (Fin 3) K)).eq
  calc z * s * z⁻¹ = z * (s * GeneralLinearGroup.scalar (Fin 3) c) *
      (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * z⁻¹ := by group
    _ = z * (GeneralLinearGroup.scalar (Fin 3) c * s) *
      (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * z⁻¹ := by rw [hcs]
    _ = _ := by group

end PglHom

section Centre

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem eq_one_or_eq_tau_or_eq_tau_sq {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : K}
    (hx : x ^ 3 = 1) : x = 1 ∨ x = τ ∨ x = τ ^ 2 := by
  have hs := one_add_tau_add_sq hτ hτ1
  have h : (x - 1) * (x - τ) * (x - τ ^ 2) = 0 := by
    linear_combination hx - x ^ 2 * hs + x * τ * hs - hτ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem pow_three_eq_one_of_scalar_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {ζ : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin 3) ζ ∈ slPi π 3 (p ^ f) K) : ζ ^ 3 = 1 := by
  have hdet := ((mem_slPi_iff hπ).mp h).2
  rw [det_scalar_three] at hdet
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])

theorem exists_tau_pow_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K)
    (hc : ∀ x ∈ slPi π 3 (p ^ f) K, s * x = x * s) :
    ∃ k : Fin 3, (s : Matrix (Fin 3) (Fin 3) K) = τ ^ (k : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨ζ, rfl⟩ := mem_statedScalars_of_commute hπ hq' hτ hτ1 hc
  have hζ3 := pow_three_eq_one_of_scalar_mem_slPi hπ hs
  have hζ : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ with h | h | h
  · exact ⟨0, by rw [coe_scalar_eq_smul, h]; simp⟩
  · exact ⟨1, by rw [coe_scalar_eq_smul, h]; simp⟩
  · exact ⟨2, by rw [coe_scalar_eq_smul, h]; simp⟩

end Centre

section CentreL

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mulAut_scalar_tau_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {t : slPi π 3 (p ^ f) K}
    (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • (1 : Matrix (Fin 3) (Fin 3) K))
    {α : MulAut (slPi π 3 (p ^ f) K)} (hα : α ^ 3 = 1) : α t = t := by
  have htc : t ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ht, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hαc : α t ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨s', rfl⟩ := α.surjective s
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp htc s')]
  obtain ⟨k, hk⟩ := exists_tau_pow_of_mem_center hK hq hτ hτ1 (α t).2 fun x hx => by
    have := Subgroup.mem_center_iff.mp hαc ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun s : slPi π 3 (p ^ f) K => ((s : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [ht, Subgroup.coe_one, Units.val_one, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at this
    exact hτ1 this
  have hα3t : (α ^ 3) t = t := by rw [hα, MulAut.one_apply]
  have hpow : ∀ n : ℕ, (((t ^ n : slPi π 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      τ ^ n • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, ht, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul, pow_succ]
  have hαt : α t = t ^ (k : ℕ) := by
    apply Subtype.ext
    apply Units.ext
    rw [hk, hpow]
  fin_cases k
  · exfalso
    apply ht1
    apply α.injective
    rw [hαt, map_one]
    rfl
  · simpa using hαt
  · exfalso
    have h2 : α t = t ^ 2 := hαt
    have h3 : (α ^ 3) t = t ^ 8 := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, h2, map_pow, h2,
        map_pow, map_pow, h2, ← pow_mul, ← pow_mul]
    rw [hα3t] at h3
    have h7 : t ^ 7 = 1 := by
      have : t ^ 8 = t ^ 7 * t := pow_succ t 7
      rw [this] at h3
      exact (mul_eq_right.mp h3.symm)
    have h3' : t ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hpow, hτ, one_smul, Subgroup.coe_one, Units.val_one]
    apply ht1
    have e1 : t = t ^ 7 * ((t ^ 3)⁻¹ * (t ^ 3)⁻¹) := by group
    rw [e1, h7, h3', inv_one, one_mul, one_mul]

end CentreL

section Setting

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem slAct_pow_three (e : L ≃* slPi π 3 (p ^ f) K) {g : G} (hg : g ^ 3 = 1) :
    slAct e ⟨g, mem_normalizer_of_normal g⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨g, mem_normalizer_of_normal g⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hg, Subgroup.coe_one])
  rw [this, map_one]

theorem mem_and_inf_centralizer_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {c : G}
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) :
    c ∈ L ∧ L ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : (τu : K) ^ 3 = 1 := by rw [hτu, Units.val_mk0, hτ]
  set t : slPi π 3 (p ^ f) K :=
    ⟨GeneralLinearGroup.scalar (Fin 3) τu, scalar_mem_slPi_of_cube hK hq hτu3⟩ with htdef
  have ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [htdef, coe_scalar_eq_smul, hτu, Units.val_mk0]
  have htc : ∀ s : slPi π 3 (p ^ f) K, t * s = s * t := fun s => Subtype.ext
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar τu (s : GL (Fin 3) K)).symm.eq
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun s : slPi π 3 (p ^ f) K => ((s : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [ht, Subgroup.coe_one, Units.val_one, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at this
    exact hτ1 this
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, smul_pow, one_pow, hτ, one_smul,
      Subgroup.coe_one, Units.val_one]
  set z₀ : G := (e.symm t : G) with hz₀
  have hz₀L : z₀ ∈ L := (e.symm t).2
  have hz₀C : z₀ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : e.symm t * ⟨l, hl⟩ = ⟨l, hl⟩ * e.symm t := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, htc]
    exact (congrArg Subtype.val h1).symm
  have hz₀A : z₀ ∈ A := by
    refine mem_of_maximal_of_commute hA ?_ fun a ha => ?_
    · rw [hz₀, ← Subgroup.coe_pow, ← map_pow, ht3, map_one, Subgroup.coe_one]
    · have hfix := mulAut_scalar_tau_eq hK hq hτ hτ1 ht (slAct_pow_three e (hA.1.2 a ha))
      have h1 := congrArg (fun s : slPi π 3 (p ^ f) K => (e.symm s : G)) hfix
      simp only [slAct_apply, MulEquiv.symm_apply_apply] at h1
      have h2 : a * z₀ * a⁻¹ = z₀ := h1
      calc a * z₀ = a * z₀ * a⁻¹ * a := by group
        _ = z₀ * a := by rw [h2]
  have hz₀c : z₀ ∈ Subgroup.zpowers c := hAc ▸ Subgroup.mem_inf.mpr ⟨hz₀A, hz₀C⟩
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply ht1
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hzc : Subgroup.zpowers z₀ = Subgroup.zpowers c := by
    have : Finite (Subgroup.zpowers c) :=
      (orderOf_pos_iff.mp (by rw [hc3]; norm_num)).finite_zpowers
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz₀c)
    rw [Nat.card_zpowers, Nat.card_zpowers, hc3]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : z₀ ^ 3 = 1 := by rw [hz₀, ← Subgroup.coe_pow, ← map_pow, ht3, map_one,
      Subgroup.coe_one]
    exact (orderOf_eq_prime h3 hz₀1).ge
  have hcL : c ∈ L := by
    have : c ∈ Subgroup.zpowers z₀ := hzc ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hz₀L) this
  refine ⟨hcL, le_antisymm ?_ ?_⟩
  · rintro l ⟨hlL, hlC⟩
    have hcen : ∀ x ∈ slPi π 3 (p ^ f) K, (e ⟨l, hlL⟩ : GL (Fin 3) K) * x = x * e ⟨l, hlL⟩ := by
      intro x hx
      obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
      have h1 : (⟨l, hlL⟩ : L) * m = m * ⟨l, hlL⟩ :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hlC _ m.2).symm)
      have h2 := congrArg (fun s : L => ((e s : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
      simp only [map_mul, Subgroup.coe_mul, hm] at h2
      exact h2
    obtain ⟨k, hk⟩ := exists_tau_pow_of_mem_center hK hq hτ hτ1 (e ⟨l, hlL⟩).2 hcen
    have hel : e ⟨l, hlL⟩ = t ^ (k : ℕ) := by
      apply Subtype.ext
      apply Units.ext
      rw [hk, Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, smul_pow, one_pow]
    have hl : l = z₀ ^ (k : ℕ) := by
      have := congrArg (fun s => (e.symm s : G)) hel
      simp only [MulEquiv.symm_apply_apply, map_pow, Subgroup.coe_pow] at this
      exact this
    rw [← hzc, hl]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [← hzc]
    exact Subgroup.zpowers_le.mpr ⟨hz₀L, hz₀C⟩

end Setting

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIc

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement

structure SLTwoData (X : Type) [Group X] (π : Bool) (p f : ℕ) (K : Type) [Field K] where
  L₀ : Subgroup X
  normal : L₀.Normal
  u : X
  a : X
  mem_centralizer : u ∈ Subgroup.centralizer (L₀ : Set X)
  not_mem : u ∉ L₀
  orderOf_u : orderOf u = 3
  a_pow : a ^ 3 = 1
  sup_eq : L₀ ⊔ Subgroup.closure {u, a} = ⊤
  comm_ne : u * a * u⁻¹ * a⁻¹ ≠ 1
  comm_mem : u * a * u⁻¹ * a⁻¹ ∈ L₀ ⊓ Subgroup.centralizer (L₀ : Set X)
  piField : PiField π p f K
  modThree : ModThree π (p ^ f)
  e : L₀ ≃* slPi π 3 (p ^ f) K
  y : GL (Fin 3) K
  y_mem : y ∈ glPi π 3 (p ^ f) K
  type3 : Type123 π (p ^ f) K y 3
  act : ∀ z : L₀, ((e ⟨a * z * a⁻¹, normal.conj_mem z z.2 a⟩ : GL (Fin 3) K)) =
    y * (e z : GL (Fin 3) K) * y⁻¹

instance SLTwoData.instNormal {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (D : SLTwoData X π p f K) : D.L₀.Normal :=
  D.normal

theorem exists_sLTwoData {X : Type} [Group X] (h : IsSLThreePiTwo X) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Nonempty (SLTwoData X π p f K) := by
  obtain ⟨L₀, hL, u, a, -, huC, huL, hu3, ha3, htop, hne, hmem, π, p, f, K, _, hK, hq, e, y, hyH,
    hy3, hact⟩ := h
  exact ⟨π, p, f, K, inferInstance, ⟨⟨L₀, hL, u, a, huC, huL, hu3, ha3, htop, hne, hmem, hK, hq,
    e, y, hyH, hy3, hact⟩⟩⟩

namespace SLTwoData

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
  (D : SLTwoData X π p f K)

theorem mk_commute :
    QuotientGroup.mk' D.L₀ D.u * QuotientGroup.mk' D.L₀ D.a =
      QuotientGroup.mk' D.L₀ D.a * QuotientGroup.mk' D.L₀ D.u := by
  have h1 : QuotientGroup.mk' D.L₀ (D.u * D.a * D.u⁻¹ * D.a⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr D.comm_mem.1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc QuotientGroup.mk' D.L₀ D.u * QuotientGroup.mk' D.L₀ D.a =
      (QuotientGroup.mk' D.L₀ D.u * QuotientGroup.mk' D.L₀ D.a *
        (QuotientGroup.mk' D.L₀ D.u)⁻¹ * (QuotientGroup.mk' D.L₀ D.a)⁻¹) *
        (QuotientGroup.mk' D.L₀ D.a * QuotientGroup.mk' D.L₀ D.u) := by group
    _ = _ := by rw [h1, one_mul]

theorem exists_normal_form (x : X) :
    ∃ l ∈ D.L₀, ∃ i < 3, ∃ j < 3, x = l * D.u ^ i * D.a ^ j := by
  set π₀ := QuotientGroup.mk' D.L₀ with hπ₀
  set ū := π₀ D.u
  set ā := π₀ D.a
  have hc : Commute ū ā := D.mk_commute
  have hu3 : ū ^ 3 = 1 := by rw [← map_pow, ← D.orderOf_u, pow_orderOf_eq_one, map_one]
  have ha3 : ā ^ 3 = 1 := by rw [← map_pow, D.a_pow, map_one]
  let T : Subgroup (X ⧸ D.L₀) :=
    { carrier := {q | ∃ i j : ℕ, q = ū ^ i * ā ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        refine ⟨i + i', j + j', ?_⟩
        rw [pow_add, pow_add, mul_assoc, ← mul_assoc (ā ^ j), ((hc.symm.pow_pow j i')).eq]
        group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        have hu' : (ū ^ i)⁻¹ = ū ^ (2 * i) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hu3,
            one_pow]
        have ha' : (ā ^ j)⁻¹ = ā ^ (2 * j) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, ha3,
            one_pow]
        rw [_root_.mul_inv_rev, ← hu', ← ha', ((hc.pow_pow i j).inv_inv).eq] }
  have hT : (⊤ : Subgroup (X ⧸ D.L₀)) ≤ T := by
    rw [← Subgroup.map_top_of_surjective π₀ (QuotientGroup.mk'_surjective _), ← D.sup_eq,
      Subgroup.map_sup, MonoidHom.map_closure]
    have hL : D.L₀.map π₀ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hL, bot_sup_eq, Subgroup.closure_le, Set.image_pair]
    rintro q (rfl | rfl)
    · exact ⟨1, 0, by simp [ū]⟩
    · exact ⟨0, 1, by simp [ā]⟩
  obtain ⟨i, j, hij⟩ := hT (Subgroup.mem_top (π₀ x))
  refine ⟨x * (D.u ^ (i % 3) * D.a ^ (j % 3))⁻¹, ?_, i % 3, Nat.mod_lt _ (by norm_num),
    j % 3, Nat.mod_lt _ (by norm_num), by group⟩
  rw [← QuotientGroup.eq_one_iff (N := D.L₀)]
  change π₀ (x * (D.u ^ (i % 3) * D.a ^ (j % 3))⁻¹) = 1
  have hu3' : ∀ n : ℕ, ū ^ n = ū ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hu3, one_pow, one_mul]
  have ha3' : ∀ n : ℕ, ā ^ n = ā ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ha3, one_pow, one_mul]
  rw [map_mul, map_inv, map_mul, map_pow, map_pow, hij, hu3' i, ha3' j, mul_inv_cancel]

theorem commutator_le : commutator X ≤ D.L₀ := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ x' _
  rw [← QuotientGroup.eq_one_iff (N := D.L₀)]
  change QuotientGroup.mk' D.L₀ ⁅x, x'⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  obtain ⟨l, hl, i, -, j, -, rfl⟩ := D.exists_normal_form x
  obtain ⟨l', hl', i', -, j', -, rfl⟩ := D.exists_normal_form x'
  have hc : Commute (QuotientGroup.mk' D.L₀ D.u) (QuotientGroup.mk' D.L₀ D.a) := D.mk_commute
  have hl1 : QuotientGroup.mk' D.L₀ l = 1 := (QuotientGroup.eq_one_iff _).mpr hl
  have hl1' : QuotientGroup.mk' D.L₀ l' = 1 := (QuotientGroup.eq_one_iff _).mpr hl'
  simp only [map_mul, map_pow, hl1, hl1', one_mul]
  exact ((Commute.pow_pow_self _ i i').mul_right (hc.pow_pow i j')).mul_left
    ((hc.symm.pow_pow j i').mul_right (Commute.pow_pow_self _ j j'))

theorem isPGLAt_a : IsPGLAt D.e D.a D.y := by
  refine ⟨D.y_mem, fun s => ?_⟩
  rw [coe_slAct_eq, D.act, MulEquiv.apply_symm_apply]

end SLTwoData

theorem type123_three_sq {K : Type} [Field K] {p f : ℕ} {π : Bool} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y : GL (Fin 3) K} (h3 : Type123 π (p ^ f) K y 3) :
    Type123 π (p ^ f) K (y ^ 2) 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hyZ, hy3, hirr⟩ := h3
  refine ⟨fun hy2 => hyZ ?_, ?_, fun W hW => hirr W fun v hv => ?_⟩
  · have e : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [e]
    exact mul_mem hy3 (inv_mem hy2)
  · rw [← pow_mul, mul_comm, pow_mul]
    exact pow_mem hy3 2
  · rw [zPi_eq hπ hq' hτ hτ1] at hy3
    obtain ⟨c, hc⟩ := hy3.2
    have h4 : ((y ^ 2 * y ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • (y : Matrix (Fin 3) (Fin 3) K) := by
      have : y ^ 2 * y ^ 2 = y ^ 3 * y := by group
      rw [this, ← hc, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_eq_diagonal_mul]
    have h1 : ((y ^ 2 * y ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW _ (hW v hv)
    rw [h4, Matrix.smul_mulVec] at h1
    have h2 := W.smul_mem ((c : K)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul] at h2

namespace SLTwoData

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
  (D : SLTwoData X π p f K)

theorem type3_pow {j : ℕ} (hj0 : j ≠ 0) (hj3 : j < 3) : Type123 π (p ^ f) K (D.y ^ j) 3 := by
  interval_cases j
  · exact absurd rfl hj0
  · rw [pow_one]
    exact D.type3
  · exact type123_three_sq D.piField D.modThree D.type3

theorem exists_of_mem_centralizer {z : X} (hz : z ∈ Subgroup.centralizer (D.L₀ : Set X)) :
    ∃ l ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X), ∃ i < 3, z = l * D.u ^ i := by
  obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := D.exists_normal_form z
  have hj0 : j = 0 := by
    by_contra hj0
    have hmem : D.a ^ j ∈ D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X) := by
      have e : D.a ^ j = (D.u ^ i)⁻¹ * l⁻¹ * (l * D.u ^ i * D.a ^ j) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ D.mem_centralizer i)))
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ hl))) (Subgroup.mem_sup_right hz)
    exact not_mem_sup_centralizer_of_type3 D.piField D.modThree (isPGLAt_pow D.isPGLAt_a j)
      (D.type3_pow hj0 hj) hmem
  subst hj0
  refine ⟨l, ⟨hl, ?_⟩, i, hi, by rw [pow_zero, mul_one]⟩
  have e : l = (l * D.u ^ i * D.a ^ 0) * (D.u ^ i)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ (Subgroup.pow_mem _ D.mem_centralizer i))

theorem pow_three_and_commute_of_mem {l : X}
    (hl : l ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X)) : l ^ 3 = 1 ∧ l * D.a = D.a * l := by
  have hcen : D.e ⟨l, hl.1⟩ ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨m, rfl⟩ := D.e.surjective s
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hl.2 m m.2)
  refine ⟨?_, ?_⟩
  · have h1 := pow_three_eq_one_of_mem_center D.piField D.modThree hcen
    have h2 : (⟨l, hl.1⟩ : D.L₀) ^ 3 = 1 := D.e.injective (by rw [map_pow, h1, map_one])
    exact congrArg Subtype.val h2
  · have hs := mem_statedScalars_of_mem_center D.piField D.modThree hcen
    have h1 := D.act ⟨l, hl.1⟩
    rw [commute_of_mem_statedScalars hs D.y, mul_inv_cancel_right] at h1
    have h2 : (⟨D.a * l * D.a⁻¹, D.normal.conj_mem l hl.1 D.a⟩ : D.L₀) = ⟨l, hl.1⟩ :=
      D.e.injective (Subtype.ext h1)
    have h3 : D.a * l * D.a⁻¹ = l := congrArg Subtype.val h2
    calc l * D.a = (D.a * l * D.a⁻¹) * D.a := by rw [h3]
      _ = D.a * l := by group

theorem commutator_pow (n : ℕ) :
    D.u ^ n * D.a * (D.u ^ n)⁻¹ * D.a⁻¹ = (D.u * D.a * D.u⁻¹ * D.a⁻¹) ^ n := by
  set c₀ := D.u * D.a * D.u⁻¹ * D.a⁻¹ with hc₀
  have hcu : ∀ k : ℕ, D.u * c₀ ^ k = c₀ ^ k * D.u := fun k =>
    ((Subgroup.mem_centralizer_iff.mp D.mem_centralizer _ (pow_mem D.comm_mem.1 k))).symm
  induction n with
  | zero => simp
  | succ n ih =>
    calc D.u ^ (n + 1) * D.a * (D.u ^ (n + 1))⁻¹ * D.a⁻¹ =
        D.u * (D.u ^ n * D.a * (D.u ^ n)⁻¹ * D.a⁻¹) * (D.a * D.u⁻¹ * D.a⁻¹) := by group
      _ = D.u * c₀ ^ n * (D.a * D.u⁻¹ * D.a⁻¹) := by rw [ih]
      _ = c₀ ^ n * (D.u * D.a * D.u⁻¹ * D.a⁻¹) := by rw [hcu n]; group
      _ = c₀ ^ (n + 1) := by rw [pow_succ]

theorem center_le : Subgroup.center X ≤ D.L₀ := by
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (D.L₀ : Set X) := Subgroup.center_le_centralizer _ hz
  obtain ⟨l, hl, i, hi, rfl⟩ := D.exists_of_mem_centralizer hzC
  obtain ⟨-, hla⟩ := D.pow_three_and_commute_of_mem hl
  obtain ⟨hc3, -⟩ := D.pow_three_and_commute_of_mem D.comm_mem
  have hza : D.a * (l * D.u ^ i) = (l * D.u ^ i) * D.a := Subgroup.mem_center_iff.mp hz D.a
  have hua : D.u ^ i * D.a = D.a * D.u ^ i := by
    have e1 : l * (D.u ^ i * D.a) = l * (D.a * D.u ^ i) := by
      calc l * (D.u ^ i * D.a) = (l * D.u ^ i) * D.a := by group
        _ = D.a * (l * D.u ^ i) := hza.symm
        _ = (D.a * l) * D.u ^ i := by group
        _ = (l * D.a) * D.u ^ i := by rw [hla]
        _ = l * (D.a * D.u ^ i) := by group
    exact mul_left_cancel e1
  have hci : (D.u * D.a * D.u⁻¹ * D.a⁻¹) ^ i = 1 := by
    rw [← D.commutator_pow i, hua]
    group
  have hord : orderOf (D.u * D.a * D.u⁻¹ * D.a⁻¹) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) D.comm_ne
    · exact h
  have hi0 : i = 0 := by
    have := orderOf_dvd_of_pow_eq_one hci
    rw [hord] at this
    omega
  subst hi0
  rw [pow_zero, mul_one]
  exact hl.1

theorem le_of_isPerfect {Q : Subgroup X} (hQ : Group.IsPerfect Q) : Q ≤ D.L₀ := by
  have hQQ : ⁅Q, Q⁆ = Q := Subgroup.commutator_eq_self
  rw [← hQQ]
  exact (Subgroup.commutator_mono le_top le_top).trans (commutator_def X ▸ D.commutator_le)

theorem le_of_normal (hq2 : 2 < p ^ f) {Q : Subgroup X} (hQn : Q.Normal)
    (hQ : Group.IsPerfect Q) (hQ1 : Q ≠ ⊥) : D.L₀ ≤ Q := by
  have hQL := D.le_of_isPerfect hQ
  have hqs : CFSG.IsQuasisimple D.L₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv D.e.symm (isQuasisimple_slPi D.piField hq2)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (hQn.subgroupOf D.L₀) with h | h
  · intro x hx
    have : (⟨x, hx⟩ : D.L₀) ∈ Q.subgroupOf D.L₀ := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hcomm : IsMulCommutative Q := ⟨⟨fun q₁ q₂ => by
      have h1 : (⟨q₁, hQL q₁.2⟩ : D.L₀) ∈ Subgroup.center D.L₀ :=
        h (Subgroup.mem_subgroupOf.mpr q₁.2)
      have h2 := Subgroup.mem_center_iff.mp h1 ⟨q₂, hQL q₂.2⟩
      exact Subtype.ext (congrArg Subtype.val h2).symm⟩⟩
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    exact Group.IsPerfect.not_isMulCommutative Q hcomm

include D in
theorem isSolvable_of_two (h2 : p ^ f = 2) : Group.IsSolvable X := by
  have hK := D.piField
  cases π
  · have := isSolvable_slPi_two hK h2
    have : Group.IsSolvable D.L₀ :=
      Group.isSolvable_of_isSolvable_injective (f := D.e.toMonoidHom) D.e.injective
    have : Group.IsSolvable (X ⧸ D.L₀) := Group.isSolvable_of_comm fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D.L₀ x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D.L₀ y
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ D.L₀ := D.commutator_le
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      have h2 : QuotientGroup.mk' D.L₀ (x * y * x⁻¹ * y⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      calc QuotientGroup.mk' D.L₀ x * QuotientGroup.mk' D.L₀ y =
          (QuotientGroup.mk' D.L₀ x * QuotientGroup.mk' D.L₀ y *
            (QuotientGroup.mk' D.L₀ x)⁻¹ * (QuotientGroup.mk' D.L₀ y)⁻¹) *
            (QuotientGroup.mk' D.L₀ y * QuotientGroup.mk' D.L₀ x) := by group
        _ = _ := by rw [h2, one_mul]
    exact Group.isSolvable_of_ker_le_range D.L₀.subtype (QuotientGroup.mk' D.L₀) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · exfalso
    have := D.modThree
    change p ^ f % 3 = 1 at this
    omega

end SLTwoData

theorem slTwoCenter : SLTwoCenter := by
  intro X _ hX Q hQn hQ hQ1
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hX
  by_cases hq2 : 2 < p ^ f
  · exact D.center_le.trans (D.le_of_normal hq2 hQn hQ hQ1)
  · exfalso
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective Q.subtype_injective
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    exact Group.IsPerfect.not_isSolvable Q inferInstance

namespace SLTwoData

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
  (D : SLTwoData X π p f K)

theorem commute_of_mem_centralizer {z z' : X} (hz : z ∈ Subgroup.centralizer (D.L₀ : Set X))
    (hz' : z' ∈ Subgroup.centralizer (D.L₀ : Set X)) : z * z' = z' * z := by
  obtain ⟨l, hl, i, -, rfl⟩ := D.exists_of_mem_centralizer hz
  obtain ⟨l', hl', i', -, rfl⟩ := D.exists_of_mem_centralizer hz'
  have h1 : l * l' = l' * l := Subgroup.mem_centralizer_iff.mp hl'.2 l hl.1
  have h2 : ∀ (m : X) (k : ℕ), m ∈ D.L₀ → D.u ^ k * m = m * D.u ^ k := fun m k hm =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ D.mem_centralizer k) m hm).symm
  calc l * D.u ^ i * (l' * D.u ^ i') = l * (D.u ^ i * l') * D.u ^ i' := by group
    _ = l * (l' * D.u ^ i) * D.u ^ i' := by rw [h2 l' i hl'.1]
    _ = (l * l') * (D.u ^ i * D.u ^ i') := by group
    _ = (l' * l) * (D.u ^ i' * D.u ^ i) := by rw [h1, ← pow_add, ← pow_add, add_comm]
    _ = l' * (D.u ^ i' * l) * D.u ^ i := by rw [h2 l i' hl.1]; group
    _ = l' * D.u ^ i' * (l * D.u ^ i) := by group

theorem card_inf_centralizer_le : Nat.card (D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) :
    Subgroup X) ≤ 3 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau D.piField D.modThree
  have hex : ∀ z : (D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) : Subgroup X), ∃ k : Fin 3,
      ((D.e ⟨z, z.2.1⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        τ ^ (k : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro z
    refine exists_tau_pow_of_mem_center D.piField D.modThree hτ hτ1 (D.e ⟨z, z.2.1⟩).2
      fun x hx => ?_
    obtain ⟨m, hm⟩ := D.e.surjective ⟨x, hx⟩
    have h1 : (⟨z, z.2.1⟩ : D.L₀) * m = m * ⟨z, z.2.1⟩ :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp z.2.2 m m.2).symm)
    have h2 := congrArg (fun w => ((D.e w : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
    simp only [map_mul, Subgroup.coe_mul, hm] at h2
    exact h2
  choose k hk using hex
  refine (Nat.card_le_card_of_injective k fun z z' hzz' => ?_).trans (by rw [Nat.card_fin])
  have h1 : D.e ⟨z, z.2.1⟩ = D.e ⟨z', z'.2.1⟩ :=
    Subtype.ext (Units.ext (by rw [hk z, hk z', hzz']))
  have h2 : (z : X) = z' := congrArg (fun w : D.L₀ => (w : X)) (D.e.injective h1)
  exact Subtype.ext h2

theorem inf_centralizer_le_zpowers [Finite X] {c : X}
    (hc : c ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X)) (hc1 : c ≠ 1) :
    D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) ≤ Subgroup.zpowers c := by
  obtain ⟨hc3, -⟩ := D.pow_three_and_commute_of_mem hc
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hle : Subgroup.zpowers c ≤ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) :=
    Subgroup.zpowers_le.mpr hc
  rw [Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact D.card_inf_centralizer_le)]

theorem card_quotient_le :
    Nat.card (X ⧸ (D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X))) ≤ 3 := by
  set N := D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X)
  have hsurj : Function.Surjective (fun j : Fin 3 => (QuotientGroup.mk' N) (D.a ^ (j : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨l, hl, i, -, j, hj, rfl⟩ := D.exists_normal_form x
    refine ⟨⟨j, hj⟩, ?_⟩
    have h1 : QuotientGroup.mk' N (l * D.u ^ i) = 1 := (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ D.mem_centralizer i)))
    change QuotientGroup.mk' N (D.a ^ j) = QuotientGroup.mk' N (l * D.u ^ i * D.a ^ j)
    rw [map_mul (QuotientGroup.mk' N) (l * D.u ^ i), h1, one_mul]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans (by rw [Nat.card_fin])

theorem a_not_mem_sup : D.a ∉ D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X) :=
  not_mem_sup_centralizer_of_type3 D.piField D.modThree D.isPGLAt_a D.type3

theorem card_inf_sup_eq_nine [Finite X] {A : Subgroup X} (h27 : Nat.card A = 27)
    (hsup : D.L₀ ⊔ A = ⊤) :
    Nat.card (A ⊓ (D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X)) : Subgroup X) = 9 := by
  set N := D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X) with hN
  have hBN : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 : Nat.card (N.subgroupOf A) * N.relIndex A = 27 := by
    rw [← h27]
    exact Subgroup.card_mul_index _
  have h2 : N.relIndex A ≤ 3 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal N A)).trans D.card_quotient_le
  rw [hBN] at h1
  have hne : Nat.card (A ⊓ N : Subgroup X) ≠ 27 := by
    intro h
    have hAN : A ⊓ N = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h27])
    apply D.a_not_mem_sup
    have : (⊤ : Subgroup X) ≤ N := by
      rw [← hsup]
      exact sup_le le_sup_left (hAN ▸ inf_le_right)
    exact this (Subgroup.mem_top _)
  interval_cases h : N.relIndex A <;> omega

theorem exists_E [Finite X] {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hsup : D.L₀ ⊔ A = ⊤) {c : X} (hcL : c ∈ D.L₀)
    (hcZ : c ∈ Subgroup.center X) (hc1 : c ≠ 1) (hcA : c ∈ A)
    (hC : A ⊓ Subgroup.centralizer (D.L₀ : Set X) ≤ Subgroup.zpowers c) :
    ∃ E : Subgroup X, E ≤ Subgroup.normalizer (A : Set X) ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 27 ∧ c ∈ E ∧ D.u ∈ E ∧ ∃ v ∈ E, v ∈ D.L₀ ∧ v ∉ Subgroup.zpowers c := by
  set N := D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X) with hN
  have hcommA : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcC : c ∈ Subgroup.centralizer (D.L₀ : Set X) := Subgroup.center_le_centralizer _ hcZ
  have hZc := D.inf_centralizer_le_zpowers ⟨hcL, hcC⟩ hc1
  have hu3 : D.u ^ 3 = 1 := by rw [← D.orderOf_u, pow_orderOf_eq_one]
  have hzc : Subgroup.zpowers c ≤ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) :=
    Subgroup.zpowers_le.mpr ⟨hcL, hcC⟩
  set B := A ⊓ N with hB
  have hB9 : Nat.card B = 9 := D.card_inf_sup_eq_nine h27 hsup
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
    obtain ⟨hc3, -⟩ := D.pow_three_and_commute_of_mem ⟨hcL, hcC⟩
    rw [Nat.card_zpowers]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  obtain ⟨b, hbB, hbc⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers c from h)
    rw [hB9, hc3] at this
    omega
  obtain ⟨l, hl, z, hz, hlz⟩ := Subgroup.mem_sup_of_normal_left.mp hbB.2
  obtain ⟨l', hl', i, -, rfl⟩ := D.exists_of_mem_centralizer hz
  have hvL : l * l' ∈ D.L₀ := D.L₀.mul_mem hl hl'.1
  have hbv : b = (l * l') * D.u ^ i := by rw [← hlz]; group
  have hvc : l * l' ∉ Subgroup.zpowers c := by
    intro h
    apply hbc
    have hvC : l * l' ∈ Subgroup.centralizer (D.L₀ : Set X) := (hzc h).2
    exact hC ⟨hbB.1, hbv ▸ Subgroup.mul_mem _ hvC (Subgroup.pow_mem _ D.mem_centralizer i)⟩
  have hub : ∀ x ∈ B, D.u * x = x * D.u := by
    intro x hx
    obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx.2
    have h1 : D.u * l₁ = l₁ * D.u :=
      (Subgroup.mem_centralizer_iff.mp D.mem_centralizer l₁ hl₁).symm
    have h2 : D.u * z₁ = z₁ * D.u := D.commute_of_mem_centralizer D.mem_centralizer hz₁
    calc D.u * (l₁ * z₁) = (D.u * l₁) * z₁ := by group
      _ = l₁ * (D.u * z₁) := by rw [h1]; group
      _ = l₁ * z₁ * D.u := by rw [h2]; group
  have hubk : ∀ x ∈ B, ∀ k : ℕ, D.u ^ k * x = x * D.u ^ k := fun x hx k =>
    ((Commute.pow_left (hub x hx) k)).eq
  have hinv : ∀ k : ℕ, (D.u ^ k)⁻¹ = D.u ^ (2 * k) := fun k => by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hu3, one_pow]
  have hBu : ∀ m < 3, D.u ^ m ∈ B → m = 0 := by
    intro m hm hmB
    have h1 : D.u ^ m ∈ D.L₀ := (hZc ⟨(hzc (hC ⟨hmB.1, Subgroup.pow_mem _ D.mem_centralizer m⟩)).1,
      Subgroup.pow_mem _ D.mem_centralizer m⟩ |> fun h => (hzc h).1)
    interval_cases m
    · rfl
    · exact absurd (by simpa using h1) D.not_mem
    · exfalso
      apply D.not_mem
      have e : (D.u ^ 2) ^ 2 = D.u := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hu3, one_mul, pow_one]
      rw [← e]
      exact D.L₀.pow_mem h1 2
  let E : Subgroup X :=
    { carrier := {y | ∃ x ∈ B, ∃ k : ℕ, y = x * D.u ^ k}
      mul_mem' := by
        rintro _ _ ⟨x, hx, k, rfl⟩ ⟨x', hx', k', rfl⟩
        refine ⟨x * x', B.mul_mem hx hx', k + k', ?_⟩
        calc x * D.u ^ k * (x' * D.u ^ k') = x * (D.u ^ k * x') * D.u ^ k' := by group
          _ = x * (x' * D.u ^ k) * D.u ^ k' := by rw [hubk x' hx' k]
          _ = x * x' * D.u ^ (k + k') := by rw [pow_add]; group
      one_mem' := ⟨1, B.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, k, rfl⟩
        refine ⟨x⁻¹, B.inv_mem hx, 2 * k, ?_⟩
        rw [_root_.mul_inv_rev, hinv k]
        exact (hubk x⁻¹ (B.inv_mem hx) (2 * k)) }
  have hmemE : ∀ {y : X}, y ∈ E ↔ ∃ x ∈ B, ∃ k : ℕ, y = x * D.u ^ k := Iff.rfl
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, l * l', ?_, hvL, hvc⟩
  ·
    have huN : D.u ∈ Subgroup.normalizer (A : Set X) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have h1 : D.u * y * D.u⁻¹ * y⁻¹ ∈ D.L₀ := D.commutator_le
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top D.u) (Subgroup.mem_top y))
      have h2 : D.u * y * D.u⁻¹ * y⁻¹ ∈ Subgroup.centralizer (D.L₀ : Set X) := by
        have e : D.u * y * D.u⁻¹ * y⁻¹ = D.u * (y * D.u⁻¹ * y⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ D.mem_centralizer
          ((inferInstance : (Subgroup.centralizer (D.L₀ : Set X)).Normal).conj_mem _
            (Subgroup.inv_mem _ D.mem_centralizer) y)
      have h3 : D.u * y * D.u⁻¹ * y⁻¹ ∈ A :=
        Subgroup.zpowers_le.mpr hcA (hZc ⟨h1, h2⟩)
      have e : D.u * y * D.u⁻¹ = (D.u * y * D.u⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact A.mul_mem h3 hy
    rintro _ ⟨x, hx, k, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hx.1) (Subgroup.pow_mem _ huN k)
  ·
    refine ⟨⟨⟨fun y y' => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, k, hy⟩ := hmemE.mp y.2
      obtain ⟨x', hx', k', hy'⟩ := hmemE.mp y'.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hy, hy']
      calc x * D.u ^ k * (x' * D.u ^ k') = (x * x') * (D.u ^ k * D.u ^ k') := by
            rw [mul_assoc, ← mul_assoc (D.u ^ k), hubk x' hx' k]; group
        _ = (x' * x) * (D.u ^ k' * D.u ^ k) := by
            rw [hcommA x hx.1 x' hx'.1, ← pow_add, ← pow_add, add_comm]
        _ = x' * (x * D.u ^ k') * D.u ^ k := by group
        _ = x' * (D.u ^ k' * x) * D.u ^ k := by rw [hubk x hx k']
        _ = x' * D.u ^ k' * (x * D.u ^ k) := by group
    · rintro _ ⟨x, hx, k, rfl⟩
      have hc : Commute x (D.u ^ k) := (hubk x hx k).symm
      rw [hc.mul_pow, hA.2 x hx.1, one_mul, ← pow_mul, mul_comm, pow_mul, hu3, one_pow]
  ·
    let φ : B × Fin 3 → E := fun xk => ⟨xk.1 * D.u ^ (xk.2 : ℕ), xk.1, xk.1.2, xk.2, rfl⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun ⟨x, k⟩ ⟨x', k'⟩ h => ?_, fun ⟨y, x, hx, k, hy⟩ => ⟨(⟨x, hx⟩, ⟨k % 3,
        Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩⟩
      · have h1 : (x : X) * D.u ^ (k : ℕ) = x' * D.u ^ (k' : ℕ) := congrArg Subtype.val h
        have h2 : D.u ^ ((k' : ℕ) + 2 * (k : ℕ)) = (x' : X)⁻¹ * x := by
          rw [pow_add, ← hinv]
          calc D.u ^ (k' : ℕ) * (D.u ^ (k : ℕ))⁻¹ =
              (x' : X)⁻¹ * (x' * D.u ^ (k' : ℕ)) * (D.u ^ (k : ℕ))⁻¹ := by group
            _ = (x' : X)⁻¹ * (x * D.u ^ (k : ℕ)) * (D.u ^ (k : ℕ))⁻¹ := by rw [h1]
            _ = (x' : X)⁻¹ * x := by group
        have h3 : D.u ^ (((k' : ℕ) + 2 * (k : ℕ)) % 3) ∈ B := by
          have e : D.u ^ ((k' : ℕ) + 2 * (k : ℕ)) =
              D.u ^ (((k' : ℕ) + 2 * (k : ℕ)) % 3) := by
            conv_lhs => rw [← Nat.div_add_mod ((k' : ℕ) + 2 * (k : ℕ)) 3, pow_add, pow_mul, hu3,
              one_pow, one_mul]
          rw [← e, h2]
          exact B.mul_mem (B.inv_mem x'.2) x.2
        have h4 := hBu _ (Nat.mod_lt _ (by norm_num)) h3
        have hkk : k = k' := by
          ext
          have := k.2
          have := k'.2
          omega
        subst hkk
        have h5 : (x : X) = x' := mul_right_cancel h1
        rw [Subtype.ext h5]
      · change x * D.u ^ (k % 3) = y
        rw [hy]
        congr 1
        conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hu3, one_pow, one_mul]
    rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, hB9, Nat.card_fin]
  · exact ⟨c, ⟨hcA, Subgroup.mem_sup_left hcL⟩, 0, by rw [pow_zero, mul_one]⟩
  · exact ⟨1, B.one_mem, 1, by rw [pow_one, one_mul]⟩
  · refine ⟨b, hbB, 2 * i, ?_⟩
    rw [← hinv, hbv]
    group

end SLTwoData

end CFSG.RankThree.PartTwo.Sec13

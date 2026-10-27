module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.I62

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem exists_ne_one_comm_of_normalizes [Finite G] {S : Subgroup G} (h2 : 2 ∣ Nat.card S)
    {m : G} (hmN : m ∈ Subgroup.normalizer (S : Set G)) {n : ℕ} (hm : m ^ (2 ^ n) = 1) :
    ∃ d ∈ S, d ≠ 1 ∧ m * d = d * m := by
  classical
  have hf : ∀ x : G, (MulAut.toPerm G (MulAut.conj m)) x ∈ S ↔ x ∈ S := fun x =>
    (Subgroup.mem_normalizer_iff.1 hmN x).symm
  let σ : Equiv.Perm {x // x ∈ S} := (MulAut.toPerm G (MulAut.conj m)).subtypePerm hf
  have hfpow : (MulAut.toPerm G (MulAut.conj m)) ^ 2 ^ n = 1 := by
    rw [← map_pow, ← map_pow, hm, map_one, map_one]
  have hσ : σ ^ 2 ^ n = 1 := by
    ext ⟨x, hx⟩
    simp only [σ, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply, hfpow,
      Equiv.Perm.coe_one, id_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥S := Fintype.ofFinite _
  have hcard : 2 ∣ Fintype.card {x // x ∈ S} := by
    rw [← Nat.card_eq_fintype_card]
    exact h2
  have h1 : σ ⟨1, S.one_mem⟩ = ⟨1, S.one_mem⟩ := by
    apply Subtype.ext
    show m * 1 * m⁻¹ = 1
    group
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hcard hσ h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have hb' : m * (b : G) * m⁻¹ = b := congrArg Subtype.val hb
  calc m * (b : G) = m * (b : G) * m⁻¹ * m := by group
    _ = (b : G) * m := by rw [hb']

theorem conj_commutatorElement_of_mul_self {a u : G} (hu : u * u = 1) :
    u * ⁅a, u⁆ * u⁻¹ = ⁅a, u⁆⁻¹ := by
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  rw [commutatorElement_def, hinv]
  calc u * (a * u * a⁻¹ * u) * u = u * a * u * a⁻¹ * (u * u) := by group
    _ = (a * u * a⁻¹ * u)⁻¹ := by
        rw [hu, mul_one]
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hinv, inv_inv]
        group

theorem two_dvd_card_of_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    2 ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rcases k with _ | k
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hne
  · rw [hk]
    exact dvd_pow_self 2 (Nat.succ_ne_zero k)

theorem mem_normalizer_of_conj {K : Subgroup G} {g : G} (h1 : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, g⁻¹ * k * g ∈ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h1 k, fun hk => ?_⟩
  have := h2 _ hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g = k by group] at this

structure Base (V A : Subgroup G) : Prop where
  hV : IsElemAbelian 2 V
  hA : IsElemAbelian 2 A
  tiV : IsTISetIn V ⊤
  tiA : IsTISetIn A ⊤
  inf : V ⊓ A = ⊥

namespace Base

variable {V A : Subgroup G} (h : Base V A)
include h

theorem symm : Base A V := ⟨h.hA, h.hV, h.tiA, h.tiV, by rw [inf_comm]; exact h.inf⟩

theorem comm_V {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  congrArg Subtype.val (h.hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mul_self_V {x : G} (hx : x ∈ V) : x * x = 1 := by
  rw [← sq]
  exact h.hV.2 x hx

theorem mem_normalizer_of_inf_ne_bot {g : G} (hne : V ⊓ conjSubgroup V g ≠ ⊥) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  by_contra hgN
  exact hne (h.tiV.2 g (Subgroup.mem_top g) hgN)

theorem mem_normalizer_of_comm {v g : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hg : g * v = v * g) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  refine h.mem_normalizer_of_inf_ne_bot fun hbot => hv1 ?_
  have hmem : v ∈ V ⊓ conjSubgroup V g := by
    refine ⟨hv, mem_conjSubgroup_iff.mpr ?_⟩
    rw [hg, mul_inv_cancel_right]
    exact hv
  rw [hbot] at hmem
  exact hmem

theorem inf_centralizer_eq {u : G} (hu : u ∈ tiU V A) (hu1 : u ≠ 1) :
    A ⊓ Subgroup.centralizer ({u} : Set G) = tiB V A := by
  apply le_antisymm
  · rintro a ⟨haA, hau⟩
    exact ⟨haA, h.mem_normalizer_of_comm hu.1 hu1 (Subgroup.mem_centralizer_singleton_iff.mp hau)⟩
  · rintro b ⟨hbA, hbN⟩
    refine ⟨hbA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : b * u * b⁻¹ * u⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp hbN u).mp hu.1) (V.inv_mem hu.1)
    have h2 : b * u * b⁻¹ * u⁻¹ ∈ A := by
      have : u * b⁻¹ * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hu.2 b⁻¹).mp (A.inv_mem hbA)
      rw [show b * u * b⁻¹ * u⁻¹ = b * (u * b⁻¹ * u⁻¹) by group]
      exact A.mul_mem hbA this
    have h3 : b * u * b⁻¹ * u⁻¹ ∈ V ⊓ A := ⟨h1, h2⟩
    rw [h.inf, Subgroup.mem_bot] at h3
    calc b * u = b * u * b⁻¹ * u⁻¹ * u * b := by group
      _ = u * b := by rw [h3, one_mul]

theorem inf_centralizer_eq' {b : G} (hb : b ∈ tiB V A) (hb1 : b ≠ 1) :
    V ⊓ Subgroup.centralizer ({b} : Set G) = tiU V A :=
  h.symm.inf_centralizer_eq hb hb1

theorem tiU_inf_tiB : tiU V A ⊓ tiB V A = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxB⟩
  have : x ∈ V ⊓ A := ⟨hxU.1, hxB.1⟩
  rwa [h.inf] at this

theorem comm_tiU_tiB {u b : G} (hu : u ∈ tiU V A) (hb : b ∈ tiB V A) : u * b = b * u := by
  by_cases hu1 : u = 1
  · rw [hu1, one_mul, mul_one]
  · have : b ∈ A ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [h.inf_centralizer_eq hu hu1]
      exact hb
    exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm

theorem commutator_tiU_tiB : ⁅tiU V A, tiB V A⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro u hu b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact h.comm_tiU_tiB hu hb

theorem isElemAbelian_tiU : IsElemAbelian 2 (tiU V A) := B2F.isElemAbelian_mono inf_le_left h.hV

theorem isElemAbelian_tiB : IsElemAbelian 2 (tiB V A) := B2F.isElemAbelian_mono inf_le_left h.hA

theorem isElemAbelian_tiY : IsElemAbelian 2 (tiY V A) :=
  B2F.isElemAbelian_sup_of_commute h.isElemAbelian_tiU h.isElemAbelian_tiB
    fun _ hu _ hb => h.comm_tiU_tiB hu hb

theorem comm_tiY {x y : G} (hx : x ∈ tiY V A) (hy : y ∈ tiY V A) : x * y = y * x :=
  congrArg Subtype.val (h.isElemAbelian_tiY.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem inv_eq_of_mem_tiY {x : G} (hx : x ∈ tiY V A) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.isElemAbelian_tiY.2 x hx)

omit h in
theorem tiY_symm : tiY A V = tiY V A := sup_comm _ _

theorem tiB_le_normalizer_tiU : tiB V A ≤ Subgroup.normalizer (tiU V A : Set G) := by
  intro b hb
  refine mem_normalizer_of_conj (fun u hu => ?_) (fun u hu => ?_)
  · rw [← h.comm_tiU_tiB hu hb, mul_inv_cancel_right]
    exact hu
  · rw [show b⁻¹ * u * b = b⁻¹ * (u * b) by group, h.comm_tiU_tiB hu hb, inv_mul_cancel_left]
    exact hu

theorem exists_mul_of_mem_tiY {y : G} (hy : y ∈ tiY V A) :
    ∃ u ∈ tiU V A, ∃ b ∈ tiB V A, u * b = y := by
  have hY : ((tiY V A : Subgroup G) : Set G) = (tiU V A : Set G) * (tiB V A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ h.tiB_le_normalizer_tiU
  have : y ∈ (tiU V A : Set G) * (tiB V A : Set G) := by
    rw [← hY]
    exact hy
  obtain ⟨u, hu, b, hb, rfl⟩ := this
  exact ⟨u, hu, b, hb, rfl⟩

theorem commutatorElement_mem_tiB {a u : G} (ha : a ∈ A) (hu : u ∈ tiU V A) :
    ⁅a, u⁆ ∈ tiB V A := by
  by_cases hu1 : u = 1
  · rw [hu1, commutatorElement_one_right]
    exact (tiB V A).one_mem
  rw [← h.inf_centralizer_eq hu hu1]
  have hcA : ⁅a, u⁆ ∈ A := by
    rw [commutatorElement_def, show a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) by group]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hu.2 a⁻¹).mp (A.inv_mem ha))
  refine ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := conj_commutatorElement_of_mul_self (a := a) (h.mul_self_V hu.1)
  have hinv : ⁅a, u⁆⁻¹ = ⁅a, u⁆ :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.hA.2 _ hcA)
  rw [hinv] at h1
  calc ⁅a, u⁆ * u = u * ⁅a, u⁆ * u⁻¹ * u := by rw [h1]
    _ = u * ⁅a, u⁆ := by group

theorem tiA_le_normalizer_tiY : A ≤ Subgroup.normalizer (tiY V A : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ tiY V A, a * y * a⁻¹ ∈ tiY V A := by
    intro a ha y hy
    obtain ⟨u, hu, b, hb, rfl⟩ := h.exists_mul_of_mem_tiY hy
    have hab : a * b = b * a :=
      congrArg Subtype.val (h.hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb.1⟩)
    have hab' : b * a⁻¹ = a⁻¹ * b := by
      calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
        _ = a⁻¹ * (b * a) * a⁻¹ := by rw [hab]
        _ = a⁻¹ * b := by group
    have e : a * (u * b) * a⁻¹ = ⁅a, u⁆ * u * b := by
      calc a * (u * b) * a⁻¹ = a * u * (b * a⁻¹) := by group
        _ = a * u * (a⁻¹ * b) := by rw [hab']
        _ = ⁅a, u⁆ * u * b := by rw [commutatorElement_def]; group
    rw [e]
    exact (tiY V A).mul_mem ((tiY V A).mul_mem
      (Subgroup.mem_sup_right (h.commutatorElement_mem_tiB ha hu)) (Subgroup.mem_sup_left hu))
      (Subgroup.mem_sup_right hb)
  intro a ha
  exact mem_normalizer_of_conj (key a ha) (fun y hy => by
    simpa using key a⁻¹ (A.inv_mem ha) y hy)

theorem tiV_le_normalizer_tiY : V ≤ Subgroup.normalizer (tiY V A : Set G) := by
  have := h.symm.tiA_le_normalizer_tiY
  rwa [tiY_symm] at this

theorem tiX_le_normalizer_tiY : tiX V A ≤ Subgroup.normalizer (tiY V A : Set G) :=
  sup_le h.tiV_le_normalizer_tiY h.tiA_le_normalizer_tiY

theorem inf_centralizer_tiY {v : G} (hv : v ∈ V) (hvU : v ∉ tiU V A) :
    tiY V A ⊓ Subgroup.centralizer ({v} : Set G) = tiU V A := by
  apply le_antisymm
  · rintro y ⟨hy, hyv⟩
    obtain ⟨u, hu, b, hb, rfl⟩ := h.exists_mul_of_mem_tiY hy
    have h1 : u * b * v = v * (u * b) := Subgroup.mem_centralizer_singleton_iff.mp hyv
    have huv := h.comm_V hu.1 hv
    have hbv : b * v = v * b := by
      have : u * (b * v) = u * (v * b) := by
        calc u * (b * v) = u * b * v := by group
          _ = v * (u * b) := h1
          _ = (v * u) * b := by group
          _ = u * (v * b) := by rw [← huv]; group
      exact mul_left_cancel this
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      exact hu
    · exfalso
      apply hvU
      have : v ∈ V ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hbv.symm⟩
      rwa [h.inf_centralizer_eq' hb hb1] at this
  · intro u hu
    exact ⟨Subgroup.mem_sup_left hu,
      Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_V hu.1 hv)⟩

theorem inf_centralizer_tiY' {a : G} (ha : a ∈ A) (haB : a ∉ tiB V A) :
    tiY V A ⊓ Subgroup.centralizer ({a} : Set G) = tiB V A := by
  have := h.symm.inf_centralizer_tiY ha haB
  rwa [tiY_symm] at this

theorem tiU_eq_inf_centralizer {v : G} (hv : v ∈ V) (hvU : v ∉ tiU V A) :
    tiU V A = tiY V A ⊓ Subgroup.centralizer (V : Set G) := by
  apply le_antisymm
  · intro u hu
    refine ⟨Subgroup.mem_sup_left hu, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact h.comm_V hw hu.1
  · rintro y ⟨hy, hyV⟩
    rw [← h.inf_centralizer_tiY hv hvU]
    exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hyV v hv).symm⟩

theorem commutatorElement_mem_centralizer {x y : G} (hx : x ∈ tiX V A) (hx2 : x * x = 1)
    (hy : y ∈ tiY V A) :
    ⁅y, x⁆ ∈ tiY V A ⊓ Subgroup.centralizer ({x} : Set G) := by
  have hxN := h.tiX_le_normalizer_tiY hx
  have hmem : ⁅y, x⁆ ∈ tiY V A := by
    rw [commutatorElement_def, show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
    exact (tiY V A).mul_mem hy ((Subgroup.mem_normalizer_iff.mp hxN y⁻¹).mp
      ((tiY V A).inv_mem hy))
  refine ⟨hmem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := conj_commutatorElement_of_mul_self (a := y) hx2
  rw [h.inv_eq_of_mem_tiY hmem] at h1
  calc ⁅y, x⁆ * x = x * ⁅y, x⁆ * x⁻¹ * x := by rw [h1]
    _ = x * ⁅y, x⁆ := by group

@[expose] noncomputable def commHom {x : G} (hx : x ∈ tiX V A) (hx2 : x * x = 1) :
    ↥(tiY V A) →* ↥(tiY V A) :=
  MonoidHom.mk' (fun y => ⟨⁅(y : G), x⁆, (h.commutatorElement_mem_centralizer hx hx2 y.2).1⟩)
    (fun y z => by
      apply Subtype.ext
      have hxN := h.tiX_le_normalizer_tiY hx
      have hp : x * (y : G)⁻¹ * x⁻¹ ∈ tiY V A :=
        (Subgroup.mem_normalizer_iff.mp hxN _).mp ((tiY V A).inv_mem y.2)
      have hq : x * (z : G)⁻¹ * x⁻¹ ∈ tiY V A :=
        (Subgroup.mem_normalizer_iff.mp hxN _).mp ((tiY V A).inv_mem z.2)
      show ⁅(y : G) * z, x⁆ = ⁅(y : G), x⁆ * ⁅(z : G), x⁆
      simp only [commutatorElement_def]
      have hc := h.comm_tiY hp ((tiY V A).mul_mem z.2 hq)
      calc (y : G) * z * x * ((y : G) * z)⁻¹ * x⁻¹ =
          (y : G) * ((z : G) * (x * (z : G)⁻¹ * x⁻¹)) * (x * (y : G)⁻¹ * x⁻¹) := by group
        _ = (y : G) * (x * (y : G)⁻¹ * x⁻¹) * ((z : G) * (x * (z : G)⁻¹ * x⁻¹)) := by
            rw [mul_assoc (y : G), ← hc, ← mul_assoc]
        _ = (y : G) * x * (y : G)⁻¹ * x⁻¹ * ((z : G) * x * (z : G)⁻¹ * x⁻¹) := by group)

theorem commHom_apply {x : G} (hx : x ∈ tiX V A) (hx2 : x * x = 1) (y : ↥(tiY V A)) :
    ((h.commHom hx hx2 y : ↥(tiY V A)) : G) = ⁅(y : G), x⁆ := rfl

variable [Finite G]

theorem card_tiB_le {v : G} (hv : v ∈ V) (hvU : v ∉ tiU V A) :
    Nat.card (tiB V A) ≤ Nat.card (tiU V A) := by
  have hvX : v ∈ tiX V A := Subgroup.mem_sup_left hv
  have hv2 := h.mul_self_V hv
  set φ := h.commHom hvX hv2 with hφ
  have hker : φ.ker = (tiU V A).subgroupOf (tiY V A) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← h.inf_centralizer_tiY hv hvU]
    constructor
    · intro hy1
      have h1 : ⁅(y : G), v⁆ = 1 := congrArg Subtype.val hy1
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp h1)⟩
    · rintro ⟨-, hyv⟩
      apply Subtype.ext
      show ⁅(y : G), v⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hyv)
  have hrange : φ.range ≤ (tiU V A).subgroupOf (tiY V A) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf, h.commHom_apply, ← h.inf_centralizer_tiY hv hvU]
    exact h.commutatorElement_mem_centralizer hvX hv2 y.2
  have hUY : tiU V A ≤ tiY V A := le_sup_left
  have hcU : Nat.card ↥((tiU V A).subgroupOf (tiY V A)) = Nat.card (tiU V A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv
  have e1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hcU] at e1
  have e2 : Nat.card ↥φ.range ≤ Nat.card (tiU V A) := by
    rw [← hcU]
    exact Subgroup.card_le_of_le hrange
  have e3 : Nat.card (tiY V A) = Nat.card (tiU V A) * Nat.card (tiB V A) := by
    have := B2F.card_sup_mul_card_inf_of_commute (A := tiU V A) (B := tiB V A)
      fun _ hu _ hb => h.comm_tiU_tiB hu hb
    rw [h.tiU_inf_tiB, Subgroup.card_bot, mul_one] at this
    exact this
  have hpos : 0 < Nat.card (tiU V A) := Nat.card_pos
  have : Nat.card (tiU V A) * Nat.card (tiB V A) ≤ Nat.card (tiU V A) * Nat.card (tiU V A) := by
    rw [← e3, ← e1]
    exact Nat.mul_le_mul_left _ e2
  exact Nat.le_of_mul_le_mul_left this hpos

end Base

structure Hyp (V A : Subgroup G) : Prop extends Base V A where
  card : Nat.card V = Nat.card A
  cross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥
  ne : tiU V A ≠ ⊥
  lt : tiU V A < V

theorem Hyp.mk' {V A : Subgroup G} (hVe : IsElemAbelian 2 V) (hAe : IsElemAbelian 2 A)
    (hcard : Nat.card V = Nat.card A) (hTIV : IsTISetIn V ⊤) (hTIA : IsTISetIn A ⊤)
    (hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥)
    (hU : tiU V A ≠ ⊥) (hUlt : tiU V A < V) : Hyp V A := by
  refine ⟨⟨hVe, hAe, hTIV, hTIA, ?_⟩, hcard, hcross, hU, hUlt⟩
  have hne : V ≠ conjSubgroup A 1 := by
    rw [conjSubgroup_one]
    rintro rfl
    exact hUlt.ne (inf_eq_left.mpr Subgroup.le_normalizer)
  have := hcross 1 hne
  rwa [conjSubgroup_one, inf_comm] at this

namespace Hyp

variable {V A : Subgroup G} (h : Hyp V A)
include h

theorem exists_mem_not_mem : ∃ v ∈ V, v ∉ tiU V A := by
  by_contra hcon
  push Not at hcon
  exact h.lt.ne (le_antisymm inf_le_left hcon)

variable [Finite G]

theorem exists_mem_not_mem' : ∃ a ∈ A, a ∉ tiB V A := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hvU⟩ := h.exists_mem_not_mem
  have hle := h.toBase.card_tiB_le hv hvU
  have hBA : tiB V A = A := le_antisymm inf_le_left hcon
  have hlt : Nat.card (tiU V A) < Nat.card V := Subgroup.card_lt_of_lt h.lt
  rw [hBA, ← h.card] at hle
  omega

end Hyp

end CFSG.Quasithin.I62

end

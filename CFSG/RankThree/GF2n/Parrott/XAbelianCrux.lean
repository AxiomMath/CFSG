module

public import CFSG.RankThree.GF2n.Parrott.SpinXFacts
public import CFSG.RankThree.GF2n.Parrott.XAbelianTools
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open CFSG.LinearAlgebra.F2Cube (fixedCount)
open scoped commutatorElement Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}

section Spin

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem exists_order_three_commuting {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3)
    (hρq : qH D ρ = xabRho) :
    ∃ r : ↥(H z), orderOf r = 3 ∧ qH D r = spinR0 ∧ r * ρ = ρ * r := by
  obtain ⟨hr3, hr1, -, -⟩ := spinOddFact
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf spinR0 = 3 := orderOf_eq_prime hr3 hr1
  obtain ⟨s₁, hs₁q, hs₁ρ⟩ := exists_lift_centralizer D hρ3 (g := spinR0)
    (by rw [hρq]; exact spinR0_comm_rho)
  obtain ⟨n, hn3, hnq⟩ := exists_zpow_orderOf_three_of_qH D s₁ (by rw [hs₁q]; exact hord)
  exact ⟨s₁ ^ n, hn3, by rw [hnq, hs₁q],
    (Commute.zpow_left (show Commute s₁ ρ from hs₁ρ) n).eq⟩

theorem conjV_fixed_iff_spinFixes (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (g : ↥(H z)) (w : V) :
    conjV h g (spinVecToV h P w) = spinVecToV h P w ↔ SpinFixes (qH D g) w := by
  rw [conjV_spinVecToV D h P hP]
  constructor
  · intro e
    exact spinVecToV_injective h P e
  · intro e
    show spinVecToV h P (((rhoA (qH D g) : GL8) : Mat8) *ᵥ w) = spinVecToV h P w
    rw [show ((rhoA (qH D g) : GL8) : Mat8) *ᵥ w = w from e]

theorem q_eq_zero_of_mul_self_eq_one (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {a : G} (ha : a ∈ J z)
    (haa : a * a = 1) {w : V} (hw : spinVecToV h P w = QuotientV.pi z ⟨a, ha⟩) : q w = 0 := by
  rw [← qVZMod_spinVecToV_eq_q D h P hP, hw, qVZMod_eq_zero_iff]
  apply Subtype.ext
  rw [qV_pi_coe, Subgroup.coe_one]
  simpa [pow_two] using haa

theorem commute_of_b_eq_zero (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {a a' : G} (ha : a ∈ J z)
    (ha' : a' ∈ J z) {w w' : V} (hw : spinVecToV h P w = QuotientV.pi z ⟨a, ha⟩)
    (hw' : spinVecToV h P w' = QuotientV.pi z ⟨a', ha'⟩) (hb : b w w' = 0) :
    a * a' = a' * a := by
  have h1 : polarVZMod h (QuotientV.pi z ⟨a, ha⟩) (QuotientV.pi z ⟨a', ha'⟩) = 0 := by
    rw [← hw, ← hw', polarVZMod_spinVecToV_eq_b D h P hP]
    exact hb
  exact ((polarVZMod_pi_eq_zero_iff h ⟨a, ha⟩ ⟨a', ha'⟩).mp h1).eq

theorem xab_fixDimV (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {x : G} (hxH : x ∈ H z)
    (hxq : qH D ⟨x, hxH⟩ = xabX) : fixDimV h ⟨x, hxH⟩ = 4 := by
  have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP ⟨x, hxH⟩
  rw [hxq] at h1
  have h2 : fixCard ((rhoA xabX : GL8) : Mat8) = 16 := xabX_fixedCount
  rw [h2] at h1
  exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))

theorem xab_crux (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxq : qH D ⟨x, hxH⟩ = xabX)
    {k : G} (hkH : k ∈ H z) (hkρ : k ∈ centralizer ({(ρ : G)} : Set G)) (hkx : k * x = x * k)
    (hkq : qH D ⟨k, hkH⟩ = tA)
    {a : G} (haJ : a ∈ J z) (haρ : a ∈ centralizer ({(ρ : G)} : Set G)) (hax : a * x = x * a) :
    k * a = a * k := by
  classical
  obtain ⟨hr3, hr1, hrt, hrfix⟩ := spinOddFact
  have hdim : fixDimV h ⟨x, hxH⟩ = 4 := xab_fixDimV D h P hP hxH hxq
  have hrv : ∀ r : ↥(H z), qH D r = spinR0 → ∀ v : QuotientV.V z, conjV h r v = v → v = 1 :=
    fun r hr => fixed_point_free_of_fixedCount D h P hP (by rw [hr]; exact hrfix)
  obtain ⟨r₀, hr₀3, hr₀q, hr₀ρ⟩ := exists_order_three_commuting D hρ3 hρq
  set x' : ↥(H z) := ⟨x, hxH⟩ with hx'
  set k' : ↥(H z) := ⟨k, hkH⟩ with hk'
  set K : Subgroup ↥(H z) := Subgroup.centralizer ({ρ} : Set ↥(H z)) with hK
  have hmemK : ∀ y : ↥(H z), y * ρ = ρ * y → y ∈ K := fun y hy => by
    rw [hK]
    exact mem_centralizer_singleton_iff.mpr hy
  have hKmem : ∀ y ∈ K, y * ρ = ρ * y := fun y hy => by
    rw [hK] at hy
    exact mem_centralizer_singleton_iff.mp hy
  have hr₀K : r₀ ∈ K := hmemK r₀ hr₀ρ
  have hx'K : x' ∈ K := hmemK _ (Subtype.ext (mem_centralizer_singleton_iff.mp hxρ))
  have hk'K : k' ∈ K := hmemK _ (Subtype.ext (mem_centralizer_singleton_iff.mp hkρ))
  have hKJ : ¬ 3 ∣ Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_three_card_J_subgroupOf (z := z))
      (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨s, hsK, hsq, hsr₀⟩ := exists_lift_centralizer_of_le D (K := K) (r := r₀) hr₀3
    (fun y hy => K.mul_mem (K.mul_mem hr₀K hy) (K.inv_mem hr₀K)) hKJ hk'K
    (by rw [hkq, hr₀q]; exact hrt.symm)
  have hsqt : qH D s = tA := hsq.trans hkq
  have hg'K : x' * r₀⁻¹ * x'⁻¹ ∈ K := K.mul_mem (K.mul_mem hx'K (K.inv_mem hr₀K)) (K.inv_mem hx'K)
  have hg'3 : orderOf (x' * r₀⁻¹ * x'⁻¹) = 3 := by
    have h1 : orderOf (x' * r₀⁻¹ * x'⁻¹) = orderOf r₀⁻¹ :=
      (SemiconjBy.orderOf_eq x' (show x' * r₀⁻¹ = (x' * r₀⁻¹ * x'⁻¹) * x' by group)).symm
    rw [h1, orderOf_inv, hr₀3]
  have hg'q : qH D (x' * r₀⁻¹ * x'⁻¹) = qH D r₀ := by
    rw [map_mul, map_mul, map_inv, map_inv, hxq, hr₀q]
    exact xabX_conj_spinR0_inv
  obtain ⟨m, hmK, hmq, hmeq⟩ :=
    exists_conj_of_orderOf_three_of_qH_eq D K hr₀K hg'K hr₀3 hg'3 hg'q.symm
  have hmJ : (m : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D m).mpr hmq)
  have hs2r : (x' * s * x'⁻¹) * (m * r₀ * m⁻¹) = (m * r₀ * m⁻¹) * (x' * s * x'⁻¹) := by
    rw [← hmeq]
    have h1 : s * r₀⁻¹ = r₀⁻¹ * s := (show Commute s r₀ from hsr₀).inv_right.eq
    calc x' * s * x'⁻¹ * (x' * r₀⁻¹ * x'⁻¹) = x' * (s * r₀⁻¹) * x'⁻¹ := by group
      _ = x' * (r₀⁻¹ * s) * x'⁻¹ := by rw [h1]
      _ = x' * r₀⁻¹ * x'⁻¹ * (x' * s * x'⁻¹) := by group
  have hs3r : (m * s * m⁻¹) * (m * r₀ * m⁻¹) = (m * r₀ * m⁻¹) * (m * s * m⁻¹) := by
    calc m * s * m⁻¹ * (m * r₀ * m⁻¹) = m * (s * r₀) * m⁻¹ := by group
      _ = m * (r₀ * s) * m⁻¹ := by rw [hsr₀]
      _ = m * r₀ * m⁻¹ * (m * s * m⁻¹) := by group
  have e1 : qH D (x' * s * x'⁻¹) = tA := by
    rw [map_mul, map_mul, map_inv, hxq, hsqt]
    exact xabX_conj_tA
  have e2 : qH D (m * s * m⁻¹) = tA := by
    rw [map_mul, map_mul, map_inv, hmq, hsqt]
    simp
  set c' : ↥(H z) := (x' * s * x'⁻¹) * (m * s * m⁻¹)⁻¹ with hc'
  have hqc' : qH D c' = 1 := by
    rw [hc', map_mul, map_inv, e1, e2, mul_inv_cancel]
  have hc'J : (c' : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D c').mpr hqc')
  set r₁ : ↥(H z) := m * r₀ * m⁻¹ with hr₁
  have hr₁q : qH D r₁ = spinR0 := by
    rw [hr₁, map_mul, map_mul, map_inv, hmq, hr₀q]
    simp
  have hc'r : c' * r₁ = r₁ * c' :=
    ((show Commute (x' * s * x'⁻¹) r₁ from hs2r).mul_left
      (show Commute (m * s * m⁻¹) r₁ from hs3r).inv_left).eq
  have hc'Z : (c' : G) ∈ centerIn (J z) := by
    refine mem_centerIn_of_centralizes h (r := r₁) (hrv r₁ hr₁q) hc'J ?_
    have h1 : (c' : G) * (r₁ : G) = (r₁ : G) * c' := congrArg Subtype.val hc'r
    calc (r₁ : G) * (c' : G) * (r₁ : G)⁻¹ = (c' : G) * (r₁ : G) * (r₁ : G)⁻¹ := by rw [h1]
      _ = c' := by group
  set jj : ↥(H z) := k' * s⁻¹ with hjj
  have hqjj : qH D jj = 1 := by rw [hjj, map_mul, map_inv, hsq, mul_inv_cancel]
  have hjjJ : (jj : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D jj).mpr hqjj)
  have hjjs : jj * s = k' := by rw [hjj]; group
  have hjjK : jj ∈ K := K.mul_mem hk'K (K.inv_mem hsK)
  have hrelH : jj * s = (x' * jj * x'⁻¹) * c' * (m * s * m⁻¹) := by
    have hxk' : x' * k' = k' * x' := Subtype.ext hkx.symm
    calc jj * s = k' := hjjs
      _ = x' * k' * x'⁻¹ := by rw [hxk']; group
      _ = x' * (jj * s) * x'⁻¹ := by rw [hjjs]
      _ = (x' * jj * x'⁻¹) * (x' * s * x'⁻¹) := by group
      _ = (x' * jj * x'⁻¹) * ((x' * s * x'⁻¹) * (m * s * m⁻¹)⁻¹) * (m * s * m⁻¹) := by group
      _ = (x' * jj * x'⁻¹) * c' * (m * s * m⁻¹) := rfl
  have hrelG : (jj : G) * (s : G) = ((x' : G) * (jj : G) * (x' : G)⁻¹) * (c' : G) *
      ((m : G) * (s : G) * (m : G)⁻¹) := congrArg Subtype.val hrelH
  have hπ := pi_relation h x' s hjjJ hmJ hc'Z hrelG
  obtain ⟨wj, hwj⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨(jj : G), hjjJ⟩)
  obtain ⟨wm, hwm⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨(m : G), hmJ⟩)
  obtain ⟨wa, hwa⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨a, haJ⟩)
  have hρfix : ∀ (b : G) (hb : b ∈ J z) (w : V), spinVecToV h P w = QuotientV.pi z ⟨b, hb⟩ →
      (ρ : G) * b = b * (ρ : G) → SpinFixes xabRho w := by
    intro b hb w hw hρb
    have h1 := conjV_pi_eq_of_commute h hb hρb
    rw [← hw] at h1
    have h2 := (conjV_fixed_iff_spinFixes D h P hP ρ w).mp h1
    rwa [hρq] at h2
  have hjjρ : (ρ : G) * (jj : G) = (jj : G) * (ρ : G) :=
    congrArg Subtype.val (hKmem jj hjjK).symm
  have hmρ : (ρ : G) * (m : G) = (m : G) * (ρ : G) := congrArg Subtype.val (hKmem m hmK).symm
  have haρ' : (ρ : G) * a = a * (ρ : G) := (mem_centralizer_singleton_iff.mp haρ).symm
  have hwjρ := hρfix _ hjjJ wj hwj hjjρ
  have hwmρ := hρfix _ hmJ wm hwm hmρ
  have hwaρ := hρfix a haJ wa hwa haρ'
  have hwax : SpinFixes xabX wa := by
    have h1 := conjV_pi_eq_of_commute h (x := x') haJ hax.symm
    rw [← hwa] at h1
    have h2 := (conjV_fixed_iff_spinFixes D h P hP x' wa).mp h1
    rwa [hxq] at h2
  have haa : a * a = 1 := mul_self_eq_one_of_commute h hZ hxH hxx hdim haJ hax
  have hwaq : q wa = 0 := q_eq_zero_of_mul_self_eq_one D h P hP haJ haa hwa
  have hwat : SpinFixes tA wa := xab_fixes_t wa hwaρ hwax hwaq
  have hrelV : wj + ((rhoA xabX : GL8) : Mat8) *ᵥ wj = wm + ((rhoA tA : GL8) : Mat8) *ᵥ wm := by
    rw [← hwj, ← hwm, conjV_spinVecToV D h P hP x' wj, conjV_spinVecToV D h P hP s wm,
      ← spinVecToV_add, ← spinVecToV_add] at hπ
    have h1 := spinVecToV_injective h P hπ
    rw [hxq, hsqt] at h1
    have hdbl : ∀ v : V, v + v = 0 := fun v => funext fun i => by
      have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
      exact h2 (v i)
    calc wj + ((rhoA xabX : GL8) : Mat8) *ᵥ wj
        = (((rhoA xabX : GL8) : Mat8) *ᵥ wj + wm + ((rhoA tA : GL8) : Mat8) *ᵥ wm) +
          ((rhoA xabX : GL8) : Mat8) *ᵥ wj := by
          rw [← h1]
      _ = (wm + ((rhoA tA : GL8) : Mat8) *ᵥ wm) +
          (((rhoA xabX : GL8) : Mat8) *ᵥ wj + ((rhoA xabX : GL8) : Mat8) *ᵥ wj) := by abel
      _ = wm + ((rhoA tA : GL8) : Mat8) *ᵥ wm := by rw [hdbl, add_zero]
  have hb : b wj wa = 0 := xab_pair wm wj wa hwmρ hwjρ hwaρ hwax hwaq hrelV
  have hja : (jj : G) * a = a * (jj : G) := commute_of_b_eq_zero D h P hP hjjJ haJ hwj hwa hb
  have hssJ : (s : G) * (s : G) ∈ J z := by
    have h1 : s * s ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).2 (by rw [map_mul, hsqt]; exact tA_mul_self)
    exact Subgroup.mem_subgroupOf.mp h1
  have hfixs : conjV h s (QuotientV.pi z ⟨a, haJ⟩) = QuotientV.pi z ⟨a, haJ⟩ := by
    rw [← hwa]
    exact (conjV_fixed_iff_spinFixes D h P hP s wa).mpr (by rw [hsqt]; exact hwat)
  have hsa : (s : G) * a * (s : G)⁻¹ = a :=
    conj_eq_of_fixed h hZ hr₀3 hsr₀ (hrv r₀ hr₀q) hssJ haJ hfixs
  have hsa' : (s : G) * a = a * (s : G) := by
    calc (s : G) * a = ((s : G) * a * (s : G)⁻¹) * (s : G) := by group
      _ = a * (s : G) := by rw [hsa]
  have hkjs : k = (jj : G) * (s : G) := congrArg Subtype.val hjjs.symm
  calc k * a = (jj : G) * (s : G) * a := by rw [← hkjs]
    _ = (jj : G) * ((s : G) * a) := by group
    _ = (jj : G) * (a * (s : G)) := by rw [hsa']
    _ = ((jj : G) * a) * (s : G) := by group
    _ = (a * (jj : G)) * (s : G) := by rw [hja]
    _ = a * ((jj : G) * (s : G)) := by group
    _ = a * k := by rw [← hkjs]

theorem xab_std (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxq : qH D ⟨x, hxH⟩ = xabX) {X : Subgroup G}
    (hXle : X ≤ centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))
    (hxX : x ∈ X)
    (hXE : ∀ (g : G) (hg : g ∈ H z), g ∈ X → qH D ⟨g, hg⟩ = 1 ∨ qH D ⟨g, hg⟩ = tA ∨
      qH D ⟨g, hg⟩ = uA * vA ∨ qH D ⟨g, hg⟩ = xabX) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  have hdim := xab_fixDimV D h P hP hxH hxq
  have hXρ : ∀ g ∈ X, g ∈ centralizer ({(ρ : G)} : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXle hg)).1).1
  have hXH : ∀ g ∈ X, g ∈ H z := fun g hg =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXle hg)).1).2
  have hXx : ∀ g ∈ X, g * x = x * g := fun g hg =>
    mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hXle hg)).2
  have hAA : ∀ a ∈ X ⊓ J z, ∀ a' ∈ X ⊓ J z, a * a' = a' * a := fun a ha a' ha' =>
    commute_of_commute_of_fixDimV_eq_four h hZ hxH hxx hdim (Subgroup.mem_inf.mp ha).2
      (Subgroup.mem_inf.mp ha').2 (hXx a (Subgroup.mem_inf.mp ha).1)
      (hXx a' (Subgroup.mem_inf.mp ha').1)
  have hxA : ∀ a ∈ X ⊓ J z, x * a = a * x := fun a ha =>
    (hXx a (Subgroup.mem_inf.mp ha).1).symm
  have hxcl : x ∈ Subgroup.closure ({x, (1 : G)} : Set G) := Subgroup.subset_closure (by simp)
  by_cases hex : ∃ k ∈ X, ∃ hk : k ∈ H z, qH D ⟨k, hk⟩ = tA
  · obtain ⟨k, hkX, hkH, hkq⟩ := hex
    have hxcl : x ∈ Subgroup.closure ({x, k} : Set G) := Subgroup.subset_closure (by simp)
    have hkcl : k ∈ Subgroup.closure ({x, k} : Set G) := Subgroup.subset_closure (by simp)
    refine commutative_of_closure_cover hxX hkX (hXx k hkX).symm hAA hxA ?_ ?_
    · intro a ha
      obtain ⟨haX, haJ⟩ := Subgroup.mem_inf.mp ha
      exact xab_crux D h hZ P hP hρ3 hρq hxH hxρ hxx hxq hkH (hXρ k hkX) (hXx k hkX) hkq haJ
        (hXρ a haX) (hXx a haX)
    · intro g hgX
      have hgH := hXH g hgX
      rcases hXE g hgH hgX with h1 | h1 | h1 | h1
      · refine ⟨1, one_mem _, ?_⟩
        rw [inv_one, one_mul]
        exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D ⟨g, hgH⟩).2 h1)
      · exact ⟨k, hkcl, inv_mul_mem_J_of_qH_eq D hkH hgH (hkq.trans h1.symm)⟩
      · have hkxH : k * x ∈ H z := (H z).mul_mem hkH hxH
        refine ⟨k * x, Subgroup.mul_mem _ hkcl hxcl, inv_mul_mem_J_of_qH_eq D hkxH hgH ?_⟩
        show qH D (⟨k, hkH⟩ * ⟨x, hxH⟩) = _
        rw [map_mul, hkq, hxq, tA_mul_xabX, h1]
      · exact ⟨x, hxcl, inv_mul_mem_J_of_qH_eq D hxH hgH (hxq.trans h1.symm)⟩
  · refine commutative_of_closure_cover (k := 1) hxX X.one_mem (by simp) hAA hxA
      (fun a ha => by simp) ?_
    intro g hgX
    have hgH := hXH g hgX
    rcases hXE g hgH hgX with h1 | h1 | h1 | h1
    · refine ⟨1, one_mem _, ?_⟩
      rw [inv_one, one_mul]
      exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D ⟨g, hgH⟩).2 h1)
    · exact absurd ⟨g, hgX, hgH, h1⟩ hex
    · exfalso
      apply hex
      refine ⟨g * x, X.mul_mem hgX hxX, (H z).mul_mem hgH hxH, ?_⟩
      show qH D (⟨g, hgH⟩ * ⟨x, hxH⟩) = _
      rw [map_mul, h1, hxq, uAvA_mul_xabX]
    · exact ⟨x, hxcl, inv_mul_mem_J_of_qH_eq D hxH hgH (hxq.trans h1.symm)⟩

end Spin

end CFSG.RankThree.GF2n.Parrott

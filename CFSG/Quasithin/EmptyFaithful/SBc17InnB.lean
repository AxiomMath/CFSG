module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
public import CFSG.Quasithin.EmptyFaithful.SBc17Inn0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace SBc17

section PermFacts

variable {n : ℕ}

theorem cycleType_eq_five (hn : n ≤ 8) {c : Equiv.Perm (Fin n)} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) :
    c.cycleType = {5} := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hall : ∀ m ∈ c.cycleType, m = 5 := by
    intro m hm
    have h1 : m ∣ 5 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hm
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h <;> omega
  have hsum : c.cycleType.sum ≤ 8 := by
    rw [Equiv.Perm.sum_cycleType]
    calc c.support.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
      _ ≤ 8 := hn
  have hne : c.cycleType ≠ 0 := fun h => hc1 (Equiv.Perm.cycleType_eq_zero.mp h)
  have hrep : c.cycleType = Multiset.replicate (Multiset.card c.cycleType) 5 :=
    Multiset.eq_replicate_card.mpr hall
  have hs : c.cycleType.sum = 5 * Multiset.card c.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : 0 < Multiset.card c.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card c.cycleType) with h | h
    · exact absurd (Multiset.card_eq_zero.mp h) hne
    · exact h
  have hcard : Multiset.card c.cycleType = 1 := by omega
  calc c.cycleType = Multiset.replicate (Multiset.card c.cycleType) 5 := hrep
    _ = Multiset.replicate 1 5 := by rw [hcard]
    _ = {5} := rfl

theorem exists_conj_of_five (hn : n ≤ 8) {c₀ c : Equiv.Perm (Fin n)} (hc₀5 : c₀ ^ 5 = 1)
    (hc₀1 : c₀ ≠ 1) (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) :
    ∃ π : Equiv.Perm (Fin n), π * c₀ * π⁻¹ = c :=
  isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr
    ((cycleType_eq_five hn hc₀5 hc₀1).trans (cycleType_eq_five hn hc5 hc1).symm))

theorem fix_of_commute_swap {c : Equiv.Perm (Fin n)} {x y : Fin n} (hxy : x ≠ y)
    (hcomm : c * Equiv.swap x y = Equiv.swap x y * c) (hc5 : c ^ 5 = 1) : c x = x ∧ c y = y := by
  have hsw : ∀ z, Equiv.swap x y z ≠ z ↔ z = x ∨ z = y := by
    intro z
    constructor
    · intro h
      by_contra hz
      push Not at hz
      exact h (Equiv.swap_apply_of_ne_of_ne hz.1 hz.2)
    · rintro (rfl | rfl)
      · rw [Equiv.swap_apply_left]
        exact hxy.symm
      · rw [Equiv.swap_apply_right]
        exact hxy
  have hc : ∀ z, Equiv.swap x y (c z) = c (Equiv.swap x y z) := fun z => by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f z) hcomm
    simpa using this.symm
  have hinv : ∀ z, c z ∈ ({x, y} : Finset (Fin n)) ↔ z ∈ ({x, y} : Finset (Fin n)) := by
    intro z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [← hsw, ← hsw, hc]
    exact c.injective.ne_iff
  have hfix := perm_fix_of_invariant_small c hc5 {x, y} hinv (by
    have := Finset.card_le_two (a := x) (b := y)
    omega)
  exact ⟨hfix x (by simp), hfix y (by simp)⟩

@[expose] def AltFive (n : ℕ) : Prop :=
  ∃ c m : Equiv.Perm (Fin n), c ^ 5 = 1 ∧ c ≠ 1 ∧ Equiv.Perm.sign m = 1 ∧
    (∀ z, c z = z → m z = z) ∧ ⁅c, m * c * m⁻¹⁆ ^ 5 = 1 ∧ ⁅c, m * c * m⁻¹⁆ ≠ 1

theorem altFive_seven : AltFive 7 :=
  ⟨List.formPerm [0, 1, 2, 3, 4], List.formPerm [0, 1, 2], by decide +kernel⟩

theorem altFive_eight : AltFive 8 :=
  ⟨List.formPerm [0, 1, 2, 3, 4], List.formPerm [0, 1, 2], by decide +kernel⟩

theorem altFive_of_le (h7 : 7 ≤ n) (h8 : n ≤ 8) : AltFive n := by
  obtain rfl | rfl : n = 7 ∨ n = 8 := by omega
  · exact altFive_seven
  · exact altFive_eight

theorem exists_m_of_altFive (hn : n ≤ 8) (hfin : AltFive n) {c : Equiv.Perm (Fin n)}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) {x y : Fin n} (hxy : x ≠ y)
    (hcomm : c * Equiv.swap x y = Equiv.swap x y * c) :
    ∃ m : Equiv.Perm (Fin n), Equiv.Perm.sign m = 1 ∧
      m * Equiv.swap x y = Equiv.swap x y * m ∧
      ⁅c, m * c * m⁻¹⁆ ^ 5 = 1 ∧ ⁅c, m * c * m⁻¹⁆ ≠ 1 := by
  obtain ⟨c₀, m₀, hc₀5, hc₀1, hm₀, hsupp, hε5, hε1⟩ := hfin
  obtain ⟨π, hπ⟩ := exists_conj_of_five hn hc₀5 hc₀1 hc5 hc1
  obtain ⟨hcx, hcy⟩ := fix_of_commute_swap hxy hcomm hc5
  have hfix : ∀ z, c z = z → (π * m₀ * π⁻¹) z = z := by
    intro z hz
    have hz' : π (c₀ (π⁻¹ z)) = z := by
      rw [← hπ] at hz
      simpa only [Equiv.Perm.mul_apply] using hz
    have hπz : π (π⁻¹ z) = z := π.apply_symm_apply z
    have h1 : c₀ (π⁻¹ z) = π⁻¹ z := π.injective (by rw [hz', hπz])
    have h2 := hsupp _ h1
    simp only [Equiv.Perm.mul_apply, h2, hπz]
  refine ⟨π * m₀ * π⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, hm₀, Equiv.Perm.sign_inv, mul_one]
    exact Int.units_mul_self _
  · rw [Equiv.mul_swap_eq_swap_mul, hfix x hcx, hfix y hcy]
  · have e : ⁅c, π * m₀ * π⁻¹ * c * (π * m₀ * π⁻¹)⁻¹⁆ = π * ⁅c₀, m₀ * c₀ * m₀⁻¹⁆ * π⁻¹ := by
      rw [← hπ]
      simp only [commutatorElement_def]
      group
    rw [e, conj_pow, hε5]
    group
  · have e : ⁅c, π * m₀ * π⁻¹ * c * (π * m₀ * π⁻¹)⁻¹⁆ = π * ⁅c₀, m₀ * c₀ * m₀⁻¹⁆ * π⁻¹ := by
      rw [← hπ]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact fun h => hε1 (conj_eq_one_iff.mp h)

end PermFacts

section Block

variable {G : Type} [Group G]

theorem alt_data_of_five {J R M V : Subgroup G} (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) [Finite G] {n : ℕ}
    {α : ↥J →* alternatingGroup (Fin n)} (hker : α.ker = CFSG.pCore 2 ↥J) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin n)}
    (hrel : ∀ (k : G) (hk : k ∈ J) (hk' : t * k * t⁻¹ ∈ J),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ J) V = autOn J V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) :
    ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ^ 5 = 1 ∧
      ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ≠ 1 ∧
      ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ =
        σ * ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  have haJ : a ∈ J := haM.2
  have haV : a ∈ Subgroup.normalizer (V : Set G) := hJV haJ
  have hmem : conjAct V ⟨a, haV⟩ ∈ autOn (M ⊓ J) V := mem_autOn_iff.mpr ⟨a, haV, haM, rfl⟩
  rw [hMK] at hmem
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ = conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ :=
    Subgroup.mem_centralizer_iff.mp hmem.2 _ (mem_autOn_iff.mpr ⟨t, htV, htR, rfl⟩)
  have hta : t * a⁻¹ * t⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hR htR) a⁻¹).mp (J.inv_mem haJ)
  have hw : a * (t * a⁻¹ * t⁻¹) ∈ J := J.mul_mem haJ hta
  have hw1 : actOn hJV ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := by
    apply Subtype.ext
    show conjAct V ⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ = 1
    have e : (⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨a, haV⟩ * (⟨t, htV⟩ * ⟨a, haV⟩⁻¹ * ⟨t, htV⟩⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h2 : conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ = conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ :=
      hcomm.symm
    calc conjAct V ⟨a, haV⟩ * (conjAct V ⟨t, htV⟩ * (conjAct V ⟨a, haV⟩)⁻¹ *
          (conjAct V ⟨t, htV⟩)⁻¹) = (conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩) *
            (conjAct V ⟨a, haV⟩)⁻¹ * (conjAct V ⟨t, htV⟩)⁻¹ := by group
      _ = (conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩) * (conjAct V ⟨a, haV⟩)⁻¹ *
            (conjAct V ⟨t, htV⟩)⁻¹ := by rw [h2]
      _ = 1 := by group
  have hwC := (actOn_eq_one_iff hJV _).mp hw1
  have hwO : a * (t * a⁻¹ * t⁻¹) ∈ pCoreOf 2 J := hD ⟨hw, hwC⟩
  have hα1 : α ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := (map_eq_one_iff_mem_pCoreOf hker _).mpr hwO
  have hsplit : (⟨a * (t * a⁻¹ * t⁻¹), hw⟩ : ↥J) = ⟨a, haJ⟩ * ⟨t * a⁻¹ * t⁻¹, hta⟩ := rfl
  rw [hsplit, map_mul] at hα1
  have hrel' := hrel a⁻¹ (J.inv_mem haJ) hta
  have hinvα : (α ⟨a⁻¹, J.inv_mem haJ⟩ : alternatingGroup (Fin n)) = (α ⟨a, haJ⟩)⁻¹ := by
    have : (⟨a⁻¹, J.inv_mem haJ⟩ : ↥J) = (⟨a, haJ⟩ : ↥J)⁻¹ := rfl
    rw [this, map_inv]
  rw [hinvα] at hrel'
  set c : Equiv.Perm (Fin n) := (α ⟨a, haJ⟩ : Equiv.Perm (Fin n)) with hc
  have h1 : c * (σ * c⁻¹ * σ⁻¹) = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n))) hα1
    simpa [hc, hrel'] using this
  have hcomm' : c * σ = σ * c := by
    have : c * σ * c⁻¹ * σ⁻¹ = 1 := by
      calc c * σ * c⁻¹ * σ⁻¹ = c * (σ * c⁻¹ * σ⁻¹) := by group
        _ = 1 := h1
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hc5 : c ^ 5 = 1 := by
    have h5 : (⟨a, haJ⟩ : ↥J) ^ 5 = 1 := Subtype.ext (by simp [← ha5, pow_orderOf_eq_one])
    have := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n)))
      (show (α ⟨a, haJ⟩) ^ 5 = 1 by rw [← map_pow, h5, map_one])
    simpa [hc] using this
  refine ⟨hc5, fun hc1 => ?_, hcomm'⟩
  have hα2 : α ⟨a, haJ⟩ = 1 := Subtype.ext (by simpa [hc] using hc1)
  exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) ha5
    ((map_eq_one_iff_mem_pCoreOf hker ⟨a, haJ⟩).mp hα2)

theorem exists_lift_mem_M {J R M V : Subgroup G} (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J)
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G)) {n : ℕ}
    {α : ↥J →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥J) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hRt : autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩)) {σ : Equiv.Perm (Fin n)}
    (hrel : ∀ (k : G) (hk : k ∈ J) (hk' : t * k * t⁻¹ ∈ J),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ J) V = autOn J V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {m₀ : alternatingGroup (Fin n)} (hm₀ : (m₀ : Equiv.Perm (Fin n)) * σ = σ * m₀) :
    ∃ (m : G) (hm : m ∈ M ⊓ J), α ⟨m, hm.2⟩ = m₀ := by
  obtain ⟨m', hm'⟩ := hα m₀
  have hm'J : (m' : G) ∈ J := m'.2
  have hm'V : (m' : G) ∈ Subgroup.normalizer (V : Set G) := hJV hm'J
  have hta : t * (m' : G)⁻¹ * t⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hR htR) _).mp (J.inv_mem hm'J)
  have hw : (m' : G) * (t * (m' : G)⁻¹ * t⁻¹) ∈ J := J.mul_mem hm'J hta
  have hα1 : α ⟨(m' : G) * (t * (m' : G)⁻¹ * t⁻¹), hw⟩ = 1 := by
    have hsplit : (⟨(m' : G) * (t * (m' : G)⁻¹ * t⁻¹), hw⟩ : ↥J) =
        m' * ⟨t * (m' : G)⁻¹ * t⁻¹, hta⟩ := rfl
    rw [hsplit, map_mul, hm']
    have hrel' := hrel (m' : G)⁻¹ (J.inv_mem hm'J) hta
    have hinvα : (α ⟨(m' : G)⁻¹, J.inv_mem hm'J⟩ : alternatingGroup (Fin n)) = (α m')⁻¹ := by
      have : (⟨(m' : G)⁻¹, J.inv_mem hm'J⟩ : ↥J) = m'⁻¹ := rfl
      rw [this, map_inv]
    rw [hinvα, hm'] at hrel'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hrel', InvMemClass.coe_inv, Subgroup.coe_one]
    calc (m₀ : Equiv.Perm (Fin n)) * (σ * (m₀ : Equiv.Perm (Fin n))⁻¹ * σ⁻¹) =
        ((m₀ : Equiv.Perm (Fin n)) * σ) * (m₀ : Equiv.Perm (Fin n))⁻¹ * σ⁻¹ := by group
      _ = (σ * (m₀ : Equiv.Perm (Fin n))) * (m₀ : Equiv.Perm (Fin n))⁻¹ * σ⁻¹ := by rw [hm₀]
      _ = 1 := by group
  have hwO : (m' : G) * (t * (m' : G)⁻¹ * t⁻¹) ∈ pCoreOf 2 J :=
    (map_eq_one_iff_mem_pCoreOf hker _).mp hα1
  have hwC := hOC hwO
  have hw1 : actOn hJV ⟨(m' : G) * (t * (m' : G)⁻¹ * t⁻¹), hw⟩ = 1 :=
    (actOn_eq_one_iff hJV _).mpr hwC
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨m', hm'V⟩ =
      conjAct V ⟨m', hm'V⟩ * conjAct V ⟨t, htV⟩ := by
    have h0 : conjAct V ⟨(m' : G) * (t * (m' : G)⁻¹ * t⁻¹), hJV hw⟩ = 1 := congrArg Subtype.val hw1
    have e : (⟨(m' : G) * (t * (m' : G)⁻¹ * t⁻¹), hJV hw⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨m', hm'V⟩ * (⟨t, htV⟩ * ⟨m', hm'V⟩⁻¹ * ⟨t, htV⟩⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    have h3 : conjAct V ⟨m', hm'V⟩ * conjAct V ⟨t, htV⟩ * (conjAct V ⟨m', hm'V⟩)⁻¹ *
        (conjAct V ⟨t, htV⟩)⁻¹ = 1 := by
      calc _ = conjAct V ⟨m', hm'V⟩ * (conjAct V ⟨t, htV⟩ * (conjAct V ⟨m', hm'V⟩)⁻¹ *
            (conjAct V ⟨t, htV⟩)⁻¹) := by group
        _ = 1 := h0
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hmemC : conjAct V ⟨m', hm'V⟩ ∈ autOn (M ⊓ J) V := by
    rw [hMK]
    refine ⟨mem_autOn_iff.mpr ⟨m', hm'V, hm'J, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [hRt] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm k).eq
  obtain ⟨m, hmV, hmM, hmx⟩ := mem_autOn_iff.mp hmemC
  have hmJ : m ∈ J := hmM.2
  refine ⟨m, hmM, ?_⟩
  have hker1 : actOn hJV (⟨m, hmJ⟩⁻¹ * m') = 1 := by
    apply Subtype.ext
    show conjAct V ⟨(m : G)⁻¹ * (m' : G), hJV (J.mul_mem (J.inv_mem hmJ) hm'J)⟩ = 1
    have e : (⟨(m : G)⁻¹ * (m' : G), hJV (J.mul_mem (J.inv_mem hmJ) hm'J)⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨m, hmV⟩⁻¹ * ⟨m', hm'V⟩ := rfl
    rw [e, map_mul, map_inv, hmx]
    exact inv_mul_cancel _
  have hC := (actOn_eq_one_iff hJV _).mp hker1
  have hO : (m : G)⁻¹ * (m' : G) ∈ pCoreOf 2 J :=
    hD ⟨J.mul_mem (J.inv_mem hmJ) hm'J, hC⟩
  have hα2 : α (⟨m, hmJ⟩⁻¹ * m') = 1 := (map_eq_one_iff_mem_pCoreOf hker _).mpr hO
  rw [map_mul, map_inv, hm'] at hα2
  exact inv_mul_eq_one.mp hα2

theorem not_seventeen_dvd_card_alternating {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 8) :
    ¬ 17 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h2
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  interval_cases n <;> decide

theorem not_seventeen_dvd_card_of_alt [Finite G] {J : Subgroup G} {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 8)
    {α : ↥J →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥J) : ¬ 17 ∣ Nat.card ↥J := by
  intro h17
  have hp : Nat.Prime 17 := by norm_num
  rw [card_eq_quot_mul_pCore] at h17
  have e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(alternatingGroup (Fin n)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rcases hp.dvd_mul.mp h17 with h | h
  · rw [Nat.card_congr e.toEquiv] at h
    exact not_seventeen_dvd_card_alternating h2 hn h
  · obtain ⟨k, hk⟩ := (isPGroup_pCore J).exists_card_eq
    rw [hk] at h
    have : 17 ∣ 2 := hp.dvd_of_dvd_pow h
    omega

theorem false_of_alt_big [Finite G] {J R M V K₁ : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (J : Set G)) (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J)
    (hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G)) {n : ℕ} (hn7 : 7 ≤ n) (hn8 : n ≤ 8)
    {α : ↥J →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥J) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hRt : autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩)) {σ : Equiv.Perm (Fin n)}
    (hσ : σ.IsSwap)
    (hrel : ∀ (k : G) (hk : k ∈ J) (hk' : t * k * t⁻¹ ∈ J),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ J) V = autOn J V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    (hK₁ : K₁ ≤ M ⊓ J) (hK₁N : M ⊓ J ≤ Subgroup.normalizer (K₁ : Set G))
    (hK₁d : IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ 17 ∣ Nat.card ↥K₁) {a : G} (haK : a ∈ K₁)
    (ha5 : orderOf a = 5) : False := by
  have haM : a ∈ M ⊓ J := hK₁ haK
  have haJ : a ∈ J := haM.2
  rcases hK₁d with h2 | h17
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, y, hxy, rfl⟩ := hσ
    obtain ⟨hc5, hc1, hcσ⟩ := alt_data_of_five hR hJV hD hker htR htV hrel hMK haM ha5
    obtain ⟨m, hmsign, hmσ, hε5, hε1⟩ :=
      exists_m_of_altFive hn8 (altFive_of_le hn7 hn8) hc5 hc1 hxy hcσ
    obtain ⟨m', hm'M, hm'α⟩ := exists_lift_mem_M hR hJV hD hOC hα hker htR htV hRt hrel hMK
      (m₀ := ⟨m, Equiv.Perm.mem_alternatingGroup.mpr hmsign⟩) hmσ
    have hma : m' * a * m'⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp (hK₁N hm'M) a).mp haK
    have hg : ⁅a, m' * a * m'⁻¹⁆ ∈ ⁅K₁, K₁⁆ := Subgroup.commutator_mem_commutator haK hma
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp h2 ⟨_, hg⟩
    rw [Subgroup.orderOf_mk] at hk
    set a' : ↥J := ⟨a, haJ⟩ with ha'
    set m'' : ↥J := ⟨m', hm'M.2⟩ with hm''
    have hgo : orderOf ⁅a', m'' * a' * m''⁻¹⁆ = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe]
      rfl
    have hα_g : ((α ⁅a', m'' * a' * m''⁻¹⁆ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        ⁅((α a' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)),
          m * ((α a' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * m⁻¹⁆ := by
      rw [map_commutatorElement, map_mul, map_mul, map_inv, hm'α]
      rfl
    have hg5 : (α ⁅a', m'' * a' * m''⁻¹⁆) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hα_g]; exact hε5)
    have hd5 : orderOf (α ⁅a', m'' * a' * m''⁻¹⁆) ∣ 5 := orderOf_dvd_of_pow_eq_one hg5
    have hd2 : orderOf (α ⁅a', m'' * a' * m''⁻¹⁆) ∣ 2 ^ k :=
      hgo ▸ orderOf_map_dvd α _
    have hd1 : orderOf (α ⁅a', m'' * a' * m''⁻¹⁆) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp hd5 with h | h
      · exact h
      · rw [h] at hd2
        have := Nat.prime_five.dvd_of_dvd_pow hd2
        omega
    have hone : α ⁅a', m'' * a' * m''⁻¹⁆ = 1 := orderOf_eq_one_iff.mp hd1
    apply hε1
    rw [← hα_g, hone]
    rfl
  · exact not_seventeen_dvd_card_of_alt (by omega) hn8 hα hker
      (h17.trans (Subgroup.card_dvd_of_le (hK₁.trans inf_le_right)))

end Block

end SBc17

end CFSG.Quasithin

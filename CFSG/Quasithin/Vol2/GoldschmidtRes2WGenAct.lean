module

public import CFSG.Quasithin.Vol2.GoldschmidtRes2WPerm
public import CFSG.Quasithin.Background.E2PairMore

public section

namespace CFSG.Quasithin.Res2

namespace WGen

open CFSG.Quasithin B6

variable {G : Type*} [Group G]

theorem toPermHom_eq_one_of_mem_kerIn {X M : Subgroup G} {z : ↥X} (hz : (z : G) ∈ kerIn M X) :
    MulAction.toPermHom ↥X (↥X ⧸ M.subgroupOf X) z = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul,
      Equiv.Perm.coe_one, id, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := (kerIn M X).inv_mem hz
    have h2 := (mem_kerIn.1 this) (x⁻¹ : ↥X) (x⁻¹).2
    simpa [mul_assoc] using h2

theorem orbit_eq_ne_base {X M : Subgroup G} {g : G} (hg : g ∈ X) (hMX : M ≤ X) (hgM : g ∉ M)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) :
    MulAction.orbit ↥(M.subgroupOf X) ((⟨g, hg⟩ : ↥X) : ↥X ⧸ M.subgroupOf X) =
      {q | q ≠ ((1 : ↥X) : ↥X ⧸ M.subgroupOf X)} := by
  ext q
  rw [MulAction.mem_orbit_iff]
  show _ ↔ q ≠ _
  constructor
  · rintro ⟨m, rfl⟩ h
    have hm : (m : ↥X) • ((1 : ↥X) : ↥X ⧸ M.subgroupOf X) = ((1 : ↥X) : ↥X ⧸ M.subgroupOf X) :=
      by
      have := toPermHom_apply_one_of_mem (X := X) (M := M) (z := (m : ↥X))
        (Subgroup.mem_subgroupOf.1 m.2)
      simpa using this
    rw [Subgroup.smul_def, ← hm] at h
    have h2 := MulAction.injective ((m : ↥X)) h
    rw [QuotientGroup.eq] at h2
    apply hgM
    simpa [Subgroup.mem_subgroupOf] using h2
  · intro hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hxM : (x : G) ∉ M := by
        intro hx
        apply hq
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using M.inv_mem hx
      obtain ⟨m₁, hm₁, m₂, hm₂, hx⟩ := (hBru x x.2).resolve_left hxM
      refine ⟨⟨⟨m₁, hMX hm₁⟩, by simpa [Subgroup.mem_subgroupOf] using hm₁⟩, ?_⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, hx]
      have := M.inv_mem hm₂
      simpa [mul_assoc] using this

theorem stabilizer_eq_conjSub {X M : Subgroup G} {g : G} (hg : g ∈ X) :
    MulAction.stabilizer ↥X ((⟨g, hg⟩ : ↥X) : ↥X ⧸ M.subgroupOf X) =
      (conjSub g M).subgroupOf X := by
  ext x
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf (H := M), Subgroup.mem_subgroupOf (H := conjSub g M), mem_conjSub]
  have e : (((x * ⟨g, hg⟩)⁻¹ * ⟨g, hg⟩ : ↥X) : G) = (g⁻¹ * (x : G) * g)⁻¹ := by
    simp [mul_assoc]
  rw [e]
  exact ⟨fun h => by simpa using M.inv_mem h, fun h => M.inv_mem h⟩

theorem ncard_ne_base {Q : Type*} [Finite Q] {n : ℕ} (hQ : Nat.card Q = n + 1) (q₀ : Q) :
    ({q | q ≠ q₀} : Set Q).ncard = n := by
  have h := Set.ncard_sdiff_singleton_of_mem (s := (Set.univ : Set Q)) (Set.mem_univ q₀)
  rw [Set.ncard_univ, hQ, Nat.add_sub_cancel] at h
  rw [← h]
  congr 1
  ext q
  simp

theorem relIndex_conjSub_eq {X M : Subgroup G} {g : G} (hg : g ∈ X) (hMX : M ≤ X) (hgM : g ∉ M)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) (hidx : M.relIndex X = 5) :
    (conjSub g M).relIndex M = 4 := by
  have hQ : Nat.card (↥X ⧸ M.subgroupOf X) = 4 + 1 := hidx
  have : Finite (↥X ⧸ M.subgroupOf X) := Nat.finite_of_card_ne_zero (by omega)
  have h1 := MulAction.index_stabilizer ↥(M.subgroupOf X)
    ((⟨g, hg⟩ : ↥X) : ↥X ⧸ M.subgroupOf X)
  rw [orbit_eq_ne_base hg hMX hgM hBru, ← MulAction.stabilizer_subgroupOf,
    stabilizer_eq_conjSub hg, ncard_ne_base hQ] at h1
  rw [← h1]
  exact (Subgroup.relIndex_subgroupOf hMX).symm

theorem mem_kerIn_of_fixed [Finite G] {X M : Subgroup G} {g : G} (hg : g ∈ X) (hMX : M ≤ X)
    (hgM : g ∉ M) (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂)
    (hidx : M.relIndex X = 5) (hJM : (kerIn M X).relIndex M = 12) {v : G} (hvM : v ∈ M)
    (hv2 : v ^ 2 = 1) {q : ↥X ⧸ M.subgroupOf X} (hq : q ≠ ((1 : ↥X) : ↥X ⧸ M.subgroupOf X))
    (hfix : MulAction.toPermHom ↥X (↥X ⧸ M.subgroupOf X) ⟨v, hMX hvM⟩ q = q) :
    v ∈ kerIn M X := by
  have hq' : q ∈ MulAction.orbit ↥(M.subgroupOf X) ((⟨g, hg⟩ : ↥X) : ↥X ⧸ M.subgroupOf X) := by
    rw [orbit_eq_ne_base hg hMX hgM hBru]
    exact hq
  obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.1 hq'
  set q₁ : ↥X ⧸ M.subgroupOf X := ((⟨g, hg⟩ : ↥X) : ↥X ⧸ M.subgroupOf X) with hq₁
  set m₁ : G := (((m : ↥(M.subgroupOf X)) : ↥X) : G) with hm₁
  have hm₁M : m₁ ∈ M := Subgroup.mem_subgroupOf.1 m.2
  have hm₁X : m₁ ∈ X := hMX hm₁M
  set w : G := m₁⁻¹ * v * m₁ with hw
  have hwM : w ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm₁M) hvM) hm₁M
  have hwX : w ∈ X := hMX hwM
  have hw2 : w ^ 2 = 1 := by
    have : w ^ 2 = m₁⁻¹ * v ^ 2 * m₁ := by
      rw [hw, pow_two, pow_two]; group
    rw [this, hv2]; group
  have hwq : (⟨w, hwX⟩ : ↥X) • q₁ = q₁ := by
    have e : (⟨w, hwX⟩ : ↥X) = ((m : ↥(M.subgroupOf X)) : ↥X)⁻¹ * ⟨v, hMX hvM⟩ *
        ((m : ↥(M.subgroupOf X)) : ↥X) := by
      apply Subtype.ext
      simp [hw, hm₁]
    have hm' : ((m : ↥(M.subgroupOf X)) : ↥X) • q₁ = q := by
      rw [← hm]; rfl
    rw [e, mul_smul, mul_smul, hm']
    have : (⟨v, hMX hvM⟩ : ↥X) • q = q := hfix
    rw [this, ← hm']
    simp
  have hwS : w ∈ conjSub g M ⊓ M := by
    refine ⟨?_, hwM⟩
    have h1 : (⟨w, hwX⟩ : ↥X) ∈ MulAction.stabilizer ↥X q₁ := hwq
    rw [hq₁, stabilizer_eq_conjSub hg] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hJS : kerIn M X ≤ conjSub g M ⊓ M := by
    refine le_inf (fun j hj => ?_) kerIn_le
    rw [mem_conjSub]
    simpa using (mem_kerIn.1 hj) g⁻¹ (X.inv_mem hg)
  have hSM : conjSub g M ⊓ M ≤ M := inf_le_right
  have h3 : (kerIn M X).relIndex (conjSub g M ⊓ M) = 3 := by
    have h1 := Subgroup.relIndex_mul_relIndex (kerIn M X) (conjSub g M ⊓ M) M hJS hSM
    rw [Subgroup.inf_relIndex_right, relIndex_conjSub_eq hg hMX hgM hBru hidx, hJM] at h1
    omega
  have hT : Subgroup.zpowers w ≤ kerIn M X := by
    refine B6.le_of_isPGroup_of_odd_relIndex (H := conjSub g M ⊓ M)
      (Subgroup.zpowers_le.2 hwS) (E2.isPGroup_zpowers_of_pow (k := 1) (by simpa using hw2)) hJS
      ((inf_le_right.trans hMX).trans (le_normalizer_kerIn M X)) (by rw [h3]; decide)
  have hwJ : w ∈ kerIn M X := hT (Subgroup.mem_zpowers w)
  have h4 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M X hm₁X) w).mp hwJ
  have e : m₁ * w * m₁⁻¹ = v := by rw [hw]; group
  rwa [e] at h4

theorem exists_smul_eq_of_ne_base [Finite G] {X M V : Subgroup G} {g : G} (hg : g ∈ X)
    (hMX : M ≤ X) (hVM : V ≤ M) (hgM : g ∉ M)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) (hidx : M.relIndex X = 5)
    (hJM : (kerIn M X).relIndex M = 12) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVB : (kerIn M X ⊓ V).relIndex V = 4) {q q' : ↥X ⧸ M.subgroupOf X}
    (hq : q ≠ ((1 : ↥X) : ↥X ⧸ M.subgroupOf X)) (hq' : q' ≠ ((1 : ↥X) : ↥X ⧸ M.subgroupOf X)) :
    ∃ w : G, ∃ hw : w ∈ V, MulAction.toPermHom ↥X (↥X ⧸ M.subgroupOf X)
      ⟨w, hMX (hVM hw)⟩ q = q' := by
  have hVX : V ≤ X := hVM.trans hMX
  have hQ : Nat.card (↥X ⧸ M.subgroupOf X) = 4 + 1 := hidx
  have : Finite (↥X ⧸ M.subgroupOf X) := Nat.finite_of_card_ne_zero (by omega)
  set q₀ : ↥X ⧸ M.subgroupOf X := ((1 : ↥X) : ↥X ⧸ M.subgroupOf X) with hq₀
  have hst : MulAction.stabilizer ↥(V.subgroupOf X) q =
      ((kerIn M X ⊓ V).subgroupOf X).subgroupOf (V.subgroupOf X) := by
    rw [← MulAction.stabilizer_subgroupOf]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
      Subgroup.mem_subgroupOf]
    have hxV : ((x : ↥(V.subgroupOf X)) : ↥X).1 ∈ V := Subgroup.mem_subgroupOf.1 x.2
    constructor
    · intro hx
      exact ⟨mem_kerIn_of_fixed hg hMX hgM hBru hidx hJM (hVM hxV) (hV2 _ hxV) hq hx, hxV⟩
    · intro hx
      have := toPermHom_eq_one_of_mem_kerIn (M := M) (z := ((x : ↥(V.subgroupOf X)) : ↥X)) hx.1
      have h2 := Equiv.Perm.ext_iff.1 this q
      simpa using h2
  have h1 := MulAction.index_stabilizer ↥(V.subgroupOf X) q
  rw [hst] at h1
  have h2 : ((kerIn M X ⊓ V).subgroupOf X).relIndex (V.subgroupOf X) = 4 := by
    rw [Subgroup.relIndex_subgroupOf hVX, hVB]
  have h3 : (MulAction.orbit ↥(V.subgroupOf X) q).ncard = 4 := by
    rw [← h1]; exact h2
  have hsub : MulAction.orbit ↥(V.subgroupOf X) q ⊆ {q | q ≠ q₀} := by
    rintro _ ⟨x, rfl⟩ h
    apply hq
    have hxM : (((x : ↥(V.subgroupOf X)) : ↥X) : G) ∈ M := hVM (Subgroup.mem_subgroupOf.1 x.2)
    have hfix := toPermHom_apply_one_of_mem (X := X) (M := M) (z := (x : ↥X)) hxM
    have h' : (x : ↥X) • q = q₀ := h
    have h0 : (x : ↥X) • q₀ = q₀ := hfix
    exact MulAction.injective (x : ↥X) (h'.trans h0.symm)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h3, ncard_ne_base hQ]) (Set.toFinite _)
  have hq'mem : q' ∈ MulAction.orbit ↥(V.subgroupOf X) q := by rw [heq]; exact hq'
  obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 hq'mem
  refine ⟨((x : ↥X) : G), Subgroup.mem_subgroupOf.1 x.2, ?_⟩
  rw [← hx]
  rfl

theorem eq_of_fpf {Q : Type*} [Fintype Q] [DecidableEq Q]
    (hQ : Fintype.card Q = 5) {q₀ q : Q} (hq : q ≠ q₀) {σ τ : Equiv.Perm Q}
    (hσ0 : σ q₀ = q₀) (hτ0 : τ q₀ = q₀) (hσ2 : ∀ x, σ (σ x) = x) (hτ2 : ∀ x, τ (τ x) = x)
    (hσf : ∀ x, x ≠ q₀ → σ x ≠ x) (hτf : ∀ x, x ≠ q₀ → τ x ≠ x) (hστ : σ q = τ q) :
    σ = τ := by
  ext x
  by_cases hx0 : x = q₀
  · subst hx0; rw [hσ0, hτ0]
  by_cases hxq : x = q
  · subst hxq; exact hστ
  by_cases hxq' : x = σ q
  · subst hxq'
    rw [hσ2, hστ, hτ2]
  have key : ∀ ρ : Equiv.Perm Q, ρ q₀ = q₀ → (∀ y, ρ (ρ y) = y) → (∀ y, y ≠ q₀ → ρ y ≠ y) →
      ρ q = σ q → ρ x ∈ Finset.univ \ ({q₀, q, σ q, x} : Finset Q) := by
    intro ρ h0 h2 hf hρq
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, hf x hx0⟩
    · intro h
      apply hx0
      apply ρ.injective
      rw [h, h0]
    · intro h
      apply hxq'
      have := congrArg ρ h
      rw [h2] at this
      rw [this, hρq]
    · intro h
      apply hxq
      apply ρ.injective
      rw [h, hρq]
  have hcard : (Finset.univ \ ({q₀, q, σ q, x} : Finset Q)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hQ]
    have h1 : σ q ≠ q₀ := by
      intro h
      apply hq
      apply σ.injective
      rw [h, hσ0]
    have h2 : σ q ≠ q := hσf q hq
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h => hxq' h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h2.symm, fun h => hxq h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hq.symm, h1.symm, fun h => hx0 h.symm⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have e1 := key σ hσ0 hσ2 hσf rfl
  have e2 := key τ hτ0 hτ2 hτf hστ.symm
  rw [ha, Finset.mem_singleton] at e1 e2
  rw [e1, e2]

theorem exists_mem_of_conj [Finite G] {X M V : Subgroup G} {g : G} (hg : g ∈ X)
    (hMX : M ≤ X) (hVM : V ≤ M) (hgM : g ∉ M)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) (hidx : M.relIndex X = 5)
    (hJM : (kerIn M X).relIndex M = 12) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVB : (kerIn M X ⊓ V).relIndex V = 4) {m v : G} (hm : m ∈ M) (hv : v ∈ V) :
    ∃ w ∈ V, w⁻¹ * (m * v * m⁻¹) ∈ kerIn M X := by
  classical
  set Q := ↥X ⧸ M.subgroupOf X with hQdef
  have hQ : Nat.card Q = 5 := hidx
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype Q := Fintype.ofFinite _
  have hQ' : Fintype.card Q = 5 := by rw [← Nat.card_eq_fintype_card]; exact hQ
  set φ := MulAction.toPermHom ↥X Q with hφ
  set q₀ : Q := ((1 : ↥X) : Q) with hq₀
  have hmX : m ∈ X := hMX hm
  have hvM : v ∈ M := hVM hv
  by_cases hvJ : v ∈ kerIn M X
  · refine ⟨1, V.one_mem, ?_⟩
    rw [inv_one, one_mul]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M X hmX) v).mp hvJ
  have hq₁ : ((⟨g, hg⟩ : ↥X) : Q) ≠ q₀ := by
    intro h
    apply hgM
    rw [hq₀, QuotientGroup.eq] at h
    simpa [Subgroup.mem_subgroupOf] using M.inv_mem (Subgroup.mem_subgroupOf.1 h)
  set q₁ : Q := ((⟨g, hg⟩ : ↥X) : Q) with hq₁def
  set a : ↥X := ⟨m, hmX⟩ with ha
  set b : ↥X := ⟨v, hMX hvM⟩ with hb
  have hu : m * v * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hvM) (M.inv_mem hm)
  have huX : m * v * m⁻¹ ∈ X := hMX hu
  have hσ : φ ⟨m * v * m⁻¹, huX⟩ = φ a * φ b * (φ a)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have ha0 : φ a q₀ = q₀ := toPermHom_apply_one_of_mem (X := X) (M := M) hm
  have hσ0 : φ ⟨m * v * m⁻¹, huX⟩ q₀ = q₀ := toPermHom_apply_one_of_mem (X := X) (M := M) hu
  have hσ2 : ∀ x, φ ⟨m * v * m⁻¹, huX⟩ (φ ⟨m * v * m⁻¹, huX⟩ x) = x := by
    intro x
    have h2 : (⟨m * v * m⁻¹, huX⟩ : ↥X) * ⟨m * v * m⁻¹, huX⟩ = 1 := by
      apply Subtype.ext
      have := hV2 v hv
      show m * v * m⁻¹ * (m * v * m⁻¹) = 1
      calc m * v * m⁻¹ * (m * v * m⁻¹) = m * (v * v) * m⁻¹ := by group
        _ = 1 := by rw [← pow_two, this]; group
    have := Equiv.Perm.ext_iff.1 (by rw [← map_mul, h2, map_one] :
      φ ⟨m * v * m⁻¹, huX⟩ * φ ⟨m * v * m⁻¹, huX⟩ = 1) x
    simpa using this
  have hσf : ∀ x, x ≠ q₀ → φ ⟨m * v * m⁻¹, huX⟩ x ≠ x := by
    intro x hx hfix
    apply hvJ
    refine mem_kerIn_of_fixed hg hMX hgM hBru hidx hJM hvM (hV2 v hv)
      (q := (φ a)⁻¹ x) ?_ ?_
    · intro h
      apply hx
      have e : x = φ a ((φ a)⁻¹ x) := by simp
      rw [e, h, ha0]
    · rw [hσ] at hfix
      have h1 : φ a (φ b ((φ a)⁻¹ x)) = x := hfix
      have h2 := congrArg (⇑(φ a)⁻¹) h1
      have h3 : φ b ((φ a)⁻¹ x) = (φ a)⁻¹ x := by simpa using h2
      exact h3
  set σ : Equiv.Perm Q := φ ⟨m * v * m⁻¹, huX⟩ with hσdef
  have hσq₁ : σ q₁ ≠ q₀ := by
    intro h
    apply hq₁
    apply σ.injective
    rw [h, hσ0]
  obtain ⟨w, hwV, hw⟩ := exists_smul_eq_of_ne_base hg hMX hVM hgM hBru hidx hJM hV2 hVB hq₁ hσq₁
  have hwM : w ∈ M := hVM hwV
  set τ : Equiv.Perm Q := φ ⟨w, hMX hwM⟩ with hτdef
  have hτ0 : τ q₀ = q₀ := toPermHom_apply_one_of_mem (X := X) (M := M) hwM
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    have h2 : (⟨w, hMX hwM⟩ : ↥X) * ⟨w, hMX hwM⟩ = 1 := by
      apply Subtype.ext
      have := hV2 w hwV
      show w * w = 1
      rw [← pow_two, this]
    have := Equiv.Perm.ext_iff.1 (by rw [hτdef, ← map_mul, h2, map_one] : τ * τ = 1) x
    simpa using this
  have hστ : σ q₁ = τ q₁ := hw.symm
  have hτf : ∀ x, x ≠ q₀ → τ x ≠ x := by
    intro x hx hfix
    have hwJ : w ∈ kerIn M X :=
      mem_kerIn_of_fixed hg hMX hgM hBru hidx hJM hwM (hV2 w hwV) hx hfix
    have h1 := toPermHom_eq_one_of_mem_kerIn (M := M) (z := ⟨w, hMX hwM⟩) hwJ
    have h2 : τ q₁ = q₁ := by rw [hτdef, h1]; rfl
    exact hσf q₁ hq₁ (hστ.trans h2)
  have hστeq : σ = τ := eq_of_fpf hQ' hq₁ hσ0 hτ0 hσ2 hτ2 hσf hτf hστ
  refine ⟨w, hwV, ?_⟩
  have h3 : φ (⟨w, hMX hwM⟩⁻¹ * ⟨m * v * m⁻¹, huX⟩) = 1 := by
    rw [map_mul, map_inv]
    rw [← hσdef, ← hτdef, hστeq]
    simp
  have h4 := mem_kerIn_of_toPermHom_eq_one h3
  simpa using h4

end WGen

end CFSG.Quasithin.Res2

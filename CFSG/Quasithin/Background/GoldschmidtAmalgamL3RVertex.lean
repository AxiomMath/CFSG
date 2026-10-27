module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3FQuad
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem Zv_le_Vv {u v : CosetGeom (A ⊔ B) A B} (huv : (graph (A ⊔ B) A B).Adj u v)
    (hu : vtype u = false) : Zv z v ≤ Vv V u :=
  Zv_le_Vv_of_adj h.natural.z_mem_V h.natural.reduced.2.1 h.normalizes_zpowers huv hu

theorem card_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) : Nat.card (Zv z v) = 2 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Zv_smul_γ₁ h.normalizes_zpowers, card_conjSub]
  exact card_zpowers_eq_two h.natural

theorem card_Vv_A {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) : Nat.card (Vv V u) = 4 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, card_conjSub]
  exact h.natural.card_eq

theorem card_Vv_B (hU : Nat.card (conjClosure V B) = 8) {v : CosetGeom (A ⊔ B) A B}
    (hv : vtype v = true) : Nat.card (Vv V v) = 8 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1, card_conjSub]
  exact hU

variable [Finite D]

theorem exists_adj_mem_Zv {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) {c : D}
    (hc : c ∈ Vv V u) (hc1 : c ≠ 1) :
    ∃ v, (graph (A ⊔ B) A B).Adj u v ∧ c ∈ Zv z v := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub] at hc
  have hc1' : (g : D)⁻¹ * c * g ≠ 1 := fun e => hc1 (by
    have : c = g * ((g : D)⁻¹ * c * g) * (g : D)⁻¹ := by group
    rw [this, e]; group)
  obtain ⟨a, haA, hae⟩ := h.exists_conj_of_mem_V hc hc1'
  have haG : a ∈ A ⊔ B := (le_sup_left : A ≤ A ⊔ B) haA
  have e0 : (⟨a, haG⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B :=
    smul_γ₀_of_mem le_sup_left haA
  refine ⟨(g * ⟨a, haG⟩) • γ₁ (A ⊔ B) A B, ?_, ?_⟩
  · have := (smul_adj (g * ⟨a, haG⟩)).mpr (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B))
    rwa [mul_smul, e0] at this
  · rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub, Subgroup.coe_mul]
    have e : (g * a)⁻¹ * c * (g * a) = a⁻¹ * ((g : D)⁻¹ * c * g) * a := by group
    rw [e, hae]
    have e2 : a⁻¹ * (a * z * a⁻¹) * a = z := by group
    rw [e2]
    exact Subgroup.mem_zpowers z

theorem eq_of_Zv_eq {u v w : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w)
    (hzz : Zv z v = Zv z w) : v = w := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hv hu
  have hw' : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (g⁻¹ • w) := by
    have := (smul_adj g⁻¹).mpr hw
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk0, hk1⟩ := exists_stab_smul_eq (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)) hw'
  obtain rfl : w = (g * k) • γ₁ (A ⊔ B) A B := by rw [mul_smul, hk1, smul_inv_smul]
  rw [Zv_smul_γ₁ h.normalizes_zpowers, Zv_smul_γ₁ h.normalizes_zpowers, Subgroup.coe_mul,
    conjSub_mul] at hzz
  have hkN : (k : D) ∈ Subgroup.normalizer (Subgroup.zpowers z : Set D) :=
    mem_normalizer_of_conjSub_eq ((conjSub_inj (g : D)).mp hzz).symm
  have hkA : (k : D) ∈ A := by
    have := mem_stab_of_smul_eq hk0
    rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  have hkB : (k : D) ∈ B := (inf_normalizer_zpowers_le h.gold h.natural ⟨hkA, hkN⟩).2
  have : k • γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B := smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) hkB
  rw [mul_smul, this]

theorem sup_stab_inf_eq {u v w : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w) (hvw : v ≠ w) :
    stab u ⊓ stab v ⊔ stab u ⊓ stab w = stab u := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hv hu
  have hw' : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (g⁻¹ • w) := by
    have := (smul_adj g⁻¹).mpr hw
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk0, hk1⟩ := exists_stab_smul_eq (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)) hw'
  obtain rfl : w = (g * k) • γ₁ (A ⊔ B) A B := by rw [mul_smul, hk1, smul_inv_smul]
  have hkA : (k : D) ∈ A := by
    have := mem_stab_of_smul_eq hk0
    rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  have hkB : (k : D) ∉ B := fun hkB => hvw (by
    have : k • γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B :=
      smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) hkB
    rw [mul_smul, this])
  have key : A ⊓ B ⊔ A ⊓ conjSub (k : D) B = A := by
    have e : A ⊓ conjSub (k : D) B = conjSub (k : D) (A ⊓ B) := by
      rw [conjSub_inf, F7.conjSub_eq_of_mem hkA]
    rw [e]
    exact h.gold.sup_conjSub_inf_eq_left hkA hkB
  rw [stab_smul, stab_smul, stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B),
    stab_γ₁ (le_sup_right : B ≤ A ⊔ B), Subgroup.coe_mul, conjSub_mul, ← conjSub_inf,
    ← conjSub_inf, ← conjSub_sup, key]

theorem mem_Zv_of_mem_Vv_of_mem_Vv {v α α' : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (hα : (graph (A ⊔ B) A B).Adj v α) (hα' : (graph (A ⊔ B) A B).Adj v α') (hne : α ≠ α')
    {c : D} (hc : c ∈ Vv V α) (hc' : c ∈ Vv V α') : c ∈ Zv z v := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  have hadj : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) :=
    (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm
  have hα0 : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (g⁻¹ • α) := by
    have := (smul_adj g⁻¹).mpr hα
    rwa [inv_smul_smul] at this
  have hα0' : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (g⁻¹ • α') := by
    have := (smul_adj g⁻¹).mpr hα'
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk1, hk0⟩ := exists_stab_smul_eq hadj hα0
  obtain ⟨k', hk1', hk0'⟩ := exists_stab_smul_eq hadj hα0'
  have hkB : (k : D) ∈ B := by
    have := mem_stab_of_smul_eq hk1
    rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  have hkB' : (k' : D) ∈ B := by
    have := mem_stab_of_smul_eq hk1'
    rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  have hxB : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ B := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact B.mul_mem (B.inv_mem hkB) hkB'
  have hxA : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∉ A := fun hxA => hne (by
    have e0 : (k⁻¹ * k' : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B :=
      smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) hxA
    have e1 : k' • γ₀ (A ⊔ B) A B = k • γ₀ (A ⊔ B) A B := by
      have : k' = k * (k⁻¹ * k') := by group
      rw [this, mul_smul, e0]
    have e2 : g⁻¹ • α = g⁻¹ • α' := by rw [← hk0, ← hk0', e1]
    exact smul_left_cancel g⁻¹ e2)
  obtain rfl : α = (g * k) • γ₀ (A ⊔ B) A B := by rw [mul_smul, hk0, smul_inv_smul]
  obtain rfl : α' = (g * k') • γ₀ (A ⊔ B) A B := by rw [mul_smul, hk0', smul_inv_smul]
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub] at hc hc'
  have hz : ((g * k : ↥(A ⊔ B)) : D)⁻¹ * c * ((g * k : ↥(A ⊔ B)) : D) ∈ Subgroup.zpowers z := by
    refine h.mem_zpowers_of_mem_of_conj_mem hxB (fun hT => hxA hT.1) hc ?_
    have e : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * (((g * k : ↥(A ⊔ B)) : D)⁻¹ * c *
        ((g * k : ↥(A ⊔ B)) : D)) * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) =
        ((g * k' : ↥(A ⊔ B)) : D)⁻¹ * c * ((g * k' : ↥(A ⊔ B)) : D) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hc'
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub]
  have e : (g : D)⁻¹ * c * g = k * (((g * k : ↥(A ⊔ B)) : D)⁻¹ * c * ((g * k : ↥(A ⊔ B)) : D)) *
      (k : D)⁻¹ := by
    simp only [Subgroup.coe_mul]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (h.normalizes_zpowers hkB) _).mp hz

omit [Finite D] in
theorem commutator_mem_Zv {u v : CosetGeom (A ⊔ B) A B} (huv : (graph (A ⊔ B) A B).Adj u v)
    (hu : vtype u = false) {x w : D} (hx : x ∈ stab u ⊓ stab v) (hw : w ∈ Vv V u) :
    x * w * x⁻¹ * w⁻¹ ∈ Zv z v := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [stab_smul, stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B),
    stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf, mem_conjSub] at hx
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub] at hw
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub]
  have e : (g : D)⁻¹ * (x * w * x⁻¹ * w⁻¹) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * w * g) *
      ((g : D)⁻¹ * x * g)⁻¹ * ((g : D)⁻¹ * w * g)⁻¹ := by group
  rw [e]
  exact h.commutator_V_T hx hw

omit [Finite D] in
theorem commutator_mem_Vv (hU : Nat.card (conjClosure V B) = 8)
    {u v : CosetGeom (A ⊔ B) A B} (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false)
    {x w : D} (hx : x ∈ stab u ⊓ stab v) (hw : w ∈ Vv V v) : x * w * x⁻¹ * w⁻¹ ∈ Vv V u := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [stab_smul, stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B),
    stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf, mem_conjSub] at hx
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1, mem_conjSub] at hw
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub]
  have e : (g : D)⁻¹ * (x * w * x⁻¹ * w⁻¹) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * w * g) *
      ((g : D)⁻¹ * x * g)⁻¹ * ((g : D)⁻¹ * w * g)⁻¹ := by group
  rw [e]
  exact h.commutator_U_T hU hx hw

theorem mem_ballStab_one_of_centralizes {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) {x : D}
    (hx : x ∈ stab u) (hc : ∀ w ∈ Vv V u, x * w * x⁻¹ = w) : x ∈ ballStab 1 u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [ballStab_smul, mem_conjSub]
  rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B), mem_conjSub] at hx
  have hxc : (g : D)⁻¹ * x * g ∈ Subgroup.centralizer (V : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hc ((g : D) * v * (g : D)⁻¹) (by
      rw [Vv_smul_γ₀ h.natural.reduced.2.1]
      exact mul_mem_conjSub hv)
    have hx2 : x * ((g : D) * v * (g : D)⁻¹) = ((g : D) * v * (g : D)⁻¹) * x :=
      mul_inv_eq_iff_eq_mul.mp h1
    calc v * ((g : D)⁻¹ * x * g) = (g : D)⁻¹ * (((g : D) * v * (g : D)⁻¹) * x) * g := by group
      _ = (g : D)⁻¹ * (x * ((g : D) * v * (g : D)⁻¹)) * g := by rw [hx2]
      _ = (g : D)⁻¹ * x * g * v := by group
  have hxQ : (g : D)⁻¹ * x * g ∈ pCoreOf 2 A := by
    rw [← h.natural.centralizer_eq]
    exact ⟨hx, hxc⟩
  have := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₀ (A ⊔ B) A B)
  rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  exact this hxQ

theorem mem_ballStab_one_of_commutator {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {x : D}
    (hx : x ∈ stab v) (hc : ∀ w ∈ Vv V v, x * w * x⁻¹ * w⁻¹ ∈ Zv z v) : x ∈ ballStab 1 v := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [ballStab_smul, mem_conjSub]
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hx
  have hxK : (g : D)⁻¹ * x * g ∈ centralizerMod (Subgroup.zpowers z) B (conjClosure V B) := by
    refine ⟨hx, h.normalizes_zpowers hx, fun w hw => ?_⟩
    have h1 := hc ((g : D) * w * (g : D)⁻¹) (by
      rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1]
      exact mul_mem_conjSub hw)
    rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub] at h1
    have e : (g : D)⁻¹ * (x * ((g : D) * w * (g : D)⁻¹) * x⁻¹ * ((g : D) * w * (g : D)⁻¹)⁻¹) * g =
        ((g : D)⁻¹ * x * g) * w * ((g : D)⁻¹ * x * g)⁻¹ * w⁻¹ := by group
    rw [e] at h1
    exact h1
  have h2 := h.pCoreOf_eq_centralizerMod.ge hxK
  have := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₁ (A ⊔ B) A B)
  rw [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  exact this h2

theorem not_stab_le_normalizer_Vv {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    ¬ stab u ≤ Subgroup.normalizer (Vv V v : Set D) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B), Vv_smul h.natural.reduced.2.1,
    Vv_γ₁ le_sup_right h.natural.reduced.2.1]
  intro hle
  apply h.not_le_normalizer_conjClosure
  rw [conjSub_normalizer, conjSub_le_iff, conjSub_conjSub_inv] at hle
  exact hle

theorem Vv_le_ballStab_A {b : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) : Vv V u ≤ ballStab b u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, ballStab_smul]
  refine conjSub_mono _ ?_
  have := (critDist_spec (h.gold.amalgamHypV h.natural) h.natural.natural.ne_bot).2.1
  rwa [hb] at this

theorem Vv_le_ballStab_B {n : ℕ} (hb : critDist (A ⊔ B) A B V = n + 1)
    {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) : Vv V v ≤ ballStab n v := by
  refine (Vv_B_le_iff hv).mpr fun u hu => ?_
  have hu0 : vtype u = false := vtype_eq_false_of_adj hu hv
  exact (h.Vv_le_ballStab_A hb hu0).trans (ballStab_succ_le_of_adj hu.symm n)

theorem Vv_le_stab_A {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) {u w : CosetGeom (A ⊔ B) A B}
    (hu : vtype u = false) (hd : CosetGeom.dist u w ≤ b) : Vv V u ≤ stab w :=
  (h.Vv_le_ballStab_A hb hu).trans (ballStab_le_stab_of_dist_le hd)

theorem Vv_le_stab_B {n : ℕ} (hb : critDist (A ⊔ B) A B V = n + 1)
    {v w : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) (hd : CosetGeom.dist v w ≤ n) :
    Vv V v ≤ stab w :=
  (h.Vv_le_ballStab_B hb hv).trans (ballStab_le_stab_of_dist_le hd)

theorem commutator_mem_Vv_inf (hU : Nat.card (conjClosure V B) = 8) {n : ℕ}
    (hb : critDist (A ⊔ B) A B V = n + 1) {u u' v v' : CosetGeom (A ⊔ B) A B}
    (hu : vtype u = true) (hv : vtype v = true) (huu' : (graph (A ⊔ B) A B).Adj u u')
    (hvv' : (graph (A ⊔ B) A B).Adj v v') (h1 : CosetGeom.dist u v ≤ n)
    (h2 : CosetGeom.dist u v' ≤ n) (h3 : CosetGeom.dist v u ≤ n) (h4 : CosetGeom.dist v u' ≤ n)
    {x w : D} (hx : x ∈ Vv V u) (hw : w ∈ Vv V v) :
    x * w * x⁻¹ * w⁻¹ ∈ Vv V u' ⊓ Vv V v' := by
  have hu' : vtype u' = false := vtype_eq_false_of_adj huu' hu
  have hv' : vtype v' = false := vtype_eq_false_of_adj hvv' hv
  have hxv : x ∈ stab v' ⊓ stab v :=
    ⟨h.Vv_le_stab_B hb hu h2 hx, h.Vv_le_stab_B hb hu h1 hx⟩
  have hwu : w ∈ stab u' ⊓ stab u :=
    ⟨h.Vv_le_stab_B hb hv h4 hw, h.Vv_le_stab_B hb hv h3 hw⟩
  refine ⟨?_, h.commutator_mem_Vv hU hvv'.symm hv' hxv hw⟩
  have := h.commutator_mem_Vv hU huu'.symm hu' hwu hx
  have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (Vv V u').inv_mem this

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

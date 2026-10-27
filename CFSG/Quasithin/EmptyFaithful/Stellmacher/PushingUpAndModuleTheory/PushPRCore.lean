module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRFrat
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_cj_iff {g x : G} {A : Subgroup G} :
    x ∈ Subgroup.normalizer ((cj g A : Subgroup G) : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx v
    have := hx (g * v * g⁻¹)
    rw [mem_cj, mem_cj] at this
    have e1 : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    have e2 : g⁻¹ * (x * (g * v * g⁻¹) * x⁻¹) * g =
        g⁻¹ * x * g * v * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro hx w
    rw [mem_cj, mem_cj]
    have := hx (g⁻¹ * w * g)
    have e2 : g⁻¹ * (x * w * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * w * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e2]
    exact this

theorem relIndex_cj_cj (g : G) (A B : Subgroup G) : (cj g A).relIndex (cj g B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

theorem cj_inf (g : G) (A B : Subgroup G) : cj g (A ⊓ B) = cj g A ⊓ cj g B :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem cj_cj_inv (g : G) (A : Subgroup G) : cj g (cj g⁻¹ A) = A := by
  rw [cj_cj, mul_inv_cancel, cj_one]

theorem cj_inv_cj (g : G) (A : Subgroup G) : cj g⁻¹ (cj g A) = A := by
  rw [cj_cj, inv_mul_cancel, cj_one]

section Setting

variable [Finite G] {X P Z : Subgroup G} {y : G}

omit [Finite G] in
theorem PushHyp.P_le_normalizer_core (h : PushHyp X P Z) :
    P ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  h.le_self.trans PushHyp.le_normalizer_core

omit [Finite G] in
theorem inv_conj_mem_of_mem_normalizer {P : Subgroup G} {y p : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hp : p ∈ P) : y⁻¹ * p * y ∈ P := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) p).mp hp
  simpa using this

omit [Finite G] in
theorem PushHyp.P_le_normalizer_cj (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.normalizer ((cj y (pCoreOf 2 X) : Subgroup G) : Set G) := by
  intro p hp
  rw [mem_normalizer_cj_iff]
  exact h.P_le_normalizer_core (inv_conj_mem_of_mem_normalizer hy hp)

theorem PushHyp.inf_centralizer_cj (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    P ⊓ Subgroup.centralizer ((cj y Z : Subgroup G) : Set G) = cj y (pCoreOf 2 X) := by
  rw [← h.inf_centralizer_eq, ← cj_inf_centralizer hy]

omit [Finite G] in
theorem PushHyp.Z_le_normalizer_zZero (h : PushHyp X P Z) :
    Z ≤ Subgroup.normalizer (zZero X Z : Set G) := by
  intro z hz
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨k, hk.1⟩ ⟨z, hz⟩)

omit [Finite G] in
theorem PushHyp.commute_Z_core (h : PushHyp X P Z) {z q : G} (hz : z ∈ Z) (hq : q ∈ pCoreOf 2 X) :
    z * q = q * z :=
  Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hq) z hz

theorem prop41_not_le (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G))
    (hne : ⁅Z, cj y Z⁆ ≠ ⊥) : ¬ cj y Z ≤ pCoreOf 2 X ∧ ¬ Z ≤ cj y (pCoreOf 2 X) := by
  constructor
  · intro hle
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := h.commute_Z_core ha (hle hb)
    rw [Subgroup.mem_bot, commutatorElement_def, this]
    group
  · intro hle
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have h1 : a ∈ Subgroup.centralizer ((cj y Z : Subgroup G) : Set G) := by
      rw [← (h.inf_centralizer_cj hy)] at hle
      exact (hle ha).2
    have := Subgroup.mem_centralizer_iff.mp h1 b hb
    rw [Subgroup.mem_bot, commutatorElement_def, ← this]
    group

theorem prop41_core_ne (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G))
    (hne : ⁅Z, cj y Z⁆ ≠ ⊥) : cj y (pCoreOf 2 X) ≠ pCoreOf 2 X := by
  intro heq
  exact (prop41_not_le h hy hne).2 (by rw [heq]; exact h.le_core)

theorem prop41_inf_le_fix (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) {x : G}
    (hx : x ∈ cj y Z) :
    cj y (pCoreOf 2 X) ⊓ Z ≤ fixSecIn (Subgroup.zpowers x) (zZero X Z) Z := by
  rintro z ⟨hzQ', hzZ⟩
  have hxP : x ∈ P := cj_le_of_le_of_mem_normalizer hy h.Z_le hx
  have hxN : x ∈ Subgroup.normalizer (zZero X Z : Set G) := h.le_normalizer_Z0 (h.le_self hxP)
  rw [mem_fixSecIn_zpowers_iff h.Z_le_normalizer_zZero hxN]
  refine ⟨hzZ, ?_⟩
  have hzC : z ∈ Subgroup.centralizer ((cj y Z : Subgroup G) : Set G) := by
    have : z ∈ P ⊓ Subgroup.centralizer ((cj y Z : Subgroup G) : Set G) := by
      rw [h.inf_centralizer_cj hy]; exact hzQ'
    exact this.2
  have := Subgroup.mem_centralizer_iff.mp hzC x hx
  have e : x * z * x⁻¹ * z⁻¹ = 1 := by rw [this]; group
  rw [e]
  exact (zZero X Z).one_mem

theorem PushHyp.hZ'P (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    cj y Z ≤ P := cj_le_of_le_of_mem_normalizer hy h.Z_le

theorem PushHyp.hQ'P (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    cj y (pCoreOf 2 X) ≤ P := cj_le_of_le_of_mem_normalizer hy h.core_le

theorem PushHyp.hcZ (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) {z b : G}
    (hz : z ∈ Z) (hb : b ∈ cj y Z) : ⁅z, b⁆ ∈ Z := by
  have hbX : b ∈ X := h.le_self (h.hZ'P hy hb)
  have := (Subgroup.mem_normalizer_iff.mp (h.normal hbX) z⁻¹).mp (Z.inv_mem hz)
  have e : ⁅z, b⁆ = z * (b * z⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Z.mul_mem hz this

theorem prop41_le_c (h : PushHyp X P Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥) :
    (pCoreOf 2 X).relIndex P ≤ (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z := by
  obtain ⟨x, hxZ', hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp (prop41_not_le h hy hne).1
  exact (hN.tr x (h.hZ'P hy hxZ') hxQ).trans
    (relIndex_le_of_le Z (prop41_inf_le_fix h hy hxZ'))

theorem prop41_d_le (h : PushHyp X P Z) (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z) ≤ (pCoreOf 2 X).relIndex P := by
  have hZ'n : cj y Z ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    (h.hZ'P hy).trans h.P_le_normalizer_core
  have h1 := relIndex_sup_eq_relIndex_inf_right hZ'n
  have h2 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) (pCoreOf 2 X ⊔ cj y Z) P le_sup_left
    (sup_le h.core_le (h.hZ'P hy))
  rw [← h1]
  exact Nat.le_of_dvd (relIndex_pos _ _) (Dvd.intro _ h2)

theorem prop41_eq (h : PushHyp X P Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥)
    (hle : (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z ≤ (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z)) :
    (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z = (pCoreOf 2 X).relIndex P ∧
      (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z) = (pCoreOf 2 X).relIndex P := by
  have h1 := prop41_le_c h hN hy hne
  have h2 := prop41_d_le h hy
  omega

theorem eq_of_relIndex_eq {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (h : A.relIndex B = A.relIndex C) : C ≤ B := by
  have h1 := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  have hpos := relIndex_pos A B
  have : B.relIndex C = 1 := by
    rw [← h] at h1
    have h2 : A.relIndex B * B.relIndex C = A.relIndex B * 1 := by rw [h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  exact Subgroup.relIndex_eq_one.mp this

theorem prop41_P_le (h : PushHyp X P Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥)
    (hle : (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z ≤ (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z)) :
    P ≤ cj y (pCoreOf 2 X) ⊔ Z ∧ P ≤ pCoreOf 2 X ⊔ cj y Z := by
  obtain ⟨hc, hd⟩ := prop41_eq h hN hy hne hle
  constructor
  · have hZn : Z ≤ Subgroup.normalizer ((cj y (pCoreOf 2 X) : Subgroup G) : Set G) :=
      h.Z_le.trans (h.P_le_normalizer_cj hy)
    have h1 := relIndex_sup_eq_relIndex_inf_right hZn
    refine eq_of_relIndex_eq le_sup_left (sup_le (h.hQ'P hy) h.Z_le) ?_
    rw [h1, hc, relIndex_cj hy]
  · have hZ'n : cj y Z ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      (h.hZ'P hy).trans h.P_le_normalizer_core
    have h1 := relIndex_sup_eq_relIndex_inf_right hZ'n
    refine eq_of_relIndex_eq le_sup_left (sup_le h.core_le (h.hZ'P hy)) ?_
    rw [h1, hd]

theorem prop41_hG (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hne : ⁅Z, cj y Z⁆ ≠ ⊥)
    (hle : (cj y (pCoreOf 2 X) ⊓ Z).relIndex Z ≤ (pCoreOf 2 X ⊓ cj y Z).relIndex (cj y Z)) :
    ∀ z ∈ Z, z ∉ cj y (pCoreOf 2 X) → ∀ b ∈ cj y Z, b ∉ pCoreOf 2 X →
      ⁅z, b⁆ ∉ phi (pCoreOf 2 X) := by
  intro z hz hzQ' b hb hbQ hmem
  have hb0 : ⁅z, b⁆ ∈ zZero X Z := inf_phi_le_zZero h hB hN ⟨h.hcZ hy hz hb, hmem⟩
  have hbP : b ∈ P := h.hZ'P hy hb
  have hbN : b ∈ Subgroup.normalizer (zZero X Z : Set G) := h.le_normalizer_Z0 (h.le_self hbP)
  have hzC : z ∈ fixSecIn (Subgroup.zpowers b) (zZero X Z) Z := by
    rw [mem_fixSecIn_zpowers_iff h.Z_le_normalizer_zZero hbN]
    refine ⟨hz, ?_⟩
    have e : b * z * b⁻¹ * z⁻¹ = ⁅z, b⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (zZero X Z).inv_mem hb0
  have hsub := prop41_inf_le_fix h hy hb
  have hCZ : fixSecIn (Subgroup.zpowers b) (zZero X Z) Z ≤ Z := fun x hx => by
    rw [mem_fixSecIn_zpowers_iff h.Z_le_normalizer_zZero hbN] at hx
    exact hx.1
  have hq := hN.tr b hbP hbQ
  have hceq := (prop41_eq h hN hy hne hle).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ Z hsub hCZ
  rw [hceq] at hmul
  have hpos := relIndex_pos (cj y (pCoreOf 2 X) ⊓ Z) (fixSecIn (Subgroup.zpowers b) (zZero X Z) Z)
  have hq0 := relIndex_pos (pCoreOf 2 X) P
  have ha1 : (cj y (pCoreOf 2 X) ⊓ Z).relIndex (fixSecIn (Subgroup.zpowers b) (zZero X Z) Z) = 1 := by
    by_contra hne1
    have h2 : 2 ≤ (cj y (pCoreOf 2 X) ⊓ Z).relIndex
        (fixSecIn (Subgroup.zpowers b) (zZero X Z) Z) := by omega
    nlinarith
  exact hzQ' ((Subgroup.relIndex_eq_one.mp ha1) hzC).1

end Setting

end CFSG.Quasithin.F53Push

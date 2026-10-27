module

public import CFSG.Quasithin.H13.NQS134EK
public import CFSG.Quasithin.H13.NQS13412D
public import CFSG.Quasithin.H13.NQS134ED

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out

variable {G : Type} [Group G] {T K W : Subgroup G}

namespace F5

variable (F : Frame5 T K W)
include F

theorem conj (g : ↥(normalizer (W : Set G))) (w : ↥W) :
    (F.ψ ⟨(g : G) * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩ : P6) =
      G6.permAct 6 (F.ρ g) (F.ψ w : P6) := by
  have h1 := F.equiv g w
  have e : conjAct W g w = ⟨(g : G) * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩ :=
    Subtype.ext (A5.conjAct_val W g w)
  rw [e] at h1
  rw [h1, G6.coreAct_coe]

theorem fix_iff (g : ↥(normalizer (W : Set G))) (w : ↥W) :
    (g : G) * w * (g : G)⁻¹ = w ↔ G6.permAct 6 (F.ρ g) (F.ψ w : P6) = F.ψ w := by
  rw [← conj F g w]
  constructor
  · intro h
    congr 2
    exact Subtype.ext h
  · intro h
    have h1 := F.ψ.injective (Subtype.ext h)
    exact congrArg Subtype.val h1

theorem mul {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    (F.ψ ⟨a * b, mul_mem ha hb⟩ : P6) = (F.ψ ⟨a, ha⟩ : P6) * (F.ψ ⟨b, hb⟩ : P6) := by
  rw [show (⟨a * b, mul_mem ha hb⟩ : ↥W) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
  rfl

theorem comm {x w : G} (hx : x ∈ normalizer (W : Set G)) (hw : w ∈ W)
    (hc : x * w * x⁻¹ * w⁻¹ ∈ W) :
    (F.ψ ⟨x * w * x⁻¹ * w⁻¹, hc⟩ : P6) =
      G6.permAct 6 (F.ρ ⟨x, hx⟩) (F.ψ ⟨w, hw⟩ : P6) * (F.ψ ⟨w, hw⟩ : P6) := by
  have hxw : x * w * x⁻¹ ∈ W := (mem_normalizer_iff.mp hx w).mp hw
  rw [show (⟨x * w * x⁻¹ * w⁻¹, hc⟩ : ↥W) = ⟨x * w * x⁻¹, hxw⟩ * (⟨w, hw⟩ : ↥W)⁻¹ from rfl,
    map_mul, map_inv]
  show ((F.ψ ⟨x * w * x⁻¹, hxw⟩ : P6) * ((F.ψ ⟨w, hw⟩)⁻¹ : ↥(G6.coreMod 6))) = _
  rw [conj F ⟨x, hx⟩ ⟨w, hw⟩]
  congr 1
  show ((F.ψ ⟨w, hw⟩ : P6))⁻¹ = (F.ψ ⟨w, hw⟩ : P6)
  exact inv_eq_of_mul_eq_one_right (P6_mul_self _)

theorem ker_iff (g : ↥(normalizer (W : Set G))) :
    F.ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G) :=
  frame5_ker_iff F g

theorem psi_eq_one_iff {w : G} (hw : w ∈ W) : (F.ψ ⟨w, hw⟩ : P6) = 1 ↔ w = 1 := by
  constructor
  · intro h
    have h1 : F.ψ ⟨w, hw⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  · rintro rfl
    rw [show (⟨1, hw⟩ : ↥W) = 1 from rfl, map_one]
    rfl

theorem psi_inj {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (h : (F.ψ ⟨a, ha⟩ : P6) = F.ψ ⟨b, hb⟩) : a = b :=
  congrArg Subtype.val (F.ψ.injective (Subtype.ext h))

theorem exists_of_core {x : P6} (hx : ∑ i, Multiplicative.toAdd x i = 0) :
    ∃ (w : G) (hw : w ∈ W), (F.ψ ⟨w, hw⟩ : P6) = x :=
  ⟨(F.ψ.symm ⟨x, G6.mem_coreMod.2 hx⟩ : G), (F.ψ.symm _).2, by
    rw [show (⟨((F.ψ.symm ⟨x, G6.mem_coreMod.2 hx⟩ : ↥W) : G), (F.ψ.symm _).2⟩ : ↥W) =
      F.ψ.symm ⟨x, G6.mem_coreMod.2 hx⟩ from rfl, MulEquiv.apply_symm_apply]⟩

theorem psi_core (w : ↥W) : ∑ i, Multiplicative.toAdd (F.ψ w : P6) i = 0 :=
  G6.mem_coreMod.1 (F.ψ w).2

theorem centralizer_A6 {w : G} (hw : w ∈ W) (hwK : w ∈ centralizer (K : Set G)) :
    (F.ψ ⟨w, hw⟩ : P6) = 1 ∨ (F.ψ ⟨w, hw⟩ : P6) = G6.allOnes 6 := by
  have hfix : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) →
      G6.permAct 6 σ (F.ψ ⟨w, hw⟩ : P6) = F.ψ ⟨w, hw⟩ := by
    intro σ hσ
    obtain ⟨g, hgK, hgσ⟩ := (F.image_L σ).2 hσ
    rw [← hgσ, ← fix_iff F g ⟨w, hw⟩]
    show (g : G) * w * (g : G)⁻¹ = w
    rw [mem_centralizer_iff.1 hwK g hgK, mul_inv_cancel_right]
  exact fix3_core _ (hfix _ (Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (Perm.mem_alternatingGroup.2 (by decide)))

theorem centralizer_T {w : G} (hw : w ∈ W) (hwT : w ∈ centralizer (T : Set G)) :
    (F.ψ ⟨w, hw⟩ : P6) = 1 ∨ (F.ψ ⟨w, hw⟩ : P6) = e45 ∨ (F.ψ ⟨w, hw⟩ : P6) = e0123 ∨
      (F.ψ ⟨w, hw⟩ : P6) = G6.allOnes 6 := by
  have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      G6.permAct 6 σ (F.ψ ⟨w, hw⟩ : P6) = F.ψ ⟨w, hw⟩ := by
    intro σ hσD hσ
    obtain ⟨g, hgT, hgσ⟩ := F.DA_T σ hσD hσ
    rw [← hgσ, ← fix_iff F g ⟨w, hw⟩]
    show (g : G) * w * (g : G)⁻¹ = w
    rw [mem_centralizer_iff.1 hwT g hgT, mul_inv_cancel_right]
  exact fixDA_core _ (psi_core F _) (hfix _ (by decide) (Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (by decide) (Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (by decide) (Perm.mem_alternatingGroup.2 (by decide)))

theorem card_le_eight [Finite G] {X : Subgroup G} (hXT : X ≤ T) (hX2 : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 8 * Nat.card ↥(X ⊓ centralizer (W : Set G)) ∧
      (Nat.card X = 8 * Nat.card ↥(X ⊓ centralizer (W : Set G)) →
        ∃ a₁ ∈ X, a₁ ∉ centralizer (W : Set G) ∧ ∃ a₂ ∈ X, ∃ w ∈ W,
          a₁ * w = w * a₁ ∧ a₂ * w ≠ w * a₂) := by
  classical
  have hXN : X ≤ normalizer (W : Set G) := hXT.trans F.T_le
  let f : ↥X →* Perm (Fin 6) := F.ρ.comp (Subgroup.inclusion hXN)
  have hker : f.ker = (X ⊓ centralizer (W : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    simp only [f, MonoidHom.comp_apply]
    refine ⟨fun h => ⟨x.2, (ker_iff F _).1 h⟩, fun h => ?_⟩
    exact (ker_iff F (Subgroup.inclusion hXN x)).2 h.2
  have hcardker : Nat.card f.ker = Nat.card ↥(X ⊓ centralizer (W : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : X ⊓ centralizer (W : Set G) ≤ X)).toEquiv
  have hmul : Nat.card ↥(X ⊓ centralizer (W : Set G)) * Nat.card f.range = Nat.card X := by
    rw [← hcardker, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hRD : ∀ σ ∈ f.range, InD6 σ := by
    rintro _ ⟨a, rfl⟩
    exact F.T_D _ (hXT a.2)
  have hR2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hX2 a a.2)
    rw [this, map_one]
  have hR8 : Nat.card f.range ≤ 8 := by
    by_cases h : 4 < Nat.card f.range
    · exact (D_e8 hRD hR2 h).1
    · omega
  refine ⟨?_, fun heq => ?_⟩
  · rw [← hmul, mul_comm]
    exact Nat.mul_le_mul_right _ hR8
  · have hpos := Nat.card_pos (α := ↥(X ⊓ centralizer (W : Set G)))
    have hR8' : Nat.card f.range = 8 := by
      have h1 : Nat.card ↥(X ⊓ centralizer (W : Set G)) * Nat.card f.range =
          Nat.card ↥(X ⊓ centralizer (W : Set G)) * 8 := by rw [hmul, heq, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    obtain ⟨-, hcases⟩ := D_e8 hRD hR2 (by omega)
    have hex : ∀ σ ∈ f.range, ∃ (a : G) (ha : a ∈ X), F.ρ ⟨a, hXN ha⟩ = σ := by
      rintro _ ⟨⟨a, ha⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    obtain ⟨⟨h24, h24a, h24b⟩, ⟨h02, h02a, h02b⟩⟩ := e24_e02_facts
    rcases hcases with ⟨h01, h23⟩ | ⟨-, h6, h1, -⟩
    · obtain ⟨a₁, ha₁, hρ₁⟩ := hex _ h01
      obtain ⟨a₂, ha₂, hρ₂⟩ := hex _ h23
      obtain ⟨w, hw, hψw⟩ := exists_of_core F h24
      refine ⟨a₁, ha₁, fun h => ?_, a₂, ha₂, w, hw, ?_, fun h => ?_⟩
      · have := (ker_iff F ⟨a₁, hXN ha₁⟩).2 h
        rw [hρ₁] at this
        exact absurd this (by decide)
      · have h1 := (fix_iff F ⟨a₁, hXN ha₁⟩ ⟨w, hw⟩).2 (by rw [hρ₁, hψw]; exact h24a)
        calc a₁ * w = a₁ * w * a₁⁻¹ * a₁ := by group
          _ = w * a₁ := by rw [h1]
      · apply h24b
        have h1 : a₂ * w * a₂⁻¹ = w := by rw [h, mul_inv_cancel_right]
        have h2 := (fix_iff F ⟨a₂, hXN ha₂⟩ ⟨w, hw⟩).1 h1
        rwa [hρ₂, hψw] at h2
    · obtain ⟨a₁, ha₁, hρ₁⟩ := hex _ h1
      obtain ⟨a₂, ha₂, hρ₂⟩ := hex _ h6
      obtain ⟨w, hw, hψw⟩ := exists_of_core F h02
      have hd1 : d6 1 = swap 4 5 := d6_canonical.2.2
      refine ⟨a₁, ha₁, fun h => ?_, a₂, ha₂, w, hw, ?_, fun h => ?_⟩
      · have := (ker_iff F ⟨a₁, hXN ha₁⟩).2 h
        rw [hρ₁, hd1] at this
        exact absurd this (by decide)
      · have h1 := (fix_iff F ⟨a₁, hXN ha₁⟩ ⟨w, hw⟩).2 (by rw [hρ₁, hd1, hψw]; exact h02a)
        calc a₁ * w = a₁ * w * a₁⁻¹ * a₁ := by group
          _ = w * a₁ := by rw [h1]
      · apply h02b
        have h1 : a₂ * w * a₂⁻¹ = w := by rw [h, mul_inv_cancel_right]
        have h2 := (fix_iff F ⟨a₂, hXN ha₂⟩ ⟨w, hw⟩).1 h1
        rwa [hρ₂, hψw] at h2

end F5

end CFSG.Quasithin.H13.NQS134

module

public import CFSG.Quasithin.H13.NQS134EP
public import CFSG.Quasithin.H13.NQS13412D
public import CFSG.Quasithin.H13.NQS134ED

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out CFSG.Quasithin.H13.NQS134.End134
open scoped IsMulCommutative

variable {G : Type} [Group G] {T K W : Subgroup G}

namespace F4

variable (F : Frame4 T K W)
include F

theorem conj (g : ↥(normalizer (W : Set G))) (w : ↥W) :
    (F.ψ ⟨(g : G) * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩ : P6) =
      act4f (F.ρ g) (F.ψ w : P6) := by
  have h1 := F.equiv g w
  have e : conjAct W g w = ⟨(g : G) * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩ :=
    Subtype.ext (A5.conjAct_val W g w)
  rw [e] at h1
  rw [h1, act4_coe]
  rfl

theorem fix_iff (g : ↥(normalizer (W : Set G))) (w : ↥W) :
    (g : G) * w * (g : G)⁻¹ = w ↔ act4f (F.ρ g) (F.ψ w : P6) = F.ψ w := by
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

theorem exists_of_W4 {x : P6} (hx : InW4 x) : ∃ (w : G) (hw : w ∈ W), (F.ψ ⟨w, hw⟩ : P6) = x :=
  ⟨(F.ψ.symm ⟨x, hx⟩ : G), (F.ψ.symm _).2, by
    rw [show (⟨((F.ψ.symm ⟨x, hx⟩ : ↥W) : G), (F.ψ.symm _).2⟩ : ↥W) =
      F.ψ.symm ⟨x, hx⟩ from rfl, MulEquiv.apply_symm_apply]⟩

theorem psi_W4 (w : ↥W) : InW4 (F.ψ w : P6) := (F.ψ w).2

theorem centralizer_T {w : G} (hw : w ∈ W) (hwT : w ∈ centralizer (T : Set G)) :
    (F.ψ ⟨w, hw⟩ : P6) = 1 ∨ (F.ψ ⟨w, hw⟩ : P6) = e0123 := by
  have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      act4f σ (F.ψ ⟨w, hw⟩ : P6) = F.ψ ⟨w, hw⟩ := by
    intro σ hσD hσ
    obtain ⟨g, hgT, hgσ⟩ := F.DA_T σ hσD hσ
    rw [← hgσ, ← fix_iff F g ⟨w, hw⟩]
    show (g : G) * w * (g : G)⁻¹ = w
    rw [mem_centralizer_iff.1 hwT g hgT, mul_inv_cancel_right]
  exact fixDA_w4 _ (psi_W4 F _) (hfix _ (by decide) (Perm.mem_alternatingGroup.2 (by decide)))
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
    refine ⟨fun h => ⟨x.2, (frame4_ker_iff F _).1 h⟩, fun h => ?_⟩
    exact (frame4_ker_iff F (Subgroup.inclusion hXN x)).2 h.2
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
    obtain ⟨⟨h24, h24a, h24b⟩, ⟨h02, h02a, h02b⟩⟩ := e24_e02_w4
    rcases hcases with ⟨h01, h23⟩ | ⟨-, h6, h1, -⟩
    · obtain ⟨a₁, ha₁, hρ₁⟩ := hex _ h01
      obtain ⟨a₂, ha₂, hρ₂⟩ := hex _ h23
      obtain ⟨w, hw, hψw⟩ := exists_of_W4 F h24
      refine ⟨a₁, ha₁, fun h => ?_, a₂, ha₂, w, hw, ?_, fun h => ?_⟩
      · have := (frame4_ker_iff F ⟨a₁, hXN ha₁⟩).2 h
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
      obtain ⟨w, hw, hψw⟩ := exists_of_W4 F h02
      have hd1 : d6 1 = swap 4 5 := d6_canonical.2.2
      refine ⟨a₁, ha₁, fun h => ?_, a₂, ha₂, w, hw, ?_, fun h => ?_⟩
      · have := (frame4_ker_iff F ⟨a₁, hXN ha₁⟩).2 h
        rw [hρ₁, hd1] at this
        exact absurd this (by decide)
      · have h1 := (fix_iff F ⟨a₁, hXN ha₁⟩ ⟨w, hw⟩).2 (by rw [hρ₁, hd1, hψw]; exact h02a)
        calc a₁ * w = a₁ * w * a₁⁻¹ * a₁ := by group
          _ = w * a₁ := by rw [h1]
      · apply h02b
        have h1 : a₂ * w * a₂⁻¹ = w := by rw [h, mul_inv_cancel_right]
        have h2 := (fix_iff F ⟨a₂, hXN ha₂⟩ ⟨w, hw⟩).1 h1
        rwa [hρ₂, hψw] at h2

end F4

theorem mem_W_or_mul {W : Subgroup G} {z x : G} (hzW : z ∈ normalizer (W : Set G))
    (hz2 : z * z = 1) (hx : x ∈ W ⊔ zpowers z) : x ∈ W ∨ x * z ∈ W := by
  have hle : zpowers z ≤ normalizer (W : Set G) := zpowers_le.2 hzW
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W (zpowers z) hle] at hx
  obtain ⟨w, hw, c, hc, rfl⟩ := hx
  have hcases : c = 1 ∨ c = z := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, hz2]
    rcases Int.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · left
      rw [← two_mul, zpow_mul, hz2', one_zpow]
    · right
      rw [zpow_add, zpow_one, zpow_mul, hz2', one_zpow, one_mul]
  rcases hcases with h | h
  · left
    show w * c ∈ W
    rw [h, mul_one]
    exact hw
  · right
    show w * c * z ∈ W
    rw [h, mul_assoc, hz2, mul_one]
    exact hw

end CFSG.Quasithin.H13.NQS134

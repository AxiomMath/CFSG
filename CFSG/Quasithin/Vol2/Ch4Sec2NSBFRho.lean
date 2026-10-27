module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFLemA
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKAct

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k n j : ℕ}

theorem uZero_comm (D : StdData G T L I K m k n j) {x y : G} (hx : x ∈ uZero I K)
    (hy : y ∈ uZero I K) : x * y = y * x :=
  coG_injOn D (mul_mem hx hy) (mul_mem hy hx)
    (by rw [coG_mul D hx hy, coG_mul D hy hx, add_comm])

@[expose] def IsRho (D : StdData G T L I K m k n j)
    (ρ : G → Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ r ∈ pCoreOf 2 I, ∀ z ∈ uZero I K,
    r * z * r⁻¹ ∈ uZero I K ∧ coG D (r * z * r⁻¹) = actM (ρ r) (coG D z)

theorem exists_rho (hIH : I ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hn : 0 < n)
    (hj : 0 < j) (D : StdData G T L I K m k n j) :
    ∃ ρ : G → Matrix (Fin n) (Fin n) (ZMod 2), IsRho D ρ := by
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have h : ∀ r : G, ∃ B : Matrix (Fin n) (Fin n) (ZMod 2), r ∈ pCoreOf 2 I →
      ∀ z ∈ uZero I K, r * z * r⁻¹ ∈ uZero I K ∧ coG D (r * z * r⁻¹) = actM B (coG D z) := by
    intro r
    by_cases hr : r ∈ pCoreOf 2 I
    · obtain ⟨x, -, hact⟩ := exists_K_action_of_R hIH hHK hn hj D r hr
      refine ⟨((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)), fun _ z hz => ?_⟩
      have hz' : r * z * r⁻¹ ∈ uZero I K :=
        (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_right hr)) z).mp hz
      refine ⟨hz', ?_⟩
      funext i
      have h1 := hact ⟨z, hz⟩ ⟨r * z * r⁻¹, hz'⟩ rfl i
      rw [coG_of_mem D ⟨r * z * r⁻¹, hz'⟩, coG_of_mem D ⟨z, hz⟩]
      exact h1
    · exact ⟨0, fun h => absurd h hr⟩
  choose ρ hρ using h
  exact ⟨ρ, fun r hr z hz => hρ r hr z hz⟩

theorem matrix_eq_of_actM_coG (hj : 0 < j) (D : StdData G T L I K m k n j)
    {B B' : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ z ∈ uZero I K, actM B (coG D z) = actM B' (coG D z)) : B = B' := by
  have hsum : B + B' = 0 := by
    apply eq_zero_of_actM_eq_zero hj
    intro Y
    obtain ⟨z, hz, rfl⟩ := exists_coG_eq D Y
    rw [actM_add_left, h z hz, tm_add_self]
  have hneg : B' = -B := by
    have := eq_neg_of_add_eq_zero_right hsum
    exact this
  rw [hneg]
  ext a b
  simp only [Matrix.neg_apply]
  have h2 : ∀ c : ZMod 2, -c = c := by decide
  exact (h2 _).symm

section Rho

variable {D : StdData G T L I K m k n j} {ρ : G → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem rho_mul_nsbfr (hj : 0 < j) (hρ : IsRho D ρ) {r₁ r₂ : G} (h₁ : r₁ ∈ pCoreOf 2 I)
    (h₂ : r₂ ∈ pCoreOf 2 I) : ρ (r₁ * r₂) = ρ r₁ * ρ r₂ := by
  apply matrix_eq_of_actM_coG hj D
  intro z hz
  obtain ⟨hz₂, hc₂⟩ := hρ r₂ h₂ z hz
  obtain ⟨hz₁, hc₁⟩ := hρ r₁ h₁ _ hz₂
  obtain ⟨hz₁₂, hc₁₂⟩ := hρ (r₁ * r₂) ((pCoreOf 2 I).mul_mem h₁ h₂) z hz
  have hconj : r₁ * r₂ * z * (r₁ * r₂)⁻¹ = r₁ * (r₂ * z * r₂⁻¹) * r₁⁻¹ := by group
  rw [hconj, hc₁, hc₂] at hc₁₂
  rw [actM_mul]
  exact hc₁₂.symm

theorem rho_eq_one_iff_nsbfr (hj : 0 < j) (hρ : IsRho D ρ) {r : G} (hr : r ∈ pCoreOf 2 I) :
    ρ r = 1 ↔ ∀ z ∈ uZero I K, r * z * r⁻¹ = z := by
  constructor
  · intro h1 z hz
    obtain ⟨hz', hc⟩ := hρ r hr z hz
    rw [h1, actM_one] at hc
    exact coG_injOn D hz' hz hc
  · intro hfix
    apply matrix_eq_of_actM_coG hj D
    intro z hz
    obtain ⟨hz', hc⟩ := hρ r hr z hz
    rw [actM_one]
    rw [hfix z hz] at hc
    exact hc.symm

theorem coG_comm_left (hρ : IsRho D ρ) {u r : G} (hu : u ∈ uZero I K) (hr : r ∈ pCoreOf 2 I) :
    u * r * u⁻¹ * r⁻¹ ∈ uZero I K ∧
      coG D (u * r * u⁻¹ * r⁻¹) = actM (ρ r + 1) (coG D u) := by
  have hu' : u⁻¹ ∈ uZero I K := Subgroup.inv_mem _ hu
  obtain ⟨hz, hc⟩ := hρ r hr u⁻¹ hu'
  have hform : u * r * u⁻¹ * r⁻¹ = u * (r * u⁻¹ * r⁻¹) := by group
  rw [hform]
  refine ⟨Subgroup.mul_mem _ hu hz, ?_⟩
  rw [coG_mul D hu hz, hc, coG_inv D hu, actM_add_left, actM_one, add_comm]

theorem coG_comm_right (hρ : IsRho D ρ) {v r : G} (hv : v ∈ uZero I K) (hr : r ∈ pCoreOf 2 I) :
    r * v * r⁻¹ * v⁻¹ ∈ uZero I K ∧
      coG D (r * v * r⁻¹ * v⁻¹) = actM (ρ r + 1) (coG D v) := by
  have hv' : v⁻¹ ∈ uZero I K := Subgroup.inv_mem _ hv
  obtain ⟨hz, hc⟩ := hρ r hr v hv
  refine ⟨Subgroup.mul_mem _ hz hv', ?_⟩
  rw [coG_mul D hz hv', hc, coG_inv D hv, actM_add_left, actM_one]

end Rho

noncomputable def zEn (D : StdData G T L I K m k n j) (Y : Fin j → Fin n → ZMod 2) : G :=
  Classical.choose (exists_coG_eq D Y)

theorem zEn_mem (D : StdData G T L I K m k n j) (Y : Fin j → Fin n → ZMod 2) :
    zEn D Y ∈ uZero I K :=
  (Classical.choose_spec (exists_coG_eq D Y)).1

theorem coG_zEn (D : StdData G T L I K m k n j) (Y : Fin j → Fin n → ZMod 2) :
    coG D (zEn D Y) = Y :=
  (Classical.choose_spec (exists_coG_eq D Y)).2

theorem zEn_coG (D : StdData G T L I K m k n j) {z : G} (hz : z ∈ uZero I K) :
    zEn D (coG D z) = z :=
  coG_injOn D (zEn_mem D _) hz (coG_zEn D _)

theorem zEn_add (D : StdData G T L I K m k n j) (Y Y' : Fin j → Fin n → ZMod 2) :
    zEn D (Y + Y') = zEn D Y * zEn D Y' := by
  apply coG_injOn D (zEn_mem D _) (Subgroup.mul_mem _ (zEn_mem D Y) (zEn_mem D Y'))
  rw [coG_zEn, coG_mul D (zEn_mem D Y) (zEn_mem D Y'), coG_zEn, coG_zEn]

end CFSG.Quasithin.H13.Ch4.NSB

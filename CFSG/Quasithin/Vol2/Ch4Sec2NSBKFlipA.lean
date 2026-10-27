module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKRF
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKTens

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k j : ℕ}

@[expose] noncomputable def wZ (D : StdData G T L I K m k (m + 1) j) (z : G) : Fin j → ZMod 2 :=
  fun i => coG D z i (Fin.last m)

theorem wZ_mul (D : StdData G T L I K m k (m + 1) j) {x y : G} (hx : x ∈ uZero I K)
    (hy : y ∈ uZero I K) : wZ D (x * y) = wZ D x + wZ D y := by
  funext i
  simp [wZ, coG_mul D hx hy]

theorem wZ_inv (D : StdData G T L I K m k (m + 1) j) {x : G} (hx : x ∈ uZero I K) :
    wZ D x⁻¹ = wZ D x := by
  funext i
  simp [wZ, coG_inv D hx]

theorem wZ_one (D : StdData G T L I K m k (m + 1) j) : wZ D 1 = 0 := by
  funext i
  simp [wZ, coG_one D]

variable (D : StdData G T L I K m k (m + 1) j) (hj : 0 < j)

theorem wZ_zZero : wZ D (zZero D hj) (⟨0, hj⟩ : Fin j) = 1 := by
  simp [wZ, coG_zZero D hj]

private theorem one_of_coG_zero_nsbkfa {c : G} (hc : c ∈ uZero I K) (h : coG D c = 0) : c = 1 :=
  coG_injOn D hc (one_mem _) (by rw [h, coG_one D])

theorem flip_identity (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) {u v : G} (hu : u ∈ uZero I K)
    (hv : v ∈ uZero I K) :
    (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹ ∈ uZero I K ∧
      coG D (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) =
        tens (arOf D hj (g⁻¹ * v * g)) (wZ D u)) ∧
    (g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ ∈ uZero I K ∧
      coG D (g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹) =
        tens (arOf D hj (g * u * g⁻¹)) (wZ D v)) := by
  have hr := h1 v hv
  have hr' := h2 u hu
  have hu' : u⁻¹ ∈ uZero I K := Subgroup.inv_mem _ hu
  have hv' : v⁻¹ ∈ uZero I K := Subgroup.inv_mem _ hv
  have hru : (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹ ∈ uZero I K := F.norm _ hr _ hu'
  have hrv : (g * u * g⁻¹) * v * (g * u * g⁻¹)⁻¹ ∈ uZero I K := F.norm _ hr' _ hv
  have hc : u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹ =
      u * ((g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) := by group
  have hc' : g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ =
      ((g * u * g⁻¹) * v * (g * u * g⁻¹)⁻¹) * v⁻¹ := by group
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hc]; exact Subgroup.mul_mem _ hu hru
  · rw [hc, coG_mul D hu hru]
    funext i b
    have h := (arOf_spec D hj F hr).2 u⁻¹ hu' i
    rw [coG_inv D hu] at h
    have hb := congrFun h b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tens_apply_apply, wZ] at hb ⊢
    rw [hb]
    generalize coG D u i b = x
    generalize coG D u i (Fin.last m) * arOf D hj (g⁻¹ * v * g) b = y
    revert x y
    decide
  · rw [hc']; exact Subgroup.mul_mem _ hrv hv'
  · rw [hc', coG_mul D hrv hv', coG_inv D hv]
    funext i b
    have h := (arOf_spec D hj F hr').2 v hv i
    have hb := congrFun h b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tens_apply_apply, wZ] at hb ⊢
    rw [hb]
    generalize coG D v i b = x
    generalize coG D v i (Fin.last m) * arOf D hj (g * u * g⁻¹) b = y
    revert x y
    decide

private theorem conj_eq_one_iff_nsbkfa {c g : G} : g * c * g⁻¹ = 1 ↔ c = 1 := by
  constructor
  · intro h
    have : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [this, h]
    group
  · intro h
    rw [h]
    group

theorem wZ_eq_zero_iff (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (hA' : ∃ u ∈ uZero I K, arOf D hj (g * u * g⁻¹) ≠ 0) {v : G} (hv : v ∈ uZero I K) :
    wZ D v = 0 ↔ arOf D hj (g⁻¹ * v * g) = 0 := by
  have hz0 := zZero_mem D hj
  constructor
  · intro hw
    obtain ⟨⟨hcZ, hcc⟩, ⟨hcZ', hcc'⟩⟩ := flip_identity D hj F h1 h2 hz0 hv
    have hc'1 := one_of_coG_zero_nsbkfa D hcZ' (by rw [hcc', hw]; exact tens_zero_right _)
    have hc1 := conj_eq_one_iff_nsbkfa.mp hc'1
    have h0 : coG D (zZero D hj * (g⁻¹ * v * g) * (zZero D hj)⁻¹ * (g⁻¹ * v * g)⁻¹) = 0 := by
      rw [hc1, coG_one D]
    rw [hcc] at h0
    have h := congrFun h0 ⟨0, hj⟩
    simpa [tens_apply, wZ_zZero D hj] using h
  · intro hAv
    have key : ∀ u ∈ uZero I K, tens (arOf D hj (g * u * g⁻¹)) (wZ D v) = 0 := by
      intro u hu
      obtain ⟨⟨hcZ, hcc⟩, ⟨hcZ', hcc'⟩⟩ := flip_identity D hj F h1 h2 hu hv
      have hc1 := one_of_coG_zero_nsbkfa D hcZ (by rw [hcc, hAv]; exact tens_zero_left _)
      rw [← hcc', hc1]
      simp [coG_one D]
    obtain ⟨u₀, hu₀, hne⟩ := hA'
    rcases (tens_eq_zero_iff _ _).mp (key u₀ hu₀) with h | h
    · exact absurd h hne
    · exact h

theorem wZ_eq_zero_iff' (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (hA : ∃ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) ≠ 0) {u : G} (hu : u ∈ uZero I K) :
    wZ D u = 0 ↔ arOf D hj (g * u * g⁻¹) = 0 := by
  have hz0 := zZero_mem D hj
  constructor
  · intro hw
    obtain ⟨⟨hcZ, hcc⟩, ⟨hcZ', hcc'⟩⟩ := flip_identity D hj F h1 h2 hu hz0
    have hc1 := one_of_coG_zero_nsbkfa D hcZ (by rw [hcc, hw]; exact tens_zero_right _)
    have h0 : coG D (g * (u * (g⁻¹ * zZero D hj * g) * u⁻¹ * (g⁻¹ * zZero D hj * g)⁻¹) * g⁻¹) = 0 := by
      rw [hc1]
      simp [coG_one D]
    rw [hcc'] at h0
    have h := congrFun h0 ⟨0, hj⟩
    simpa [tens_apply, wZ_zZero D hj] using h
  · intro hAu
    have key : ∀ v ∈ uZero I K, tens (arOf D hj (g⁻¹ * v * g)) (wZ D u) = 0 := by
      intro v hv
      obtain ⟨⟨hcZ, hcc⟩, ⟨hcZ', hcc'⟩⟩ := flip_identity D hj F h1 h2 hu hv
      have hc'1 := one_of_coG_zero_nsbkfa D hcZ' (by rw [hcc', hAu]; exact tens_zero_left _)
      have hc1 := conj_eq_one_iff_nsbkfa.mp hc'1
      rw [← hcc, hc1, coG_one D]
    obtain ⟨v₀, hv₀, hne⟩ := hA
    rcases (tens_eq_zero_iff _ _).mp (key v₀ hv₀) with h | h
    · exact absurd h hne
    · exact h

end CFSG.Quasithin.H13.Ch4.NSB

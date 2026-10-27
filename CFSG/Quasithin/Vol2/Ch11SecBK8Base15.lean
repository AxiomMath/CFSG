module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base10
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem le_dgSub_of_card_fixV [Finite K] {A : Subgroup (MulAut (W6 K))} (hA : A ≤ normD K)
    (h : Nat.card K ^ 3 < Nat.card ↥(fixV A)) : A ≤ dgSub K := by
  intro y hy
  have hle : fixV A ≤ fixV (Subgroup.zpowers y) := fun v hv x hx =>
    hv x ((Subgroup.zpowers_le.mpr hy) hx)
  have h1 : Nat.card K ^ 3 < Nat.card (FixW y) := by
    rw [← card_fixV_zpowers]
    exact lt_of_lt_of_le h (Subgroup.card_le_of_le hle)
  obtain ⟨A₀, rfl⟩ := exists_dg_of_lt_card_fix (hA hy) h1
  exact matAut_dgHom_mem_dgSub A₀

theorem exists_ne_zero_ne_one [Finite K] (h : 2 < Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra hc
  push Not at hc
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := by
    intro c _
    by_cases h0 : c = 0
    · exact Or.inl h0
    · exact Or.inr (hc c h0)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 := Set.ncard_insert_le (0 : K) {1}
  rw [Set.ncard_singleton] at h2
  omega

theorem exists_mem_ker_ne_zero [Finite K] (f : (Fin 3 → K) →ₗ[K] K) :
    ∃ w, f w = 0 ∧ w ≠ 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have h3 : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  exact ⟨w, hw, hw0⟩

variable {G : Type} [Group G] {W : Subgroup G} {hW : IsElemAbelian 2 W}

theorem comap_psi_self (Φ : IntMod W hW ≃* W6 K) : W.comap (psi Φ) = ⊤ :=
  eq_top_iff.mpr fun v _ => psi_mem Φ v

theorem comap_psi_zpowers (Φ : IntMod W hW ≃* W6 K) (a : W6 K) :
    (Subgroup.zpowers (psi Φ a)).comap (psi Φ) = Subgroup.zpowers a := by
  rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq_self_of_injective (psi_injective Φ)]

theorem mQuot_bot_map_psi (Φ : IntMod W hW ≃* W6 K) (N : Subgroup (W6 K)) :
    E3.mQuot (N.map (psi Φ)) ⊥ = padicValNat 2 (Nat.card ↥N) := by
  rw [E3.mQuot, Subgroup.relIndex_bot_left, Subgroup.card_map_of_injective (psi_injective Φ)]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8

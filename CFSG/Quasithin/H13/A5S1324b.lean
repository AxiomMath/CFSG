module

public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.Background.B2FactorizationBaumann

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem InV4_of_D_inv_fixW2 : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ * σ = 1 → FixW2 σ →
    InV4 σ := by
  decide +kernel

theorem pb_conj_swaps : pb * Equiv.swap 0 1 * pb⁻¹ = Equiv.swap 2 3 ∧
    pb * Equiv.swap 2 3 * pb⁻¹ = Equiv.swap 0 1 := by
  decide

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem rho_InV4_of_isMaxElemAbelian {A : Subgroup G} (hA : IsMaxElemAbelian T A) {a : G}
    (ha : a ∈ A) : InV4 (S.frame.ρ ⟨a, S.frame.T_le (hA.1 ha)⟩) := by
  have hp := S.rho_props_of_isMaxElemAbelian hA ha ha
  have hfix := (S.mem_centralizer_V2_iff ⟨a, S.frame.T_le (hA.1 ha)⟩).1
    (S.le_centralizer_V2_of_isMaxElemAbelian hA ha)
  exact InV4_of_D_inv_fixW2 _ hp.1 hp.2.1 hfix

theorem exists_swap_of_isMaxElemAbelian {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    ∃ a ∈ A, ∃ h : a ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨a, h⟩ = Equiv.swap 0 1 ∨ S.frame.ρ ⟨a, h⟩ = Equiv.swap 2 3 := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans S.frame.T_le
  by_contra hne
  push Not at hne
  have hval : ∀ b (hb : b ∈ A), S.frame.ρ ⟨b, hAN hb⟩ = 1 ∨ S.frame.ρ ⟨b, hAN hb⟩ = pa := by
    intro b hb
    rcases S.rho_InV4_of_isMaxElemAbelian hA hb with h | h | h | h
    · exact Or.inl h
    · exact absurd h (hne b hb (hAN hb)).1
    · exact absurd h (hne b hb (hAN hb)).2
    · exact Or.inr h
  obtain ⟨a, haA, ha⟩ := IsConcreteLE.not_le_iff_exists.1 hAV
  have hra : S.frame.ρ ⟨a, hAN haA⟩ = pa := by
    rcases hval a haA with h | h
    · exact absurd (S.frame.mem_centralizer_of_rho _ h) ha
    · exact h
  have hff := card_mul_le_of_isMaxElemAbelian S.elemAbelian_V S.V_le_T hA
  rw [S.card_V] at hff
  set f := S.frame.ρ.comp (Subgroup.inclusion hAN)
  have hfker := S.ker_rho_restrict hAN
  have hfval : ∀ b : ↥A, f b = S.frame.ρ ⟨(b : G), hAN b.2⟩ := fun _ => rfl
  have hA2 := card_le_of_range_subset inf_le_left f hfker {σ | σ = 1 ∨ σ = pa}
    fun c => by rw [hfval]; exact hval c c.2
  have hX2 : Nat.card ({σ | σ = 1 ∨ σ = pa} : Set (Equiv.Perm (Fin 5))) ≤ 2 := by
    have : ({σ | σ = 1 ∨ σ = pa} : Set (Equiv.Perm (Fin 5))) = {1, pa} := by
      ext σ; simp
    rw [this, Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hCV : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
    rw [← card_fix_K4 pa (Or.inr (Or.inl rfl)) (by decide), ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun v => ⟨S.frame.ψ ⟨v, v.2.1⟩, ?_⟩) ?_
    · rw [← hra]
      refine (S.conj_eq_iff ⟨a, hAN haA⟩ ⟨v, v.2.1⟩).1 ?_
      have := Subgroup.mem_centralizer_iff.mp v.2.2 a haA
      show a * (v : G) * a⁻¹ = v
      rw [this]; group
    · intro v w hvw
      have h1 := S.frame.ψ.injective (congrArg Subtype.val hvw)
      exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) h1)
  have : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
        ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hff
      _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 4 :=
        Nat.mul_le_mul (hA2.trans (Nat.mul_le_mul_right _ hX2)) hCV
      _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
  have hKpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  omega

theorem lemma_13_2_4_two_b (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    (∃ j ∈ thompsonJ T, ∃ h : j ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨j, h⟩ = Equiv.swap 0 1) ∧
    (∃ j ∈ thompsonJ T, ∃ h : j ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨j, h⟩ = Equiv.swap 2 3) := by
  obtain ⟨A, hA, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hJ (iSup₂_le fun A hA => h A hA)
  obtain ⟨a, haA, haN, hsw⟩ := S.exists_swap_of_isMaxElemAbelian hA hAV
  have hajJ : a ∈ thompsonJ T := (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T) haA
  obtain ⟨g₀, hg₀T, hg₀σ⟩ := S.frame.K4_T pb (Or.inr (Or.inr (Or.inl rfl)))
  have hconjJ : (g₀ : G) * a * (g₀ : G)⁻¹ ∈ thompsonJ T :=
    (Subgroup.mem_normalizer_iff.mp (B2F.R_le_normalizer_thompsonJ T hg₀T) a).mp hajJ
  have hconjN : (g₀ : G) * a * (g₀ : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ g₀.2 haN) (Subgroup.inv_mem _ g₀.2)
  have hρ : S.frame.ρ ⟨(g₀ : G) * a * (g₀ : G)⁻¹, hconjN⟩ =
      pb * S.frame.ρ ⟨a, haN⟩ * pb⁻¹ := by
    have e : (⟨(g₀ : G) * a * (g₀ : G)⁻¹, hconjN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        g₀ * ⟨a, haN⟩ * g₀⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hg₀σ]
  rcases hsw with h | h
  · exact ⟨⟨a, hajJ, haN, h⟩, ⟨_, hconjJ, hconjN, by rw [hρ, h]; exact pb_conj_swaps.1⟩⟩
  · exact ⟨⟨_, hconjJ, hconjN, by rw [hρ, h]; exact pb_conj_swaps.2⟩, ⟨a, hajJ, haN, h⟩⟩

end Setting

end CFSG.Quasithin.H13.A5

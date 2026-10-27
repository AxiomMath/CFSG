module

public import CFSG.Quasithin.Background.RonanE111Wr

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem wr_pPower_finset {p : ℕ} {Y' : Subgroup G} (s : Finset (Subgroup G))
    (hp : ∀ V ∈ s, ∀ x ∈ V, ∃ k : ℕ, x ^ p ^ k ∈ Y')
    (hcomm : ∀ V ∈ s, ∀ V' ∈ s, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x) :
    ∀ x ∈ sSup (s : Set (Subgroup G)), ∃ k : ℕ, x ^ p ^ k ∈ Y' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    rw [Finset.coe_empty, sSup_empty, Subgroup.mem_bot] at hx
    exact ⟨0, by rw [hx]; simp⟩
  | insert a s ha ih =>
    have hp' : ∀ V ∈ s, ∀ x ∈ V, ∃ k : ℕ, x ^ p ^ k ∈ Y' := fun V hV =>
      hp V (Finset.mem_insert_of_mem hV)
    have hcomm' : ∀ V ∈ s, ∀ V' ∈ s, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x :=
      fun V hV V' hV' hne =>
        hcomm V (Finset.mem_insert_of_mem hV) V' (Finset.mem_insert_of_mem hV') hne
    have ih' := ih hp' hcomm'
    rw [Finset.coe_insert, sSup_insert]
    have hcen : ∀ u ∈ a, ∀ w ∈ sSup (s : Set (Subgroup G)), u * w = w * u := by
      intro u hu w hw
      have hcent : sSup (s : Set (Subgroup G)) ≤ Subgroup.centralizer ({u} : Set G) := by
        refine sSup_le fun V hV y hy => ?_
        have hVs : V ∈ s := by exact_mod_cast hV
        have hne : a ≠ V := fun e => ha (e ▸ hVs)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hcomm a (Finset.mem_insert_self a s) V (Finset.mem_insert_of_mem hVs) hne u hu y hy
      exact Subgroup.mem_centralizer_iff.mp (hcent hw) u (Set.mem_singleton _)
    intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := wr_mem_sup (H := a) (K := sSup (s : Set (Subgroup G)))
      (fun h hh k hk => by
        have := hcen h hh k hk
        have e : h * k * h⁻¹ = k := by rw [this]; group
        rw [e]; exact hk) hx
    obtain ⟨k₁, hk₁⟩ := hp a (Finset.mem_insert_self a s) u hu
    obtain ⟨k₂, hk₂⟩ := ih' w hw
    refine ⟨k₁ + k₂, ?_⟩
    have hc : Commute u w := hcen u hu w hw
    rw [hc.mul_pow]
    have h1 : u ^ p ^ (k₁ + k₂) ∈ Y' := by
      have : u ^ p ^ (k₁ + k₂) = (u ^ p ^ k₁) ^ p ^ k₂ := by rw [← pow_mul, ← pow_add]
      rw [this]; exact Y'.pow_mem hk₁ _
    have h2 : w ^ p ^ (k₁ + k₂) ∈ Y' := by
      have : w ^ p ^ (k₁ + k₂) = (w ^ p ^ k₂) ^ p ^ k₁ := by
        rw [← pow_mul, ← pow_add, add_comm]
      rw [this]; exact Y'.pow_mem hk₂ _
    exact Y'.mul_mem h1 h2

section Application

variable {X T A J C : Subgroup G} [Fintype ↥C]

theorem wrP_pgroup (h : DiagSetting X T A J C) {p : ℕ} {R YR : Subgroup G} (hRJ : R ≤ J)
    (hRE : ∀ e ∈ actE T A J, A1b.conjSub e R = R)
    (hpq : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ YR) :
    ∀ x ∈ wrN h.diagComm T A R, ∃ k : ℕ, x ^ p ^ k ∈ wrY h.diagComm T A YR := by
  classical
  set 𝒱 : Set (Subgroup G) :=
    {V | ∃ k ∈ actT T A, V = A1b.conjSub k (dimg h.diagComm R)} with h𝒱
  have hfin : 𝒱.Finite := Set.toFinite 𝒱
  have hsup : sSup 𝒱 = wrN h.diagComm T A R := by
    rw [wrN_eq]
    apply le_antisymm
    · refine sSup_le fun V hV => ?_
      obtain ⟨k, hk, rfl⟩ := hV
      exact le_iSup₂_of_le (f := fun k (_ : k ∈ actT T A) => A1b.conjSub k (dimg h.diagComm R))
        k hk le_rfl
    · exact iSup₂_le fun k hk => le_sSup ⟨k, hk, rfl⟩
  have hp : ∀ V ∈ 𝒱, ∀ x ∈ V, ∃ m : ℕ, x ^ p ^ m ∈ wrY h.diagComm T A YR := by
    rintro V ⟨k, hk, rfl⟩ x hx
    rw [A1b.mem_conjSub_iff] at hx
    obtain ⟨u, hu, hux⟩ := (mem_dimg_iff h.diagComm).mp hx
    obtain ⟨m, hm⟩ := hpq (u : G) hu
    refine ⟨m, ?_⟩
    have h1 : (k⁻¹ * x * k) ^ p ^ m ∈ dimg h.diagComm YR := by
      rw [← hux, ← map_pow]
      exact (mem_dimg_iff h.diagComm).mpr ⟨u ^ p ^ m, by simpa using hm, rfl⟩
    have hconj : (k⁻¹ * x * k) ^ p ^ m = k⁻¹ * x ^ p ^ m * k := by
      have := map_pow (MulAut.conj k⁻¹) x (p ^ m)
      simpa [MulAut.conj_apply] using this.symm
    have h2 : x ^ p ^ m ∈ A1b.conjSub k (dimg h.diagComm YR) := by
      rw [A1b.mem_conjSub_iff, ← hconj]
      exact h1
    have h3 : A1b.conjSub k (dimg h.diagComm YR) ≤ wrY h.diagComm T A YR := by
      calc A1b.conjSub k (dimg h.diagComm YR) ≤ A1b.conjSub k (wrY h.diagComm T A YR) :=
            A1b.conjSub_mono k (wr_dimg_le_wrY h)
        _ = wrY h.diagComm T A YR := wr_conjSub_wrY h hk
    exact h3 h2
  have hcomm : ∀ V ∈ 𝒱, ∀ V' ∈ 𝒱, V ≠ V' → ∀ x ∈ V, ∀ y ∈ V', x * y = y * x := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ hne x hx y hy
    by_cases hblock : A1b.conjSub k (diagSub J C h.diagComm) =
        A1b.conjSub k' (diagSub J C h.diagComm)
    · exact absurd (wr_same_block_dimg h hRJ hRE hk hk' hblock) hne
    · exact wr_block_comm h hk hk' hblock x
        (A1b.conjSub_mono k (dimg_le_diagSub h hRJ) hx) y
        (A1b.conjSub_mono k' (dimg_le_diagSub h hRJ) hy)
  intro x hx
  rw [← hsup] at hx
  have hfin' : (hfin.toFinset : Set (Subgroup G)) = 𝒱 := hfin.coe_toFinset
  rw [← hfin'] at hx
  exact wr_pPower_finset hfin.toFinset
    (fun V hV => hp V ((Set.Finite.mem_toFinset hfin).mp hV))
    (fun V hV V' hV' hne => hcomm V ((Set.Finite.mem_toFinset hfin).mp hV) V'
      ((Set.Finite.mem_toFinset hfin).mp hV') hne) x hx

end Application

end CFSG.Quasithin.RonanE111

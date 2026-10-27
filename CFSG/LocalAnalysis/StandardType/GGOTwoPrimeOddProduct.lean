module

public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.StandardType

theorem ggOTwoPrime_sup_of_isPGroup_odd {G : Type*} [Group G] {p : ℕ}
    {F R : Subgroup G} (hp : Odd p) (hF : IsPGroup p F)
    (hFR : F ≤ Subgroup.centralizer (R : Set G)) (hdis : F ⊓ R = ⊥) :
    ggOTwoPrime (F ⊔ R) = ggOTwoPrime R := by
  apply le_antisymm
  · change Subgroup.closure {x : G | x ∈ F ⊔ R ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} ≤ _
    rw [Subgroup.closure_le]
    rintro x ⟨hx, k, hxk⟩
    have hFN : F ≤ Subgroup.normalizer (R : Set G) :=
      hFR.trans (Subgroup.centralizer_le_normalizer _)
    rw [sup_comm] at hx
    obtain ⟨r, hr, f, hf, rfl⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hFN).mp hx
    have hrf : Commute r f := Subgroup.mem_centralizer_iff.mp (hFR hf) r hr
    have he : r ^ (2 ^ k) * f ^ (2 ^ k) = 1 := by
      simpa only [hrf.mul_pow] using hxk
    have hfR : f ^ (2 ^ k) = (r ^ (2 ^ k))⁻¹ := by
      calc
        f ^ (2 ^ k) = (r ^ (2 ^ k))⁻¹ * (r ^ (2 ^ k) * f ^ (2 ^ k)) := by group
        _ = (r ^ (2 ^ k))⁻¹ := by rw [he, mul_one]
    have hf2 : f ^ (2 ^ k) = 1 := by
      have hmem : f ^ (2 ^ k) ∈ F ⊓ R :=
        ⟨F.pow_mem hf _, by rw [hfR]; exact R.inv_mem (R.pow_mem hr _)⟩
      rwa [hdis, Subgroup.mem_bot] at hmem
    obtain ⟨m, hm⟩ := hF ⟨f, hf⟩
    have hfp : f ^ (p ^ m) = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hm
    have hcop : (p ^ m).Coprime (2 ^ k) :=
      Nat.Coprime.pow m k (Nat.coprime_two_right.mpr hp)
    have hf1 : f = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hfp, hf2⟩
    rw [hf1, mul_one]
    exact Subgroup.subset_closure ⟨hr, k, by simpa only [hf1, mul_one] using hxk⟩
  · change Subgroup.closure _ ≤ Subgroup.closure _
    exact Subgroup.closure_mono fun x hx =>
      ⟨(show R ≤ F ⊔ R from le_sup_right) hx.1, hx.2⟩

theorem ggOTwoPrime_perm_eq_top {α : Type*} [Finite α] :
    ggOTwoPrime (⊤ : Subgroup (Equiv.Perm α)) = ⊤ := by
  classical
  have hgen : Subgroup.closure {σ : Equiv.Perm α | σ.IsSwap} ≤
      ggOTwoPrime (⊤ : Subgroup (Equiv.Perm α)) := by
    rw [Subgroup.closure_le]
    rintro σ ⟨a, b, -, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, 1, ?_⟩
    simpa only [pow_one, pow_two] using Equiv.swap_mul_self a b
  exact top_unique (by simpa only [Equiv.Perm.closure_isSwap] using hgen)

theorem ggOTwoPrime_eq_self_of_equiv_perm {G : Type} [Group G] {R : Subgroup G}
    {α : Type} [Finite α] (e : R ≃* Equiv.Perm α) : ggOTwoPrime R = R := by
  have htop : ggOTwoPrime (⊤ : Subgroup R) = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [ggOTwoPrime_top_map_mulEquiv e, ggOTwoPrime_perm_eq_top,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← ggOTwoPrime_top_map_subtype, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end CFSG.StandardType

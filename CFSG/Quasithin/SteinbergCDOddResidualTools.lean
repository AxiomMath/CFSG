module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup

variable {E : Type*} [Group E]

theorem exists_two_pow_mem_of_sup_eq_top {X T : Subgroup E} [X.Normal] (hT : IsPGroup 2 T)
    (hXT : X ⊔ T = ⊤) (g : E) : ∃ k : ℕ, g ^ 2 ^ k ∈ X := by
  have hg : g ∈ ((X ⊔ T : Subgroup E) : Set E) := by
    rw [hXT]
    exact mem_top g
  rw [normal_mul] at hg
  obtain ⟨x, hx, t, ht, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨k, ?_⟩
  have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff x).mpr hx, one_mul, ← QuotientGroup.mk_pow, htk,
    QuotientGroup.mk_one]

theorem exists_index_eq_two_pow_of_sup_eq_top [Finite E] {X T : Subgroup E} [X.Normal]
    (hT : IsPGroup 2 T) (hXT : X ⊔ T = ⊤) : ∃ a : ℕ, X.index = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (E ⧸ X) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hT hXT g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  exact IsPGroup.iff_card.mp h2

theorem le_of_inf_le_of_le_of_index_eq_two_pow {K X S H : Subgroup E} [X.Normal] {a : ℕ}
    (hX : X.index = 2 ^ a) (hS : ¬ 2 ∣ S.relIndex K) (hXH : X ⊓ K ≤ H) (hSH : S ≤ H) :
    K ≤ H := by
  have h1 : H.relIndex K ∣ 2 ^ a := by
    rw [← hX]
    refine (relIndex_dvd_of_le_left K hXH).trans ?_
    rw [inf_relIndex_right]
    exact relIndex_dvd_index_of_normal X K
  have h2 : H.relIndex K ∣ S.relIndex K := relIndex_dvd_of_le_left K hSH
  have hcop : Nat.Coprime (2 ^ a) (S.relIndex K) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS)
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem isCoatom_map_of_surjective_of_ker_le {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {M : Subgroup G} (hM : IsCoatom M) (hkM : f.ker ≤ M) :
    IsCoatom (M.map f) := by
  have hcm : (M.map f).comap f = M := by rw [comap_map_eq, sup_eq_left.mpr hkM]
  refine ⟨fun h => hM.1 ?_, fun K hK => ?_⟩
  · rw [← hcm, h, comap_top]
  · have h1 : M < K.comap f := by
      rw [← hcm]
      exact (comap_lt_comap_of_surjective hf).mpr hK
    rw [← map_comap_eq_self_of_surjective hf K, hM.2 _ h1, map_top_of_surjective _ hf]

theorem map_frattini_eq_of_ker_le_frattini {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) (hker : f.ker ≤ frattini G) :
    (frattini G).map f = frattini H := by
  refine le_antisymm (map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective hf)) ?_
  intro h hh
  obtain ⟨g, rfl⟩ := hf h
  refine mem_map_of_mem f ?_
  change g ∈ Order.radical (Subgroup G)
  simp only [Order.radical, mem_iInf]
  intro M hM
  have hkM : f.ker ≤ M := hker.trans (frattini_le_coatom hM)
  have h1 : f g ∈ M.map f := frattini_le_coatom (isCoatom_map_of_surjective_of_ker_le hf hM hkM) hh
  have h2 : g ∈ (M.map f).comap f := h1
  rwa [comap_map_eq, sup_eq_left.mpr hkM] at h2

theorem exists_frattini_quotient_equiv {G : Type*} [Group G] [Finite G] {N M : Subgroup G}
    [N.Normal] [M.Normal] (hNM : N ≤ M)
    (hM : M.map (QuotientGroup.mk' N) ≤ frattini (G ⧸ N)) :
    ∃ μ : (G ⧸ M) ⧸ frattini (G ⧸ M) ≃* (G ⧸ N) ⧸ frattini (G ⧸ N), ∀ x : G,
      μ ((x : G ⧸ M) : (G ⧸ M) ⧸ frattini (G ⧸ M)) =
        ((x : G ⧸ N) : (G ⧸ N) ⧸ frattini (G ⧸ N)) := by
  set g : G ⧸ N →* G ⧸ M := QuotientGroup.map N M (MonoidHom.id G) hNM with hg
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, rfl⟩
  have hgk : g.ker = M.map (QuotientGroup.mk' N) := by
    have h := QuotientGroup.ker_map N M (MonoidHom.id G) hNM
    rw [comap_id] at h
    exact h
  have hΦ : (frattini (G ⧸ N)).map g = frattini (G ⧸ M) :=
    map_frattini_eq_of_ker_le_frattini hgs (hgk ▸ hM)
  set π : G →* (G ⧸ M) ⧸ frattini (G ⧸ M) :=
    (QuotientGroup.mk' (frattini (G ⧸ M))).comp (QuotientGroup.mk' M) with hπ
  set ψ : G →* (G ⧸ N) ⧸ frattini (G ⧸ N) :=
    (QuotientGroup.mk' (frattini (G ⧸ N))).comp (QuotientGroup.mk' N) with hψ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hgN : QuotientGroup.mk' M = g.comp (QuotientGroup.mk' N) := by
    ext x
    rfl
  have hker : π.ker = ψ.ker := by
    rw [hπ, hψ, ← MonoidHom.comap_ker, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      QuotientGroup.ker_mk', ← hΦ, hgN, ← comap_comap, comap_map_eq,
      sup_eq_left.mpr (hgk ▸ hM)]
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)), fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm
      ((x : G ⧸ M) : (G ⧸ M) ⧸ frattini (G ⧸ M)) = (x : G ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, h1]
  rfl

end CFSG.Quasithin.SteinbergCD

module

public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Q9

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le [Finite G] {K : Subgroup G} {t : G}
    (h : ∀ k ∈ K, t * k * t⁻¹ ∈ K) : t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  let φ : K → K := fun k => ⟨t * k * t⁻¹, h k k.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only [φ] at h1
    exact Subtype.ext (by simpa using h1)
  obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.mp hinj ⟨t * x * t⁻¹, hx⟩
  have h1 := congrArg Subtype.val hk
  simp only [φ] at h1
  have h2 : (k : G) = x := by simpa using h1
  rw [← h2]
  exact k.2

theorem covBy_map_conj {A B : Subgroup G} (g : G) (h : A ⋖ B) :
    A.map (MulAut.conj g).toMonoidHom ⋖ B.map (MulAut.conj g).toMonoidHom :=
  (apply_covBy_apply_iff (MulAut.conj g).mapSubgroup).mpr h

theorem conj_eq_or_eq_of_covBy {K U P P' : Subgroup G}
    (hcov : ∀ A : Subgroup G, U ≤ A → A ≤ K → (A ⋖ K ↔ A = P ∨ A = P'))
    (hUP : U ≤ P) (hPK : P ≤ K) {x : G} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    P.map (MulAut.conj x).toMonoidHom = P ∨ P.map (MulAut.conj x).toMonoidHom = P' := by
  have hPcov : P ⋖ K := (hcov P hUP hPK).mpr (Or.inl rfl)
  have hK : K.map (MulAut.conj x).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxK
  have hU : U.map (MulAut.conj x).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxU
  have hcov' : P.map (MulAut.conj x).toMonoidHom ⋖ K := by
    have := covBy_map_conj x hPcov
    rwa [hK] at this
  refine (hcov _ ?_ ?_).mp hcov'
  · rw [← hU]
    exact Subgroup.map_mono hUP
  · rw [← hK]
    exact Subgroup.map_mono hPK

theorem eq_of_isSylowTwoOf_of_le [Finite G] {A B K : Subgroup G} (hA : IsSylowTwoOf A K)
    (hB : IsSylowTwoOf B K) (hAB : A ≤ B) : A = B :=
  le_antisymm hAB ((A4.isSylowTwoOf_iff_maximal.mp hA).2.2 B hB.1 hB.2.1 hAB)

theorem exists_swap_of_sylow [Finite G] {N T T1 K U P P' : Subgroup G}
    (hT : IsSylowTwoOf T N) (hT1 : IsSylowTwoOf T1 N)
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hNU : N ≤ Subgroup.normalizer (U : Set G))
    (hcov : ∀ A : Subgroup G, U ≤ A → A ≤ K → (A ⋖ K ↔ A = P ∨ A = P'))
    (hUP : U ≤ P) (hPK : P ≤ K) (hTP : ¬ T ≤ Subgroup.normalizer (P : Set G))
    (hTP' : ¬ T ≤ Subgroup.normalizer (P' : Set G)) :
    ∃ r ∈ T1, P.map (MulAut.conj r).toMonoidHom = P' := by
  obtain ⟨g, hgN, hg⟩ := A4.exists_conj_of_isSylowTwoOf hT hT1
  by_contra hcon
  push Not at hcon
  have hT1P : T1 ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    rcases conj_eq_or_eq_of_covBy hcov hUP hPK (hNK (hT1.1 hr)) (hNU (hT1.1 hr)) with h | h
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    · exact absurd h (hcon r hr)
  have hgi : g⁻¹ ∈ N := N.inv_mem hgN
  have hPg := conj_eq_or_eq_of_covBy hcov hUP hPK (hNK hgi) (hNU hgi)
  have hTPg : T ≤ Subgroup.normalizer
      ((P.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    intro t ht
    have h1 : g * t * g⁻¹ ∈ T1 := by
      refine (hg _).mpr ?_
      have : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [this]
      exact ht
    have h2 := Subgroup.mem_normalizer_iff.mp (hT1P h1)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [A38.mem_map_conj, inv_inv]
    have h3 := h2 (g * y * g⁻¹)
    have h4 : g * t * g⁻¹ * (g * y * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * y * t⁻¹) * g⁻¹ := by
      group
    rw [h4] at h3
    exact h3
  rcases hPg with h | h
  · rw [h] at hTPg
    exact hTP hTPg
  · rw [h] at hTPg
    exact hTP' hTPg

theorem conjClosure_eq_of_cComp [Finite G] {H K K1 T : Subgroup G} (hK : K ∈ cComp H)
    (hHeq : H = K1 ⊔ T) (hK1K : K1 ≤ K) (hK1ne : K1 ≠ ⊥) (hK1perf : ⁅K1, K1⁆ = K1)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : conjClosure K1 T = K := by
  set Y := conjClosure K1 T with hY
  have hYK : Y ≤ K := conjClosure_le fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTK hh) z).mp (hK1K hz)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hYH : Y ≤ H := hYK.trans hKH
  have hYne : Y ≠ ⊥ := fun h => hK1ne (le_bot_iff.mp ((le_conjClosure K1 T).trans h.le))
  have hYperf : ⁅Y, Y⁆ = Y := by
    refine le_antisymm (A3.commutator_self_le Y) (conjClosure_le fun h hh z hz => ?_)
    have hz' : z ∈ ⁅K1, K1⁆ := by
      rw [hK1perf]
      exact hz
    have hmap : K1.map (MulAut.conj h).toMonoidHom ≤ Y := by
      rintro x ⟨z', hz'', rfl⟩
      exact mem_conjClosure hh hz''
    have hmem : h * z * h⁻¹ ∈ ⁅K1.map (MulAut.conj h).toMonoidHom,
        K1.map (MulAut.conj h).toMonoidHom⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map.mpr ⟨z, hz', by simp [MulAut.conj_apply]⟩
    exact Subgroup.commutator_mono hmap hmap hmem
  have hnormH : H ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hHeq]
    exact sup_le (le_trans (le_conjClosure K1 T) Subgroup.le_normalizer)
      (le_normalizer_conjClosure K1 T)
  have hsub : IsSubnormal Y H :=
    A3.subnormal_of_normal hYH ((Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hnormH)
  by_contra hne
  exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hYK hne) hYne hYperf hsub

end Q9

end CFSG.Quasithin

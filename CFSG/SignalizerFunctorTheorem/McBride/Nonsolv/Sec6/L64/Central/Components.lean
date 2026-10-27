module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem map_conj_map_conj (J : Subgroup G) (x y : G) :
    (J.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      J.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj (1 : G)).toMonoidHom = J := by
  ext x
  simp

theorem commutator_eq_self_of_mem_simpleComponents {K J : Subgroup G}
    (hJ : J ∈ simpleComponents K) : ⁅J, J⁆ = J := by
  have := hJ.2.2.1
  exact commutator_self_eq_of_isSimpleGroup hJ.2.2.2

theorem map_conj_mem_simpleComponents {K J : Subgroup G} (hJ : J ∈ simpleComponents K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    J.map (MulAut.conj g).toMonoidHom ∈ simpleComponents K := by
  obtain ⟨hJK, hJn, hJs, x₀, hx₀, y₀, hy₀, hxy₀⟩ := hJ
  have hconj : ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hconj' : ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun k hk => by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
  have hle : J.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨j, hj, rfl⟩
    exact hconj j (hJK hj)
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ k ⟨j, hj, rfl⟩ hk
    have hjk := (Subgroup.normal_subgroupOf_iff hJK).mp hJn j (g⁻¹ * k * g) hj (hconj' k hk)
    refine ⟨_, hjk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have := hJs
    exact (Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.isSimpleGroup
  · refine ⟨_, ⟨x₀, hx₀, rfl⟩, _, ⟨y₀, hy₀, rfl⟩, fun h => hxy₀ ?_⟩
    have := (MulAut.conj g).injective (by simpa [← map_mul] using h)
    exact (by simpa using this : x₀ * y₀ = y₀ * x₀)

theorem iSupIndep_simpleComponents [Finite G] {A K : Subgroup G} (hK : IsASimple A K) :
    iSupIndep (fun J : simpleComponents K => (J : Subgroup G)) := by
  intro J
  refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
  obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
  have hS : (⨆ (J' : simpleComponents K) (_ : J' ≠ J), (J' : Subgroup G)) ≤
      Subgroup.centralizer ((J : Subgroup G) : Set G) :=
    iSup₂_le fun J' hJ' =>
      (hK.components_commute J'.2 J.2 (fun h => hJ' (Subtype.ext h))).1
  have hJs : IsSimpleGroup (J : Subgroup G) := J.2.2.2.1
  set N : Subgroup G := (J : Subgroup G) ⊓ ⨆ (J' : simpleComponents K) (_ : J' ≠ J),
    (J' : Subgroup G) with hN
  have hNJ : N ≤ (J : Subgroup G) := inf_le_left
  have hNc : ∀ n ∈ N, ∀ g ∈ (J : Subgroup G), g * n = n * g := fun n hn g hg =>
    Subgroup.mem_centralizer_iff.mp (hS (Subgroup.mem_inf.mp hn).2) g hg
  have hNn : (N.subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNJ]
    intro n k hn hk
    rw [mul_inv_eq_iff_eq_mul.mpr (hNc n hn k hk)]
    exact hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with h | h
  · have hx' : (⟨x, hxJ⟩ : (J : Subgroup G)) ∈ N.subgroupOf J := Subgroup.mem_inf.mpr ⟨hxJ, hxS⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := J.2.2.2.2
    have hx₀N : x₀ ∈ N := by
      have : (⟨x₀, hx₀⟩ : (J : Subgroup G)) ∈ N.subgroupOf J := by rw [h]; trivial
      exact this
    exact hxy₀ (hNc x₀ hx₀N y₀ hy₀).symm

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

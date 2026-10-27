module

public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.SeitzGeneration

theorem exists_mem_normalizer_conj_of_commutative_sylow {R : Type} [Group R] [Finite R] {p : ℕ}
    (P : Sylow p R) (hP : IsMulCommutative (P : Subgroup R)) {x y g : R}
    (hx : x ∈ (P : Subgroup R)) (hy : y ∈ (P : Subgroup R)) (hg : g * x * g⁻¹ = y)
    (hp : p.Prime := by assumption) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup R) : Set R), n * x * n⁻¹ = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  have hy' : g⁻¹⁻¹ * x * g⁻¹ ∈ (P : Subgroup R) := by rwa [inv_inv, hg]
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem x g⁻¹ hx hy'
  refine ⟨n⁻¹, Subgroup.inv_mem _ hn, ?_⟩
  rw [inv_inv] at h ⊢
  rw [← hg, h]

theorem isPGroup_of_isElemAbelian_frame {R : Type} [Group R] {p : ℕ} {E : Subgroup R}
    (hE : IsElemAbelian p E) : IsPGroup p E := fun g =>
  ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem exists_sylow_of_sylowTorus_elemAbelian {R : Type} [Group R] [Finite R] {p N : ℕ}
    (hp : p.Prime) (hT : SylowTorus R p N) {E : Subgroup R} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ N) :
    ∃ P : Sylow p R, E ≤ (P : Subgroup R) ∧ IsMulCommutative (P : Subgroup R) ∧
      ∀ x ∈ (P : Subgroup R), x ^ p = 1 → x ∈ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP⟩ := (isPGroup_of_isElemAbelian_frame hE).exists_le_sylow
  obtain ⟨T, E₀, hTc, hconj, -, -, -, -⟩ := hT.exists_torus
  obtain ⟨g, hg⟩ := hconj (P : Subgroup R) P.isPGroup'
  have hPc : IsMulCommutative (P : Subgroup R) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 (hg a.2)
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hg b.2)
    apply Subtype.ext
    show (a : R) * b = b * a
    have hst : s * t = t * s := setLike_mul_comm hs ht
    rw [← hsa, ← htb]
    change g * s * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
      _ = g * (t * s) * g⁻¹ := by rw [hst]
      _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
  refine ⟨P, hEP, hPc, ?_⟩
  set F := torsionSubgroup (P : Subgroup R) hPc p with hF
  have hEF : E ≤ F := fun x hx => ⟨hEP hx, hE.2 x hx⟩
  have hFel : IsElemAbelian p F := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => hx.2⟩
    apply Subtype.ext
    exact setLike_mul_comm a.2.1 b.2.1
  have hle : Nat.card F ≤ Nat.card E := by
    rw [hcard]
    exact hT.rank_le hp hFel
  have hEF' : E = F := Subgroup.eq_of_le_of_card_ge hEF hle
  intro x hx hxp
  have hxF : x ∈ F := ⟨hx, hxp⟩
  rwa [← hEF'] at hxF

theorem map_conj_map_conj_sylowTorusFusion {R : Type} [Group R] (H : Subgroup R) (a b : R) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change b * (a * x * a⁻¹) * b⁻¹ = b * a * x * (b * a)⁻¹
  group

theorem exists_conj_eq_of_selfCentralizing_of_sylowTorus {R : Type} [Group R] [Finite R]
    {p N : ℕ} (hp : p.Prime) (hT : SylowTorus R p N) {E E' : Subgroup R}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ N) (hE' : IsElemAbelian p E')
    (hsc : ∀ g : R, (∀ e ∈ E', g * e = e * g) → g ^ p = 1 → g ∈ E') :
    ∃ c : R, E' = E.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨T, E₀, hTc, hconj, hE₀T, hE₀, hE₀el, hE₀card⟩ := hT.exists_torus
  have key : ∀ F : Subgroup R, IsElemAbelian p F →
      ∃ g : R, F ≤ E₀.map (MulAut.conj g).toMonoidHom := by
    intro F hF
    obtain ⟨g, hg⟩ := hconj F (isPGroup_of_isElemAbelian_frame hF)
    refine ⟨g, fun x hx => ?_⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 (hg hx)
    refine Subgroup.mem_map.2 ⟨t, hE₀ t ht ?_, rfl⟩
    have h1 := hF.2 _ hx
    have h2 : (MulAut.conj g).toMonoidHom (t ^ p) = (MulAut.conj g).toMonoidHom 1 := by
      rw [map_pow, map_one]
      exact h1
    exact (MulAut.conj g).injective h2
  obtain ⟨g, hg⟩ := key E' hE'
  obtain ⟨g', hg'⟩ := key E hE
  have hE'eq : E' = E₀.map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm hg ?_
    rintro _ ⟨t, ht, rfl⟩
    refine hsc _ (fun e he => ?_) ?_
    · obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 (hg he)
      have hst : t * s = s * t := setLike_mul_comm (hE₀T ht) (hE₀T hs)
      change g * t * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * t * g⁻¹)
      calc g * t * g⁻¹ * (g * s * g⁻¹) = g * (t * s) * g⁻¹ := by group
        _ = g * (s * t) * g⁻¹ := by rw [hst]
        _ = g * s * g⁻¹ * (g * t * g⁻¹) := by group
    · change (g * t * g⁻¹) ^ p = 1
      rw [conj_pow, (hE₀el.2 t ht), mul_one, mul_inv_cancel]
  have hEeq : E = E₀.map (MulAut.conj g').toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hg' ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g').injective, hE₀card, hcard]
  refine ⟨g * g'⁻¹, ?_⟩
  rw [hE'eq, hEeq, map_conj_map_conj_sylowTorusFusion]
  congr 2
  group

end CFSG.StandardType

end

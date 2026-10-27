module

public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Surjections

variable {A B C : Type*} [Group A] [Group B] [Group C]

theorem ggExists_surjective_of_map_eq (f : A →* B) {S : Subgroup A} {T : Subgroup B}
    (h : S.map f = T) : ∃ Φ : ↥S →* ↥T, Function.Surjective Φ := by
  subst h
  exact ⟨f.subgroupMap S, f.subgroupMap_surjective S⟩

theorem ggExists_surjective_subgroupOf {X : Type*} [Group X] {W D : Subgroup X} (h : D ≤ W) :
    ∃ Φ : ↥D →* ↥(D.subgroupOf W), Function.Surjective Φ :=
  ⟨(Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom,
    (Subgroup.subgroupOfEquivOfLe h).symm.surjective⟩

theorem ggExists_surjective_trans {S : Subgroup A} {T : Subgroup B} {U : Subgroup C}
    (h₁ : ∃ Φ : ↥S →* ↥T, Function.Surjective Φ) (h₂ : ∃ Φ : ↥T →* ↥U, Function.Surjective Φ) :
    ∃ Φ : ↥S →* ↥U, Function.Surjective Φ := by
  obtain ⟨Φ₁, hΦ₁⟩ := h₁
  obtain ⟨Φ₂, hΦ₂⟩ := h₂
  exact ⟨Φ₂.comp Φ₁, hΦ₂.comp hΦ₁⟩

end Surjections

section Lift

variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (p : ℕ) [Fact p.Prime]

theorem ggPComponent_lift_ambient (f : A →* B) {Y : Subgroup A} (hp2 : p ≠ 2)
    (hker : IsPGroup 2 f.ker) {C₀ : Subgroup B} (hC₀Z : C₀ ≤ Y.map f)
    (hC₀ : CFSG.IsPComponent p (C₀.subgroupOf (Y.map f))) :
    ∃ S : Subgroup A, S ≤ Y ∧ CFSG.IsPComponent p (S.subgroupOf Y) ∧ S.map f = C₀ := by
  let g : ↥Y →* ↥(Y.map f) := f.subgroupMap Y
  have hg : Function.Surjective g := f.subgroupMap_surjective Y
  have hker2 : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.subgroupMap Y).ker
    rw [Subgroup.ker_subgroupMap Y f]
    exact hker.comap_subtype
  have hker' : ¬ p ∣ Nat.card g.ker := by
    obtain ⟨n, hn⟩ := hker2.exists_card_eq
    intro hdiv
    have hp_dvd_two : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (hn ▸ hdiv)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hp_dvd_two)
  obtain ⟨-, hinv, -⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (p := p) g hg hker'
  let S₁ : Subgroup ↥Y := Subgroup.closure {x : ↥Y |
    x ∈ (C₀.subgroupOf (Y.map f)).comap g ∧ ∃ k : ℕ, orderOf x = p ^ k}
  obtain ⟨hS₁pc, hS₁map⟩ := hinv (C₀.subgroupOf (Y.map f)) hC₀
  have hS₁pc' : CFSG.IsPComponent p S₁ := hS₁pc
  have hS₁map' : S₁.map g = C₀.subgroupOf (Y.map f) := hS₁map
  refine ⟨S₁.map Y.subtype, Subgroup.map_subtype_le S₁, ?_, ?_⟩
  · rw [show (S₁.map Y.subtype).subgroupOf Y = S₁ from
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective S₁]
    exact hS₁pc'
  · have hc : f.comp Y.subtype = (Y.map f).subtype.comp g := by
      ext x
      rfl
    calc (S₁.map Y.subtype).map f = S₁.map (f.comp Y.subtype) := by
          rw [Subgroup.map_map]
      _ = S₁.map ((Y.map f).subtype.comp g) := by rw [hc]
      _ = (S₁.map g).map (Y.map f).subtype := by rw [← Subgroup.map_map]
      _ = (C₀.subgroupOf (Y.map f)).map (Y.map f).subtype := by rw [hS₁map']
      _ = C₀ := Subgroup.map_subgroupOf_eq_of_le hC₀Z

end Lift

section Coprime

variable {N : Type*} [Group N] [Finite N]

theorem ggCoprime_centralizer_map (P : Subgroup N) [P.Normal] (hP : IsPGroup 2 P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {e : N} (he : e ^ p = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' P e} : Set (N ⧸ P)) =
      (Subgroup.centralizer ({e} : Set N)).map (QuotientGroup.mk' P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hep : IsPGroup p ↥(Subgroup.zpowers e) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one he
  haveI : Fact (IsPGroup p ↥(Subgroup.zpowers e)) := ⟨hep⟩
  have hcard : Nat.Coprime p (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right k
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer p (Subgroup.zpowers e) P
    inferInstance hcard
  simp only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, MonoidHom.map_closure,
    Set.image_singleton] at h
  exact h

end Coprime

theorem ggMap_subtype_centralizer {G : Type*} [Group G] {r : G}
    (e : ↥(Subgroup.centralizer ({r} : Set G))) :
    (Subgroup.centralizer ({e} : Set ↥(Subgroup.centralizer ({r} : Set G)))).map
        (Subgroup.centralizer ({r} : Set G)).subtype =
      Subgroup.centralizer ({r, (e : G)} : Set G) := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
    · exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)).symm
  · intro hx
    have hxr : x ∈ Subgroup.centralizer ({r} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) r (by simp)).symm
    refine Subgroup.mem_map.mpr ⟨⟨x, hxr⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simpa using ((Subgroup.mem_centralizer_iff.mp hx) (e : G) (by simp)).symm

end CFSG.StandardType

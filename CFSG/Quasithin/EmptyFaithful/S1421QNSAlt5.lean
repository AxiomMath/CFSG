module

public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421NS

theorem hom_units_int_eq_one_of_isPerfect {K : Type*} [Group K] [Group.IsPerfect K]
    (f : K →* ℤˣ) (k : K) : f k = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (⟨f k, k, rfl⟩ : f.range) 1)

theorem range_le_alternatingGroup_of_isPerfect {K : Type*} [Group K] [Group.IsPerfect K]
    (φ : K →* Equiv.Perm (Fin 5)) : φ.range ≤ alternatingGroup (Fin 5) := by
  rintro _ ⟨k, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  exact hom_units_int_eq_one_of_isPerfect (Equiv.Perm.sign.comp φ) k

theorem eq_bot_or_eq_alternatingGroup_of_normal {P : Subgroup (Equiv.Perm (Fin 5))}
    (hPn : P.Normal) (hP : P ≤ alternatingGroup (Fin 5)) :
    P = ⊥ ∨ P = alternatingGroup (Fin 5) := by
  have hn : (P.subgroupOf (alternatingGroup (Fin 5))).Normal := hPn.subgroupOf _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (alternatingGroup (Fin 5))) with
    h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hP
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hP h

theorem range_eq_alternatingGroup_of_isPerfect {K : Type*} [Group K] [Group.IsPerfect K]
    (φ : K →* Equiv.Perm (Fin 5)) (hN : φ.range.Normal) (hne : φ.range ≠ ⊥) :
    φ.range = alternatingGroup (Fin 5) :=
  (eq_bot_or_eq_alternatingGroup_of_normal hN
    (range_le_alternatingGroup_of_isPerfect φ)).resolve_left hne

theorem isPGroup_two_of_pCore_eq_top {H : Type*} [Group H] [Finite H]
    (h : CFSG.Open.pCore 2 H = ⊤) : IsPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 H) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  rw [h] at hp
  exact hp.of_equiv Subgroup.topEquiv

theorem val_mem_pCoreOf_two_iff_mem_pCore_two {G : Type*} [Group G] (K : Subgroup G) (k : ↥K) :
    (k : G) ∈ pCoreOf 2 K ↔ k ∈ CFSG.Open.pCore 2 ↥K := by
  unfold pCoreOf
  exact Subgroup.mem_map_iff_mem K.subtype_injective

theorem pCoreOf_two_eq_inf_of_le_normalizer {G : Type*} [Group G] [Finite G] {Y M : Subgroup G}
    (hYM : Y ≤ M) (hn : M ≤ Subgroup.normalizer (Y : Set G)) :
    pCoreOf 2 Y = Y ⊓ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 Y) ?_
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYM) ?_ (pCoreOf_isPGroup 2 Y)
    exact hn.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
    intro g hg
    have hgM : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      le_normalizer_pCoreOf 2 M (hYM hg)
    have hgM' : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      (Subgroup.normalizer (pCoreOf 2 M : Set G)).inv_mem hgM
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxY, hxQ⟩
      exact ⟨Y.mul_mem (Y.mul_mem hg hxY) (Y.inv_mem hg),
        (Subgroup.mem_normalizer_iff.mp hgM x).mp hxQ⟩
    · rintro ⟨h1, h2⟩
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      refine ⟨?_, ?_⟩
      · have := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) h1) hg
        simpa [mul_assoc] using this
      · have := (Subgroup.mem_normalizer_iff.mp hgM' (g * x * g⁻¹)).mp h2
        rwa [e] at this

variable {G : Type} [Group G] [Finite G]

theorem oTwoQuot_equiv_alt5 {K1 S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K1 : Set G))
    (hK1 : K1 ≠ ⊥) (hperf : ⁅K1, K1⁆ = K1)
    (e : OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) :
    Nonempty (OTwoQuot K1 ≃* alternatingGroup (Fin 5)) := by
  classical
  set X : Subgroup G := K1 ⊔ S
  have hK1X : K1 ≤ X := le_sup_left
  have hXN : X ≤ Subgroup.normalizer (K1 : Set G) := sup_le Subgroup.le_normalizer hS
  have hperfK : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr hperf
  let Ψ : ↥X →* Equiv.Perm (Fin 5) :=
    (e : OTwoQuot X →* Equiv.Perm (Fin 5)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))
  have hΨsurj : Function.Surjective Ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hΨker : ∀ x : ↥X, Ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
    intro x
    have h1 : Ψ x = 1 ↔ (QuotientGroup.mk x : OTwoQuot X) = 1 := e.map_eq_one_iff
    rw [h1, QuotientGroup.eq_one_iff]
    exact (val_mem_pCoreOf_two_iff_mem_pCore_two X x).symm
  let φ : ↥K1 →* Equiv.Perm (Fin 5) := Ψ.comp (Subgroup.inclusion hK1X)
  have hpc : pCoreOf 2 K1 = K1 ⊓ pCoreOf 2 X :=
    pCoreOf_two_eq_inf_of_le_normalizer hK1X hXN
  have hφker : ∀ k : ↥K1, φ k = 1 ↔ k ∈ CFSG.Open.pCore 2 ↥K1 := by
    intro k
    have h1 : φ k = 1 ↔ ((k : G) ∈ pCoreOf 2 X) := hΨker ⟨k, hK1X k.2⟩
    rw [h1, ← val_mem_pCoreOf_two_iff_mem_pCore_two, hpc, Subgroup.mem_inf]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hrange : φ.range = (K1.subgroupOf X).map Ψ := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, hK1X k.2⟩, k.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hnormal : φ.range.Normal := by
    rw [hrange]
    have : (K1.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK1X).mpr hXN
    exact Subgroup.Normal.map inferInstance Ψ hΨsurj
  have hne : φ.range ≠ ⊥ := by
    intro hbot
    have htop : CFSG.Open.pCore 2 ↥K1 = ⊤ := by
      refine eq_top_iff.mpr fun k _ => (hφker k).mp ?_
      have : φ k ∈ φ.range := ⟨k, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial ↥K1 := (Subgroup.nontrivial_iff_ne_bot K1).mpr hK1
    have hp2 : IsPGroup 2 ↥K1 := isPGroup_two_of_pCore_eq_top htop
    exact Group.IsPerfect.not_isNilpotent ↥K1 hp2.isNilpotent
  have hA5 : φ.range = alternatingGroup (Fin 5) :=
    range_eq_alternatingGroup_of_isPerfect φ hnormal hne
  have hker : CFSG.Open.pCore 2 ↥K1 = φ.ker := by
    ext k
    rw [MonoidHom.mem_ker, hφker]
  have : (CFSG.Open.pCore 2 ↥K1).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hA5)⟩

end S1421NS

end CFSG.Quasithin

module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeConjugators

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG.DisconnectedInvolutionGraph.Helpers

@[expose, instance_reducible] def normalizerConjAction {G : Type*} [Group G] {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) : MulDistribMulAction A Y where
  smul a y := ⟨(a : G) * (y : G) * (a : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hAY a.2) (y : G)).mp y.2⟩
  one_smul y := Subtype.ext (show (1 : G) * (y : G) * (1 : G)⁻¹ = y by group)
  mul_smul a b y := Subtype.ext (show (a : G) * (b : G) * (y : G) * ((a : G) * (b : G))⁻¹ =
    (a : G) * ((b : G) * (y : G) * (b : G)⁻¹) * (a : G)⁻¹ by group)
  smul_one a := Subtype.ext (show (a : G) * 1 * (a : G)⁻¹ = 1 by group)
  smul_mul a y z := Subtype.ext (show (a : G) * ((y : G) * (z : G)) * (a : G)⁻¹ =
    ((a : G) * (y : G) * (a : G)⁻¹) * ((a : G) * (z : G) * (a : G)⁻¹) by group)

theorem exists_invariant_sylow_two_of_coprime {G : Type} [Group G] [Finite G]
    {A Y T : Subgroup G} (hA : IsPGroup 3 A) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hTY : T ≤ Y) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    ∃ P : Subgroup G, T ≤ P ∧ P ≤ Y ∧ A ≤ Subgroup.normalizer (P : Set G) ∧ IsPGroup 2 P ∧
      ¬ 2 ∣ (P.subgroupOf Y).index := by
  letI : MulDistribMulAction A Y := normalizerConjAction hAY
  have hT2' : IsPGroup 2 (T.subgroupOf Y) :=
    hT2.comap_of_injective Y.subtype Subtype.coe_injective
  have hTinv : InvariantSubgroup (A := ↥A) (T.subgroupOf Y) := by
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAT a.2) (y : G)).mp hy
  obtain ⟨S, hTS, hSinv⟩ :=
    coprime_pgroup_invariant_sylow_containment 3 2 hA hY3 (T.subgroupOf Y) hT2' hTinv
  have hconj : ∀ b : G, b ∈ A → ∀ x : G, x ∈ (S : Subgroup ↥Y).map Y.subtype →
      b * x * b⁻¹ ∈ (S : Subgroup ↥Y).map Y.subtype := by
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨(⟨b, hb⟩ : A) • y, hSinv (⟨b, hb⟩ : A) y hy, rfl⟩
  have hPeq : ((S : Subgroup ↥Y).map Y.subtype).subgroupOf Y = (S : Subgroup ↥Y) := by
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      have hxy' : x = y := Subtype.ext hxy
      rwa [hxy'] at hx
    · intro hy
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  refine ⟨(S : Subgroup ↥Y).map Y.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : (⟨t, hTY ht⟩ : Y) ∈ T.subgroupOf Y := Subgroup.mem_subgroupOf.mpr ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTY ht⟩, hTS ht', rfl⟩
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj a ha x hx
    · intro hx
      have h := hconj a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
      have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
      rwa [e] at h
  · exact S.isPGroup'.map Y.subtype
  · rw [hPeq]
    exact Sylow.not_dvd_index S

theorem exists_conj_of_invariant_sylow_two {G : Type} [Group G] [Finite G]
    {A Y P Q : Subgroup G} (hA : IsPGroup 3 A) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hPY : P ≤ Y) (hQY : Q ≤ Y)
    (hP2 : IsPGroup 2 P) (hQ2 : IsPGroup 2 Q) (hPs : ¬ 2 ∣ (P.subgroupOf Y).index)
    (hQs : ¬ 2 ∣ (Q.subgroupOf Y).index) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ y ∈ Y ⊓ Subgroup.centralizer (A : Set G), Q = P.map (MulAut.conj y).toMonoidHom := by
  letI : MulDistribMulAction A Y := normalizerConjAction hAY
  have hPinv : InvariantSubgroup (A := ↥A) (P.subgroupOf Y) := by
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAP a.2) (y : G)).mp hy
  have hQinv : InvariantSubgroup (A := ↥A) (Q.subgroupOf Y) := by
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAQ a.2) (y : G)).mp hy
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 ↥Y, (S : Subgroup ↥Y) = P.subgroupOf Y :=
    ⟨IsPGroup.toSylow (hP2.comap_of_injective Y.subtype Subtype.coe_injective) hPs, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 ↥Y, (T : Subgroup ↥Y) = Q.subgroupOf Y :=
    ⟨IsPGroup.toSylow (hQ2.comap_of_injective Y.subtype Subtype.coe_injective) hQs, rfl⟩
  obtain ⟨e, hfix, hsmul⟩ :=
    coprime_pgroup_invariant_sylows_conjugate 3 2 hA hY3 S T
      (by rw [hS]; exact hPinv) (by rw [hT]; exact hQinv)
  have hTeq : (P.subgroupOf Y).map (MulAut.conj e).toMonoidHom = Q.subgroupOf Y := by
    rw [← hS, ← hT, ← sylow_smul_subgroup_eq_map 2 S e, hsmul]
  have hcent : (e : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg Subtype.val (hfix (⟨h, hh⟩ : A))
    have h2 : h * (e : G) * h⁻¹ = (e : G) := h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hQeq : Q = P.map (MulAut.conj (e : G)).toMonoidHom := by
    calc Q = (Q.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hQY).symm
      _ = ((P.subgroupOf Y).map (MulAut.conj e).toMonoidHom).map Y.subtype := by rw [hTeq]
      _ = (P.subgroupOf Y).map (Y.subtype.comp (MulAut.conj e).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = (P.subgroupOf Y).map ((MulAut.conj (e : G)).toMonoidHom.comp Y.subtype) := by
          rw [show Y.subtype.comp (MulAut.conj e).toMonoidHom =
            (MulAut.conj (e : G)).toMonoidHom.comp Y.subtype from MonoidHom.ext fun z => rfl]
      _ = ((P.subgroupOf Y).map Y.subtype).map (MulAut.conj (e : G)).toMonoidHom := by
          rw [Subgroup.map_map]
      _ = P.map (MulAut.conj (e : G)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hPY]
  exact ⟨(e : G), Subgroup.mem_inf.mpr ⟨e.2, hcent⟩, hQeq⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S

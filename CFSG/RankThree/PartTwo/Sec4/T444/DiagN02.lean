module

public import CFSG.RankThree.PartTwo.Sec4.Steps444

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

theorem ys03N02_sylow_invariant {G : Type} [Group G] [Finite G] {A J : Subgroup G}
    (hA : IsPGroup 3 A) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (h3J : 3 ∣ Nat.card J) :
    ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 3 T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      (∀ E : Subgroup G, E ≤ J → IsPGroup 3 E →
        ∃ j ∈ J, E.map (MulAut.conj j).toMonoidHom ≤ T) ∧ 3 ∣ Nat.card T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJmem : ∀ (a : ↥A) (x : ↥J), (a : G) * (x : G) * (a : G)⁻¹ ∈ J := fun a x =>
    (Subgroup.mem_normalizer_iff.mp (hAJ a.2) (x : G)).1 x.2
  letI : MulDistribMulAction ↥A ↥J :=
    { smul := fun a x => ⟨(a : G) * (x : G) * (a : G)⁻¹, hJmem a x⟩
      one_smul := fun x => Subtype.ext (show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G) by group)
      mul_smul := fun a b x => Subtype.ext
        (show (a : G) * (b : G) * (x : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹ by group)
      smul_mul := fun a x y => Subtype.ext
        (show (a : G) * ((x : G) * (y : G)) * (a : G)⁻¹ =
          ((a : G) * (x : G) * (a : G)⁻¹) * ((a : G) * (y : G) * (a : G)⁻¹) by group)
      smul_one := fun a => Subtype.ext (show (a : G) * (1 : G) * (a : G)⁻¹ = (1 : G) by group) }
  haveI : Finite (Sylow 3 J) :=
    Finite.of_injective (fun P : Sylow 3 J => (P : Set J)) SetLike.coe_injective
  obtain ⟨P₀, hP₀⟩ :=
    hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 J) (not_dvd_card_sylow 3 J)
  have hfix : ∀ a : ↥A, a • P₀ = P₀ := MulAction.mem_fixedPoints.1 hP₀
  have hfwd : ∀ b ∈ A, ∀ x ∈ P₀.toSubgroup.map J.subtype,
      b * x * b⁻¹ ∈ P₀.toSubgroup.map J.subtype := by
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hS : (⟨b, hb⟩ : ↥A) • P₀.toSubgroup = P₀.toSubgroup := by
      have h := congrArg Sylow.toSubgroup (hfix ⟨b, hb⟩)
      rwa [Sylow.pointwise_smul_def] at h
    have hmem := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : ↥A) _ hy
    rw [hS] at hmem
    exact Subgroup.mem_map_of_mem J.subtype hmem
  refine ⟨P₀.toSubgroup.map J.subtype, ?_, P₀.isPGroup'.map J.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hfwd a ha h hh
    · intro hh
      have h' := hfwd a⁻¹ (A.inv_mem ha) _ hh
      have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
      rwa [e] at h'
  · intro E hEJ hE
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (hE.comap_subtype (K := J))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q P₀
    have hgQ : MulAut.conj g • (Q : Subgroup J) = (P₀ : Subgroup J) := by
      rw [← Sylow.coe_subgroup_smul, hg]
    refine ⟨(g : G), g.2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxJ : x ∈ J := hEJ hx
    have hxQ : (⟨x, hxJ⟩ : ↥J) ∈ (Q : Subgroup J) := hQ (Subgroup.mem_comap.2 hx)
    have hmem := Subgroup.smul_mem_pointwise_smul (⟨x, hxJ⟩ : ↥J) (MulAut.conj g) _ hxQ
    rw [hgQ] at hmem
    exact Subgroup.mem_map_of_mem J.subtype hmem
  · rw [Subgroup.card_map_of_injective J.subtype_injective]
    have hidx := Subgroup.card_mul_index P₀.toSubgroup
    have hndvd : ¬ 3 ∣ P₀.toSubgroup.index := Sylow.not_dvd_index P₀
    rw [← hidx] at h3J
    exact ((Nat.Prime.dvd_mul Nat.prime_three).1 h3J).resolve_right hndvd

theorem ys03N02_central_three {G : Type} [Group G] [Finite G] {A T : Subgroup G}
    (hT : IsPGroup 3 T) (hA : IsPGroup 3 A) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (h3T : 3 ∣ Nat.card T) :
    ∃ w : G, w ∈ T ∧ w ≠ 1 ∧ w ^ 3 = 1 ∧ (∀ t ∈ T, Commute w t) ∧ (∀ a ∈ A, Commute w a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : T ⊔ A ≤ Subgroup.normalizer (T : Set G) :=
    sup_le (fun t ht => Subgroup.le_normalizer ht) hAT
  have hp : IsPGroup 3 (T ⊔ A : Subgroup G) := IsPGroup.to_sup_of_normal_left' hT hA hAT
  have hmem : ∀ (h : ↥(T ⊔ A)) (t : ↥T), (h : G) * (t : G) * (h : G)⁻¹ ∈ T := fun h t =>
    (Subgroup.mem_normalizer_iff.mp (hnorm h.2) (t : G)).1 t.2
  letI : MulAction ↥(T ⊔ A) ↥T :=
    { smul := fun h t => ⟨(h : G) * (t : G) * (h : G)⁻¹, hmem h t⟩
      one_smul := fun t => Subtype.ext (show (1 : G) * (t : G) * (1 : G)⁻¹ = (t : G) by group)
      mul_smul := fun h₁ h₂ t => Subtype.ext
        (show (h₁ : G) * (h₂ : G) * (t : G) * ((h₁ : G) * (h₂ : G))⁻¹ =
          (h₁ : G) * ((h₂ : G) * (t : G) * (h₂ : G)⁻¹) * (h₁ : G)⁻¹ by group) }
  have ha1 : (1 : ↥T) ∈ MulAction.fixedPoints ↥(T ⊔ A) ↥T :=
    MulAction.mem_fixedPoints.2 fun h => Subtype.ext
      (show (h : G) * (1 : G) * (h : G)⁻¹ = (1 : G) by group)
  obtain ⟨y, hyfix, hy1⟩ :=
    hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥T h3T ha1
  have hyG : (y : G) ≠ 1 := fun h => hy1.symm (Subtype.ext h)
  have hcomm : ∀ h : ↥(T ⊔ A), (h : G) * (y : G) = (y : G) * (h : G) := by
    intro h
    have e : (h : G) * (y : G) * (h : G)⁻¹ = (y : G) :=
      congrArg Subtype.val (MulAction.mem_fixedPoints.1 hyfix h)
    exact mul_inv_eq_iff_eq_mul.1 e
  have hyT_comm : ∀ t ∈ T, Commute (y : G) t := fun t ht =>
    (hcomm ⟨t, Subgroup.mem_sup_left ht⟩).symm
  have hyA_comm : ∀ a ∈ A, Commute (y : G) a := fun a ha =>
    (hcomm ⟨a, Subgroup.mem_sup_right ha⟩).symm
  classical
  obtain ⟨k, hk⟩ := hT y
  have hk' : (y : G) ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hex : ∃ m, (y : G) ^ 3 ^ m = 1 := ⟨k, hk'⟩
  have hk₀ : (y : G) ^ 3 ^ Nat.find hex = 1 := Nat.find_spec hex
  have hk₀pos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk₀
    exact hyG hk₀
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnot : (y : G) ^ 3 ^ n ≠ 1 := fun h =>
    Nat.find_min hex (show n < Nat.find hex by omega) h
  have hw3 : ((y : G) ^ 3 ^ n) ^ 3 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hn]
    exact hk₀
  exact ⟨(y : G) ^ 3 ^ n, pow_mem y.2 _, hnot, hw3,
    fun t ht => (hyT_comm t ht).pow_left _, fun a ha => (hyA_comm a ha).pow_left _⟩

theorem ys03_N02_sylow_center {G : Type} [Group G] [Finite G] {A M J : Subgroup G}
    (hctx : Ctx444 G A M) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (h3J : 3 ∣ Nat.card J) :
    ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 3 T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      (∀ E : Subgroup G, E ≤ J → IsPGroup 3 E →
        ∃ j ∈ J, E.map (MulAut.conj j).toMonoidHom ≤ T) ∧
      ∃ z ∈ A ⊓ J, z ≠ 1 ∧ T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hA3 : IsPGroup 3 A := hctx.isE27.isPGroup
  obtain ⟨T, hTJ, hT3, hAT, hsyl, h3T⟩ := ys03N02_sylow_invariant hA3 hAJ h3J
  obtain ⟨w, hwT, hw1, hw3, hwT_comm, hwA_comm⟩ :=
    ys03N02_central_three hT3 hA3 hAT h3T
  have hwA : w ∈ A := hctx.rank3II_4_45
    (Subgroup.mem_centralizer_iff.2 fun a ha => (hwA_comm a ha).symm) hw3
  refine ⟨T, hTJ, hT3, hAT, hsyl, w, Subgroup.mem_inf.2 ⟨hwA, hTJ hwT⟩, hw1, ?_⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hwT_comm t ht

end CFSG.RankThree.PartTwo.Sec4

end

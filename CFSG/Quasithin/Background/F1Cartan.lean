module

public import CFSG.Quasithin.Background.F1Borel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

variable {G : Type u} [Group G]

@[expose] def IsCartanOf (D B : Subgroup G) : Prop :=
  D ≤ B ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.relIndex B = 2 ^ k

namespace F1

variable [Finite G]

theorem exists_cartan {Lj S : Subgroup G} (h : IsSylowTwoOf (S ⊓ Lj) Lj) :
    ∃ D : Subgroup G, IsCartanOf D (borelOf Lj S) ∧ D ⊓ (S ⊓ Lj) = ⊥ ∧
      (S ⊓ Lj) ⊔ D = borelOf Lj S := by
  set B := borelOf Lj S with hB
  have hSB : S ⊓ Lj ≤ B := sylow_le_borelOf Lj S
  have hN : ((S ⊓ Lj).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr (borelOf_le_normalizer Lj S)
  have hsyl : IsSylowTwoOf (S ⊓ Lj) B := isSylowTwoOf_mono_right h hSB (borelOf_le Lj S)
  have hp : IsPGroup 2 ↥((S ⊓ Lj).subgroupOf B) :=
    h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  have hodd : ¬ 2 ∣ ((S ⊓ Lj).subgroupOf B).index := hsyl.2.2
  have hcop : Nat.Coprime (Nat.card ↥((S ⊓ Lj).subgroupOf B)) ((S ⊓ Lj).subgroupOf B).index := by
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcard : Nat.card ↥((S ⊓ Lj).subgroupOf B) * Nat.card K = Nat.card B := hK.card_mul_card
  have hN0 : 0 < Nat.card ↥((S ⊓ Lj).subgroupOf B) := Nat.card_pos
  have hKcard : Nat.card K = ((S ⊓ Lj).subgroupOf B).index := by
    have h2 := Subgroup.card_mul_index ((S ⊓ Lj).subgroupOf B)
    exact Nat.eq_of_mul_eq_mul_left hN0 (hcard.trans h2.symm)
  have hKindex : K.index = Nat.card ↥((S ⊓ Lj).subgroupOf B) := by
    have h2 := Subgroup.card_mul_index K
    have hK0 : 0 < Nat.card K := Nat.card_pos
    rw [mul_comm] at hcard
    exact Nat.eq_of_mul_eq_mul_left hK0 (h2.trans hcard.symm)
  have hmapN : ((S ⊓ Lj).subgroupOf B).map B.subtype = S ⊓ Lj := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hSB
  have hsub : (K.map B.subtype).subgroupOf B = K :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective K
  have hKS : K.map B.subtype ≤ B := Subgroup.map_subtype_le K
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  refine ⟨K.map B.subtype, ⟨hKS, ?_, ⟨k, ?_⟩⟩, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective, hKcard]
    exact Nat.odd_iff.mpr (by omega)
  · rw [Subgroup.relIndex, hsub, hKindex, hk]
  · rw [eq_bot_iff]
    rintro x ⟨⟨y, hyK, rfl⟩, hxS⟩
    have hyN : y ∈ (S ⊓ Lj).subgroupOf B := hxS
    have h1 : y ∈ ((S ⊓ Lj).subgroupOf B) ⊓ K := ⟨hyN, hyK⟩
    rw [hK.disjoint.eq_bot] at h1
    have : y = 1 := h1
    simp [this]
  · apply le_antisymm
    · exact sup_le hSB hKS
    · intro b hb
      have h1 : (⟨b, hb⟩ : B) ∈ ((S ⊓ Lj).subgroupOf B) ⊔ K := by
        rw [hK.sup_eq_top]
        exact Subgroup.mem_top _
      have h3 : b ∈ (((S ⊓ Lj).subgroupOf B) ⊔ K).map B.subtype := ⟨⟨b, hb⟩, h1, rfl⟩
      rw [Subgroup.map_sup, hmapN] at h3
      exact h3

omit [Finite G] in
theorem sup_borelOf_eq_sup_cartan {Li Lj S D : Subgroup G} (hD : (S ⊓ Lj) ⊔ D = borelOf Lj S) :
    Li ⊔ S ⊔ borelOf Lj S = Li ⊔ S ⊔ D := by
  have hSD : S ⊓ Lj ⊔ D ≤ Li ⊔ S ⊔ D :=
    sup_le ((inf_le_left : S ⊓ Lj ≤ S).trans (le_sup_right.trans le_sup_left)) le_sup_right
  have hDB : D ≤ borelOf Lj S := hD ▸ (le_sup_right : D ≤ S ⊓ Lj ⊔ D)
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [← hD]
    exact hSD.trans le_rfl
  · exact sup_le_sup_left hDB _

omit [Finite G] in
theorem borelOf_le_normalizer_iff {Li Lj S D : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (Li : Set G)) (hD : (S ⊓ Lj) ⊔ D = borelOf Lj S) :
    borelOf Lj S ≤ Subgroup.normalizer (Li : Set G) ↔ D ≤ Subgroup.normalizer (Li : Set G) := by
  have hDB : D ≤ borelOf Lj S := hD ▸ (le_sup_right : D ≤ S ⊓ Lj ⊔ D)
  constructor
  · intro h
    exact hDB.trans h
  · intro h
    rw [← hD]
    exact sup_le (inf_le_left.trans hS) h

omit [Finite G] in
theorem isSolvable_of_normal_subgroupOf {N H : Subgroup G} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] (hN : Group.IsSolvable N)
    (hq : Group.IsSolvable (↥H ⧸ N.subgroupOf H)) : Group.IsSolvable H := by
  have : Group.IsSolvable ↥(N.subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).symm.surjective
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf H).subtype
    (QuotientGroup.mk' (N.subgroupOf H)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem isSolvable_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) : Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  infer_instance

omit [Finite G] in
theorem isSolvable_sup_of_le_normalizer {N K : Subgroup G} (hN : Group.IsSolvable N)
    (hK : Group.IsSolvable K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    Group.IsSolvable ↥(N ⊔ K) := by
  have hnorm : (N.subgroupOf (N ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hKN)
  refine isSolvable_of_normal_subgroupOf le_sup_left hN ?_
  refine Group.isSolvable_of_surjective
    (f := (QuotientGroup.mk' (N.subgroupOf (N ⊔ K))).comp
      (Subgroup.inclusion (le_sup_right : K ≤ N ⊔ K))) ?_
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨a, ha, b, hb, hx⟩ := (mem_sup_iff_exists_mul_of_normalizes hKN).mp x.2
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (⟨b, _⟩ : ↥(N ⊔ K)) : ↥(N ⊔ K) ⧸ N.subgroupOf (N ⊔ K)) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((⟨b, Subgroup.mem_sup_right hb⟩ : ↥(N ⊔ K))⁻¹ * x : ↥(N ⊔ K)) : G) = b⁻¹ * (a * b) := by
      simp [hx]
    rw [this]
    have hab : b⁻¹ * (a * b) ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hb)) a).mp ha
      simpa [mul_assoc] using this
    exact hab

theorem isSolvable_borelOf {Li S : Subgroup G} (hsyl : IsSylowTwoOf (S ⊓ Li) Li)
    (hR : RankOneAt Li (S ⊓ Li)) : Group.IsSolvable (borelOf Li S) := by
  have hN : ((S ⊓ Li).subgroupOf (borelOf Li S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sylow_le_borelOf Li S)).mpr
      (borelOf_le_normalizer Li S)
  refine isSolvable_of_normal_subgroupOf (sylow_le_borelOf Li S)
    (isSolvable_of_isPGroup_two hsyl.2.1) ?_
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have := hR.comm ((y⁻¹ : ↥(borelOf Li S)) : G) (y⁻¹).2 ((x⁻¹ : ↥(borelOf Li S)) : G) (x⁻¹).2
      simpa [mul_assoc] using this

omit [Finite G] in
theorem normalizer_subgroupOf_eq {Li S : Subgroup G} :
    Subgroup.normalizer (((S ⊓ Li).subgroupOf Li : Subgroup ↥Li) : Set ↥Li) =
      (borelOf Li S).subgroupOf Li := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
  show _ ↔ (x : G) ∈ Li ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ Li
    · exact h ⟨g, hg⟩
    · constructor
      · intro hg'
        exact absurd (Subgroup.mem_inf.mp hg').2 hg
      · intro hg'
        have hg2 : (x : G) * g * (x : G)⁻¹ ∈ Li := (Subgroup.mem_inf.mp hg').2
        apply absurd _ hg
        have := Li.mul_mem (Li.mul_mem (Li.inv_mem x.2) hg2) x.2
        simpa [mul_assoc] using this
  · rintro ⟨-, h⟩ y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp h) (y : G)
    exact this

theorem map_borelOf_eq_normalizer {Li S : Subgroup G} (hsyl : IsSylowTwoOf (S ⊓ Li) Li) :
    IsPGroup 2 (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))) ∧
      ¬ 2 ∣ (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))).index ∧
      ((borelOf Li S).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) =
        Subgroup.normalizer
          ((((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) :
            Subgroup (oTwoQuot ↥Li)) : Set (oTwoQuot ↥Li)) := by
  set π : ↥Li →* oTwoQuot ↥Li := QuotientGroup.mk' (pCore 2 ↥Li) with hπ
  set T : Subgroup ↥Li := (S ⊓ Li).subgroupOf Li with hT
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ T := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 Li := (mem_pCore_iff_coe x).mp hx
    exact isSylowTwoOf_pCoreOf_le hsyl h1
  refine ⟨?_, ?_, ?_⟩
  · exact (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).map π
  · rw [Subgroup.index_map_eq (f := π) (H := T) hsurj hker]
    exact hsyl.2.2
  · rw [← normalizer_subgroupOf_eq]
    have h1 : (Subgroup.normalizer ((T.map π : Subgroup (oTwoQuot ↥Li)) :
        Set (oTwoQuot ↥Li))).comap π = Subgroup.normalizer T := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hsurj, Subgroup.comap_map_eq_self hker]
    conv_rhs => rw [← Subgroup.map_comap_eq_self_of_surjective hsurj
      (Subgroup.normalizer ((T.map π : Subgroup (oTwoQuot ↥Li)) : Set (oTwoQuot ↥Li))), h1]

theorem isSolvable_bigB {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    Group.IsSolvable (bigB L1 L2 S) := by
  have hB1 : Group.IsSolvable (borelOf L1 S) := isSolvable_borelOf h.hyp.h1.sylow h.r1
  have hB2 : Group.IsSolvable (borelOf L2 S) := isSolvable_borelOf h.hyp.h2.sylow h.r2
  have hX : Group.IsSolvable ↥(borelOf L1 S ⊔ borelOf L2 S) :=
    isSolvable_sup_of_le_normalizer hB1 hB2 (borelOf_le_normalizer_borelOf h)
  have hS : Group.IsSolvable S := isSolvable_of_isPGroup_two h.hyp.h1.pgroup
  exact isSolvable_sup_of_le_normalizer hX hS
    (le_normalizer_sup (le_normalizer_borelOf h.hyp.h1.normalizes)
      (le_normalizer_borelOf h.hyp.h2.normalizes))

end F1

end CFSG.Quasithin

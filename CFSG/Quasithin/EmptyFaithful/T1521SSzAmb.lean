module

public import CFSG.Quasithin.EmptyFaithful.T1521SSzAbs
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure SzComponent1521 (L : Subgroup G) : Prop where
  quasi : CFSG.Open.IsQuasisimple ↥L
  center_two : IsPGroup 2 ↥(Subgroup.center ↥L)
  sz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)

theorem SzComponent1521.of_cases [Finite G] {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hSz : (∃ e : ℕ, IsSz e ↥L) ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)) : SzComponent1521 L :=
  ⟨hq, hZ, SzQuot1521.exists_isSz_quot hq hZ hSz⟩

theorem SzComponent1521.pCoreOf_central [Finite G] {L : Subgroup G} (hL : SzComponent1521 L) {x : G}
    (hx : x ∈ pCoreOf 2 L) : ∀ l ∈ L, x * l = l * x := by
  rw [C2A3Orbits.pCoreOf_eq_map_pCore L] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyc : y ∈ Subgroup.center ↥L := by
    rw [← SzQuot1521.pCore_eq_center hL.quasi hL.center_two]
    exact hy
  intro l hl
  have := Subgroup.mem_center_iff.mp hyc ⟨l, hl⟩
  exact congrArg Subtype.val this.symm

theorem SzComponent1521.exists_mul {S L : Subgroup G}
    (hL : SzComponent1521 L) (hP : IsSylowTwoOf (S ⊓ L) L)
    (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1) {m : G} (hmS : m ∈ S)
    (hmN : m ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ S ⊓ L, ∃ c ∈ S ⊓ Subgroup.centralizer (L : Set G), m = l * c := by
  obtain ⟨e, he⟩ := hL.sz
  obtain ⟨a, ha, -, ⟨φ⟩⟩ := SBc2.isSz_equiv he
  obtain ⟨k, hk⟩ := hS m hmS
  have hmem : m ∈ L ⊔ Subgroup.centralizer (L : Set G) :=
    CFSG.ComponentClassification.GMS78.mem_sup_centralizer_of_sz hL.quasi.1 ha φ hmN hk
  have hmem' : m ∈ (L : Set G) * (Subgroup.centralizer (L : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L _
      (Subgroup.centralizer_le_normalizer (L : Set G))]
    exact hmem
  obtain ⟨l, hl, c, hc, rfl⟩ := hmem'
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  have hcN : c ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (s := ((S ⊓ L : Subgroup G) : Set G)) (t := (L : Set G)) (fun x hx => hx.2) hc)
  have hmN' : l * c ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hmN x
    have h2 : (l * c) * x * (l * c)⁻¹ ∈ S ↔ x ∈ S := by
      constructor
      · intro h
        have := S.mul_mem (S.mul_mem (S.inv_mem hmS) h) hmS
        simpa [mul_assoc] using this
      · intro h
        exact S.mul_mem (S.mul_mem hmS h) (S.inv_mem hmS)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hlN : l ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    have := Subgroup.mul_mem _ hmN' (Subgroup.inv_mem _ hcN)
    simpa using this
  have hpow : l ^ 2 ^ k * c ^ 2 ^ k = 1 := by
    rw [← Commute.mul_pow hlc]
    exact hk
  have hlk_cent : ∀ y ∈ L, y * l ^ 2 ^ k = l ^ 2 ^ k * y := by
    intro y hy
    have h1 : l ^ 2 ^ k = (c ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [h1]
    have hcp : c ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hc _
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hcp) y hy
  have hzc : (⟨l ^ 2 ^ k, L.pow_mem hl _⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hlk_cent y y.2)
  obtain ⟨j, hj⟩ := hL.center_two ⟨⟨l ^ 2 ^ k, L.pow_mem hl _⟩, hzc⟩
  have hl2 : l ^ 2 ^ (k + j) = 1 := by
    have h1 := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : G)) hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    rw [pow_add, pow_mul]
    exact h1
  have hlP : l ∈ S ⊓ L := by
    have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.normalizer
        (((A4.toSylow hP : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.mp hlN (x : G)
    exact SzQuot1521.mem_of_pow_eq_one_of_mem_normalizer (A4.toSylow hP) hmem (k := k + j)
      (Subtype.ext (by simpa using hl2))
  refine ⟨l, hlP, c, ⟨?_, hc⟩, rfl⟩
  have := S.mul_mem (S.inv_mem hlP.1) hmS
  simpa using this

theorem SzComponent1521.mem_centralizer_of_commutator [Finite G]
    {S L : Subgroup G} (hL : SzComponent1521 L)
    (hP : IsSylowTwoOf (S ⊓ L) L) {s : G} (hs : s ∈ S ⊓ L)
    (h : ∀ h ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G), Odd (orderOf h) →
      ⁅s, h⁆ ∈ Subgroup.centralizer (L : Set G)) :
    ∀ y ∈ L, s * y = y * s := by
  obtain ⟨e, he⟩ := hL.sz
  have hmain := SzQuot1521.mem_center_of_commutator_mem_center hL.center_two
    (SzQuot1521.fusionIsBenderGroup_of_isSz he) (A4.toSylow hP) (s := ⟨s, hs.2⟩) hs ?_
  · intro y hy
    have := Subgroup.mem_center_iff.mp hmain ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · intro h' hh' hodd
    have hmem : (h' : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact (Subgroup.mem_normalizer_iff.mp hh' ⟨x, hx.2⟩).mp hx
      · intro hx
        have hxL : x ∈ L := by
          have := L.mul_mem (L.inv_mem h'.2) (L.mul_mem hx.2 h'.2)
          simpa [mul_assoc] using this
        exact (Subgroup.mem_normalizer_iff.mp hh' ⟨x, hxL⟩).mpr hx
    have hodd' : Odd (orderOf (h' : G)) := by rwa [Subgroup.orderOf_coe]
    have hc := h (h' : G) ⟨h'.2, hmem⟩ hodd'
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    have := Subgroup.mem_centralizer_iff.mp hc y y.2
    simpa [commutatorElement_def] using this

theorem SzComponent1521.conj_mem {S L : Subgroup G}
    (hL : SzComponent1521 L) (hP : IsSylowTwoOf (S ⊓ L) L)
    (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1)
    {b : G} (hb : b ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))
    {y : G} (hyS : y ∈ S) (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    b * y * b⁻¹ ∈ S ⊓ Subgroup.normalizer (L : Set G) := by
  obtain ⟨l, hl, c, hc, rfl⟩ := hL.exists_mul hP hS hyS hyN
  have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hc.2 b hb.1
  have hbl : b * l * b⁻¹ ∈ S ⊓ L := (Subgroup.mem_normalizer_iff.mp hb.2 l).mp hl
  have e : b * (l * c) * b⁻¹ = (b * l * b⁻¹) * (b * c * b⁻¹) := by group
  have e2 : b * c * b⁻¹ = c := by rw [hbc]; group
  refine ⟨?_, ?_⟩
  · rw [e, e2]
    exact S.mul_mem hbl.1 hc.1
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hb.1) hyN)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hb.1))

theorem SzComponent1521.centralizes_of_forall_odd [Finite G]
    {S L : Subgroup G} (hL : SzComponent1521 L)
    (hP : IsSylowTwoOf (S ⊓ L) L) {s c : G} (hs : s ∈ S ⊓ L)
    (hc : c ∈ Subgroup.centralizer (L : Set G))
    (h : ∀ h ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G), Odd (orderOf h) →
      ⁅s, h⁆ ∈ Subgroup.centralizer (L : Set G)) :
    ∀ l ∈ L, (s * c) * l = l * (s * c) := by
  intro l hl
  have hsl := hL.mem_centralizer_of_commutator hP hs h l hl
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  calc s * c * l = s * (c * l) := by rw [mul_assoc]
    _ = s * (l * c) := by rw [hcl]
    _ = s * l * c := by rw [mul_assoc]
    _ = l * s * c := by rw [hsl]
    _ = l * (s * c) := by rw [mul_assoc]

end CFSG.Quasithin

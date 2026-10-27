module

public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Zc

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

variable {G : Type} [Group G]

noncomputable abbrev conjOn {E L : Subgroup G}
    (h : E ≤ Subgroup.normalizer (L : Set G)) : ↥E →* MulAut ↥L :=
  CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct h

theorem mem_innerPart_iff (S L : Subgroup G) {x : G} :
    x ∈ innerPart1521 S L ↔
      ∃ r ∈ S ⊓ L, ∃ c ∈ S ⊓ Subgroup.centralizer (L : Set G), x = r * c := by
  have hcn : S ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hc.2 y hy.2
    exact Subgroup.centralizer_le_normalizer _ hc'
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (S ⊓ L) _ hcn
  constructor
  · intro hx
    have hx0 : x ∈ ((S ⊓ L ⊔ S ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := hx
    rw [h] at hx0
    have hx' : x ∈ ((S ⊓ L : Subgroup G) : Set G) * ((S ⊓ Subgroup.centralizer (L : Set G) :
        Subgroup G) : Set G) := hx0
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    exact ⟨a, ha, c, hc, rfl⟩
  · rintro ⟨r, hr, c, hc, rfl⟩
    exact Subgroup.mul_mem_sup hr hc

variable [Finite G]

theorem mem_innerPart_iff_conjAct_inner {S L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSU 3 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (s : ↥S) :
    (s : G) ∈ innerPart1521 S L ↔ conjOn hSN s ∈ Inn ↥L := by
  have hinj := conj_injective_of_isPSU hn hL
  constructor
  · intro hs
    obtain ⟨r, hr, c, hc, hsrc⟩ := (mem_innerPart_iff S L).1 hs
    refine ⟨⟨r, hr.2⟩, ?_⟩
    ext x
    change (r : G) * x * (r : G)⁻¹ = (s : G) * x * (s : G)⁻¹
    rw [hsrc]
    have hcx : (c : G) * x = x * c := (Subgroup.mem_centralizer_iff.mp hc.2 x x.2).symm
    calc (r : G) * x * (r : G)⁻¹ = r * (c * x * c⁻¹) * r⁻¹ := by
          rw [show (c : G) * x * c⁻¹ = x by rw [hcx]; group]
      _ = r * c * x * (r * c)⁻¹ := by group
  · rintro ⟨y, hy⟩
    have hyx : ∀ x : ↥L, (y : G) * x * (y : G)⁻¹ = (s : G) * x * (s : G)⁻¹ := fun x =>
      congrArg (fun φ : MulAut ↥L => ((φ x : ↥L) : G)) hy
    set c : G := (y : G)⁻¹ * s with hcdef
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hyx ⟨x, hx⟩
      change (y : G) * x * (y : G)⁻¹ = (s : G) * x * (s : G)⁻¹ at this
      rw [hcdef]
      calc x * ((y : G)⁻¹ * s) = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * s := by group
        _ = (y : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * s := by rw [this]
        _ = (y : G)⁻¹ * s * x := by group
    have hys : (s : G) = (y : G) * c := by rw [hcdef]; group
    have hyN : (y : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
      have hsN : (s : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have h1 := Subgroup.mem_normalizer_iff.mp (hSN s.2) z
        have h2 : (s : G) * z * (s : G)⁻¹ ∈ S ↔ z ∈ S := by
          constructor
          · intro h
            have := S.mul_mem (S.mul_mem (S.inv_mem s.2) h) s.2
            simpa [mul_assoc] using this
          · intro h
            exact S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2)
        rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
      have hcN : c ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
          (s := ((S ⊓ L : Subgroup G) : Set G)) (t := (L : Set G)) (fun z hz => hz.2) hcC)
      have : (y : G) = s * c⁻¹ := by rw [hys]; group
      rw [this]
      exact Subgroup.mul_mem _ hsN (Subgroup.inv_mem _ hcN)
    obtain ⟨k, hk⟩ := hS2 s
    have hsk : (s : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hyk : (y : G) ^ 2 ^ k = 1 := by
      have hconj : (MulAut.conj y : MulAut ↥L) ^ 2 ^ k = 1 := by
        rw [hy, ← map_pow, hk, map_one]
      have : y ^ 2 ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hconj)
      exact congrArg Subtype.val this
    have hyR : (y : G) ∈ S ⊓ L := by
      have hyN' : y ∈ Subgroup.normalizer
          (((A4.toSylow hSyl : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have := Subgroup.mem_normalizer_iff.mp hyN (x : G)
        change (x : G) ∈ S ⊓ L ↔ (y : G) * (x : G) * (y : G)⁻¹ ∈ S ⊓ L
        exact this
      have := mem_of_pow_eq_one_of_mem_normalizer_aux (A4.toSylow hSyl) hyN'
        (k := k) (Subtype.ext (by simpa using hyk))
      exact this
    have hcS : c ∈ S := by
      rw [hcdef]
      exact S.mul_mem (S.inv_mem hyR.1) s.2
    exact (mem_innerPart_iff S L).2 ⟨y, hyR, c, ⟨hcS, hcC⟩, hys⟩

theorem exists_involution_cover {S L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSU 3 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ b ∈ S, b ^ 2 = 1 ∧ ∀ a ∈ S, a ^ 2 = 1 →
      a ∈ innerPart1521 S L ∨ b⁻¹ * a ∈ innerPart1521 S L := by
  classical
  set Θ : ↥S →* Outer ↥L := (QuotientGroup.mk' (Inn ↥L)).comp (conjOn hSN) with hΘ
  have hΘone : ∀ s : ↥S, Θ s = 1 ↔ (s : G) ∈ innerPart1521 S L := fun s =>
    (QuotientGroup.eq_one_iff _).trans
      (mem_innerPart_iff_conjAct_inner hn hL hSyl hS2 hSN s).symm
  have hB2 : IsPGroup 2 (conjOn hSN).range :=
    hS2.of_surjective (conjOn hSN).rangeRestrict (conjOn hSN).rangeRestrict_surjective
  have hcyc := cyclic_map_outer_of_isPGroup hn hL hB2
  have hmem : ∀ s : ↥S, Θ s ∈ (conjOn hSN).range.map (QuotientGroup.mk' (Inn ↥L)) := fun s =>
    Subgroup.mem_map.mpr ⟨conjOn hSN s, ⟨s, rfl⟩, rfl⟩
  have key : ∀ s s' : ↥S, Θ s ^ 2 = 1 → Θ s' ^ 2 = 1 → Θ s ≠ 1 → Θ s' ≠ 1 → Θ s = Θ s' := by
    intro s s' hs hs' hs1 hs1'
    have := eq_of_sq_eq_one_of_isCyclic (C := (conjOn hSN).range.map (QuotientGroup.mk' (Inn ↥L)))
      (x := ⟨Θ s, hmem s⟩) (y := ⟨Θ s', hmem s'⟩) (Subtype.ext hs) (Subtype.ext hs')
      (fun h => hs1 (congrArg Subtype.val h)) (fun h => hs1' (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hsq : ∀ a : G, ∀ ha : a ∈ S, a ^ 2 = 1 → Θ ⟨a, ha⟩ ^ 2 = 1 := by
    intro a ha ha2
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥S) ^ 2 = 1 := Subtype.ext (by simpa using ha2)
    rw [this, map_one]
  by_cases hall : ∀ a ∈ S, a ^ 2 = 1 → a ∈ innerPart1521 S L
  · exact ⟨1, S.one_mem, by simp, fun a ha ha2 => Or.inl (hall a ha ha2)⟩
  · push Not at hall
    obtain ⟨a₀, ha₀S, ha₀2, ha₀T⟩ := hall
    refine ⟨a₀, ha₀S, ha₀2, fun a haS ha2 => ?_⟩
    by_cases haT : a ∈ innerPart1521 S L
    · exact Or.inl haT
    · right
      have h1 : Θ ⟨a, haS⟩ = Θ ⟨a₀, ha₀S⟩ :=
        key ⟨a, haS⟩ ⟨a₀, ha₀S⟩ (hsq a haS ha2) (hsq a₀ ha₀S ha₀2)
          (fun h => haT ((hΘone _).1 h)) (fun h => ha₀T ((hΘone _).1 h))
      have h2 : Θ (⟨a₀, ha₀S⟩⁻¹ * ⟨a, haS⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact (hΘone _).1 h2

end CFSG.Quasithin.U31521

module

public import CFSG.Quasithin.H13.A7FiveModelSolvable
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Quasithin

section General

variable {G : Type*} [Group G]

theorem eq_top_of_normal_sup_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] [Group.IsPerfect G]
    {N P : Subgroup G} [N.Normal] (hP : IsPGroup p P) (h : N ⊔ P = ⊤) : N = ⊤ := by
  have hq : IsPGroup p (G ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ ((N ⊔ P : Subgroup G) : Set G) := by
      rw [h]
      exact mem_top g
    rw [normal_mul] at hg
    obtain ⟨n, hn, q, hq, rfl⟩ := hg
    obtain ⟨k, hk⟩ := hP ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul, ← QuotientGroup.mk_pow,
      hk', QuotientGroup.mk_one]
  by_contra hne
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.2 hne
  exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hq.isNilpotent

theorem not_isSolvable_of_perfect {B : Subgroup G} (hB1 : B ≠ ⊥) (hBperf : ⁅B, B⁆ = B) :
    ¬ Group.IsSolvable B := by
  have : Group.IsPerfect B := Subgroup.isPerfect_iff.2 hBperf
  have : Nontrivial B := (nontrivial_iff_ne_bot B).2 hB1
  exact Group.IsPerfect.not_isSolvable B

theorem normal_of_sup_eq_top {B S : Subgroup G} (hSB : S ≤ normalizer (B : Set G))
    (h : B ⊔ S = ⊤) : B.Normal := by
  have hle : (⊤ : Subgroup G) ≤ normalizer (B : Set G) :=
    h ▸ sup_le le_normalizer hSB
  exact normalizer_eq_top_iff.1 (top_le_iff.1 hle)

end General

theorem five_model_Sylow_normalized_perfect_subgroup_eq_top
    {Q : Type} [Group Q] [Finite Q]
    (hQ : QT13Five Q) (S : Sylow 2 Q) {B : Subgroup Q} (hB1 : B ≠ ⊥) (hBperf : ⁅B, B⁆ = B)
    (hSB : (S : Subgroup Q) ≤ normalizer (B : Set Q)) : B = ⊤ := by
  have hBS : B ⊔ (S : Subgroup Q) = ⊤ := by
    by_contra hne
    have hsolv := five_model_proper_Sylow_two_overgroups_are_solvable hQ S le_sup_right
      (lt_top_iff_ne_top.2 hne)
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective
        (f := inclusion (le_sup_left (b := (S : Subgroup Q)))) (inclusion_injective _)
    exact not_isSolvable_of_perfect hB1 hBperf this
  have hBn : B.Normal := normal_of_sup_eq_top hSB hBS
  have hsimple : IsSimpleGroup Q → B = ⊤ := fun _ =>
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal B).resolve_left hB1
  rcases hQ with he | hL | he | ⟨hperf, -, -⟩ | hU
  · obtain ⟨e⟩ := he
    exact hsimple e.isSimpleGroup
  · exact hsimple (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL)
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact hsimple e.isSimpleGroup
  · exact eq_top_of_normal_sup_isPGroup S.isPGroup' hBS
  · exact hsimple (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU)

theorem local_chain_eq_of_QT13Five
    {G : Type} [Group G] [Finite G] (T : Sylow 2 G)
    {D B : Subgroup G} (hDperf : ⁅D, D⁆ = D) (hTD : (T : Subgroup G) ≤ normalizer (D : Set G))
    (hBD : B ≤ D) (hB1 : B ≠ ⊥) (hBperf : ⁅B, B⁆ = B)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h5 : QT13Five (↥D ⧸ CFSG.pCore 2 ↥D)) : B = D := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := CFSG.pCore 2 ↥D with hq
  have hqn : q.Normal := CFSG.pCore_normal (p := 2) (G := ↥D)
  have hq2 : IsPGroup 2 q := CFSG.pCore_isPGroup (p := 2) (G := ↥D)
  set π := QuotientGroup.mk' q with hπ
  set B' := B.subgroupOf D with hB'
  have hB'map : B'.map D.subtype = B := by
    rw [hB', subgroupOf_map_subtype, inf_eq_left.2 hBD]
  have hB'perf : ⁅B', B'⁆ = B' := by
    apply map_injective D.subtype_injective
    rw [map_commutator, hB'map, hBperf]
  have hB'1 : B' ≠ ⊥ := by
    intro h
    apply hB1
    rw [← hB'map, h, Subgroup.map_bot]
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) (D ⊔ (T : Subgroup G)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, T.isPGroup', fun h2 => T.not_dvd_index ?_⟩
    rw [← relIndex_top_right, ← relIndex_mul_relIndex (T : Subgroup G) (D ⊔ (T : Subgroup G)) ⊤
      le_sup_right le_top]
    exact h2.mul_right _
  have hTDsyl := hTsyl.inf_of_le_normalizer (N := D) le_sup_left
    (sup_le le_normalizer hTD)
  obtain ⟨SD, hSD⟩ := hTDsyl
  have hSDT : ∀ s ∈ (SD : Subgroup D), (s : G) ∈ (T : Subgroup G) := by
    intro s hs
    have : (s : G) ∈ (SD : Subgroup D).map D.subtype := ⟨s, hs, rfl⟩
    rw [hSD] at this
    exact this.1
  have hBbar : B'.map π = ⊤ := by
    refine five_model_Sylow_normalized_perfect_subgroup_eq_top h5
      (SD.mapSurjective (QuotientGroup.mk'_surjective q)) ?_ ?_ ?_
    · intro h
      apply hB'1
      have hle : B' ≤ q := by
        intro b hb
        have : π b ∈ B'.map π := ⟨b, hb, rfl⟩
        rw [h, mem_bot] at this
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      have h2 : IsPGroup 2 B' := hq2.to_le hle
      by_contra hne
      have : Group.IsPerfect B' := Subgroup.isPerfect_iff.2 hB'perf
      have : Nontrivial B' := (nontrivial_iff_ne_bot B').2 hne
      exact Group.IsPerfect.not_isNilpotent B' h2.isNilpotent
    · rw [← map_commutator, hB'perf]
    · rintro _ ⟨s, hs, rfl⟩
      rw [mem_normalizer_iff]
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective q x
      have hsN : (s : G) ∈ normalizer (B : Set G) := hTB (hSDT s hs)
      constructor
      · rintro ⟨b, hb, hby⟩
        refine ⟨s * b * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hby]⟩
        simp only [SetLike.mem_coe, hB', mem_subgroupOf] at hb ⊢
        simpa using (mem_normalizer_iff.1 hsN b).1 hb
      · rintro ⟨b, hb, hby⟩
        refine ⟨s⁻¹ * b * s, ?_, ?_⟩
        · simp only [SetLike.mem_coe, hB', mem_subgroupOf] at hb ⊢
          have := (mem_normalizer_iff.1 (inv_mem hsN) b).1 hb
          simpa using this
        · rw [map_mul, map_mul, map_inv, hby, hπ]
          group
  have hBq : B' ⊔ q = ⊤ := by
    have h1 := comap_map_eq π B'
    rw [hBbar, comap_top, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hqSD : q ≤ (SD : Subgroup D) := hq2.le_sylow_of_normal SD
  have hBn : B'.Normal := by
    refine normal_of_sup_eq_top (S := q) ?_ hBq
    intro x hx
    have hxT := hSDT x (hqSD hx)
    rw [mem_normalizer_iff]
    intro b
    simp only [hB', mem_subgroupOf]
    simpa using mem_normalizer_iff.1 (hTB hxT) b
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hDperf
  have hB'top : B' = ⊤ := eq_top_of_normal_sup_isPGroup hq2 hBq
  rw [← hB'map, hB'top, ← MonoidHom.range_eq_map, range_subtype]

end CFSG.Quasithin.H13.A7

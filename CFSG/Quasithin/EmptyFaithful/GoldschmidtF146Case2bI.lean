module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bG

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Index

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G} {c : Case2a.Setting T M H K}
  {F : Type} [Field F] [Finite F] {m : ℕ} {P : Fin 2 → Subgroup (E2.StarQuot (H ⊓ M) H)}

omit [Finite G] in
theorem star_mem_normalizers (c : Case2a.Setting T M H K) {t : G} (ht : t ∈ T) :
    ((⟨t, c.le_H' ht⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        Subgroup.normalizer ((E2.star (H ⊓ M) H K : Subgroup (E2.StarQuot (H ⊓ M) H)) :
          Set (E2.StarQuot (H ⊓ M) H)) ∧
      ((⟨t, c.le_H' ht⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        Subgroup.normalizer ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
          Set (E2.StarQuot (H ⊓ M) H)) := by
  have hJH := Case2a.kerIn_le_H M H
  exact ⟨Case2a.mk_mem_normalizer_star (x := ⟨t, c.le_H' ht⟩) c.le_H hJH (c.norm ht),
    Case2a.mk_mem_normalizer_star (x := ⟨t, c.le_H' ht⟩) (inf_le_right.trans c.le_H) hJH
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, c.norm ht⟩)⟩

theorem mem_normalizer_K1_iff (hm : 2 ≤ m)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P) {t : G}
    (ht : t ∈ T) : t ∈ Subgroup.normalizer (K1 c (P 1) : Set G) ↔
      ((⟨t, c.le_H' ht⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        Subgroup.normalizer ((P 1 : Subgroup (E2.StarQuot (H ⊓ M) H)) :
          Set (E2.StarQuot (H ⊓ M) H)) := by
  constructor
  · intro htN
    obtain ⟨hyK, hyU⟩ := star_mem_normalizers c ht
    have hJH := Case2a.kerIn_le_H M H
    have hyW : ((⟨t, c.le_H' ht⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        Subgroup.normalizer ((perfectCore (P 1) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
          Set (E2.StarQuot (H ⊓ M) H)) := by
      rw [← star_K1 (c := c) (hP.le 1)]
      exact Case2a.mk_mem_normalizer_star (x := ⟨t, c.le_H' ht⟩) ((K1_le (P 1)).trans c.le_H)
        hJH htN
    rcases fix_or_swap hP hyK hyU with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exfalso
      refine not_perfectCore_le_inf hP hm ?_
      have h2 : perfectCore (P 0) = perfectCore (P 1) := by
        rw [← h1]
        have := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyW
        rw [← this]
        exact (map_perfectCore (MulAut.conj _).toMonoidHom (P 1)).symm
      exact le_inf (by rw [← h2]; exact perfectCore_le (P 0)) (perfectCore_le (P 1))
  · intro hy
    exact mem_normalizer_perfectCore_Khat (c.le_H' ht) (c.norm ht) hy

theorem relIndex_sOf_K1 (hm : 2 ≤ m)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P)
    (hdiag : E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H (T ⊓ K))) :
    (S1421.sOf T (K1 c (P 1))).relIndex T = 2 := by
  obtain ⟨a, haT, ha⟩ : ∃ a ∈ T, a ∉ Subgroup.normalizer (K1 c (P 1) : Set G) := by
    by_contra hcon
    push Not at hcon
    refine hdiag (P 1) (hP.maxPar 1) (hP.borel 1) fun y hy => ?_
    obtain ⟨h, hhT, rfl⟩ := Case2a.exists_of_mem_star hy
    exact (mem_normalizer_K1_iff hm hP hhT).mp (hcon h hhT)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, haT⟩, fun b => ?_⟩
  have hmem : ∀ t : ↥T, t ∈ (S1421.sOf T (K1 c (P 1))).subgroupOf T ↔
      (t : G) ∈ Subgroup.normalizer (K1 c (P 1) : Set G) := fun t => by
    rw [Subgroup.mem_subgroupOf, S1421.sOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨t.2, h⟩⟩
  rw [hmem, hmem]
  have hmul : ((b * ⟨a, haT⟩ : ↥T) : G) = (b : G) * a := rfl
  rw [hmul]
  have hbT : (b : G) ∈ T := b.2
  have hba : (b : G) * a ∈ T := T.mul_mem hbT haT
  rw [mem_normalizer_K1_iff hm hP hba, mem_normalizer_K1_iff hm hP hbT]
  rw [mem_normalizer_K1_iff hm hP haT] at ha
  set yb : E2.StarQuot (H ⊓ M) H := ((⟨b, c.le_H' hbT⟩ : ↥H) : E2.StarQuot (H ⊓ M) H)
  set ya : E2.StarQuot (H ⊓ M) H := ((⟨a, c.le_H' haT⟩ : ↥H) : E2.StarQuot (H ⊓ M) H)
  have hyba : ((⟨(b : G) * a, c.le_H' hba⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) = yb * ya := rfl
  rw [hyba]
  obtain ⟨hKa, hUa⟩ := star_mem_normalizers c haT
  obtain ⟨hKb, hUb⟩ := star_mem_normalizers c hbT
  have hswap_a : B6.conjSub ya (P 1) = P 0 ∧ B6.conjSub ya (P 0) = P 1 := by
    rcases fix_or_swap hP hKa hUa with ⟨h1, -⟩ | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) ha
    · exact h
  by_cases hb : yb ∈ Subgroup.normalizer ((P 1 : Subgroup (E2.StarQuot (H ⊓ M) H)) :
      Set (E2.StarQuot (H ⊓ M) H))
  · right
    refine ⟨hb, fun hab => ha ?_⟩
    have := Subgroup.mul_mem _ (inv_mem hb) hab
    simpa using this
  · left
    refine ⟨?_, hb⟩
    rcases fix_or_swap hP hKb hUb with ⟨h1, -⟩ | ⟨h1, h0⟩
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hb
    · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      show B6.conjSub (yb * ya) (P 1) = P 1
      rw [B6.conjSub_mul, hswap_a.1, h0]

end Index

end CFSG.Quasithin.F146Field.Case2b

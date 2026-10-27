module

public import CFSG.Monster.B.CTIB.FourClasses
public import Certificates.Certificate3123
public import Certificates.Certificate3100
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def tableSixRows : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(4, 6, 34560, 128, 2168, 3), (5, 6, 32768, 128, 2158, 5), (6, 6, 64, 64, 1860, 1),
    (7, 6, 128, 128, 2048, 0), (8, 6, 64, 64, 2168, 3), (9, 8, 256, 256, 2168, 3),
    (10, 8, 17920, 512, 2168, 3), (11, 8, 256, 256, 2048, 0), (12, 10, 4096, 2048, 2168, 3),
    (13, 10, 2048, 2048, 2158, 5)]

@[expose] def qSizes : List ℕ := [128, 128, 64, 128, 64, 256, 512, 256, 2048, 2048]

theorem orbitRecs_reps :
    (43, 128) ∈ orbitRecs 6 ∧ (61, 128) ∈ orbitRecs 6 ∧ (10541, 64) ∈ orbitRecs 6 ∧
      (26925, 128) ∈ orbitRecs 6 ∧ (46090, 64) ∈ orbitRecs 6 ∧ (0, 256) ∈ orbitRecs 8 ∧
      (128, 512) ∈ orbitRecs 8 ∧ (35764, 256) ∈ orbitRecs 8 ∧ (107, 2048) ∈ orbitRecs 10 ∧
      (66038, 2048) ∈ orbitRecs 10 :=
  Certificates.certificate3123

theorem ncard_qClass_conj {g : Sbp} (hg : g.unop ∈ Jbar) (t : Sbp) :
    (qClass (g⁻¹ * t * g)).ncard = (qClass t).ncard := by
  have hg' : (g⁻¹).unop ∈ Jbar := by
    rw [unop_inv]
    exact Jbar.inv_mem hg
  have e : qClass (g⁻¹ * t * g) = (fun u => g⁻¹ * u * g) '' qClass t := by
    ext u
    constructor
    · rintro ⟨e, he, rfl⟩
      have he' : g * e * g⁻¹ ∈ Qs := by
        simpa only [inv_inv] using conj_mem_Qs hg' he
      exact ⟨(g * e * g⁻¹)⁻¹ * t * (g * e * g⁻¹), ⟨g * e * g⁻¹, he', rfl⟩, by group⟩
    · rintro ⟨u', ⟨e, he, rfl⟩, rfl⟩
      exact ⟨g⁻¹ * e * g, conj_mem_Qs hg he, by group⟩
  rw [e, Set.ncard_image_of_injective _ fun a b h => by simpa using h]

theorem invariants_of_mem_jClass
    {u t : Sbp} (h : u ∈ jClass t) :
    ((βr u) - 1).rank = ((βr t) - 1).rank ∧ (qClass u).ncard = (qClass t).ncard := by
  refine ⟨rank_beta_conj (isConj_of_mem_jClass h), ?_⟩
  obtain ⟨g, hg, rfl⟩ := h
  exact ncard_qClass_conj hg t

theorem ncard_qClass_rs
    {i : ℕ}
    (hi : i ∈ Finset.Icc 4 13) :
    (qClass (rs i)).ncard = qSizes.getD (i - 4) 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := orbitRecs_reps
  have q6 : IsRank 6 := .inl rfl
  have q8 : IsRank 8 := .inr (.inl rfl)
  have q10 : IsRank 10 := .inr (.inr rfl)
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  interval_cases i
  · exact (qOrbit_facts q6 h1).2.1
  · exact (qOrbit_facts q6 h2).2.1
  · exact (qOrbit_facts q6 h3).2.1
  · exact (qOrbit_facts q6 h4).2.1
  · exact (qOrbit_facts q6 h5).2.1
  · exact (qOrbit_facts q8 h6).2.1
  · exact (qOrbit_facts q8 h7).2.1
  · exact (qOrbit_facts q8 h8).2.1
  · exact (qOrbit_facts q10 h9).2.1
  · exact (qOrbit_facts q10 h10).2.1

theorem invariants_separate : ∀ i ∈ Finset.Icc 4 13, ∀ j ∈ Finset.Icc 4 13,
    repRanks.getD i 0 = repRanks.getD j 0 → qSizes.getD (i - 4) 0 = qSizes.getD (j - 4) 0 →
      i = j := by
  decide

theorem eq_of_mem_jClass_rs
    {i j : ℕ}
    (hi : i ∈ Finset.Icc 4 13)
    (hj : j ∈ Finset.Icc 4 13)
    (h : rs i ∈ jClass (rs j)) : i = j := by
  obtain ⟨hr, hq⟩ := invariants_of_mem_jClass h
  have hi' : i < 14 := by
    rw [Finset.mem_Icc] at hi
    omega
  have hj' : j < 14 := by
    rw [Finset.mem_Icc] at hj
    omega
  rw [rank_rs hi', rank_rs hj'] at hr
  rw [ncard_qClass_rs hi, ncard_qClass_rs hj] at hq
  exact invariants_separate i hi j hj hr hq

theorem coset_jcover
    {k : ℕ} (hk : IsRank k) {t : Sbp} (ht : t ∈ cosetInv k) :
    ∃ g ∈ Jbar.op, ∃ i ∈ Finset.Icc 4 13, g⁻¹ * t * g = rs i := by
  have hc := native_three_coset_involution_cover
  have conv : ∀ {S : Finset ℕ}, S ⊆ Finset.Icc 4 13 →
      (∃ g ∈ Jbar.op, ∃ i ∈ S, g⁻¹ * t * g = rs i) →
        ∃ g ∈ Jbar.op, ∃ i ∈ Finset.Icc 4 13, g⁻¹ * t * g = rs i := by
    rintro S hS ⟨g, hg, i, hi, e⟩
    exact ⟨g, hg, i, hS hi, e⟩
  rcases hk with rfl | rfl | rfl
  · exact conv (by decide) (hc.1 t ht)
  · exact conv (by decide) (hc.2.1 t ht)
  · exact conv (by decide) (hc.2.2.1 t ht)

theorem exists_jClass_rs
    {t : Sbp} (htJ : t.unop ∈ Jbar) (ht : t * t = 1) (hq : t ∉ Qs) :
    ∃ i ∈ Finset.Icc 4 13, t ∈ jClass (rs i) := by
  set kt := piH ⟨t, htJ⟩ with hkt
  have hk2 : kt * kt = 1 := by
    rw [hkt, ← map_mul, ← map_one piH]
    congr 1
    exact Subtype.ext ht
  have hk1 : kt ≠ 1 := fun h => hq ((piH_eq_one_iff _).1 h)
  have main : ∀ r, IsRank r → rkW kt = r → ∃ i ∈ Finset.Icc 4 13, t ∈ jClass (rs i) := by
    intro r hr hrk
    have hc := kv_conj_of_rank co2_involution_input hk2 hk1 (piH_hs_sq hr) (piH_hs_ne_one hr)
      (by rw [hrk, rkW_hs hr])
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    obtain ⟨g, rfl⟩ := piH_surjective c
    set u : Sbp := g.val * t * g.val⁻¹ with hu
    have huJ : u.unop ∈ Jbar :=
      Jbar.op.mul_mem (Jbar.op.mul_mem g.2 htJ) (Jbar.op.inv_mem g.2)
    have hpu : piH ⟨u, huJ⟩ = piH ⟨hs r, hs_mem_Jbar hr⟩ := by
      rw [← hc, hkt, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hq' : (hs r)⁻¹ * u ∈ Qs := by
      have h1 : piH (⟨hs r, hs_mem_Jbar hr⟩⁻¹ * ⟨u, huJ⟩) = 1 := by
        rw [map_mul, hpu, ← map_mul, inv_mul_cancel, map_one]
      exact (piH_eq_one_iff _).1 h1
    have hmem : u ∈ cosetInv r := by
      refine ⟨⟨(hs r)⁻¹ * u, hq', by group⟩, ?_⟩
      rw [hu]
      calc g.val * t * g.val⁻¹ * (g.val * t * g.val⁻¹) = g.val * (t * t) * g.val⁻¹ := by group
        _ = 1 := by rw [ht]; group
    obtain ⟨g', hg', i, hi, e⟩ := coset_jcover hr hmem
    refine ⟨i, hi, g'⁻¹ * g.val, Jbar.op.mul_mem (Jbar.op.inv_mem hg') g.2, ?_⟩
    rw [← e, hu]
    group
  rcases kv_rank_cases co2_involution_input hk2 hk1 with h | h | h
  · exact main 6 (.inl rfl) h
  · exact main 8 (.inr (.inl rfl)) h
  · exact main 10 (.inr (.inr rfl)) h

theorem existsUnique_jClass_rs
    {t : Sbp} (htJ : t.unop ∈ Jbar)
    (ht : t * t = 1) (hq : t ∉ Qs) :
    ∃! i, i ∈ Finset.Icc 4 13 ∧ t ∈ jClass (rs i) := by
  obtain ⟨i, hi, hti⟩ := exists_jClass_rs htJ ht hq
  refine ⟨i, ⟨hi, hti⟩, fun j ⟨hj, htj⟩ => ?_⟩
  have h : rs j ∈ jClass (rs i) := by
    rw [← jClass_eq_of_mem hti, jClass_eq_of_mem htj]
    exact mem_jClass_self _
  exact eq_of_mem_jClass_rs hj hi h

theorem rec_rep
    {k : ℕ} (hk : IsRank k) {r : ℕ × ℕ × ℕ} (hr : r ∈ fusionRecsN k) :
    ∃ j ∈ Finset.Icc 4 13, cosetElt k r.2.2 = rs j := by
  obtain ⟨h6, h8, h10⟩ := fusionRecs_eq
  rcases hk with rfl | rfl | rfl
  · rw [h6] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
    · exact ⟨6, by decide, rfl⟩
    · exact ⟨7, by decide, rfl⟩
    · exact ⟨8, by decide, rfl⟩
  · rw [h8] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨9, by decide, rfl⟩
    · exact ⟨10, by decide, rfl⟩
    · exact ⟨11, by decide, rfl⟩
  · rw [h10] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨12, by decide, rfl⟩
    · exact ⟨13, by decide, rfl⟩

theorem fClass_subset_jClass
    {k : ℕ} (hk : IsRank k) (t : Sbp) : fClass k t ⊆ jClass t := by
  rintro u ⟨f, hf, rfl⟩
  exact ⟨f, fuseGroup_le k hk hf, rfl⟩

theorem jClass_inter_cosetInv
    {k : ℕ} (hk : IsRank k) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ fusionRecsN k)
    {i : ℕ} (hi : i ∈ Finset.Icc 4 13) (hri : cosetElt k r.2.2 = rs i) :
    jClass (rs i) ∩ cosetInv k = fClass k (rs i) := by
  ext u
  constructor
  · rintro ⟨hu, hu'⟩
    obtain ⟨r', hr', hur'⟩ := cover_fClass hk hu'
    obtain ⟨j, hj, hrj⟩ := rec_rep hk hr'
    rw [hrj] at hur'
    have h1 : jClass u = jClass (rs j) := jClass_eq_of_mem (fClass_subset_jClass hk _ hur')
    have h2 : rs i ∈ jClass (rs j) := by
      rw [← h1, jClass_eq_of_mem hu]
      exact mem_jClass_self _
    rw [eq_of_mem_jClass_rs hi hj h2]
    exact hur'
  · intro hu
    refine ⟨fClass_subset_jClass hk _ hu, ?_⟩
    rw [← hri] at hu
    exact fClass_subset hk hr hu

theorem ncard_jClass_inter_cosetInv
    {k : ℕ} (hk : IsRank k)
    {r : ℕ × ℕ × ℕ}
    (hr : r ∈ fusionRecsN k) {i : ℕ} (hi : i ∈ Finset.Icc 4 13)
    (hri : cosetElt k r.2.2 = rs i) :
    (jClass (rs i) ∩ cosetInv k).ncard = r.2.1 := by
  rw [jClass_inter_cosetInv hk hr hi hri, ← hri]
  exact (fOrbit_facts hk hr).2.1

theorem cosetElt_unop_mem_Jbar
    {k : ℕ} (hk : IsRank k) (n : ℕ) :
    (cosetElt k n).unop ∈ Jbar :=
  Jbar.op.mul_mem (hs_mem_Jbar hk) (Ebar_le_Jbar (qS_mem n))

theorem cosetElt_not_mem_Qs
    {k : ℕ} (hk : IsRank k) (n : ℕ) :
    cosetElt k n ∉ Qs := by
  intro h
  have h1 : hs k ∈ Qs := by
    have := Qs.mul_mem h (Qs.inv_mem (qS_mem n))
    rwa [cosetElt, mul_inv_cancel_right] at this
  exact piH_hs_ne_one hk ((piH_eq_one_iff _).2 h1)

theorem tableSix_row_of
    {i k q n m rep ρ b : ℕ} (hk : IsRank k)
    (hi : i ∈ Finset.Icc 4 13)
    (hrec : (q, n, rep) ∈ fusionRecsN k) (hri : cosetElt k rep = rs i)
    (horb : (rep, m) ∈ orbitRecs k) (hρ : repRanks.getD i 0 = ρ) (hb : IsConj (rs i) (rs b)) :
    (rs i).unop ∈ Jbar ∧ rs i ∉ Qs ∧ rs i ∈ cosetInv k ∧
      (jClass (rs i) ∩ cosetInv k).ncard = n ∧ (qClass (rs i)).ncard = m ∧
      ((βr (rs i)) - 1).rank = ρ ∧ IsConj (rs i) (rs b) := by
  have hi' : i < 14 := by
    rw [Finset.mem_Icc] at hi
    omega
  refine ⟨hri ▸ cosetElt_unop_mem_Jbar hk rep, hri ▸ cosetElt_not_mem_Qs hk rep,
    hri ▸ fClass_subset hk hrec ⟨1, (fuseGroup k).one_mem, by group⟩,
    ncard_jClass_inter_cosetInv hk hrec hi hri, hri ▸ (qOrbit_facts hk horb).2.1,
    (rank_rs hi').trans hρ, hb⟩

theorem native_table_six_classes :
    (∀ t : Sbp, t.unop ∈ Jbar → t * t = 1 → t ∉ Qs →
      ∃! i, i ∈ Finset.Icc 4 13 ∧ t ∈ jClass (rs i)) ∧
    (∀ i ∈ Finset.Icc 4 13, ∀ j ∈ Finset.Icc 4 13, rs i ∈ jClass (rs j) → i = j) ∧
    tableSixRows.map (·.1) = List.range' 4 10 ∧
    ∀ i k n m ρ b : ℕ, (i, k, n, m, ρ, b) ∈ tableSixRows →
      (rs i).unop ∈ Jbar ∧ rs i ∉ Qs ∧ rs i ∈ cosetInv k ∧
        (jClass (rs i) ∩ cosetInv k).ncard = n ∧ (qClass (rs i)).ncard = m ∧
        ((βr (rs i)) - 1).rank = ρ ∧ IsConj (rs i) (rs b) := by
  refine ⟨fun t htJ ht hq => existsUnique_jClass_rs htJ ht hq,
    fun i hi j hj h => eq_of_mem_jClass_rs hi hj h, rfl, ?_⟩
  intro i k n m ρ b h
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := orbitRecs_reps
  obtain ⟨h6, h8, h10⟩ := fusionRecs_eq
  have q6 : IsRank 6 := .inl rfl
  have q8 : IsRank 8 := .inr (.inl rfl)
  have q10 : IsRank 10 := .inr (.inr rfl)
  simp only [tableSixRows, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact tableSix_row_of (q := 270) (rep := 43) q6 (by decide) (by rw [h6]; simp) rfl o1 rfl
      (fusion_conj_at 1 (by norm_num))
  · exact tableSix_row_of (q := 256) (rep := 61) q6 (by decide) (by rw [h6]; simp) rfl o2 rfl
      (IsConj.refl _)
  · exact tableSix_row_of (q := 1) (rep := 10541) q6 (by decide) (by rw [h6]; simp) rfl o3 rfl
      (fusion_conj_at 2 (by norm_num))
  · exact tableSix_row_of (q := 1) (rep := 26925) q6 (by decide) (by rw [h6]; simp) rfl o4 rfl
      (fusion_conj_at 3 (by norm_num))
  · exact tableSix_row_of (q := 1) (rep := 46090) q6 (by decide) (by rw [h6]; simp) rfl o5 rfl
      (fusion_conj_at 4 (by norm_num))
  · exact tableSix_row_of (q := 1) (rep := 0) q8 (by decide) (by rw [h8]; simp) rfl o6 rfl
      (fusion_conj_at 5 (by norm_num))
  · exact tableSix_row_of (q := 35) (rep := 128) q8 (by decide) (by rw [h8]; simp) rfl o7 rfl
      (fusion_conj_at 6 (by norm_num))
  · exact tableSix_row_of (q := 1) (rep := 35764) q8 (by decide) (by rw [h8]; simp) rfl o8 rfl
      (fusion_conj_at 7 (by norm_num))
  · exact tableSix_row_of (q := 2) (rep := 107) q10 (by decide) (by rw [h10]; simp) rfl o9 rfl
      (fusion_conj_at 8 (by norm_num))
  · exact tableSix_row_of (q := 1) (rep := 66038) q10 (by decide) (by rw [h10]; simp) rfl o10 rfl
      (fusion_conj_at 9 (by norm_num))

end CFSG.Monster.B.CTIB

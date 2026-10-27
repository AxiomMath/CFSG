module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.Quasithin.H13.Ch4.I436

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

theorem centralizer_card_of_reps {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ data, Nat.card (centralizerIn Q.originalSubgroup u) = Nat.card d.2 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d, hd, ?_⟩
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem m22_inv_centralizer_card :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hdc⟩ := centralizer_card_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) [(m22Rep1, m22CentQ1.originalSubgroup)] (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hdc, hKc1]

theorem m22_outer_centralizer_card :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 320 ∨
        Nat.card (centralizerIn NativeSporadic.M22 u) = 1344 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hdc⟩ := centralizer_card_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB)
    m22Delta hg₀
    [(m22OutRep1, m22OutCentQ1.originalSubgroup), (m22OutRep2, m22OutCentQ2.originalSubgroup)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
      · refine ⟨hK2, ?_⟩
        rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card]) u hu ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (hdc.trans hKc1)
  · exact Or.inr (hdc.trans hKc2)

theorem m23_inv_centralizer_card :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hdc⟩ := centralizer_card_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) [(m23Rep1, m23CentQ1.originalSubgroup)] (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hdc, hKc1]

end CFSG.Quasithin.H13.Ch4.I436

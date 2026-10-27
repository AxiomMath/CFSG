module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem sylow_center_of_baseCert [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (qs : List (Γ × Γ))
    (z g gi h hi : Γ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : BaseCert n B (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray))
      (tab n z).toArray (tab n g).toArray (tab n gi).toArray (tab n h).toArray
      (tab n hi).toArray Ts par cl k) :
    ∃ Q : Subgroup Γ, IsPGroup 2 ↥Q ∧ ¬ 2 ∣ Q.index ∧
      ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
  obtain ⟨hinv, -, -, hEnum, hsize, hcen, -, -, -⟩ := hcert
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := fun p hp =>
    hinv_of p.1 p.2 (hinv _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  let gens : List Γ := qs.map Prod.fst
  have hG : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.fst =
      genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.snd =
      genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hEnum
  rw [hG] at hcen
  have hP : ∀ p ∈ ptsOf B (genTabs n gens), p < n := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  let Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens}
  have hQmem : ∀ x : Γ, x ∈ Q ↔ rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := by
    intro x
    refine ⟨benum_closed hB gens Ts par cl hEnum x, fun hx => ?_⟩
    obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
    have hiT' : i < Ts.size := by simpa using hi
    obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts par cl hEnum i hiT'
    have : rt n (ptsOf B (genTabs n gens)) y = rt n (ptsOf B (genTabs n gens)) x := by
      rw [hyT, getElem!_pos Ts i hiT']
      simpa using hiT
    rwa [← rt_injective hB hBP hbase this]
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hQindex : Q.index = m := by
    have h1 := Q.card_mul_index
    rw [hcardQ, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  refine ⟨Q, IsPGroup.of_card hcardQ, ?_, ?_⟩
  · rw [hQindex]
    exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)
  · intro c hcQ hcc
    have hcT : rt n (ptsOf B (genTabs n gens)) c ∈ Ts.toList := (hQmem c).mp hcQ
    have hcomm := rt_comm_clause hB gens c fun s hs =>
      hcc s (Subgroup.subset_closure hs)
    rcases hcen _ hcT hcomm with h1 | h1
    · left
      exact rt_injective hB hBP hbase (by rw [h1, rt_one hP])
    · right
      exact rt_injective hB hBP hbase (by rw [h1, rt_one_mul hP])

theorem sylow_center_of_baseCertS [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m)
    (hm : Odd m)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    ∃ (Q : Subgroup Γ) (z : Γ), IsPGroup 2 ↥Q ∧ ¬ 2 ∣ Q.index ∧
      ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hc' := hc
  rw [← hE' zn hz, ← hE' gn hg, ← hE' gin hgi, ← hE' hn hh, ← hE' hin hhi] at hc'
  have : (qp.map fun p => (T[p.1]!, T[p.2]!)) =
      (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1)).map
        (fun p => ((tab n p.1).toArray, (tab n p.2).toArray)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
  rw [this] at hc'
  obtain ⟨Q, hQ2, hQi, hQc⟩ := sylow_center_of_baseCert B hB hbase
    (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1))
    ((slpElts a b prog).getD zn 1) ((slpElts a b prog).getD gn 1) ((slpElts a b prog).getD gin 1)
    ((slpElts a b prog).getD hn 1) ((slpElts a b prog).getD hin 1) Ts par cl k m hcard hm hc'
  exact ⟨Q, _, hQ2, hQi, hQc⟩

end CFSG.Quasithin.ZPInv

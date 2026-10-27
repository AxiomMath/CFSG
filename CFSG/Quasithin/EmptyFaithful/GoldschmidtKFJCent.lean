module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFJBase
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.ComponentClassification.J2Cover

theorem not_isSolvable_ofArrays_triangle {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)}
    {hk : 2 ≤ S.size} {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)} {chunks : ℕ}
    (hc : rawChainOK n (S.extract 0 2) S (base.map Fin.val).toArray W chunks = true)
    (hch : 0 < chunks) {wx wy : List ℕ} (hwx : ∀ l ∈ wx, l < 2) (hwy : ∀ l ∈ wy, l < 2)
    {N : ℕ} (hN : N.Coprime 6) (hx2 : ∀ b ∈ base, imgWord S wx (imgWord S wx b) = b)
    (hy3 : ∀ b ∈ base, imgWord S wy (imgWord S wy (imgWord S wy b)) = b)
    (hxy : ∀ b ∈ base, (fun j => imgWord S wx (imgWord S wy j))^[N] b = b) (p : Fin n)
    (hp : imgWord S wx p ≠ p) :
    ¬ Group.IsSolvable ↥(RawSchreierDatum.ofArrays n hn S 2 hk base hb W).originalSubgroup := by
  have hQ := ofArrays_valid (hn := hn) (hk := hk) (hb := hb) hch hc
  have hmem : ∀ l, l < 2 → permOfArr n S[l]! ∈
      (RawSchreierDatum.ofArrays n hn S 2 hk base hb W).originalSubgroup := fun l hl => by
    rw [ofArrays_originalSubgroup]
    exact Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hbase := RawSchreierDatum.ofArrays_base_toList (n := n) (hn := hn) (S := S) (k := 2)
    (hk := hk) (base := base) (hb := hb) (W := W)
  refine not_isSolvable_of_chain_triangle _ hQ S (fun l => permOfArr n S[l]!)
    (fun l hl => rep_permOfArr_of_chainOK hc hl) (wx := wx) (wy := wy)
    (fun l hl => ⟨by have := hwx l hl; have := hk; omega, hmem l (hwx l hl)⟩)
    (fun l hl => ⟨by have := hwy l hl; have := hk; omega, hmem l (hwy l hl)⟩) hN
    (fun b hb' => hx2 b (by rw [hbase] at hb'; exact hb'))
    (fun b hb' => hy3 b (by rw [hbase] at hb'; exact hb'))
    (fun b hb' => hxy b (by rw [hbase] at hb'; exact hb')) p hp

theorem not_isSolvable_cent2B :
    ¬ Group.IsSolvable ↥cent2BChain.originalSubgroup := by
  have hc : rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong
      (([0, 3] : List (Fin 315)).map Fin.val).toArray cent2BWords 4 = true := cent2B_check.1
  refine not_isSolvable_ofArrays_triangle (wx := [1, 1, 0, 0, 0, 0]) (wy := [1, 1]) (N := 5)
    (chunks := 4) hc (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (0 : Fin 315)
    (by decide +kernel)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel

theorem not_isSolvable_cent2A :
    ¬ Group.IsSolvable ↥cent2AChain.originalSubgroup := by
  have hc : rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong
      (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray cent2AWords 4 = true := cent2A_check.1
  refine not_isSolvable_ofArrays_triangle (wx := [1, 1, 1, 0, 1, 0]) (wy := [1, 0, 1, 0]) (N := 5)
    (chunks := 4) hc (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (0 : Fin 315)
    (by decide +kernel)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem not_isSolvable_centOuter :
    ¬ Group.IsSolvable ↥centOuterChain.originalSubgroup := by
  have hc : rawChainOK 315 (centOuterStrong.extract 0 2) centOuterStrong
      (([0, 3] : List (Fin 315)).map Fin.val).toArray centOuterWords 4 = true := centOuter_check.1
  refine not_isSolvable_ofArrays_triangle (wx := [1, 0, 1, 1, 0, 1, 0]) (wy := [0]) (N := 7)
    (chunks := 4) hc (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (0 : Fin 315)
    (by decide +kernel)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide +kernel

theorem not_isSolvable_P : ¬ Group.IsSolvable ↥P := by
  rw [← autChain_originalSubgroup]
  refine not_isSolvable_ofArrays_triangle (wx := [0]) (wy := [1]) (N := 7) (chunks := 4)
    autChain_ok (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (0 : Fin 315)
    (by decide +kernel)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide +kernel

end CFSG.Quasithin.SBd19F

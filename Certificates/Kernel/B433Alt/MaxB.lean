module

public import Certificates.Kernel.B433Alt.Exact
public import Certificates.Kernel.B433Alt.ArithC
public import CFSG.Certificates.Kernel.B433Alt.ArithSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CFSG.YGroups.DCE.B433 CFSG.Certificates.TwDce

#kc_forall_tree ar_all (fun k => CFSG.KD.B4AR.arChk k = true) 13 CFSG.KD.B4AR.ar

theorem arith_data : (∀ pe ∈ CFSG.KD.B4AR.F, Nat.Prime pe.1) ∧
    (CFSG.KD.B4AR.F.map fun pe => pe.1 ^ pe.2).prod = 1015970529280000 ∧
    CFSG.KD.B4AR.A.length = (divsOf CFSG.KD.B4AR.F).length ∧
    (∀ a ∈ CFSG.KD.B4AR.A, a < CFSG.KD.B4AR.M.length) ∧ (∀ m ∈ CFSG.KD.B4AR.M, 0 < m) ∧
    CFSG.KD.B4AR.M.length = 13 := by
  refine ⟨?_, ?_⟩
  · have h : CFSG.KD.B4AR.F = [(2, 23), (5, 4), (7, 1), (19, 1), (31, 1), (47, 1)] := by
      decide +kernel
    rw [h]
    intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · decide +kernel

theorem idx_data : CFSG.KD.B4AR.idx.Nodup ∧
    (Ev.erase (idxOf 0)).image nodeAt = CFSG.KD.B4AR.idx.toFinset ∧
    (∀ i, CFSG.KD.B4AR.wv (nodeAt i) = vN i) ∧
    (∀ j ∈ CFSG.KD.B4AR.idx, 0 < CFSG.KD.B4AR.wv j) := by
  refine ⟨by decide +kernel, by decide +kernel, fun i => rfl, by decide +kernel⟩

theorem nodeAt_injective : Function.Injective nodeAt := by decide +kernel

theorem arith_even : ∀ U ⊆ Ev, idxOf 0 ∈ U → (∑ i ∈ U, vN i) ∣ ∑ i ∈ Ev, vN i →
    U = {idxOf 0} ∨ U = Ev := by
  classical
  intro U hUE h0 hdvd
  obtain ⟨hF, hT, hA, hAk, hm, hM⟩ := arith_data
  obtain ⟨hnd, himg, hw, hpos⟩ := idx_data
  have hsumI : 1 + ∑ j ∈ CFSG.KD.B4AR.idx.toFinset, CFSG.KD.B4AR.wv j = 1015970529280000 := by
    rw [← himg, Finset.sum_image fun a _ b _ h => nodeAt_injective h]
    simp only [hw]
    rw [← vN_idx0, Finset.add_sum_erase _ _ idx0_mem, sum_Ev]
  have key := arith_sound CFSG.KD.B4AR.wv CFSG.KD.B4AR.idx CFSG.KD.B4AR.F CFSG.KD.B4AR.A
    CFSG.KD.B4AR.M 1015970529280000 hF hT hsumI hpos hm hA hAk
    (fun k hk => ar_all k (by rw [hM] at hk; exact hk))
  have hsub : (U.erase (idxOf 0)).image nodeAt ⊆ CFSG.KD.B4AR.idx.toFinset := by
    rw [← himg]
    exact Finset.image_subset_image (Finset.erase_subset_erase _ hUE)
  have hsU : ∑ i ∈ U, vN i = 1 + ∑ j ∈ (U.erase (idxOf 0)).image nodeAt, CFSG.KD.B4AR.wv j := by
    rw [Finset.sum_image fun a _ b _ h => nodeAt_injective h, ← Finset.add_sum_erase _ _ h0,
      vN_idx0]
    simp only [hw]
  rw [hsU, sum_Ev] at hdvd
  rcases key _ hsub hdvd with h | h
  · left
    have h' : U.erase (idxOf 0) = ∅ := Finset.image_eq_empty.1 h
    rw [← Finset.insert_erase h0, h']
    rfl
  · right
    rw [← himg] at h
    have h2 := Finset.image_injective nodeAt_injective h
    rw [← Finset.insert_erase h0, ← Finset.insert_erase idx0_mem, h2]

section

theorem psi_range_maximal (hG : 4154781481226426191177580544000000 ≤ Nat.card B433)
    (L : Subgroup B433) (hL : psi.range ≤ L) : L = psi.range ∨ L = ⊤ := by
  have := finite_Ghat
  have hHh : Hh hsw = psi.range.map (inlB : B433 →* Ghat hsw) := by
    rw [Hh, psiG, MonoidHom.range_comp]
  have hHL : Hh hsw ≤ L.map (inlB : B433 →* Ghat hsw) := by
    rw [hHh]
    exact Subgroup.map_mono hL
  have hLK : L.map (inlB : B433 →* Ghat hsw) ≤ (inlB : B433 →* Ghat hsw).range := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have htot : 4089470473293004800 * ∑ i ∈ Ev, vN i ≤ Nat.card (inlB : B433 →* Ghat hsw).range := by
    rw [sum_Ev, MonoidHom.range_eq_map, Subgroup.card_map_of_injective inlB_injective,
      Subgroup.card_top]
    calc 4089470473293004800 * 1015970529280000 = 4154781481226426191177580544000000 := by norm_num
      _ ≤ Nat.card B433 := hG
  have hx0 : (twist).x (idxOf 0) ∈ Hh hsw := (twist).base_mem
  rcases eq_or_eq_of_cover (Hh hsw) (inlB : B433 →* Ghat hsw).range
      (L.map (inlB : B433 →* Ghat hsw)) (twist).S (twist).x vN Ev (idxOf 0) (twist).S_conj
      ((twist).exists_eq (u_mul_self hsw) (u_conj_Th hsw) (closure_Hh_u hsw))
      relIndex_le_v x_mem_inl_iff (hHL.trans hLK) hHL hLK _ card_Hh_le htot hx0 vN_idx0
      arith_even with h | h
  · left
    rw [hHh] at h
    exact Subgroup.map_injective inlB_injective h
  · right
    rw [MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective inlB_injective h

end

end CertificateChecks.KernelB433

end

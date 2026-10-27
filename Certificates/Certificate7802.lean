module

public import CFSG.Milestones.ASVolI.F48.D43.ChainDefs
public import Certificates.Kernel.D43.GenCube
public import Certificates.Kernel.D43.TreeX0
public import Certificates.Kernel.D43.TreeX1
public import Certificates.Kernel.D43.TreeS
public import Certificates.Kernel.D43.Bind
public import CFSG.Certificates.Kernel.D43.KeySound
public import CFSG.Certificates.Kernel.D43.TreeGlue
public import CFSG.Milestones.ASVolI.F48.D43.Model

public section

open CFSG CFSG.ASVolI CFSG.KC.D43 CertificateChecks.KernelD43

namespace CertificateChecks.KernelD43

@[expose] noncomputable def chGen (k : ℕ) : ↥burnsideF48d_X :=
  if h : k < 8 then ⟨burnsideF48d_γ k, burnsideF48d_γ_mem ⟨k, h⟩⟩ else 1

theorem chGen_tab : TabRep GX.F chGen := by
  intro k hk p
  obtain ⟨e, he⟩ := exists_perm_of_cube (F := GX.F) (k := k) fun c hc => by
    have h := genCube (13 * k + c) (by change 13 * k + c < 104; omega)
    change cubeChunk GX.F ((13 * k + c) / 13) ((13 * k + c) % 13) = true at h
    rwa [show (13 * k + c) / 13 = k by omega, show (13 * k + c) % 13 = c by omega] at h
  have hrep : CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_toT (burnsideF48d_gen k)) e :=
    burnsideF48d_rep_of_apply (by
      simp only [burnsideF48d_gen, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn])
      fun q => (he q).trans (gen_tab hk q.2).symm
  have hγ : burnsideF48d_γ k = e := burnsideF48d_perm_eq hrep
  unfold chGen
  rw [dif_pos hk]
  change ((burnsideF48d_γ k) p : ℕ) = _
  rw [hγ, he]

theorem TW_eq : ∀ j < 17, TW j = encW (burnsideF48d_LW.getD j []) := by
  decide +kernel

theorem LW_len : ∀ j < 17, (burnsideF48d_LW.getD j []).length ≤ 24 := by
  decide +kernel

theorem lG_chGen (j : Fin 17) : lG chGen TW j = burnsideF48d_L j := by
  unfold lG
  rw [TW_eq j j.2, wG_encW chGen _ 24 (LW_len j j.2)]
  apply Subtype.ext
  have e : (fun k : Fin 8 => burnsideF48d_γ k) =
      fun k : Fin 8 => burnsideF48d_X.subtype (chGen k) := by
    funext k
    simp [chGen, k.2]
  change burnsideF48d_X.subtype _ = burnsideF48s_ev (fun k : Fin 8 => burnsideF48d_γ k) _
  rw [e, burnsideF48s_ev_map]

theorem chainBound_of {C : List (Fin 26572 × Finset (Fin 17) × ℕ)} {B lo : ℕ}
    (hB : ∀ t (ht : t < C.length), ((C[t].1 : Fin 26572) : ℕ) = bAt B t)
    (hlev : ∀ i (hi : i < C.length), ∃ M ℓ o n, fixAll GX.F TW B i lo M = true ∧
      (∀ c < n, treeChunk GX.F TW TR TQ ℓ o C[i].2.2 C[i].1 M c = true) ∧
      C[i].2.2 ≤ 256 * n ∧ M < 2 ^ 17 ∧
      ∀ j : Fin 17, M.testBit j = true ↔ j ∈ (C.getD i (0, ∅, 0)).2.1) :
    burnsideF48d_ChainBound C := by
  intro i hi
  obtain ⟨M, ℓ, o, n, hfix, htree, hs, hM, hS⟩ := hlev i hi
  have e : C.getD i (0, ∅, 0) = C[i] := by simp [hi]
  rw [e] at hS
  refine ⟨fun j hj t ht => ?_, ?_⟩
  · have hb : bAt B t < 26572 := by rw [← hB t (by omega)]; exact C[t].1.2
    have h := (fixAll_spec chGen_tab hfix j.2 ((hS j).2 hj)).2 t ht hb
    rw [lG_chGen] at h
    have e : (⟨bAt B t, hb⟩ : Fin 26572) = C[t].1 := Fin.ext (hB t (by omega)).symm
    rw [e] at h
    exact h
  · rw [← maskGroup_eq hM hS lG_chGen]
    exact le_ncard_orbit_of_trees chGen_tab hs C[i].1.2 htree

theorem one_chunk {ℓ o s b M : ℕ} (h : treeChunk GX.F TW TR TQ ℓ o s b M 0 = true) :
    ∀ c < 1, treeChunk GX.F TW TR TQ ℓ o s b M c = true := fun c hc => by
  obtain rfl : c = 0 := by omega
  exact h

theorem chainX_bound : burnsideF48d_ChainBound burnsideF48d_chainXL := by
  have hf := fixX
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩ := hf
  refine chainBound_of (B := D43BX) (lo := 0) (by decide +kernel) fun i hi => ?_
  change i < 8 at hi
  interval_cases i
  · exact ⟨131071, 0, 0, 104, f0, treeX0, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨131069, 1, 26572, 77, f1, treeX1, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨253, 2, 46255, 1, f2, one_chunk treeX2, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨252, 3, 46283, 1, f3, one_chunk treeX3, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨252, 4, 46284, 1, f4, one_chunk treeX4, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨28, 5, 46311, 1, f5, one_chunk treeX5, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨28, 6, 46312, 1, f6, one_chunk treeX6, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨24, 7, 46314, 1, f7, one_chunk treeX7, by norm_num, by norm_num, by decide +kernel⟩

theorem chainB_bound : burnsideF48d_ChainBound burnsideF48d_chainBL := by
  have hf := fixB
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩ := hf
  refine chainBound_of (B := D43BB) (lo := 2) (by decide +kernel) fun i hi => ?_
  change i < 5 at hi
  interval_cases i
  · exact ⟨131068, 8, 46340, 1, f0, one_chunk treeB0, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨130812, 9, 46343, 26, f1, treeB1, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨252, 10, 52904, 1, f2, one_chunk treeB2, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨28, 11, 52931, 1, f3, one_chunk treeB3, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨24, 12, 52933, 1, f4, one_chunk treeB4, by norm_num, by norm_num, by decide +kernel⟩

end CertificateChecks.KernelD43

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7802 : burnsideF48d_ChainBound burnsideF48d_chainXL ∧ burnsideF48d_ChainBound burnsideF48d_chainBL := ⟨chainX_bound, chainB_bound⟩

end Certificates

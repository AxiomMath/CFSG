module

public import CFSG.Quasithin.Background.HMathieuCode23Inputs
import Certificates.Kernel.HMathieu.T23XGlue
import Certificates.Kernel.HMathieu.C7110
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.GreedyPSound
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.PickKSound

public section

open CFSG.Quasithin.H.Mathieu
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
theorem certificate7110 :
    ∀ k ∈ [1, 2, 3, 4],
      forallGreedyP pos23s2 inv23s2 (predC23 k) k [] = true := by
  have hMd : T23.Md.length = 36 := by rw [T23.mdOK, List.length_map, T23.lenP]
  have hFs : ∀ y < inv23s2.length,
      T23X.F23.getD y [] = fixMasks 11 actM [T23.Md.getD y []] := by
    intro y hy
    rw [T23.len] at hy
    rw [fixTab_get T23X.tab y (by simp [hMd]; omega)]
    simp [fixMasks, List.getD_eq_getElem?_getD, List.getElem?_take, hy]
  have hmem : ∀ x ∈ inv23s2, actC23s2 x = actM (T23.Md.getD (inv23s2.idxOf x) []) :=
    fun x hx => T23.actC_mem hx
  have hA := forallGreedyAll_fixT T23X.gtabs (by rw [T23.len]; exact T23X.rowsLen) pos23s2_eq
    T23.Md T23X.F23 11 hFs _ (predXiKF 11 10 11 T23X.F23 35) (fun _ _ _ => rfl) 4
    (by rw [T23.len]; exact C7110.search)
  have hB := forallGreedyAll_mono_of (I := fun l => (∀ y ∈ l, y ∈ inv23s2) ∧ IndepList l)
    (q := fun l => l.isEmpty || predC23 l.length l)
    (fun l x hl hx => indep_step T23X.gtabs l x hl hx) (fun l hl hp => ?_) 4 []
    ⟨by simp, IndepList.nil⟩ hA
  · intro k hk
    have hb : 1 ≤ k ∧ k ≤ 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact forallGreedyP_of_all hB k hb.1 hb.2
  obtain ⟨hR, hind⟩ := hl
  have hci := isCommInvol_of_indepList hind
  have hfix : fixMasks 11 actC23s2 l =
      fixMasks 11 actM (l.map fun x => T23.Md.getD (inv23s2.idxOf x) []) :=
    fixMasks_map 11 _ fun x hx => hmem x (hR x hx)
  have hF : ∀ s ∈ inv23s2, T23X.F23.getD (inv23s2.idxOf s) [] = fixMasks 11 actC23s2 [s] := by
    intro s hs
    rw [hFs _ (List.idxOf_lt_length_iff.2 hs)]
    have e := fixMasks_map 11 (act := actC23s2) (act' := actM)
      (fun x => T23.Md.getD (inv23s2.idxOf x) []) (l := [s]) fun x hx => by
        rw [List.mem_singleton.1 hx]
        exact hmem s hs
    simp only [List.map_cons, List.map_nil] at e
    exact e.symm
  have hxi := xiCands_eq T23X.gtabs hci hF
  rw [T23.len] at hxi
  rw [predXiKF_eq] at hp
  unfold predXiK fixSt at hp
  unfold predC23 xiCheck
  rw [hfix, hxi]
  simp only [List.length_map, List.isEmpty_map] at hp ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
  rcases hp with h | ⟨h12, h3 | ⟨_, h5⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨h12, Or.inl h3⟩
  · exact Or.inr ⟨h12, Or.inr (indepCheck_of_indepK h5)⟩

end Certificates

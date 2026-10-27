module

public import CFSG.Quasithin.EmptyFaithful.ModGChkS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Data

public section

namespace CFSG.Quasithin.ModG

open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

@[expose] def nOK (w : List ℕ) : Bool :=
  Nat.beq (evc Lks8K w) kId ||
    anyL (fun i => !(memB (comp (comp (evc Lks8K w) (LsK.getD i kId)) (evc Lks8K (invW 4 w))) SK))
      [0, 1, 2]

theorem nCheck_true : allL nOK dWd = true := by decide +kernel

theorem dEl_normalizes : ∀ d ∈ dEl, d = 1 ∨ ∃ s ∈ Ls, d * s * d⁻¹ ∉ Sg := by
  intro d hd
  rw [dEl, List.mem_map] at hd
  obtain ⟨w, hw, rfl⟩ := hd
  have h := allL_iff.1 nCheck_true w hw
  simp only [nOK, Bool.or_eq_true] at h
  rcases h with h | h
  · left
    apply cd_injective
    rw [cd_one, c_ev cd cd_mul cd_one, Lks8_cd]
    exact Nat.eq_of_beq_eq_true h
  · right
    obtain ⟨i, hi, hi'⟩ := anyL_iff.1 h
    have hi3 : i < 3 := by simp at hi; omega
    refine ⟨Ls.getD i 1, ?_, ?_⟩
    · have : i < Ls.length := by
        rw [Ls, invAlph_length, List.length_map, sWd_len]
        omega
      rw [List.getD_eq_getElem _ _ this]
      exact List.getElem_mem _
    · intro hmem
      rw [mem_Sg_iff] at hmem
      have h2 : cd (ev Lks8 w * Ls.getD i 1 * (ev Lks8 w)⁻¹) ∈ SK := by
        rw [← SEl_cd]
        exact cd_mem_of_mem hmem
      have h3 := memB_iff.2 h2
      have hcl : cd (Ls.getD i 1) = LsK.getD i kId := by
        have := List.getD_map Ls 1 (n := i) cd
        rw [cd_one, Ls_cd] at this
        exact this.symm
      have hinv : cd ((ev Lks8 w)⁻¹) = evc Lks8K (invW 4 w) := by
        rw [← ev_invW Lks8_inv w (dWd_lt w hw), c_ev cd cd_mul cd_one, Lks8_cd]
      rw [cd_mul, cd_mul, hcl, hinv, c_ev cd cd_mul cd_one, Lks8_cd] at h3
      rw [h3] at hi'
      exact Bool.noConfusion hi'

@[expose] def B0l : List ℕ := [1, 5, 14, 15, 16, 19]

@[expose] def okA (e : ℕ × ℕ × List ℕ) : Bool :=
  Nat.blt e.2.1 6 &&
    allL (fun x => memB (Nat.sub (dg (comp (evc LsK e.2.2) (zK.getD e.2.1 kId)) x) 1)
      (M22Insp.blocks.getD e.1 [])) B0l

theorem aCheck_true : allL okA hexW = true := by decide +kernel

theorem aCover : ∀ i < 77, ∃ e ∈ hexW, e.1 = i := by decide +kernel

theorem blocks_zero : M22Insp.blocks.getD 0 [] = B0l := by decide +kernel

theorem blocks_length : M22Insp.blocks.length = 77 := by decide +kernel

theorem hex_cover : ∀ i < 77, ∃ k < 6, ∃ s ∈ SEl, ∀ x : Fin 22, x.val ∈ B0l →
    (((s * zEl.getD k 1 : Mg) : Equiv.Perm (Fin 22)) x).val ∈ M22Insp.blocks.getD i [] := by
  intro i hi
  obtain ⟨⟨i', k, sw⟩, he, rfl⟩ := aCover i hi
  have h := allL_iff.1 aCheck_true _ he
  simp only [okA, Bool.and_eq_true] at h
  obtain ⟨hk, hall⟩ := h
  have hk6 : k < 6 := by simpa using hk
  refine ⟨k, hk6, ev Ls sw, ?_, ?_⟩
  · rw [← mem_Sg_iff]
    exact ev_mem (fun x hx => Subgroup.subset_closure hx) sw
  · intro x hx
    have h1 := memB_iff.1 (allL_iff.1 hall x.val (by simpa using hx))
    have hz : cd (zEl.getD k 1) = zK.getD k kId := by
      have := List.getD_map zEl 1 (n := k) cd
      rw [cd_one, zEl_cd] at this
      exact this.symm
    have hs : cd (ev Ls sw) = evc LsK sw := by
      rw [c_ev cd cd_mul cd_one, Ls_cd]
    have : (((ev Ls sw * zEl.getD k 1 : Mg) : Equiv.Perm (Fin 22)) x).val =
        dg (comp (evc LsK sw) (zK.getD k kId)) x.val - 1 := by
      rw [val_apply_eq]
      show dg (cd (ev Ls sw * zEl.getD k 1)) x.val - 1 = _
      rw [cd_mul, hs, hz]
    rw [this]
    simpa using h1

@[expose] def uOK (i : ℕ) : Bool :=
  Nat.beq i 0 ||
    anyL (fun g => anyL (fun x => !(memB (Nat.sub (dg (LsK.getD g kId) x) 1) (M22Insp.blocks.getD i [])))
      (M22Insp.blocks.getD i [])) [0, 1, 2]

theorem uCheck_true : allL uOK (List.range 77) = true := by decide +kernel

theorem blocks_lt : ∀ l ∈ M22Insp.blocks, ∀ x ∈ l, x < 22 := by decide +kernel

theorem hex_unique : ∀ i < 77, i ≠ 0 → ∃ s ∈ Ls, ∃ x : Fin 22, x.val ∈ M22Insp.blocks.getD i [] ∧
    ((s : Equiv.Perm (Fin 22)) x).val ∉ M22Insp.blocks.getD i [] := by
  intro i hi hi0
  have h := allL_iff.1 uCheck_true i (List.mem_range.2 hi)
  simp only [uOK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (Nat.eq_of_beq_eq_true h) hi0
  · obtain ⟨g, hg, h2⟩ := anyL_iff.1 h
    obtain ⟨x, hx, hx2⟩ := anyL_iff.1 h2
    have hg3 : g < 3 := by simp at hg; omega
    have hlen : g < Ls.length := by
      rw [Ls, invAlph_length, List.length_map, sWd_len]
      omega
    have hblk : M22Insp.blocks.getD i [] ∈ M22Insp.blocks := by
      rw [List.getD_eq_getElem _ _ (by rw [blocks_length]; exact hi)]
      exact List.getElem_mem _
    have hx22 : x < 22 := blocks_lt _ hblk x hx
    refine ⟨Ls.getD g 1, ?_, ⟨x, hx22⟩, hx, ?_⟩
    · rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem _
    · rw [val_apply_eq]
      have hcl : cd (Ls.getD g 1) = LsK.getD g kId := by
        have := List.getD_map Ls 1 (n := g) cd
        rw [cd_one, Ls_cd] at this
        exact this.symm
      have : dg (pk ((Ls.getD g 1 : Mg) : Equiv.Perm (Fin 22))) x = dg (LsK.getD g kId) x := by
        rw [← hcl]
        rfl
      rw [this]
      intro hmem
      have h3 : memB (Nat.sub (dg (LsK.getD g kId) x) 1) (M22Insp.blocks.getD i []) = true :=
        memB_iff.2 hmem
      rw [h3] at hx2
      exact absurd hx2 (by decide)

end CFSG.Quasithin.ModG

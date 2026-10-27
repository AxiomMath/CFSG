module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeFin

public section

namespace CFSG.StandardType

namespace E6Dep

private def wd : List (List ℕ) := [[], [2], [1], [5, 1], [5], [4], [11, 4], [12, 4], [12, 10], [11, 1], [11], [10], [13], [12], [12, 1], [22, 19], [19, 4], [21, 4], [19, 1], [20], [19], [22], [21], [21, 1], [25, 1], [26], [25], [29, 1], [29], [28], [32, 1], [32], [31], [34], [33], [33, 1]]

private def actI (w : List ℕ) (x : ℕ) : ℕ := w.foldl (fun y t => cjN t y) x

private def Bad (c : ℕ) : Prop :=
  ∃ (I : Finset ℕ) (r : ℕ), I ⊆ fix1 c ∧ CjClosed I ∧ I ≠ fix1 c ∧ r < 36 ∧ CjGen (insert r I)

private theorem wd_spec :
    ∀ c < 36, (∀ t ∈ wd.getD c [], t < 36) ∧ actI (wd.getD c []) c = 0 := by
  decide +kernel

private theorem cjN_lt : ∀ t < 36, ∀ a < 36, cjN t a < 36 := by
  decide +kernel

private theorem cjN_invol : ∀ t < 36, ∀ a < 36, cjN t (cjN t a) = a := by
  decide +kernel

private theorem cjN_mul :
    ∀ t < 36, ∀ a < 36, ∀ b < 36, cjN t (cjN a b) = cjN (cjN t a) (cjN t b) := by
  decide +kernel

private theorem fix_char :
    ∀ c < 36, ∀ i < 36, (bil6 (cen i) (cen c) = 0 ↔ (i ≠ c ∧ cjN i c = c)) := by
  decide +kernel

private lemma mem_fix1 {c i : ℕ} (hc : c < 36) :
    i ∈ fix1 c ↔ i < 36 ∧ i ≠ c ∧ cjN i c = c := by
  rw [fix1, zset, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1, (fix_char c hc i h.1).mp h.2⟩,
    fun h => ⟨h.1, (fix_char c hc i h.1).mpr h.2⟩⟩

private lemma actI_cons (t : ℕ) (w : List ℕ) (c : ℕ) :
    actI (t :: w) c = actI w (cjN t c) := rfl

private lemma image_cjN_range (t : ℕ) (ht : t < 36) :
    (Finset.range 36).image (cjN t) = Finset.range 36 := by
  apply Finset.Subset.antisymm
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range] at ha ⊢
    exact cjN_lt t ht a ha
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_image]
    exact ⟨cjN t a, Finset.mem_range.mpr (cjN_lt t ht a ha), cjN_invol t ht a ha⟩

private lemma image_cjN_image {t : ℕ} (ht : t < 36) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range 36) : (J.image (cjN t)).image (cjN t) = J := by
  apply Finset.Subset.antisymm
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨b, hb, hby⟩ := hy
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [cjN_invol t ht a (Finset.mem_range.mp (hJ ha))] at hby
    rw [← hby]
    exact ha
  · intro a ha
    rw [Finset.mem_image]
    refine ⟨cjN t a, ?_, cjN_invol t ht a (Finset.mem_range.mp (hJ ha))⟩
    rw [Finset.mem_image]
    exact ⟨a, ha, rfl⟩

private lemma bad_step {t c : ℕ} (ht : t < 36) (hc : c < 36) (h : Bad c) :
    Bad (cjN t c) := by
  obtain ⟨I, r, hI, hcl, hne, hr, hgen⟩ := h
  have htc : cjN t c < 36 := cjN_lt t ht c hc
  refine ⟨I.image (cjN t), cjN t r, ?_, ?_, ?_, cjN_lt t ht r hr, ?_⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hjI, rfl⟩ := hy
    obtain ⟨hjlt, hjne, hjc⟩ := (mem_fix1 hc).mp (hI hjI)
    rw [mem_fix1 htc]
    refine ⟨cjN_lt t ht j hjlt, ?_, ?_⟩
    · intro hcon
      exact hjne (by
        have h2 := congrArg (cjN t) hcon
        rwa [cjN_invol t ht j hjlt, cjN_invol t ht c hc] at h2)
    · calc cjN (cjN t j) (cjN t c) = cjN t (cjN j c) := (cjN_mul t ht j hjlt c hc).symm
        _ = cjN t c := by rw [hjc]
  · intro a ha b hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have ha₀lt : a₀ < 36 := ((mem_fix1 hc).mp (hI ha₀)).1
    have hb₀lt : b₀ < 36 := ((mem_fix1 hc).mp (hI hb₀)).1
    rw [Finset.mem_image]
    exact ⟨cjN a₀ b₀, hcl a₀ ha₀ b₀ hb₀, cjN_mul t ht a₀ ha₀lt b₀ hb₀lt⟩
  · intro heq
    apply hne
    refine Finset.Subset.antisymm hI ?_
    intro j hj
    obtain ⟨hjlt, hjne, hjc⟩ := (mem_fix1 hc).mp hj
    have hjf : cjN t j ∈ fix1 (cjN t c) := by
      rw [mem_fix1 htc]
      refine ⟨cjN_lt t ht j hjlt, ?_, ?_⟩
      · intro hcon
        exact hjne (by
          have h2 := congrArg (cjN t) hcon
          rwa [cjN_invol t ht j hjlt, cjN_invol t ht c hc] at h2)
      · calc cjN (cjN t j) (cjN t c) = cjN t (cjN j c) := (cjN_mul t ht j hjlt c hc).symm
          _ = cjN t c := by rw [hjc]
    rw [← heq, Finset.mem_image] at hjf
    obtain ⟨i, hiI, hieq⟩ := hjf
    have hilt : i < 36 := ((mem_fix1 hc).mp (hI hiI)).1
    have hij : i = j := by
      have h2 := congrArg (cjN t) hieq
      rwa [cjN_invol t ht i hilt, cjN_invol t ht j hjlt] at h2
    exact hij ▸ hiI
  · intro J hJsub hJcl hJcon
    have hJ''sub : J.image (cjN t) ⊆ Finset.range 36 := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, haJ, rfl⟩ := hy
      rw [Finset.mem_range]
      exact cjN_lt t ht a (Finset.mem_range.mp (hJsub haJ))
    have hJ''cl : CjClosed (J.image (cjN t)) := by
      intro a ha b hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      rw [Finset.mem_image]
      exact ⟨cjN a₀ b₀, hJcl a₀ ha₀ b₀ hb₀,
        cjN_mul t ht a₀ (Finset.mem_range.mp (hJsub ha₀)) b₀
          (Finset.mem_range.mp (hJsub hb₀))⟩
    have hJcon' : insert r I ⊆ J.image (cjN t) := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with hxr | hxI
      · rw [hxr, Finset.mem_image]
        exact ⟨cjN t r, hJcon (Finset.mem_insert_self (cjN t r) (I.image (cjN t))),
          cjN_invol t ht r hr⟩
      · rw [Finset.mem_image]
        refine ⟨cjN t x, ?_, cjN_invol t ht x ((mem_fix1 hc).mp (hI hxI)).1⟩
        exact hJcon (Finset.mem_insert_of_mem (by
          rw [Finset.mem_image]
          exact ⟨x, hxI, rfl⟩))
    have hgen' : J.image (cjN t) = Finset.range 36 := hgen _ hJ''sub hJ''cl hJcon'
    have hinv : (J.image (cjN t)).image (cjN t) = J := image_cjN_image ht J hJsub
    rw [hgen', image_cjN_range t ht] at hinv
    exact hinv.symm

private lemma bad_actI (w : List ℕ) :
    (∀ t ∈ w, t < 36) → ∀ c < 36, Bad c → Bad (actI w c) := by
  induction w with
  | nil => intro _ _ _ h; exact h
  | cons t w ih =>
    intro hw c hc h
    have ht : t < 36 := hw t (by simp)
    have hw' : ∀ s ∈ w, s < 36 := fun s hs => hw s (by simp [hs])
    rw [actI_cons]
    exact ih hw' (cjN t c) (cjN_lt t ht c hc) (bad_step ht hc h)

theorem all_not_gen {c : ℕ} (hc : c < 36) {I : Finset ℕ} (hI : I ⊆ fix1 c) (hcl : CjClosed I)
    (hne : I ≠ fix1 c) {r : ℕ} (hr : r < 36) : ¬ CjGen (insert r I) := by
  intro hgen
  have hBad : Bad c := ⟨I, r, hI, hcl, hne, hr, hgen⟩
  obtain ⟨hletters, hact⟩ := wd_spec c hc
  have h0 : Bad 0 := by
    have h' := bad_actI (wd.getD c []) hletters c hc hBad
    rwa [hact] at h'
  obtain ⟨I₀, r₀, hI₀, hcl₀, hne₀, hr₀, hgen₀⟩ := h0
  exact base_not_gen hI₀ hcl₀ hne₀ hr₀ hgen₀

end E6Dep

end CFSG.StandardType

end

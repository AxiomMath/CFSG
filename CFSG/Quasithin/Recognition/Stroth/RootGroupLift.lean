module

public import CFSG.Quasithin.Recognition.Stroth.WeissEmbeddingFacts
public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleNormal

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons

universe u

private theorem lift_segment {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
    {n : ℕ} (hn : 3 ≤ n) {V : Type} [Fintype V] {Δ : SimpleGraph V} [DecidableRel Δ.Adj]
    (ι : c.Γ → V) (hconn : c.graph.Connected)
    (hInjOn : Set.InjOn ι (edgeBall (n - 1) c))
    (hSurj : ∀ y : V, ∃ w ∈ edgeBall (n - 1) c, ι w = y)
    (hE2 : ∀ w w', w ∈ edgeBall (n - 2) c → w' ∈ edgeBall (n - 1) c →
      (Δ.Adj (ι w) (ι w') ↔ c.graph.Adj w w'))
    {x0 : c.Γ} (hx0 : x0 = c.xv ∨ x0 = c.lv)
    {k : ℕ} (hk : k ≤ n - 1) {r : GPath Δ k} (hr : r.NoBack) (hr0 : r 0 = ι x0) :
    ∃ q : GPath c.graph k, q 0 = x0 ∧ (∀ i, ι (q i) = r i) ∧ q.NoBack ∧
      (∀ i, c.graph.dist x0 (q i) ≤ i) ∧
      (∀ i, i ≤ n - 2 → q i ∈ edgeBall (n - 2) c) ∧
      (∀ i, q i ∈ edgeBall (n - 1) c) := by
  induction k with
  | zero =>
    let q0 : GPath c.graph 0 :=
      { toFun := fun _ => x0
        adj := by intro i hi; exact absurd hi (Nat.not_lt_zero i)
        tail := by intro i hi; rfl }
    refine ⟨q0, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [r.tail i (Nat.zero_le i)]
      simpa using hr0.symm
    · intro i hi
      omega
    · intro i
      rw [SimpleGraph.dist_self]
      exact Nat.zero_le i
    · intro i hi
      rcases hx0 with hx | hx
      · left; rw [← hx]; rw [SimpleGraph.dist_self]; omega
      · right; rw [← hx]; rw [SimpleGraph.dist_self]; omega
    · intro i
      rcases hx0 with hx | hx
      · left; rw [← hx]; rw [SimpleGraph.dist_self]; omega
      · right; rw [← hx]; rw [SimpleGraph.dist_self]; omega
  | succ k ih =>
    have hk' : k ≤ n - 1 := by omega
    have hrk : (r.take k (by omega)).NoBack := hr.take k (by omega)
    have hrk0 : r.take k (by omega) 0 = ι x0 := by
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le k)]
      exact hr0
    obtain ⟨q0, hq00, hq0ι, hq0nb, hq0dist, hq0mem, hq0ball⟩ := ih hk' hrk hrk0
    obtain ⟨w, hwball, hwι⟩ := hSurj (r (k + 1))
    have hq0k : q0 k ∈ edgeBall (n - 2) c := hq0mem k (by omega)
    have hadj : c.graph.Adj (q0 k) w := by
      apply (hE2 (q0 k) w hq0k hwball).mp
      rw [hq0ι k, GPath.take_apply_of_le _ _ _ le_rfl, hwι]
      exact r.adj k (by omega)
    let q : GPath c.graph (k + 1) := q0.snoc w hadj
    have hq_le : ∀ i, i ≤ k → q i = q0 i := fun i hi => GPath.snoc_of_le _ _ _ hi
    have hq_last : q (k + 1) = w := GPath.snoc_last _ _ _
    have hwd : c.graph.dist x0 w ≤ k + 1 := by
      have h1 : c.graph.dist x0 w ≤ c.graph.dist x0 (q0 k) + 1 := by
        have hd : c.graph.dist (q0 k) w = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        have := hconn.dist_triangle (u := x0) (v := q0 k) (w := w)
        omega
      have := hq0dist k
      omega
    refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hq_le 0 (Nat.zero_le k)]
      exact hq00
    · intro i
      by_cases hi : i ≤ k
      · rw [hq_le i hi, hq0ι i]
        rw [GPath.take_apply_of_le _ _ _ hi]
      · by_cases hi1 : i = k + 1
        · subst hi1
          rw [hq_last]
          exact hwι
        · have hi2 : i > k + 1 := by omega
          rw [q.tail i (by omega), hq_last, r.tail i (by omega)]
          exact hwι
    · intro i hi
      by_cases hik : i + 2 ≤ k
      · rw [hq_le i (by omega), hq_le (i + 2) (by omega)]
        exact hq0nb i hik
      · have hi' : i = k - 1 := by omega
        subst hi'
        have hlt : k - 1 ≤ k := by omega
        rw [hq_le (k - 1) hlt, show k - 1 + 2 = k + 1 by omega, hq_last]
        intro heq
        have hιeq : ι (q0 (k - 1)) = ι w := by rw [heq]
        rw [hq0ι (k - 1), GPath.take_apply_of_le _ _ _ (by omega), hwι] at hιeq
        exact hr (k - 1) (by omega) (by simpa [show k - 1 + 2 = k + 1 by omega] using hιeq)
    · intro i
      by_cases hi : i ≤ k
      · rw [hq_le i hi]
        exact hq0dist i
      · by_cases hi1 : i = k + 1
        · subst hi1
          rw [hq_last]
          exact hwd
        · have hi2 : i > k + 1 := by omega
          rw [q.tail i (by omega), hq_last]
          exact le_trans hwd (by omega)
    · intro i hi
      by_cases hik : i ≤ k
      · rw [hq_le i hik]
        exact hq0mem i hi
      · by_cases hi1 : i = k + 1
        · subst hi1
          rw [hq_last]
          have hk2 : k + 1 ≤ n - 2 := by omega
          rcases hx0 with hx | hx
          · left; rw [← hx]; exact le_trans hwd hk2
          · right; rw [← hx]; exact le_trans hwd hk2
        · have hi2 : i > k + 1 := by omega
          have hk2 : k + 1 ≤ n - 2 := by omega
          rw [q.tail i (by omega), hq_last]
          rcases hx0 with hx | hx
          · left; rw [← hx]; exact le_trans hwd hk2
          · right; rw [← hx]; exact le_trans hwd hk2
    · intro i
      by_cases hik : i ≤ k
      · rw [hq_le i hik]
        exact hq0ball i
      · by_cases hi1 : i = k + 1
        · subst hi1
          rw [hq_last]
          exact hwball
        · have hi2 : i > k + 1 := by omega
          rw [q.tail i (by omega), hq_last]
          exact hwball

theorem rootGroupLift (n : ℕ) : RootGroupLift n := by
  intro X _ P1 P2 Y _ c hn hc hM V _ Δ _ D _ _ _ _ u v ψ₁ ψ₂ ι hP hT hMΔ hW
  classical
  rcases hW with ⟨hInj1, hInj2, hAgree, hGen, hιx, hιl, hBij, hE2, hE3₁, hE3₂⟩
  have hInjOn : Set.InjOn ι (edgeBall (n - 1) c) := hBij.2.1
  have hSurj : ∀ y : V, ∃ w ∈ edgeBall (n - 1) c, ι w = y := by
    intro y
    obtain ⟨w, hw, hwy⟩ := hBij.2.2 (Set.mem_univ y)
    exact ⟨w, hw, hwy⟩
  have hbase : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hxvInner : c.xv ∈ edgeBall (n - 2) c := by
    left; rw [SimpleGraph.dist_self]; omega
  have hlvBall : c.lv ∈ edgeBall (n - 1) c := by
    right; rw [SimpleGraph.dist_self]; omega
  have hAdjUV : Δ.Adj u v := by
    have h := (hE2 c.xv c.lv hxvInner hlvBall).mpr hbase
    rwa [hιx, hιl] at h
  have huv : u ≠ v := hAdjUV.ne
  have main_case : ∀ (p : GPath Δ n) (j : ℕ), p.NoBack → 1 ≤ j → j + 1 ≤ n →
      ((p j = u ∧ p (j + 1) = v) ∨ (p j = v ∧ p (j + 1) = u)) →
      pathRootGroup D Δ p ≤ (psiB P2 ψ₁).range := by
    intro p j hp hj hj1 hEdge
    have hpj : p j = u ∨ p j = v := by
      rcases hEdge with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hpj1 : p (j + 1) = u ∨ p (j + 1) = v := by
      rcases hEdge with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
    let xL : c.Γ := if p j = u then c.xv else c.lv
    let xR : c.Γ := if p j = u then c.lv else c.xv
    have hxLι : ι xL = p j := by
      by_cases h : p j = u
      · simp [xL, h, hιx]
      · have hv : p j = v := hpj.resolve_left h
        have hvu : v ≠ u := by intro hvu; exact h (hv.trans hvu)
        simp [xL, h, hv, hvu, hιl]
    have hxRι : ι xR = p (j + 1) := by
      by_cases h : p j = u
      · have hv : p (j + 1) = v := by
          rcases hEdge with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · exact absurd (h.symm.trans h1) huv
        simp [xR, h, hv, hιl]
      · have hu : p (j + 1) = u := by
          rcases hEdge with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 h
          · exact h2
        simp [xR, h, hu, hιx]
    have hxLbase : xL = c.xv ∨ xL = c.lv := by
      by_cases h : p j = u
      · left; simp [xL, h]
      · right; simp [xL, h]
    have hxRbase : xR = c.xv ∨ xR = c.lv := by
      by_cases h : p j = u
      · right; simp [xR, h]
      · left; simp [xR, h]
    have hxLR : c.graph.Adj xL xR := by
      by_cases h : p j = u
      · simp [xL, xR, h]; exact hbase
      · simp [xL, xR, h]; exact hbase.symm
    have hjle : j ≤ n - 1 := by omega
    have hrLnb : ((p.take j (by omega)).rev).NoBack :=
      (hp.take j (by omega)).rev
    have hrL0 : (p.take j (by omega)).rev 0 = ι xL := by
      rw [GPath.rev_apply _ (by omega), Nat.sub_zero,
        GPath.take_apply_of_le _ _ _ (le_refl j)]
      exact hxLι.symm
    obtain ⟨qLrev, hqLrev0, hqLrevι, hqLrevnb, hqLrevdist, hqLrevmem,
      hqLrevball⟩ :=
      lift_segment (n := n) (c := c) (ι := ι) hn hconn hInjOn hSurj hE2 hxLbase
        hjle hrLnb hrL0
    let qL : GPath c.graph j := qLrev.rev
    have hqLj : qL j = xL := by
      have hrev := GPath.rev_apply qLrev (i := j) (by omega)
      dsimp only [qL]
      rw [hrev, Nat.sub_self]
      exact hqLrev0
    have hqLnb : qL.NoBack := hqLrevnb.rev
    have hqLι' : ∀ i, i ≤ j → ι (qL i) = p i := by
      intro i hi
      rw [show qL i = qLrev (j - i) from GPath.rev_apply qLrev (by omega)]
      rw [hqLrevι (j - i), GPath.rev_apply (p.take j (by omega)) (by omega)]
      rw [show j - (j - i) = i by omega, GPath.take_apply_of_le _ _ _ hi]
    have hqLmem : ∀ i, 1 ≤ i → i ≤ j → qL i ∈ edgeBall (n - 2) c := by
      intro i hi1 hi2
      rw [show qL i = qLrev (j - i) from GPath.rev_apply qLrev (by omega)]
      exact hqLrevmem (j - i) (by omega)
    have hqLball : ∀ i, i ≤ j → qL i ∈ edgeBall (n - 1) c := by
      intro i hi
      rw [show qL i = qLrev (j - i) from GPath.rev_apply qLrev (by omega)]
      exact hqLrevball (j - i)
    have hnr : n - (j + 1) ≤ n - 1 := by omega
    have hrRnb : (p.drop (j + 1) (by omega)).NoBack := hp.drop (j + 1) (by omega)
    have hrR0 : p.drop (j + 1) (by omega) 0 = ι xR := by
      rw [GPath.drop_apply p (j + 1) (by omega) (by omega)]
      simpa using hxRι.symm
    obtain ⟨qR, hqR0, hqRι, hqRnb, hqRdist, hqRmem, hqRball⟩ :=
      lift_segment (n := n) (c := c) (ι := ι) hn hconn hInjOn hSurj hE2 hxRbase
        hnr hrRnb hrR0
    let q : GPath c.graph n :=
      { toFun := fun i => if i ≤ j then qL i else qR (i - (j + 1))
        adj := by
          intro i hi
          by_cases hij : i < j
          · have h1 : i ≤ j := by omega
            have h2 : i + 1 ≤ j := by omega
            change c.graph.Adj (if i ≤ j then qL i else qR (i - (j + 1)))
              (if i + 1 ≤ j then qL (i + 1) else qR (i + 1 - (j + 1)))
            rw [if_pos h1, if_pos h2]
            exact qL.adj i hij
          · by_cases heq : i = j
            · subst i
              change c.graph.Adj (if j ≤ j then qL j else qR (j - (j + 1)))
                (if j + 1 ≤ j then qL (j + 1) else qR (j + 1 - (j + 1)))
              rw [if_pos le_rfl, if_neg (by omega), Nat.sub_self, hqLj, hqR0]
              exact hxLR
            · have h1 : ¬ i ≤ j := by omega
              have h2 : ¬ i + 1 ≤ j := by omega
              change c.graph.Adj (if i ≤ j then qL i else qR (i - (j + 1)))
                (if i + 1 ≤ j then qL (i + 1) else qR (i + 1 - (j + 1)))
              rw [if_neg h1, if_neg h2]
              have e : i + 1 - (j + 1) = (i - (j + 1)) + 1 := by omega
              rw [e]
              exact qR.adj (i - (j + 1)) (by omega)
        tail := by
          intro i hi
          have h1 : ¬ i ≤ j := by omega
          change (if i ≤ j then qL i else qR (i - (j + 1))) =
            (if n ≤ j then qL n else qR (n - (j + 1)))
          rw [if_neg h1, if_neg (by omega)]
          exact qR.tail (i - (j + 1)) (by omega) }
    have hqj : q j = xL := by
      dsimp only [q]
      rw [if_pos le_rfl, hqLj]
    have hqj1 : q (j + 1) = xR := by
      dsimp only [q]
      rw [if_neg (by omega), Nat.sub_self, hqR0]
    have hqι : ∀ i, i ≤ n → ι (q i) = p i := by
      intro i hi
      by_cases hij : i ≤ j
      · dsimp only [q]
        rw [if_pos hij]
        exact hqLι' i hij
      · have h1 : ¬ i ≤ j := hij
        dsimp only [q]
        rw [if_neg h1]
        rw [hqRι (i - (j + 1))]
        rw [GPath.drop_apply p (j + 1) (by omega) (by omega)]
        congr 1
        omega
    have hqnb : q.NoBack := by
      intro i hi
      by_cases h1 : i + 2 ≤ j
      · have e1 : i ≤ j := by omega
        have e2 : i + 2 ≤ j := h1
        dsimp only [q]
        rw [if_pos e1, if_pos e2]
        exact hqLnb i h1
      · by_cases h2 : i + 1 ≤ j
        · have e1 : i ≤ j := by omega
          have e2 : ¬ i + 2 ≤ j := h1
          dsimp only [q]
          rw [if_pos e1, if_neg e2]
          have hi' : i = j - 1 := by omega
          subst hi'
          intro heq
          have hιeq := congrArg ι heq
          rw [show j - 1 + 2 - (j + 1) = 0 by omega] at hιeq
          rw [hqLι' (j - 1) (by omega), hqRι 0,
            GPath.drop_apply p (j + 1) (by omega) (by omega)] at hιeq
          exact hp (j - 1) (by omega)
            (by simpa [show j - 1 + 2 = j + 1 by omega] using hιeq)
        · by_cases h3 : i = j
          · subst i
            have e1 : j ≤ j := le_rfl
            have e2 : ¬ j + 2 ≤ j := by omega
            dsimp only [q]
            rw [if_pos e1, if_neg e2, hqLj]
            intro heq
            have hιeq := congrArg ι heq
            rw [show j + 2 - (j + 1) = 1 by omega] at hιeq
            rw [hxLι, hqRι 1,
              GPath.drop_apply p (j + 1) (by omega) (by omega)] at hιeq
            exact hp j (by omega) hιeq
          · have e1 : ¬ i ≤ j := by omega
            have e2 : ¬ i + 1 ≤ j := h2
            have e3 : ¬ i + 2 ≤ j := h1
            dsimp only [q]
            rw [if_neg e1, if_neg e3,
              show i + 2 - (j + 1) = (i - (j + 1)) + 2 by omega]
            exact hqRnb (i - (j + 1)) (by omega)
    have hqinner : ∀ i, 1 ≤ i → i ≤ n - 1 → q i ∈ edgeBall (n - 2) c := by
      intro i hi1 hi2
      by_cases hij : i ≤ j
      · dsimp only [q]
        rw [if_pos hij]
        exact hqLmem i hi1 hij
      · dsimp only [q]
        rw [if_neg hij]
        exact hqRmem (i - (j + 1)) (by omega)
    have hqn_inner : q n ∈ edgeBall (n - 2) c := by
      have h1 : ¬ n ≤ j := by omega
      dsimp only [q]
      rw [if_neg h1]
      exact hqRmem (n - (j + 1)) (by omega)
    have hfixL : ∀ h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q,
        h • xL = xL := by
      intro h hh
      by_cases hj1' : j = 1
      · subst j
        have h2 : 2 ≤ n - 1 := by omega
        have hadj : c.graph.Adj (q 2) xL := by
          have h := (q.adj 1 (by omega)).symm
          rwa [hqj] at h
        exact (mem_pathRootGroup.mp hh) 2 (by omega) h2 xL hadj
      · have hj2 : 2 ≤ j := by omega
        have hadj : c.graph.Adj (q (j - 1)) xL := by
          have h := q.adj (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at h
          rwa [hqj] at h
        exact (mem_pathRootGroup.mp hh) (j - 1) (by omega) (by omega) xL hadj
    have hfixR : ∀ h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q,
        h • xR = xR := by
      intro h hh
      have hadj : c.graph.Adj (q j) xR := by
        have h := q.adj j (by omega)
        rwa [hqj1] at h
      exact (mem_pathRootGroup.mp hh) j hj (by omega) xR hadj
    have hfixbase : ∀ h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q,
        h • c.xv = c.xv ∧ h • c.lv = c.lv := by
      intro h hh
      by_cases hcase : p j = u
      · have hL : xL = c.xv := by simp [xL, hcase]
        have hR : xR = c.lv := by simp [xR, hcase]
        exact ⟨hL ▸ hfixL h hh, hR ▸ hfixR h hh⟩
      · have hL : xL = c.lv := by simp [xL, hcase]
        have hR : xR = c.xv := by simp [xR, hcase]
        exact ⟨hR ▸ hfixR h hh, hL ▸ hfixL h hh⟩
    have htransport : ∀ h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q,
        ∃ s ∈ (psiB P2 ψ₁).range, ∀ w ∈ edgeBall (n - 1) c, s • ι w = ι (h • w) := by
      intro h hh
      have hb := hfixbase h hh
      have hmem12 : (h : Y) ∈ c.φ12.range := by
        have h1 : (h : Y) ∈ c.φ1.range := by
          have := CosetGeom.mem_stab_of_smul_eq hb.1
          rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
            (G₂ := c.φ2.range) le_sup_left] at this
        have h2 : (h : Y) ∈ c.φ2.range := by
          have := CosetGeom.mem_stab_of_smul_eq hb.2
          rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
            (G₂ := c.φ2.range) le_sup_right] at this
        rw [← c.inter]
        exact ⟨h1, h2⟩
      obtain ⟨b0, hb0⟩ := hmem12
      refine ⟨psiB P2 ψ₁ b0, ⟨b0, rfl⟩, ?_⟩
      intro w hw
      by_cases hwx : c.graph.dist c.xv w ≤ n - 1
      · have hhφ1 : (h : Y) = c.φ1 (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b0) :=
          hb0.symm.trans (c.comm1 b0).symm
        have hE := hE3₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b0)
          h hhφ1 w hwx
        rw [show psiB P2 ψ₁ b0 =
          ψ₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b0) from rfl]
        exact hE
      · have hwl : c.graph.dist c.lv w ≤ n - 1 := by
          rcases hw with h | h
          · exact absurd h hwx
          · exact h
        have hhφ2 : (h : Y) = c.φ2 (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b0) :=
          hb0.symm.trans (c.comm2 b0).symm
        have hE := hE3₂ (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b0)
          h hhφ2 w hwl
        rw [show psiB P2 ψ₁ b0 =
          ψ₂ (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b0) from hAgree b0]
        exact hE
    have hSle : ∀ h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q,
        ∃ s ∈ (psiB P2 ψ₁).range ⊓ pathRootGroup D Δ p,
          ∀ w ∈ edgeBall (n - 1) c, s • ι w = ι (h • w) := by
      intro h hh
      obtain ⟨s, hs, hsw⟩ := htransport h hh
      refine ⟨s, ⟨hs, ?_⟩, hsw⟩
      refine mem_pathRootGroup.mpr ?_
      intro i hi1 hi2 y hy
      obtain ⟨w, hwball, hwy⟩ := hSurj y
      have hqinner' : q i ∈ edgeBall (n - 2) c := hqinner i hi1 hi2
      have hadj : c.graph.Adj (q i) w := by
        apply (hE2 (q i) w hqinner' hwball).mp
        rw [hqι i (by omega), hwy]
        exact hy
      have hwfix : h • w = w := (mem_pathRootGroup.mp hh) i hi1 hi2 w hadj
      calc s • y = s • ι w := by rw [hwy]
        _ = ι (h • w) := hsw w hwball
        _ = ι w := by rw [hwfix]
        _ = y := hwy
    have hTransS : ∀ y1 y2 : V, Δ.Adj (p n) y1 → Δ.Adj (p n) y2 →
        y1 ≠ p (n - 1) → y2 ≠ p (n - 1) →
        ∃ s : D, s ∈ (psiB P2 ψ₁).range ⊓ pathRootGroup D Δ p ∧ s • y1 = y2 := by
      intro y1 y2 hy1 hy2 h1 h2
      obtain ⟨w1, hw1ball, hw1y⟩ := hSurj y1
      obtain ⟨w2, hw2ball, hw2y⟩ := hSurj y2
      have hq1 : c.graph.Adj (q n) w1 := by
        apply (hE2 (q n) w1 hqn_inner hw1ball).mp
        rw [hqι n le_rfl, hw1y]
        exact hy1
      have hq2 : c.graph.Adj (q n) w2 := by
        apply (hE2 (q n) w2 hqn_inner hw2ball).mp
        rw [hqι n le_rfl, hw2y]
        exact hy2
      have h1' : w1 ≠ q (n - 1) := by
        intro h
        exact h1 (by rw [← hw1y, h, hqι (n - 1) (by omega)])
      have h2' : w2 ≠ q (n - 1) := by
        intro h
        exact h2 (by rw [← hw2y, h, hqι (n - 1) (by omega)])
      obtain ⟨h, hhfix, hhw⟩ := hM q hqnb w1 w2 hq1 hq2 h1' h2'
      have hh : h ∈ pathRootGroup (↥(c.φ1.range ⊔ c.φ2.range)) c.graph q :=
        mem_pathRootGroup.mpr hhfix
      obtain ⟨s, hs, hsw⟩ := hSle h hh
      refine ⟨s, hs, ?_⟩
      calc s • y1 = s • ι w1 := by rw [hw1y]
        _ = ι (h • w1) := hsw w1 hw1ball
        _ = ι w2 := by rw [hhw]
        _ = y2 := hw2y
    intro g hg
    have hNex : ∃ y0, Δ.Adj (p n) y0 ∧ y0 ≠ p (n - 1) := by
      have hcard : 3 ≤ (Δ.neighborFinset (p n)).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hT (p n)
      obtain ⟨a, ha, b, hb, cc, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card.mp (by omega : 2 < (Δ.neighborFinset (p n)).card)
      rw [SimpleGraph.mem_neighborFinset] at ha hb hc
      by_cases h1 : a ≠ p (n - 1)
      · exact ⟨a, ha, h1⟩
      · by_cases h2 : b ≠ p (n - 1)
        · exact ⟨b, hb, h2⟩
        · exact ⟨cc, hc, by
            intro hcc
            exact hac ((not_not.mp h1).trans hcc.symm)⟩
    obtain ⟨y0, hy0, hy0ne⟩ := hNex
    have hgpn : g • (p n) = p n := by
      have hadj : Δ.Adj (p (n - 1)) (p n) := by
        simpa [show n - 1 + 1 = n by omega] using p.adj (n - 1) (by omega)
      exact (mem_pathRootGroup.mp hg) (n - 1) (by omega) le_rfl (p n) hadj
    have hgpm : g • (p (n - 1)) = p (n - 1) := by
      have hadj : Δ.Adj (p (n - 2)) (p (n - 1)) := by
        simpa [show n - 2 + 1 = n - 1 by omega] using p.adj (n - 2) (by omega)
      exact (mem_pathRootGroup.mp hg) (n - 2) (by omega) (by omega) (p (n - 1)) hadj
    have hgy0 : Δ.Adj (p n) (g • y0) := by
      rw [← hgpn]
      exact (GraphAction.adj_smul g (p n) y0).mpr hy0
    have hgy0ne : g • y0 ≠ p (n - 1) := by
      intro h
      apply hy0ne
      have hgpm' : g⁻¹ • p (n - 1) = p (n - 1) := by
        have := congrArg (fun v => g⁻¹ • v) hgpm
        simpa using this.symm
      have hh := congrArg (fun v => g⁻¹ • v) h
      simpa [hgpm'] using hh
    obtain ⟨s, hs, hsy⟩ := hTransS y0 (g • y0) hy0 hgy0 hy0ne hgy0ne
    have hsg : s⁻¹ * g = 1 := by
      apply pathRootGroup_eq_one_of_fix (p := p) (n := n) hn hP hT hp
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs.2) hg) hy0 hy0ne
      rw [mul_smul, ← hsy, inv_smul_smul]
    have hg_eq : g = s := by
      have hh := congrArg (fun w => s * w) hsg
      simpa using hh
    rw [hg_eq]
    exact hs.1
  intro p hp j hj hEdge
  by_cases hj0 : j = 0
  · subst j
    have hp' : p.rev.NoBack := hp.rev
    have hEdge' : (p.rev (n - 1) = u ∧ p.rev n = v) ∨
        (p.rev (n - 1) = v ∧ p.rev n = u) := by
      have e1 : p.rev (n - 1) = p 1 := by
        rw [GPath.rev_apply p (by omega)]
        congr 1; omega
      have e2 : p.rev n = p 0 := by
        rw [GPath.rev_apply p le_rfl, Nat.sub_self]
      rw [e1, e2]
      rcases hEdge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    have hEdge'' : ((p.rev (n - 1) = u ∧ p.rev (n - 1 + 1) = v) ∨
        (p.rev (n - 1) = v ∧ p.rev (n - 1 + 1) = u)) := by
      simpa [show n - 1 + 1 = n by omega] using hEdge'
    have h := main_case p.rev (n - 1) hp' (by omega) (by omega) hEdge''
    rwa [pathRootGroup_rev] at h
  · have hj1 : 1 ≤ j := by omega
    exact main_case p j hp hj1 (by omega) hEdge

theorem weissEmbeddingFacts (n : ℕ) : WeissEmbeddingFacts n :=
  weissEmbeddingFacts_of_rootGroupLift n (rootGroupLift n)

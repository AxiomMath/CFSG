module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPathUnique
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPathExists
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Delta

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem stabPath_castLength {m k : ℕ} (h : m = k) (p : GPath Γ m) :
    GPath.stabPath (H := H) (GPath.castLength h p) = GPath.stabPath (H := H) p := by
  cases h
  rw [show GPath.castLength rfl p = p from GPath.ext' fun i _ => rfl]

private theorem mem_take_rev_of_mem_drop {n i : ℕ} {p : GPath Γ (n + 1 + i)} {g : H}
    (hg : g ∈ GPath.stabPath (H := H) (p.drop i (by omega))) :
    g ∈ GPath.stabPath (H := H) (p.rev.take (n + 1) (by omega)) := by
  rw [GPath.mem_stabPath_iff] at hg ⊢
  intro l hl
  rw [GPath.take_apply_of_le _ _ _ hl, GPath.rev_apply _ (by omega)]
  have h1 : g • p ((n + 1 + i) - l) = p ((n + 1 + i) - l) := by
    have h := hg ((n + 1 + i) - i - l) (by omega)
    rwa [GPath.drop_apply _ _ _ (by omega),
      show i + ((n + 1 + i) - i - l) = (n + 1 + i) - l by omega] at h
  exact h1

private theorem mem_stabPath_of_mem_stabPath_take [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) {s : ℕ} {P : GPath Γ s}
    (hP : IsGoodPath H P) {k : ℕ} (hk : n + 1 ≤ k) (hks : k ≤ s) {g : H}
    (hg : g ∈ GPath.stabPath (H := H) (P.take k hks)) :
    g ∈ GPath.stabPath (H := H) P := by
  have hmain : ∀ (r : ℕ) (hr : k + r ≤ s),
      g ∈ GPath.stabPath (H := H) (P.take (k + r) hr) := by
    intro r hr
    induction r with
    | zero => simpa using hg
    | succ r ih =>
        have hprev := ih (by omega)
        have hkr : k + r < s := by omega
        have hk1 : n + 1 ≤ k + r := by omega
        have hw : Γ.Adj ((P.take (k + r) (by omega)) (k + r)) (P (k + r + 1)) := by
          rw [GPath.take_apply_of_le _ _ _ le_rfl]
          exact P.adj (k + r) hkr
        have hsnoc : (P.take (k + r) (by omega)).snoc (P (k + r + 1)) hw =
            P.take (k + r + 1) (by omega) := by
          apply GPath.ext'
          intro l hl
          by_cases hl' : l ≤ k + r
          · rw [GPath.snoc_of_le _ _ _ hl', GPath.take_apply_of_le _ _ _ hl',
              GPath.take_apply_of_le _ _ _ hl]
          · have hl'' : l = k + r + 1 := by omega
            subst hl''
            rw [GPath.snoc_last, GPath.take_apply_of_le _ _ _ le_rfl]
        have hgood : IsGoodPath H
            ((P.take (k + r) (by omega)).snoc (P (k + r + 1)) hw) := by
          rw [hsnoc]
          exact hP.take (k + r + 1) (by omega)
        have hstab := stabPath_le_stabilizer_of_isGoodPath hn hW hL hk1 hw hgood
        have hgnew : g ∈ MulAction.stabilizer H (P (k + r + 1)) := hstab hprev
        rw [GPath.mem_stabPath_iff]
        intro l hl
        by_cases hl' : l ≤ k + r
        · have h := GPath.mem_stabPath_iff.mp hprev l hl'
          rw [GPath.take_apply_of_le _ _ _ hl'] at h
          rw [GPath.take_apply_of_le _ _ _ (by omega)]
          exact h
        · have hl'' : l = k + r + 1 := by omega
          subst hl''
          rw [GPath.take_apply_of_le _ _ _ (by omega)]
          exact MulAction.mem_stabilizer_iff.mp hgnew
  have hres := hmain (s - k) (by omega)
  have htake : GPath.castLength (show k + (s - k) = s by omega)
      (P.take (k + (s - k)) (by omega)) = P :=
    GPath.ext' fun i _ => by
      rw [GPath.castLength_apply, GPath.take_apply_of_le _ _ _ (by omega)]
  rw [← stabPath_castLength (show k + (s - k) = s by omega)
    (P.take (k + (s - k)) (by omega)), htake] at hres
  exact hres

private theorem mem_stabPath_of_mem_stabPath_drop [Finite H] {n i : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) {P : GPath Γ (n + 1 + i)}
    (hP : IsGoodPath H P) {g : H}
    (hg : g ∈ GPath.stabPath (H := H) (P.drop i (by omega))) :
    g ∈ GPath.stabPath (H := H) P := by
  have htake : g ∈ GPath.stabPath (H := H) (P.rev.take (n + 1) (by omega)) :=
    mem_take_rev_of_mem_drop (p := P) hg
  have hrev : g ∈ GPath.stabPath (H := H) P.rev :=
    mem_stabPath_of_mem_stabPath_take hn hW hL hP.rev (k := n + 1) (by omega) (by omega)
      htake
  have h := hrev
  rw [GPath.stabPath_rev] at h
  exact h

theorem weissLemma4_of_weissLemma4' [Finite V] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    (h4 : WeissLemma4' H Γ n) : WeissLemma4 H Γ n := by
  intro w hw i hi0 hin z hz hznm1 hznp1
  have hwgood : IsGoodPath H w :=
    isGoodPath_of_noBack hn hM hne (fun z => (hL z).kernel_le) (s := n + 1) le_rfl hw
  have hext : ∀ k : ℕ, ∃ P : GPath Γ (n + 1 + k), P.NoBack ∧
      (∀ j, j ≤ n + 1 → P j = w j) ∧ IsGoodPath H P := by
    intro k
    induction k with
    | zero => exact ⟨w, hw, fun j _ => rfl, hwgood⟩
    | succ k ih =>
        obtain ⟨P, _, hPagree, hPgood⟩ := ih
        obtain ⟨v, hv, hPv⟩ :=
          exists_isGoodPath_snoc hn hM hne hL (s := n + 1 + k) (by omega) hPgood
        refine ⟨P.snoc v hv, hPv.1, ?_, hPv⟩
        intro j hj
        rw [GPath.snoc_of_le P v hv (by omega)]
        exact hPagree j hj
  obtain ⟨P, _, hPa, hPgood⟩ := hext i
  let wt : GPath Γ (n + 1) :=
    GPath.castLength (by omega : n + 1 + i - i = n + 1) (P.drop i (by omega))
  have hwtgood : IsGoodPath H wt :=
    (isGoodPath_castLength _).mpr (hPgood.drop i (by omega))
  have hwt0 : wt 0 = w i := by
    rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
    exact hPa i (by omega)
  have hwt_n : wt (n - i) = w n := by
    rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
    rw [show i + (n - i) = n by omega]
    exact hPa n (by omega)
  have hwt_nm1 : wt (n - i - 1) = w (n - 1) := by
    rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
    rw [show i + (n - i - 1) = n - 1 by omega]
    exact hPa (n - 1) (by omega)
  have hwt_np1 : wt (n - i + 1) = w (n + 1) := by
    rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
    rw [show i + (n - i + 1) = n + 1 by omega]
    exact hPa (n + 1) (by omega)
  obtain ⟨g, hgin, hgz⟩ :=
    h4 wt hwtgood.1 (n - i) (by omega) (by omega) z (by rwa [hwt_n])
      (by rw [hwt_nm1]; exact hznm1) (by rw [hwt_np1]; exact hznp1)
  refine ⟨g, ⟨?_, ?_⟩, hgz⟩
  · change g ∈ GPath.stabPath (H := H) w
    have hwtstab : g ∈ GPath.stabPath (H := H) (P.drop i (by omega)) := by
      have h := hgin.2
      change g ∈ GPath.stabPath (H := H)
        (GPath.castLength (by omega : n + 1 + i - i = n + 1)
          (P.drop i (by omega))) at h
      rwa [stabPath_castLength] at h
    have hgP : g ∈ GPath.stabPath (H := H) P :=
      mem_stabPath_of_mem_stabPath_drop hn hW hL hPgood hwtstab
    rw [GPath.mem_stabPath_iff]
    intro j hj
    rw [← hPa j hj]
    exact GPath.mem_stabPath_iff.mp hgP j (by omega)
  · have h := hgin.1
    rwa [hwt0] at h

theorem goodPathSystem_isGoodPath [Finite V] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    (h4 : WeissLemma4 H Γ n) :
    GoodPathSystem H Γ n (fun _ p => IsGoodPath H p) where
  noBack := fun _ _ hp => hp.1
  short := fun _ p hs hp => isGoodPath_of_noBack hn hM hne (fun z => (hL z).kernel_le) hs hp
  take := fun _ p k hk hp => hp.take k hk
  drop := fun _ p k hk hp => hp.drop k hk
  rev := fun _ p hp => hp.rev
  smul := fun _ g p hp => hp.smul g
  extend := by
    intro s p hs hp
    obtain ⟨w, hw, hgw⟩ := exists_isGoodPath_snoc hn hM hne hL (s := s) (by omega) hp
    refine ⟨w, ⟨hw, hgw⟩, ?_⟩
    rintro w' ⟨hw', hgw'⟩
    exact (isGoodPath_snoc_unique hn hW hL hs hw hw' hgw hgw').symm
  lemma3 := by
    intro P Q hP hQ hPQ hQne
    classical
    let B : GPath Γ n := P.rev.take n (by omega)
    have hBapply : ∀ j, j ≤ n → B j = P (2 * n - j) := by
      intro j hj
      rw [GPath.take_apply_of_le _ _ _ hj, GPath.rev_apply _ (by omega)]
    have hBnb : B.NoBack := hP.rev.1.take n (by omega)
    have hQn : Q n = P n := hPQ n (by omega)
    have hBadj : Γ.Adj (B n) (Q (n + 1)) := by
      rw [hBapply n le_rfl, show 2 * n - n = n by omega, ← hQn]
      exact Q.adj n (by omega)
    let B1 : GPath Γ (n + 1) := B.snoc (Q (n + 1)) hBadj
    have hB1nb : B1.NoBack := by
      intro i hi
      by_cases hin : i + 2 ≤ n
      · rw [show B1 i = B i from GPath.snoc_of_le B _ _ (by omega),
          show B1 (i + 2) = B (i + 2) from GPath.snoc_of_le B _ _ hin]
        exact hBnb i hin
      · have hi' : i = n - 1 := by omega
        subst hi'
        rw [show B1 (n - 1) = B (n - 1) from GPath.snoc_of_le B _ _ (by omega),
          show B1 (n - 1 + 2) = Q (n + 1) from by
            rw [show n - 1 + 2 = n + 1 by omega, GPath.snoc_last]]
        rw [hBapply (n - 1) (by omega), show 2 * n - (n - 1) = n + 1 by omega]
        exact fun h => hQne h.symm
    have hB1good : IsGoodPath H B1 :=
      isGoodPath_of_noBack hn hM hne (fun z => (hL z).kernel_le) (s := n + 1) le_rfl hB1nb
    have hreach : ∀ k : ℕ, ∃ R : GPath Γ (n + 1 + k), R.NoBack ∧
        (∀ j, j ≤ n → R j = P (2 * n - j)) ∧ R (n + 1) = Q (n + 1) ∧
        IsGoodPath H R := by
      intro k
      induction k with
      | zero =>
          refine ⟨B1, hB1nb, ?_, ?_, hB1good⟩
          · intro j hj
            rw [show B1 j = B j from GPath.snoc_of_le B _ _ (by omega)]
            exact hBapply j hj
          · exact GPath.snoc_last B (Q (n + 1)) hBadj
      | succ k ih =>
          obtain ⟨R, _, hRinit, hRmid, hRgood⟩ := ih
          obtain ⟨v, hv, hRv⟩ :=
            exists_isGoodPath_snoc hn hM hne hL (s := n + 1 + k) (by omega) hRgood
          refine ⟨R.snoc v hv, hRv.1, ?_, ?_, hRv⟩
          · intro j hj
            rw [GPath.snoc_of_le R v hv (by omega)]
            exact hRinit j hj
          · rw [GPath.snoc_of_le R v hv (by omega)]
            exact hRmid
    obtain ⟨R, hRnb, hRinit, hRmid, hRgood⟩ := hreach (n - 2)
    have htail_all : ∀ j, j ≤ n - 1 → ∀ l, 1 ≤ l → l ≤ j → R (n + l) = Q (n + l) := by
      intro j hj
      induction j with
      | zero => intro l hl1 hl0; omega
      | succ j ih =>
          intro l hl1 hlj
          have hprev : ∀ l, 1 ≤ l → l ≤ j → R (n + l) = Q (n + l) := ih (by omega)
          rcases (by omega : l = j + 1 ∨ l ≤ j) with hl | hl
          · subst hl
            by_cases hj0 : j = 0
            · subst hj0
              simpa using hRmid
            · by_contra hne
              have hj1 : 1 ≤ j := by omega
              have hjn : j ≤ n - 2 := by omega
              let Z : GPath Γ (n + 1 + j) := Q.take (n + 1 + j) (by omega)
              have hZgood : IsGoodPath H Z := hQ.take (n + 1 + j) (by omega)
              let W : GPath Γ (n + 1) :=
                GPath.castLength (by omega : (n + 1 + j) - j = n + 1)
                  (Z.drop j (by omega))
              have hWgood : IsGoodPath H W :=
                (isGoodPath_castLength _).mpr (hZgood.drop j (by omega))
              have hWapply : ∀ l, l ≤ n + 1 → W l = Z (j + l) := by
                intro l hl
                rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
              have hWQ : ∀ l, l ≤ n + 1 → W l = Q (j + l) := by
                intro l hl
                rw [hWapply l hl, GPath.take_apply_of_le _ _ _ (by omega)]
              have hWn : W n = Q (n + j) := by
                rw [hWQ n (by omega), show j + n = n + j by omega]
              have hWnm1 : W (n - 1) = Q (n + j - 1) := by
                rw [hWQ (n - 1) (by omega), show j + (n - 1) = n + j - 1 by omega]
              have hWnp1 : W (n + 1) = Q (n + j + 1) := by
                rw [hWQ (n + 1) le_rfl, show j + (n + 1) = n + j + 1 by omega]
              have hWmid : W (n - j) = P n := by
                rw [hWQ (n - j) (by omega), show j + (n - j) = n by omega, ← hQn]
              have hRnj : R (n + j) = Q (n + j) := hprev j (by omega) le_rfl
              have hadj : Γ.Adj (W n) (R (n + j + 1)) := by
                rw [hWn, ← hRnj]
                exact R.adj (n + j) (by omega)
              have hz1 : R (n + j + 1) ≠ W (n - 1) := by
                rw [hWnm1]
                have hRnj1 : R (n + j - 1) = Q (n + j - 1) := by
                  rcases (by omega : j = 1 ∨ 2 ≤ j) with hj1' | hj2
                  · subst hj1'
                    rw [show n + 1 - 1 = n by omega]
                    exact (hRinit n le_rfl).trans
                      (by rw [show 2 * n - n = n by omega]; exact hQn.symm)
                  · have h := hprev (j - 1) (by omega) (by omega)
                    simpa [show n + (j - 1) = n + j - 1 by omega] using h
                rw [← hRnj1]
                have h := hRnb (n + j - 1) (by omega)
                rw [show n + j - 1 + 2 = n + j + 1 by omega] at h
                exact h.symm
              have hz2 : R (n + j + 1) ≠ W (n + 1) := by
                rw [hWnp1]
                exact hne
              obtain ⟨g, hgK, hgz⟩ :=
                h4 W hWgood.1 (n - j) (by omega) (by omega)
                  (R (n + j + 1)) hadj hz1 hz2
              have hgK' : g ∈ GPath.stabPath (H := H) W ⊓
                  fixingSubgroup H (Γ.neighborSet (P n)) := by
                have h := hgK
                rwa [hWmid] at h
              have hfixK : ∀ x ∈ GPath.stabPath (H := H) W ⊓
                  fixingSubgroup H (Γ.neighborSet (P n)),
                  x • R (n + j + 1) = R (n + j + 1) := by
                intro x hx
                have hxW : x ∈ GPath.stabPath (H := H) (Z.drop j (by omega)) := by
                  have h := hx.1
                  change x ∈ GPath.stabPath (H := H)
                    (GPath.castLength (by omega : (n + 1 + j) - j = n + 1)
                      (Z.drop j (by omega))) at h
                  rwa [stabPath_castLength] at h
                have hxZ : x ∈ GPath.stabPath (H := H) Z :=
                  mem_stabPath_of_mem_stabPath_drop hn hW hL hZgood hxW
                have hxtake : x ∈ GPath.stabPath (H := H) (P.take (n + 1) (by omega)) := by
                  rw [GPath.mem_stabPath_iff]
                  intro l hl
                  rw [GPath.take_apply_of_le _ _ _ hl]
                  by_cases hln : l ≤ n
                  · have hZl : x • Z l = Z l := GPath.mem_stabPath_iff.mp hxZ l (by omega)
                    have hZl' : Z l = P l := by
                      rw [GPath.take_apply_of_le _ _ _ (by omega)]
                      exact hPQ l hln
                    rw [← hZl', hZl]
                  · have hl' : l = n + 1 := by omega
                    subst hl'
                    exact (mem_fixingSubgroup_iff H).mp hx.2 (P (n + 1)) (P.adj n (by omega))
                have hxP : x ∈ GPath.stabPath (H := H) P :=
                  mem_stabPath_of_mem_stabPath_take hn hW hL hP (k := n + 1) (by omega)
                    (by omega) hxtake
                have hxRtake : x ∈ GPath.stabPath (H := H) (R.take (n + j) (by omega)) := by
                  rw [GPath.mem_stabPath_iff]
                  intro l hl
                  rw [GPath.take_apply_of_le _ _ _ hl]
                  by_cases hln : l ≤ n
                  · rw [hRinit l hln]
                    exact GPath.mem_stabPath_iff.mp hxP (2 * n - l) (by omega)
                  · have hl' : l = n + (l - n) := by omega
                    have hl'1 : 1 ≤ l - n := by omega
                    have hl'j : l - n ≤ j := by omega
                    have hZ := GPath.mem_stabPath_iff.mp hxZ l (by omega)
                    rw [GPath.take_apply_of_le _ _ _ (by omega), hl'] at hZ
                    rw [hl', hprev (l - n) hl'1 hl'j]
                    exact hZ
                have hwR : Γ.Adj ((R.take (n + j) (by omega)) (n + j)) (R (n + j + 1)) := by
                  rw [GPath.take_apply_of_le _ _ _ le_rfl]
                  exact R.adj (n + j) (by omega)
                have hsnocR : (R.take (n + j) (by omega)).snoc (R (n + j + 1)) hwR =
                    R.take (n + j + 1) (by omega) := by
                  apply GPath.ext'
                  intro l hl
                  by_cases hl' : l ≤ n + j
                  · rw [GPath.snoc_of_le _ _ _ hl', GPath.take_apply_of_le _ _ _ hl',
                      GPath.take_apply_of_le _ _ _ hl]
                  · have hl'' : l = n + j + 1 := by omega
                    subst hl''
                    rw [GPath.snoc_last, GPath.take_apply_of_le _ _ _ le_rfl]
                have hgoodR : IsGoodPath H
                    ((R.take (n + j) (by omega)).snoc (R (n + j + 1)) hwR) := by
                  rw [hsnocR]
                  exact hRgood.take (n + j + 1) (by omega)
                have hstabR :=
                  stabPath_le_stabilizer_of_isGoodPath hn hW hL (s := n + j) (by omega)
                    hwR hgoodR
                exact MulAction.mem_stabilizer_iff.mp (hstabR hxRtake)
              exact hgz (hfixK g hgK')
          · exact hprev l hl1 hl
    have htail : ∀ l, 1 ≤ l → l ≤ n - 1 → R (n + l) = Q (n + l) :=
      fun l hl1 hl => htail_all (n - 1) le_rfl l hl1 hl
    let Rc : GPath Γ (2 * n - 1) :=
      GPath.castLength (by omega : n + 1 + (n - 2) = 2 * n - 1) R
    let r : GPath Γ (2 * n - 1) := Rc.rev
    refine ⟨r, ?_, ?_, ?_⟩
    · exact ((isGoodPath_castLength _).mpr hRgood).rev
    · intro i hi
      show Rc.rev i = Q (2 * n - 1 - i)
      rw [GPath.rev_apply _ (by omega), GPath.castLength_apply]
      rcases (by omega : 2 * n - 1 - i = n ∨ n + 1 ≤ 2 * n - 1 - i) with h | h
      · rw [h]
        exact (hRinit n le_rfl).trans
          (by rw [show 2 * n - n = n by omega]; exact hQn.symm)
      · have h2 := htail (2 * n - 1 - i - n) (by omega) (by omega)
        rwa [show n + (2 * n - 1 - i - n) = 2 * n - 1 - i by omega] at h2
    · intro i hi1 hi2
      show Rc.rev i = P (i + 1)
      rw [GPath.rev_apply _ (by omega), GPath.castLength_apply]
      have h := hRinit (2 * n - 1 - i) (by omega)
      rwa [show 2 * n - (2 * n - 1 - i) = i + 1 by omega] at h

end CFSG.Quasithin.Stroth.WeissDelta

end

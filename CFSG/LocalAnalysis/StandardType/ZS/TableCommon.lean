module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem commutatorSpace_inv_of_mem {B : Subgroup (V ≃ₗ[K] V)} :
    ∀ h ∈ B, ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace B,
      h x ∈ HardMathSupport.Kantor79.commutatorSpace B := by
  intro h hh x hx
  have hle : HardMathSupport.Kantor79.commutatorSpace B ≤
      Submodule.comap (h : V →ₗ[K] V) (HardMathSupport.Kantor79.commutatorSpace B) := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro w ⟨b, hb, hv⟩
    obtain ⟨v, rfl⟩ := hv
    have h1 : (h * b) v - v ∈ HardMathSupport.Kantor79.commutatorSpace B := by
      rw [HardMathSupport.Kantor79.commutatorSpace]
      exact Submodule.subset_span ⟨h * b, B.mul_mem hh hb, v, rfl⟩
    have h2 : h v - v ∈ HardMathSupport.Kantor79.commutatorSpace B := by
      rw [HardMathSupport.Kantor79.commutatorSpace]
      exact Submodule.subset_span ⟨h, hh, v, rfl⟩
    have heq : h (b v - v) = (h * b) v - v - (h v - v) := by
      rw [map_sub, LinearEquiv.mul_apply]
      abel
    change h (b v - v) ∈ HardMathSupport.Kantor79.commutatorSpace B
    rw [heq]
    exact Submodule.sub_mem _ h1 h2
  exact hle hx

private theorem commutatorSpace_eq_of_isCompl {B : Subgroup (V ≃ₗ[K] V)} {W W' : Submodule K V}
    (hWW' : IsCompl W W') (hfix : ∀ h ∈ B, ∀ w ∈ W', h w = w)
    (hinv : ∀ h ∈ B, ∀ w ∈ W, h w ∈ W) (hirr : IrredOnSection B ⊥ W)
    (hVinv : ∀ h ∈ B, ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace B,
      h x ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hne : ∃ h ∈ B, ∃ w ∈ W, h w ≠ w) :
    HardMathSupport.Kantor79.commutatorSpace B = W := by
  have hVle : HardMathSupport.Kantor79.commutatorSpace B ≤ W := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro x ⟨h, hh, hv⟩
    obtain ⟨v, rfl⟩ := hv
    have hv : v ∈ W ⊔ W' := by rw [hWW'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have hvw : h (w + w') - (w + w') = h w - w := by
      rw [map_add, hfix h hh w' hw']
      abel
    rw [hvw]
    exact Submodule.sub_mem _ (hinv h hh w hw) hw
  apply le_antisymm hVle
  obtain ⟨h, hh, w, hw, hne⟩ := hne
  have hne0 : h w - w ≠ 0 := sub_ne_zero.mpr hne
  have hmem : h w - w ∈ HardMathSupport.Kantor79.commutatorSpace B := by
    rw [HardMathSupport.Kantor79.commutatorSpace]
    exact Submodule.subset_span ⟨h, hh, w, rfl⟩
  have hneV : HardMathSupport.Kantor79.commutatorSpace B ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmem
    exact hne0 (by simpa using hmem)
  rcases hirr (HardMathSupport.Kantor79.commutatorSpace B) bot_le hVle hVinv with hbot | htop
  · exact absurd hbot hneV
  · exact le_of_eq htop.symm

private theorem centralizerSpace_eq_of_isCompl {B : Subgroup (V ≃ₗ[K] V)} {W W' : Submodule K V}
    (hWW' : IsCompl W W') (hfix : ∀ h ∈ B, ∀ w ∈ W', h w = w)
    (hinv : ∀ h ∈ B, ∀ w ∈ W, h w ∈ W) (hirr : IrredOnSection B ⊥ W)
    (hne : ∃ h ∈ B, ∃ w ∈ W, h w ≠ w) :
    centralizerSpace B = W' := by
  have hInfBot : centralizerSpace B ⊓ W = ⊥ := by
    have hXinv : ∀ h ∈ B, ∀ x ∈ centralizerSpace B ⊓ W, h x ∈ centralizerSpace B ⊓ W := by
      rintro h hh x ⟨hxV, hxW⟩
      refine ⟨?_, hinv h hh x hxW⟩
      refine (mem_centralizerSpace).mpr fun h' hh' => ?_
      have hxVh : h x = x := (mem_centralizerSpace).mp hxV h hh
      have hxVh' : h' x = x := (mem_centralizerSpace).mp hxV h' hh'
      rw [hxVh, hxVh']
    rcases hirr (centralizerSpace B ⊓ W) bot_le inf_le_right hXinv with hbot | htop
    · exact hbot
    · exfalso
      have hWle : W ≤ centralizerSpace B := by rw [← htop]; exact inf_le_left
      obtain ⟨h, hh, w, hw, hne⟩ := hne
      exact hne ((mem_centralizerSpace).mp (hWle hw) h hh)
  apply le_antisymm
  · intro v hv
    have hv' : ∀ h ∈ B, h v = v := (mem_centralizerSpace).mp hv
    have hvsup : v ∈ W ⊔ W' := by rw [hWW'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hvsup
    have hwfix : ∀ h ∈ B, h w = w := by
      intro h hh
      have h1 : h (w + w') = w + w' := hv' h hh
      rw [map_add, hfix h hh w' hw'] at h1
      exact add_right_cancel h1
    have hwV : w ∈ centralizerSpace B := (mem_centralizerSpace).mpr hwfix
    have hwbot : w ∈ (⊥ : Submodule K V) := by
      rw [← hInfBot]; exact ⟨hwV, hw⟩
    rw [show w = 0 from by simpa using hwbot, zero_add]
    exact hw'
  · intro v hv
    exact (mem_centralizerSpace).mpr fun h hh => hfix h hh v hv

theorem splitSupport_of_isCompl {B : Subgroup (V ≃ₗ[K] V)} {W W' : Submodule K V}
    (hWW' : IsCompl W W') (hfix : ∀ h ∈ B, ∀ w ∈ W', h w = w)
    (hinv : ∀ h ∈ B, ∀ w ∈ W, h w ∈ W) (hirr : IrredOnSection B ⊥ W)
    (hne : ∃ h ∈ B, ∃ w ∈ W, h w ≠ w) : SplitSupport B (Module.finrank K W) := by
  have hVinv := commutatorSpace_inv_of_mem (B := B)
  have hVeq := commutatorSpace_eq_of_isCompl hWW' hfix hinv hirr hVinv hne
  have hVceq := centralizerSpace_eq_of_isCompl hWW' hfix hinv hirr hne
  unfold SplitSupport
  rw [hVeq, hVceq]
  exact ⟨hWW', rfl, hirr⟩

private noncomputable def diagonalSubMap {S : Type*} (e : S → K) (c : K) :
    (S →₀ K) →ₗ[K] (S →₀ K) :=
  { toFun := fun l =>
      Finsupp.onFinset l.support (fun i => l i * (e i - c)) (by
        intro i hi
        exact Finsupp.mem_support_iff.mpr (fun h => hi (by rw [h, zero_mul])))
    map_add' := by intro l1 l2; ext i; simp [add_mul]
    map_smul' := by intro a l; ext i; simp [mul_assoc] }

@[simp] private theorem diagonalSubMap_apply {S : Type*} (e : S → K) (c : K) (l : S →₀ K)
    (k : S) : diagonalSubMap e c l k = l k * (e k - c) := by
  simp [diagonalSubMap, Finsupp.onFinset_apply]

private theorem map_linearCombination_sub_smul {S : Type*} {bS : S → V} {h : V ≃ₗ[K] V}
    {e : S → K} {c : K} (he : ∀ k, h (bS k) = e k • bS k) (l : S →₀ K) :
    h (Finsupp.linearCombination K bS l) - c • Finsupp.linearCombination K bS l =
      Finsupp.linearCombination K bS (diagonalSubMap e c l) := by
  induction l using Finsupp.induction with
  | zero =>
    rw [show diagonalSubMap e c 0 = 0 from map_zero (diagonalSubMap e c)]
    simp
  | single_add k a f _ _ ih =>
    have hsingle : h (Finsupp.linearCombination K bS (Finsupp.single k a)) -
        c • Finsupp.linearCombination K bS (Finsupp.single k a) =
        Finsupp.linearCombination K bS (diagonalSubMap e c (Finsupp.single k a)) := by
      rw [Finsupp.linearCombination_single]
      rw [show diagonalSubMap e c (Finsupp.single k a) =
          Finsupp.single k (a * (e k - c)) from by
        ext i0
        by_cases hik : i0 = k
        · subst hik; simp [diagonalSubMap]
        · simp [diagonalSubMap, Finsupp.onFinset_apply, Finsupp.single_eq_of_ne hik]]
      rw [Finsupp.linearCombination_single, map_smul, he k]
      module
    have hlin : h (Finsupp.linearCombination K bS (Finsupp.single k a + f)) -
        c • Finsupp.linearCombination K bS (Finsupp.single k a + f) =
        (h (Finsupp.linearCombination K bS (Finsupp.single k a)) -
          c • Finsupp.linearCombination K bS (Finsupp.single k a)) +
        (h (Finsupp.linearCombination K bS f) - c • Finsupp.linearCombination K bS f) := by
      rw [map_add, map_add]
      module
    rw [hlin, hsingle, ih, map_add, map_add]

private theorem map_mem_span_of_diagonal {S : Type*} {bS : S → V} {h : V ≃ₗ[K] V} {e : S → K}
    (he : ∀ k, h (bS k) = e k • bS k) {x : V} (hx : x ∈ Submodule.span K (Set.range bS)) :
    h x ∈ Submodule.span K (Set.range bS) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [he k]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul a y _ ihy => rw [map_smul]; exact Submodule.smul_mem _ a ihy

private theorem repr_sub_smul_eq {S : Type*} {bS : S → V} (hbS : LinearIndependent K bS)
    {h : V ≃ₗ[K] V} {e : S → K} {c : K} (he : ∀ k, h (bS k) = e k • bS k)
    (x : Submodule.span K (Set.range bS)) :
    LinearIndependent.repr hbS
        ⟨h x.1 - c • x.1, Submodule.sub_mem (Submodule.span K (Set.range bS))
          (map_mem_span_of_diagonal he x.2) (Submodule.smul_mem _ c x.2)⟩ =
      diagonalSubMap e c (LinearIndependent.repr hbS x) := by
  apply LinearIndependent.repr_eq
  have h := map_linearCombination_sub_smul (bS := bS) (c := c) he (LinearIndependent.repr hbS x)
  rw [LinearIndependent.linearCombination_repr] at h
  exact h.symm

private theorem diagonalCoeff_eq {S : Type*} {bS : S → V} (hbS : LinearIndependent K bS)
    {h : V ≃ₗ[K] V} {e : S → K} (he : ∀ k, h (bS k) = e k • bS k) {i : S} {c : K}
    (hci : h (bS i) = c • bS i) : e i = c := by
  have h1 : e i • bS i = c • bS i := by rw [← he i, hci]
  have h2 : (e i - c) • bS i = 0 := by rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hbS.ne_zero i))

private theorem exists_smaller_support {S : Type*} {bS : S → V} (hbS : LinearIndependent K bS)
    {h : V ≃ₗ[K] V} {e : S → K} {c d : K} (he : ∀ k, h (bS k) = e k • bS k)
    {i j : S} (hei : e i = c) (hej : e j = d) (hcd : c ≠ d)
    (x : Submodule.span K (Set.range bS))
    (hi : i ∈ (LinearIndependent.repr hbS x).support)
    (hj : j ∈ (LinearIndependent.repr hbS x).support) :
    ∃ y : Submodule.span K (Set.range bS), y.1 = h x.1 - c • x.1 ∧
      (LinearIndependent.repr hbS y).support.card <
        (LinearIndependent.repr hbS x).support.card ∧ y.1 ≠ 0 := by
  let y : Submodule.span K (Set.range bS) :=
    ⟨h x.1 - c • x.1, Submodule.sub_mem (Submodule.span K (Set.range bS))
      (map_mem_span_of_diagonal he x.2) (Submodule.smul_mem _ c x.2)⟩
  have hyrepr : LinearIndependent.repr hbS y = diagonalSubMap e c (LinearIndependent.repr hbS x) :=
    repr_sub_smul_eq hbS he x
  have hsupp_sub : (LinearIndependent.repr hbS y).support ⊆
      (LinearIndependent.repr hbS x).support := by
    intro k hk
    rw [hyrepr, Finsupp.mem_support_iff, diagonalSubMap_apply] at hk
    rw [Finsupp.mem_support_iff]
    intro hk0
    exact hk (by rw [hk0, zero_mul])
  have hi_not : i ∉ (LinearIndependent.repr hbS y).support := by
    rw [hyrepr, Finsupp.mem_support_iff, diagonalSubMap_apply]
    simp [hei]
  have hj_mem : j ∈ (LinearIndependent.repr hbS y).support := by
    rw [hyrepr, Finsupp.mem_support_iff, diagonalSubMap_apply]
    have hlj : (LinearIndependent.repr hbS x) j ≠ 0 := by
      rw [← Finsupp.mem_support_iff]; exact hj
    have hdj : e j - c ≠ 0 := by rw [hej]; exact sub_ne_zero.mpr (Ne.symm hcd)
    exact mul_ne_zero hlj hdj
  have hy_ne : y.1 ≠ 0 := by
    intro hy0
    have hsub : y = 0 := Subtype.ext hy0
    have h0 : LinearIndependent.repr hbS y = 0 := by rw [hsub]; simp
    have hsupp : (LinearIndependent.repr hbS y).support = ∅ := by rw [h0]; simp
    rw [hsupp] at hj_mem
    simp at hj_mem
  refine ⟨y, rfl, ?_, hy_ne⟩
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsupp_sub, ?_⟩)
  intro hEq
  exact hi_not (hEq ▸ hi)

private theorem exists_minimal_support {S : Type*} {bS : S → V} (hbS : LinearIndependent K bS)
    {X : Submodule K V} (hXle : X ≤ Submodule.span K (Set.range bS)) (hX : X ≠ ⊥) :
    ∃ x : Submodule.span K (Set.range bS), x.1 ∈ X ∧ x.1 ≠ 0 ∧
      ∀ y : Submodule.span K (Set.range bS), y.1 ∈ X → y.1 ≠ 0 →
        (LinearIndependent.repr hbS x).support.card ≤
          (LinearIndependent.repr hbS y).support.card := by
  classical
  let P (n : ℕ) : Prop := ∃ x : Submodule.span K (Set.range bS),
    x.1 ∈ X ∧ x.1 ≠ 0 ∧ (LinearIndependent.repr hbS x).support.card = n
  have hP : ∃ n, P n := by
    obtain ⟨x0, hx0X, hx0_ne⟩ := (Submodule.ne_bot_iff X).mp hX
    exact ⟨_, ⟨⟨x0, hXle hx0X⟩, hx0X, hx0_ne, rfl⟩⟩
  obtain ⟨x1, hx1X, hx1_ne, hx1_card⟩ := Nat.find_spec hP
  refine ⟨x1, hx1X, hx1_ne, fun y hyX hy_ne => ?_⟩
  have hyP : P (LinearIndependent.repr hbS y).support.card := ⟨y, hyX, hy_ne, rfl⟩
  have hfind := Nat.find_min' hP hyP
  rw [← hx1_card] at hfind
  exact hfind

private theorem support_card_eq_one_of_separating {S : Type*} {bS : S → V}
    (hbS : LinearIndependent K bS) {B : Subgroup (V ≃ₗ[K] V)}
    (hsep : ∀ i j : S, i ≠ j → ∃ h ∈ B, (∀ k, ∃ e : K, h (bS k) = e • bS k) ∧
      ∃ c d : K, c ≠ d ∧ h (bS i) = c • bS i ∧ h (bS j) = d • bS j)
    {X : Submodule K V} (hXinv : ∀ h ∈ B, ∀ x ∈ X, h x ∈ X)
    {x1 : Submodule.span K (Set.range bS)} (hx1X : x1.1 ∈ X) (hx1_ne : x1.1 ≠ 0)
    (hmin : ∀ y : Submodule.span K (Set.range bS), y.1 ∈ X → y.1 ≠ 0 →
      (LinearIndependent.repr hbS x1).support.card ≤
        (LinearIndependent.repr hbS y).support.card) :
    (LinearIndependent.repr hbS x1).support.card = 1 := by
  by_contra hcard
  have hlt : 1 < (LinearIndependent.repr hbS x1).support.card := by
    have hpos : 0 < (LinearIndependent.repr hbS x1).support.card := by
      rw [Finset.card_pos]
      exact Finsupp.support_nonempty_iff.mpr (by
        intro h
        apply hx1_ne
        have hlc := LinearIndependent.linearCombination_repr hbS x1
        rw [show LinearIndependent.repr hbS x1 = 0 from h] at hlc
        simpa using hlc.symm)
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hlt
  obtain ⟨h, hh, hdiag, c, d, hcd, hci, hdj⟩ := hsep i j hij
  let e : S → K := fun k => Classical.choose (hdiag k)
  have he : ∀ k : S, h (bS k) = e k • bS k := fun k => Classical.choose_spec (hdiag k)
  have hei : e i = c := diagonalCoeff_eq hbS he hci
  have hej : e j = d := diagonalCoeff_eq hbS he hdj
  obtain ⟨y, hyeq, hycard, hy_ne⟩ := exists_smaller_support hbS he hei hej hcd x1 hi hj
  have hyX : y.1 ∈ X := by
    rw [hyeq]
    exact X.sub_mem (hXinv h hh x1.1 hx1X) (X.smul_mem c hx1X)
  exact absurd (hmin y hyX hy_ne) (not_le.mpr hycard)

private theorem span_le_of_support_card_eq_one {S : Type*} {bS : S → V}
    (hbS : LinearIndependent K bS) {B : Subgroup (V ≃ₗ[K] V)}
    (htrans : ∀ i j : S, ∃ h ∈ B, ∃ c : K, c ≠ 0 ∧ h (bS i) = c • bS j)
    {X : Submodule K V} (hXinv : ∀ h ∈ B, ∀ x ∈ X, h x ∈ X)
    {x1 : Submodule.span K (Set.range bS)} (hx1X : x1.1 ∈ X)
    (hsing : (LinearIndependent.repr hbS x1).support.card = 1) :
    Submodule.span K (Set.range bS) ≤ X := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsing
  have hx1_eq : x1.1 = (LinearIndependent.repr hbS x1 i) • bS i := by
    have hl : LinearIndependent.repr hbS x1 =
        Finsupp.single i (LinearIndependent.repr hbS x1 i) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · have hk' : k ∉ (LinearIndependent.repr hbS x1).support := by rw [hi]; simp [hk]
        have hk0 : LinearIndependent.repr hbS x1 k = 0 := by
          by_contra h
          exact hk' (Finsupp.mem_support_iff.mpr h)
        rw [hk0]
        simp [Finsupp.single_eq_of_ne hk]
    calc x1.1 = Finsupp.linearCombination K bS (LinearIndependent.repr hbS x1) :=
          (LinearIndependent.linearCombination_repr hbS x1).symm
      _ = Finsupp.linearCombination K bS (Finsupp.single i (LinearIndependent.repr hbS x1 i)) := by
          conv_lhs => rw [hl]
      _ = (LinearIndependent.repr hbS x1 i) • bS i := by
          rw [Finsupp.linearCombination_single]
  have ha_ne : LinearIndependent.repr hbS x1 i ≠ 0 := by
    rw [← Finsupp.mem_support_iff]
    rw [hi]; exact Finset.mem_singleton_self i
  have hbiX : bS i ∈ X := by
    have hmem : (LinearIndependent.repr hbS x1 i)⁻¹ • x1.1 ∈ X := X.smul_mem _ hx1X
    rw [hx1_eq, smul_smul, inv_mul_cancel₀ ha_ne, one_smul] at hmem
    exact hmem
  rw [Submodule.span_le]
  rintro y ⟨j, rfl⟩
  obtain ⟨h', hh', c', hc', hci'⟩ := htrans i j
  have hmem : h' (bS i) ∈ X := hXinv h' hh' (bS i) hbiX
  rw [hci'] at hmem
  have : bS j = c'⁻¹ • (c' • bS j) := by rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [this]
  exact X.smul_mem _ hmem

theorem irredOnSection_span_of_separating {ι : Type*} {b : ι → V}
    (hb : LinearIndependent K b) {S : Set ι} {B : Subgroup (V ≃ₗ[K] V)}
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∃ h ∈ B, (∀ k ∈ S, ∃ e : K, h (b k) = e • b k) ∧
      ∃ c d : K, c ≠ d ∧ h (b i) = c • b i ∧ h (b j) = d • b j)
    (htrans : ∀ i ∈ S, ∀ j ∈ S, ∃ h ∈ B, ∃ c : K, c ≠ 0 ∧ h (b i) = c • b j) :
    IrredOnSection B ⊥ (Submodule.span K (b '' S)) := by
  intro X hXbot hXle hXinv
  by_cases hX : X = ⊥
  · exact Or.inl hX
  · right
    classical
    let bS : S → V := fun i => b i.1
    have hbS : LinearIndependent K bS := by
      simpa [bS, Function.comp_def] using hb.comp (fun i : S => i.1) (fun _ _ h => Subtype.ext h)
    let M' := Submodule.span K (Set.range bS)
    have hM' : M' = Submodule.span K (b '' S) := by
      dsimp [M']
      congr 1
      ext x
      simp [bS, Set.mem_range, Set.mem_image]
    have hXle' : X ≤ M' := by rw [hM']; exact hXle
    have hsepS : ∀ i j : S, i ≠ j → ∃ h ∈ B, (∀ k : S, ∃ e : K, h (bS k) = e • bS k) ∧
        ∃ c d : K, c ≠ d ∧ h (bS i) = c • bS i ∧ h (bS j) = d • bS j := by
      intro i j hij
      obtain ⟨h, hh, hdiag, c, d, hcd, hci, hdj⟩ :=
        hsep i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
      exact ⟨h, hh, fun k => hdiag k.1 k.2, c, d, hcd, hci, hdj⟩
    obtain ⟨x1, hx1X, hx1_ne, hx1_min⟩ := exists_minimal_support hbS hXle' hX
    have hsing : (LinearIndependent.repr hbS x1).support.card = 1 :=
      support_card_eq_one_of_separating hbS hsepS hXinv hx1X hx1_ne hx1_min
    have hMle : M' ≤ X :=
      span_le_of_support_card_eq_one hbS (fun i j => htrans i.1 i.2 j.1 j.2) hXinv hx1X hsing
    rw [hM'] at hMle
    exact le_antisymm hXle hMle
end Field

section Defs

variable (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def fixReflSubgroup (J : Subgroup (U ≃ₗ[ZMod p] U)) (v : U) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {t | t ∈ J ∧ IsRefl p t ∧ t v = v}

end Defs

section Prime

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem fixReflSubgroup_le (J : Subgroup (U ≃ₗ[ZMod p] U)) (v : U) :
    fixReflSubgroup p J v ≤ J := by
  rw [fixReflSubgroup, Subgroup.closure_le]
  intro x hx
  exact hx.1

theorem reflGen_fixReflSubgroup (J : Subgroup (U ≃ₗ[ZMod p] U)) (v : U) :
    ReflGen p (fixReflSubgroup p J v) := by
  unfold ReflGen
  apply le_antisymm
  · rw [fixReflSubgroup, Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2.1⟩
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1

theorem mem_fixReflSubgroup {J : Subgroup (U ≃ₗ[ZMod p] U)} {v : U} {t : U ≃ₗ[ZMod p] U}
    (ht : t ∈ J) (hrt : IsRefl p t) (htv : t v = v) : t ∈ fixReflSubgroup p J v := by
  rw [fixReflSubgroup]
  exact Subgroup.subset_closure ⟨ht, hrt, htv⟩

theorem fixReflSubgroup_apply_eq {J : Subgroup (U ≃ₗ[ZMod p] U)} {v : U}
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ fixReflSubgroup p J v) : h v = v := by
  rw [fixReflSubgroup] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx.2.2
  | one => simp
  | mul x y hx hy ihx ihy => rw [LinearEquiv.mul_apply, ihy, ihx]
  | inv x hx ihx =>
      have h := congrArg x.symm ihx
      simpa using h.symm

theorem throughRefl_of_forall_conj {J : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (S : Set (U ≃ₗ[ZMod p] U))
    (hS : ∀ s ∈ S, ∃ B : Subgroup (U ≃ₗ[ZMod p] U), B ≤ J ∧ s ∈ B ∧ ReflGen p B ∧
      SplitSupport B l)
    (hconj : ∀ r ∈ J, IsRefl p r → ∃ g ∈ J, ∃ s ∈ S, r = g * s * g⁻¹) :
    ThroughRefl p l J := by
  intro r hr hrr
  obtain ⟨g, hg, s, hs, hrs⟩ := hconj r hr hrr
  obtain ⟨B, hBJ, hsB, hB, hsplit⟩ := hS s hs
  refine ⟨B.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    exact J.mul_mem (J.mul_mem hg (hBJ hb)) (J.inv_mem hg)
  · rw [hrs]
    exact Subgroup.mem_map_of_mem _ hsB
  · exact reflGen_map_conj g hB
  · exact splitSupport_map_conj g hsplit

theorem throughRefl_of_oneClass {J : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hone : OneClass p J)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} (hBJ : B ≤ J) {x : U ≃ₗ[ZMod p] U} (hxB : x ∈ B)
    (hx : IsRefl p x) (hB : ReflGen p B) (hs : SplitSupport B l) : ThroughRefl p l J := by
  intro r hr hrr
  obtain ⟨g, hg, hgs⟩ := hone x (hBJ hxB) r hr hx hrr
  refine ⟨B.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    exact J.mul_mem (J.mul_mem hg (hBJ hb)) (J.inv_mem hg)
  · rw [hgs]
    exact Subgroup.mem_map_of_mem _ hxB
  · exact reflGen_map_conj g hB
  · exact splitSupport_map_conj g hs

theorem exists_isRefl_of_splitSupport {N : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hN : ReflGen p N) (hs : SplitSupport N l) (hl : 0 < l) : ∃ x ∈ N, IsRefl p x := by
  by_contra h
  have hNbot : N = ⊥ := by
    have hS : {t | t ∈ N ∧ IsRefl p t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hrefl => h ⟨x, hx, hrefl⟩
    rw [hN, hS, Subgroup.closure_empty]
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace N) = 0 := by
    have hbot : HardMathSupport.Kantor79.commutatorSpace
        (⊥ : Subgroup (U ≃ₗ[ZMod p] U)) = ⊥ := by
      rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_eq_bot]
      rintro w ⟨g, hg, v, rfl⟩
      have hg1 : g = 1 := by simpa using hg
      rw [hg1]
      simp
    rw [hNbot, hbot, finrank_bot]
  have hfin' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace N) = l := hs.2.1
  rw [hfin'] at hfin
  omega

private theorem splitSupport_closure_singleton (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : U ≃ₗ[ZMod p] U} (hrr : IsRefl p r) :
    SplitSupport (Subgroup.closure {r}) 1 := by
  have hcl : Subgroup.closure (Set.range (fun _ : Fin 1 => r)) = Subgroup.closure {r} := by
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rfl
    · intro hy
      exact ⟨0, hy.symm⟩
  rw [← hcl]
  have hsup : (⨆ _ : Fin 1, HardMathSupport.Kantor79.movedSpace r) =
      HardMathSupport.Kantor79.movedSpace r := by
    apply le_antisymm
    · exact iSup_le fun _ => le_rfl
    · exact le_iSup (fun _ : Fin 1 => HardMathSupport.Kantor79.movedSpace r) 0
  have hdim : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (Set.range (fun _ : Fin 1 => r)))) = 1 := by
    rw [HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace, hsup]
    exact hrr.2
  refine splitSupport_of_isRefl hp (fun _ : Fin 1 => r) (fun _ => hrr) hdim ?_
  intro X hX hXle hXinv
  have hdimX : Module.finrank (ZMod p) X ≤ 1 := by
    rw [← hdim]
    exact Submodule.finrank_mono hXle
  rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) X) with h0 | hpos
  · left
    exact (Submodule.finrank_eq_zero).mp h0
  · right
    have h1 : Module.finrank (ZMod p) X = 1 := by omega
    apply Submodule.eq_of_le_of_finrank_eq hXle
    rw [h1, hdim]

theorem throughRefl_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (J : Subgroup (U ≃ₗ[ZMod p] U)) : ThroughRefl p 1 J := by
  intro r hr hrr
  refine ⟨Subgroup.closure {r}, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hr
  · exact Subgroup.subset_closure (Set.mem_singleton r)
  · rw [ReflGen]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Set.mem_singleton r), hrr⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  · exact splitSupport_closure_singleton hp hrr

theorem coprimeWitness_of_neg_mem (hp : p ≠ 2) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J) : CoprimeWitness p J := by
  let D : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.zpowers (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U)
  have hDle : D ≤ J := by
    change Subgroup.zpowers (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ≤ J
    rw [Subgroup.zpowers_le]
    exact h
  have hcard : Nat.card D ∣ 2 := by
    change Nat.card (Subgroup.zpowers (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U)) ∣ 2
    rw [Nat.card_zpowers]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    ext v
    simp [pow_two]
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hp2 : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hdiv
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hdiv))
  have hcop : Nat.Coprime (Nat.card D) p := Nat.Coprime.coprime_dvd_left hcard hp2
  have hcomm : HardMathSupport.Kantor79.commutatorSpace D = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ D := by
      change (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈
        Subgroup.zpowers (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U)
      exact Subgroup.mem_zpowers _
    have hmem : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) v - v ∈
        HardMathSupport.Kantor79.commutatorSpace D := by
      rw [HardMathSupport.Kantor79.commutatorSpace]
      exact Submodule.subset_span ⟨_, hneg, v, rfl⟩
    have hv : v = (-(2 : ZMod p))⁻¹ •
        ((LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) v - v) := by
      rw [LinearEquiv.neg_apply]
      have h : -v - v = (-(2 : ZMod p)) • v := by
        rw [show (-(2 : ZMod p)) • v = -((2 : ZMod p) • v) from neg_smul _ _]
        rw [two_smul]
        abel
      rw [h]
      exact (inv_smul_smul₀ (neg_ne_zero.mpr h2) v).symm
    rw [hv]
    exact Submodule.smul_mem _ _ hmem
  exact ⟨D, hDle, hcop, hcomm⟩

private theorem scalar_eq_neg_one {c : ZMod p} (hc2 : c * c = 1) (hc_ne_one : c ≠ 1) :
    c = -1 := by
  have h : (c - 1) * (c + 1) = 0 := by linear_combination hc2
  rcases mul_eq_zero.mp h with h1 | h1
  · exfalso; exact hc_ne_one (sub_eq_zero.mp h1)
  · exact eq_neg_of_add_eq_zero_left h1

private theorem eq_neg_of_order_two_of_comm {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : AbsIrred p J) {z : U ≃ₗ[ZMod p] U} (hz : orderOf z = 2)
    (hcomm : ∀ a ∈ J, (z : U →ₗ[ZMod p] U) ∘ₗ (a : U →ₗ[ZMod p] U) =
      (a : U →ₗ[ZMod p] U) ∘ₗ (z : U →ₗ[ZMod p] U)) :
    z = LinearEquiv.neg (ZMod p) := by
  have hz_ne_one : z ≠ 1 := by
    intro h
    have : orderOf z = 1 := by rw [h, orderOf_one]
    rw [hz] at this
    omega
  obtain ⟨c, hc⟩ := hA.2 (z : U →ₗ[ZMod p] U) hcomm
  have h_exists : ∃ v : U, z v ≠ v := by
    by_contra h
    push Not at h
    exact hz_ne_one (LinearEquiv.ext h)
  obtain ⟨v, hv⟩ := h_exists
  have hv0 : v ≠ 0 := by
    intro h0
    exact hv (by rw [h0, map_zero])
  have hzv : z v = c • v := by
    have := congrArg (fun T : U →ₗ[ZMod p] U => T v) hc
    simpa using this
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    apply hv
    rw [hzv, hc1, one_smul]
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hc2 : c * c = 1 := by
    have hzz : z (z v) = v := by
      have hz2' := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hz2
      simpa [pow_two, LinearEquiv.mul_apply] using hz2'
    have h1 : z (z v) = c • (c • v) := by rw [hzv, map_smul, hzv]
    have h2 : c • (c • v) = v := by rw [← h1, hzz]
    have h3 : (c * c) • v = v := by simpa [smul_smul] using h2
    have h4 : (c * c - 1) • v = 0 := by rw [sub_smul, h3, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hv0)
  have hc_eq : c = -1 := scalar_eq_neg_one hc2 hc_ne_one
  ext w
  calc z w = (z : U →ₗ[ZMod p] U) w := rfl
    _ = (c • LinearMap.id : U →ₗ[ZMod p] U) w := by rw [hc]
    _ = c • w := by simp
    _ = (-1 : ZMod p) • w := by rw [hc_eq]
    _ = (LinearEquiv.neg (ZMod p)) w := by
      rw [LinearEquiv.neg_apply]
      exact neg_one_smul (ZMod p) w

theorem neg_mem_of_two_dvd_card_center {J : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p J)
    (h2 : 2 ∣ Nat.card (Subgroup.center J)) (h0 : Nat.card (Subgroup.center J) ≠ 0) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  have hfin : Finite (Subgroup.center J) := (Nat.card_ne_zero.mp h0).2
  obtain ⟨z, hz⟩ := @exists_prime_orderOf_dvd_card' (Subgroup.center J) _ hfin 2 ⟨by norm_num⟩ h2
  let zU : U ≃ₗ[ZMod p] U := (z : J)
  have hzU : orderOf zU = 2 := by
    dsimp only [zU]
    exact (Subgroup.orderOf_coe (z : J)).trans ((Subgroup.orderOf_coe z).trans hz)
  have hz_comm : ∀ a ∈ J, (zU : U →ₗ[ZMod p] U) ∘ₗ (a : U →ₗ[ZMod p] U) =
      (a : U →ₗ[ZMod p] U) ∘ₗ (zU : U →ₗ[ZMod p] U) := by
    intro a ha
    have h := (Subgroup.mem_center_iff.mp z.2) ⟨a, ha⟩
    have h2' : zU * a = a * zU := by
      simpa [zU] using (congrArg (fun w : J => (w : U ≃ₗ[ZMod p] U)) h).symm
    simpa only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp] using
      congrArg (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U)) h2'
  have hz_eq : zU = LinearEquiv.neg (ZMod p) :=
    eq_neg_of_order_two_of_comm hA hzU hz_comm
  rw [← hz_eq]
  exact (z : J).2

end Prime

end CFSG.StandardType.ZS

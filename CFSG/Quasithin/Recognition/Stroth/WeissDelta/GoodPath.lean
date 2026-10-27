module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalFacts

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

@[expose] def WeissLemma4 (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V) (n : ℕ) :
    Prop :=
  ∀ w : GPath Γ (n + 1), w.NoBack → ∀ i, 0 < i → i < n →
    ∀ z, Γ.Adj (w n) z → z ≠ w (n - 1) → z ≠ w (n + 1) →
      ∃ g ∈ GPath.stabPath (H := H) w ⊓ fixingSubgroup H (Γ.neighborSet (w i)), g • z ≠ z

@[expose] def WeissLemma4' (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V) (n : ℕ) :
    Prop :=
  ∀ w : GPath Γ (n + 1), w.NoBack → ∀ i, 0 < i → i < n →
    ∀ z, Γ.Adj (w i) z → z ≠ w (i - 1) → z ≠ w (i + 1) →
      ∃ g ∈ fixingSubgroup H (Γ.neighborSet (w 0)) ⊓ GPath.stabPath (H := H) w, g • z ≠ z

theorem exists_smul_of_mem_stabPath_take_fixing {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {s : ℕ} {p : GPath Γ s} (hp : p.NoBack) {i : ℕ} (hi1 : 1 ≤ i) (his : i ≤ s)
    (hin : i ≤ n) {y y' : V} (hy : Γ.Adj (p i) y) (hy' : Γ.Adj (p i) y')
    (hyne : y ≠ p (i - 1)) (hy'ne : y' ≠ p (i - 1)) :
    ∃ g : H, g ∈ (p.take i his).stabPath ∧
      (∀ j, 1 ≤ j → j < i → g ∈ fixingSubgroup H (Γ.neighborSet (p j))) ∧ g • y = y' := by
  have hsi : 1 ≤ s := le_trans hi1 his
  have h0 : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
  by_cases hin' : i = n
  · subst i
    have hqnb : (p.take n his).NoBack := hp.take n his
    have hqn : (p.take n his) n = p n := GPath.take_apply_of_le _ _ _ le_rfl
    have hqn1 : (p.take n his) (n - 1) = p (n - 1) :=
      GPath.take_apply_of_le _ _ _ (by omega)
    obtain ⟨g, hgfix, hgy⟩ := hM (p.take n his) hqnb y y'
      (by rwa [hqn]) (by rwa [hqn]) (by rwa [hqn1]) (by rwa [hqn1])
    refine ⟨g, ?_, ?_, hgy⟩
    · have hgU : g ∈ pathRootGroup H Γ (p.take n his) := mem_pathRootGroup.mpr hgfix
      have hfixq := smul_path_eq_self_of_mem_pathRootGroup hn hgU
      rw [GPath.mem_stabPath_iff]
      intro j hj
      simpa only [GPath.take_apply_of_le _ _ _ hj] using hfixq j hj
    · intro j hj1 hji
      have hgU : g ∈ pathRootGroup H Γ (p.take n his) := mem_pathRootGroup.mpr hgfix
      have hval : (p.take n his) j = p j := GPath.take_apply_of_le _ _ _ (by omega)
      exact (mem_fixingSubgroup_iff H).mpr fun w hw =>
        (mem_pathRootGroup.mp hgU) j (by omega) (by omega) w (by rwa [hval])
  · have hkpos : 0 < n - i := by omega
    obtain ⟨r, hrnb, hrk, hrprev⟩ :=
      exists_backward_noBack hne (x := p 0) (z := p 1) h0 (n - i)
    have hjoin : r (n - i) = (p.take i his) 0 := by
      rw [hrk, GPath.take_apply_of_le _ _ _ (Nat.zero_le i)]
    have hcross : r ((n - i) - 1) ≠ (p.take i his) 1 := by
      rw [GPath.take_apply_of_le _ _ _ hi1]
      exact hrprev hkpos
    have hq2nb : (GPath.append r (p.take i his) hjoin).NoBack :=
      GPath.noBack_append r (p.take i his) hjoin hrnb (hp.take i his) hkpos hi1 hcross
    let q := GPath.castLength (Nat.sub_add_cancel hin) (GPath.append r (p.take i his) hjoin)
    have hqnb : q.NoBack := GPath.castLength_noBack _ hq2nb
    have hqn : q n = p i := by
      have hcast : q n = (GPath.append r (p.take i his) hjoin) ((n - i) + i) :=
        congrArg (GPath.append r (p.take i his) hjoin).toFun (Nat.sub_add_cancel hin).symm
      rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
      rw [show (n - i) + i - (n - i) = i by omega, GPath.take_apply_of_le _ _ _ le_rfl]
    have hqn1 : q (n - 1) = p (i - 1) := by
      have hcast : q (n - 1) = (GPath.append r (p.take i his) hjoin) ((n - i) + i - 1) :=
        congrArg (GPath.append r (p.take i his) hjoin).toFun
          (by omega : n - 1 = (n - i) + i - 1)
      rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
      rw [show (n - i) + i - 1 - (n - i) = i - 1 by omega,
        GPath.take_apply_of_le _ _ _ (by omega)]
    obtain ⟨g, hgfix, hgy⟩ := hM q hqnb y y'
      (by rwa [hqn]) (by rwa [hqn]) (by rw [hqn1]; exact hyne)
      (by rw [hqn1]; exact hy'ne)
    refine ⟨g, ?_, ?_, hgy⟩
    · have hgU : g ∈ pathRootGroup H Γ q := mem_pathRootGroup.mpr hgfix
      have hfixq := smul_path_eq_self_of_mem_pathRootGroup hn hgU
      rw [GPath.mem_stabPath_iff]
      intro j hj
      have hval : q ((n - i) + j) = (p.take i his) j := by
        have hcast : q ((n - i) + j) =
            (GPath.append r (p.take i his) hjoin) ((n - i) + j) := rfl
        rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
        rw [show (n - i) + j - (n - i) = j by omega]
      have hval' : q ((n - i) + j) = p j := by
        rw [hval, GPath.take_apply_of_le _ _ _ hj]
      have h := hfixq ((n - i) + j) (by omega)
      rw [hval'] at h
      simpa only [GPath.take_apply_of_le _ _ _ hj] using h
    · intro j hj1 hji
      have hgU : g ∈ pathRootGroup H Γ q := mem_pathRootGroup.mpr hgfix
      have hval : q ((n - i) + j) = p j := by
        have hcast : q ((n - i) + j) =
            (GPath.append r (p.take i his) hjoin) ((n - i) + j) := rfl
        rw [hcast, GPath.append_apply_right _ _ _ (by omega)]
        rw [show (n - i) + j - (n - i) = j by omega,
          GPath.take_apply_of_le _ _ _ (by omega)]
      exact (mem_fixingSubgroup_iff H).mpr fun w hw =>
        (mem_pathRootGroup.mp hgU) ((n - i) + j) (by omega) (by omega) w (by rwa [hval])

variable (H) in
@[expose] def IsGoodPath {s : ℕ} (p : GPath Γ s) : Prop :=
  p.NoBack ∧ ∀ i, 0 < i → i < s →
    socTorus H Γ (p i) (p (i - 1)) (p (i + 1)) ≤
      (GPath.stabPath (H := H) p ⊓ socleAt H Γ (p i)) ⊔ fixingSubgroup H (Γ.neighborSet (p i))

theorem IsGoodPath.take {s : ℕ} {p : GPath Γ s} (hp : IsGoodPath H p) (k : ℕ) (hk : k ≤ s) :
    IsGoodPath H (p.take k hk) := by
  refine ⟨hp.1.take k hk, ?_⟩
  intro i hi0 hik
  have hi : i ≤ k := by omega
  have him1 : i - 1 ≤ k := by omega
  have hip1 : i + 1 ≤ k := by omega
  have hgood := hp.2 i (by omega) (by omega)
  have hqi : (p.take k hk) i = p i := GPath.take_apply_of_le _ _ _ hi
  have hqim1 : (p.take k hk) (i - 1) = p (i - 1) := GPath.take_apply_of_le _ _ _ him1
  have hqip1 : (p.take k hk) (i + 1) = p (i + 1) := GPath.take_apply_of_le _ _ _ hip1
  rw [hqi, hqim1, hqip1]
  refine le_trans hgood (sup_le_sup (inf_le_inf_right _ ?_) le_rfl)
  intro g hg l hl
  rw [GPath.take_apply_of_le _ _ _ hl]
  exact hg l (by omega)

theorem IsGoodPath.drop {s : ℕ} {p : GPath Γ s} (hp : IsGoodPath H p) (k : ℕ) (hk : k ≤ s) :
    IsGoodPath H (p.drop k hk) := by
  refine ⟨hp.1.drop k hk, ?_⟩
  intro i hi0 hisub
  have hkis : k + i < s := by omega
  have hgood := hp.2 (k + i) (by omega) hkis
  have hqi : (p.drop k hk) i = p (k + i) := GPath.drop_apply _ _ _ (by omega)
  have hqim1 : (p.drop k hk) (i - 1) = p (k + (i - 1)) := GPath.drop_apply _ _ _ (by omega)
  have hqip1 : (p.drop k hk) (i + 1) = p (k + (i + 1)) := GPath.drop_apply _ _ _ (by omega)
  rw [hqi, hqim1, hqip1,
    show k + (i - 1) = k + i - 1 by omega,
    show k + (i + 1) = k + i + 1 by omega]
  exact le_trans hgood
    (sup_le_sup (inf_le_inf_right _ (GPath.stabPath_le_drop p k hk)) le_rfl)

theorem IsGoodPath.rev {s : ℕ} {p : GPath Γ s} (hp : IsGoodPath H p) : IsGoodPath H p.rev := by
  refine ⟨hp.1.rev, ?_⟩
  intro i hi0 his
  have hgood := hp.2 (s - i) (by omega) (by omega)
  have hqi : p.rev i = p (s - i) := GPath.rev_apply _ (by omega)
  have hqim1 : p.rev (i - 1) = p (s - i + 1) := by
    rw [GPath.rev_apply _ (by omega), show s - (i - 1) = s - i + 1 by omega]
  have hqip1 : p.rev (i + 1) = p (s - i - 1) := by
    rw [GPath.rev_apply _ (by omega), show s - (i + 1) = s - i - 1 by omega]
  rw [hqi, hqim1, hqip1, socTorus_comm, GPath.stabPath_rev]
  exact hgood

theorem IsGoodPath.smul {s : ℕ} {p : GPath Γ s} (hp : IsGoodPath H p) (g : H) :
    IsGoodPath H (g • p) := by
  refine ⟨GPath.smul_noBack (g := g) hp.1, ?_⟩
  intro i hi0 his
  have hgood := hp.2 i hi0 his
  have hqi : (g • p) i = g • p i := rfl
  have hqim1 : (g • p) (i - 1) = g • p (i - 1) := rfl
  have hqip1 : (g • p) (i + 1) = g • p (i + 1) := rfl
  rw [hqi, hqim1, hqip1,
    socTorus_smul (H := H) (Γ := Γ) g (p i) (p (i - 1)) (p (i + 1))]
  have hstab : ((g • p).stabPath : Subgroup H) =
      (p.stabPath).map (MulAut.conj g).toMonoidHom := by
    rw [GPath.stabPath_smul]
    rfl
  have hsoc := socleAt_smul (H := H) (Γ := Γ) g (p i)
  have hfix := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g (p i)
  rw [hstab, hsoc, hfix, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_sup]
  exact Subgroup.map_mono hgood

theorem isGoodPath_castLength {m k : ℕ} (h : m = k) {p : GPath Γ m} :
    IsGoodPath H (GPath.castLength h p) ↔ IsGoodPath H p := by
  subst h
  rfl

theorem pathRootGroup_rev_eq {n : ℕ} (p : GPath Γ n) :
    pathRootGroup H Γ p.rev = pathRootGroup H Γ p := by
  ext g
  rw [mem_pathRootGroup, mem_pathRootGroup]
  constructor
  · intro h i hi1 hi2 w hw
    have hrev : p.rev (n - i) = p i := by
      rw [GPath.rev_apply _ (by omega), show n - (n - i) = i by omega]
    exact h (n - i) (by omega) (by omega) w (by rwa [hrev])
  · intro h i hi1 hi2 w hw
    have hrev : p.rev i = p (n - i) := GPath.rev_apply _ (by omega)
    exact h (n - i) (by omega) (by omega) w (by rwa [← hrev])

theorem pathRootGroup_smul_eq {n : ℕ} (p : GPath Γ n) (g : H) :
    pathRootGroup H Γ (g • p) = (pathRootGroup H Γ p).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_pathRootGroup] at hx ⊢
      intro i hi1 hi2 w hw
      have hAdj : Γ.Adj ((g • p) i) (g • w) :=
        (GraphAction.adj_smul g (p i) w).mpr hw
      have hfix := hx i hi1 hi2 (g • w) (by simpa using hAdj)
      show (g⁻¹ * x * g) • w = w
      rw [mul_smul, mul_smul, hfix, inv_smul_smul]
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
  · rintro ⟨y, hy, rfl⟩
    rw [mem_pathRootGroup] at hy ⊢
    intro i hi1 hi2 w hw
    have hAdj : Γ.Adj (p i) (g⁻¹ • w) := by
      apply (GraphAction.adj_smul g (p i) (g⁻¹ • w)).mp
      rwa [smul_inv_smul]
    have hfix := hy i hi1 hi2 (g⁻¹ • w) hAdj
    show (MulAut.conj g) y • w = w
    rw [MulAut.conj_apply]
    calc
      (g * y * g⁻¹) • w = g • (y • (g⁻¹ • w)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • w) := by rw [hfix]
      _ = w := by rw [smul_inv_smul]

theorem stabilizer_le_normalizer_fixingSubgroup {z : V} :
    MulAction.stabilizer H z ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet z) : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have haz : a • z = z := MulAction.mem_stabilizer_iff.mp ha
  have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) a z
  rw [haz] at h
  exact h.symm

private theorem socleAt_le_normalizer_fixingSubgroup (z : V) :
    socleAt H Γ z ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet z) : Set H) := by
  unfold socleAt
  refine sup_le ?_ ?_
  · intro a ha
    exact stabilizer_le_normalizer_fixingSubgroup
      (Subgroup.map_subtype_le (CFSG.perfectResidual ↥(MulAction.stabilizer H z)) ha)
  · intro a ha
    exact Subgroup.le_normalizer ha

private theorem pathRootGroup_le_stabilizer {n : ℕ} (hn : 2 ≤ n) (p : GPath Γ n) :
    pathRootGroup H Γ p ≤ MulAction.stabilizer H (p n) := by
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  have hv : Γ.Adj (p (n - 1)) (p n) := by
    have h := p.adj (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at h
  exact (mem_pathRootGroup.mp hx) (n - 1) (by omega) (by omega) (p n) hv

private theorem backward_step {n s i m : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {p : GPath Γ s} (hp : p.NoBack) (hi1 : 1 ≤ i) (his1 : i + 1 ≤ s)
    (hin : i ≤ n) (hm1 : 1 ≤ m) (hmi : m < i)
    {t : H} (ht : t ∈ socleAt H Γ (p i))
    (hfix : ∀ l, i - m ≤ l → l ≤ i + 1 → t • p l = p l) :
    ∃ g ∈ fixingSubgroup H (Γ.neighborSet (p i)),
      (g * t) ∈ socleAt H Γ (p i) ∧
      ∀ l, i - (m + 1) ≤ l → l ≤ i + 1 → (g * t) • p l = p l := by
  classical
  let rpath : GPath Γ (i + 1) := (p.take (i + 1) his1).rev
  have hrpath_nb : rpath.NoBack := (hp.take (i + 1) his1).rev
  have hr_apply : ∀ l, l ≤ i + 1 → rpath l = p (i + 1 - l) := by
    intro l hl
    show ((p.take (i + 1) his1).rev) l = p (i + 1 - l)
    rw [GPath.rev_apply _ hl, GPath.take_apply_of_le _ _ _ (by omega)]
  have hji1 : m + 1 ≤ i := by omega
  have hji : m + 1 ≤ i + 1 := by omega
  have hjs : m + 1 < i + 1 := by omega
  have hbase : t • rpath ((m + 1) - 1) = rpath ((m + 1) - 1) := by
    rw [hr_apply ((m + 1) - 1) (by omega)]
    exact hfix (i + 1 - ((m + 1) - 1)) (by omega) (by omega)
  have htj : t • rpath (m + 1) = rpath (m + 1) := by
    rw [hr_apply (m + 1) hji]
    exact hfix (i + 1 - (m + 1)) (by omega) (by omega)
  have hy : Γ.Adj ((t • rpath) (m + 1)) (t • rpath ((m + 1) + 1)) :=
    (GraphAction.adj_smul t (rpath (m + 1)) (rpath ((m + 1) + 1))).mpr
      (rpath.adj (m + 1) hjs)
  have hy' : Γ.Adj ((t • rpath) (m + 1)) (rpath ((m + 1) + 1)) := by
    change Γ.Adj (t • rpath (m + 1)) (rpath ((m + 1) + 1))
    rw [htj]
    exact rpath.adj (m + 1) hjs
  have hnb : rpath ((m + 1) + 1) ≠ rpath ((m + 1) - 1) := by
    have h := hrpath_nb ((m + 1) - 1) (by omega)
    rw [show (m + 1) - 1 + 2 = (m + 1) + 1 by omega] at h
    exact h.symm
  have hyne : t • rpath ((m + 1) + 1) ≠ t • rpath ((m + 1) - 1) := by
    intro h
    exact hnb (MulAction.injective t h)
  have hy'ne : rpath ((m + 1) + 1) ≠ t • rpath ((m + 1) - 1) := by
    intro h
    exact hnb (h.trans hbase)
  obtain ⟨g, hgstab, hgneigh, hgy⟩ :=
    exists_smul_of_mem_stabPath_take_fixing (n := n) hn hM hne
      (p := t • rpath) (hp := GPath.smul_noBack (g := t) hrpath_nb) (i := m + 1)
      (by omega) hji (by omega) hy hy' hyne hy'ne
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet ((t • rpath) 1)) :=
    hgneigh 1 (by omega) (by omega)
  have h1eq : (t • rpath) 1 = p i := by
    change t • rpath 1 = p i
    rw [hr_apply 1 (by omega), show i + 1 - 1 = i by omega]
    exact hfix i (by omega) (by omega)
  have hgG1 : g ∈ fixingSubgroup H (Γ.neighborSet (p i)) := by
    rwa [h1eq] at hg1
  have hstep_le : ∀ l, l ≤ m + 1 → (g * t) • rpath l = rpath l := by
    intro l hl
    have htl : t • rpath l = rpath l := by
      rw [hr_apply l (by omega)]
      exact hfix (i + 1 - l) (by omega) (by omega)
    have hgl := (GPath.mem_stabPath_iff.mp hgstab) l hl
    rw [GPath.take_apply_of_le _ _ _ hl] at hgl
    change g • (t • rpath l) = t • rpath l at hgl
    rw [htl] at hgl
    rw [mul_smul, htl]
    exact hgl
  have hstep_succ : (g * t) • rpath ((m + 1) + 1) = rpath ((m + 1) + 1) := by
    rw [mul_smul]
    exact hgy
  refine ⟨g, hgG1, Subgroup.mul_mem _ (Subgroup.mem_sup_right hgG1) ht, ?_⟩
  intro l hl1 hl2
  have hqle : i + 1 - l ≤ (m + 1) + 1 := by omega
  have hrq : rpath (i + 1 - l) = p l := by
    rw [hr_apply (i + 1 - l) (by omega)]
    congr 1
    omega
  by_cases hq : i + 1 - l ≤ m + 1
  · have h := hstep_le (i + 1 - l) hq
    rwa [hrq] at h
  · have hqeq : i + 1 - l = (m + 1) + 1 := by omega
    rw [← hrq, hqeq]
    exact hstep_succ

private theorem forward_step {n s i j : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {p : GPath Γ s} (hp : p.NoBack) (hi1 : 1 ≤ i) (hij : i < j)
    (hjs : j < s) (hjn : j ≤ n)
    {t : H} (ht : t ∈ socleAt H Γ (p i))
    (hfix : ∀ l, l ≤ j → t • p l = p l) :
    ∃ g ∈ fixingSubgroup H (Γ.neighborSet (p i)),
      (g * t) ∈ socleAt H Γ (p i) ∧ ∀ l, l ≤ j + 1 → (g * t) • p l = p l := by
  classical
  have hpnb : (t • p).NoBack := GPath.smul_noBack (g := t) hp
  have hbase : t • p (j - 1) = p (j - 1) := hfix (j - 1) (by omega)
  have htj : t • p j = p j := hfix j le_rfl
  have hy : Γ.Adj ((t • p) j) (t • p (j + 1)) :=
    (GraphAction.adj_smul t (p j) (p (j + 1))).mpr (p.adj j hjs)
  have hy' : Γ.Adj ((t • p) j) (p (j + 1)) := by
    change Γ.Adj (t • p j) (p (j + 1))
    rw [htj]
    exact p.adj j hjs
  have hnb : p (j + 1) ≠ p (j - 1) := by
    have h := hp (j - 1) (by omega)
    rw [show j - 1 + 2 = j + 1 by omega] at h
    exact h.symm
  have hyne : t • p (j + 1) ≠ t • p (j - 1) := by
    intro h
    exact hnb (MulAction.injective t h)
  have hy'ne : p (j + 1) ≠ t • p (j - 1) := by
    intro h
    exact hnb (h.trans hbase)
  obtain ⟨g, hgstab, hgneigh, hgy⟩ :=
    exists_smul_of_mem_stabPath_take_fixing (n := n) hn hM hne
      (p := t • p) (hp := hpnb) (i := j) (by omega) (by omega) hjn
      hy hy' hyne hy'ne
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet ((t • p) i)) :=
    hgneigh i hi1 hij
  have hieq : (t • p) i = p i := by
    change t • p i = p i
    exact hfix i (by omega)
  have hgG1 : g ∈ fixingSubgroup H (Γ.neighborSet (p i)) := by
    rwa [hieq] at hg1
  refine ⟨g, hgG1, Subgroup.mul_mem _ (Subgroup.mem_sup_right hgG1) ht, ?_⟩
  intro l hl
  rw [mul_smul]
  by_cases hlj : l ≤ j
  · have htl : t • p l = p l := hfix l hlj
    have hgl := (GPath.mem_stabPath_iff.mp hgstab) l hlj
    rw [GPath.take_apply_of_le _ _ _ hlj] at hgl
    change g • (t • p l) = t • p l at hgl
    rw [htl] at hgl
    rw [htl]
    exact hgl
  · have hleq : l = j + 1 := by omega
    rw [hleq]
    exact hgy

private theorem backward_iterate {n s i : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {p : GPath Γ s} (hp : p.NoBack) (hi1 : 1 ≤ i) (his : i ≤ s) (hin : i ≤ n)
    (his1 : i + 1 ≤ s) {t : H} (ht : t ∈ socleAt H Γ (p i))
    (hfix0 : ∀ l, i - 1 ≤ l → l ≤ i + 1 → t • p l = p l) :
    ∃ k ∈ fixingSubgroup H (Γ.neighborSet (p i)),
      (k * t) ∈ socleAt H Γ (p i) ∧ ∀ l, l ≤ i + 1 → (k * t) • p l = p l := by
  classical
  let motive : (r : ℕ) → r ≤ i - 1 → Prop := fun r _ =>
    ∀ t : H, t ∈ socleAt H Γ (p i) →
      (∀ l, i - (r + 1) ≤ l → l ≤ i + 1 → t • p l = p l) →
      ∃ k ∈ fixingSubgroup H (Γ.neighborSet (p i)),
        (k * t) ∈ socleAt H Γ (p i) ∧ ∀ l, l ≤ i + 1 → (k * t) • p l = p l
  have hself : motive (i - 1) le_rfl := by
    intro t ht hfix
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · simpa using ht
    · intro l hl
      simpa using hfix l (by omega) hl
  have hstep : ∀ r (hr : r < i - 1), motive (r + 1) hr → motive r (Nat.le_of_succ_le hr) := by
    intro r hr ih t ht hfix
    obtain ⟨g, hgG1, hgtSoc, hgtfix⟩ :=
      backward_step (m := r + 1) hn hM hne hp hi1 his1 hin (by omega) (by omega) ht hfix
    obtain ⟨k, hkG1, hktSoc, hktfix⟩ := ih (g * t) hgtSoc hgtfix
    refine ⟨k * g, Subgroup.mul_mem _ hkG1 hgG1, ?_, ?_⟩
    · rwa [mul_assoc]
    · intro l hl
      rw [mul_assoc]
      exact hktfix l hl
  have hres : motive 0 (by omega) :=
    Nat.decreasingInduction (motive := motive) hstep hself (by omega)
  exact hres t ht hfix0

private theorem forward_iterate {n s i : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {p : GPath Γ s} (hp : p.NoBack) (hi1 : 1 ≤ i) (his : i < s) (hin : i ≤ n)
    (hs : s ≤ n + 1) {t : H} (ht : t ∈ socleAt H Γ (p i))
    (hfix0 : ∀ l, l ≤ i + 1 → t • p l = p l) :
    ∃ k ∈ fixingSubgroup H (Γ.neighborSet (p i)),
      (k * t) ∈ socleAt H Γ (p i) ∧ ∀ l, l ≤ s → (k * t) • p l = p l := by
  classical
  let motive : (r : ℕ) → r ≤ s - i - 1 → Prop := fun r _ =>
    ∀ t : H, t ∈ socleAt H Γ (p i) →
      (∀ l, l ≤ i + 1 + r → t • p l = p l) →
      ∃ k ∈ fixingSubgroup H (Γ.neighborSet (p i)),
        (k * t) ∈ socleAt H Γ (p i) ∧ ∀ l, l ≤ s → (k * t) • p l = p l
  have hself : motive (s - i - 1) le_rfl := by
    intro t ht hfix
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · simpa using ht
    · intro l hl
      have hle : l ≤ i + 1 + (s - i - 1) := by omega
      simpa using hfix l hle
  have hstep : ∀ r (hr : r < s - i - 1), motive (r + 1) hr → motive r (Nat.le_of_succ_le hr) := by
    intro r hr ih t ht hfix
    have hjs : i + 1 + r < s := by omega
    have hjn : i + 1 + r ≤ n := by omega
    have hij : i < i + 1 + r := by omega
    obtain ⟨g, hgG1, hgtSoc, hgtfix⟩ :=
      forward_step (j := i + 1 + r) hn hM hne hp hi1 hij hjs hjn ht hfix
    have hgtfix' : ∀ l, l ≤ i + 1 + (r + 1) → (g * t) • p l = p l := by
      intro l hl
      exact hgtfix l (by omega)
    obtain ⟨k, hkG1, hktSoc, hktfix⟩ := ih (g * t) hgtSoc hgtfix'
    refine ⟨k * g, Subgroup.mul_mem _ hkG1 hgG1, ?_, ?_⟩
    · rwa [mul_assoc]
    · intro l hl
      rw [mul_assoc]
      exact hktfix l hl
  have hres : motive 0 (by omega) :=
    Nat.decreasingInduction (motive := motive) hstep hself (by omega)
  exact hres t ht hfix0

theorem isGoodPath_of_noBack {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {s : ℕ} (hs : s ≤ n + 1)
    {p : GPath Γ s} (hp : p.NoBack) : IsGoodPath H p := by
  refine ⟨hp, ?_⟩
  intro i hi0 his t ht
  obtain ⟨⟨htSoc, htw⟩, hty⟩ := ht
  have hfixw : t • p (i - 1) = p (i - 1) := MulAction.mem_stabilizer_iff.mp htw
  have hfixy : t • p (i + 1) = p (i + 1) := MulAction.mem_stabilizer_iff.mp hty
  have hfixi : t • p i = p i := socleAt_le_stabilizer (hK (p i)) htSoc
  have hi1 : 1 ≤ i := hi0
  have his1 : i + 1 ≤ s := by omega
  have hin : i ≤ n := by omega
  have hfix0 : ∀ l, i - 1 ≤ l → l ≤ i + 1 → t • p l = p l := by
    intro l hl1 hl2
    rcases (by omega : l = i - 1 ∨ l = i ∨ l = i + 1) with rfl | rfl | rfl
    · exact hfixw
    · exact hfixi
    · exact hfixy
  obtain ⟨kb, hkbG1, htbsoc, htbfix⟩ :=
    backward_iterate hn hM hne hp hi1 (by omega) hin his1 htSoc hfix0
  obtain ⟨kf, hkfG1, htfsoc, htffix⟩ :=
    forward_iterate hn hM hne hp hi1 his hin hs htbsoc htbfix
  have hhstab : kf * (kb * t) ∈ GPath.stabPath (H := H) p := by
    rw [GPath.mem_stabPath_iff]
    intro l hl
    exact htffix l hl
  have hhsoc : kf * (kb * t) ∈ socleAt H Γ (p i) := htfsoc
  have ht_eq : t = (kf * kb)⁻¹ * (kf * (kb * t)) := by group
  rw [ht_eq]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mul_mem _ hkfG1 hkbG1))
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hhstab, hhsoc⟩)

theorem pathRootGroup_torus_conj_mem {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {q : GPath Γ n}
    (hq : q.NoBack) {ω' : V} (hω' : Γ.Adj (q n) ω') (hω'ne : ω' ≠ q (n - 1)) :
    ∀ t ∈ socTorus H Γ (q n) (q (n - 1)) ω', ∀ x ∈ pathRootGroup H Γ q,
      t * x * t⁻¹ ∈ pathRootGroup H Γ q ⊔ fixingSubgroup H (Γ.neighborSet (q n)) := by
  classical
  intro t ht x hx
  set p' : GPath Γ (n + 1) := q.snoc ω' hω' with hp'_def
  have hp'nb : p'.NoBack := by
    rw [hp'_def]
    exact GPath.noBack_snoc hq hω' (fun _ => hω'ne)
  have hp'n : p' n = q n := by
    rw [hp'_def]
    exact GPath.snoc_of_le q ω' hω' (i := n) (by omega)
  have hp'nm1 : p' (n - 1) = q (n - 1) := by
    rw [hp'_def]
    exact GPath.snoc_of_le q ω' hω' (i := n - 1) (by omega)
  have hp'np1 : p' (n + 1) = ω' := by
    rw [hp'_def]
    exact GPath.snoc_last q ω' hω'
  have hgood := (isGoodPath_of_noBack hn hM hne hK (s := n + 1) (by omega) hp'nb).2 n
    (by omega) (by omega)
  rw [hp'n, hp'nm1, hp'np1] at hgood
  have htR : t ∈ (p'.stabPath ⊓ socleAt H Γ (q n)) ⊔
      fixingSubgroup H (Γ.neighborSet (q n)) := hgood ht
  have hAnorm : (p'.stabPath ⊓ socleAt H Γ (q n)) ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (q n)) : Set H) :=
    inf_le_right.trans (socleAt_le_normalizer_fixingSubgroup (q n))
  have ht' : t ∈ (↑((p'.stabPath ⊓ socleAt H Γ (q n)) ⊔
      fixingSubgroup H (Γ.neighborSet (q n))) : Set H) := htR
  rw [Subgroup.coe_mul_of_left_le_normalizer_right
    (p'.stabPath ⊓ socleAt H Γ (q n))
    (fixingSubgroup H (Γ.neighborSet (q n))) hAnorm] at ht'
  rcases ht' with ⟨a, ha, k, hk, hakt⟩
  have haq : a • q = q := by
    rw [GPath.smul_eq_iff]
    intro l hl
    have h := (GPath.mem_stabPath_iff.mp ha.1) l (by omega)
    rwa [GPath.snoc_of_le q ω' hω' hl] at h
  have hNaU : a ∈ Subgroup.normalizer (pathRootGroup H Γ q : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := pathRootGroup_smul_eq (H := H) (Γ := Γ) q a
    rw [haq] at h
    exact h.symm
  have hNaK : a ∈ Subgroup.normalizer
      (fixingSubgroup H (Γ.neighborSet (q n)) : Set H) :=
    socleAt_le_normalizer_fixingSubgroup (q n) ha.2
  have hUS : pathRootGroup H Γ q ≤ MulAction.stabilizer H (q n) :=
    pathRootGroup_le_stabilizer (by omega) q
  have hkx : k * x * k⁻¹ ∈
      pathRootGroup H Γ q ⊔ fixingSubgroup H (Γ.neighborSet (q n)) := by
    have hxS : x • q n = q n :=
      MulAction.mem_stabilizer_iff.mp (hUS hx)
    have hconjK : x * k⁻¹ * x⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (q n)) := by
      have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) x (q n)
      rw [hxS] at h
      have hmem : (MulAut.conj x) k⁻¹ ∈
          (fixingSubgroup H (Γ.neighborSet (q n))).map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom (Subgroup.inv_mem _ hk)
      rw [← h] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hku : k * x * k⁻¹ = (k * (x * k⁻¹ * x⁻¹)) * x := by group
    rw [hku]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_right hconjK))
      (Subgroup.mem_sup_left hx)
  have hU : ∀ u ∈ pathRootGroup H Γ q,
      (MulAut.conj a) u ∈ pathRootGroup H Γ q := by
    intro u hu
    have h := (Subgroup.mem_normalizer_iff.mp hNaU u).mp hu
    simpa [MulAut.conj_apply] using h
  have hK : ∀ v ∈ fixingSubgroup H (Γ.neighborSet (q n)),
      (MulAut.conj a) v ∈ fixingSubgroup H (Γ.neighborSet (q n)) := by
    intro v hv
    have h := (Subgroup.mem_normalizer_iff.mp hNaK v).mp hv
    simpa [MulAut.conj_apply] using h
  have hUK : pathRootGroup H Γ q ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (q n)) : Set H) := by
    intro u hu
    exact stabilizer_le_normalizer_fixingSubgroup (hUS hu)
  have hay : a * (k * x * k⁻¹) * a⁻¹ ∈
      pathRootGroup H Γ q ⊔ fixingSubgroup H (Γ.neighborSet (q n)) := by
    have hkx' : k * x * k⁻¹ ∈
        (↑(pathRootGroup H Γ q ⊔
          fixingSubgroup H (Γ.neighborSet (q n))) : Set H) := hkx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (pathRootGroup H Γ q)
      (fixingSubgroup H (Γ.neighborSet (q n))) hUK] at hkx'
    rcases hkx' with ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    rw [show a * (u * v) * a⁻¹ = (MulAut.conj a) (u * v) by rw [MulAut.conj_apply]]
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hU u hu))
      (Subgroup.mem_sup_right (hK v hv))
  have htxy : t * x * t⁻¹ ∈
      pathRootGroup H Γ q ⊔ fixingSubgroup H (Γ.neighborSet (q n)) := by
    rw [← hakt]
    have h1 : (a * k) * x * (a * k)⁻¹ = a * (k * x * k⁻¹) * a⁻¹ := by group
    rw [h1]
    exact hay
  exact htxy

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.Quasithin.Background.F3PathCons
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexSylowAction

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
  (sylow_isPretransitive_of_primePower_card)

universe u v

variable {V : Type u}

@[expose] def WeissFreeHat (α : RankTwoAmalgam.{u}) (n : ℕ) : Prop :=
  ∀ p : GPath α.graphHat n, p.NoBack → ∀ h : ↥(α.Ghat1 ⊔ α.Ghat2),
    (∀ i, i ≤ n → h • p i = p i) →
    (∀ w, α.graphHat.Adj (p 0) w → h • w = w) →
    (∀ w, α.graphHat.Adj (p 1) w → h • w = w) → h = 1

@[expose] def WeissMoufangHat (α : RankTwoAmalgam.{u}) (n : ℕ) : Prop :=
  MoufangHat α n ∧ WeissFreeHat α n

@[expose] def IsLocallyTrans (H : Type*) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (s : ℕ) : Prop :=
  ∀ p p' : GPath Γ s, p.NoBack → p'.NoBack → p 0 = p' 0 → ∃ g : H, g • p = p'

@[expose] def IsLocallyTransHat (α : RankTwoAmalgam.{u}) (s : ℕ) : Prop :=
  IsLocallyTrans ↥(α.Ghat1 ⊔ α.Ghat2) α.graphHat s

section Kernel

variable {H : Type*} [Group H] [MulAction H V] {Γ : SimpleGraph V} [GraphAction H Γ]

@[expose] def edgeKernel (Γ : SimpleGraph V) (x y : V) : Subgroup H :=
  fixingSubgroup H (Γ.neighborSet x) ⊓ fixingSubgroup H (Γ.neighborSet y)

theorem mem_edgeKernel {Γ : SimpleGraph V} {x y : V} {g : H} :
    g ∈ edgeKernel Γ x y ↔
      (∀ w, Γ.Adj x w → g • w = w) ∧ (∀ w, Γ.Adj y w → g • w = w) := by
  simp only [edgeKernel, Subgroup.mem_inf, mem_fixingSubgroup_iff, SimpleGraph.mem_neighborSet]

end Kernel

@[expose] def MoufangCondition (H : Type*) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (n : ℕ) : Prop :=
  ∀ p : GPath Γ n, p.NoBack → ∀ y y' : V, Γ.Adj (p n) y → Γ.Adj (p n) y' →
    y ≠ p (n - 1) → y' ≠ p (n - 1) →
    ∃ g : H, (∀ i, 1 ≤ i → i ≤ n - 1 → ∀ w, Γ.Adj (p i) w → g • w = w) ∧ g • y = y'

section PropO

variable {H : Type*} [Group H] [MulAction H V] {Γ : SimpleGraph V} [GraphAction H Γ]

theorem eq_one_of_odd {n : ℕ} (hn : 1 ≤ n)
    (hedge : ∀ (x y : V) (g : H), Γ.Adj x y →
      (∀ w, Γ.Adj x w → g • w = w) → (∀ w, Γ.Adj y w → g • w = w) →
      ∃ k, orderOf g = 2 ^ k)
    (hpath : ∀ (g : H) (q : GPath Γ (n + 1)), q.NoBack →
      (∀ i, i ≤ n + 1 → g • q i = q i) → (∃ k, orderOf g = 2 ^ k) → g = 1)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {p : GPath Γ n} (hp : p.NoBack) {g : H}
    (hfix : ∀ i, i ≤ n → g • p i = p i)
    (h0 : ∀ w, Γ.Adj (p 0) w → g • w = w)
    (h1 : ∀ w, Γ.Adj (p 1) w → g • w = w) : g = 1 := by
  have hadj : Γ.Adj (p 0) (p 1) := by
    have h := p.adj 0 (by omega)
    rwa [show 0 + 1 = 1 by omega] at h
  have h2 : ∃ k, orderOf g = 2 ^ k := hedge (p 0) (p 1) g hadj h0 h1
  obtain ⟨y, hy, hyn⟩ := hne (p 0) (p 1) hadj
  refine hpath g (GPath.cons y p hy.symm) (GPath.noBack_cons y p hy.symm hp hyn) ?_ h2
  · intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [GPath.cons_zero]
      exact h0 y hy
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [GPath.cons_succ]
      exact hfix j (by omega)

theorem weissFreeHat_of_odd (α : RankTwoAmalgam.{u}) {n : ℕ} (hn : 1 ≤ n)
    (hedge : ∀ (x y : α.Γhat) (g : ↥(α.Ghat1 ⊔ α.Ghat2)), α.graphHat.Adj x y →
      (∀ w, α.graphHat.Adj x w → g • w = w) →
      (∀ w, α.graphHat.Adj y w → g • w = w) → ∃ k, orderOf g = 2 ^ k)
    (hpath : ∀ (g : ↥(α.Ghat1 ⊔ α.Ghat2)) (q : GPath α.graphHat (n + 1)), q.NoBack →
      (∀ i, i ≤ n + 1 → g • q i = q i) → (∃ k, orderOf g = 2 ^ k) → g = 1)
    (hne : ∀ v w : α.Γhat, α.graphHat.Adj v w → ∃ u, α.graphHat.Adj v u ∧ u ≠ w) :
    WeissFreeHat α n :=
  fun p hp g hfix h0 h1 => eq_one_of_odd hn hedge hpath hne hp hfix h0 h1

end PropO

section TheoremMi

variable {H : Type*} [Group H] [MulAction H V] {Γ : SimpleGraph V} [GraphAction H Γ]

private theorem snoc_noBack {n : ℕ} {p : GPath Γ n} {u : V} (hu : Γ.Adj (p n) u)
    (hp : p.NoBack) (hne : u ≠ p (n - 1)) : (p.snoc u hu).NoBack := by
  intro i hi
  by_cases h : i + 2 ≤ n
  · rw [GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)]
    exact hp i h
  · have hi2 : i + 2 = n + 1 := by omega
    have hin : i = n - 1 := by omega
    rw [hi2, GPath.snoc_last, hin, GPath.snoc_of_le _ _ _ (by omega)]
    exact fun h => hne h.symm

private lemma exists_extend_forward (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {L : ℕ} {s : GPath Γ L} (hs : s.NoBack) (hL : 1 ≤ L) :
    ∀ n, L ≤ n → ∃ p : GPath Γ n, p.NoBack ∧ ∀ i, i ≤ L → p i = s i := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨s, hs, fun i _ => rfl⟩
  | succ n hn ih =>
    obtain ⟨p, hp, hps⟩ := ih
    have hn1 : 1 ≤ n := le_trans hL hn
    have hadj : Γ.Adj (p n) (p (n - 1)) := by
      have h := (p.adj (n - 1) (by omega)).symm
      rwa [show n - 1 + 1 = n by omega] at h
    obtain ⟨u, hu, hune⟩ := hne (p n) (p (n - 1)) hadj
    exact ⟨p.snoc u hu, snoc_noBack hu hp hune, fun i hi => by
      rw [GPath.snoc_of_le _ _ _ (by omega)]
      exact hps i hi⟩

theorem exists_smul_of_isLocallyTrans {s : ℕ} (hs : 3 ≤ s) (hLT : IsLocallyTrans H Γ s)
    (hval : ∀ v w : V, Γ.Adj v w →
      ∃ k, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ k)
    (hfin : ∀ v : V, Finite ↥(MulAction.stabilizer H v))
    (h2 : ∀ (v w w' : V) (g : H), Γ.Adj v w → Γ.Adj v w' → w ≠ w' →
      (∃ k, orderOf g = 2 ^ k) → g • v = v → g • w = w → g • w' = w' →
      ∀ u, Γ.Adj v u → g • u = u)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {t : ℕ} (ht2 : 2 ≤ t) (hts : t ≤ s - 1) {p : GPath Γ t} (hp : p.NoBack)
    {y y' : V} (hy : Γ.Adj (p t) y) (hy' : Γ.Adj (p t) y')
    (hyt : y ≠ p (t - 1)) (hy't : y' ≠ p (t - 1)) :
    ∃ g : H, (∀ i, 1 ≤ i → i ≤ t - 1 → ∀ w, Γ.Adj (p i) w → g • w = w) ∧
      (∀ i, i ≤ t → g • p i = p i) ∧ g • y = y' := by
  let K : Subgroup H :=
    { carrier := {g | ∀ i, i ≤ t → g • p i = p i}
      mul_mem' := by
        rintro g h hg hh i hi
        show (g * h) • p i = p i
        rw [mul_smul, hh i hi, hg i hi]
      one_mem' := by
        intro i _
        show (1 : H) • p i = p i
        rw [one_smul]
      inv_mem' := by
        rintro g hg i hi
        show g⁻¹ • p i = p i
        calc g⁻¹ • p i = g⁻¹ • (g • p i) := by rw [hg i hi]
          _ = p i := by rw [← mul_smul, inv_mul_cancel, one_smul] }
  have hKle : K ≤ MulAction.stabilizer H (p 0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    exact hg 0 (Nat.zero_le t)
  haveI hKfin : Finite ↥K := Finite.of_injective
    (fun k : ↥K => (⟨(k : H), hKle k.2⟩ : ↥(MulAction.stabilizer H (p 0))))
    (fun a b hab => Subtype.ext
      (congrArg (fun z : ↥(MulAction.stabilizer H (p 0)) => (z : H)) hab))
  let E := {y : V // Γ.Adj (p t) y ∧ y ≠ p (t - 1)}
  have hEfin : Finite E := by
    obtain ⟨k, hk⟩ := hval (p t) (p (t - 1)) (by
      have h := (p.adj (t - 1) (by omega)).symm
      rwa [show t - 1 + 1 = t by omega] at h)
    refine (Nat.card_ne_zero.mp ?_).2
    rw [show Nat.card E = 2 ^ k from hk]
    exact pow_ne_zero k (by norm_num)
  letI : MulAction ↥K E :=
    { smul := fun k y => ⟨(k : H) • y.1, by
        obtain ⟨hy1, hy2⟩ := y.2
        refine ⟨?_, ?_⟩
        · have hk : (k : H) • p t = p t := k.2 t le_rfl
          have hadj : Γ.Adj ((k : H) • p t) ((k : H) • y.1) :=
            (GraphAction.adj_smul (k : H) (p t) y.1).mpr hy1
          rwa [hk] at hadj
        · intro h
          have h1 : (k : H) • y.1 = (k : H) • p (t - 1) := by
            rw [h]
            exact (k.2 (t - 1) (by omega)).symm
          exact hy2 (by simpa using h1)⟩
      one_smul := fun y => Subtype.ext (one_smul ↥K y.1)
      mul_smul := fun a b y => Subtype.ext (mul_smul a b y.1) }
  have smul_coe : ∀ (k : ↥K) (z : E), ((k • z : E) : V) = (k : H) • (z : V) := by
    intro k z
    change (k : H) • (z : V) = (k : H) • (z : V)
    rfl
  have htrans : MulAction.IsPretransitive ↥K E := by
    rw [MulAction.isPretransitive_iff]
    intro y y'
    have ht1 : t + 1 ≤ s := by omega
    have hp1 : 1 ≤ t + 1 := by omega
    have hNB : (p.snoc y.1 y.2.1).NoBack := snoc_noBack y.2.1 hp y.2.2
    have hNB' : (p.snoc y'.1 y'.2.1).NoBack := snoc_noBack y'.2.1 hp y'.2.2
    obtain ⟨q, hq, hqps⟩ := exists_extend_forward hne hNB hp1 s ht1
    obtain ⟨q', hq', hqps'⟩ := exists_extend_forward hne hNB' hp1 s ht1
    have hq0 : q 0 = q' 0 := by
      rw [hqps 0 (by omega), hqps' 0 (by omega)]
      rw [GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)]
    obtain ⟨g, hg⟩ := hLT q q' hq hq' hq0
    have hgfix : ∀ i, i ≤ t → g • p i = p i := by
      intro i hi
      have h := (GPath.smul_eq_iff.mp hg) i (by omega)
      rwa [hqps i (by omega), hqps' i (by omega),
        GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)] at h
    have hgy : g • y.1 = y'.1 := by
      have h := (GPath.smul_eq_iff.mp hg) (t + 1) (by omega)
      rwa [hqps (t + 1) (by omega), hqps' (t + 1) (by omega), GPath.snoc_last,
        GPath.snoc_last] at h
    exact ⟨⟨g, hgfix⟩, Subtype.ext (by rw [smul_coe]; exact hgy)⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥K)
  have hvalE : ∃ k, Nat.card E = 2 ^ k :=
    hval (p t) (p (t - 1)) (by
      have h := (p.adj (t - 1) (by omega)).symm
      rwa [show t - 1 + 1 = t by omega] at h)
  have hPtrans : MulAction.IsPretransitive ↥P E :=
    sylow_isPretransitive_of_primePower_card hvalE P
  rw [MulAction.isPretransitive_iff] at hPtrans
  obtain ⟨k, hk⟩ := hPtrans ⟨y, hy, hyt⟩ ⟨y', hy', hy't⟩
  refine ⟨((k : ↥K) : H), ?_, ?_, ?_⟩
  · intro i hi1 hit
    have h2pow : ∃ n, orderOf (((k : ↥K) : H)) = 2 ^ n := by
      obtain ⟨n, hn⟩ := Sylow.isPGroup' P k
      have hinj : Function.Injective (fun z : ↥P => (((z : ↥K) : H))) := by
        intro a b hab
        exact Subtype.ext (Subtype.ext hab)
      have hord : orderOf (((k : ↥K) : H)) = orderOf k :=
        orderOf_injective ((Subgroup.subtype K).comp (Subgroup.subtype (P : Subgroup ↥K))) hinj k
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp
        (orderOf_dvd_iff_pow_eq_one.mpr hn)
      exact ⟨m, by rw [hord, hm]⟩
    refine h2 (p i) (p (i - 1)) (p (i + 1)) ((k : ↥K) : H) ?_ ?_ ?_ h2pow ?_ ?_ ?_
    · have h := (p.adj (i - 1) (by omega)).symm
      rwa [show i - 1 + 1 = i by omega] at h
    · exact p.adj i (by omega)
    · intro h
      exact hp (i - 1) (by omega) (by
        rw [show i - 1 + 2 = i + 1 by omega]
        exact h)
    · exact (k : ↥K).2 i (by omega)
    · exact (k : ↥K).2 (i - 1) (by omega)
    · exact (k : ↥K).2 (i + 1) (by omega)
  · intro i hi
    exact (k : ↥K).2 i hi
  · rw [← smul_coe k ⟨y, hy, hyt⟩]
    exact congrArg Subtype.val hk

theorem moufangCondition_of_isLocallyTrans {s : ℕ} (hs : 3 ≤ s) (hLT : IsLocallyTrans H Γ s)
    (hval : ∀ v w : V, Γ.Adj v w →
      ∃ k, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ k)
    (hfin : ∀ v : V, Finite ↥(MulAction.stabilizer H v))
    (h2 : ∀ (v w w' : V) (g : H), Γ.Adj v w → Γ.Adj v w' → w ≠ w' →
      (∃ k, orderOf g = 2 ^ k) → g • v = v → g • w = w → g • w' = w' →
      ∀ u, Γ.Adj v u → g • u = u)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) :
    MoufangCondition H Γ (s - 1) :=
  fun p hp y y' hy hy' hyt hy't => by
    obtain ⟨g, h1, -, h3⟩ :=
      exists_smul_of_isLocallyTrans hs hLT hval hfin h2 hne (t := s - 1) (by omega) le_rfl hp hy hy'
        hyt hy't
    exact ⟨g, h1, h3⟩

theorem moufangHat_of_isLocallyTrans (α : RankTwoAmalgam.{u}) {s : ℕ} (hs : 3 ≤ s)
    (hLT : IsLocallyTransHat α s)
    (hval : ∀ v w : α.Γhat, α.graphHat.Adj v w →
      ∃ k, Nat.card {y : α.Γhat // α.graphHat.Adj v y ∧ y ≠ w} = 2 ^ k)
    (hfin : ∀ v : α.Γhat, Finite ↥(MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v))
    (h2 : ∀ (v w w' : α.Γhat) (g : ↥(α.Ghat1 ⊔ α.Ghat2)), α.graphHat.Adj v w →
      α.graphHat.Adj v w' → w ≠ w' → (∃ k, orderOf g = 2 ^ k) → g • v = v → g • w = w →
      g • w' = w' → ∀ u, α.graphHat.Adj v u → g • u = u)
    (hne : ∀ v w : α.Γhat, α.graphHat.Adj v w → ∃ u, α.graphHat.Adj v u ∧ u ≠ w) :
    MoufangHat α (s - 1) :=
  moufangCondition_of_isLocallyTrans hs hLT hval hfin h2 hne

end TheoremMi

section LemmaK

variable {H : Type*} [Group H] [MulAction H V] {Γ : SimpleGraph V} [GraphAction H Γ]

theorem eq_one_of_mem_edgeKernel_of_commute (hΓ : Γ.Connected)
    (hfaith : ∀ h : H, (∀ v : V, h • v = v) → h = 1)
    {x y : V} (hxy : Γ.Adj x y) {u : H} (hu : u ∈ edgeKernel (H := H) Γ x y)
    {Cx Cy : Subgroup H} (hCxu : ∀ c ∈ Cx, c * u = u * c) (hCyu : ∀ c ∈ Cy, c * u = u * c)
    (hCxtrans : ∀ w₁ w₂ : V, Γ.Adj x w₁ → Γ.Adj x w₂ → ∃ c ∈ Cx, c • w₁ = w₂)
    (hCytrans : ∀ w₁ w₂ : V, Γ.Adj y w₁ → Γ.Adj y w₂ → ∃ c ∈ Cy, c • w₁ = w₂) : u = 1 := by
  have hux : u • x = x := (mem_edgeKernel.mp hu).2 x hxy.symm
  have huy : u • y = y := (mem_edgeKernel.mp hu).1 y hxy
  let K : Subgroup H := Cx ⊔ Cy
  have hCxK : Cx ≤ K := le_sup_left
  have hCyK : Cy ≤ K := le_sup_right
  have huK : ∀ k ∈ K, u * k = k * u := by
    have h1 : K ≤ Subgroup.centralizer ({u} : Set H) := by
      refine sup_le ?_ ?_
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (hCxu c hc).symm
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (hCyu c hc).symm
    intro k hk
    exact Subgroup.mem_centralizer_iff.mp (h1 hk) u (Set.mem_singleton u)
  let O : Set V := {v | ∃ k ∈ K, k • x = v} ∪ {v | ∃ k ∈ K, k • y = v}
  have hxO : x ∈ O := Or.inl ⟨1, one_mem _, one_smul _ _⟩
  have hxO' : ∀ w : V, Γ.Adj x w → w ∈ O := by
    intro w hw
    obtain ⟨c, hc, hcw⟩ := hCxtrans y w hxy hw
    exact Or.inr ⟨c, hCxK hc, hcw⟩
  have hyO' : ∀ w : V, Γ.Adj y w → w ∈ O := by
    intro w hw
    obtain ⟨c, hc, hcw⟩ := hCytrans x w hxy.symm hw
    exact Or.inl ⟨c, hCyK hc, hcw⟩
  have hOadj : ∀ a b : V, Γ.Adj a b → a ∈ O → b ∈ O := by
    rintro a b hab (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · have h2 : Γ.Adj (k • x) b ↔ Γ.Adj x (k⁻¹ • b) := by
        have h := GraphAction.adj_smul (Γ := Γ) k x (k⁻¹ • b)
        rwa [smul_inv_smul] at h
      rcases hxO' (k⁻¹ • b) (h2.mp hab) with ⟨k', hk', hk'b⟩ | ⟨k', hk', hk'b⟩
      · refine Or.inl ⟨k * k', Subgroup.mul_mem _ hk hk', ?_⟩
        rw [mul_smul, hk'b, smul_inv_smul]
      · refine Or.inr ⟨k * k', Subgroup.mul_mem _ hk hk', ?_⟩
        rw [mul_smul, hk'b, smul_inv_smul]
    · have h2 : Γ.Adj (k • y) b ↔ Γ.Adj y (k⁻¹ • b) := by
        have h := GraphAction.adj_smul (Γ := Γ) k y (k⁻¹ • b)
        rwa [smul_inv_smul] at h
      rcases hyO' (k⁻¹ • b) (h2.mp hab) with ⟨k', hk', hk'b⟩ | ⟨k', hk', hk'b⟩
      · refine Or.inl ⟨k * k', Subgroup.mul_mem _ hk hk', ?_⟩
        rw [mul_smul, hk'b, smul_inv_smul]
      · refine Or.inr ⟨k * k', Subgroup.mul_mem _ hk hk', ?_⟩
        rw [mul_smul, hk'b, smul_inv_smul]
  have hOuniv : O = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨w, -⟩ := hΓ.exists_walk_length_eq_dist x v
    have key : ∀ (a b : V) (w : Γ.Walk a b), a ∈ O → b ∈ O := by
      intro a b w
      induction w with
      | nil => exact id
      | cons h w ih => exact fun ha => ih (hOadj _ _ h ha)
    exact key x v w hxO
  refine hfaith u fun v => ?_
  have hv : v ∈ O := by rw [hOuniv]; exact Set.mem_univ v
  rcases hv with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · calc u • (k • x) = (u * k) • x := (mul_smul u k x).symm
      _ = (k * u) • x := by rw [huK k hk]
      _ = k • (u • x) := mul_smul k u x
      _ = k • x := by rw [hux]
  · calc u • (k • y) = (u * k) • y := (mul_smul u k y).symm
      _ = (k * u) • y := by rw [huK k hk]
      _ = k • (u • y) := mul_smul k u y
      _ = k • y := by rw [huy]

end LemmaK

end CFSG.Quasithin.Stroth

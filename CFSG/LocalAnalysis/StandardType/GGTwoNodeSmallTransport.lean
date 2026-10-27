module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pts0_getD_eq_getElem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem pts0_getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d ∈ l := by
  rw [pts0_getD_eq_getElem h]
  exact List.mem_iff_getElem.mpr ⟨i, h, rfl⟩

private theorem pts0_getElem_mem_take {α : Type*} {l : List α} {n i : ℕ}
    (h : i < n) (hl : i < l.length) : l[i] ∈ l.take n := by
  induction l generalizing i n with
  | nil => simp at hl
  | cons a t ih =>
      cases n with
      | zero => exfalso; omega
      | succ n =>
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.take_succ_cons, List.getElem_cons_succ, List.mem_cons]
              exact Or.inr (ih (by omega) (by simpa using hl))

private theorem pts0_getD_mem_take {α : Type*} {l : List α} {n i : ℕ} {d : α}
    (h : i < n) (hl : i < l.length) : l.getD i d ∈ l.take n := by
  rw [pts0_getD_eq_getElem hl]
  exact pts0_getElem_mem_take h hl

private noncomputable def pts0_conjMulEquiv {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) : (V ≃ₗ[ZMod p] V) ≃* (W ≃ₗ[ZMod p] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.trans_apply]
  right_inv h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]

private theorem pts0_conjMulEquiv_apply {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    pts0_conjMulEquiv e g = e.symm.trans (g.trans e) := rfl

private theorem pts0_conj_refl {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) (h : V) (α : Module.Dual (ZMod p) V)
    (hg : ∀ v, g v = v - α v • h) :
    ∀ w, pts0_conjMulEquiv e g w = w - α (e.symm w) • e h := by
  intro w
  calc pts0_conjMulEquiv e g w = (e.symm.trans (g.trans e)) w := by
        rw [pts0_conjMulEquiv_apply]
    _ = e (g (e.symm w)) := by simp [LinearEquiv.trans_apply]
    _ = e (e.symm w - α (e.symm w) • h) := by rw [hg]
    _ = w - α (e.symm w) • e h := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem pts0_conj_sub_id {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    ((e.symm.trans (g.trans e) : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) - LinearMap.id =
      e.toLinearMap.comp (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp e.symm.toLinearMap) := by
  ext w
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, map_sub,
    LinearEquiv.apply_symm_apply]

private theorem pts0_move_conj {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    CFSG.StandardType.ggLinMove (pts0_conjMulEquiv e g) =
      Submodule.map e.toLinearMap (CFSG.StandardType.ggLinMove g) := by
  rw [pts0_conjMulEquiv_apply]
  unfold CFSG.StandardType.ggLinMove
  rw [pts0_conj_sub_id e g]
  set L : V →ₗ[ZMod p] V := (g : V →ₗ[ZMod p] V) - LinearMap.id with hL
  ext w
  simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.comp_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨L (e.symm u), ⟨e.symm u, rfl⟩, hu⟩
  · rintro ⟨v, ⟨u, hu⟩, hv⟩
    refine ⟨e u, ?_⟩
    rw [show e.symm.toLinearMap (e u) = u by simp, hu, hv]

private theorem pts0_isTransv_conj {p : ℕ} [Fact p.Prime] {V W : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    IsTransv (pts0_conjMulEquiv e g) ↔ IsTransv g := by
  unfold IsTransv
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [pts0_move_conj e g, LinearEquiv.finrank_map_eq] at h1
      exact h1
    · intro v
      have hv := h2 (e v)
      have hφ : ∀ u, (pts0_conjMulEquiv e g) (e u) = e (g u) := by
        intro u
        rw [pts0_conjMulEquiv_apply]
        simp [LinearEquiv.trans_apply]
      rw [hφ v] at hv
      rw [← map_sub] at hv
      rw [hφ] at hv
      exact e.injective hv
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [pts0_move_conj e g, LinearEquiv.finrank_map_eq]
      exact h1
    · intro w
      obtain ⟨v, rfl⟩ : ∃ v, w = e v := ⟨e.symm w, by simp⟩
      have hφ : ∀ u, (pts0_conjMulEquiv e g) (e u) = e (g u) := by
        intro u
        rw [pts0_conjMulEquiv_apply]
        simp [LinearEquiv.trans_apply]
      rw [hφ v, ← map_sub, hφ, h2 v]

private theorem pts0_isRefl_conj {p : ℕ} [Fact p.Prime] {V W : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    CFSG.StandardType.ZS.IsRefl p (pts0_conjMulEquiv e g) ↔
      CFSG.StandardType.ZS.IsRefl p g := by
  unfold CFSG.StandardType.ZS.IsRefl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' : pts0_conjMulEquiv e (g * g) = pts0_conjMulEquiv e 1 := by
        rw [map_mul, map_one, h1]
      exact (pts0_conjMulEquiv e).injective h1'
    · change Module.finrank (ZMod p) (CFSG.StandardType.ggLinMove (pts0_conjMulEquiv e g)) = 1 at h2
      rw [pts0_move_conj e g, LinearEquiv.finrank_map_eq] at h2
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · change Module.finrank (ZMod p) (CFSG.StandardType.ggLinMove (pts0_conjMulEquiv e g)) = 1
      rw [pts0_move_conj e g, LinearEquiv.finrank_map_eq]
      exact h2

theorem Pt.facts_transport (P : Pt) [Fact P.p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod P.p) V] {n : ℕ} (h : Fin n → V) (α : Fin n → Module.Dual (ZMod P.p) V) (x : V)
    (r : Fin n → (V ≃ₗ[ZMod P.p] V)) (ha : V) (αa : Module.Dual (ZMod P.p) V)
    (t : V ≃ₗ[ZMod P.p] V) (hr : ∀ i v, r i v = v - α i v • h i) (ht : ∀ v, t v = v - αa v • ha)
    (e : V ≃ₗ[ZMod P.p] P.V) (hM : P.Models e h α x ha αa)
    (hcl : (∃ g ∈ P.group, IsTransv g) ∨ P.bound < Nat.card P.group ∨ P.FrameViolation ∨
      CFSG.StandardType.ZS.LinWeyl P.p P.group) :
    (∃ g ∈ CFSG.StandardType.lr6Group r t, IsTransv g) ∨
      P.bound < Nat.card ↥(CFSG.StandardType.lr6Group r t) ∨
      (∃ v : V, (∀ i, α i v = 0) ∧ v ∉ Submodule.span (ZMod P.p) {x}) ∨
      CFSG.StandardType.ZS.LinWeyl P.p (CFSG.StandardType.lr6Group r t) := by
  obtain ⟨hn, hlen, hex, hgen, hha, hαa⟩ := hM
  have hgen_h : ∀ i : Fin n, e (h i) = P.vec (P.gens.getD (i : ℕ) ⟨[], []⟩).h :=
    fun i => (hgen i).1
  have hgen_α : ∀ (i : Fin n) (w : V),
      α i w = P.dot (P.vec (P.gens.getD (i : ℕ) ⟨[], []⟩).f) (e w) :=
    fun i => (hgen i).2
  have hgetD_lt : ∀ i : Fin n, (i : ℕ) < P.gens.length := by
    intro i
    rw [hlen]
    exact Nat.lt_succ_of_lt i.isLt
  have hgen_mem : ∀ i : Fin n, pts0_conjMulEquiv e (r i) ∈ P.genSet := by
    intro i
    refine ⟨P.gens.getD (i : ℕ) ⟨[], []⟩, pts0_getD_mem (hgetD_lt i), ?_⟩
    intro w
    rw [pts0_conj_refl e (r i) (h i) (α i) (hr i)]
    rw [hgen_α i (e.symm w), hgen_h i, LinearEquiv.apply_symm_apply]
  have ht_mem : pts0_conjMulEquiv e t ∈ P.genSet := by
    refine ⟨P.gens.getD n ⟨[], []⟩, ?_, ?_⟩
    · apply pts0_getD_mem
      rw [hlen]
      exact Nat.lt_succ_self n
    · intro w
      rw [pts0_conj_refl e t ha αa ht]
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply]
  have hsub1 : pts0_conjMulEquiv e '' (Set.range r ∪ {t}) ⊆ P.genSet := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨i, rfl⟩ | rfl
    · exact hgen_mem i
    · exact ht_mem
  have hsub2 : P.genSet ⊆ pts0_conjMulEquiv e '' (Set.range r ∪ {t}) := by
    intro z hz
    obtain ⟨r', hr'mem, hr'formula⟩ := hz
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hr'mem
    have hjle : j < n + 1 := by rw [← hlen]; exact hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjle) with hjlt | hjeqjn
    · refine ⟨r ⟨j, hjlt⟩, Or.inl ⟨⟨j, hjlt⟩, rfl⟩, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pts0_conj_refl e (r ⟨j, hjlt⟩) (h ⟨j, hjlt⟩) (α ⟨j, hjlt⟩) (hr ⟨j, hjlt⟩)]
      have hgetD : P.gens.getD j ⟨[], []⟩ = r' := by
        rw [pts0_getD_eq_getElem hj, hjeq]
      rw [hgen_α ⟨j, hjlt⟩ (e.symm w), hgen_h ⟨j, hjlt⟩,
        LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
    · refine ⟨t, Or.inr rfl, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pts0_conj_refl e t ha αa ht]
      have hopt : P.gens[n]? = some r' := by
        rw [← hjeqjn, List.getElem?_eq_getElem hj, hjeq]
      have hgetD : P.gens.getD n ⟨[], []⟩ = r' := by
        rw [List.getD_eq_getElem?_getD, hopt]
        rfl
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
  have hset : pts0_conjMulEquiv e '' (Set.range r ∪ {t}) = P.genSet :=
    Set.Subset.antisymm hsub1 hsub2
  have hmap_eq : Subgroup.map (pts0_conjMulEquiv e)
      (CFSG.StandardType.lr6Group r t) = P.group := by
    rw [CFSG.StandardType.lr6Group, Pt.group, MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset
  have hcard : Nat.card ↥(CFSG.StandardType.lr6Group r t) = Nat.card ↥P.group := by
    rw [← hmap_eq]
    exact Nat.card_congr (MulEquiv.subgroupMap (pts0_conjMulEquiv e)
      (CFSG.StandardType.lr6Group r t)).toEquiv
  rcases hcl with h1 | h2 | h3 | h4
  · obtain ⟨g', hg'mem, hg'tv⟩ := h1
    have hg'mem' : g' ∈ Subgroup.map (pts0_conjMulEquiv e)
        (CFSG.StandardType.lr6Group r t) := by
      rw [hmap_eq]
      exact hg'mem
    obtain ⟨g, hgH, hgφ⟩ := Subgroup.mem_map.mp hg'mem'
    exact Or.inl ⟨g, hgH, (pts0_isTransv_conj e g).mp (hgφ.symm ▸ hg'tv)⟩
  · right; left
    rw [hcard]
    exact h2
  · right; right; left
    obtain ⟨w, hw0, hwspan⟩ := h3
    refine ⟨e.symm w, ?_, ?_⟩
    · intro i
      rw [hgen_α i (e.symm w), LinearEquiv.apply_symm_apply]
      exact hw0 (P.gens.getD (i : ℕ) ⟨[], []⟩)
        (pts0_getD_mem_take (by rw [hn]; exact i.isLt) (hgetD_lt i))
    · intro hv
      apply hwspan
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← hex, ← map_smul, hc, LinearEquiv.apply_symm_apply]
  · right; right; right
    obtain ⟨ι, M, hMweyl, f, hf⟩ := h4
    refine ⟨ι, M, hMweyl, ?_⟩
    let Ψ : ↥P.group ≃* ↥(CFSG.StandardType.lr6Group r t) :=
    { toFun := fun z =>
        ⟨(pts0_conjMulEquiv e).symm (z : P.V ≃ₗ[ZMod P.p] P.V), by
          have hz : (z : P.V ≃ₗ[ZMod P.p] P.V) ∈
              Subgroup.map (pts0_conjMulEquiv e)
                (CFSG.StandardType.lr6Group r t) := by
            rw [hmap_eq]
            exact z.2
          obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
          have hzy : (pts0_conjMulEquiv e).symm (z : P.V ≃ₗ[ZMod P.p] P.V) = y := by
            rw [← hyz]
            exact (pts0_conjMulEquiv e).symm_apply_apply y
          rw [hzy]
          exact hy⟩
      invFun := fun y =>
        ⟨(pts0_conjMulEquiv e) (y : V ≃ₗ[ZMod P.p] V), by
          rw [← hmap_eq]
          exact ⟨(y : V ≃ₗ[ZMod P.p] V), y.2, rfl⟩⟩
      left_inv := by
        intro z
        apply Subtype.ext
        show (pts0_conjMulEquiv e) ((pts0_conjMulEquiv e).symm
            (z : P.V ≃ₗ[ZMod P.p] P.V)) = (z : P.V ≃ₗ[ZMod P.p] P.V)
        exact (pts0_conjMulEquiv e).apply_symm_apply _
      right_inv := by
        intro y
        apply Subtype.ext
        show (pts0_conjMulEquiv e).symm ((pts0_conjMulEquiv e)
            (y : V ≃ₗ[ZMod P.p] V)) = (y : V ≃ₗ[ZMod P.p] V)
        exact (pts0_conjMulEquiv e).symm_apply_apply _
      map_mul' := by
        intro z z'
        apply Subtype.ext
        exact map_mul (pts0_conjMulEquiv e).symm
          (z : P.V ≃ₗ[ZMod P.p] P.V) (z' : P.V ≃ₗ[ZMod P.p] P.V) }
    refine ⟨f.trans Ψ, ?_⟩
    intro i
    change CFSG.StandardType.ZS.IsRefl P.p
      ((pts0_conjMulEquiv e).symm ((f (M.simple i) : P.V ≃ₗ[ZMod P.p] P.V)))
    exact (pts0_isRefl_conj e.symm ((f (M.simple i) : P.V ≃ₗ[ZMod P.p] P.V))).mpr (hf i)

end CFSG.TwoNodeSmall

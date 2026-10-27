module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModelExcl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosCycle
public import Certificates.Certificate708602

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pge_getD_eq_getElem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem pge_getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d ∈ l := by
  rw [pge_getD_eq_getElem h]
  exact List.mem_iff_getElem.mpr ⟨i, h, rfl⟩

private noncomputable def pge_conjMulEquiv {p : ℕ} [Fact p.Prime] {V W : Type*}
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

private theorem pge_conjMulEquiv_apply {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    pge_conjMulEquiv e g = e.symm.trans (g.trans e) := rfl

private theorem pge_conj_refl {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) (h : V) (α : Module.Dual (ZMod p) V)
    (hg : ∀ v, g v = v - α v • h) :
    ∀ w, pge_conjMulEquiv e g w = w - α (e.symm w) • e h := by
  intro w
  calc pge_conjMulEquiv e g w = (e.symm.trans (g.trans e)) w := by
        rw [pge_conjMulEquiv_apply]
    _ = e (g (e.symm w)) := by simp [LinearEquiv.trans_apply]
    _ = e (e.symm w - α (e.symm w) • h) := by rw [hg]
    _ = w - α (e.symm w) • e h := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem pge_conj_sub_id {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    ((e.symm.trans (g.trans e) : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) - LinearMap.id =
      e.toLinearMap.comp (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp e.symm.toLinearMap) := by
  ext w
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, map_sub,
    LinearEquiv.apply_symm_apply]

private theorem pge_move_conj {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    CFSG.StandardType.ggLinMove (pge_conjMulEquiv e g) =
      Submodule.map e.toLinearMap (CFSG.StandardType.ggLinMove g) := by
  rw [pge_conjMulEquiv_apply]
  unfold CFSG.StandardType.ggLinMove
  rw [pge_conj_sub_id e g]
  set L : V →ₗ[ZMod p] V := (g : V →ₗ[ZMod p] V) - LinearMap.id with hL
  ext w
  simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.comp_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨L (e.symm u), ⟨e.symm u, rfl⟩, hu⟩
  · rintro ⟨v, ⟨u, hu⟩, hv⟩
    refine ⟨e u, ?_⟩
    rw [show e.symm.toLinearMap (e u) = u by simp, hu, hv]

private theorem pge_isTransv_conj {p : ℕ} [Fact p.Prime] {V W : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    IsTransv (pge_conjMulEquiv e g) ↔ IsTransv g := by
  unfold IsTransv
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [pge_move_conj e g, LinearEquiv.finrank_map_eq] at h1
      exact h1
    · intro v
      have hv := h2 (e v)
      have hφ : ∀ u, (pge_conjMulEquiv e g) (e u) = e (g u) := by
        intro u
        rw [pge_conjMulEquiv_apply]
        simp [LinearEquiv.trans_apply]
      rw [hφ v] at hv
      rw [← map_sub] at hv
      rw [hφ] at hv
      exact e.injective hv
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [pge_move_conj e g, LinearEquiv.finrank_map_eq]
      exact h1
    · intro w
      obtain ⟨v, rfl⟩ : ∃ v, w = e v := ⟨e.symm w, by simp⟩
      have hφ : ∀ u, (pge_conjMulEquiv e g) (e u) = e (g u) := by
        intro u
        rw [pge_conjMulEquiv_apply]
        simp [LinearEquiv.trans_apply]
      rw [hφ v, ← map_sub, hφ, h2 v]

private theorem pge_transv_of_models {P : Pt} [Fact P.p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod P.p) V] {n : ℕ} {e : V ≃ₗ[ZMod P.p] P.V} {h : Fin n → V}
    {α : Fin n → Module.Dual (ZMod P.p) V} {x ha : V} {αa : Module.Dual (ZMod P.p) V}
    (hM : P.Models e h α x ha αa) (r : Fin n → (V ≃ₗ[ZMod P.p] V)) (t : V ≃ₗ[ZMod P.p] V)
    (hr : ∀ i v, r i v = v - α i v • h i) (ht : ∀ v, t v = v - αa v • ha)
    (htv : ∃ g ∈ P.group, IsTransv g) :
    ∃ g ∈ CFSG.StandardType.lr6ExclGroup r t, IsTransv g := by
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
  have hgen_mem : ∀ i : Fin n, pge_conjMulEquiv e (r i) ∈ P.genSet := by
    intro i
    refine ⟨P.gens.getD (i : ℕ) ⟨[], []⟩, pge_getD_mem (hgetD_lt i), ?_⟩
    intro w
    rw [pge_conj_refl e (r i) (h i) (α i) (hr i)]
    rw [hgen_α i (e.symm w), hgen_h i, LinearEquiv.apply_symm_apply]
  have ht_mem : pge_conjMulEquiv e t ∈ P.genSet := by
    refine ⟨P.gens.getD n ⟨[], []⟩, ?_, ?_⟩
    · apply pge_getD_mem
      rw [hlen]
      exact Nat.lt_succ_self n
    · intro w
      rw [pge_conj_refl e t ha αa ht]
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply]
  have hsub1 : pge_conjMulEquiv e '' (Set.range r ∪ {t}) ⊆ P.genSet := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨i, rfl⟩ | rfl
    · exact hgen_mem i
    · exact ht_mem
  have hsub2 : P.genSet ⊆ pge_conjMulEquiv e '' (Set.range r ∪ {t}) := by
    intro z hz
    obtain ⟨r', hr'mem, hr'formula⟩ := hz
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hr'mem
    have hjle : j < n + 1 := by rw [← hlen]; exact hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjle) with hjlt | hjeqjn
    · refine ⟨r ⟨j, hjlt⟩, Or.inl ⟨⟨j, hjlt⟩, rfl⟩, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pge_conj_refl e (r ⟨j, hjlt⟩) (h ⟨j, hjlt⟩) (α ⟨j, hjlt⟩) (hr ⟨j, hjlt⟩)]
      have hgetD : P.gens.getD j ⟨[], []⟩ = r' := by
        rw [pge_getD_eq_getElem hj, hjeq]
      rw [hgen_α ⟨j, hjlt⟩ (e.symm w), hgen_h ⟨j, hjlt⟩,
        LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
    · refine ⟨t, Or.inr rfl, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pge_conj_refl e t ha αa ht]
      have hopt : P.gens[n]? = some r' := by
        rw [← hjeqjn, List.getElem?_eq_getElem hj, hjeq]
      have hgetD : P.gens.getD n ⟨[], []⟩ = r' := by
        rw [List.getD_eq_getElem?_getD, hopt]
        rfl
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
  have hset : pge_conjMulEquiv e '' (Set.range r ∪ {t}) = P.genSet :=
    Set.Subset.antisymm hsub1 hsub2
  have hmap_eq : Subgroup.map (pge_conjMulEquiv e)
      (CFSG.StandardType.lr6Group r t) = P.group := by
    rw [CFSG.StandardType.lr6Group, Pt.group, MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset
  obtain ⟨g', hg'mem, hg'tv⟩ := htv
  have hg'mem' : g' ∈ Subgroup.map (pge_conjMulEquiv e)
      (CFSG.StandardType.lr6Group r t) := by
    rw [hmap_eq]
    exact hg'mem
  obtain ⟨g, hgH, hgφ⟩ := Subgroup.mem_map.mp hg'mem'
  refine ⟨g, ?_, (pge_isTransv_conj e g).mp (hgφ.symm ▸ hg'tv)⟩
  change g ∈ CFSG.StandardType.lr6Group r t
  exact hgH

theorem lr6SmallRankExcl_of_closed
    (hcl : ∀ Q ∈ exclPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl) : CFSG.StandardType.LR6SmallRankExcl := by
  intro p N hp hcell V _ _ hV h α x r ha αa t hF hr ht hha hx hsp hK hnt
  obtain ⟨S, MK, CK, ⟨s, hs, hS⟩, hW, hC, hpair, hc, htri, -⟩ := hK
  have hcellA : CFSG.StandardType.lr6SmallCellA p N := by
    rcases hcell with ⟨hp5, hN5⟩ | ⟨hp7, hN7⟩
    · exact Or.inl ⟨hp5, hN5⟩
    · exact Or.inr (Or.inr ⟨hp7, hN7⟩)
  have hchain : ∀ i j : ↥S, ((CK (some i) (some j) : ℤ) : ZMod p) =
      ((CartanMatrix.A (N - 1) (i : Fin (N - 1)) (j : Fin (N - 1)) : ℤ) : ZMod p) := by
    intro i j
    rw [hpair (some i) (some j)]
    exact hF.pair i j
  have hself : ((CK none none : ℤ) : ZMod p) = 2 := by
    rw [hpair none none]
    exact hha
  obtain ⟨o, ho, hoCK⟩ := cellA_kopts p N hcellA s hs S hS MK CK hW hC hchain hself hc
  have hH : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).1
    rw [hpair (some ⟨j, hj⟩) none] at h3
    exact h3
  have hA : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).2
    rw [hpair none (some ⟨j, hj⟩)] at h3
    exact h3
  obtain ⟨D, nF, gens, x', b, hmemL, c, hc0, e, hM⟩ :=
    excl_model p N hcell hV h α x ha αa hF hha hx hsp s hs o ho hH hA
  let Q : SPt := ⟨⟨p, D, nF, gens, x', b⟩, s⟩
  have hQ : Q ∈ exclPts () := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Q ∈ exclCell false 5 5 ++ exclCell false 7 7 ++ exclCell true 5 5 ++ exclCell true 7 7
      rw [List.mem_append, List.mem_append, List.mem_append]
      rw [List.mem_append] at hmemL
      rcases hmemL with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
    · show Q ∈ exclCell false 5 5 ++ exclCell false 7 7 ++ exclCell true 5 5 ++ exclCell true 7 7
      rw [List.mem_append, List.mem_append, List.mem_append]
      rw [List.mem_append] at hmemL
      rcases hmemL with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
  haveI : Fact Q.pt.p.Prime := hp
  rcases hcl Q hQ with hfix | hnwf | htrv | hcyc
  · exfalso
    have hz : c • αa x = 0 := by simpa using alphaFixed_models hM hfix
    exact hx ((smul_eq_zero.mp hz).resolve_left hc0)
  · exfalso
    have hd : ∀ i : Fin (N - 1), α i (h i) = 2 := fun i => by
      simpa [CartanMatrix.A, Matrix.of_apply] using hF.pair i i
    exact hnwf (wf_of_models hM hd hha)
  · exfalso
    obtain ⟨g, hg, htg⟩ := pge_transv_of_models hM r t hr ht htrv
    exact hnt g hg htg
  · exfalso
    have hS' : ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + ((N - 1) - 2) := by
      intro i
      rw [hS i]
      constructor <;> (rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩)
    exact (cycleAt_models hM r t hr ht s hs S hS' hcyc) htri

end CFSG.TwoNodeSmall

namespace CFSG.StandardType

theorem lr6SmallRankExcl_of_certificate : LR6SmallRankExcl :=
  CFSG.TwoNodeSmall.lr6SmallRankExcl_of_closed Certificates.certificate708602

end CFSG.StandardType

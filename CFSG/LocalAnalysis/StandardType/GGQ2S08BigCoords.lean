module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumIrr
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumCoxeter
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumConn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08bf1_linRefl_conj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V')
    {T : V ≃ₗ[ZMod 3] V} (h : GGLinRefl T) : GGLinRefl (ggLinConj κ T) := by
  rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)] at h ⊢
  obtain ⟨c, f, hcf, hT⟩ := h
  refine ⟨κ c, f.comp κ.symm.toLinearMap, ?_, fun v => ?_⟩
  · change f (κ.symm (κ c)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hcf
  · rw [ggLinConj_apply, hT (κ.symm v)]
    change κ (κ.symm v - f (κ.symm v) • c) = v - f (κ.symm v) • κ c
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2s08bf1_mem_span_map {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V') (y : V) (v : V') :
    v ∈ Submodule.span (ZMod 3) {κ y} ↔ κ.symm v ∈ Submodule.span (ZMod 3) {y} := by
  have hmap : (Submodule.span (ZMod 3) {y}).map κ.toLinearMap =
      Submodule.span (ZMod 3) {κ y} := by
    rw [Submodule.map_span]
    simp
  rw [← hmap, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzv⟩
    have hzv' : κ.symm v = z := by
      rw [← hzv]
      exact LinearEquiv.symm_apply_apply κ z
    simpa [hzv'] using hz
  · intro hv
    exact ⟨κ.symm v, hv, by simp⟩

private theorem ggQ2s08bf1_coords_of {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {ℓ : ℕ} (M : GGQ2LDatum 3 Bs L x) (hF : M.ShapeFull)
    (hconn : ∀ i j : M.Λ, Relation.ReflTransGen
      (fun a b => a ≠ b ∧ M.coxeter a b ≠ 2) i j)
    (h6 : ∀ i j : M.Λ, i ≠ j → M.coxeter i j ≠ 6)
    (X : CoxeterMatrix (Fin ℓ)) (e : Fin ℓ ≃ M.Λ) (he : M.coxeter = X.reindex e)
    (hX : X = CoxeterMatrix.A ℓ ∨ X = CoxeterMatrix.B ℓ ∨ X = ggCoxeterMatrixD ℓ) :
    ∃ (κ : M.V ≃ₗ[ZMod 3] Vn (ℓ + 1))
      (s : Fin ℓ → (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)))
      (H : Submodule (ZMod 3) (Vn (ℓ + 1))),
      (∀ i j, X i j = M.coxeter (e i) (e j)) ∧
      (∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v) ∧
      GGQ2S08BigLin s X (κ M.xV) H := by
  classical
  obtain ⟨hxV, hcompl, hfinrank, hWpres, hfix⟩ := ggQ2s08d_full_split M hF
  have hind : LinearIndependent (ZMod 3) M.coroot := hF.2.1
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hcard : Fintype.card M.Λ = ℓ := by
    simpa using (Fintype.card_congr e).symm
  have hfr : Module.finrank (ZMod 3) M.V = ℓ + 1 := by
    rw [hfinrank, hcard]
  let bV : Module.Basis (Fin (ℓ + 1)) (ZMod 3) M.V :=
    Module.finBasisOfFinrankEq (ZMod 3) M.V hfr
  let κ : M.V ≃ₗ[ZMod 3] Vn (ℓ + 1) := bV.equivFun
  let T : Fin ℓ → M.V ≃ₗ[ZMod 3] M.V := fun i => ggLin (p := 3) M.model (M.simple (e i))
  let s : Fin ℓ → Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1) := fun i => ggLinConj κ (T i)
  let H : Submodule (ZMod 3) (Vn (ℓ + 1)) := M.coSpan.map κ.toLinearMap
  have hs : ∀ i, s i = ggLinConj κ (T i) := fun _ => rfl
  have hsmul : ∀ i j, s i * s j = ggLinConj κ (T i * T j) := fun i j => by
    show ggLinConj κ (T i) * ggLinConj κ (T j) = ggLinConj κ (T i * T j)
    rw [← map_mul]
  have hXe : ∀ i j, X i j = M.coxeter (e i) (e j) := fun i j => by
    rw [he, CoxeterMatrix.reindex_apply]
    simp
  have hclos : Subgroup.closure (Set.range s) =
      ((ggAutomizer L Bs).map (ggLin (p := 3) M.model)).map
        (ggLinConj κ).toMonoidHom := by
    have h1 : (ggAutomizer L Bs).map (ggQ2CellLin M κ) =
        ((ggAutomizer L Bs).map (ggLin (p := 3) M.model)).map
          (ggLinConj κ).toMonoidHom := by
      rw [show ggQ2CellLin M κ =
        (ggLinConj κ).toMonoidHom.comp (ggLin (p := 3) M.model) from rfl]
      exact (Subgroup.map_map (K := ggAutomizer L Bs) (g := (ggLinConj κ).toMonoidHom)
        (f := ggLin (p := 3) M.model)).symm
    rw [← h1]
    exact (ggQ2Cell_map_automizer_L M κ e s (fun _ _ => rfl)).symm
  have hx : κ M.xV ≠ 0 := by
    intro h0
    exact hxV (κ.injective (by simpa using h0))
  have hH : IsCompl H (Submodule.span (ZMod 3) {κ M.xV}) := by
    have hmap := Submodule.isCompl_map κ hcompl
    simpa [H, Submodule.map_span] using hmap
  refine ⟨κ, s, H, hXe, ?_, ?_⟩
  · intro i v
    rfl
  · refine ⟨hx, hH, hX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro i
      exact ggQ2s08bf1_linRefl_conj κ (ggQ2s08d_simple_refl M (e i)).2.1
    ·
      intro i
      obtain ⟨hne, -, hmove⟩ := ggQ2s08d_simple_refl M (e i)
      refine ⟨κ (M.coroot (e i)), ?_, ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨M.coroot (e i),
          Submodule.subset_span (Set.mem_range_self (e i)), rfl⟩
      · intro h0
        exact hne (κ.injective (by simpa using h0))
      · intro v
        have hmem : T i (κ.symm v) - κ.symm v ∈
            Submodule.span (ZMod 3) {M.coroot (e i)} := hmove (κ.symm v)
        have hspan : (Submodule.span (ZMod 3) {M.coroot (e i)}).map κ.toLinearMap =
            Submodule.span (ZMod 3) {κ (M.coroot (e i))} := by
          rw [Submodule.map_span]
          simp
        have hval : s i v - v = κ (T i (κ.symm v) - κ.symm v) := by
          rw [hs i, ggLinConj_apply, map_sub, LinearEquiv.apply_symm_apply]
        rw [hval, ← hspan]
        exact Submodule.mem_map_of_mem hmem
    ·
      intro i j hij
      have hij' : e i ≠ e j := fun h => hij (e.injective h)
      have hf := (ggQ2s08d_coxeter_facts M hind h6 (e i) (e j) hij').1
      rw [hXe i j, hsmul i j, ← map_pow, hf, map_one]
    ·
      intro i j hij h
      have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
      have hf := (ggQ2s08d_coxeter_facts M hind h6 (e i) (e j) hij').2.1
      exact hf ((ggLinConj κ).injective (by simpa [hs i, hs j] using h))
    ·
      intro i j hij h2 h
      have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
      have hf := (ggQ2s08d_coxeter_facts M hind h6 (e i) (e j) hij').2.2.2
      have hm : M.coxeter (e i) (e j) ≠ 2 := by
        rw [← hXe i j]
        exact h2
      exact hf hm ((ggLinConj κ).injective (by simpa [hsmul i j, hsmul j i] using h))
    ·
      intro v
      rw [hclos]
      constructor
      · intro hv
        apply (ggQ2s08bf1_mem_span_map κ M.xV v).mpr
        exact (hfix (κ.symm v)).mp (fun u hu => by
          have hu' : ggLinConj κ u ∈ ((ggAutomizer L Bs).map
              (ggLin (p := 3) M.model)).map (ggLinConj κ).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
          have h1 := hv _ hu'
          rw [ggLinConj_apply] at h1
          exact κ.injective (by rw [h1, LinearEquiv.apply_symm_apply]))
      · intro hv w hw
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
        change (ggLinConj κ u) v = v
        rw [ggLinConj_apply]
        have hufix : u (κ.symm v) = κ.symm v :=
          (hfix (κ.symm v)).mpr ((ggQ2s08bf1_mem_span_map κ M.xV v).mp hv) u hu
        rw [hufix, LinearEquiv.apply_symm_apply]
    ·
      intro w hw h hh
      rw [hclos] at hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hh
      change (ggLinConj κ u) (κ y) ∈ H
      rw [ggLinConj_apply, LinearEquiv.symm_apply_apply]
      exact Submodule.mem_map.mpr ⟨u y, hWpres u hu y hy, rfl⟩
    ·
      intro U hU hUinv
      let U₀ : Submodule (ZMod 3) M.V := U.comap κ.toLinearMap
      have hU₀le : U₀ ≤ M.coSpan := by
        intro y hy
        have hyU : κ y ∈ U := Submodule.mem_comap.mp hy
        obtain ⟨y', hy', hy'y⟩ := Submodule.mem_map.mp (hU hyU)
        exact (κ.injective hy'y) ▸ hy'
      have hU₀inv : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model),
          ∀ u ∈ U₀, w u ∈ U₀ := by
        intro w hw u hu
        have hw' : ggLinConj κ w ∈ Subgroup.closure (Set.range s) := by
          rw [hclos]
          exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
        change κ (w u) ∈ U
        have hkey : κ (w u) = ggLinConj κ w (κ u) := by
          rw [ggLinConj_apply, LinearEquiv.symm_apply_apply]
        rw [hkey]
        exact hUinv _ hw' _ (Submodule.mem_comap.mp hu)
      rcases ggQ2s08d_irr M hF hconn h6 U₀ hU₀le hU₀inv with hbot | htop
      · left
        rw [eq_bot_iff]
        intro u hu
        have hmem : κ.symm u ∈ U₀ := Submodule.mem_comap.mpr (by simpa using hu)
        rw [hbot] at hmem
        have hsymm : κ.symm u = 0 := by simpa using hmem
        rw [Submodule.mem_bot]
        simpa using congrArg κ hsymm
      · right
        apply le_antisymm hU
        intro h hh
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hh
        have hyU₀ : y ∈ U₀ := by
          rw [htop]
          exact hy
        exact Submodule.mem_comap.mp hyU₀

theorem ggQ2s08_big_coords [Finite G] (M : GGQ2LDatum 3 Bs L x) (hF : M.ShapeFull)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter) :
    ∃ (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) (e : Fin lab.rank ≃ M.Λ)
      (s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)))
      (Mx : CoxeterMatrix (Fin lab.rank)) (H : Submodule (ZMod 3) (Vn (lab.rank + 1))),
      (∀ i j, Mx i j = M.coxeter (e i) (e j)) ∧
      (∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v) ∧
      GGQ2S08BigLin s Mx (κ M.xV) H := by
  obtain ⟨hconn, h6⟩ := ggQ2s08d_label_connected hlab M.coxeter hMW
  obtain ⟨-, htag, -⟩ := hlab
  rcases htag with hA | hB | hC | hD | hD
  · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, hA] using hMW
    obtain ⟨κ, s, H, h1, h2, h3⟩ :=
      ggQ2s08bf1_coords_of M hF hconn h6 (CoxeterMatrix.A lab.rank) e he (Or.inl rfl)
    exact ⟨κ, e, s, CoxeterMatrix.A lab.rank, H, h1, h2, h3⟩
  · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, hB] using hMW
    obtain ⟨κ, s, H, h1, h2, h3⟩ :=
      ggQ2s08bf1_coords_of M hF hconn h6 (CoxeterMatrix.B lab.rank) e he (Or.inr (Or.inl rfl))
    exact ⟨κ, e, s, CoxeterMatrix.B lab.rank, H, h1, h2, h3⟩
  · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, hC] using hMW
    obtain ⟨κ, s, H, h1, h2, h3⟩ :=
      ggQ2s08bf1_coords_of M hF hconn h6 (CoxeterMatrix.B lab.rank) e he (Or.inr (Or.inl rfl))
    exact ⟨κ, e, s, CoxeterMatrix.B lab.rank, H, h1, h2, h3⟩
  · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, hD] using hMW
    obtain ⟨κ, s, H, h1, h2, h3⟩ :=
      ggQ2s08bf1_coords_of M hF hconn h6 (ggCoxeterMatrixD lab.rank) e he
        (Or.inr (Or.inr rfl))
    exact ⟨κ, e, s, ggCoxeterMatrixD lab.rank, H, h1, h2, h3⟩
  · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, hD] using hMW
    obtain ⟨κ, s, H, h1, h2, h3⟩ :=
      ggQ2s08bf1_coords_of M hF hconn h6 (ggCoxeterMatrixD lab.rank) e he
        (Or.inr (Or.inr rfl))
    exact ⟨κ, e, s, ggCoxeterMatrixD lab.rank, H, h1, h2, h3⟩

end CFSG.StandardType

end

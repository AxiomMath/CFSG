module

public import CFSG.Quasithin.Vol2.Ch12Sec5Nat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125Tr3 S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "SL41" => Matrix.SpecialLinearGroup (Fin 4 ⊕ Fin 1) (ZMod 2)

namespace S125F

@[expose] def c46 : Fin 4 → Fin 10 := ![3, 6, 8, 9]

@[expose] def uniM (w : Fin 4 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun a b => if b.val < 4 then (if a = b then 1 else 0) else
    (if h : a.val < 4 then w ⟨a.val, h⟩ else 1)

@[expose] def embed (z : Fin 4 → ZMod 2) : Fin 10 → ZMod 2 :=
  fun k => ∑ b, if c46 b = k then z b else 0

theorem uniM_cols : ∀ w : Fin 4 → ZMod 2, ∀ k l : Fin 10, (∀ a, c46 a ≠ l) →
    decide ((JonesParshall.wedgeMat (uniM w) - 1) k l = 0) = true := by
  decide +kernel

theorem uniM_fix : ∀ w z : Fin 4 → ZMod 2, w ≠ 0 →
    decide ((JonesParshall.wedgeMat (uniM w) - 1) *ᵥ embed z = 0) = decide (z = 0 ∨ z = w) := by
  decide +kernel

theorem c46_injective : Function.Injective c46 := by decide

theorem pr5_c46 : ∀ a, JonesParshall.pr5 (c46 a) = (Fin.castLE (by norm_num) a, 4) := by
  decide

theorem not_mem_S6_iff : ∀ k : Fin 10,
    k ∉ ({0, 1, 2, 4, 5, 7} : Finset (Fin 10)) ↔ ∃ a, c46 a = k := by
  decide

theorem pr5_eq_four : ∀ l : Fin 10, (JonesParshall.pr5 l).2 = 4 → ∃ a, c46 a = l := by decide

theorem embed_c46 (z : Fin 4 → ZMod 2) (a : Fin 4) : embed z (c46 a) = z a := by
  change (∑ b, if c46 b = c46 a then z b else 0) = z a
  rw [Finset.sum_eq_single a (fun b _ hb => ite_eq_right fun h => hb (c46_injective h))
    (fun h => absurd (Finset.mem_univ a) h), ite_eq_left rfl]

theorem reindex_uniHom (W : Matrix (Fin 4) (Fin 1) (ZMod 2)) :
    ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5)
      (uniHom (ZMod 2) (Fin 4) (Fin 1) (Multiplicative.ofAdd W)) : SL5) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = uniM fun a => W a 0 := by
  ext a b
  rw [S125Nat.reindex_apply, uniHom_val, uniM, Matrix.of_apply]
  by_cases hb : b.val < 4
  · rw [sumEquiv_symm_of_lt _ hb, ite_eq_left hb]
    by_cases ha : a.val < 4
    · rw [sumEquiv_symm_of_lt _ ha, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · have : (⟨a.val, ha⟩ : Fin 4) ≠ ⟨b.val, hb⟩ := fun h => hab (Fin.ext (by
          have := congrArg Fin.val h
          simpa using this))
        rw [ite_eq_right this, ite_eq_right hab]
    · rw [sumEquiv_symm_of_le _ (not_lt.1 ha), Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      have hab : a ≠ b := fun h => by rw [h] at ha; exact ha hb
      rw [ite_eq_right hab]
  · rw [sumEquiv_symm_of_le _ (not_lt.1 hb), ite_eq_right hb]
    by_cases ha : a.val < 4
    · rw [sumEquiv_symm_of_lt _ ha, Matrix.fromBlocks_apply₁₂, dite_eq_left ha]
      congr 1
      exact Subsingleton.elim _ _
    · rw [sumEquiv_symm_of_le _ (not_lt.1 ha), Matrix.fromBlocks_apply₂₂, dite_eq_right ha]
      rw [Subsingleton.elim (⟨a.val - 4, _⟩ : Fin 1) ⟨b.val - 4, by omega⟩, Matrix.one_apply_eq]

theorem wedge_uniM_fix {w : Fin 4 → ZMod 2} (hw : w ≠ 0) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeMat (uniM w) *ᵥ x = x ↔
      (fun a => x (c46 a)) = 0 ∨ (fun a => x (c46 a)) = w := by
  have h1 : (JonesParshall.wedgeMat (uniM w) - 1) *ᵥ x =
      (JonesParshall.wedgeMat (uniM w) - 1) *ᵥ embed fun a => x (c46 a) := by
    funext k
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : ∃ a, c46 a = l
    · obtain ⟨a, rfl⟩ := hl
      rw [embed_c46]
    · have hl' : ∀ a, c46 a ≠ l := fun a h => hl ⟨a, h⟩
      have := of_decide_eq_true (uniM_cols w k l hl')
      rw [this, zero_mul, zero_mul]
  have h2 := uniM_fix w (fun a => x (c46 a)) hw
  rw [decide_eq_decide, ← h1, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
  exact h2

theorem sumEquiv41_four : (sumEquiv (show 4 + 1 = 5 by norm_num)).symm 4 = Sum.inr 0 := by
  rw [sumEquiv_symm_of_le _ (show 4 ≤ (4 : Fin 5).val by decide)]
  rfl

theorem reindex_row4 {g : SL41}
    (hg : g ∈ (parQ : Subgroup SL41)) (b : Fin 5) :
    ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5) g : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      4 b = if b = 4 then 1 else 0 := by
  have h22 : g.val.toBlocks₂₂ = 1 := by
    rw [← S125Pb.parJL_eq_parQ_of_fin_one] at hg
    exact (mem_parJL.1 hg).2
  have h21 : g.val.toBlocks₂₁ = 0 := hg
  rw [S125Nat.reindex_apply, sumEquiv41_four]
  by_cases hb : b.val < 4
  · rw [sumEquiv_symm_of_lt _ hb]
    have hb4 : b ≠ 4 := fun h => by rw [h] at hb; exact absurd hb (by decide)
    rw [ite_eq_right hb4]
    exact congrFun₂ h21 0 ⟨b.val, hb⟩
  · have hb4 : b = 4 := Fin.ext (by have := b.2; omega)
    subst hb4
    rw [sumEquiv41_four, ite_eq_left rfl]
    exact (congrFun₂ h22 0 0).trans (Matrix.one_apply_eq 0)

theorem wedge_row (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hM : ∀ b, M 4 b = if b = 4 then 1 else 0) (a : Fin 4) (x : Fin 10 → ZMod 2) :
    (JonesParshall.wedgeMat M *ᵥ x) (c46 a) =
      ∑ b, M (Fin.castLE (by norm_num) a) (Fin.castLE (by norm_num) b) * x (c46 b) := by
  have hent : ∀ l : Fin 10, JonesParshall.wedgeMat M (c46 a) l =
      if (JonesParshall.pr5 l).2 = 4 then M (Fin.castLE (by norm_num) a) (JonesParshall.pr5 l).1
        else 0 := by
    intro l
    have hl := pr5_lt l
    have hl1 : (JonesParshall.pr5 l).1 ≠ 4 := fun h => by
      rw [h] at hl
      exact absurd hl (by
        have := (JonesParshall.pr5 l).2.2
        intro h'
        change (4 : ℕ) < (JonesParshall.pr5 l).2.val at h'
        omega)
    simp only [JonesParshall.wedgeMat, Matrix.of_apply, pr5_c46, hM, ite_eq_right hl1, mul_zero,
      sub_zero]
    split_ifs <;> simp
  rw [Matrix.mulVec, dotProduct, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image c46)),
    Finset.sum_image fun i _ j _ h => c46_injective h]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [hent, pr5_c46, ite_eq_left rfl]
  · intro l _ hl
    rw [hent]
    by_cases h4 : (JonesParshall.pr5 l).2 = 4
    · obtain ⟨b, rfl⟩ := pr5_eq_four l h4
      exact absurd (Finset.mem_image_of_mem c46 (Finset.mem_univ b)) hl
    · rw [ite_eq_right h4, zero_mul]

theorem zvec_theta {g : SL41}
    (hg : g ∈ (parQ : Subgroup SL41)) (x : Fin 10 → ZMod 2) (a : Fin 4) :
    (JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5) g : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) (c46 a) =
      ∑ b, g.val.toBlocks₁₁ a b * x (c46 b) := by
  rw [wedge_row _ (reindex_row4 hg)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [S125Nat.reindex_castLE]
  rfl

theorem conj_uni {g : SL41} (hg : g ∈ (parQ : Subgroup SL41))
    (X : Matrix (Fin 4) (Fin 1) (ZMod 2)) :
    g * uniHom (ZMod 2) (Fin 4) (Fin 1) (Multiplicative.ofAdd X) * g⁻¹ =
      uniHom (ZMod 2) (Fin 4) (Fin 1) (Multiplicative.ofAdd (g.val.toBlocks₁₁ * X)) := by
  have h22 : g.val.toBlocks₂₂ = 1 := by
    rw [← S125Pb.parJL_eq_parQ_of_fin_one] at hg
    exact (mem_parJL.1 hg).2
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change g.val * (uniHom (ZMod 2) (Fin 4) (Fin 1) (Multiplicative.ofAdd X)).val =
    (uniHom (ZMod 2) (Fin 4) (Fin 1) (Multiplicative.ofAdd (g.val.toBlocks₁₁ * X))).val * g.val
  rw [uniHom_val, uniHom_val, eq_fromBlocks_of_mem_parQ hg, h22, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₁]
  rw [add_comm]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def zHom (F : Frame125 T L V) :
    ↥V →* Multiplicative (Matrix (Fin 4) (Fin 1) (ZMod 2)) where
  toFun v := Multiplicative.ofAdd (Matrix.of fun a _ => Multiplicative.toAdd (F.e v) (c46 a))
  map_one' := by
    rw [map_one]
    rfl
  map_mul' v w := by
    rw [map_mul]
    rfl

theorem part4_f (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ∃ f : ↥V →* ↥(autOn (ri T L F.V6) V), Function.Surjective f ∧
      (∀ v : ↥V, f v = 1 ↔ (v : G) ∈ F.V6) ∧
      (∀ (h : ↥(autOn (li L F.V6) V)) (v : ↥V),
        ((f ((h : MulAut ↥V) v) : MulAut ↥V)) = (h : MulAut ↥V) * f v * (h : MulAut ↥V)⁻¹) ∧
      ∀ r : ↥(autOn (ri T L F.V6) V), r ≠ 1 → ∀ v : ↥V,
        (r : MulAut ↥V) v = v ↔ (f v = 1 ∨ f v = r) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V6 F hf.normalizes hf.T_le
  have hTW := (S125L2G.T_le_V F hf.T_le).2.2.2
  have hres := S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ41
  have hde : 4 + 1 = 5 := by norm_num
  have hRL : autOn (ri T L F.V6) V ⊓ autOn (li L F.V6) V =
      (S125Pb.uniRad (Fin 4) (Fin 1)).map (theta F hde) :=
    rbar_inf_lbar F hH hf hde hst hTW hres S125Pb.uniRad_le_parJL
      (fun N hN hn hp => S125Pb.le_uniRad_of_parJL (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hN hn hp)
  have hML := (S125L2G.part4_groups h1222 F hH).1
  have hRle : autOn (ri T L F.V6) V ≤ autOn (li L F.V6) V := by
    rw [← hML]
    exact A4.autOn_mono ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_mi hTW))
  have hR : autOn (ri T L F.V6) V = (S125Pb.uniRad (Fin 4) (Fin 1)).map (theta F hde) := by
    rw [← hRL, inf_of_le_left hRle]
  have hLb : autOn (li L F.V6) V = (parQ : Subgroup SL41).map (theta F hde) := by
    have := lbar_eq F hf.normalizes hf.T_le hde hst hres
    rw [S125Pb.parJL_eq_parQ_of_fin_one] at this
    exact this
  let f₀ : ↥V →* MulAut ↥V :=
    (theta F hde).comp ((uniHom (ZMod 2) (Fin 4) (Fin 1)).comp (zHom F))
  have hf₀ : ∀ v, f₀ v ∈ autOn (ri T L F.V6) V := fun v => by
    rw [hR]
    exact ⟨_, ⟨zHom F v, rfl⟩, rfl⟩
  let f : ↥V →* ↥(autOn (ri T L F.V6) V) := f₀.codRestrict _ hf₀
  have hfv : ∀ v, (f v : MulAut ↥V) =
      theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) (zHom F v)) := fun _ => rfl
  have hinj : Function.Injective fun X : Multiplicative (Matrix (Fin 4) (Fin 1) (ZMod 2)) =>
      theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X) :=
    (theta_injective F hde).comp (uniHom_injective (F := ZMod 2) (a := Fin 4) (b := Fin 1))
  have hz : ∀ (v : ↥V) (X : Multiplicative (Matrix (Fin 4) (Fin 1) (ZMod 2))),
      zHom F v = X ↔
        ∀ a, Multiplicative.toAdd (F.e v) (c46 a) = Multiplicative.toAdd X a 0 := by
    intro v X
    constructor
    · intro h a
      rw [← h]
      rfl
    · intro h
      apply Multiplicative.toAdd.injective
      ext a b
      rw [Subsingleton.elim b 0]
      exact h a
  have hf1 : ∀ v, f v = 1 ↔ zHom F v = 1 := by
    intro v
    constructor
    · intro h1
      have h2 : (f v : MulAut ↥V) = theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) 1) := by
        rw [h1, map_one, map_one]
        rfl
      rw [hfv] at h2
      exact hinj h2
    · intro h1
      apply Subtype.ext
      rw [hfv, h1, map_one, map_one]
      rfl
  have hz1 : ∀ v, zHom F v = 1 ↔ ∀ a, Multiplicative.toAdd (F.e v) (c46 a) = 0 := by
    intro v
    rw [hz]
    rfl
  refine ⟨f, ?_, fun v => ?_, fun h v => ?_, fun r hr v => ?_⟩
  ·
    rintro ⟨r, hrR⟩
    have hrR' := hrR
    rw [hR] at hrR'
    obtain ⟨u, ⟨X, rfl⟩, rfl⟩ := hrR'
    let x : Fin 10 → ZMod 2 := embed fun a => Multiplicative.toAdd X a 0
    refine ⟨F.e.symm (Multiplicative.ofAdd x), Subtype.ext ?_⟩
    rw [hfv]
    have : zHom F (F.e.symm (Multiplicative.ofAdd x)) = X := (hz _ X).2 fun a => by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact embed_c46 _ a
    rw [this]
  ·
    change f v = 1 ↔ (v : G) ∈ F.sub {0, 1, 2, 4, 5, 7}
    rw [mem_sub_iff, hf1, hz1]
    constructor
    · intro h k hk
      obtain ⟨a, rfl⟩ := (not_mem_S6_iff k).1 hk
      exact h a
    · intro h a
      exact h _ ((not_mem_S6_iff _).2 ⟨a, rfl⟩)
  ·
    obtain ⟨g, hg, hgh⟩ : (h : MulAut ↥V) ∈ (parQ : Subgroup SL41).map (theta F hde) :=
      hLb ▸ h.2
    have hzg : zHom F ((h : MulAut ↥V) v) = Multiplicative.ofAdd
        (g.val.toBlocks₁₁ * Multiplicative.toAdd (zHom F v)) := by
      rw [hz]
      intro a
      rw [← hgh, e_theta_apply, toAdd_ofAdd, zvec_theta hg, toAdd_ofAdd, Matrix.mul_apply]
      rfl
    calc ((f ((h : MulAut ↥V) v) : MulAut ↥V)) =
        theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) (zHom F ((h : MulAut ↥V) v))) := hfv _
      _ = theta F hde (g * uniHom (ZMod 2) (Fin 4) (Fin 1) (zHom F v) * g⁻¹) := by
        rw [hzg, ← conj_uni hg (Multiplicative.toAdd (zHom F v)), ofAdd_toAdd]
      _ = (h : MulAut ↥V) * f v * (h : MulAut ↥V)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hgh, hfv]
  ·
    obtain ⟨r, hrR⟩ := r
    have hrR' := hrR
    rw [hR] at hrR'
    obtain ⟨u, ⟨X, rfl⟩, rfl⟩ := hrR'
    set w : Fin 4 → ZMod 2 := fun a => Multiplicative.toAdd X a 0 with hw
    have hw0 : w ≠ 0 := by
      intro h0
      apply hr
      apply Subtype.ext
      have : X = 1 := by
        apply Multiplicative.toAdd.injective
        ext a b
        rw [Subsingleton.elim b 0]
        exact congrFun h0 a
      change theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X) = 1
      rw [this, map_one, map_one]
    have hact : ((⟨theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X), hrR⟩ :
        ↥(autOn (ri T L F.V6) V)) : MulAut ↥V) v = v ↔
        JonesParshall.wedgeMat (uniM w) *ᵥ Multiplicative.toAdd (F.e v) =
          Multiplicative.toAdd (F.e v) := by
      change theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X) v = v ↔ _
      have e1 : theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X) =
          theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1)
            (Multiplicative.ofAdd (Multiplicative.toAdd X))) := by
        rw [ofAdd_toAdd]
      rw [e1, ← F.e.injective.eq_iff, e_theta_apply, reindex_uniHom,
        ← Multiplicative.toAdd.injective.eq_iff, toAdd_ofAdd]
    rw [hact, wedge_uniM_fix hw0, hf1, hz1]
    have e2 : f v = ⟨theta F hde (uniHom (ZMod 2) (Fin 4) (Fin 1) X), hrR⟩ ↔ zHom F v = X := by
      constructor
      · intro h1
        have h2 := congrArg (fun r : ↥(autOn (ri T L F.V6) V) => (r : MulAut ↥V)) h1
        simp only at h2
        rw [hfv] at h2
        exact hinj h2
      · intro h1
        apply Subtype.ext
        rw [hfv, h1]
    rw [e2, hz]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl fun a => congrFun h1 a
      · exact Or.inr fun a => congrFun h1 a
    · rintro (h1 | h1)
      · exact Or.inl (funext h1)
      · exact Or.inr (funext h1)

end S125F

end CFSG.Quasithin.H13

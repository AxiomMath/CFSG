module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLOut
public import CFSG.GH74.GLS.LU.Local.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private def conjNormalizerSub {G : Type} [Group G] (X : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : X ≃* X where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) (x : G)).mp x.2⟩
  left_inv x := Subtype.ext <| by
    show g⁻¹ * (g * (x : G) * g⁻¹) * g = x
    group
  right_inv x := Subtype.ext <| by
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x
    group
  map_mul' x y := Subtype.ext <| by
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group

private def conjNormalizerQuot {G : Type} [Group G] (X : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : MulAut (↥X ⧸ Subgroup.center ↥X) :=
  QuotientGroup.congr (Subgroup.center ↥X) (Subgroup.center ↥X) (conjNormalizerSub X g hg)
    (Subgroup.map_center_eq (conjNormalizerSub X g hg))

private lemma conjNormalizerQuot_mk {G : Type} [Group G] (X : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (x : X) :
    conjNormalizerQuot X g hg (QuotientGroup.mk x) =
      QuotientGroup.mk (conjNormalizerSub X g hg x) :=
  rfl

private lemma conjNormalizerQuot_pow_mk {G : Type} [Group G] (X : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (k : ℕ) (q : X) :
    (conjNormalizerQuot X g hg ^ k) (QuotientGroup.mk q) =
      QuotientGroup.mk (⟨g ^ k * (q : G) * (g ^ k)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (pow_mem hg k) (q : G)).mp q.2⟩ : X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (conjNormalizerQuot X g hg) k, MulAut.mul_apply, ih, conjNormalizerQuot_mk]
    congr 1
    apply Subtype.ext
    show g * (g ^ k * (q : G) * (g ^ k)⁻¹) * g⁻¹ = g ^ (k + 1) * (q : G) * (g ^ (k + 1))⁻¹
    group

theorem exists_mem_inv_mul_mem_centralizer_of_odd {G : Type} [Group G] [Finite G]
    {X : Subgroup G} (hXq : CFSG.IsQuasisimple X) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {m : ℕ} (hmo : Odd m) (hgm : g ^ m = 1) :
    ∃ x ∈ X, x⁻¹ * g ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one hmod
  have hn3 : 3 ≤ n := by rcases hn with h | h <;> omega
  have hσm : conjNormalizerQuot X g hg ^ m = 1 := by
    ext z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
    rw [conjNormalizerQuot_pow_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp [hgm]
  have hαm : (MulAut.congr e (conjNormalizerQuot X g hg)) ^ m = 1 := by
    rw [← map_pow (MulAut.congr e), hσm, map_one]
  obtain ⟨y, hy⟩ := Hering214.inner_of_pow_odd_eq_one hK hn3 hmo hαm
  have hconj : ∀ q : ↥X ⧸ Subgroup.center ↥X,
      conjNormalizerQuot X g hg q = e.symm y * q * (e.symm y)⁻¹ := by
    intro q
    have h1 : e (conjNormalizerQuot X g hg q) = y * e q * y⁻¹ := by
      have := DFunLike.congr_fun hy (e q)
      simpa [MulAut.congr_apply, MulAut.conj_apply] using this
    calc conjNormalizerQuot X g hg q = e.symm (e (conjNormalizerQuot X g hg q)) :=
          (e.symm_apply_apply _).symm
      _ = e.symm (y * e q * y⁻¹) := by rw [h1]
      _ = e.symm y * q * (e.symm y)⁻¹ := by simp [map_mul, map_inv]
  obtain ⟨X₀, hX₀⟩ := QuotientGroup.mk_surjective (e.symm y)
  rw [← hX₀] at hconj
  have hJX := Subgroup.isPerfect_iff.mp hXq.1
  have hcond : ∀ j ∈ X, ∃ c ∈ X, (∀ g' ∈ X, c * g' = g' * c) ∧
      ((X₀ : G)⁻¹ * g) * j * ((X₀ : G)⁻¹ * g)⁻¹ = c * j := by
    intro j hj
    have hJ : (QuotientGroup.mk (conjNormalizerSub X g hg (⟨j, hj⟩ : X)) :
        ↥X ⧸ Subgroup.center ↥X) = QuotientGroup.mk (X₀ * (⟨j, hj⟩ : X) * X₀⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← hconj (QuotientGroup.mk (⟨j, hj⟩ : X)), conjNormalizerQuot_mk]
    obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : X,
        c₀ = (X₀ * (⟨j, hj⟩ : X) * X₀⁻¹)⁻¹ * conjNormalizerSub X g hg (⟨j, hj⟩ : X) :=
      ⟨_, rfl⟩
    have hc₀ : c₀ ∈ Subgroup.center ↥X := by
      rw [hc₀def]
      exact QuotientGroup.eq.mp hJ.symm
    have hw := Subgroup.mem_center_iff.mp hc₀
    have hcj : j * (c₀ : G) = (c₀ : G) * j := congrArg Subtype.val (hw ⟨j, hj⟩)
    have hcx : (X₀ : G) * (c₀ : G) = (c₀ : G) * (X₀ : G) := congrArg Subtype.val (hw X₀)
    have hc : (c₀ : G) = ((X₀ : G) * j * (X₀ : G)⁻¹)⁻¹ * (g * j * g⁻¹) := by
      subst hc₀def
      rfl
    have hP : g * j * g⁻¹ = (X₀ : G) * j * (X₀ : G)⁻¹ * (c₀ : G) := by
      rw [hc, mul_inv_cancel_left]
    have hxc : (X₀ : G)⁻¹ * (c₀ : G) * (X₀ : G) = (c₀ : G) := by
      calc (X₀ : G)⁻¹ * (c₀ : G) * (X₀ : G) = (X₀ : G)⁻¹ * ((c₀ : G) * (X₀ : G)) :=
            mul_assoc _ _ _
        _ = (X₀ : G)⁻¹ * ((X₀ : G) * (c₀ : G)) := by rw [hcx]
        _ = (c₀ : G) := inv_mul_cancel_left _ _
    refine ⟨(c₀ : G), c₀.2, fun g' hg' => (congrArg Subtype.val (hw ⟨g', hg'⟩)).symm, ?_⟩
    calc ((X₀ : G)⁻¹ * g) * j * ((X₀ : G)⁻¹ * g)⁻¹
        = (X₀ : G)⁻¹ * (g * j * g⁻¹) * (X₀ : G) := by group
      _ = (X₀ : G)⁻¹ * ((X₀ : G) * j * (X₀ : G)⁻¹ * (c₀ : G)) * (X₀ : G) := by rw [hP]
      _ = j * ((X₀ : G)⁻¹ * (c₀ : G) * (X₀ : G)) := by group
      _ = j * (c₀ : G) := by rw [hxc]
      _ = (c₀ : G) * j := hcj
  have hcent := CFSG.GH74.GLS.LU.Local.centralizes_of_perfect_mod_center hJX hcond
  refine ⟨(X₀ : G), X₀.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (mul_inv_eq_iff_eq_mul.mp (hcent h hh)).symm

end CFSG.RankThree.PartTwo.Sec21

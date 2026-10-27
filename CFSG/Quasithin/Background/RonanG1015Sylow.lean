module

public import CFSG.Quasithin.Background.RonanG1015Order4
public import CFSG.Quasithin.Background.RonanG1015Big
public import CFSG.Quasithin.Background.RonanG1015Inputs
public import CFSG.RankThree.Literature.FSmithOrthogonal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.Quasithin.G11.P4InspSp

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem exists_hyp_pairs [Finite U] (hf : IsSymplectic f) (k : ℕ)
    (hk : 2 * k ≤ Module.finrank (ZMod 2) U) :
    ∃ E F : Fin k → U, (∀ i j, f (E i) (E j) = 0) ∧ (∀ i j, f (F i) (F j) = 0) ∧
      ∀ i j, f (E i) (F j) = if i = j then 1 else 0 := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨m, b, hd, h1, h2, h3⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      f hf.1 hf.nondegenerate
  have hkm : k ≤ m := by omega
  refine ⟨fun i => b (Sum.inl (Fin.castLE hkm i)), fun i => b (Sum.inr (Fin.castLE hkm i)),
    fun i j => h1 _ _, fun i j => h2 _ _, fun i j => ?_⟩
  rw [h3]
  simp [Fin.castLE_inj]

theorem exists_sp_config [Finite U] (hf : IsSymplectic f) (hd : 4 ≤ Module.finrank (ZMod 2) U) :
    ∃ a b c : U, f a b = 1 ∧ f b c = 1 ∧ f a c = 0 ∧ a ≠ c := by
  obtain ⟨E, F, h1, h2, h3⟩ := exists_hyp_pairs hf 2 (by omega)
  have e00 := h3 0 0
  have e11 := h3 1 1
  have e01 := h3 0 1
  have e10 := h3 1 0
  simp only [if_true] at e00 e11
  rw [if_neg (by decide)] at e01 e10
  have hFE0 : f (F 0) (E 0) = 1 := by rw [hf.symm']; exact e00
  refine ⟨E 0, F 0 + E 1, F 1, ?_, ?_, ?_, ?_⟩
  · rw [map_add, h1, e00, add_zero]
  · rw [map_add, LinearMap.add_apply, h2, e11, zero_add]
  · exact e01
  · intro h
    have := congrArg (fun w => f (F 0) w) h
    simp only [hFE0, h2] at this
    exact one_ne_zero this

section Orth

variable {q : U → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + f x y)
include hq

theorem exists_nonsing_pair {x y : U} (hxy : f x y = 1) :
    ∃ e, q e = 1 ∧ ∀ w, f w x = 0 → f w y = 0 → f w e = 0 := by
  rcases g12_eq_zero_or_one (q x) with hx | hx
  · rcases g12_eq_zero_or_one (q y) with hy | hy
    · refine ⟨x + y, ?_, fun w hwx hwy => ?_⟩
      · rw [hq, hx, hy, hxy]; decide
      · rw [map_add, hwx, hwy, add_zero]
    · exact ⟨y, hy, fun w _ hwy => hwy⟩
  · exact ⟨x, hx, fun w hwx _ => hwx⟩

theorem exists_nonsing_lift {e x : U} (he : q e = 1) (hxe : f x e = 0) :
    ∃ s : ZMod 2, q (x + s • e) = 1 := by
  rcases g12_eq_zero_or_one (q x) with hx | hx
  · refine ⟨1, ?_⟩
    rw [one_smul, hq, hx, he, hxe]; decide
  · exact ⟨0, by rw [zero_smul, add_zero]; exact hx⟩

end Orth

theorem lift_f (hf : IsSymplectic f) {e x y : U} (hxe : f x e = 0) (hye : f y e = 0)
    (s t : ZMod 2) : f (x + s • e) (y + t • e) = f x y := by
  have hex : f e x = 0 := by rw [hf.symm']; exact hxe
  have hey : f e y = 0 := by rw [hf.symm']; exact hye
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hf.1, hxe,
    hye, hex, hey, mul_zero, add_zero]

theorem exists_orth_config [Finite U] (hf : IsSymplectic f) {q : U → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hd : 6 ≤ Module.finrank (ZMod 2) U) :
    ∃ a b c e : U, q a = 1 ∧ q b = 1 ∧ q c = 1 ∧ q e = 1 ∧ f a b = 1 ∧ f b c = 1 ∧ f a c = 0 ∧
      a ≠ c ∧ f a e = 0 ∧ f b e = 0 ∧ f c e = 0 := by
  obtain ⟨E, F, h1, h2, h3⟩ := exists_hyp_pairs hf 3 (by omega)
  have z : ∀ i j : Fin 3, i ≠ j → f (E i) (F j) = 0 := fun i j h => by rw [h3, if_neg h]
  have d : ∀ i : Fin 3, f (E i) (F i) = 1 := fun i => by rw [h3, if_pos rfl]
  have zs : ∀ i j : Fin 3, i ≠ j → f (F j) (E i) = 0 := fun i j h => by rw [hf.symm']; exact z i j h
  have ds : ∀ i : Fin 3, f (F i) (E i) = 1 := fun i => by rw [hf.symm']; exact d i
  obtain ⟨e, he1, he2⟩ := exists_nonsing_pair hq (x := E 2) (y := F 2) (d 2)
  have hE0 : f (E 0) e = 0 := he2 _ (h1 _ _) (z _ _ (by decide))
  have hF0 : f (F 0) e = 0 := he2 _ (zs _ _ (by decide)) (h2 _ _)
  have hE1 : f (E 1) e = 0 := he2 _ (h1 _ _) (z _ _ (by decide))
  have hF1 : f (F 1) e = 0 := he2 _ (zs _ _ (by decide)) (h2 _ _)
  have hx2 : f (F 0 + E 1) e = 0 := by rw [map_add, LinearMap.add_apply, hF0, hE1, add_zero]
  obtain ⟨s₁, hs₁⟩ := exists_nonsing_lift hq he1 hE0
  obtain ⟨s₂, hs₂⟩ := exists_nonsing_lift hq he1 hx2
  obtain ⟨s₃, hs₃⟩ := exists_nonsing_lift hq he1 hF1
  have hee : f e e = 0 := hf.1 e
  refine ⟨E 0 + s₁ • e, (F 0 + E 1) + s₂ • e, F 1 + s₃ • e, e, hs₁, hs₂, hs₃, he1, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [lift_f hf hE0 hx2, map_add, h1 0 1, d 0, add_zero]
  · rw [lift_f hf hx2 hF1, map_add, LinearMap.add_apply, h2 0 1, d 1, zero_add]
  · rw [lift_f hf hE0 hF1, z 0 1 (by decide)]
  · intro h
    have h' := congrArg (fun w => f (F 0) w) h
    simp only [map_add, map_smul, hF0, hee, smul_eq_mul, mul_zero, add_zero, ds 0, h2,
      zs 0 1 (by decide)] at h'
    exact one_ne_zero h'
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hE0, hee,
      mul_zero, add_zero]
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hF0, hE1, hee,
      mul_zero, add_zero]
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hF1, hee,
      mul_zero, add_zero]


theorem reflect_eq_tv (hf : IsSymplectic f) {q : U → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {u : U} (hu : q u = 1) :
    CFSG.ClassicalGroups.Orthogonal.reflect (p4insporth_quad hq) u = tv f u := by
  refine LinearEquiv.ext fun x => ?_
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hu, p4insporth_polar_quad hq,
    tv_apply hf]

theorem orth_order_four [Finite U] (hf : IsSymplectic f) {q : U → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hd : 6 ≤ Module.finrank (ZMod 2) U) :
    ∃ x ∈ ⁅orthSub q, orthSub q⁆, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  obtain ⟨a, b, c, e, ha, hb, hc, he, hab, hbc, hac, hne, hae, hbe, hce⟩ :=
    exists_orth_config hf hq hd
  refine ⟨tv f a * tv f b * tv f c * tv f e, ?_, path_extra_pow_four hf hab hbc hac hae hbe hce,
    path_extra_sq_ne_one hf hab hbc hac hne hae hbe hce⟩
  have hQ := p4insporth_nondegenerate_quad hf hq
  have h5 : 5 ≤ Module.finrank (ZMod 2) U := by omega
  have hm := CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator hQ h5
    (u := a) (u' := b) ha hb
  have hm' := CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator hQ h5
    (u := c) (u' := e) hc he
  rw [reflect_eq_tv hf hq ha, reflect_eq_tv hf hq hb, p4insporth_orthogonalGroup_quad hq] at hm
  rw [reflect_eq_tv hf hq hc, reflect_eq_tv hf hq he, p4insporth_orthogonalGroup_quad hq] at hm'
  have e : tv f a * tv f b * tv f c * tv f e = (tv f a * tv f b) * (tv f c * tv f e) := by
    simp only [mul_assoc]
  rw [e]
  exact Subgroup.mul_mem _ hm hm'

theorem sp_order_four [Finite U] (hf : IsSymplectic f) (hd : 4 ≤ Module.finrank (ZMod 2) U) :
    ∃ x ∈ spSub f, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  obtain ⟨a, b, c, hab, hbc, hac, hne⟩ := exists_sp_config hf hd
  exact ⟨tv f a * tv f b * tv f c,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (tv_mem_spSub hf a) (tv_mem_spSub hf b))
      (tv_mem_spSub hf c), path_pow_four hf hab hbc hac, path_sq_ne_one hf hab hbc hac hne⟩

theorem exists_order_four_of_big [Finite U] {M K Q : Subgroup (GLV U)} {v : U}
    (hD : G121Data f M K Q v) (hns : ¬ CFSG.IsStronglyQuasithin ↥K) :
    ∃ x : ↥K, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  have key : ∀ {x : GLV U} (hx : x ∈ K), x ^ 4 = 1 → x ^ 2 ≠ 1 →
      ∃ x : ↥K, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
    intro x hx h4 h2
    refine ⟨⟨x, hx⟩, Subtype.ext (by simpa using h4), fun h => h2 ?_⟩
    have := congrArg Subtype.val h
    simpa using this
  rcases big_cases hD hns with ⟨-, hK, h6⟩ | ⟨q, hq, -, hK, -, n, hn, hcases⟩
  · obtain ⟨x, hx, h4, h2⟩ := sp_order_four hD.symp (by omega)
    exact key (by rw [hK]; exact hx) h4 h2
  · have h6 : 6 ≤ Module.finrank (ZMod 2) U := by rcases hcases with h | h <;> omega
    obtain ⟨x, hx, h4, h2⟩ := orth_order_four hD.symp hq h6
    exact key (by rw [hK]; exact hx) h4 h2

theorem nonSQTSylow : NonSQTSylow := by
  intro U _ _ _ f M K Q v hD hns P hP
  obtain ⟨x, h4, h2⟩ := exists_order_four_of_big hD hns
  refine CFSG.Quasithin.G11.P4InspEnd.p4inspend_no_order4 P (fun s hs => ?_) x h4 h2
  have hsq := hD.Q_sq _ (hP s hs)
  exact Subtype.ext (by simpa using hsq)

end RonanG1015

end CFSG.Quasithin

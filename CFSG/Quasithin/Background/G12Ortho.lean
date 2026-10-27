module

public import CFSG.Quasithin.Background.G12Rad
import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem g12o_eq_or_eq_of_mul_mem {G : Type*} [Group G] {N O Γ : Subgroup G} {T : Set G}
    (hN : ∀ g ∈ O, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hTO : T ⊆ O)
    (hTT : ∀ s ∈ T, ∀ t ∈ T, s * t ∈ N) (hO : O ≤ Subgroup.closure (T ∪ N))
    (h1 : N ≤ Γ) (h2 : Γ ≤ O) : Γ = N ∨ Γ = O := by
  by_cases hΓ : Γ ≤ N
  · exact Or.inl (le_antisymm hΓ h1)
  right
  refine le_antisymm h2 ?_
  obtain ⟨x, hxΓ, hxN⟩ := Set.not_subset.1 hΓ
  have hT : ∃ t₀, t₀ ∈ T := by
    by_contra hT
    simp only [not_exists] at hT
    apply hxN
    have e : T ∪ (N : Set G) = N := by
      ext g
      simp [hT g]
    rw [e, Subgroup.closure_eq] at hO
    exact hO (h2 hxΓ)
  obtain ⟨t₀, ht₀⟩ := hT
  have ht₀O : t₀ ∈ O := hTO ht₀
  have ht₀₀ : t₀ * t₀ ∈ N := hTT t₀ ht₀ t₀ ht₀
  have key : ∀ g ∈ Subgroup.closure (T ∪ (N : Set G)), g ∈ N ∨ t₀ * g ∈ N := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact Or.inr (hTT t₀ ht₀ g hg)
      · exact Or.inl hg
    | one => exact Or.inl N.one_mem
    | mul x y _ _ ihx ihy =>
      rcases ihx with hx | hx <;> rcases ihy with hy | hy
      · exact Or.inl (N.mul_mem hx hy)
      · right
        have e : t₀ * (x * y) = t₀ * x * t₀⁻¹ * (t₀ * y) := by group
        rw [e]
        exact N.mul_mem (hN t₀ ht₀O x hx) hy
      · right
        rw [← mul_assoc]
        exact N.mul_mem hx hy
      · left
        have e : x * y = t₀⁻¹ * (t₀ * x) * t₀⁻¹⁻¹ * (t₀ * t₀)⁻¹ * (t₀ * y) := by group
        rw [e]
        exact N.mul_mem (N.mul_mem (hN t₀⁻¹ (O.inv_mem ht₀O) _ hx) (N.inv_mem ht₀₀)) hy
    | inv x _ ihx =>
      rcases ihx with hx | hx
      · exact Or.inl (N.inv_mem hx)
      · right
        have e : t₀ * x⁻¹ = t₀ * (t₀ * x)⁻¹ * t₀⁻¹ * (t₀ * t₀) := by group
        rw [e]
        exact N.mul_mem (hN t₀ ht₀O _ (N.inv_mem hx)) ht₀₀
  intro g hg
  rcases key g (hO hg) with hgN | hgN
  · exact h1 hgN
  · have hxt : t₀ * x ∈ N := (key x (hO (h2 hxΓ))).resolve_left hxN
    have e : g = x * (t₀ * x)⁻¹ * (t₀ * g) := by group
    rw [e]
    exact Γ.mul_mem (Γ.mul_mem hxΓ (h1 (N.inv_mem hxt))) (h1 hgN)

theorem g12o_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide

theorem g12o_mul_self : ∀ a : ZMod 2, a * a = a := by decide

theorem g12o_tv_mul_tv (hB : IsSymplectic B) {a b : V} (hab : B a b = 0) :
    radE B a 0 1 * radE B b 0 1 = radE B (a + b) a 1 := by
  have hu : B (a + b) a = 0 := by
    rw [map_add, LinearMap.add_apply, hB.1 a, hB.symm' b a, hab, add_zero]
  have hba : B b a = 0 := by rw [hB.symm']; exact hab
  refine LinearEquiv.ext fun x => ?_
  show radE B a 0 1 (radE B b 0 1 x) = radE B (a + b) a 1 x
  rw [radE_one_apply hB, radE_one_apply hB, radE_apply hB hu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hba,
    mul_zero, add_zero, one_mul]
  have h2a : (2 : ZMod 2) • a = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have h2b : (2 : ZMod 2) • b = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  linear_combination (norm := module) (-(B x b) - B x a) • h2a - (B x a) • h2b

section Quad

variable {q : V → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + B x y)
include hq

theorem g12o_q_zero : q 0 = 0 := by
  have h := hq 0 0
  simp only [add_zero, map_zero] at h
  have h2 := g12_add_self (q 0)
  rw [← h] at h2
  exact h2

theorem g12o_q_smul (c : ZMod 2) (x : V) : q (c • x) = c * q x := by
  rcases g12_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, zero_mul, g12o_q_zero hq]
  · rw [one_smul, one_mul]

theorem g12o_B_eq (x y : V) : B x y = q (x + y) + q x + q y := by
  rw [hq x y]
  have two0 : (2 : ZMod 2) = 0 := rfl
  linear_combination (-(q x) - q y) * two0

theorem g12o_orthSub_le_spSub : orthSub q ≤ spSub B := by
  intro g hg x y
  have hg' : ∀ x, q (g x) = q x := hg
  rw [g12o_B_eq hq (g x) (g y), g12o_B_eq hq x y, ← map_add, hg', hg', hg']

theorem g12o_q_radE (hB : IsSymplectic B) {z a : V} (hqz : q z = 0) (hza : B z a = 0)
    (c : ZMod 2) (x : V) : q (radE B z a c x) = q x + B x z * (q a + c) := by
  have haz : B a z = 0 := by rw [hB.symm']; exact hza
  rw [radE_apply hB hza, hq (x + _) _, hq x _, g12o_q_smul hq, g12o_q_smul hq, hqz]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haz,
    mul_zero, add_zero]
  have two0 : (2 : ZMod 2) = 0 := rfl
  linear_combination (B x z * B x a) * two0 + c * g12o_mul_self (B x z)

theorem g12o_radE_mem_orthSub (hB : IsSymplectic B) {z a : V} (hqz : q z = 0)
    (hza : B z a = 0) : radE B z a (q a) ∈ orthSub q := by
  intro x
  rw [g12o_q_radE hq hB hqz hza, g12_add_self, mul_zero, add_zero]

theorem g12o_eq_of_radE_mem (hB : IsSymplectic B) {z a : V} (hz0 : z ≠ 0) (hqz : q z = 0)
    (hza : B z a = 0) {c : ZMod 2} (hc : radE B z a c ∈ orthSub q) : c = q a := by
  obtain ⟨x, hx⟩ := hB.exists_B_eq_one hz0
  have h : q (radE B z a c x) = q x := hc x
  rw [g12o_q_radE hq hB hqz hza, hx, one_mul] at h
  have h2 : q a + c = 0 := by linear_combination h
  exact g12o_eq_of_add_eq_zero _ _ h2

theorem g12o_tv_mem_orthSub (hB : IsSymplectic B) {a : V} (hqa : q a = 1) :
    radE B a 0 1 ∈ orthSub q := by
  intro x
  rw [radE_one_apply hB, hq, g12o_q_smul hq, hqa, map_smul, smul_eq_mul, mul_one,
    g12o_mul_self, add_assoc, g12_add_self, add_zero]

section Fin

variable [Finite V]

theorem g12o_mem_QSub_orthSub_iff (hB : IsSymplectic B) {z : V} (hz0 : z ≠ 0) (hqz : q z = 0)
    {g : GLV V} :
    g ∈ QSub (orthSub q) z (perp B z) ↔ ∃ a, B z a = 0 ∧ g = radE B z a (q a) := by
  constructor
  · rintro ⟨hgO, hgz, hgU⟩
    have hgSp : g ∈ spSub B := g12o_orthSub_le_spSub hq hgO
    obtain ⟨x0, hx0⟩ := hB.exists_B_eq_one hz0
    have hz : z ∈ perp B z := mem_perp_iff.2 (hB.1 z)
    let φ : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) - LinearMap.id
    let f : perp B z →ₗ[ZMod 2] ZMod 2 := (B x0).comp (φ.comp (perp B z).subtype)
    have hf : f ⟨z, hz⟩ = 0 := by
      show B x0 (g z - z) = 0
      rw [hgz, sub_self, map_zero]
    obtain ⟨a, hza, ha⟩ := hB.exists_rep_perp hz f hf
    have hgu : ∀ u ∈ perp B z, g u = u + B u a • z := by
      intro u hu
      obtain ⟨-, hgu'⟩ := hgU u hu
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hgu'
      have h1 : f ⟨u, hu⟩ = t := by
        show B x0 (g u - u) = t
        rw [← ht, map_smul, smul_eq_mul, hx0, mul_one]
      have h2 : B u a = t := by rw [← h1]; exact ha ⟨u, hu⟩
      rw [h2, ht]
      abel
    obtain ⟨c, hc⟩ := eq_radE_of_fix hB hza hgSp hgu
    refine ⟨a, hza, ?_⟩
    have hcq : c = q a := g12o_eq_of_radE_mem hq hB hz0 hqz hza (hc ▸ hgO)
    rw [hc, hcq]
  · rintro ⟨a, hza, rfl⟩
    exact radE_mem_QSub hB hza (g12o_radE_mem_orthSub hq hB hqz hza)

theorem g12o_radE_mem_omegaSub (hB : IsSymplectic B) {z a : V} (hz0 : z ≠ 0) (hqz : q z = 0)
    (hza : B z a = 0) : radE B z a (q a) ∈ omegaSub B q :=
  Subgroup.subset_closure ⟨z, hz0, hqz, (g12o_mem_QSub_orthSub_iff hq hB hz0 hqz).2 ⟨a, hza, rfl⟩⟩

theorem g12o_omegaSub_le_of_radE_mem (hB : IsSymplectic B) {H : Subgroup (GLV V)}
    (hH : ∀ z a, z ≠ 0 → q z = 0 → B z a = 0 → radE B z a (q a) ∈ H) : omegaSub B q ≤ H := by
  rw [omegaSub, Subgroup.closure_le]
  rintro g ⟨z, hz0, hqz, hg⟩
  obtain ⟨a, hza, rfl⟩ := (g12o_mem_QSub_orthSub_iff hq hB hz0 hqz).1 hg
  exact hH z a hz0 hqz hza

theorem g12o_omegaSub_le_orthSub (hB : IsSymplectic B) : omegaSub B q ≤ orthSub q :=
  g12o_omegaSub_le_of_radE_mem hq hB fun _ _ _ hqz hza => g12o_radE_mem_orthSub hq hB hqz hza

theorem g12o_conj_mem_omegaSub (hB : IsSymplectic B) {g : GLV V} (hg : g ∈ orthSub q)
    {x : GLV V} (hx : x ∈ omegaSub B q) : g * x * g⁻¹ ∈ omegaSub B q := by
  have hgSp : g ∈ spSub B := g12o_orthSub_le_spSub hq hg
  have hle : omegaSub B q ≤ (omegaSub B q).comap (MulAut.conj g).toMonoidHom := by
    refine g12o_omegaSub_le_of_radE_mem hq hB fun z a hz0 hqz hza => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, radE_conj hB hgSp hza]
    have hga : q (g a) = q a := hg a
    rw [← hga]
    refine g12o_radE_mem_omegaSub hq hB ?_ ?_ ?_
    · intro h
      apply hz0
      simpa using h
    · rw [hg z]
      exact hqz
    · rw [hgSp z a]
      exact hza
  exact hle hx

theorem g12o_omegaSub_le (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} (hΓq : Γ ≤ orthSub q)
    {v : V} (hv : IsStarVec B Γ v) (hqv : q v = 0)
    (horb : ∀ w, w ≠ 0 → q w = 0 → ∃ g ∈ Γ, w = g v) : omegaSub B q ≤ Γ := by
  have hΓ : Γ ≤ spSub B := hΓq.trans (g12o_orthSub_le_spSub hq)
  obtain ⟨hv0, hrad⟩ := (isStarVec_iff_rad hB hΓ).1 hv
  have h1 : ∀ a, B v a = 0 → radE B v a (q a) ∈ Γ := by
    intro a hva
    obtain ⟨c, hc⟩ := hrad a hva
    have hcq := g12o_eq_of_radE_mem hq hB hv0 hqv hva (hΓq hc)
    rwa [hcq] at hc
  refine g12o_omegaSub_le_of_radE_mem hq hB fun z a hz0 hqz hza => ?_
  obtain ⟨g, hg, rfl⟩ := horb z hz0 hqz
  have hgi : ∀ x y, B (g x) (g y) = B x y := hΓ hg
  have hva : B v (g.symm a) = 0 := by
    rw [← hgi, LinearEquiv.apply_symm_apply]
    exact hza
  have h2 := radE_conj_mem hB hΓ hg hva (h1 _ hva)
  rw [LinearEquiv.apply_symm_apply] at h2
  have h3 : q (g.symm a) = q a := by
    have := hΓq hg (g.symm a)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  rwa [h3] at h2

theorem g12o_tv_mul_tv_mem_of_perp (hB : IsSymplectic B) {a b : V} (hqa : q a = 1)
    (hqb : q b = 1) (hab : B a b = 0) : radE B a 0 1 * radE B b 0 1 ∈ omegaSub B q := by
  by_cases hab' : a = b
  · subst hab'
    rw [radE_mul_self hB (by simp)]
    exact (omegaSub B q).one_mem
  · rw [g12o_tv_mul_tv hB hab]
    have hz0 : a + b ≠ 0 := by
      intro h
      apply hab'
      calc a = a + (b + b) := by rw [g12_vadd_self, add_zero]
        _ = (a + b) + b := by rw [add_assoc]
        _ = b := by rw [h, zero_add]
    have hqz : q (a + b) = 0 := by rw [hq, hqa, hqb, hab]; decide
    have hza : B (a + b) a = 0 := by
      rw [map_add, LinearMap.add_apply, hB.1 a, hB.symm' b a, hab, add_zero]
    have := g12o_radE_mem_omegaSub hq hB hz0 hqz hza
    rwa [hqa] at this

theorem g12o_exists_nonsing_perp (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {a b : V} (hab : B a b = 1) : ∃ c, B a c = 0 ∧ B b c = 0 ∧ q c = 1 := by
  let f : V →ₗ[ZMod 2] ZMod 2 × ZMod 2 := (B a).prod (B b)
  have hmem : ∀ x, x ∈ LinearMap.ker f ↔ B a x = 0 ∧ B b x = 0 := fun x => by
    simp [f]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hax, hbx⟩ := (hmem x).1 hxk
  obtain ⟨y0, hy0⟩ := hB.exists_B_eq_one hx0
  have hba : B b a = 1 := by rw [hB.symm']; exact hab
  have hay : B a (y0 + B y0 b • a + B y0 a • b) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, hB.1 a, hab, mul_zero, mul_one, add_zero]
    rw [hB.symm' a y0]
    exact g12_add_self _
  have hby : B b (y0 + B y0 b • a + B y0 a • b) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, hB.1 b, hba, mul_zero, mul_one, add_zero]
    rw [hB.symm' b y0]
    exact g12_add_self _
  have hxa : B x a = 0 := by rw [hB.symm']; exact hax
  have hxb : B x b = 0 := by rw [hB.symm']; exact hbx
  have hxy : B x (y0 + B y0 b • a + B y0 a • b) = 1 := by
    simp only [map_add, map_smul, smul_eq_mul, hxa, hxb, mul_zero, add_zero]
    rw [hB.symm']
    exact hy0
  rcases g12_eq_zero_or_one (q x) with hqx | hqx
  · rcases g12_eq_zero_or_one (q (y0 + B y0 b • a + B y0 a • b)) with hqy | hqy
    · refine ⟨x + (y0 + B y0 b • a + B y0 a • b), ?_, ?_, ?_⟩
      · rw [map_add, hax, hay, add_zero]
      · rw [map_add, hbx, hby, add_zero]
      · rw [hq, hqx, hqy, hxy]
        decide
    · exact ⟨_, hay, hby, hqy⟩
  · exact ⟨x, hax, hbx, hqx⟩

theorem g12o_tv_mul_tv_mem (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {a b : V} (hqa : q a = 1) (hqb : q b = 1) : radE B a 0 1 * radE B b 0 1 ∈ omegaSub B q := by
  rcases g12_eq_zero_or_one (B a b) with hab | hab
  · exact g12o_tv_mul_tv_mem_of_perp hq hB hqa hqb hab
  · obtain ⟨c, hac, hbc, hqc⟩ := g12o_exists_nonsing_perp hq hB hd hab
    have hcb : B c b = 0 := by rw [hB.symm']; exact hbc
    have e : radE B a 0 1 * radE B b 0 1 =
        (radE B a 0 1 * radE B c 0 1) * (radE B c 0 1 * radE B b 0 1) := by
      rw [mul_assoc, ← mul_assoc (radE B c 0 1), radE_mul_self hB (by simp), one_mul]
    rw [e]
    exact (omegaSub B q).mul_mem (g12o_tv_mul_tv_mem_of_perp hq hB hqa hqc hac)
      (g12o_tv_mul_tv_mem_of_perp hq hB hqc hqb hcb)

end Fin

private noncomputable def g12oQuad : QuadraticForm (ZMod 2) V where
  toFun := q
  toFun_smul a x := by
    rw [g12o_q_smul hq, smul_eq_mul, g12o_mul_self]
  exists_companion' := ⟨B, hq⟩

private theorem g12oQuad_apply (x : V) : g12oQuad hq x = q x := rfl

private theorem polar_g12oQuad (x y : V) : QuadraticMap.polar (g12oQuad hq) x y = B x y := by
  rw [QuadraticMap.polar, g12oQuad_apply, g12oQuad_apply, g12oQuad_apply, hq]
  ring

private theorem polarBilin_g12oQuad : QuadraticMap.polarBilin (g12oQuad hq) = B := by
  ext x y
  exact polar_g12oQuad hq x y

private theorem orthogonalGroup_g12oQuad :
    TauCeti.QuadraticMap.orthogonalGroup (g12oQuad hq) = orthSub q := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact Iff.rfl

private theorem reflect_g12oQuad (hB : IsSymplectic B) (a : V) :
    CFSG.ClassicalGroups.Orthogonal.reflect (g12oQuad hq) a = 1 ∨
      (q a = 1 ∧ CFSG.ClassicalGroups.Orthogonal.reflect (g12oQuad hq) a = radE B a 0 1) := by
  rcases g12_eq_zero_or_one (q a) with h | h
  · left
    exact CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero h
  · right
    refine ⟨h, LinearEquiv.ext fun x => ?_⟩
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one h, radE_one_apply hB,
      polar_g12oQuad]

private theorem eichler_g12oQuad (hB : IsSymplectic B) {u w : V} (hu : q u = 0)
    (huw : B u w = 0) :
    CFSG.ClassicalGroups.Orthogonal.eichler (g12oQuad hq) u w = radE B u w (q w) := by
  have huw' : QuadraticMap.polar (g12oQuad hq) u w = 0 := by rw [polar_g12oQuad]; exact huw
  have hneg : ∀ y : V, -y = y := fun y => neg_eq_of_add_eq_zero_right (g12_vadd_self y)
  refine LinearEquiv.ext fun x => ?_
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu huw', radE_apply hB huw, polar_g12oQuad,
    polar_g12oQuad, g12oQuad_apply, sub_eq_add_neg, hneg]

variable [Finite V]

theorem g12o_orthSub_le_closure (hB : IsSymplectic B) (hd : 3 ≤ Module.finrank (ZMod 2) V) :
    orthSub q ≤ Subgroup.closure
      ({g | ∃ a, q a = 1 ∧ g = radE B a 0 1} ∪ (omegaSub B q : Set (GLV V))) := by
  classical
  have hQ : (QuadraticMap.polarBilin (g12oQuad hq)).Nondegenerate := by
    rw [polarBilin_g12oQuad hq]
    exact hB.nondegenerate
  have h2 : (2 : ZMod 2) = 0 := rfl
  obtain ⟨x₀, hx₀, hQx₀⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_ne_zero_map_eq_zero (Q := g12oQuad hq) hd
  obtain ⟨P₀, -⟩ := CFSG.ClassicalGroups.Orthogonal.exists_hypPair hQ hQx₀ hx₀
  obtain ⟨r, P, hP, hA⟩ := CFSG.ClassicalGroups.Orthogonal.exists_family_anisotropic hQ P₀
  have hr : 1 ≤ r := by
    by_contra hr0
    rw [show r = 0 by omega] at hA
    exact hx₀ (hA x₀ Submodule.mem_top hQx₀)
  have hgen := CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2
    hA (fun x hx hx0 y hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.exists_eq_smul_of_anisotropic hA hx hx0 hy hxy) hr
  rw [orthogonalGroup_g12oQuad hq] at hgen
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro g (⟨a, rfl⟩ | hg)
  · rcases reflect_g12oQuad hq hB a with h | ⟨ha, h⟩
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  · have hle : CFSG.ClassicalGroups.Orthogonal.elementaryGroup (g12oQuad hq) ≤ omegaSub B q := by
      refine CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_of_eichler_mem
        fun u w hu huw => ?_
      have huw' : B u w = 0 := by rwa [polar_g12oQuad] at huw
      by_cases hu0 : u = 0
      · rw [hu0, CFSG.ClassicalGroups.Orthogonal.eichler_zero_left]
        exact Subgroup.one_mem _
      · rw [eichler_g12oQuad hq hB hu huw']
        exact g12o_radE_mem_omegaSub hq hB hu0 hu huw'
    exact Subgroup.subset_closure (Or.inr (hle hg))

end Quad

section Main

variable [Finite V]

theorem orthSub_index_le_two (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {q : V → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + B x y) {Γ : Subgroup (GLV V)}
    (h1 : omegaSub B q ≤ Γ) (h2 : Γ ≤ orthSub q) : Γ = omegaSub B q ∨ Γ = orthSub q := by
  refine g12o_eq_or_eq_of_mul_mem (T := {g | ∃ a, q a = 1 ∧ g = radE B a 0 1})
    (fun g hg n hn => g12o_conj_mem_omegaSub hq hB hg hn) ?_ ?_
    (g12o_orthSub_le_closure hq hB (by omega)) h1 h2
  · rintro _ ⟨a, ha, rfl⟩
    exact g12o_tv_mem_orthSub hq hB ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact g12o_tv_mul_tv_mem hq hB hd ha hb

theorem g12_orth_conclusion (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {q : V → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + B x y)
    {Γ : Subgroup (GLV V)} (hΓq : Γ ≤ orthSub q) {v : V} (hv : IsStarVec B Γ v) (hqv : q v = 0)
    (horb : ∀ w, (∃ g ∈ Γ, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) :
    Γ = orthSub q ∨ Γ = omegaSub B q := by
  have h1 : omegaSub B q ≤ Γ :=
    g12o_omegaSub_le hq hB hΓq hv hqv fun w hw0 hqw => (horb w).2 ⟨hw0, hqw⟩
  rcases orthSub_index_le_two hB hd hq h1 hΓq with h | h
  · exact Or.inr h
  · exact Or.inl h

end Main

end NoInst

end CFSG.Quasithin.G11

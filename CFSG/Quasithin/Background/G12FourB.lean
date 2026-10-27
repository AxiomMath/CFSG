module

public import CFSG.Quasithin.Background.G12FourField
public import CFSG.Quasithin.Background.G12FourNorm
public import CFSG.Quasithin.Background.G12FourTransport

public section

namespace CFSG.Quasithin.G11

open Matrix

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

theorem g12f_q_smul {q : V → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + f x y) (c : ZMod 2)
    (y : V) : q (c • y) = c * q y := by
  have hq0 : q 0 = 0 := by
    have h := hq 0 0
    simp only [add_zero, map_zero] at h
    have h2 := g12_add_self (q 0)
    rw [← h] at h2
    exact h2
  rcases g12_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, hq0, zero_mul]
  · rw [one_smul, one_mul]

theorem g12f_radE_mem_orthSub (hf : IsSymplectic f) {q : V → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {w a : V} (hqw : q w = 0) (hwa : f w a = 0) :
    radE f w a (q a) ∈ orthSub q := by
  intro x
  have haw : f a w = 0 := by rw [hf.symm']; exact hwa
  rw [radE_apply hf hwa, hq, hq, g12f_q_smul hq, g12f_q_smul hq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hqw, haw,
    mul_zero, add_zero]
  generalize q x = t
  generalize f x w = c1
  generalize f x a = c2
  generalize q a = qa
  revert t c1 c2 qa
  decide

theorem g12f_tv_mem_orthSub (hf : IsSymplectic f) {q : V → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {x : V} (hqx : q x = 1) :
    radE f x 0 1 ∈ orthSub q := by
  intro z
  rw [radE_one_apply hf, hq, g12f_q_smul hq, hqx, map_smul, smul_eq_mul]
  generalize q z = t
  generalize f z x = c
  revert t c
  decide

theorem g12f_exists_nonsingular (hf : IsSymplectic f) {q : V → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {v : V} (hv : v ≠ 0) : ∃ x, q x = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ x, q x = 0 := fun x => by
    rcases g12_eq_zero_or_one (q x) with e | e
    · exact e
    · exact absurd e (h x)
  apply hv
  apply hf.2 v
  intro y
  have := hq v y
  rw [h0, h0, h0, zero_add, zero_add] at this
  exact this.symm

variable {K : Subgroup (GLV V)}

theorem g12f_exists_commK_rel [Finite V] (hf : IsSymplectic f) {h : GLV V}
    (hhK : ∀ k ∈ K, h⁻¹ * k * h ∈ K) (hfK : FormInv K f)
    (hne : ∃ x y, f (h x) (h y) ≠ f x y) :
    ∃ T : V →ₗ[ZMod 2] V, G12CommK K T ∧ T ≠ 0 ∧ T ≠ LinearMap.id ∧
      ∀ x y, f (T x) y = f (h.symm x) (h.symm y) := by
  let f' : LinearMap.BilinForm (ZMod 2) V :=
    f.compl₁₂ (h.symm : V →ₗ[ZMod 2] V) (h.symm : V →ₗ[ZMod 2] V)
  have hf'app : ∀ x y, f' x y = f (h.symm x) (h.symm y) := fun x y => rfl
  let T : V →ₗ[ZMod 2] V :=
    ((LinearMap.BilinForm.toDual f hf.nondegenerate).symm :
      Module.Dual (ZMod 2) V →ₗ[ZMod 2] V) ∘ₗ f'
  have hT : ∀ x y, f (T x) y = f' x y := fun x y => by
    have := LinearMap.BilinForm.toDual_def (B := f) hf.nondegenerate (m := T x) (n := y)
    rw [← this]
    show (LinearMap.BilinForm.toDual f hf.nondegenerate
      ((LinearMap.BilinForm.toDual f hf.nondegenerate).symm (f' x))) y = f' x y
    rw [LinearEquiv.apply_symm_apply]
  have hext : ∀ u w : V, (∀ y, f u y = f w y) → u = w := fun u w huw => by
    have h0 : u + w = 0 := by
      apply hf.2
      intro y
      rw [map_add, LinearMap.add_apply, huw y, g12_add_self]
    calc u = u + (w + w) := by rw [g12_vadd_self, add_zero]
      _ = (u + w) + w := by rw [add_assoc]
      _ = w := by rw [h0, zero_add]
  refine ⟨T, ?_, ?_, ?_, fun x y => (hT x y).trans (hf'app x y)⟩
  · intro k hk x
    apply hext
    intro y
    have hk' : h⁻¹ * k * h ∈ K := hhK k hk
    have e1 : f (k (T x)) y = f' x (k.symm y) := by
      have := hfK k hk (T x) (k.symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [this, hT]
    have e2 : f (T (k x)) y = f' (k x) y := hT _ _
    rw [e1, e2, hf'app, hf'app]
    have e3 : h.symm (k x) = (h⁻¹ * k * h) (h.symm x) := by
      show h⁻¹ (k x) = h⁻¹ (k (h (h⁻¹ x)))
      simp
    have e4 : h.symm (k.symm y) = (h⁻¹ * k * h).symm (h.symm y) := by
      rw [eq_comm, LinearEquiv.symm_apply_eq]
      show h.symm y = h.symm (k (h (h.symm (k.symm y))))
      simp
    rw [e3, e4]
    have := hfK _ hk' (h.symm x) ((h⁻¹ * k * h).symm (h.symm y))
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  · intro h0
    obtain ⟨x, y, hxy⟩ := hne
    apply hxy
    have hz : ∀ u w, f u w = 0 := fun u w => by
      have := hT (h u) (h w)
      rw [h0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, hf'app] at this
      simpa using this.symm
    rw [hz, hz]
  · intro h1
    obtain ⟨x, y, hxy⟩ := hne
    apply hxy
    have := hT (h x) (h y)
    rw [h1, LinearMap.id_apply, hf'app] at this
    simpa using this

section Main

variable [Finite V]

omit [Finite V] in
theorem g12f_le_normalizer {H : Subgroup (GLV V)} (hirr : IsIrr K ⊤)
    (hKH : ∀ g ∈ H, ∀ k ∈ K, g⁻¹ * k * g ∈ K) {T : V →ₗ[ZMod 2] V} (hTK : G12CommK K T)
    (hT0 : T ≠ 0) (hT1 : T ≠ LinearMap.id) (hT2 : ∀ x, T (T x) = T x + x)
    (hall : ∀ S : V →ₗ[ZMod 2] V, G12CommK K S → S = 0 ∨ S = 1 ∨ S = T ∨ S = T + 1)
    {ω : GLV V} (hω : ∀ x, ω x = T x) :
    H ≤ Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)) := by
  have hinj := hTK.injective hirr hT0
  have hω3 : ω * ω * ω = 1 := LinearEquiv.ext fun x => by
    show ω (ω (ω x)) = x
    rw [hω, hω, hω, hT2, hT2, add_comm (T x) x, add_assoc, g12_vadd_self, add_zero]
  have hω1 : ω ≠ 1 := fun h => hT1 (LinearMap.ext fun x => by
    rw [← hω, h]; rfl)
  intro g hg
  rw [g12f_mem_normalizer_zpowers_iff hω3 hω1]
  let S : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) ∘ₗ T ∘ₗ (g.symm : V →ₗ[ZMod 2] V)
  have hS : ∀ x, S x = g (T (g.symm x)) := fun _ => rfl
  have hSK : G12CommK K S := by
    intro k hk x
    rw [hS, hS]
    have hk' := hKH g hg k hk
    have e1 : g.symm (k x) = (g⁻¹ * k * g) (g.symm x) := by
      show g.symm (k x) = g.symm (k (g (g.symm x)))
      rw [LinearEquiv.apply_symm_apply]
    rw [e1, hTK _ hk']
    show g (g.symm (k (g (T (g.symm x))))) = _
    rw [LinearEquiv.apply_symm_apply]
  obtain ⟨x0, hx0⟩ : ∃ x : V, x ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0 (LinearMap.ext fun x => by rw [h x, map_zero]; rfl)
  have hS0 : S ≠ 0 := by
    intro h
    have := congrArg (fun F : V →ₗ[ZMod 2] V => F x0) h
    simp only [hS, LinearMap.zero_apply] at this
    have h2 : T (g.symm x0) = 0 := by
      have := congrArg g.symm this
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have h3 : g.symm x0 = 0 := hinj (h2.trans (map_zero T).symm)
    exact hx0 (by simpa using h3)
  have hS1 : S ≠ 1 := by
    intro h
    apply hT1
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun F : V →ₗ[ZMod 2] V => F (g x)) h
    simp only [hS, LinearEquiv.symm_apply_apply] at this
    have h2 := congrArg g.symm this
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.trans (by simp)
  rcases hall S hSK with h | h | h | h
  · exact absurd h hS0
  · exact absurd h hS1
  · left
    refine LinearEquiv.ext fun x => ?_
    show g (ω (g.symm x)) = ω x
    rw [hω, hω, ← hS, h]
  · right
    have hinv : ω⁻¹ = ω * ω := by rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hω3]
    rw [hinv]
    refine LinearEquiv.ext fun x => ?_
    show g (ω (g.symm x)) = ω (ω x)
    rw [hω, hω, hω, ← hS, h, hT2]
    rfl

theorem g12f_exists_isometry_om (hf : IsSymplectic f) (hd : Module.finrank (ZMod 2) V = 4)
    {T : V →ₗ[ZMod 2] V} (hSA : ∀ x y, f (T x) y = f x (T y)) (hAL : ∀ x, f (T x) x = 0)
    (hT2 : ∀ x, T (T x) = T x + x) {ω : GLV V} (hω : ∀ x, ω x = T x) {x0 : V} (hx0 : x0 ≠ 0) :
    ∃ φ : FourV ≃ₗ[ZMod 2] V, (∀ x y, f (φ x) (φ y) = fourB x y) ∧ fourConj φ ω = fourOm := by
  have hs := hf.symm'
  have hTx0 : T x0 ≠ 0 := by
    intro h
    have := hT2 x0
    rw [h, map_zero, zero_add] at this
    exact hx0 this.symm
  obtain ⟨u, hu1, hu2⟩ := hf.exists_B_eq_one_one hx0 hTx0
  have hva : f x0 (T x0 + x0) = 0 := by rw [map_add, hf.1 x0, add_zero, hs, hAL]
  have hvu : f x0 u = 1 := by rw [hs]; exact hu1
  have hTu : f (T x0) u = 1 := by rw [hs]; exact hu2
  have hvy : f x0 (T u + u) = 0 := by
    rw [map_add, ← hSA, hTu, hvu]; decide
  have hau : f (T x0 + x0) u = 0 := by
    rw [map_add, LinearMap.add_apply, hTu, hvu]; decide
  have hay : f (T x0 + x0) (T u + u) = 1 := by
    rw [map_add, ← hSA, hau, add_zero, map_add, hT2, add_comm (T x0) x0, add_assoc,
      g12_vadd_self, add_zero, hvu]
  have huy : f u (T u + u) = 0 := by rw [map_add, hf.1 u, add_zero, hs, hAL]
  obtain ⟨φ, hφ, h0, h1, h2, h3⟩ := g12f_exists_isometry hf hd hva hvu hvy hau hay huy
  refine ⟨φ, hφ, LinearEquiv.ext fun z => ?_⟩
  show φ.symm (ω (φ z)) = fourOm z
  rw [LinearEquiv.symm_apply_eq]
  have hO : fourOm (fourBasisVec 0) = fourBasisVec 0 + fourBasisVec 1 ∧ fourOm (fourBasisVec 1) = fourBasisVec 0 ∧ fourOm (fourBasisVec 2) = fourBasisVec 2 + fourBasisVec 3 ∧
      fourOm (fourBasisVec 3) = fourBasisVec 2 := by
    simp only [fourOm_apply]
    decide
  have hb : ∀ i, ω (φ (fourBasisVec i)) = φ (fourOm (fourBasisVec i)) := by
    intro i
    fin_cases i
    · show ω (φ (fourBasisVec 0)) = φ (fourOm (fourBasisVec 0))
      rw [hO.1, map_add, h0, h1, hω, ← add_assoc, add_comm x0, add_assoc, g12_vadd_self,
        add_zero]
    · show ω (φ (fourBasisVec 1)) = φ (fourOm (fourBasisVec 1))
      rw [hO.2.1, h0, h1, hω, map_add, hT2, add_assoc, add_comm x0, ← add_assoc, g12_vadd_self,
        zero_add]
    · show ω (φ (fourBasisVec 2)) = φ (fourOm (fourBasisVec 2))
      rw [hO.2.2.1, map_add, h2, h3, hω, ← add_assoc, add_comm u, add_assoc, g12_vadd_self,
        add_zero]
    · show ω (φ (fourBasisVec 3)) = φ (fourOm (fourBasisVec 3))
      rw [hO.2.2.2, h2, h3, hω, map_add, hT2, add_assoc, add_comm u, ← add_assoc, g12_vadd_self,
        zero_add]
  have hz : z = z 0 • fourBasisVec 0 + z 1 • fourBasisVec 1 + z 2 • fourBasisVec 2 + z 3 • fourBasisVec 3 := by
    funext i
    fin_cases i <;> simp [fourBasisVec]
  rw [hz]
  simp only [map_add, map_smul, hb]

variable {φ : FourV ≃ₗ[ZMod 2] V} {ω : GLV V}

omit [Finite V] in
theorem fourConj_mem_fourN_iff (hφω : fourConj φ ω = fourOm) {g : GLV V} :
    g ∈ Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)) ↔ fourConj φ g ∈ fourN := by
  have hω3 : ω * ω * ω = 1 := (fourConj φ).injective (by
    rw [map_mul, map_mul, hφω, fourOm_cube, map_one])
  have hω1 : ω ≠ 1 := fun h => fourOm_ne_one (by rw [← hφω, h, map_one])
  rw [g12f_mem_normalizer_zpowers_iff hω3 hω1, fourN,
    g12f_mem_normalizer_zpowers_iff fourOm_cube fourOm_ne_one, ← hφω, ← map_inv, ← map_mul,
    ← map_mul, ← map_inv, (fourConj φ).injective.eq_iff, (fourConj φ).injective.eq_iff]

omit [Finite V] in
theorem g12f_conjSub_eq_fourM0 (hf : IsSymplectic f) (hφ : ∀ x y, f (φ x) (φ y) = fourB x y)
    (hφω : fourConj φ ω = fourOm) {X : Subgroup (GLV V)} (hX : X ≤ spSub f)
    (hXN : X ≤ Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V))) {v : V} (hv0 : v ≠ 0)
    (hconcl : G121Concl f X v) : fourConjSub φ X = fourM0 := by
  have hXN0 : ∀ g ∈ X, fourConj φ g ∈ fourN := fun g hg => (fourConj_mem_fourN_iff hφω).1 (hXN hg)
  have hX0 : fourConjSub φ X ≤ fourM0 := by
    rintro _ ⟨g, hg, rfl⟩
    exact fourNorm_inf_sp_le (hXN0 g hg) (fourConj_mem_spSub hφ (hX hg))
  have hnot : ∀ w, w ≠ 0 → radE f w 0 1 ∉ X := by
    intro w hw hmem
    have := hXN0 _ hmem
    rw [fourConj_radE hφ hf (by simp) 1, map_zero] at this
    exact fourNorm_not_tv (fun h => hw (by simpa using h)) this
  rcases hconcl with h1 | ⟨q, hq, hXq, -⟩ | ⟨-, h3 | ⟨⟨e⟩, -⟩⟩
  · exact absurd (h1 ▸ radE_mem_spSub hf (by simp)) (hnot v hv0)
  · rcases hXq with hXq | hXq
    · obtain ⟨x, hx⟩ := g12f_exists_nonsingular hf hq hv0
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, ← zero_smul (ZMod 2) (0 : V), g12f_q_smul hq, zero_mul] at hx
        exact absurd hx (by decide)
      exact absurd (hXq ▸ g12f_tv_mem_orthSub hf hq hx) (hnot x hx0)
    · let q' : FourV → ZMod 2 := fun z => q (φ z)
      have hq' : ∀ x y, q' (x + y) = q' x + q' y + fourB x y := fun x y => by
        show q (φ (x + y)) = q (φ x) + q (φ y) + fourB x y
        rw [map_add, hq, hφ]
      obtain ⟨w, a, hw0, hqw, hwa, hn⟩ := fourNorm_not_omega hq'
      have hwa' : f (φ w) (φ a) = 0 := by rw [hφ]; exact hwa
      have hmem : radE f (φ w) (φ a) (q (φ a)) ∈ X := by
        rw [hXq]
        refine Subgroup.subset_closure ⟨φ w, fun h => hw0 (by simpa using h), hqw, ?_⟩
        exact radE_mem_QSub hf hwa' (g12f_radE_mem_orthSub hf hq hqw hwa')
      have := hXN0 _ hmem
      rw [fourConj_radE hφ hf hwa', LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply] at this
      exact (hn this).elim
  · exfalso
    have hxy : f (φ (fourBasisVec 3)) (φ (fourBasisVec 1)) = 1 := by rw [hφ]; decide
    have hmem : radE f (φ (fourBasisVec 3)) 0 1 * radE f (φ (fourBasisVec 1)) 0 1 ∈ X := by
      rw [h3, g12f_tv_mul_eq_commutator hf hxy]
      exact Subgroup.commutator_mem_commutator (g12f_tv_mem hf _) (g12f_tv_mem hf _)
    have := hXN0 _ hmem
    rw [map_mul, fourConj_radE hφ hf (by simp) 1, fourConj_radE hφ hf (by simp) 1, map_zero,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact fourNorm_not_tvProd this
  · have : Finite (GLV FourV) := Finite.of_injective (fun g : GLV FourV => (g : FourV → FourV))
      (fun a b h => LinearEquiv.ext (congrFun h))
    refine Subgroup.eq_of_le_of_card_ge hX0 ?_
    have hc : Nat.card ↥(fourConjSub φ X) = Nat.card ↥X :=
      (Nat.card_congr ((fourConj φ).subgroupMap X).toEquiv).symm
    rw [fourM0_card, hc, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

omit [Finite V] in
theorem g12f_eq_normalizer_of_conj (hφ : ∀ x y, f (φ x) (φ y) = fourB x y)
    (hφω : fourConj φ ω = fourOm) {H : Subgroup (GLV V)}
    (hHN : H ≤ Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)))
    (hM : fourM0 ≤ fourConjSub φ H) (hns : ¬ H ≤ spSub f) :
    H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)) := by
  have hH0N : fourConjSub φ H ≤ fourN := by
    rintro _ ⟨g, hg, rfl⟩
    exact (fourConj_mem_fourN_iff hφω).1 (hHN hg)
  have hωN : fourOm ∈ fourN := by
    rw [fourN, g12f_mem_normalizer_zpowers_iff fourOm_cube fourOm_ne_one]
    left
    group
  obtain ⟨h, hh, hns'⟩ : ∃ h ∈ H, h ∉ spSub f := by
    by_contra hc
    push Not at hc
    exact hns hc
  have h0H : fourConj φ h ∈ fourConjSub φ H := fourConj_mem_fourConjSub hh
  have h0N := hH0N h0H
  have h0s : fourConj φ h ∉ spSub fourB := fun hs => hns' (by
    have := fourConj_symm_mem_spSub hφ hs
    rwa [MulEquiv.symm_apply_apply] at this)
  obtain ⟨j, hj3, hjs⟩ := fourNorm_exists_pow_mem_sp h0N
  have hjM : fourConj φ h * fourOm ^ j ∈ fourM0 :=
    fourNorm_inf_sp_le (fourN.mul_mem h0N (fourN.pow_mem hωN j)) hjs
  have hpow : fourOm ^ j ∈ fourConjSub φ H := by
    have := (fourConjSub φ H).mul_mem ((fourConjSub φ H).inv_mem h0H) (hM hjM)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hω0 : fourOm ∈ fourConjSub φ H := by
    interval_cases j
    · exact absurd (by simpa using hjs) h0s
    · simpa using hpow
    · have h4 := (fourConjSub φ H).mul_mem hpow hpow
      have e : fourOm ^ 2 * fourOm ^ 2 = fourOm := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, pow_succ, pow_succ, pow_one,
          fourOm_cube, one_mul]
      rwa [e] at h4
  have hNH : fourN ≤ fourConjSub φ H := by
    intro n hn
    obtain ⟨i, -, his⟩ := fourNorm_exists_pow_mem_sp hn
    have h1 := hM (fourNorm_inf_sp_le (fourN.mul_mem hn (fourN.pow_mem hωN i)) his)
    have h2 := (fourConjSub φ H).mul_mem h1 ((fourConjSub φ H).inv_mem
      ((fourConjSub φ H).pow_mem hω0 i))
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  have heq : fourConjSub φ H = fourN := le_antisymm hH0N hNH
  ext g
  rw [fourConj_mem_fourN_iff hφω, ← heq, mem_fourConjSub, MulEquiv.symm_apply_apply]

end Main

theorem g12_part_four_fact : G1212PartFourFact := by
  intro V _ _ _ H K Q W v f hyp hf hKQ hW hconcl hd
  by_cases hH : H ≤ spSub f
  · exact Or.inl hH
  right
  have hd4 : 4 ≤ Module.finrank (ZMod 2) V := hd.ge
  have hKsp : K ≤ spSub f := le_trans le_sup_left hKQ
  have hQsp : Q ≤ spSub f := le_trans le_sup_right hKQ
  have hfK : FormInv K f := fun k hk x y => hKsp hk x y
  have hKH' : ∀ g ∈ H, ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun g hg k hk => by
    simpa using hyp.normal g⁻¹ (H.inv_mem hg) k hk
  obtain ⟨h, hh, hns⟩ : ∃ h ∈ H, h ∉ spSub f := by
    by_contra hc
    push Not at hc
    exact hH hc
  have hne : ∃ x y, f (h x) (h y) ≠ f x y := by
    by_contra hc
    push Not at hc
    exact hns hc
  obtain ⟨T, hTK, hT0, hT1, hTf⟩ := g12f_exists_commK_rel hf (hKH' h hh) hfK hne
  have hfix : ∀ S : V →ₗ[ZMod 2] V, G12CommK K S → (∀ y ∈ Q, ∀ x, S (y x) = y (S x)) →
      S ≠ 0 → S = LinearMap.id := fun S hSK hSQ hS0 =>
    g12_eq_id_of_commQ hf hd4 hyp.irr hQsp hyp.v_mem hyp.v_ne hyp.transvections hW hSK hSQ hS0
  have hcard := g12f_card_endK_le_four hyp.irr (fun y hy => hKH' y (hyp.q_le hy))
    (fun y hy => hyp.normal y (hyp.q_le hy)) hyp.q_sq hfix
  obtain ⟨hTT, hall⟩ := g12f_endK_eq_of_ne hyp.irr hcard hTK hT0 hT1
  have hT2 : ∀ x, T (T x) = T x + x := fun x => by
    have := congrArg (fun S : V →ₗ[ZMod 2] V => S x) hTT
    simpa using this
  have hinj := hTK.injective hyp.irr hT0
  let ω : GLV V := LinearEquiv.ofInjectiveEndo T hinj
  have hω : ∀ x, ω x = T x := fun x => by
    show LinearEquiv.ofInjectiveEndo T hinj x = T x
    rw [LinearEquiv.coe_ofInjectiveEndo]
  refine ⟨ω, fun x => ?_, ?_⟩
  · rw [hω, hω, hT2]
    calc T x + x + T x + x = (T x + T x) + (x + x) := by abel
      _ = 0 := by rw [g12_vadd_self, g12_vadd_self, add_zero]
  have hHN := g12f_le_normalizer hyp.irr hKH' hTK hT0 hT1 hT2 hall hω
  have hs := hf.symm'
  have hSA : ∀ x y, f (T x) y = f x (T y) := fun x y => by
    rw [hTf, hs (h.symm x), ← hTf, hs]
  have hAL : ∀ x, f (T x) x = 0 := fun x => by rw [hTf, hf.1]
  obtain ⟨φ, hφ, hφω⟩ := g12f_exists_isometry_om hf hd hSA hAL hT2 hω hyp.v_ne
  have hX0 := g12f_conjSub_eq_fourM0 hf hφ hφω hKQ (le_trans (sup_le hyp.le hyp.q_le) hHN)
    hyp.v_ne hconcl
  have hM : fourM0 ≤ fourConjSub φ H := by
    rw [← hX0]
    exact Subgroup.map_mono (sup_le hyp.le hyp.q_le)
  exact g12f_eq_normalizer_of_conj hφ hφω hHN hM hH

end NoInst

end CFSG.Quasithin.G11

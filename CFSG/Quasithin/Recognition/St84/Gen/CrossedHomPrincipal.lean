module

public import CFSG.GroupTheory.InternalSemidirectEquiv
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F112R.St84

variable {G G' : Type*} [Group G] [Group G']

abbrev CrossedHomPrincipalOn (Q Z R N : Subgroup G) (Z' R' : Subgroup G') (e : ↥R ≃* ↥R') : Prop :=
  ∀ δ : ↥R → ↥Q →* ↥Z', (∀ (r : ↥R) (v : ↥Q), (v : G) ∈ Z → δ r v = 1) →
    (∀ (r s : ↥R) (v w : ↥Q), (w : G) = (s : G) * v * (s : G)⁻¹ →
      ((δ (r * s) v : ↥Z') : G') = (δ r w : G') * ((e r : G') * (δ s v : G') * (e r : G')⁻¹)) →
    ∃ φ : ↥Q →* ↥Z', (∀ v : ↥Q, (v : G) ∈ Z → φ v = 1) ∧
      ∀ r : ↥R, (r : G) ∈ N → ∀ (v w : ↥Q), (w : G) = (r : G) * v * (r : G)⁻¹ →
        ((δ r v : ↥Z') : G') = (φ w : G') * ((e r : G') * (φ v : G') * (e r : G')⁻¹)⁻¹

abbrev CrossedHomPrincipal (Q Z R : Subgroup G) (Z' R' : Subgroup G') (e : ↥R ≃* ↥R') : Prop :=
  CrossedHomPrincipalOn Q Z R R Z' R' e

private def conjQ {Q R : Subgroup G}
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) : ↥R →* MulAut ↥Q :=
  CFSG.GroupTheory.conjHom Q R hRQ

private theorem conjQ_apply {Q R : Subgroup G}
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (r : ↥R) (u : ↥Q) :
    ((conjQ hRQ r) u : G) = (r : G) * (u : G) * (r : G)⁻¹ :=
  CFSG.GroupTheory.conjHom_apply hRQ r u

private theorem conjQ_symm_apply {Q R : Subgroup G}
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (r : ↥R) (u : ↥Q) :
    (((conjQ hRQ r).symm) u : G) = (r : G)⁻¹ * (u : G) * (r : G) := by
  rw [← MulAut.inv_def, ← map_inv (conjQ hRQ) r]
  simpa using conjQ_apply hRQ r⁻¹ u

private def conjZ {R : Subgroup G} {Z' R' : Subgroup G'}
    (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (e : ↥R ≃* ↥R') (r : ↥R) : ↥Z' →* ↥Z' :=
  { toFun := fun z => ⟨(e r : G') * (z : G') * (e r : G')⁻¹,
      hR'Z' (e r) (e r).2 (z : G') z.2⟩
    map_one' := by ext; simp
    map_mul' := by
      intro x y
      ext
      simp only [Subgroup.coe_mul]
      group }

theorem crossedHomPrincipalOn_of_odd {Q Z R N : Subgroup G} {Z' R' : Subgroup G'}
    (e : ↥R ≃* ↥R') (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z) (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a) (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hNR : N ≤ R) (hodd : Odd (Nat.card N)) :
    CrossedHomPrincipalOn Q Z R N Z' R' e := by
  classical
  intro δ hZδ hcoc
  haveI hZ'comm : IsMulCommutative ↥Z' :=
    ⟨⟨fun a b => Subtype.ext (hZ'c (a : G') a.2 (b : G') b.2)⟩⟩
  letI : CommGroup ↥Z' := IsMulCommutative.instCommGroup
  have hNne : Nat.card ↥N ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    omega
  letI : Finite ↥N := Nat.finite_of_card_ne_zero hNne
  letI : Fintype ↥N := Fintype.ofFinite ↥N
  let cj : ↥R →* MulAut ↥Q := conjQ hRQ
  let cr (r : ↥R) : ↥Z' →* ↥Z' := conjZ hR'Z' e r
  have hcj_val : ∀ (r : ↥R) (u : ↥Q),
      ((cj r) u : G) = (r : G) * (u : G) * (r : G)⁻¹ :=
    fun r u => conjQ_apply hRQ r u
  have hcj_symm_val : ∀ (r : ↥R) (u : ↥Q),
      (((cj r).symm) u : G) = (r : G)⁻¹ * (u : G) * (r : G) :=
    fun r u => conjQ_symm_apply hRQ r u
  let act (r : ↥R) : (↥Q →* ↥Z') →* (↥Q →* ↥Z') :=
    { toFun := fun f => (cr r).comp (f.comp (cj r).symm.toMonoidHom)
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro f g
        ext u
        simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul] }
  have hact_val : ∀ (r : ↥R) (f : ↥Q →* ↥Z') (u : ↥Q),
      (((act r) f) u : G') = (e r : G') * (f ((cj r).symm u) : G') * (e r : G')⁻¹ :=
    fun r f u => rfl
  have hact_mul : ∀ (r s : ↥R) (f : ↥Q →* ↥Z'),
      act r (act s f) = act (r * s) f := by
    intro r s f
    ext u
    have harg : ((cj s).symm ((cj r).symm u) : ↥Q) = (cj (r * s)).symm u := by
      apply Subtype.ext
      rw [hcj_symm_val s ((cj r).symm u), hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    simp only [hact_val]
    rw [harg, map_mul e]
    simp only [Subgroup.coe_mul]
    group
  let D (r : ↥R) : ↥Q →* ↥Z' := (δ r).comp (cj r).symm.toMonoidHom
  have hDcoc : ∀ (r s : ↥R), D (r * s) = D r * act r (D s) := by
    intro r s
    apply MonoidHom.ext
    intro u
    apply Subtype.ext
    have harg : ((cj s).symm ((cj r).symm u) : ↥Q) = (cj (r * s)).symm u := by
      apply Subtype.ext
      rw [hcj_symm_val s ((cj r).symm u), hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    have hw : (((cj r).symm u : ↥Q) : G) =
        (s : G) * (((cj (r * s)).symm u : ↥Q) : G) * (s : G)⁻¹ := by
      rw [hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    have hc := hcoc r s ((cj (r * s)).symm u) ((cj r).symm u) hw
    change ((δ (r * s) ((cj (r * s)).symm u) : ↥Z') : G') =
      ((δ r ((cj r).symm u) : ↥Z') : G') *
        ((e r : G') * (δ s ((cj s).symm ((cj r).symm u)) : ↥Z') * (e r : G')⁻¹)
    rw [harg]
    exact hc
  let DN (n : ↥N) : ↥Q →* ↥Z' := D ⟨n, hNR n.2⟩
  let φ : ↥Q →* ↥Z' := ∏ n : ↥N, DN n
  have hφ_triv : ∀ v : ↥Q, (v : G) ∈ Z → φ v = 1 := by
    intro v hv
    have hprodeval : φ v = ∏ n : ↥N, DN n v := by
      have h := map_prod (MonoidHom.eval v) DN Finset.univ
      rw [MonoidHom.eval_apply_apply] at h
      change (∏ n : ↥N, DN n) v = ∏ n : ↥N, DN n v
      exact h
    rw [hprodeval]
    apply Finset.prod_eq_one
    intro n _
    show DN n v = 1
    change δ ⟨n, hNR n.2⟩ ((cj ⟨n, hNR n.2⟩).symm v) = 1
    apply hZδ
    rw [hcj_symm_val]
    simpa using hRZ (⟨n, hNR n.2⟩ : ↥R)⁻¹
      (R.inv_mem (⟨n, hNR n.2⟩ : ↥R).2) (v : G) hv
  have hpow : ∀ r : ↥R, (D r) ^ Fintype.card ↥N = D r := by
    intro r
    apply MonoidHom.ext
    intro u
    rw [MonoidHom.pow_apply]
    have h2 : (D r u) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hZ'2 (D r u : G') (D r u).2
    obtain ⟨k, hk⟩ := hodd
    have hcard : Fintype.card ↥N = 2 * k + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hk
    rw [hcard, pow_succ,
      show (D r u) ^ (2 * k) = ((D r u) ^ 2) ^ k by rw [pow_mul],
      h2, one_pow, one_mul]
  have hD_r : ∀ (r : ↥R), (r : G) ∈ N → D r = φ * (act r φ)⁻¹ := by
    intro r hr
    let rN : ↥N := ⟨r, hr⟩
    have hreindex : (∏ n : ↥N, DN n) = ∏ n : ↥N, DN (rN * n) :=
      (Equiv.prod_comp (Equiv.mulLeft rN) DN).symm
    have hterm : ∀ n : ↥N, DN (rN * n) = D r * act r (DN n) := by
      intro n
      have hone : (r * ⟨n, hNR n.2⟩ : ↥R) = ⟨rN * n, hNR (rN * n).2⟩ :=
        Subtype.ext rfl
      have h := hDcoc r ⟨n, hNR n.2⟩
      rw [hone] at h
      simpa only [DN, Subgroup.coe_mul] using h
    have hprod : φ = ∏ n : ↥N, (D r * act r (DN n)) := by
      calc φ = (∏ n : ↥N, DN n) := rfl
        _ = ∏ n : ↥N, DN (rN * n) := hreindex
        _ = ∏ n : ↥N, (D r * act r (DN n)) := by
          apply Finset.prod_congr rfl
          intro n _
          exact hterm n
    have hsplit : (∏ n : ↥N, (D r * act r (DN n))) =
        (D r) ^ Fintype.card ↥N * act r φ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      congr 1
      exact (map_prod (act r) DN Finset.univ).symm
    have hEq : φ = D r * act r φ := by
      calc φ = ∏ n : ↥N, (D r * act r (DN n)) := hprod
        _ = (D r) ^ Fintype.card ↥N * act r φ := hsplit
        _ = D r * act r φ := by rw [hpow r]
    calc D r = (D r * act r φ) * (act r φ)⁻¹ := by group
      _ = φ * (act r φ)⁻¹ := by rw [← hEq]
  refine ⟨φ, hφ_triv, ?_⟩
  intro r hr v w hw
  have hD := hD_r r hr
  have hw' : w = (cj r) v := by
    apply Subtype.ext
    rw [hcj_val, hw]
  have hDval : D r ((cj r) v) = δ r v := by
    show δ r ((cj r).symm ((cj r) v)) = δ r v
    rw [MulEquiv.symm_apply_apply]
  have hact_eval : ((act r φ) ((cj r) v) : G') =
      (e r : G') * (φ v : G') * (e r : G')⁻¹ := by
    rw [hact_val, MulEquiv.symm_apply_apply]
  have hD_eval : ((D r) ((cj r) v) : G') =
      (φ w : G') * ((e r : G') * (φ v : G') * (e r : G')⁻¹)⁻¹ := by
    have h := congrArg (fun f : ↥Q →* ↥Z' => ((f ((cj r) v) : ↥Z') : G')) hD
    rw [h]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hact_eval, ← hw']
  rw [hDval] at hD_eval
  exact hD_eval

theorem crossedHomPrincipal_of_normal {Q Z R N : Subgroup G} {Z' R' : Subgroup G'}
    (e : ↥R ≃* ↥R') (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z) (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a)
    (hNR : N ≤ R) (hNnorm : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N)
    (hN : CrossedHomPrincipalOn Q Z R N Z' R' e)
    (hfix : ∀ φ : ↥Q →* ↥Z', (∀ v : ↥Q, (v : G) ∈ Z → φ v = 1) →
      (∀ n : ↥R, (n : G) ∈ N → ∀ (v w : ↥Q), (w : G) = (n : G) * v * (n : G)⁻¹ →
        (φ w : G') = (e n : G') * (φ v : G') * (e n : G')⁻¹) → φ = 1) :
    CrossedHomPrincipal Q Z R Z' R' e := by
  classical
  intro δ hZδ hcoc
  obtain ⟨φ₀, hφ₀Z, hφ₀N⟩ := hN δ hZδ hcoc
  haveI hZ'comm : IsMulCommutative ↥Z' :=
    ⟨⟨fun a b => Subtype.ext (hZ'c (a : G') a.2 (b : G') b.2)⟩⟩
  letI : CommGroup ↥Z' := IsMulCommutative.instCommGroup
  let cj : ↥R →* MulAut ↥Q := conjQ hRQ
  let cr (r : ↥R) : ↥Z' →* ↥Z' := conjZ hR'Z' e r
  have hcj_val : ∀ (r : ↥R) (u : ↥Q),
      ((cj r) u : G) = (r : G) * (u : G) * (r : G)⁻¹ :=
    fun r u => conjQ_apply hRQ r u
  have hcj_symm_val : ∀ (r : ↥R) (u : ↥Q),
      (((cj r).symm) u : G) = (r : G)⁻¹ * (u : G) * (r : G) :=
    fun r u => conjQ_symm_apply hRQ r u
  let act (r : ↥R) : (↥Q →* ↥Z') →* (↥Q →* ↥Z') :=
    { toFun := fun f => (cr r).comp (f.comp (cj r).symm.toMonoidHom)
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro f g
        ext u
        simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul] }
  have hact_val : ∀ (r : ↥R) (f : ↥Q →* ↥Z') (u : ↥Q),
      (((act r) f) u : G') = (e r : G') * (f ((cj r).symm u) : G') * (e r : G')⁻¹ :=
    fun r f u => rfl
  have hact_mul : ∀ (r s : ↥R) (f : ↥Q →* ↥Z'),
      act r (act s f) = act (r * s) f := by
    intro r s f
    ext u
    have harg : ((cj s).symm ((cj r).symm u) : ↥Q) = (cj (r * s)).symm u := by
      apply Subtype.ext
      rw [hcj_symm_val s ((cj r).symm u), hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    simp only [hact_val]
    rw [harg, map_mul e]
    simp only [Subgroup.coe_mul]
    group
  let D (r : ↥R) : ↥Q →* ↥Z' := (δ r).comp (cj r).symm.toMonoidHom
  have hDcoc : ∀ (r s : ↥R), D (r * s) = D r * act r (D s) := by
    intro r s
    apply MonoidHom.ext
    intro u
    apply Subtype.ext
    have harg : ((cj s).symm ((cj r).symm u) : ↥Q) = (cj (r * s)).symm u := by
      apply Subtype.ext
      rw [hcj_symm_val s ((cj r).symm u), hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    have hw : (((cj r).symm u : ↥Q) : G) =
        (s : G) * (((cj (r * s)).symm u : ↥Q) : G) * (s : G)⁻¹ := by
      rw [hcj_symm_val r u, hcj_symm_val (r * s) u]
      simp only [Subgroup.coe_mul]
      group
    have hc := hcoc r s ((cj (r * s)).symm u) ((cj r).symm u) hw
    change ((δ (r * s) ((cj (r * s)).symm u) : ↥Z') : G') =
      ((δ r ((cj r).symm u) : ↥Z') : G') *
        ((e r : G') * (δ s ((cj s).symm ((cj r).symm u)) : ↥Z') * (e r : G')⁻¹)
    rw [harg]
    exact hc
  let D' (r : ↥R) : ↥Q →* ↥Z' := D r * act r φ₀ * φ₀⁻¹
  have hD'coc : ∀ (r s : ↥R), D' (r * s) = D' r * act r (D' s) := by
    intro r s
    simp only [D']
    rw [hDcoc r s, ← hact_mul r s φ₀, map_mul (act r), map_mul (act r)]
    have hmap : (act r) (φ₀⁻¹) = ((act r) φ₀)⁻¹ := map_inv (act r) φ₀
    rw [hmap]
    symm
    calc D r * (act r) φ₀ * φ₀⁻¹ *
          ((act r) (D s) * (act r) ((act s) φ₀) * ((act r) φ₀)⁻¹)
        = D r * (act r) (D s) * (act r) ((act s) φ₀) * φ₀⁻¹ *
            ((act r) φ₀ * ((act r) φ₀)⁻¹) := by ac_rfl
      _ = D r * (act r) (D s) * (act r) ((act s) φ₀) * φ₀⁻¹ := by
            group
  have hD'_N : ∀ (n : ↥R), (n : G) ∈ N → D' n = 1 := by
    intro n hn
    have hDn : D n = φ₀ * (act n φ₀)⁻¹ := by
      apply MonoidHom.ext
      intro u
      apply Subtype.ext
      have hw : ((u : ↥Q) : G) = (n : G) * (((cj n).symm u : ↥Q) : G) * (n : G)⁻¹ := by
        rw [hcj_symm_val n u]
        group
      have hc := hφ₀N n hn ((cj n).symm u) u hw
      change ((δ n ((cj n).symm u) : ↥Z') : G') =
        (φ₀ u : G') * ((((act n) φ₀) u : ↥Z') : G')⁻¹
      rw [hact_val]
      exact hc
    rw [show D' n = D n * act n φ₀ * φ₀⁻¹ from rfl, hDn]
    group
  have hD'Z : ∀ (r : ↥R) (v : ↥Q), (v : G) ∈ Z → D' r v = 1 := by
    intro r v hv
    have hDv : D r v = 1 := by
      change δ r ((cj r).symm v) = 1
      apply hZδ
      rw [hcj_symm_val]
      simpa using hRZ (⟨r, r.2⟩ : ↥R)⁻¹ (R.inv_mem r.2) (v : G) hv
    have hactv : (act r φ₀) v = 1 := by
      apply Subtype.ext
      rw [hact_val]
      have hmem : (((cj r).symm v : ↥Q) : G) ∈ Z := by
        rw [hcj_symm_val]
        simpa using hRZ ((r : G)⁻¹) (R.inv_mem r.2) (v : G) hv
      rw [hφ₀Z ((cj r).symm v) hmem]
      simp
    have hφv : φ₀ v = 1 := hφ₀Z v hv
    simp only [D']
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hDv, hactv,
      hφv]
    group
  have hD'fix : ∀ (r : ↥R), (∀ n : ↥R, (n : G) ∈ N → ∀ (v w : ↥Q),
      (w : G) = (n : G) * v * (n : G)⁻¹ →
      ((D' r) w : G') = (e n : G') * ((D' r) v : G') * (e n : G')⁻¹) := by
    intro r n hn v w hw
    have hn' : (r⁻¹ * n * r : G) ∈ N := by
      simpa using hNnorm ((r : G)⁻¹) (R.inv_mem r.2) (n : G) hn
    let n' : ↥R := ⟨r⁻¹ * n * r, hNR hn'⟩
    have hn'N : (n' : G) ∈ N := hn'
    have hnr : n * r = r * n' := by
      apply Subtype.ext
      show (n : G) * (r : G) = (r : G) * ((n' : G))
      change (n : G) * (r : G) = (r : G) * ((r : G)⁻¹ * (n : G) * (r : G))
      group
    have hD'n : D' n = 1 := hD'_N n hn
    have hD'n' : D' n' = 1 := hD'_N n' hn'N
    have hact : act n (D' r) = D' r := by
      have h1 : D' (n * r) = act n (D' r) := by
        rw [hD'coc n r, hD'n, one_mul]
      have h2 : D' (n * r) = D' r := by
        rw [hnr, hD'coc r n', hD'n', map_one, mul_one]
      exact h1.symm.trans h2
    have hargw : (cj n).symm w = v := by
      apply Subtype.ext
      rw [hcj_symm_val, hw]
      group
    have h := congrArg (fun f : ↥Q →* ↥Z' => ((f w : ↥Z') : G')) hact
    rw [hact_val, hargw] at h
    exact h.symm
  have hD_r : ∀ r : ↥R, D r = φ₀ * (act r φ₀)⁻¹ := by
    intro r
    have h1 : D' r = 1 := hfix (D' r) (hD'Z r) (hD'fix r)
    have h2 : D r * act r φ₀ * φ₀⁻¹ = 1 := by
      rw [← h1]
    calc D r = (D r * act r φ₀ * φ₀⁻¹) * (act r φ₀ * φ₀⁻¹)⁻¹ := by group
      _ = 1 * (act r φ₀ * φ₀⁻¹)⁻¹ := by rw [h2]
      _ = φ₀ * (act r φ₀)⁻¹ := by group
  refine ⟨φ₀, hφ₀Z, ?_⟩
  intro r hr v w hw
  have hD := hD_r r
  have hw' : w = (cj r) v := by
    apply Subtype.ext
    rw [hcj_val, hw]
  have hDval : D r ((cj r) v) = δ r v := by
    show δ r ((cj r).symm ((cj r) v)) = δ r v
    rw [MulEquiv.symm_apply_apply]
  have hact_eval : ((act r φ₀) ((cj r) v) : G') =
      (e r : G') * (φ₀ v : G') * (e r : G')⁻¹ := by
    rw [hact_val, MulEquiv.symm_apply_apply]
  have hD_eval : ((D r) ((cj r) v) : G') =
      (φ₀ w : G') * ((e r : G') * (φ₀ v : G') * (e r : G')⁻¹)⁻¹ := by
    have h := congrArg (fun f : ↥Q →* ↥Z' => ((f ((cj r) v) : ↥Z') : G')) hD
    rw [h]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hact_eval, ← hw']
  rw [hDval] at hD_eval
  exact hD_eval

end CFSG.Quasithin.F112R.St84

end

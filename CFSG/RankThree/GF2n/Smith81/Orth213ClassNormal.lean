module

public import CFSG.RankThree.GF2n.Smith81.Orth213ClassE
public import CFSG.RankThree.GF2n.Smith81.Orth213ClassRoot
public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIBasic
public import CFSG.RankThree.GF2n.Smith81.LinStmt

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement Matrix

section LinAlg

variable {K ι : Type} [Field K] [CharP K 2] (qU : QuadraticForm K (ι → K))

theorem polar_self_of_charTwo (v : ι → K) : polar qU v v = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

theorem polar_range_unip {u w : ι → K} (hqu : qU u = 0) (huw : polar qU u w = 0) (β : K)
    (v : ι → K) :
    polar qU (-(β • eichler qU u w v)) (v - eichler qU u w v) =
      -(β * qU w * polar qU v u ^ 2) := by
  have hwu : polar qU w u = 0 := by rw [polar_comm, huw]
  have hvw : polar qU w v = polar qU v w := polar_comm qU w v
  have hvu : polar qU u v = polar qU v u := polar_comm qU u v
  rw [eichler_apply hqu huw v]
  simp only [polar_neg_left, polar_smul_left_eq, polar_smul_right_eq, polar_add_left,
    polar_add_right, polar_sub_left, polar_sub_right, polar_self_of_charTwo,
    polar_self_eq_zero hqu, hwu, huw, hvw, hvu, mul_zero, sub_zero, add_zero, zero_add]
  ring

omit [CharP K 2] in
theorem eichler_smul_self_eq_one {u : ι → K} (hqu : qU u = 0) (c : K) :
    eichler qU u (c • u) = 1 := by
  have h := eichler_add_smul_self hqu (0 : ι → K) c
  rw [zero_add, eichler_zero_right] at h
  exact h

omit [CharP K 2] in
theorem orthTensor_unip_apply (β : K) (E : (ι → K) → (ι → K)) (p : (ι → K) × (ι → K)) :
    orthTensor !![1, β; 0, 1] E p = (E p.1 + β • E p.2, E p.2) :=
  orthTensor_unipotent β E p

omit [CharP K 2] in
theorem eichler_apply_perp {u w : ι → K} (hqu : qU u = 0) (huw : polar qU u w = 0) {s : ι → K}
    (hs : polar qU s u = 0) : eichler qU u w s = s - polar qU s w • u := by
  rw [eichler_apply hqu huw s, hs, zero_smul, add_zero, mul_zero, add_zero]

end LinAlg

section Group

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem theta_zero_of (h4 : Orth212C4CondStatement) (h28 : Smith28OrthStatement)
    (hc : SmithOrthCfg M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    ∀ y ∈ Q, ⁅y, x⁆ ∈ Z → ⁅y, x⁆ = 1 := by
  intro y hy hyZ
  have h12 := smith_1_12 hs
  have hne : Q ⊓ QB X ≠ ⊥ := by
    obtain ⟨v, hv, hvQ, hvX⟩ := h28 G M Q Z B hc X x hs
    intro h
    have hm : v ∈ Q ⊓ QB X := ⟨hvQ, hvX⟩
    rw [h, Subgroup.mem_bot] at hm
    exact ne_one_of_isConj_Z hs.ne_one hv hm
  have hxz : x * ⁅y, x⁆ * x⁻¹ = ⁅y, x⁆ := hs.x_cent h12 _ hyZ
  have hconj : IsConj x (x * ⁅y, x⁆) := by
    refine isConj_iff.mpr ⟨y, ?_⟩
    have e : x * ⁅y, x⁆ = ⁅y, x⁆ * x := by
      rw [mul_inv_eq_iff_eq_mul] at hxz
      exact hxz
    rw [e]
    simp only [commutatorElement_def]
    group
  exact h4 G M Q Z B hc X x hs hne _ hyZ hconj

theorem normal_form_std (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) {A : Subgroup G} (hA : IsZConjugate Z A) (hAQ : A ≤ Q)
    (hAX : A ≤ QB X) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {u : C.ι → C.K} (hu0 : u ≠ 0)
    (hqu : C.qU u = 0) (hpa : C.φ (C.M₀.π a) = (u, 0)) :
    ∃ (β : C.K) (w : C.ι → C.K), polar C.qU u w = 0 ∧
      ActsAsTensor Q Z C.M₀ C.φ x !![1, β; 0, 1] ⇑(eichler C.qU u w) := by
  have H := hc.ctx.hyp
  have hAZ : A ≠ Z := (lin29_of_sit hs hA hAQ hAX).1
  have hcA : Ctx M Q Z A := ⟨H, hA, hAQ, hAZ⟩
  have hX' : IsZConjugate Z X := hs.conj
  have hXA : X ≤ QB A := (IsZConjugate.le_QB_iff H hA hX').mpr hAX
  have hxQA : x ∈ QB A := hXA hs.mem
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨g, o, hdet, hiso, hact⟩ := C.hA.act x hxL
  have hline := isLineGen_pi hcA C.hD haA ha1
  obtain ⟨-, hconv⟩ := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA A hA hAQ hAZ 1 0 u
    (Or.inl one_ne_zero) hu0 hqu ⟨a, haA, ha1, by simpa using hpa⟩
  have hkey : ∀ v ∈ Q ⊓ QB A, ∃ c : C.K, C.φ (C.M₀.π v) - orthTensor g o (C.φ (C.M₀.π v)) =
      c • ((u, 0) : (C.ι → C.K) × (C.ι → C.K)) := by
    intro v hv
    have hcommA : ⁅v, x⁆ ∈ A := IsZConjugate.comm_mem_QB H hA hv.2 hxQA
    obtain ⟨c, hc'⟩ := (hline _).mp (C.M₀.pi_mem_img hcommA (hAQ hcommA))
    refine ⟨c, ?_⟩
    rw [← OrthEps.phi_pi_commutator C hxQ hv.1 hact, hc', map_smul, hpa]
  have hfix : orthTensor g o (u, 0) = (u, 0) := by
    have hdx : x * a = a * x := hs.QB_comm_X hs.mem (hAX haA)
    have := OrthCaseI.fixed_of_commute hc C hs hact (hAQ haA) hdx.symm
    rwa [hpa] at this
  have hfix' : g 0 0 • o u = u ∧ g 1 0 • o u = 0 := by
    have h := Prod.ext_iff.mp hfix
    simpa [orthTensor] using h
  obtain ⟨c₁, hc₁⟩ : ∃ c : C.K, ((0 : C.ι → C.K), u) - orthTensor g o (0, u) =
      c • ((u, 0) : (C.ι → C.K) × (C.ι → C.K)) := by
    obtain ⟨v, hv, hφ⟩ := hconv 0 0 1 (by simp)
    have hφ' : C.φ (C.M₀.π v) = (0, u) := by simpa using hφ
    have := hkey v hv
    rwa [hφ'] at this
  have h11 : g 1 1 • o u = u := by
    have h := (Prod.ext_iff.mp hc₁).2
    simp only [orthTensor, map_zero, smul_zero, zero_add, Prod.snd_sub, Prod.smul_snd] at h
    exact (sub_eq_zero.mp h).symm
  have hou0 : o u ≠ 0 := by
    intro h
    rw [h, smul_zero] at hfix'
    exact hu0 hfix'.1.symm
  have g10 : g 1 0 = 0 := (smul_eq_zero.mp hfix'.2).resolve_right hou0
  have g00g11 : g 0 0 = g 1 1 := by
    have h : (g 0 0 - g 1 1) • o u = 0 := by rw [sub_smul, hfix'.1, h11, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hou0)
  have hdet' : g 0 0 * g 1 1 = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, g10] at h
    simpa using h
  have g00 : g 0 0 = 1 := by
    have h2 : g 0 0 ^ 2 = 1 ^ 2 := by
      rw [_root_.sq, one_pow]
      nth_rewrite 2 [g00g11]
      exact hdet'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  have hou : o u = u := by
    have := hfix'.1
    rwa [g00, one_smul] at this
  have hperp : ∀ s, polar C.qU s u = 0 → ∃ c : C.K, o s = s + c • u := by
    intro s hsu
    obtain ⟨v, hv, hφ⟩ := hconv s 0 0 hsu
    have hφ' : C.φ (C.M₀.π v) = (s, 0) := by simpa using hφ
    obtain ⟨c, hc'⟩ := hkey v hv
    rw [hφ'] at hc'
    have h := (Prod.ext_iff.mp hc').1
    simp only [orthTensor, map_zero, smul_zero, add_zero, Prod.fst_sub, Prod.smul_fst, g00,
      one_smul] at h
    refine ⟨-c, ?_⟩
    rw [neg_smul, ← sub_eq_add_neg, ← h]
    abel
  have hQ : (polarBilin C.qU).Nondegenerate := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have ho : (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  obtain ⟨w, hw, hoeq⟩ := exists_eichler_of_fix_perp hQ ho hqu hu0 hou hperp
  have hg : g = !![1, g 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g00, g10, ← g00g11]
  refine ⟨g 0 1, w, hw, ?_⟩
  rw [hg, hoeq] at hact
  exact hact

section Shapes

theorem beta_mul_q_eq_zero {X : Subgroup G} {x : G} (hθ : ∀ y ∈ Q, ⁅y, x⁆ ∈ Z → ⁅y, x⁆ = 1)
    (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x) {u w : C.ι → C.K}
    (hu0 : u ≠ 0) (hqu : C.qU u = 0) (huw : polar C.qU u w = 0) {β : C.K}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x !![1, β; 0, 1] ⇑(eichler C.qU u w)) :
    β * C.qU w = 0 := by
  have hQ : (polarBilin C.qU).Nondegenerate := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hu0
  have hvu : polar C.qU v u ≠ 0 := by rw [polar_comm]; exact hv
  set E : (C.ι → C.K) → (C.ι → C.K) := ⇑(eichler C.qU u w) with hE
  set p' : (C.ι → C.K) × (C.ι → C.K) := (0, v) with hp'
  obtain ⟨y, hyQ, hy⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ)
    (p' - orthTensor !![1, β; 0, 1] E p')
  obtain ⟨hxy, hγ⟩ := OrthCaseI.theta_of_range hc C hs hact hyQ hy
  have hyx : ⁅y, x⁆ ∈ Z := by
    rw [← commutatorElement_inv]
    exact Z.inv_mem hxy
  have h1 : ⁅x, y⁆ = 1 := by
    have := hθ y hyQ hyx
    rw [← commutatorElement_inv, this, inv_one]
  rw [h1, C.hD.reg.one, hy] at hγ
  have hp : orthTensor !![1, β; 0, 1] E p' = (β • E v, E v) := by
    rw [orthTensor_unip_apply]
    simp [hp', hE]
  rw [hp] at hγ
  simp only [hp', Prod.fst_sub, Prod.snd_sub] at hγ
  have h2 : polar C.qU (-(β • eichler C.qU u w v)) (v - eichler C.qU u w v) = 0 := by
    rw [← zero_sub (β • eichler C.qU u w v)]
    exact hγ.symm
  rw [polar_range_unip C.qU hqu huw] at h2
  have h3 : β * C.qU w * polar C.qU v u ^ 2 = 0 := neg_eq_zero.mp h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hvu

theorem exists_moved (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) :
    ∃ p : (C.ι → C.K) × (C.ι → C.K), orthTensor g o p ≠ p := by
  obtain ⟨q₀, hq₀Q, hq₀⟩ := OrthCaseI.exists_comm_ne hc C hs hact
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  refine ⟨C.φ (C.M₀.π q₀), fun h => hq₀ ?_⟩
  have := OrthEps.phi_pi_commutator C hxQ hq₀Q hact
  rw [h, sub_self] at this
  exact C.φ.map_eq_zero_iff.mp this

theorem not_shape_zero (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {X : Subgroup G}
    {x : G} (hs : Sit M Q Z X x) {u : C.ι → C.K} (hqu : C.qU u = 0) (c : C.K)
    (hact : ActsAsTensor Q Z C.M₀ C.φ x !![1, 0; 0, 1] ⇑(eichler C.qU u (c • u))) : False := by
  obtain ⟨p, hp⟩ := exists_moved hc C hs hact
  apply hp
  rw [orthTensor_unip_apply, eichler_smul_self_eq_one C.qU hqu c]
  simp

theorem imgSet_eq_Ish (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hθ : ∀ y ∈ Q, ⁅y, x⁆ ∈ Z → ⁅y, x⁆ = 1) {A : Subgroup G} (hA : IsZConjugate Z A)
    (hAQ : A ≤ Q) (hAX : A ≤ QB X) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {u : C.ι → C.K}
    (hu0 : u ≠ 0) (hqu : C.qU u = 0) (hpa : C.φ (C.M₀.π a) = (u, 0)) {β : C.K}
    {w : C.ι → C.K} (huw : polar C.qU u w = 0)
    (hact : ActsAsTensor Q Z C.M₀ C.φ x !![1, β; 0, 1] ⇑(eichler C.qU u w)) :
    imgSet C ((Q ⊓ QB A) ⊓ Subgroup.centralizer ({x} : Set G)) = Ish C.qU u w β := by
  have hAZ : A ≠ Z := (lin29_of_sit hs hA hAQ hAX).1
  obtain ⟨hforw, hconv⟩ := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA A hA hAQ
    hAZ 1 0 u (Or.inl one_ne_zero) hu0 hqu ⟨a, haA, ha1, by simpa using hpa⟩
  have hpu : polar C.qU u u = 0 := polar_self_eq_zero hqu
  have hfixiff : ∀ (s : C.ι → C.K) (t : C.K), polar C.qU s u = 0 →
      (orthTensor !![1, β; 0, 1] (⇑(eichler C.qU u w)) (s, t • u) = (s, t • u) ↔
        polar C.qU s w = β * t) := by
    intro s t hsu
    rw [orthTensor_unip_apply]
    simp only [map_smul, eichler_apply_self, eichler_apply_perp C.qU hqu huw hsu, Prod.mk.injEq,
      and_true]
    constructor
    · intro h
      have h' : (β * t - polar C.qU s w) • u = 0 := by
        have : s - polar C.qU s w • u + β • t • u = s := h
        calc (β * t - polar C.qU s w) • u = (s - polar C.qU s w • u + β • t • u) - s := by
              rw [sub_smul, mul_smul]; abel
          _ = 0 := by rw [this, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hu0)).symm
    · intro h
      show s - polar C.qU s w • u + β • t • u = s
      rw [h, smul_smul]
      abel
  ext ⟨s₀, p₂⟩
  constructor
  · rintro ⟨y, ⟨⟨hyQ, hyQA⟩, hyC⟩, hy⟩
    obtain ⟨w', s', t', hw', hφ⟩ := hforw y ⟨hyQ, hyQA⟩
    have hφ' : C.φ (C.M₀.π y) = (w' + s' • u, t' • u) := by simpa using hφ
    have hdx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hfix := OrthCaseI.fixed_of_commute hc C hs hact hyQ hdx
    have hsu : polar C.qU (w' + s' • u) u = 0 := by
      rw [polar_add_left, polar_smul_left_eq, hw', hpu]; simp
    obtain ⟨hs0, hp2⟩ := Prod.mk.inj (hφ'.symm.trans hy)
    subst hs0
    subst hp2
    rw [hφ'] at hfix
    exact ⟨hsu, t', rfl, (hfixiff _ _ hsu).mp hfix⟩
  · rintro ⟨hpu', t, hp2, hpw⟩
    have hp2' : p₂ = t • u := hp2
    subst hp2'
    obtain ⟨v, hv, hφ⟩ := hconv s₀ 0 t hpu'
    have hφ' : C.φ (C.M₀.π v) = (s₀, t • u) := by simpa using hφ
    refine ⟨v, ⟨hv, ?_⟩, hφ'⟩
    have hfix : orthTensor !![1, β; 0, 1] (⇑(eichler C.qU u w)) (C.φ (C.M₀.π v)) =
        C.φ (C.M₀.π v) := by
      rw [hφ']
      exact (hfixiff _ _ hpu').mpr hpw
    have hZ : ⁅v, x⁆ ∈ Z := (OrthCaseI.comm_mem_Z_iff hc C hs hact hv.1).mpr hfix
    have h1 := hθ v hv.1 hZ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp h1)

end Shapes

end Group

end CFSG.RankThree.GF2n.Smith81.OrthClass

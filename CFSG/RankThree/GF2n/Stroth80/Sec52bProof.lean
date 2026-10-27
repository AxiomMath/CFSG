module

public import CFSG.RankThree.GF2n.Stroth80.Sec52aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec52Orders
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec52b_conj_Vt_of_mem_Rt (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
  conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hg)

theorem sec52b_conj_Wt_of_mem_Rt (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    conjSubgroup g (Wt Q (Vt M (LB M Q B) B Z t)) = Wt Q (Vt M (LB M Q B) B Z t) := by
  rw [conjSubgroup_eq_self_iff]
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · exact conj_mem_Wt (hc.hyp.Q_normal.2 (hc.Rt_le_M t hg))
      (hc.Rt_normalizes_Vt hs.mem hg) hw
  · have h1 : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
      conj_mem_Wt (hc.hyp.Q_normal.2 (M.inv_mem (hc.Rt_le_M t hg)))
        (hc.Rt_normalizes_Vt hs.mem ((Rt M (LB M Q B) t).inv_mem hg)) hw
    have e : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w := by group
    rwa [e] at h1

theorem sec52b_card_QB_inf_Vt_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(QB (conjSubgroup g B) ⊓ Vt M (LB M Q B) B Z t) =
      Nat.card ↥(QB B ⊓ Vt M (LB M Q B) B Z t) := by
  have h : conjSubgroup g (QB B ⊓ Vt M (LB M Q B) B Z t) =
      QB (conjSubgroup g B) ⊓ Vt M (LB M Q B) B Z t := by
    rw [QB_conj, conjSubgroup_inf, sec52b_conj_Vt_of_mem_Rt hc hs hg]
  rw [← h, card_conjSubgroup]

theorem sec52b_card_QB_inf_Wt_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(QB (conjSubgroup g B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) := by
  have h : conjSubgroup g (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      QB (conjSubgroup g B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
    rw [QB_conj, conjSubgroup_inf, sec52b_conj_Wt_of_mem_Rt hc hs hg]
  rw [← h, card_conjSubgroup]

theorem sec52b_prod_conj {W X Y : Subgroup G} {g : G} (hW : conjSubgroup g W = W)
    (h : ∀ x ∈ W, ∃ a ∈ X, ∃ b ∈ Y, x = a * b) :
    ∀ x ∈ W, ∃ a ∈ conjSubgroup g X, ∃ b ∈ conjSubgroup g Y, x = a * b := by
  intro x hx
  have hx' : g⁻¹ * x * g ∈ W := by
    have hxW : x ∈ conjSubgroup g W := hW.symm ▸ hx
    exact mem_conjSubgroup.mp hxW
  obtain ⟨a, ha, b, hb, hab⟩ := h (g⁻¹ * x * g) hx'
  refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_⟩
  · rw [mem_conjSubgroup]
    convert ha using 2
    group
  · rw [mem_conjSubgroup]
    convert hb using 2
    group
  · calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (a * b) * g⁻¹ := by rw [hab]
      _ = g * a * g⁻¹ * (g * b * g⁻¹) := by group

theorem sec52b_mem_V_of_comm {V A₂ D : Subgroup G} {y : G}
    (hmap : conjSubgroup y A₂ = D) (hinf : A₂ ⊓ D = V) (hVA₂ : V ≤ A₂)
    {a : G} (ha : a ∈ A₂)
    (hcomm : ⁅y, a⁆ ∈ V) : a ∈ V := by
  have hyaD : y * a * y⁻¹ ∈ D := by
    rw [← hmap, mem_conjSubgroup]
    convert ha using 2
    group
  have hyaA : y * a * y⁻¹ ∈ A₂ := by
    have e : y * a * y⁻¹ = ⁅y, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A₂.mul_mem (hVA₂ hcomm) ha
  have hyaV : y * a * y⁻¹ ∈ V := by
    rw [← hinf]
    exact ⟨hyaA, hyaD⟩
  have e : a = ⁅y, a⁆⁻¹ * (y * a * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact V.mul_mem (V.inv_mem hcomm) hyaV

theorem sec52b_inf_of_prod {W V X Y : Subgroup G} {q n m : ℕ}
    (hq : 2 ≤ q) (hmn : m ≤ n) (hZV : Z ≤ V) (hXQ : X ≤ Q) (hYQ : Y ≤ Q) (hVQ : V ≤ Q)
    (hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z)
    (hVW : V ≤ W) (hXW : X ≤ W) (hYW : Y ≤ W)
    (hXV : Nat.card ↥(X ⊓ V) = q ^ (2 * m))
    (hYV : Nat.card ↥(Y ⊓ V) = q ^ (2 * m))
    (hXc : Nat.card X = q ^ n) (hYc : Nat.card Y = q ^ n)
    (hVc : Nat.card V = q ^ (2 * m + 1))
    (hWc : Nat.card W = q ^ (2 * n - 2 * m + 1))
    (hprod : ∀ x ∈ W, ∃ a ∈ X, ∃ b ∈ Y, x = a * b) :
    (X ⊔ V) ⊓ (Y ⊔ V) = V := by
  have hqpos : 0 < q := by omega
  have hnorm : ∀ {A B : Subgroup G}, A ≤ Q → Z ≤ B → B ≤ Q →
      A ≤ Subgroup.normalizer (B : Set G) := by
    intro A B hA hZB hB a ha
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => ?_, fun hb => ?_⟩
    · have hz : ⁅a, b⁆ ∈ Z := hcommQ a (hA ha) b (hB hb)
      rw [show a * b * a⁻¹ = ⁅a, b⁆ * b by
        simp only [commutatorElement_def]; group]
      exact B.mul_mem (hZB hz) hb
    · have hcQ : a * b * a⁻¹ ∈ Q := hB hb
      have hz : ⁅a⁻¹, a * b * a⁻¹⁆ ∈ Z := hcommQ a⁻¹ (Q.inv_mem (hA ha)) _ hcQ
      rw [show b = ⁅a⁻¹, a * b * a⁻¹⁆ * (a * b * a⁻¹) by
        simp only [commutatorElement_def]; group]
      exact B.mul_mem (hZB hz) hb
  have hXsup : Nat.card ↥(X ⊔ V) = q ^ (n + 1) := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := X) (K := V) (hnorm hXQ hZV hVQ)
    have h' : Nat.card ↥(X ⊔ V) * Nat.card ↥(X ⊓ V) =
        q ^ (n + 1) * Nat.card ↥(X ⊓ V) := by
      rw [h, hXc, hVc, hXV, ← pow_add, ← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hYsup : Nat.card ↥(Y ⊔ V) = q ^ (n + 1) := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Y) (K := V) (hnorm hYQ hZV hVQ)
    have h' : Nat.card ↥(Y ⊔ V) * Nat.card ↥(Y ⊓ V) =
        q ^ (n + 1) * Nat.card ↥(Y ⊓ V) := by
      rw [h, hYc, hVc, hYV, ← pow_add, ← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hjoin : (X ⊔ V) ⊔ (Y ⊔ V) = W := by
    refine le_antisymm (sup_le (sup_le hXW hVW) (sup_le hYW hVW)) ?_
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have ha' : a ∈ (X ⊔ V) ⊔ (Y ⊔ V) := Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)
    have hb' : b ∈ (X ⊔ V) ⊔ (Y ⊔ V) :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_left (show b ∈ Y from hb))
    exact ((X ⊔ V) ⊔ (Y ⊔ V)).mul_mem ha' hb'
  have hAB := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := X ⊔ V) (K := Y ⊔ V)
    (hnorm (sup_le hXQ hVQ) (le_trans hZV le_sup_right) (sup_le hYQ hVQ))
  have hinfc : Nat.card ↥((X ⊔ V) ⊓ (Y ⊔ V)) = q ^ (2 * m + 1) := by
    have h' : Nat.card ↥((X ⊔ V) ⊔ (Y ⊔ V)) *
        Nat.card ↥((X ⊔ V) ⊓ (Y ⊔ V)) = q ^ (2 * n - 2 * m + 1) * q ^ (2 * m + 1) := by
      rw [hAB, hXsup, hYsup, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hjoin, hWc] at h'
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hqpos (2 * n - 2 * m + 1)) h'
  have hVEq : V = (X ⊔ V) ⊓ (Y ⊔ V) :=
    Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right le_sup_right) (by rw [hinfc, hVc])
  exact hVEq.symm

theorem sec52b_fixed_of_map {W V L A₁ A₂ D : Subgroup G} {y : G}
    (hQV : W ≤ Subgroup.normalizer (V : Set G))
    (hA₁W : A₁ ≤ W) (hA₂W : A₂ ≤ W)
    (hfac : ∀ x ∈ W, ∃ a ∈ A₁, ∃ b ∈ A₂, x = a * b)
    (hinf₂ : A₂ ⊓ D = V)
    (hmap : conjSubgroup y A₂ = D)
    (hcommA₁ : ⁅L, A₁⁆ ≤ V) (hyL : y ∈ L)
    (hVA₁ : V ≤ A₁) (hVA₂ : V ≤ A₂) :
    ∀ x ∈ W, (∀ l ∈ L, ⁅l, x⁆ ∈ V) → x ∈ A₁ := by
  intro x hxW hfix
  obtain ⟨a, ha, b, hb, hab⟩ := hfac x hxW
  have haW : a ∈ W := hA₁W ha
  have hbW : b ∈ W := hA₂W hb
  have h1 : ⁅y, a⁆ ∈ V := Subgroup.commutator_le.mp hcommA₁ y hyL a ha
  have hx : ⁅y, x⁆ ∈ V := hfix y hyL
  have hbcomm : ⁅y, b⁆ ∈ V := by
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hab, e] at hx
    have h2 : a * ⁅y, b⁆ * a⁻¹ ∈ V := by
      have h2' : ⁅y, a⁆⁻¹ * (⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹)) ∈ V :=
        V.mul_mem (V.inv_mem h1) hx
      rwa [inv_mul_cancel_left] at h2'
    exact (Subgroup.mem_normalizer_iff.mp (hQV haW) _).mpr h2
  have hbV : b ∈ V :=
    sec52b_mem_V_of_comm hmap hinf₂ hVA₂ hb hbcomm
  rw [hab]
  exact A₁.mul_mem ha (hVA₁ hbV)

theorem sec52b_polar_eichler_ne_zero {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q' : QuadraticForm K V) {u w c : V}
    (hu : Q' u = 0) (hwu : polar Q' u w = 0) (hQw : Q' w ≠ 0)
    (hc : Q' c = 0) (hcu : polar Q' c u ≠ 0) :
    polar Q' c (eichler Q' u w c) ≠ 0 := by
  have hcalc : polar Q' c (eichler Q' u w c) = Q' w * (polar Q' c u) ^ 2 := by
    rw [eichler_apply hu hwu, polar_sub_right, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_self_eq_zero hc]
    ring_nf
    rw [CharTwo.neg_eq]
  rw [hcalc]
  exact mul_ne_zero hQw (pow_ne_zero 2 hcu)

theorem sec52b_GL_mulVec_inv {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : GL ι K) (x : ι → K) :
    (a : Matrix ι ι K) *ᵥ (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec]
  have h : (a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h, Matrix.one_mulVec]

theorem sec52b_c2_core {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K))
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X) (u : ι → K)
    (hQu : Q' u = 0) (hu0 : u ≠ 0)
    (hLB : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u)
    (hrMap : ∀ r' : ↥(Rt M (LB M Q B) t),
      ((conjSubgroup (r' : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        E.LomGL ((φ r' : Matrix ι ι K) *ᵥ u))
    (hrIff : ∀ r' : ↥(Rt M (LB M Q B) t),
      HypPlane Q Z B (conjSubgroup (r' : G) B) t ↔
        polar Q' u ((φ r' : Matrix ι ι K) *ᵥ u) ≠ 0)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∃ y ∈ LB M Q B, ∃ r' ∈ Rt M (LB M Q B) t, ∃ z ∈ LB M Q (conjSubgroup r B),
      HypPlane Q Z B (conjSubgroup r' B) t ∧
      conjSubgroup r (conjSubgroup r' B) = conjSubgroup y (conjSubgroup r B) ∧
      HypPlane Q Z B (conjSubgroup z B) t := by
  classical
  let R := Rt M (LB M Q B) t
  let rR : ↥R := ⟨r, hr⟩
  let Mg : GL ι K := φ rR
  let Mx : Matrix ι ι K := (Mg : Matrix ι ι K)
  let Minv : Matrix ι ι K := ((Mg⁻¹ : GL ι K) : Matrix ι ι K)
  let c : ι → K := Mx *ᵥ u
  have hcu' : polar Q' u c ≠ 0 := (hrIff rR).mp hplane
  have hcu : polar Q' c u ≠ 0 := by rwa [polar_comm] at hcu'
  have hc0 : c ≠ 0 := fun h0 => hcu' (by rw [h0, polar_zero_right])
  have hφX : Mg ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨rR, rfl⟩
  have hQuC : Q' c = 0 := by
    show Q' (Mx *ᵥ u) = 0
    rw [show Mx = (Mg : Matrix ι ι K) from rfl, E.quad_mulVec hφX, hQu]
  obtain ⟨A, hA, w, hwu, hQw, hAform⟩ := E.exists_eichler_LomGL hQ h3 hQu hu0
  have hAmem : A ∈ ((LB M Q B).subgroupOf R).map φ := by
    rw [hLB]
    exact hA
  obtain ⟨yR, hyR, hyφ⟩ := Subgroup.mem_map.mp hAmem
  have hyL : (yR : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hyR
  have hyRmem : (yR : G) ∈ R := yR.2
  have hAc : (A : Matrix ι ι K) *ᵥ c =
      c + polar Q' c u • w - (polar Q' c w + Q' w * polar Q' c u) • u := hAform c
  have hAcne : polar Q' c ((A : Matrix ι ι K) *ᵥ c) ≠ 0 := by
    rw [hAc]
    have hne := sec52b_polar_eichler_ne_zero Q' hQu hwu hQw hQuC hcu
    rwa [eichler_apply hQu hwu] at hne
  set r' : G := r⁻¹ * (yR : G) * r with hr'def
  have hr'R : r' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hr) hyRmem) hr
  have hr'φ : φ ⟨r', hr'R⟩ = (φ rR)⁻¹ * A * φ rR := by
    have hdecomp : (⟨r', hr'R⟩ : ↥R) = (⟨r, hr⟩ : ↥R)⁻¹ * yR * ⟨r, hr⟩ := by
      apply Subtype.ext
      show r' = r⁻¹ * (yR : G) * r
      rfl
    rw [hdecomp, map_mul, map_mul, map_inv, hyφ]
  have hmatrix : ((Mg⁻¹ * A * Mg : GL ι K) : Matrix ι ι K) =
      Minv * (A : Matrix ι ι K) * Mx := by
    simp only [Minv, Mx, Units.val_mul, Units.val_inv_eq_inv_val]
  have hvec' : (φ ⟨r', hr'R⟩ : Matrix ι ι K) *ᵥ u =
      (Minv * (A : Matrix ι ι K)) *ᵥ c := by
    rw [hr'φ, hmatrix]
    rw [← Matrix.mulVec_mulVec]
  have hinv : Mx *ᵥ ((Minv * (A : Matrix ι ι K)) *ᵥ c) = (A : Matrix ι ι K) *ᵥ c := by
    rw [← Matrix.mulVec_mulVec]
    exact sec52b_GL_mulVec_inv Mg ((A : Matrix ι ι K) *ᵥ c)
  have hpol' : polar Q' u ((φ ⟨r', hr'R⟩ : Matrix ι ι K) *ᵥ u) ≠ 0 := by
    rw [hvec']
    have hp := E.polar_mulVec hφX u ((Minv * (A : Matrix ι ι K)) *ᵥ c)
    rw [show (Mg : Matrix ι ι K) *ᵥ ((Minv * (A : Matrix ι ι K)) *ᵥ c) =
      (A : Matrix ι ι K) *ᵥ c from hinv] at hp
    intro h0
    exact hAcne (hp.trans h0)
  have hplane' : HypPlane Q Z B (conjSubgroup r' B) t := (hrIff ⟨r', hr'R⟩).mpr hpol'
  have hEq : conjSubgroup r (conjSubgroup r' B) =
      conjSubgroup (yR : G) (conjSubgroup r B) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 1
    show r * r' = (yR : G) * r
    simp only [r']
    group
  obtain ⟨A', hA', w', hwu', hQw', hA'form⟩ := E.exists_eichler_LomGL hQ h3 hQuC hc0
  have hLC : LB M Q (conjSubgroup r B) =
      conjSubgroup r (LB M Q B) := hc.LB_conj (hc.Rt_le_M t hr)
  have hLMap : ((LB M Q (conjSubgroup r B)).subgroupOf R).map φ = E.LomGL c := by
    rw [hLC]
    exact hrMap rR
  have hA'mem : A' ∈ ((LB M Q (conjSubgroup r B)).subgroupOf R).map φ := by
    rw [hLMap]
    exact hA'
  obtain ⟨zR, hzRsub, hzφ⟩ := Subgroup.mem_map.mp hA'mem
  have hzL : (zR : G) ∈ LB M Q (conjSubgroup r B) := Subgroup.mem_subgroupOf.mp hzRsub
  have hzR : (zR : G) ∈ R := zR.2
  have hA'c : (A' : Matrix ι ι K) *ᵥ u = eichler Q' c w' u := by
    rw [eichler_apply hQuC hwu']; exact hA'form u
  have hpolz : polar Q' u ((φ ⟨zR, hzR⟩ : Matrix ι ι K) *ᵥ u) ≠ 0 := by
    rw [hzφ, hA'c]
    exact sec52b_polar_eichler_ne_zero Q' hQuC hwu' hQw' hQu hcu'
  exact ⟨(yR : G), hyL, r', hr'R, (zR : G), hzL, hplane', hEq,
    (hrIff ⟨zR, hzR⟩).mpr hpolz⟩

theorem sec52b_hC2 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    ∀ (G : Type) [Group G] [Finite G]
      (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → OmegaNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∃ y ∈ LB M Q B, ∃ r' ∈ Rt M (LB M Q B) t, ∃ z ∈ LB M Q (conjSubgroup r B),
          HypPlane Q Z B (conjSubgroup r' B) t ∧
          conjSubgroup r (conjSubgroup r' B) = conjSubgroup y (conjSubgroup r B) ∧
          HypPlane Q Z B (conjSubgroup z B) t := by
  intro G _ _ M Q Z B hc n t hs hom r hr hplane
  obtain ⟨K, fK, finK, hK, hplus | hminus⟩ := hom
  · obtain ⟨m, hm, hnat⟩ := hplus
    letI := fK
    letI := finK
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    have hact' := hact
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hnat' : NaturalRep (ι := Fin m ⊕ Fin m) K (StatedOmega (StatedQuadPlus m K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hφ, hker, hact'⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hQ := nondegenerate_polarBilin_quadPlus m K
    have hX := addCommutantScalar_statedOmegaPlus (K := K) (m := m) hm
    have hsing := hc.omega_singular h34 hRoot hs (Or.inr ⟨K, fK, finK, hK,
      Or.inl ⟨m, hm, hnat'⟩⟩) hK (ElemMatrixIso.plus hm) hQ h3 hX φ hφ ψ hψ
    obtain ⟨u, hQu, hu0, -, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs
      (Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat'⟩⟩) hK (ElemMatrixIso.plus hm) hQ h3 hX
      φ hφ hker ψ hψ hsing
    exact sec52b_c2_core (ElemMatrixIso.plus hm) hQ h3 hc hs φ hφ u hQu hu0 hL
      (fun r' => (hr' r').2) (fun r' => (hr' r').1) hr hplane
  · obtain ⟨m, b, c, hm, hirr, hnat⟩ := hminus
    letI := fK
    letI := finK
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    have hact' := hact
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hnat' : NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hφ, hker, hact'⟩
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega
    have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
    have hX := addCommutantScalar_statedOmegaMinus (m := m) (b := b) (c := c) hm hirr
    have hsing := hc.omega_singular h34 hRoot hs (Or.inr ⟨K, fK, finK, hK,
      Or.inr ⟨m, b, c, hm, hirr, hnat'⟩⟩) hK (ElemMatrixIso.minus hm hirr) hQ h3 hX
      φ hφ ψ hψ
    obtain ⟨u, hQu, hu0, -, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs
      (Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat'⟩⟩) hK
      (ElemMatrixIso.minus hm hirr) hQ h3 hX φ hφ hker ψ hψ hsing
    exact sec52b_c2_core (ElemMatrixIso.minus hm hirr) hQ h3 hc hs φ hφ u hQu hu0 hL
      (fun r' => (hr' r').2) (fun r' => (hr' r').1) hr hplane

theorem stroth52b_of_c2 (h52a : Stroth52aStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement)
    (hC2 : ∀ (G : Type) [Group G] [Finite G]
      (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → OmegaNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∃ y ∈ LB M Q B, ∃ r' ∈ Rt M (LB M Q B) t, ∃ z ∈ LB M Q (conjSubgroup r B),
          HypPlane Q Z B (conjSubgroup r' B) t ∧
          conjSubgroup r (conjSubgroup r' B) = conjSubgroup y (conjSubgroup r B) ∧
          HypPlane Q Z B (conjSubgroup z B) t) :
    Stroth52bStatement := by
  intro G _ _ M Q Z B hc n t hs hom r hr hplane C L L' V W hC hL hL' hV hW
  subst hC
  subst hL
  subst hL'
  subst hV
  subst hW
  obtain ⟨y, hyL, r', hr'R, z, hzL, hplane', hEq, hplanez⟩ :=
    hC2 G M Q Z B hc n t hs hom r hr hplane
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set L : Subgroup G := LB M Q B with hLdef
  set C : Subgroup G := conjSubgroup r B with hCdef
  set L' : Subgroup G := LB M Q C with hL'def
  set A₁ : Subgroup G := (QB B ⊓ W) ⊔ V with hA₁def
  set A₂ : Subgroup G := (QB C ⊓ W) ⊔ V with hA₂def
  set D : Subgroup G := (QB (conjSubgroup y C) ⊓ W) ⊔ V with hDdef
  set D' : Subgroup G := (QB (conjSubgroup z B) ⊓ W) ⊔ V with hD'def
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hyR : y ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hyL
  have hzR : z ∈ Rt M (LB M Q B) t := by
    have hzL' : z ∈ conjSubgroup r (LB M Q B) := by
      rw [← hc.LB_conj hrM]
      exact hzL
    have hmem : r⁻¹ * z * r ∈ LB M Q B := mem_conjSubgroup.mp hzL'
    have h1 : z = r * (r⁻¹ * z * r) * r⁻¹ := by group
    rw [h1]
    exact (Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hr (le_Rt (M := M) (LB M Q B) ht hmem))
      ((Rt M (LB M Q B) t).inv_mem hr)
  have hq2 : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hVW : V ≤ W := sec7ctr_Vt_le_Wt h34 hc hs
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hc.hyp.toHyp79.comm_mem_V ha hb
  obtain ⟨m, hm, hVcard, hVQB⟩ := Ctx.card_Vt_inf_QB_of_omegaNat h34 hRoot hc hs hom
  have hmn : m ≤ n := by
    have hle : Nat.card V ≤ Nat.card Q := Subgroup.card_le_of_le hVQ
    rw [hVcard, hs.width] at hle
    have := (Nat.pow_le_pow_iff_right hq2).mp hle
    omega
  have hWcard : Nat.card ↥W = Nat.card Z ^ (2 * n - 2 * m + 1) := by
    have hWmul := hc.card_Wt_mul_card_Vt t
    rw [hVcard, hs.width] at hWmul
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := Z)) (2 * m + 1)) ?_
    calc Nat.card ↥W * Nat.card Z ^ (2 * m + 1)
        = Nat.card Z ^ (2 * n + 2) := hWmul
      _ = Nat.card Z ^ (2 * n - 2 * m + 1) * Nat.card Z ^ (2 * m + 1) := by
          rw [← pow_add]; congr 1; omega
  have hX_Bc : Nat.card ↥(QB B ⊓ W) = Nat.card Z ^ n :=
    card_QB_inf_Wt h34 hRoot hc hs hom
  have hX_Cc : Nat.card ↥(QB C ⊓ W) = Nat.card Z ^ n := by
    rw [show QB C ⊓ W = QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) from rfl,
      sec52b_card_QB_inf_Wt_conj hc hs hr]
    exact hX_Bc
  have hXV_B' : Nat.card ↥(QB B ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [inf_comm]
    exact hVQB
  have hXV_C' : Nat.card ↥(QB C ⊓ V) = Nat.card Z ^ (2 * m) := by
    have h' : Nat.card ↥(QB B ⊓ Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m) := by
      rw [inf_comm]
      exact hVQB
    have h := (sec52b_card_QB_inf_Vt_conj hc hs hr).trans h'
    simpa only [hCdef, hVdef] using h
  have hXV_B : Nat.card ↥((QB B ⊓ W) ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [show QB B ⊓ W ⊓ V = QB B ⊓ V by
      rw [inf_assoc, inf_of_le_right hVW]]
    exact hXV_B'
  have hXV_C : Nat.card ↥((QB C ⊓ W) ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [show QB C ⊓ W ⊓ V = QB C ⊓ V by
      rw [inf_assoc, inf_of_le_right hVW]]
    exact hXV_C'
  have hWconj : conjSubgroup r W = W := sec52b_conj_Wt_of_mem_Rt hc hs hr
  have hprod_BC : ∀ x ∈ W, ∃ a ∈ QB B ⊓ W, ∃ b ∈ QB C ⊓ W, x = a * b := by
    have h := (h52a G M Q Z B hc n t hs hom r hr hplane (conjSubgroup r B) (hc.CN t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl).1
    simpa only [hWdef, hVdef, hCdef] using h
  have hprod_r' : ∀ x ∈ W, ∃ a ∈ QB B ⊓ W, ∃ b ∈ QB (conjSubgroup r' B) ⊓ W, x = a * b := by
    have h := (h52a G M Q Z B hc n t hs hom r' hr'R hplane' (conjSubgroup r' B) (hc.CN t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl).1
    simpa only [hWdef, hVdef] using h
  have hprod_Cy : ∀ x ∈ W, ∃ a ∈ QB C ⊓ W, ∃ b ∈ QB (conjSubgroup y C) ⊓ W, x = a * b := by
    have h := sec52b_prod_conj (W := W) (X := QB B ⊓ W)
      (Y := QB (conjSubgroup r' B) ⊓ W) (g := r) hWconj hprod_r'
    have h1 : conjSubgroup r (QB B ⊓ W) = QB C ⊓ W := by
      rw [hCdef, QB_conj, conjSubgroup_inf, hWconj]
    have h2 : conjSubgroup r (QB (conjSubgroup r' B) ⊓ W) =
        QB (conjSubgroup y C) ⊓ W := by
      rw [conjSubgroup_inf, hWconj, ← QB_conj, hEq]
    rw [h1, h2] at h
    exact h
  have hprod_z : ∀ x ∈ W, ∃ a ∈ QB B ⊓ W, ∃ b ∈ QB (conjSubgroup z B) ⊓ W, x = a * b := by
    have h := (h52a G M Q Z B hc n t hs hom z hzR hplanez (conjSubgroup z B) (hc.CN t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl).1
    simpa only [hWdef, hVdef] using h
  have hX'_r' : Nat.card ↥(QB (conjSubgroup r' B) ⊓ W) = Nat.card Z ^ n := by
    rw [sec52b_card_QB_inf_Wt_conj hc hs hr'R]
    exact hX_Bc
  have hX'_y : Nat.card ↥(QB (conjSubgroup y C) ⊓ W) = Nat.card Z ^ n := by
    have hyR : y ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hyL
    have hWy : conjSubgroup y W = W := sec52b_conj_Wt_of_mem_Rt hc hs hyR
    have heq : QB (conjSubgroup y C) ⊓ W = conjSubgroup y (QB C ⊓ W) := by
      rw [QB_conj, conjSubgroup_inf, hWy]
    rw [heq, card_conjSubgroup, hX_Cc]
  have hX'_z : Nat.card ↥(QB (conjSubgroup z B) ⊓ W) = Nat.card Z ^ n := by
    rw [sec52b_card_QB_inf_Wt_conj hc hs hzR]
    exact hX_Bc
  have hXV_r' : Nat.card ↥((QB (conjSubgroup r' B) ⊓ W) ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [show QB (conjSubgroup r' B) ⊓ W ⊓ V = QB (conjSubgroup r' B) ⊓ V by
      rw [inf_assoc, inf_of_le_right hVW]]
    rw [sec52b_card_QB_inf_Vt_conj hc hs hr'R]
    exact hXV_B'
  have hXV_y : Nat.card ↥((QB (conjSubgroup y C) ⊓ W) ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [show QB (conjSubgroup y C) ⊓ W ⊓ V = QB (conjSubgroup y C) ⊓ V by
      rw [inf_assoc, inf_of_le_right hVW]]
    have hyR : y ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hyL
    have heq : QB (conjSubgroup y C) ⊓ V = conjSubgroup y (QB C ⊓ V) := by
      rw [QB_conj, conjSubgroup_inf, sec52b_conj_Vt_of_mem_Rt hc hs hyR]
    rw [heq, card_conjSubgroup]
    exact hXV_C'
  have hXV_z : Nat.card ↥((QB (conjSubgroup z B) ⊓ W) ⊓ V) = Nat.card Z ^ (2 * m) := by
    rw [show QB (conjSubgroup z B) ⊓ W ⊓ V = QB (conjSubgroup z B) ⊓ V by
      rw [inf_assoc, inf_of_le_right hVW]]
    rw [sec52b_card_QB_inf_Vt_conj hc hs hzR]
    exact hXV_B'
  have hinf : A₁ ⊓ A₂ = V := by
    rw [hA₁def, hA₂def]
    exact sec52b_inf_of_prod (W := W) (V := V) (X := QB B ⊓ W) (Y := QB C ⊓ W)
      (q := Nat.card Z) (n := n) (m := m) (hq := hq2) (hmn := hmn) (hZV := hZV)
      (hXQ := inf_le_right.trans hWQ) (hYQ := inf_le_right.trans hWQ)
      (hVQ := hVQ) (hcommQ := hcommQ)
      (hVW := hVW) (hXW := inf_le_right) (hYW := inf_le_right) (hXV := hXV_B)
      (hYV := hXV_C) (hXc := hX_Bc) (hYc := hX_Cc) (hVc := hVcard)
      (hWc := hWcard) (hprod := hprod_BC)
  have hinfD : A₂ ⊓ D = V := by
    rw [hA₂def, hDdef]
    exact sec52b_inf_of_prod (W := W) (V := V) (X := QB C ⊓ W)
      (Y := QB (conjSubgroup y C) ⊓ W) (q := Nat.card Z) (n := n) (m := m)
      (hq := hq2) (hmn := hmn) (hZV := hZV) (hXQ := inf_le_right.trans hWQ)
      (hYQ := inf_le_right.trans hWQ) (hVQ := hVQ) (hcommQ := hcommQ) (hVW := hVW)
      (hXW := inf_le_right) (hYW := inf_le_right) (hXV := hXV_C) (hYV := hXV_y)
      (hXc := hX_Cc) (hYc := hX'_y) (hVc := hVcard) (hWc := hWcard)
      (hprod := hprod_Cy)
  have hinfD' : A₁ ⊓ D' = V := by
    rw [hA₁def, hD'def]
    exact sec52b_inf_of_prod (W := W) (V := V) (X := QB B ⊓ W)
      (Y := QB (conjSubgroup z B) ⊓ W) (q := Nat.card Z) (n := n) (m := m)
      (hq := hq2) (hmn := hmn) (hZV := hZV) (hXQ := inf_le_right.trans hWQ)
      (hYQ := inf_le_right.trans hWQ) (hVQ := hVQ) (hcommQ := hcommQ) (hVW := hVW)
      (hXW := inf_le_right) (hYW := inf_le_right) (hXV := hXV_B) (hYV := hXV_z)
      (hXc := hX_Bc) (hYc := hX'_z) (hVc := hVcard) (hWc := hWcard)
      (hprod := hprod_z)
  have hWVn : W ≤ Subgroup.normalizer (V : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer (V : Set G) hw.2
  have hA₁Q : A₁ ≤ Q := by
    rw [hA₁def]
    exact sup_le (inf_le_right.trans hWQ) hVQ
  have hA₂Q : A₂ ≤ Q := by
    rw [hA₂def]
    exact sup_le (inf_le_right.trans hWQ) hVQ
  have hcommA₁ : ⁅L, A₁⁆ ≤ V := by
    rw [hA₁def]
    refine Subgroup.commutator_le.mpr fun l hl x hx => ?_
    have hXnorm : QB B ⊓ W ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
      hWVn ha.2
    obtain ⟨a, ha, v, hv, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer hXnorm hx
    have hla : ⁅l, a⁆ ∈ V := by
      refine (sup_le hZV (hc.B_le_Vt ht)) ?_
      exact hc.comm_LB_inf_QB_mem_sup hl ⟨hWQ ha.2, ha.1⟩
    have hlv : ⁅l, v⁆ ∈ V := by
      have hLR : L ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
      have hv' : l * v * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (hLR hl)) v).mp hv
      rw [commutatorElement_def]
      exact V.mul_mem hv' (V.inv_mem hv)
    have hav : a * ⁅l, v⁆ * a⁻¹ ∈ V := by
      have hcomm : a * ⁅l, v⁆ = ⁅l, v⁆ * a :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha.2).2 (⁅l, v⁆) hlv).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hlv
    have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hla hav
  have hcommA₂ : ⁅L', A₂⁆ ≤ V := by
    have hcC : Ctx M Q Z C := hc.conj_of_mem hrM
    have hL'R : L' ≤ Rt M (LB M Q B) t := by
      rw [hL'def, hCdef, hc.LB_conj hrM]
      have hrN : r ∈ Subgroup.normalizer ((Rt M (LB M Q B) t) : Set G) :=
        Subgroup.le_normalizer hr
      have hconjRt : conjSubgroup r (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
        conjSubgroup_eq_self_iff.mpr hrN
      calc conjSubgroup r (LB M Q B) ≤ conjSubgroup r (Rt M (LB M Q B) t) :=
            Subgroup.map_mono (le_Rt (M := M) (LB M Q B) ht)
        _ = Rt M (LB M Q B) t := hconjRt
    rw [hA₂def]
    refine Subgroup.commutator_le.mpr fun l hl x hx => ?_
    have hXnorm : QB C ⊓ W ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
      hWVn ha.2
    obtain ⟨a, ha, v, hv, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer hXnorm hx
    have hCV : C ≤ V := by
      rw [hCdef]
      exact le_sup_left.trans (hc.conj_Rt_le_Vt hs.mem hr)
    have hla : ⁅l, a⁆ ∈ V := by
      exact (sup_le hZV hCV) (hcC.comm_LB_inf_QB_mem_sup hl ⟨hWQ ha.2, ha.1⟩)
    have hlv : ⁅l, v⁆ ∈ V := by
      have hv' : l * v * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (hL'R hl)) v).mp hv
      rw [commutatorElement_def]
      exact V.mul_mem hv' (V.inv_mem hv)
    have hav : a * ⁅l, v⁆ * a⁻¹ ∈ V := by
      have hcomm : a * ⁅l, v⁆ = ⁅l, v⁆ * a :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha.2).2 (⁅l, v⁆) hlv).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hlv
    have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hla hav
  have hfacBC : ∀ x ∈ W, ∃ a ∈ A₁, ∃ b ∈ A₂, x = a * b := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod_BC x hx
    exact ⟨a, by rw [hA₁def]; exact Subgroup.mem_sup_left ha,
      b, by rw [hA₂def]; exact Subgroup.mem_sup_left hb, rfl⟩
  have hmapY : conjSubgroup y A₂ = D := by
    rw [hA₂def, hDdef, conjSubgroup_sup', conjSubgroup_inf,
      sec52b_conj_Wt_of_mem_Rt hc hs hyR, sec52b_conj_Vt_of_mem_Rt hc hs hyR, hCdef,
      ← QB_conj]
  have hfixedB : ∀ x ∈ W, (∀ l ∈ L, ⁅l, x⁆ ∈ V) → x ∈ A₁ :=
    sec52b_fixed_of_map (W := W) (V := V) (L := L) (A₁ := A₁) (A₂ := A₂) (D := D)
      (y := y) hWVn (by rw [hA₁def]; exact sup_le inf_le_right hVW)
      (by rw [hA₂def]; exact sup_le inf_le_right hVW) hfacBC hinfD hmapY hcommA₁ hyL
      (by rw [hA₁def]; exact le_sup_right) (by rw [hA₂def]; exact le_sup_right)
  have hfacSwap : ∀ x ∈ W, ∃ a ∈ A₂, ∃ b ∈ A₁, x = a * b := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hfacBC x hx
    refine ⟨b, hb, b⁻¹ * a * b, ?_, by group⟩
    have hz : ⁅b⁻¹, a⁆ ∈ Z := hcommQ b⁻¹ (Q.inv_mem (hA₂Q hb)) a (hA₁Q ha)
    have e : b⁻¹ * a * b = ⁅b⁻¹, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A₁.mul_mem ((by rw [hA₁def]; exact Subgroup.mem_sup_right (hZV hz))) ha
  have hmapZ : conjSubgroup z A₁ = D' := by
    rw [hA₁def, hD'def, conjSubgroup_sup', conjSubgroup_inf,
      sec52b_conj_Wt_of_mem_Rt hc hs hzR, sec52b_conj_Vt_of_mem_Rt hc hs hzR,
      ← QB_conj]
  have hfixedC : ∀ x ∈ W, (∀ l ∈ L', ⁅l, x⁆ ∈ V) → x ∈ A₂ :=
    sec52b_fixed_of_map (W := W) (V := V) (L := L') (A₁ := A₂) (A₂ := A₁) (D := D')
      (y := z) hWVn (by rw [hA₂def]; exact sup_le inf_le_right hVW)
      (by rw [hA₁def]; exact sup_le inf_le_right hVW) hfacSwap hinfD' hmapZ hcommA₂ hzL
      (by rw [hA₂def]; exact le_sup_right) (by rw [hA₁def]; exact le_sup_right)
  refine ⟨?_, ?_, ?_, ?_, ?_, hinf, ?_, ?_, ?_, ?_⟩
  · rw [hA₁def]; exact le_sup_right
  · rw [hA₁def]; exact sup_le inf_le_right hVW
  · rw [hA₂def]; exact le_sup_right
  · rw [hA₂def]; exact sup_le inf_le_right hVW
  · refine le_antisymm (sup_le (by rw [hA₁def]; exact sup_le inf_le_right hVW)
      (by rw [hA₂def]; exact sup_le inf_le_right hVW)) ?_
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hfacBC x hx
    exact Subgroup.mul_mem_sup ha hb
  · intro x hx y hy
    exact hZV (hcommQ x (hWQ hx) y (hWQ hy))
  · intro x hx
    exact hZV (hc.hyp.toHyp79.sq_mem_V (hWQ hx))
  · intro x hx
    constructor
    · intro hxA l hl
      exact Subgroup.commutator_le.mp hcommA₁ l hl x hxA
    · exact hfixedB x hx
  · intro x hx
    constructor
    · intro hxA l hl
      exact Subgroup.commutator_le.mp hcommA₂ l hl x hxA
    · exact hfixedC x hx

section Certs

theorem stroth52bStatement_holds : Stroth52bStatement :=
  stroth52b_of_c2 stroth52aStatement_holds stroth34Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional)
    (sec52b_hC2 stroth34Statement_unconditional
      (stroth310Root_of_34 stroth34Statement_unconditional))

end Certs

end CFSG.RankThree.GF2n.Stroth80

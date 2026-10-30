module

public import CFSG.RankThree.GF2n.Stroth80.Sec56Swap
public import CFSG.ClassicalGroups.Orthogonal.PerpValue
public import CFSG.RankThree.GF2n.Stroth80.Sec56SingularSpan
public import CFSG.ClassicalGroups.Orthogonal.SingularPairPerp
public import CFSG.RankThree.GF2n.Stroth80.Sec56Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem secVec_conj_eq {V : Subgroup G} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    {y : G} (hy : ∀ z ∈ Z, y * z * y⁻¹ = z) {v v' w w' : ↥V} (h : secVec ψ v = secVec ψ v')
    (hw : (w : G) = y * v * y⁻¹) (hw' : (w' : G) = y * v' * y⁻¹) : secVec ψ w = secVec ψ w' := by
  rw [secVec_eq_iff] at h ⊢
  have e : (w : G) * (w' : G)⁻¹ = y * ((v : G) * (v' : G)⁻¹) * y⁻¹ := by rw [hw, hw']; group
  rw [e, hy _ h]
  exact h

omit [Finite G] in
theorem secVec_conj_add {V : Subgroup G} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    {y : G} (hy : ∀ z ∈ Z, y * z * y⁻¹ = z) {v₁ v₂ v₃ w₁ w₂ w₃ : ↥V}
    (h : secVec ψ v₃ = secVec ψ v₁ + secVec ψ v₂) (hw₁ : (w₁ : G) = y * v₁ * y⁻¹)
    (hw₂ : (w₂ : G) = y * v₂ * y⁻¹) (hw₃ : (w₃ : G) = y * v₃ * y⁻¹) :
    secVec ψ w₃ = secVec ψ w₁ + secVec ψ w₂ := by
  rw [← secVec_mul] at h ⊢
  refine secVec_conj_eq ψ hy h hw₃ ?_
  simp only [Subgroup.coe_mul]
  rw [hw₁, hw₂]
  group

omit [Finite G] in
theorem conjSubgroup_eq_self_of_commute {E : Subgroup G} {y : G}
    (hy : ∀ e ∈ E, y * e = e * y) : conjSubgroup y E = E := by
  ext e
  rw [mem_conjSubgroup]
  constructor
  · intro he
    have e1 : e = y * (y⁻¹ * e * y) * y⁻¹ := by group
    rw [e1, hy _ he, mul_inv_cancel_right]
    exact he
  · intro he
    have e1 : y⁻¹ * e * y = e := by
      rw [mul_assoc, ← hy e he, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e1]
    exact he

theorem Ctx.secVec_conj_smul (hc : Ctx M Q Z B) {t : G} {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v)
    {y : G} (hyM : y ∈ M) (hyZ : y ∈ Subgroup.centralizer (Z : Set G))
    {v v' w w' : ↥(Vt M (LB M Q B) B Z t)} {c : K} (hvv' : secVec ψ v' = c • secVec ψ v)
    (hw : (w : G) = y * v * y⁻¹) (hw' : (w' : G) = y * v' * y⁻¹) :
    secVec ψ w' = c • secVec ψ w := by
  obtain ⟨T, hT, -, -⟩ := h.linear_of_centralizes hyM (fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hyZ z hz, mul_inv_cancel_right])
  have hVQ := hc.Vt_le_Q t
  obtain ⟨x, hxV, hxQ, hx⟩ :=
    hc.smul_mem_img_Vt h t (θ.symm c) (Tim79.QuadModel.pi_mem_img M₀ v.2 (hVQ v.2))
  have h1 : secVec ψ ⟨x, hxV⟩ = c • secVec ψ v := by
    rw [hθ (θ.symm c) v ⟨x, hxV⟩ hx, RingEquiv.apply_symm_apply]
  have h2 : M₀.π v' = θ.symm c • M₀.π v := by
    have h3 : (v' : G) * x⁻¹ ∈ Z := (secVec_eq_iff ψ v' ⟨x, hxV⟩).mp (hvv'.trans h1.symm)
    have e : (v' : G) = ((v' : G) * x⁻¹) * x := by group
    rw [e, M₀.π_mul _ (Q.mul_mem (hVQ v'.2) (Q.inv_mem hxQ)) _ hxQ,
      (M₀.π_ker _ (Q.mul_mem (hVQ v'.2) (Q.inv_mem hxQ))).mpr h3, zero_add, hx]
  have h4 : M₀.π w' = θ.symm c • M₀.π w := by
    rw [hw', hw, hT _ (hVQ v'.2), hT _ (hVQ v.2), h2, map_smul]
  rw [hθ (θ.symm c) w w' h4, RingEquiv.apply_symm_apply]

theorem Ctx.natSingularConj_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hnat : SpNat hc t ∨ OmegaNat hc t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) (h6 : 6 ≤ Module.finrank K (ι → K))
    (hX : AddCommutantScalar X)
    (hWitt : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = Q' y →
      ∃ A ∈ X, ((A : GL ι K) : Matrix ι ι K) *ᵥ x = y) :
    NatSingularConj hc t Q' X := by
  classical
  intro φ hφ hker _ ψ hψ g hg hgV b₁ hb₁
  by_contra hQb₁
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have h3 : 3 ≤ Module.finrank K (ι → K) := by omega
  have hsB := hc.omega_singular h34 hRoot hs hnat hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u, hQu, hu0, hBiff, hW, -, hroot⟩ :=
    hc.omega_points_core h34 hRoot hs hnat hK E hQ h3 hX φ hφ hker ψ hψ hsB
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  have hconjV : ∀ r : ↥(Rt M (LB M Q B) t), ∀ x ∈ Vt M (LB M Q B) B Z t,
      (r : G) * x * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := fun r x hx =>
    (Subgroup.mem_normalizer_iff.mp (hVR r.2) x).mp hx
  have hsupZ : ∀ {S : Subgroup G}, S ≤ Vt M (LB M Q B) B Z t →
      ∀ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ S ⊔ Z →
        ∃ s : ↥(Vt M (LB M Q B) B Z t), (s : G) ∈ S ∧ secVec ψ s = secVec ψ x := by
    intro S hSV x hx
    let T : Subgroup G :=
      { carrier := {y | ∃ hy : y ∈ Vt M (LB M Q B) B Z t, ∃ s : ↥(Vt M (LB M Q B) B Z t),
          (s : G) ∈ S ∧ secVec ψ s = secVec ψ ⟨y, hy⟩}
        mul_mem' := by
          rintro a b ⟨ha, s, hs, hsa⟩ ⟨hb, s', hs', hsb⟩
          refine ⟨(Vt M (LB M Q B) B Z t).mul_mem ha hb, s * s', S.mul_mem hs hs', ?_⟩
          rw [secVec_mul, hsa, hsb, ← secVec_mul]
          rfl
        one_mem' := ⟨(Vt M (LB M Q B) B Z t).one_mem, 1, S.one_mem, rfl⟩
        inv_mem' := by
          rintro a ⟨ha, s, hs, hsa⟩
          refine ⟨(Vt M (LB M Q B) B Z t).inv_mem ha, s⁻¹, S.inv_mem hs, ?_⟩
          rw [secVec_inv, hsa, ← secVec_inv]
          rfl }
    have hle : S ⊔ Z ≤ T := sup_le (fun s hs => ⟨hSV hs, ⟨s, hSV hs⟩, hs, rfl⟩)
      (fun z hz => ⟨hZV hz, 1, S.one_mem, by
        rw [(secVec_eq_zero_iff ψ (1 : ↥(Vt M (LB M Q B) B Z t))).mpr Z.one_mem,
          (secVec_eq_zero_iff ψ ⟨z, hZV hz⟩).mpr hz]⟩)
    obtain ⟨hy, s, hs, hsx⟩ := hle hx
    exact ⟨s, hs, hsx⟩
  have hC₀c : Ctx M Q Z (conjSubgroup g B) := hc.conj_of_mem hg
  have hC₀V : conjSubgroup g B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hgV
  obtain ⟨c₀, hc₀C, hc₀0, hC₀iff⟩ := hC₀c.exists_point_of_le hC₀V ψ hglob θ hθ
  have hQc₀ : Q' (secVec ψ c₀) ≠ 0 := by
    obtain ⟨l₁, hl₁⟩ := (hC₀iff (secVec ψ b₁)).mp ⟨b₁, hb₁, rfl⟩
    intro h0
    apply hQb₁
    rw [hl₁, map_smul_eq_sq, h0, mul_zero]
  obtain ⟨v, hvu, hQv⟩ := exists_perp_map_eq hQ h3 hu0 (Q' (secVec ψ c₀))
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hQc₀ (by rw [← hQv, QuadraticMap.map_zero])
  have hQv0 : Q' v ≠ 0 := by rw [hQv]; exact hQc₀
  obtain ⟨A, hA, hAv⟩ := hWitt _ _ hc₀0 hv0 hQv.symm
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A := by
    rw [← hφ] at hA
    exact MonoidHom.mem_range.mp hA
  have hrM : (r : G) ∈ M := hRM r.2
  set C := conjSubgroup (r : G) (conjSubgroup g B) with hCdef
  have hCc : Ctx M Q Z C := hC₀c.conj_of_mem hrM
  have hCV : C ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    have h1 := hC₀V (mem_conjSubgroup.mp hx)
    have e : x = (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ := by group
    rw [e]
    exact hconjV r _ h1
  have hCvec : ∀ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ C → ∃ l : K, secVec ψ x = l • v := by
    intro x hx
    have hx' := mem_conjSubgroup.mp hx
    obtain ⟨l, hl⟩ := (hC₀iff (secVec ψ ⟨(r : G)⁻¹ * x * r, hC₀V hx'⟩)).mp ⟨_, hx', rfl⟩
    have h1 := hψ r ⟨(r : G)⁻¹ * x * r, hC₀V hx'⟩ x (by simp only; group)
    change secVec ψ x = (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨(r : G)⁻¹ * x * r, hC₀V hx'⟩ at h1
    exact ⟨l, by rw [h1, hl, Matrix.mulVec_smul, hr, hAv]⟩
  obtain ⟨c₁, hc₁C, hc₁v⟩ : ∃ c₁ : ↥(Vt M (LB M Q B) B Z t), (c₁ : G) ∈ C ∧ secVec ψ c₁ = v := by
    refine ⟨⟨(r : G) * c₀ * (r : G)⁻¹, hconjV r _ c₀.2⟩, ?_, ?_⟩
    · show (r : G) * c₀ * (r : G)⁻¹ ∈ C
      rw [hCdef, mem_conjSubgroup]
      have e : (r : G)⁻¹ * ((r : G) * c₀ * (r : G)⁻¹) * r = c₀ := by group
      rw [e]
      exact hc₀C
    · have h1 := hψ r c₀ ⟨(r : G) * c₀ * (r : G)⁻¹, hconjV r _ c₀.2⟩ rfl
      change secVec ψ _ = (φ r : Matrix ι ι K) *ᵥ secVec ψ c₀ at h1
      rw [h1, hr, hAv]
  have hZQB : Z ≤ QB B := (Ctx.Z_le_QB hc).1
  have hCQB : C ≤ QB B := by
    intro x hx
    obtain ⟨l, hl⟩ := hCvec ⟨x, hCV hx⟩ hx
    obtain ⟨w, ⟨-, hwQB⟩, hw⟩ := (hW (secVec ψ ⟨x, hCV hx⟩)).mpr
      (by rw [hl, polar_smul_right_eq, hvu, mul_zero])
    exact mem_of_secVec_eq hZQB ψ hwQB hw
  obtain ⟨b₀, hb₀B, hb₀u⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
  have hCB : ¬ C ≤ B ⊔ Z := by
    intro hle
    obtain ⟨s, hsB, hs⟩ := hsupZ hBV c₁ (hle hc₁C)
    obtain ⟨l, hl⟩ := (hBiff _).mp ⟨s, hsB, rfl⟩
    apply hQv0
    rw [← hc₁v, ← hs, hl, map_smul_eq_sq, hQu, mul_zero]
  have hBC : ¬ B ≤ C ⊔ Z := by
    intro hle
    obtain ⟨s, hsC, hs⟩ := hsupZ hCV b₀ (hle hb₀B)
    obtain ⟨l, hl⟩ := hCvec s hsC
    rw [hs, hb₀u] at hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hl
      exact hu0 hl
    apply hQv0
    have h1 : Q' u = l ^ 2 * Q' v := by rw [hl, map_smul_eq_sq]
    rw [hQu] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hl0
    · exact h
  obtain ⟨hWZ, D, hDc, hDW, hDB, y, hyQD, hyZ, hyBC⟩ := hc.exists_QB_cent_swap hCc hCQB hCB hBC
  have hWV : B ⊔ C ≤ Vt M (LB M Q B) B Z t := sup_le hBV hCV
  have hDV : D ≤ Vt M (LB M Q B) B Z t := hDW.trans hWV
  obtain ⟨d₀, hd₀D, hd₀0, hDiff⟩ := hDc.exists_point_of_le hDV ψ hglob θ hθ
  have hWspan : ∀ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ B ⊔ C →
      ∃ α β : K, secVec ψ x = α • u + β • v := by
    intro x hx
    let T : Subgroup G :=
      { carrier := {y | ∃ hy : y ∈ Vt M (LB M Q B) B Z t, ∃ α β : K,
          secVec ψ ⟨y, hy⟩ = α • u + β • v}
        mul_mem' := by
          rintro a b ⟨ha, α, β, hab⟩ ⟨hb, α', β', hab'⟩
          refine ⟨(Vt M (LB M Q B) B Z t).mul_mem ha hb, α + α', β + β', ?_⟩
          have e := secVec_mul ψ ⟨a, ha⟩ ⟨b, hb⟩
          rw [hab, hab'] at e
          rw [show (⟨a * b, (Vt M (LB M Q B) B Z t).mul_mem ha hb⟩ :
            ↥(Vt M (LB M Q B) B Z t)) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, e]
          module
        one_mem' := ⟨(Vt M (LB M Q B) B Z t).one_mem, 0, 0, by
          rw [zero_smul, zero_smul, add_zero]
          exact (secVec_eq_zero_iff ψ (1 : ↥(Vt M (LB M Q B) B Z t))).mpr Z.one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, α, β, hab⟩
          refine ⟨(Vt M (LB M Q B) B Z t).inv_mem ha, -α, -β, ?_⟩
          have e := secVec_inv ψ ⟨a, ha⟩
          rw [hab] at e
          rw [show (⟨a⁻¹, (Vt M (LB M Q B) B Z t).inv_mem ha⟩ :
            ↥(Vt M (LB M Q B) B Z t)) = (⟨a, ha⟩)⁻¹ from rfl, e]
          module }
    have hle : B ⊔ C ≤ T := by
      refine sup_le (fun b hb => ⟨hBV hb, ?_⟩) (fun c hc' => ⟨hCV hc', ?_⟩)
      · obtain ⟨l, hl⟩ := (hBiff _).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
        exact ⟨l, 0, by rw [hl, zero_smul, add_zero]⟩
      · obtain ⟨l, hl⟩ := hCvec ⟨c, hCV hc'⟩ hc'
        exact ⟨0, l, by rw [hl, zero_smul, zero_add]⟩
    obtain ⟨hy, α, β, h⟩ := hle hx
    exact ⟨α, β, h⟩
  have hQd : Q' (secVec ψ d₀) ≠ 0 := by
    intro hQd0
    obtain ⟨α, β, hαβ⟩ := hWspan d₀ (hDW hd₀D)
    have h1 : Q' (secVec ψ d₀) = β ^ 2 * Q' v := by
      rw [hαβ, QuadraticMap.map_add Q', map_smul_eq_sq, map_smul_eq_sq, hQu, mul_zero, zero_add,
        polar_smul_left_eq, polar_smul_right_eq, hvu, mul_zero, mul_zero, add_zero]
    rw [hQd0] at h1
    have hβ : β = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.mp h
      · exact absurd h hQv0
    rw [hβ, zero_smul, add_zero] at hαβ
    obtain ⟨b, hb, hbd⟩ := (hBiff (α • u)).mpr ⟨α, rfl⟩
    have h2 : (d₀ : G) * (b : G)⁻¹ ∈ Z := (secVec_eq_iff ψ d₀ b).mp (hαβ.trans hbd.symm)
    have h3 : (d₀ : G) * (b : G)⁻¹ ∈ B ⊔ C :=
      (B ⊔ C).mul_mem (hDW hd₀D) ((B ⊔ C).inv_mem (Subgroup.mem_sup_left hb))
    have h4 : (d₀ : G) * (b : G)⁻¹ = 1 := by
      have := Subgroup.mem_inf.mpr ⟨h3, h2⟩
      rw [hWZ] at this
      exact this
    have h5 : (d₀ : G) = b := by
      have := congrArg (· * (b : G)) h4
      simpa using this
    have h6' : (d₀ : G) ∈ D ⊓ B := Subgroup.mem_inf.mpr ⟨hd₀D, h5 ▸ hb⟩
    rw [hDB, Subgroup.mem_bot] at h6'
    exact hd₀0 ((secVec_eq_zero_iff ψ d₀).mpr (h6' ▸ Z.one_mem))
  have hZQD : Z ≤ QB D := (Ctx.Z_le_QB hDc).1
  have hQBconj : ∀ r' : ↥(Rt M (LB M Q B) t), ∀ x : ↥(Vt M (LB M Q B) B Z t),
      QuadraticMap.polar Q' ((φ r' : Matrix ι ι K) *ᵥ u) (secVec ψ x) = 0 →
        (x : G) ∈ QB (conjSubgroup (r' : G) B) := by
    intro r' x hx
    rw [QB_conj, mem_conjSubgroup]
    set x' : ↥(Vt M (LB M Q B) B Z t) :=
      ⟨(r' : G)⁻¹ * x * r', by
        have := hconjV r'⁻¹ _ x.2
        simpa using this⟩ with hx'
    have h1 := hψ r' x' x (by simp only [hx']; group)
    change secVec ψ x = (φ r' : Matrix ι ι K) *ᵥ secVec ψ x' at h1
    rw [h1, E.polar_mulVec (hφ ▸ MonoidHom.mem_range.mpr ⟨r', rfl⟩)] at hx
    obtain ⟨w, ⟨-, hwQB⟩, hw⟩ := (hW (secVec ψ x')).mpr hx
    exact mem_of_secVec_eq hZQB ψ hwQB hw
  have hconjBvec : ∀ r' : ↥(Rt M (LB M Q B) t), ∀ l : K,
      ∃ e : ↥(Vt M (LB M Q B) B Z t), (e : G) ∈ conjSubgroup (r' : G) B ∧
        secVec ψ e = l • ((φ r' : Matrix ι ι K) *ᵥ u) := by
    intro r' l
    obtain ⟨b, hb, hbv⟩ := (hBiff (l • u)).mpr ⟨l, rfl⟩
    refine ⟨⟨(r' : G) * b * (r' : G)⁻¹, hconjV r' _ b.2⟩, ?_, ?_⟩
    · show (r' : G) * b * (r' : G)⁻¹ ∈ conjSubgroup (r' : G) B
      rw [mem_conjSubgroup]
      have e : (r' : G)⁻¹ * ((r' : G) * b * (r' : G)⁻¹) * r' = b := by group
      rw [e]
      exact hb
    · have h1 := hψ r' b ⟨(r' : G) * b * (r' : G)⁻¹, hconjV r' _ b.2⟩ rfl
      change secVec ψ _ = (φ r' : Matrix ι ι K) *ᵥ secVec ψ b at h1
      rw [h1, hbv, Matrix.mulVec_smul]
  have hyM : y ∈ M := by
    rw [← hc.hyp.normalizer_Z.1]
    exact Subgroup.centralizer_le_normalizer (Z : Set G) hyZ
  have hyconj : ∀ z ∈ Z, y * z * y⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hyZ z hz, mul_inv_cancel_right]
  have hconjBvec' : ∀ r' : ↥(Rt M (LB M Q B) t), ∀ e : ↥(Vt M (LB M Q B) B Z t),
      (e : G) ∈ conjSubgroup (r' : G) B →
        ∃ l : K, secVec ψ e = l • ((φ r' : Matrix ι ι K) *ᵥ u) := by
    intro r' e he
    have he' := mem_conjSubgroup.mp he
    obtain ⟨l, hl⟩ := (hBiff (secVec ψ ⟨(r' : G)⁻¹ * e * r', hBV he'⟩)).mp ⟨_, he', rfl⟩
    have h1 := hψ r' ⟨(r' : G)⁻¹ * e * r', hBV he'⟩ e (by simp only; group)
    change secVec ψ e = (φ r' : Matrix ι ι K) *ᵥ secVec ψ ⟨(r' : G)⁻¹ * e * r', hBV he'⟩ at h1
    exact ⟨l, by rw [h1, hl, Matrix.mulVec_smul]⟩
  set d : ι → K := secVec ψ d₀ with hd
  have hDvec : ∀ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ D → ∃ l : K, secVec ψ x = l • d :=
    fun x hx => (hDiff _).mp ⟨x, hx, rfl⟩
  let S : AddSubgroup (ι → K) :=
    { carrier := {x' | ∃ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ QB D ∧ secVec ψ x = x'}
      add_mem' := by
        rintro a b ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x * x', (QB D).mul_mem hx hx', secVec_mul ψ x x'⟩
      zero_mem' := ⟨1, (QB D).one_mem,
        (secVec_eq_zero_iff ψ (1 : ↥(Vt M (LB M Q B) B Z t))).mpr Z.one_mem⟩
      neg_mem' := by
        rintro a ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, (QB D).inv_mem hx, secVec_inv ψ x⟩ }
  have hSmem : ∀ x' : ι → K, x' ∈ S ↔
      ∃ x : ↥(Vt M (LB M Q B) B Z t), (x : G) ∈ QB D ∧ secVec ψ x = x' := fun _ => Iff.rfl
  have hS : ∀ s : ι → K, polar Q' d s = 0 → Q' s = 0 → s ∈ S := by
    intro s hds hQs
    by_cases hs0 : s = 0
    · rw [hs0]
      exact S.zero_mem
    obtain ⟨A', hA', hA'u⟩ := hWitt u s hu0 hs0 (hQu.trans hQs.symm)
    obtain ⟨r', hr'⟩ : ∃ r' : ↥(Rt M (LB M Q B) t), φ r' = A' := by
      rw [← hφ] at hA'
      exact MonoidHom.mem_range.mp hA'
    have hE'c : Ctx M Q Z (conjSubgroup (r' : G) B) := hc.conj_of_mem (hRM r'.2)
    have hDQE : D ≤ QB (conjSubgroup (r' : G) B) := by
      intro x hx
      obtain ⟨l, hl⟩ := hDvec ⟨x, hDV hx⟩ hx
      exact hQBconj r' ⟨x, hDV hx⟩ (by
        rw [hl, hr', hA'u, polar_smul_right_eq, QuadraticMap.polar_comm, hds, mul_zero])
    have hDE : D ≠ conjSubgroup (r' : G) B := by
      intro hDE
      obtain ⟨l, hl⟩ := hconjBvec' r' d₀ (hDE ▸ hd₀D)
      apply hQd
      rw [hd, hl, map_smul_eq_sq, hr', hA'u, hQs, mul_zero]
    obtain ⟨h', hh'⟩ := hE'c.conj
    obtain ⟨c', hc'⟩ := hDc.conj
    have hEQD : conjSubgroup (r' : G) B ≤ QB D := (Ctx.Z_le_QB (hE'c.frame hh' hc' hDQE hDE)).1
    obtain ⟨e, he, hes⟩ := hconjBvec r' 1
    rw [one_smul, hr', hA'u] at hes
    exact (hSmem s).mpr ⟨e, hEQD he, hes⟩
  have hV₀ : ∀ x : ↥(Vt M (LB M Q B) B Z t), polar Q' d (secVec ψ x) = 0 → (x : G) ∈ QB D := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := (hSmem _).mp (mem_of_forall_singular_perp hQ h3 hQd hS hx)
    exact mem_of_secVec_eq hZQD ψ hw hwx
  have hcommD : ∀ x : ↥(Vt M (LB M Q B) B Z t), polar Q' d (secVec ψ x) = 0 →
      y * x * y⁻¹ * (x : G)⁻¹ ∈ D := fun x hx => by
    have h1 := hDc.QB_comm_mem hyQD (hV₀ x hx)
    rwa [commutatorElement_def] at h1
  have hconjVmem : ∀ x : ↥(Vt M (LB M Q B) B Z t), polar Q' d (secVec ψ x) = 0 →
      y * x * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx => by
    have e : y * (x : G) * y⁻¹ = (y * x * y⁻¹ * (x : G)⁻¹) * x := by group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hDV (hcommD x hx)) x.2
  let pre : (ι → K) → ↥(Vt M (LB M Q B) B Z t) := fun x' => (exists_secVec_eq ψ x').choose
  have hpre : ∀ x', secVec ψ (pre x') = x' := fun x' => (exists_secVec_eq ψ x').choose_spec
  let P : Submodule K (ι → K) := LinearMap.ker (polarBilin Q' d)
  have hPmem : ∀ x', x' ∈ P ↔ polar Q' d x' = 0 := fun x' => by
    simp only [P, LinearMap.mem_ker, polarBilin_apply_apply]
  have hpreP : ∀ p : P, polar Q' d (secVec ψ (pre p)) = 0 := fun p => by
    rw [hpre]
    exact (hPmem p).mp p.2
  let σ : P → ι → K := fun p => secVec ψ ⟨y * pre p * y⁻¹, hconjVmem _ (hpreP p)⟩
  have hσ_add : ∀ p p' : P, σ (p + p') = σ p + σ p' := fun p p' =>
    secVec_conj_add ψ hyconj (by rw [hpre, hpre, hpre]; rfl) rfl rfl rfl
  have hσ_smul : ∀ (c : K) (p : P), σ (c • p) = c • σ p := fun c p =>
    hc.secVec_conj_smul ψ hglob θ hθ hyM hyZ (v := pre p) (v' := pre (c • p))
      (by rw [hpre, hpre]) rfl rfl
  let δ : P →ₗ[K] (ι → K) :=
    { toFun := fun p => σ p - (p : ι → K)
      map_add' := fun p p' => by
        simp only [Submodule.coe_add]
        rw [hσ_add]
        abel
      map_smul' := fun c p => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [hσ_smul, smul_sub] }
  have hδ_mem : ∀ p : P, ∃ l : K, δ p = l • d := by
    intro p
    have hx := hpreP p
    obtain ⟨l, hl⟩ := hDvec ⟨y * pre p * y⁻¹ * (pre p : G)⁻¹, hDV (hcommD _ hx)⟩ (hcommD _ hx)
    have e : (⟨y * pre p * y⁻¹ * (pre p : G)⁻¹, hDV (hcommD _ hx)⟩ :
        ↥(Vt M (LB M Q B) B Z t)) = ⟨y * pre p * y⁻¹, hconjVmem _ hx⟩ * (pre p)⁻¹ := rfl
    refine ⟨l, ?_⟩
    rw [← hl, e, secVec_mul, secVec_inv, hpre, ← sub_eq_add_neg]
    rfl
  have hd0 : d ≠ 0 := fun h => hQd (by rw [h, QuadraticMap.map_zero])
  have hrange : Module.finrank K (LinearMap.range δ) ≤ 1 := by
    have hle : LinearMap.range δ ≤ K ∙ d := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨l, hl⟩ := hδ_mem p
      rw [hl]
      exact Submodule.smul_mem _ l (Submodule.mem_span_singleton_self d)
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton hd0).le
  have hPdim : Module.finrank K (ι → K) ≤ Module.finrank K P + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (polarBilin Q' d)
    have h2 : Module.finrank K (LinearMap.range (polarBilin Q' d)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (polarBilin Q' d))
      rwa [Module.finrank_self] at this
    show Module.finrank K (ι → K) ≤ Module.finrank K (LinearMap.ker (polarBilin Q' d)) + 1
    omega
  let U : Submodule K (ι → K) := (LinearMap.ker δ).map P.subtype
  have hUdim : Module.finrank K (ι → K) ≤ Module.finrank K U + 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker δ
    have h2 : Module.finrank K U = Module.finrank K (LinearMap.ker δ) :=
      (Submodule.equivMapOfInjective _ P.injective_subtype _).finrank_eq.symm
    omega
  have hdP : d ∈ P := (hPmem d).mpr (by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero])
  have hyd₀ : y * (d₀ : G) * y⁻¹ = d₀ := by
    rw [hDc.QB_comm hyQD hd₀D, mul_inv_cancel_right]
  have hδd : δ ⟨d, hdP⟩ = 0 := by
    have h1 : σ ⟨d, hdP⟩ = d :=
      secVec_conj_eq ψ hyconj (v' := d₀) (w' := d₀) (hpre d) rfl hyd₀.symm
    show σ ⟨d, hdP⟩ - d = 0
    rw [h1, sub_self]
  have hdU : d ∈ U := Submodule.mem_map.mpr ⟨⟨d, hdP⟩, LinearMap.mem_ker.mpr hδd, rfl⟩
  have hUd : ∀ x ∈ U, polar Q' d x = 0 := by
    rintro x ⟨p, -, rfl⟩
    exact (hPmem p).mp p.2
  have hcent : ∀ x' ∈ U, ∀ e : ↥(Vt M (LB M Q B) B Z t), secVec ψ e = x' →
      y * (e : G) = e * y := by
    rintro x' ⟨p, hp, rfl⟩ e he
    have hpe : polar Q' d (secVec ψ e) = 0 := by
      rw [he]
      exact (hPmem p).mp p.2
    have h0 : δ p = 0 := LinearMap.mem_ker.mp hp
    have h1 : σ p = (p : ι → K) := sub_eq_zero.mp h0
    have h2 : secVec ψ ⟨y * e * y⁻¹, hconjVmem e hpe⟩ = secVec ψ e := by
      have h3 : secVec ψ ⟨y * e * y⁻¹, hconjVmem e hpe⟩ = σ p :=
        secVec_conj_eq ψ hyconj (he.trans (hpre p).symm) rfl rfl
      rw [h3, h1, he]
      rfl
    have h3 : y * (e : G) * y⁻¹ * (e : G)⁻¹ ∈ Z :=
      (secVec_eq_iff ψ ⟨_, hconjVmem e hpe⟩ e).mp h2
    have h4 : y * (e : G) * y⁻¹ * (e : G)⁻¹ = 1 := by
      have h5 := Subgroup.mem_inf.mpr ⟨h3, hcommD e hpe⟩
      rwa [hDc.inf_eq_bot, Subgroup.mem_bot] at h5
    calc y * (e : G) = (y * e * y⁻¹ * (e : G)⁻¹) * e * y := by group
      _ = e * y := by rw [h4, one_mul]
  obtain ⟨x₁, hx₁U, x₂, hx₂U, hQx₁, hQx₂, hx₁₂⟩ :=
    exists_singular_pair_of_le_perp hQ h6 hQd U hdU hUd hUdim
  have hx₁0 : x₁ ≠ 0 := by
    rintro rfl
    simp at hx₁₂
  have hx₂0 : x₂ ≠ 0 := by
    rintro rfl
    simp at hx₁₂
  obtain ⟨A₁, hA₁, hA₁u⟩ := hWitt u x₁ hu0 hx₁0 (hQu.trans hQx₁.symm)
  obtain ⟨A₂, hA₂, hA₂u⟩ := hWitt u x₂ hu0 hx₂0 (hQu.trans hQx₂.symm)
  obtain ⟨r₁, hr₁⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A₁ := by
    rw [← hφ] at hA₁
    exact MonoidHom.mem_range.mp hA₁
  obtain ⟨r₂, hr₂⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = A₂ := by
    rw [← hφ] at hA₂
    exact MonoidHom.mem_range.mp hA₂
  have hyL : ∀ (r' : ↥(Rt M (LB M Q B) t)) (x' : ι → K), x' ∈ U →
      (φ r' : Matrix ι ι K) *ᵥ u = x' →
        conjSubgroup y (LB M Q (conjSubgroup (r' : G) B)) = LB M Q (conjSubgroup (r' : G) B) := by
    intro r' x' hx' hr'x
    have hfix : conjSubgroup y (conjSubgroup (r' : G) B) = conjSubgroup (r' : G) B := by
      refine conjSubgroup_eq_self_of_commute fun e he => ?_
      have heV : e ∈ Vt M (LB M Q B) B Z t := by
        have h1 := hBV (mem_conjSubgroup.mp he)
        have e1 : e = (r' : G) * ((r' : G)⁻¹ * e * r') * (r' : G)⁻¹ := by group
        rw [e1]
        exact hconjV r' _ h1
      obtain ⟨l, hl⟩ := hconjBvec' r' ⟨e, heV⟩ he
      rw [hr'x] at hl
      exact hcent _ (U.smul_mem l hx') ⟨e, heV⟩ hl
    rw [← (hc.conj_of_mem (hRM r'.2)).LB_conj hyM, hfix]
  have hLmap : ∀ (r' : ↥(Rt M (LB M Q B) t)) (x' : ι → K), (φ r' : Matrix ι ι K) *ᵥ u = x' →
      ((LB M Q (conjSubgroup (r' : G) B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        E.LomGL x' := by
    intro r' x' hx'
    rw [hc.LB_conj (hRM r'.2), ← hx']
    exact (hroot r').2
  set L₁ := LB M Q (conjSubgroup (r₁ : G) B) with hL₁
  set L₂ := LB M Q (conjSubgroup (r₂ : G) B) with hL₂
  have hR₀R : L₁ ⊔ L₂ ≤ Rt M (LB M Q B) t :=
    sup_le (hc.LB_conj_le_Rt_of_mem ht r₁.2) (hc.LB_conj_le_Rt_of_mem ht r₂.2)
  have hyR₀ : conjSubgroup y (L₁ ⊔ L₂) = L₁ ⊔ L₂ := by
    rw [conjSubgroup_sup', hyL r₁ x₁ hx₁U (by rw [hr₁, hA₁u]),
      hyL r₂ x₂ hx₂U (by rw [hr₂, hA₂u])]
  obtain ⟨lam, hlam0, hlam1⟩ : ∃ lam : K, lam ≠ 0 ∧ lam ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun a : K => decide (a = 0)) := by
      intro a b hab
      by_cases ha : a = 0
      · by_cases hb : b = 0
        · rw [ha, hb]
        · simp [ha, hb] at hab
      · by_cases hb : b = 0
        · simp [ha, hb] at hab
        · rw [hcon a ha, hcon b hb]
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
    have h4 := hc.hyp.q4
    omega
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    apply hlam1
    have h1 : (lam + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
    have h2 := eq_neg_of_add_eq_zero_left (pow_eq_zero_iff two_ne_zero |>.mp h1)
    rwa [CharTwo.neg_eq] at h2
  obtain ⟨A₀, hA₀, hA₀u⟩ := hWitt u (lam • u) hu0 (smul_ne_zero hlam0 hu0)
    (by rw [map_smul_eq_sq, hQu, mul_zero])
  have hA₀R₀ : A₀ ∈ ((L₁ ⊔ L₂).subgroupOf (Rt M (LB M Q B) t)).map φ := by
    have h1 : A₀ ∈ E.LomGL x₁ ⊔ E.LomGL x₂ := by
      rw [E.LomGL_sup_eq hQ hQx₁ hQx₂ (by rw [hx₁₂]; exact one_ne_zero)]
      exact hA₀
    rw [← hLmap r₁ x₁ (by rw [hr₁, hA₁u]), ← hLmap r₂ x₂ (by rw [hr₂, hA₂u]),
      ← Subgroup.map_sup] at h1
    refine Subgroup.map_mono (sup_le ?_ ?_) h1
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨r₀, hr₀R₀, hr₀⟩ := Subgroup.mem_map.mp hA₀R₀
  have hr₃mem : y * (r₀ : G) * y⁻¹ ∈ L₁ ⊔ L₂ := by
    rw [← hyR₀, mem_conjSubgroup]
    have e : y⁻¹ * (y * (r₀ : G) * y⁻¹) * y = r₀ := by group
    rw [e]
    exact Subgroup.mem_subgroupOf.mp hr₀R₀
  set r₃ : ↥(Rt M (LB M Q B) t) := ⟨y * r₀ * y⁻¹, hR₀R hr₃mem⟩ with hr₃
  set w : ↥(Vt M (LB M Q B) B Z t) := ⟨y * b₀ * y⁻¹, hCV (hyBC b₀ hb₀B)⟩ with hw
  obtain ⟨μ, hμ⟩ := hCvec w (hyBC b₀ hb₀B)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul, secVec_eq_zero_iff] at hμ
    have h1 := hyconj _ hμ
    have e : (b₀ : G) = y * b₀ * y⁻¹ := by
      calc (b₀ : G) = y⁻¹ * (y * b₀ * y⁻¹) * y := by group
        _ = y⁻¹ * (y * (y * b₀ * y⁻¹) * y⁻¹) * y := by rw [h1]
        _ = y * b₀ * y⁻¹ := by group
    have hb₀Z : (b₀ : G) ∈ Z := by
      rw [e]
      exact hμ
    apply hu0
    rw [← hb₀u]
    exact (secVec_eq_zero_iff ψ b₀).mpr hb₀Z
  set b' : ↥(Vt M (LB M Q B) B Z t) := ⟨(r₀ : G) * b₀ * (r₀ : G)⁻¹, hconjV r₀ _ b₀.2⟩ with hb'
  have hb'vec : secVec ψ b' = lam • secVec ψ b₀ := by
    have h1 := hψ r₀ b₀ b' rfl
    change secVec ψ b' = (φ r₀ : Matrix ι ι K) *ᵥ secVec ψ b₀ at h1
    rw [h1, hr₀, hb₀u, hA₀u]
  have hw'V : y * (b' : G) * y⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have e : y * (b' : G) * y⁻¹ = (r₃ : G) * w * (r₃ : G)⁻¹ := by
      simp only [hb', hr₃, hw]
      group
    rw [e]
    exact hconjV r₃ _ w.2
  set w' : ↥(Vt M (LB M Q B) B Z t) := ⟨y * b' * y⁻¹, hw'V⟩ with hw'
  have h1 : secVec ψ w' = lam • secVec ψ w :=
    hc.secVec_conj_smul ψ hglob θ hθ hyM hyZ hb'vec rfl rfl
  have h2 : secVec ψ w' = (φ r₃ : Matrix ι ι K) *ᵥ secVec ψ w := by
    refine hψ r₃ w w' ?_
    simp only [hw', hb', hr₃, hw]
    group
  have h3 : (φ r₃ : Matrix ι ι K) *ᵥ v = lam • v := by
    have h4 := h1.symm.trans h2
    rw [hμ, Matrix.mulVec_smul, smul_comm] at h4
    exact (smul_right_injective _ hμ0 h4).symm
  have h5 : Q' v = lam ^ 2 * Q' v := by
    rw [← map_smul_eq_sq, ← h3, E.quad_mulVec (hφ ▸ MonoidHom.mem_range.mpr ⟨r₃, rfl⟩)]
  apply hlam2
  have h6 : (lam ^ 2 - 1) * Q' v = 0 := by rw [sub_mul, ← h5, one_mul, sub_self]
  rcases mul_eq_zero.mp h6 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hQv0

theorem sec56SingularConj_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Sec56SingularConjStatement := by
  refine ⟨?_, ?_⟩
  · intro G _ _ M Q Z B hc n t hs K _ _ hK m hm3 φ hφ hker _ ψ hψ
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have hnat : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, inferInstance, inferInstance, hK, Or.inl ⟨m, hm3, φ, hφ, hker,
        hc.Rt_normalizes_Vt hs.mem, inferInstance, ψ, hψ⟩⟩
    have h6 : 6 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    exact hc.natSingularConj_of h34 hRoot hs hnat hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h6 (addCommutantScalar_statedOmegaPlus hm3)
      (fun x y hx hy hxy => (ElemMatrixIso.plus hm3).exists_mulVec_eq
        (nondegenerate_polarBilin_quadPlus m K)
        (plusPair_orth (K := K) (n := m) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
          (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hx hy hxy) φ hφ hker ψ hψ
  · intro G _ _ M Q Z B hc n t hs K _ _ hK m b c hm3 hirr φ hφ hker _ ψ hψ
    have hmm : 2 ≤ m := by omega
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have hnat : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, inferInstance, inferInstance, hK, Or.inr ⟨m, b, c, hmm, hirr, φ, hφ, hker,
        hc.Rt_normalizes_Vt hs.mem, inferInstance, ψ, hψ⟩⟩
    have h6 : 6 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega
    exact hc.natSingularConj_of h34 hRoot hs hnat hK (ElemMatrixIso.minus hmm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h6
      (addCommutantScalar_statedOmegaMinus hmm hirr)
      (fun x y hx hy hxy => (ElemMatrixIso.minus hmm hirr).exists_mulVec_eq
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
        (minusPair_orth (K := K) (n := m) (b := b) (c := c) (i := ⟨0, by omega⟩)
          (j := ⟨1, by omega⟩) (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hx hy hxy)
      φ hφ hker ψ hψ

theorem stroth56Nat_of_34 (h34 : Stroth34Statement) : Stroth56NatStatement :=
  stroth56Nat_of h34 (stroth310Root_of_34 h34) (sec56SingularConj_of h34 (stroth310Root_of_34 h34))

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Matrix
open scoped Matrix

noncomputable section

variable {F : Type} [Field F] [Finite F]

theorem uJGL_zero_central [Finite F] [CharP F 2] {k : ℕ} (hFc : Nat.card F = (2 ^ k) ^ 2)
    {b : F} {y : GL (Fin 3) F} (hy : y ∈ CFSG.Quasithin.H.SU3.ujSub k F) :
    CFSG.Quasithin.H.SU3.uJGL k 0 b * y = y * CFSG.Quasithin.H.SU3.uJGL k 0 b := by
  obtain ⟨a, b', hb', rfl⟩ := exists_uJGL_of_mem_ujSub (F := F) hFc hy
  simp only [uJGL_mul]
  congr 1 <;> simp [add_comm, add_left_comm, add_assoc]

theorem exists_uJGL_zero_of_central [Finite F] [CharP F 2] {k : ℕ}
    (hk : 1 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2) {w : GL (Fin 3) F}
    (hwB : w ∈ CFSG.Quasithin.H.SU3.ujSub k F)
    (hwc : ∀ y ∈ CFSG.Quasithin.H.SU3.ujSub k F, w * y = y * w) :
    ∃ b : F, w = CFSG.Quasithin.H.SU3.uJGL k 0 b := by
  obtain ⟨a, b, hb, rfl⟩ := exists_uJGL_of_mem_ujSub (F := F) hFc hwB
  have hcomm : ∀ t : F,
      a * CFSG.Quasithin.H.SU3.bar k t = t * CFSG.Quasithin.H.SU3.bar k a := by
    intro t
    obtain ⟨c, hc⟩ := CFSG.Quasithin.H.SU3.exists_traceHom_eq (n := k) hk hFc
      (c := t * CFSG.Quasithin.H.SU3.bar k t)
      (CFSG.Quasithin.H.SU3.bar_mul_bar_self hFc t)
    have hu : CFSG.Quasithin.H.SU3.uJGL k t c ∈ CFSG.Quasithin.H.SU3.ujSub k F :=
      CFSG.Quasithin.H.SU3.uJGL_mem_ujSub hFc hc
    have h := hwc _ hu
    rw [uJGL_mul, uJGL_mul] at h
    have h' := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 2)) h
    simp only [CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one] at h'
    have h'' : a * CFSG.Quasithin.H.SU3.bar k t + (b + c) =
        t * CFSG.Quasithin.H.SU3.bar k a + (b + c) := by
      simpa [add_comm, add_left_comm, add_assoc] using h'
    exact add_right_cancel h''
  have ha1 : a = CFSG.Quasithin.H.SU3.bar k a := by
    simpa using hcomm 1
  obtain ⟨t, ht⟩ := CFSG.Quasithin.H.SU3.exists_bar_ne (n := k) hk hFc
  have ht0 : CFSG.Quasithin.H.SU3.bar k t + t ≠ 0 := by
    intro h
    apply ht
    have h' := add_eq_zero_iff_eq_neg.mp h
    simpa [CharTwo.neg_eq] using h'
  have ha : a = 0 := by
    have h := hcomm t
    rw [← ha1] at h
    have h' : a * (CFSG.Quasithin.H.SU3.bar k t + t) = 0 := by
      rw [mul_add, h, mul_comm t a, CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h').resolve_right ht0
  subst ha
  exact ⟨b, rfl⟩

theorem u3_similitude_weight [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2) (g : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hgL : ∀ x ∈ su3Anti F k, ∃ x' ∈ su3Anti F k, ∀ v,
      g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ g v)
    (hgT : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k F, ∃ x' ∈ CFSG.Quasithin.H.SU3.ujSub k F, ∀ v,
      g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ g v)
    (hg0 : ∀ c : F, g (Pi.single 0 c) = Pi.single 0 c) :
    (∀ (c : F) (v : Fin 3 → F), g (c • v) = c • g v) ∧
    ∃ χ₂ χ₃ : Fˣ, (χ₃ : F) = (χ₂ : F) ^ (2 ^ k + 1) ∧ (χ₃ : F) ^ 2 ^ k = χ₃ ∧
      (∃ x : F, g (Pi.single 1 1) = (χ₂ : F) • Pi.single 1 1 + Pi.single 0 x) ∧
      ∃ x y : F, g (Pi.single 2 1) = (χ₃ : F) • Pi.single 2 1 + Pi.single 1 y + Pi.single 0 x := by
  classical
  have hlin : ∀ (c : F) (v : Fin 3 → F), g (c • v) = c • g v := by
    intro c v
    have hsc := hasScalarCommutant_su3Anti (F := F) (k := k) (by omega) hFc
    let f : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun w => g.symm (c • g w)
        map_zero' := by simp
        map_add' := fun w u => by
          simp only [map_add, smul_add, map_add] }
    have hf : ∀ x ∈ su3Anti F k, ∀ w : Fin 3 → F,
        f ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
          (x : Matrix (Fin 3) (Fin 3) F) *ᵥ f w := by
      intro x hx w
      obtain ⟨x', hx', hx'w⟩ := hgL x hx
      apply g.injective
      calc
        g (f ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ w))
            = c • g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by simp [f]
        _ = c • ((x' : Matrix (Fin 3) (Fin 3) F) *ᵥ (g w)) := by rw [hx'w w]
        _ = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ (c • g w) := by rw [Matrix.mulVec_smul]
        _ = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ (g (f w)) := by simp [f]
        _ = g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ f w) := by rw [hx'w (f w)]
    obtain ⟨d, hd⟩ := hsc f hf
    have hsingle : Pi.single 0 c = c • (Pi.single 0 1 : Fin 3 → F) := by
      funext i
      fin_cases i <;> simp
    have hgc : g (c • (Pi.single 0 1 : Fin 3 → F)) = c • (Pi.single 0 1 : Fin 3 → F) := by
      simpa [hsingle] using hg0 c
    have hfe : f (Pi.single 0 1) = c • (Pi.single 0 1 : Fin 3 → F) := by
      have h := congrArg g.symm hgc
      simpa [f, hg0 1] using h.symm
    have hdc : d = c := by
      have h := hd (Pi.single 0 1)
      rw [hfe] at h
      have h0 := congrFun h 0
      simpa using h0.symm
    have hfv : f v = c • v := by
      rw [hd v, hdc]
    rw [← hfv]
    simp [f]
  let e0 : Fin 3 → F := Pi.single 0 1
  let e1 : Fin 3 → F := Pi.single 1 1
  let e2 : Fin 3 → F := Pi.single 2 1
  have hge0 : g e0 = e0 := hg0 1
  let M : GL (Fin 3) F → Matrix (Fin 3) (Fin 3) F :=
    fun x => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  let B : Subgroup (GL (Fin 3) F) := CFSG.Quasithin.H.SU3.ujSub k F
  let φ : ↥B → ↥B := fun x =>
    ⟨Classical.choose (hgT x x.2), (Classical.choose_spec (hgT x x.2)).1⟩
  have hφspec : ∀ x : ↥B, ∀ v,
      g ((x : GL (Fin 3) F) *ᵥ v) = M (φ x) *ᵥ g v :=
    fun x => (Classical.choose_spec (hgT x x.2)).2
  have hφmul : ∀ x y : ↥B, φ (x * y) = φ x * φ y := by
    intro x y
    apply Subtype.ext
    apply Units.ext
    ext i j
    have h : ∀ v : Fin 3 → F,
        M (φ (x * y)) *ᵥ (g v) =
          M (φ x * φ y) *ᵥ (g v) := by
      intro v
      have h1 : M (x * y) *ᵥ v =
          M x *ᵥ (M y *ᵥ v) := by
        simp [M, Units.val_mul, Matrix.mulVec_mulVec]
      rw [← hφspec (x * y) v]
      change g (M (x * y) *ᵥ v) = M (φ x * φ y) *ᵥ g v
      rw [h1, hφspec x (M y *ᵥ v), hφspec y v]
      simp [M, Units.val_mul, Matrix.mulVec_mulVec]
    have h' := h (g.symm (Pi.single j 1))
    simpa [M, Matrix.mulVec_single_one] using congrFun h' i
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : ((φ x : ↥B) : GL (Fin 3) F) = ((φ y : ↥B) : GL (Fin 3) F) :=
      congrArg Subtype.val hxy
    apply Subtype.ext
    apply Units.ext
    ext i j
    have h : M x *ᵥ (Pi.single j 1 : Fin 3 → F) =
        M y *ᵥ (Pi.single j 1 : Fin 3 → F) := by
      apply g.injective
      rw [hφspec x, hφspec y, hxy']
    simpa [Matrix.mulVec_single_one] using congrFun h i
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  let z : GL (Fin 3) F := CFSG.Quasithin.H.SU3.uJGL k 0 1
  have hzB : z ∈ B := by
    refine CFSG.Quasithin.H.SU3.uJGL_mem_ujSub hFc ?_
    simp [CFSG.Quasithin.H.SU3.traceHom_apply, CharTwo.add_self_eq_zero]
  have hzcentral : ∀ y ∈ B, z * y = y * z := by
    intro y hy
    exact uJGL_zero_central (F := F) hFc hy
  have hφzcentral : ∀ y ∈ B, ((φ ⟨z, hzB⟩ : ↥B) : GL (Fin 3) F) * y =
      y * ((φ ⟨z, hzB⟩ : ↥B) : GL (Fin 3) F) := by
    intro y hy
    obtain ⟨w, hw⟩ := hφsurj ⟨y, hy⟩
    change ((φ ⟨z, hzB⟩ : ↥B) : GL (Fin 3) F) * ((⟨y, hy⟩ : ↥B) : GL (Fin 3) F) =
      ((⟨y, hy⟩ : ↥B) : GL (Fin 3) F) * ((φ ⟨z, hzB⟩ : ↥B) : GL (Fin 3) F)
    rw [← hw]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    rw [← congrArg Subtype.val (hφmul ⟨z, hzB⟩ w),
      ← congrArg Subtype.val (hφmul w ⟨z, hzB⟩)]
    congr 2
    apply Subtype.ext
    exact hzcentral (w : GL (Fin 3) F) w.2
  obtain ⟨d, hd⟩ := exists_uJGL_zero_of_central (F := F) (k := k) (by omega) hFc
    (φ ⟨z, hzB⟩).2 hφzcentral
  have hd1 : d ≠ 0 := by
    intro hd0
    have h1 : (φ ⟨z, hzB⟩ : ↥B) = 1 := by
      apply Subtype.ext
      rw [hd, hd0]
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat]
    have hzv : ∀ v : Fin 3 → F, z *ᵥ v = v := by
      intro v
      apply g.injective
      rw [hφspec ⟨z, hzB⟩ v, h1]
      simp [M]
    have hz1 : z = 1 := by
      apply Units.ext
      ext i j
      have := congrFun (hzv (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this.symm
    have := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 2)) hz1
    simp [z, CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat] at this
  let v1 : Fin 3 → F := g e1
  have hz_e1 : z *ᵥ e1 = e1 := by
    dsimp [z]
    rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  have hv1eq : v1 = (CFSG.Quasithin.H.SU3.uJGL k 0 d : Matrix (Fin 3) (Fin 3) F) *ᵥ v1 := by
    have h := hφspec ⟨z, hzB⟩ e1
    rw [hz_e1, hd] at h
    exact h
  have hv12 : v1 2 = 0 := by
    have h0 := congrFun hv1eq 0
    rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec] at h0
    simp only [Matrix.cons_val_zero, zero_mul, add_zero, mul_one] at h0
    have h0' : v1 0 + 0 = v1 0 + d * v1 2 := by simpa using h0
    have h := add_left_cancel h0'
    exact (mul_eq_zero.mp h.symm).resolve_left hd1
  have hge1 : g e1 = (v1 1) • e1 + (v1 0) • e0 := by
    ext i
    fin_cases i <;> simp [e0, e1, v1, hv12]
  have hy1 : v1 1 ≠ 0 := by
    intro hy0
    have h1 : g e1 = (v1 0) • e0 := by rw [hge1, hy0, zero_smul, zero_add]
    have hz : g (e1 + (v1 0) • e0) = 0 := by
      rw [map_add, hlin, h1, hge0, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hne : e1 + (v1 0) • e0 ≠ 0 := by
      intro h
      have := congrFun h 1
      simp [e0, e1] at this
    have h0 : e1 + (v1 0) • e0 = 0 := by
      apply g.injective
      rw [hz, map_zero]
    exact hne h0
  let v2 : Fin 3 → F := g e2
  have hb2 : v2 2 ≠ 0 := by
    intro hb0
    have hge2 : g e2 = (v2 0) • e0 + (v2 1) • e1 := by
      ext i
      fin_cases i <;> simp [e0, e1, v2, hb0]
    let W : Submodule F (Fin 3 → F) := Submodule.span F {e0, e1}
    have hW0 : e0 ∈ W := Submodule.subset_span (by simp)
    have hW1 : e1 ∈ W := Submodule.subset_span (by simp)
    have hWge1 : g e1 ∈ W := by
      rw [hge1]
      exact W.add_mem (W.smul_mem _ hW1) (W.smul_mem _ hW0)
    have hWge2 : g e2 ∈ W := by
      rw [hge2]
      exact W.add_mem (W.smul_mem _ hW0) (W.smul_mem _ hW1)
    have hWall : ∀ v : Fin 3 → F, g v ∈ W := by
      intro v
      have hv : v = (v 0) • e0 + (v 1) • e1 + (v 2) • e2 := by
        ext i
        fin_cases i <;> simp [e0, e1, e2]
      rw [hv]
      simp only [map_add, hlin, hge0]
      exact W.add_mem (W.add_mem (W.smul_mem _ hW0) (W.smul_mem _ hWge1))
        (W.smul_mem _ hWge2)
    have he2not : e2 ∉ W := by
      intro h
      have hker : W ≤ LinearMap.ker (LinearMap.proj (R := F) (i := 2)) := by
        apply Submodule.span_le.mpr
        intro x hx
        rcases hx with rfl | rfl <;>
          simp [LinearMap.mem_ker, e0, e1]
      have := hker h
      simp [LinearMap.mem_ker, e2] at this
    obtain ⟨v, hv⟩ := g.surjective e2
    exact he2not (hv ▸ hWall v)
  obtain ⟨c, hc⟩ := CFSG.Quasithin.H.SU3.exists_traceHom_eq (n := k) (by omega) hFc
    (c := (1 : F)) (by simp)
  have hc' : c + c ^ (2 ^ k) = 1 := by
    simpa [CFSG.Quasithin.H.SU3.traceHom_apply, CFSG.Quasithin.H.SU3.bar_apply] using hc
  let u : GL (Fin 3) F := CFSG.Quasithin.H.SU3.uJGL k 1 c
  have huB : u ∈ B := by
    refine CFSG.Quasithin.H.SU3.uJGL_mem_ujSub hFc ?_
    simpa using hc
  obtain ⟨a', b', hb', hu'eq⟩ := exists_uJGL_of_mem_ujSub (F := F) hFc
    (φ ⟨u, huB⟩).2
  have hu'_eq : ((φ ⟨u, huB⟩ : ↥B) : GL (Fin 3) F) =
      CFSG.Quasithin.H.SU3.uJGL k a' b' := hu'eq
  have hu_e1 : u *ᵥ e1 = e1 + e0 := by
    rw [show u = CFSG.Quasithin.H.SU3.uJGL k 1 c from rfl,
      CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  have hu_e2 : u *ᵥ e2 = e2 + e1 + c • e0 := by
    rw [show u = CFSG.Quasithin.H.SU3.uJGL k 1 c from rfl,
      CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
    ext i
    fin_cases i <;> simp [e0, e1, e2, CFSG.Quasithin.H.SU3.bar_apply]
  have hcoef1 : a' * (v1 1) = 1 := by
    have h := hφspec ⟨u, huB⟩ e1
    rw [hu_e1, hu'_eq, map_add, hge0] at h
    have h0 := congrFun h 0
    dsimp only [M] at h0
    rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec] at h0
    simp only [Matrix.cons_val_zero, mul_zero, add_zero] at h0
    have hv12' : g e1 2 = 0 := hv12
    rw [hv12'] at h0
    simp only [mul_zero, add_zero] at h0
    have h0' : v1 0 + 1 = v1 0 + a' * v1 1 := h0
    exact (add_left_cancel h0').symm
  have hcoef2 : v1 1 = (CFSG.Quasithin.H.SU3.bar k a') * (v2 2) := by
    have h := hφspec ⟨u, huB⟩ e2
    rw [hu_e2, hu'_eq] at h
    have h2 := congrFun h 1
    dsimp only [M] at h2
    rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec] at h2
    simp only [Matrix.cons_val_one, Matrix.head_cons, mul_one] at h2
    have hv1 : g (e2 + e1 + c • e0) = v2 + v1 + c • e0 := by
      rw [map_add, map_add, hlin, hge0]
    rw [hv1] at h2
    simp only [Pi.add_apply, Pi.smul_apply] at h2
    have h2' : v1 1 + v2 1 = v2 1 +
        (CFSG.Quasithin.H.SU3.bar k) a' * v2 2 := by
      simpa [e0, e1, e2, v1, v2, Pi.single_apply, add_comm, add_left_comm,
        add_assoc] using h2
    rw [add_comm (v1 1) (v2 1)] at h2'
    exact add_left_cancel h2'
  have hrel : (v2 2) = (v1 1) ^ (2 ^ k + 1) := by
    have ha' : a' = (v1 1)⁻¹ := by
      have := congrArg (fun t : F => t * (v1 1)⁻¹) hcoef1
      simpa [mul_assoc, hy1] using this
    have ha'0 : a' ≠ 0 := by
      rw [ha']
      exact inv_ne_zero hy1
    have hbar'0 : CFSG.Quasithin.H.SU3.bar k a' ≠ 0 :=
      (map_ne_zero (CFSG.Quasithin.H.SU3.bar k)).mpr ha'0
    have hb : v2 2 = (v1 1) / (CFSG.Quasithin.H.SU3.bar k a') := by
      rw [hcoef2]
      field_simp
    rw [hb, ha']
    simp only [CFSG.Quasithin.H.SU3.bar_apply, map_inv₀, inv_pow]
    rw [div_inv_eq_mul, pow_succ']
  have hrelq : ((v2 2) ^ (2 ^ k)) = v2 2 := by
    have hyq2 : ((v1 1) ^ (2 ^ k * 2 ^ k)) = v1 1 := by
      letI : Fintype F := Fintype.ofFinite F
      rw [show 2 ^ k * 2 ^ k = Nat.card F by rw [hFc]; ring,
        Nat.card_eq_fintype_card]
      exact FiniteField.pow_card (v1 1)
    calc
      (v2 2) ^ (2 ^ k) = ((v1 1) ^ (2 ^ k + 1)) ^ (2 ^ k) := by rw [hrel]
      _ = (v1 1) ^ ((2 ^ k + 1) * 2 ^ k) := by rw [pow_mul]
      _ = (v1 1) ^ (2 ^ k * 2 ^ k + 2 ^ k) := by
        rw [show (2 ^ k + 1) * 2 ^ k = 2 ^ k * 2 ^ k + 2 ^ k by ring]
      _ = (v1 1) ^ (2 ^ k * 2 ^ k) * (v1 1) ^ (2 ^ k) := by rw [pow_add]
      _ = (v1 1) * (v1 1) ^ (2 ^ k) := by rw [hyq2]
      _ = (v1 1) ^ (2 ^ k + 1) := by rw [pow_succ']
      _ = v2 2 := by rw [hrel]
  refine ⟨hlin, ⟨Units.mk0 (v1 1) hy1, Units.mk0 (v2 2) hb2, ?_, ?_, ?_, ?_⟩⟩
  ·
    simpa using hrel
  ·
    simpa using hrelq
  ·
    refine ⟨v1 0, ?_⟩
    rw [hge1]
    ext i
    fin_cases i <;> simp [e0, e1, Units.val_mk0]
  ·
    refine ⟨v2 0, v2 1, ?_⟩
    ext i
    fin_cases i <;> simp [e0, e1, e2, v2, Units.val_mk0, Pi.single_smul]

end

end CFSG.Quasithin.Stroth

module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Link
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.StandardType.LieKnownR2.LinkTriD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis CFSG.StandardType.LieKnownR2.Link
  CFSG.StandardType.LieKnownR2.Coord

private abbrev F8 : Type := Fin 8

private def f8add (a b : F8) : F8 := ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by norm_num)⟩

private def f8mul (a b : F8) : F8 :=
  let c := (if a.val.testBit 0 then b.val else 0) ^^^ (if a.val.testBit 1 then b.val <<< 1 else 0) ^^^
    (if a.val.testBit 2 then b.val <<< 2 else 0)
  ⟨((c &&& 7) ^^^ (if c.testBit 3 then 3 else 0) ^^^ (if c.testBit 4 then 6 else 0)) % 8,
    Nat.mod_lt _ (by norm_num)⟩

private def tri (a : F8) : Fin 3 → ZMod 2 := fun i => if a.val.testBit i then 1 else 0

private theorem tri_add : ∀ a b : F8, tri (f8add a b) = tri a + tri b := by decide +kernel

private theorem tri_mul : ∀ a b : F8, tri (f8mul a b) =
    ![tri a 0 * tri b 0 + (tri a 1 * tri b 2 + tri a 2 * tri b 1),
      tri a 0 * tri b 1 + tri a 1 * tri b 0 + (tri a 1 * tri b 2 + tri a 2 * tri b 1) +
        tri a 2 * tri b 2,
      tri a 0 * tri b 2 + tri a 1 * tri b 1 + tri a 2 * tri b 0 + tri a 2 * tri b 2] := by
  decide +kernel

private noncomputable def ev {K : Type} [Field K] [CharP K 2] (ω : K) (a : F8) : K :=
  φ2 (tri a 0) + φ2 (tri a 1) * ω + φ2 (tri a 2) * ω ^ 2

private theorem ev_add {K : Type} [Field K] [CharP K 2] (ω : K) (a b : F8) :
    ev ω (f8add a b) = ev ω a + ev ω b := by
  simp only [ev, tri_add, Pi.add_apply, map_add]
  ring

private theorem ev_mul {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (a b : F8) :
    ev ω (f8mul a b) = ev ω a * ev ω b := by
  simp only [ev, tri_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_mul]
  linear_combination (-(φ2 (tri a 1) * φ2 (tri b 2) + φ2 (tri a 2) * φ2 (tri b 1)) -
    φ2 (tri a 2) * φ2 (tri b 2) * ω) * hω

private theorem ev_zero {K : Type} [Field K] [CharP K 2] (ω : K) : ev ω 0 = 0 := by
  have : tri 0 = 0 := by decide +kernel
  simp [ev, this]

private theorem ev_one {K : Type} [Field K] [CharP K 2] (ω : K) : ev ω 1 = 1 := by
  have : tri 1 = ![1, 0, 0] := by decide +kernel
  simp [ev, this]

private abbrev M8 : Type := Fin 8 → Fin 8 → F8

private def mmul (A B : M8) : M8 := fun i j =>
  (List.finRange 8).foldl (fun s k => f8add s (f8mul (A i k) (B k j))) 0

private def madd (A B : M8) : M8 := fun i j => f8add (A i j) (B i j)

private def eye : M8 := fun i j => if i = j then 1 else 0

private def mpow (S : M8) : ℕ → M8
  | 0 => eye
  | n + 1 => mmul S (mpow S n)

private noncomputable def evMat {K : Type} [Field K] [CharP K 2] (ω : K) (A : M8) :
    Matrix (Fin 8) (Fin 8) K := Matrix.of fun i j => ev ω (A i j)

private theorem ev_foldl {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (g : Fin 8 → F8) :
    ∀ (l : List (Fin 8)) (s : F8),
      ev ω (l.foldl (fun s k => f8add s (g k)) s) = ev ω s + (l.map fun k => ev ω (g k)).sum
  | [], s => by simp
  | k :: l, s => by
    rw [List.foldl_cons, ev_foldl hω g l, ev_add, List.map_cons, List.sum_cons, add_assoc]

private theorem evMat_mmul {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (A B : M8) :
    evMat ω (mmul A B) = evMat ω A * evMat ω B := by
  ext i j
  simp only [evMat, mmul, Matrix.of_apply, Matrix.mul_apply]
  rw [ev_foldl hω, ev_zero, zero_add, Fin.sum_univ_def]
  simp only [ev_mul hω]

private theorem evMat_madd {K : Type} [Field K] [CharP K 2] (ω : K) (A B : M8) :
    evMat ω (madd A B) = evMat ω A + evMat ω B := by
  ext i j
  simp only [evMat, madd, Matrix.of_apply, Matrix.add_apply, ev_add]

private theorem evMat_eye {K : Type} [Field K] [CharP K 2] (ω : K) : evMat ω eye = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [evMat, eye, ev_one]
  · simp [evMat, eye, h, ev_zero, Matrix.one_apply_ne h]

private theorem evMat_mpow {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (S : M8) :
    ∀ n : ℕ, evMat ω (mpow S n) = evMat ω S ^ n
  | 0 => by simp [mpow, evMat_eye]
  | n + 1 => by rw [mpow, evMat_mmul hω, evMat_mpow hω S n, pow_succ']

private def L1D4 : List (Fin Tag.D4.rank → ℤ) :=
  [![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
    ![1, 1, 1, 0], ![1, 1, 1, 1]]

private def ex (i : Fin Tag.D4.rank) : Fin Tag.D4.rank → ℤ := Pi.single i 1

private def Ef (γ : Fin Tag.D4.rank → ℤ) (e : F8) : M8 := fun i j =>
  f8add (if i = j then 1 else 0) (if L1D4.getD i 0 = γ + L1D4.getD j 0 then e else 0)

private theorem evMat_Ef {K : Type} [Field K] [CharP K 2] (ω : K) (γ : Fin Tag.D4.rank → ℤ) (e : F8) :
    evMat ω (Ef γ e) =
      (1 : Matrix (Fin 8) (Fin 8) K) + ev ω e • (nilpMat L1D4 8 γ : Matrix (Fin 8) (Fin 8) K) := by
  ext i j
  simp only [evMat, Ef, Matrix.of_apply, ev_add, Matrix.add_apply, Matrix.smul_apply, nilpMat,
    smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [ev_one, ev_zero]

private def Mw (e0 e1 e2 : F8) : M8 :=
  mmul (Ef (-ex 0) e0) (mmul (Ef (-ex 1) e1) (mmul (Ef (-ex 3) e2)
    (mmul (Ef (ex 0) 1) (mmul (Ef (ex 1) 1) (Ef (ex 3) 1)))))

private theorem chk1 : ∀ i j, mmul (Mw 2 4 6) (mpow (madd (Mw 2 4 6) eye) 7) i j = eye i j := by
  decide +kernel

private theorem chk2 : ∀ i j, mmul (Mw 2 6 4) (mpow (madd (Mw 2 6 4) eye) 7) i j = eye i j := by
  decide +kernel

private theorem chk0 : ∀ i j, mmul (Mw 2 2 2) (mpow (madd (Mw 2 2 2) eye) 7) i j = eye i j := by
  decide +kernel

private theorem Mw_inv {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) {e0 e1 e2 : F8}
    (hchk : ∀ i j, mmul (Mw e0 e1 e2) (mpow (madd (Mw e0 e1 e2) eye) 7) i j = eye i j) :
    (evMat ω (Mw e0 e1 e2) + 1) * (evMat ω (Mw e0 e1 e2) * (evMat ω (Mw e0 e1 e2) + 1) ^ 6) = 1 := by
  set M := evMat ω (Mw e0 e1 e2) with hM
  have h7 : M * (M + 1) ^ 7 = 1 := by
    have := congrArg (evMat ω) (funext fun i => funext fun j => hchk i j : _ = eye)
    rw [evMat_mmul hω, evMat_mpow hω, evMat_madd, evMat_eye] at this
    exact this
  have hc : (M + 1) * M = M * (M + 1) := by noncomm_ring
  calc (M + 1) * (M * (M + 1) ^ 6) = ((M + 1) * M) * (M + 1) ^ 6 := by rw [mul_assoc]
    _ = M * (M + 1) ^ 7 := by rw [hc, mul_assoc, ← pow_succ']
    _ = 1 := h7

theorem prod_pinnedX_mem_Pθ
    {τ : Tag} {K : Type} [Field K] :
    ∀ ws : List ((Fin τ.rank → ℤ) × K), (∀ p ∈ ws, IsRoot τ p.1 ∧ p.1 (iθ τ) = 0) →
      (ws.map fun p => pinnedX τ K p.1 p.2).prod ∈ Pθ τ K
  | [], _ => by simp [one_mem]
  | p :: w, hw => by
    simp only [List.map_cons, List.prod_cons]
    exact mul_mem (pinnedX_mem_Pθ (hw p List.mem_cons_self).1 (hw p List.mem_cons_self).2 p.2)
      (prod_pinnedX_mem_Pθ w fun r hr => hw r (List.mem_cons_of_mem _ hr))

theorem cvec_conj_prod
    {τ : Tag} {K : Type} [Field K] [CharP K 2] {d : ℕ} {L1 : List (Fin τ.rank → ℤ)}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hlen : L1.length = d) (hnd : L1.Nodup)
    (hdeg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ) :
    ∀ ws : List ((Fin τ.rank → ℤ) × K), (∀ p ∈ ws, IsRoot τ p.1 ∧ p.1 (iθ τ) = 0) →
      ∀ q ∈ Qθ τ K,
        cvec L1 d ((ws.map fun p => pinnedX τ K p.1 p.2).prod * q *
            ((ws.map fun p => pinnedX τ K p.1 p.2).prod)⁻¹) =
          ((ws.map fun p => (1 : Matrix (Fin d) (Fin d) K) +
            p.2 • (nilpMat L1 d p.1 : Matrix (Fin d) (Fin d) K)).prod).mulVec (cvec L1 d q)
  | [], _, q, _ => by simp
  | p :: w, hw, q, hq => by
    have hw' : ∀ r ∈ w, IsRoot τ r.1 ∧ r.1 (iθ τ) = 0 := fun r hr =>
      hw r (List.mem_cons_of_mem _ hr)
    have hP := prod_pinnedX_mem_Pθ (K := K) w hw'
    have e : ((p :: w).map fun p => pinnedX τ K p.1 p.2).prod * q *
          (((p :: w).map fun p => pinnedX τ K p.1 p.2).prod)⁻¹ =
        pinnedX τ K p.1 p.2 * ((w.map fun p => pinnedX τ K p.1 p.2).prod * q *
          (w.map fun p => pinnedX τ K p.1 p.2).prod⁻¹) * (pinnedX τ K p.1 p.2)⁻¹ := by
      simp only [List.map_cons, List.prod_cons]
      group
    rw [e, cvec_conj_param hτ hlen hnd hdeg1 (hw p List.mem_cons_self) p.2 (conj_mem_Qθ hP hq),
      cvec_conj_prod hτ hlen hnd hdeg1 w hw' q hq, Matrix.mulVec_mulVec]
    simp only [List.map_cons, List.prod_cons]

private def wsOf {K : Type} [Field K] (a b c : K) : List ((Fin Tag.D4.rank → ℤ) × K) :=
  [(-ex 0, a), (-ex 1, b), (-ex 3, c), (ex 0, 1), (ex 1, 1), (ex 3, 1)]

private theorem wsOf_roots {K : Type} [Field K] (a b c : K) :
    ∀ p ∈ wsOf a b c, IsRoot Tag.D4 p.1 ∧ p.1 (iθ Tag.D4) = 0 := by
  have h6 : ∀ γ ∈ [-ex 0, -ex 1, -ex 3, ex 0, ex 1, ex 3],
      γ ∈ rootFinset Tag.D4 ∧ γ (iθ Tag.D4) = 0 := by decide +kernel
  intro p hp
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact gam_of_check h6 _ (by simp)

private theorem orbit_D4_facts :
    (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 ∧
    (TwistTag.D4.perm ^ 0) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = 0 ∧
    (TwistTag.D4.perm ^ 1) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = 1 ∧
    (TwistTag.D4.perm ^ 2) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = 3 := by
  decide +kernel

private theorem coe_orbitX_D4
    {K : Type} [Field K] (σ : K →+* K) (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    ((orbitX TwistTag.D4 K σ ⟨0, by decide⟩ c : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) =
      xUnit TwistTag.D4.tag K 0 (c : K) * xUnit TwistTag.D4.tag K 1 (σ (c : K)) *
        xUnit TwistTag.D4.tag K 3 (σ (σ (c : K))) := by
  obtain ⟨c0, p0, p1, p2⟩ := orbit_D4_facts
  have hσ0 : ∀ x : K, (σ ^ 0) x = x := fun x => rfl
  have hσ1 : ∀ x : K, (σ ^ 1) x = σ x := fun x => by rw [pow_one]
  have hσ2 : ∀ x : K, (σ ^ 2) x = σ (σ x) := fun x => by rw [pow_two]; rfl
  rw [coe_orbitX, c0]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, p0, p1, p2,
    hσ0, hσ1, hσ2]

private theorem coe_orbitY_D4
    {K : Type} [Field K] (σ : K →+* K) (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    ((orbitY TwistTag.D4 K σ ⟨0, by decide⟩ c : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) =
      yUnit TwistTag.D4.tag K 0 (c : K) * yUnit TwistTag.D4.tag K 1 (σ (c : K)) *
        yUnit TwistTag.D4.tag K 3 (σ (σ (c : K))) := by
  obtain ⟨c0, p0, p1, p2⟩ := orbit_D4_facts
  have hσ0 : ∀ x : K, (σ ^ 0) x = x := fun x => rfl
  have hσ1 : ∀ x : K, (σ ^ 1) x = σ x := fun x => by rw [pow_one]
  have hσ2 : ∀ x : K, (σ ^ 2) x = σ (σ x) := fun x => by rw [pow_two]; rfl
  rw [coe_orbitY, c0]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, p0, p1, p2,
    hσ0, hσ1, hσ2]

private theorem mem_orbitField_D4 {K : Type} [Field K] (σ : K →+* K) {ω : K}
    (hω3 : σ (σ (σ ω)) = ω) : ω ∈ orbitField TwistTag.D4 K σ ⟨0, by decide⟩ := by
  rw [mem_orbitField, orbit_D4_facts.1]
  simpa [pow_succ] using hω3

private theorem wsOf_prod_eq
    {K : Type} [Field K] (σ : K →+* K) {ω : K} (hω3 : σ (σ (σ ω)) = ω) :
    ((wsOf ω (σ ω) (σ (σ ω))).map fun p => pinnedX Tag.D4 K p.1 p.2).prod =
      ((orbitY TwistTag.D4 K σ ⟨0, by decide⟩ ⟨ω, mem_orbitField_D4 σ hω3⟩ :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) *
        ((orbitX TwistTag.D4 K σ ⟨0, by decide⟩ ⟨1, one_mem _⟩ :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
  rw [coe_orbitY_D4, coe_orbitX_D4]
  simp only [wsOf, ex, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pinnedX_single, pinnedX_neg_single, map_one, mul_assoc]
  rfl

private theorem cubic_root_cases {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1)
    {x : K} (hx : x ^ 3 = x + 1) : x = ω ∨ x = ω ^ 2 ∨ x = ω ^ 4 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h : (x - ω) * ((x - ω ^ 2) * (x - ω ^ 4)) = 0 := by
    linear_combination hx + (-1 - ω - ω ^ 2 - ω ^ 4 + 3 * x + x * ω + x * ω ^ 2 + x * ω ^ 3 -
      x ^ 2 * ω) * hω + (-ω - ω ^ 2 + 2 * x + 2 * x * ω + x * ω ^ 2 - x ^ 2 * ω - x ^ 2 * ω ^ 2) * h2
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h))

private theorem ev_two {K : Type} [Field K] [CharP K 2] (ω : K) : ev ω 2 = ω := by
  have : tri 2 = ![0, 1, 0] := by decide +kernel
  simp [ev, this]

private theorem ev_four {K : Type} [Field K] [CharP K 2] (ω : K) : ev ω 4 = ω ^ 2 := by
  have : tri 4 = ![0, 0, 1] := by decide +kernel
  simp [ev, this]

private theorem ev_six {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) :
    ev ω 6 = ω ^ 4 := by
  have : tri 6 = ![0, 1, 1] := by decide +kernel
  simp [ev, this]
  linear_combination (-ω) * hω

private theorem triD4_core
    {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (σ : K →+* K)
    (hσ3 : σ (σ (σ ω)) = ω) {e0 e1 e2 : F8} (h0 : ev ω e0 = ω) (h1 : ev ω e1 = σ ω)
    (h2 : ev ω e2 = σ (σ ω))
    (hchk : ∀ i j, mmul (Mw e0 e1 e2) (mpow (madd (Mw e0 e1 e2) eye) 7) i j = eye i j) :
    ∃ h ∈ Pθ .D4 K ⊓ graphFixedRootGroup TwistTag.D4 K σ, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .D4 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .D4 K → q ∈ Uθ .D4 K := by
  have hroots := wsOf_roots ω (σ ω) (σ (σ ω))
  have hlen : L1D4.length = 8 := by decide
  have hdeg1 : ∀ α, α ∈ L1D4 ↔ α ∈ Deg1 Tag.D4 := deg1_of_filter (by decide +kernel)
  have hnd : L1D4.Nodup := by decide +kernel
  have hP := prod_pinnedX_mem_Pθ (K := K) _ hroots
  have hS : ((wsOf ω (σ ω) (σ (σ ω))).map fun p => pinnedX Tag.D4 K p.1 p.2).prod ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
    rw [wsOf_prod_eq σ hσ3]
    exact mul_mem
      (graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ σ _ _))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ σ _ _))
  have hconj := cvec_conj_prod (K := K) (Or.inl rfl) hlen hnd hdeg1 _ hroots
  have hW : ((wsOf ω (σ ω) (σ (σ ω))).map fun p => (1 : Matrix (Fin 8) (Fin 8) K) +
      p.2 • (nilpMat L1D4 8 p.1 : Matrix (Fin 8) (Fin 8) K)).prod = evMat ω (Mw e0 e1 e2) := by
    simp only [wsOf, Mw, evMat_mmul hω, evMat_Ef, h0, h1, h2, ev_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  exact exists_odd_fpf_of_conj (L1 := L1D4) hlen hdeg1 hP _ hS (Mw_inv hω hchk)
    (fun q hq => by rw [hconj q hq, hW])

theorem triD4_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 3 = ω + 1) (σ : K →+* K) :
    ∃ h ∈ Pθ .D4 K ⊓ graphFixedRootGroup TwistTag.D4 K σ, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .D4 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .D4 K → q ∈ Uθ .D4 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h7 : ω ^ 7 = 1 := by
    linear_combination (1 + ω + ω ^ 2 + ω ^ 4) * hω + (ω + ω ^ 2) * h2
  have hσx : (σ ω) ^ 3 = σ ω + 1 := by rw [← map_pow, hω, map_add, map_one]
  rcases cubic_root_cases hω hσx with h | h | h
  · have h2' : σ (σ ω) = ω := by rw [h, h]
    have h3' : σ (σ (σ ω)) = ω := by rw [h, h, h]
    exact triD4_core hω σ h3' (e0 := 2) (e1 := 2) (e2 := 2) (ev_two ω) (by rw [ev_two, h])
      (by rw [ev_two, h2']) chk0
  · have h2' : σ (σ ω) = ω ^ 4 := by rw [h, map_pow, h]; ring
    have h3' : σ (σ (σ ω)) = ω := by
      rw [h2', map_pow, h]
      linear_combination ω * h7
    exact triD4_core hω σ h3' (e0 := 2) (e1 := 4) (e2 := 6) (ev_two ω) (by rw [ev_four, h])
      (by rw [ev_six hω, h2']) chk1
  · have h2' : σ (σ ω) = ω ^ 2 := by
      rw [h, map_pow, h]
      linear_combination ω ^ 2 * (ω ^ 7 + 1) * h7
    have h3' : σ (σ (σ ω)) = ω := by
      rw [h2', map_pow, h]
      linear_combination ω * h7
    exact triD4_core hω σ h3' (e0 := 2) (e1 := 6) (e2 := 4) (ev_two ω) (by rw [ev_six hω, h])
      (by rw [ev_four, h2']) chk2

theorem exists_cubic_root_of_card {K : Type} [Field K] [Finite K] [CharP K 2] (g : ℕ)
    (hK : Nat.card K = 2 ^ (3 * g)) : ∃ ω : K, ω ^ 3 = ω + 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card Kˣ := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 3) 1 g
    rw [Nat.card_units, hK, pow_mul]
    norm_num at this ⊢
    exact this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hx7 : (x : K) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg (fun y : Kˣ => (y : K)) h
  have hx1 : (x : K) ≠ 1 := by
    intro h
    have hx' : x = 1 := Units.ext h
    rw [hx', orderOf_one] at hx
    norm_num at hx
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h : ((x : K) - 1) * (((x : K) ^ 3 + x + 1) * ((x : K) ^ 3 + (x : K) ^ 2 + 1)) = 0 := by
    linear_combination hx7 + ((x : K) ^ 4 - (x : K) ^ 3) * h2
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hx1
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨x, by linear_combination h + (-((x : K) + 1)) * h2⟩
    · have hx0 : (x : K) ≠ 0 := x.ne_zero
      refine ⟨(x : K)⁻¹, ?_⟩
      field_simp
      linear_combination (-1 : K) * h + h2

theorem triD4_exists_odd_fpf_of_card
    (K : Type) [Field K] [Finite K] [CharP K 2] (g : ℕ) (hK : Nat.card K = 2 ^ (3 * g))
    (σ : K →+* K) :
    ∃ h ∈ Pθ .D4 K ⊓ graphFixedRootGroup TwistTag.D4 K σ, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .D4 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .D4 K → q ∈ Uθ .D4 K :=
  triD4_exists_odd_fpf K (exists_cubic_root_of_card g hK).choose_spec σ

end CFSG.StandardType.LieKnownR2.LinkTriD4

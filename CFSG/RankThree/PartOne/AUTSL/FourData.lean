module

public import CFSG.RankThree.PartOne.AUTSL.FourPlane

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Matrix Equiv CFSG.RankThree.PartOne.KF1514B
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section Basics

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

include c in
theorem b_ne_zero : b ≠ 0 := by
  intro hb
  have hK : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hK c
  apply AnisoPair.hirr (b := b) (c := c) s
  rw [hb, hs]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination s * s * h2

@[expose] def planeVec (x : Fin 3) (a : Fin 2 → K) : PV K := (Pi.single x a, 0)

@[expose] def injP (x : Fin 3) : (Fin 2 → K) →ₗ[K] PV K :=
  (LinearMap.inl K (Fin 3 → (Fin 2 → K)) (Fin 2 → K)).comp
    (LinearMap.single K (fun _ : Fin 3 => Fin 2 → K) x)

@[expose] def projP (x : Fin 3) : PV K →ₗ[K] (Fin 2 → K) :=
  (LinearMap.proj x).comp (LinearMap.fst K (Fin 3 → (Fin 2 → K)) (Fin 2 → K))

theorem projP_apply (x : Fin 3) (v : PV K) : projP x v = v.1 x := rfl

theorem projP_planeVec (x : Fin 3) (a : Fin 2 → K) : projP x (planeVec x a) = a := by
  simp [projP_apply, planeVec]

theorem projP_planeVec_ne {x y : Fin 3} (h : y ≠ x) (a : Fin 2 → K) :
    projP y (planeVec x a) = 0 := by
  simp [projP_apply, planeVec, Pi.single_eq_of_ne h]

theorem planeVec_add (x : Fin 3) (a a' : Fin 2 → K) :
    planeVec x (a + a') = planeVec x a + planeVec x a' := by
  simp [planeVec, Pi.single_add]

theorem planeVec_smul (x : Fin 3) (r : K) (a : Fin 2 → K) :
    planeVec x (r • a) = r • planeVec x a := by
  ext i
  · by_cases hx : i = x
    · subst hx
      simp [planeVec]
    · simp [planeVec, Pi.single_eq_of_ne hx]
  · simp [planeVec]

theorem dh_planeVec (t : Pt b c p) (x : Fin 3) (a : Fin 2 → K) :
    dh b c p t (planeVec x a) = planeVec x ((tg t x : Matrix (Fin 2) (Fin 2) K).mulVec a) := by
  rw [dh_apply, diagEquiv_apply]
  refine Prod.ext (funext fun y => ?_) rfl
  by_cases hx : y = x
  · subst hx
    simp [planeVec]
  · simp [planeVec, Pi.single_eq_of_ne hx]

theorem dh_snd (t : Pt b c p) (v : PV K) : (dh b c p t v).2 = v.2 := rfl

theorem dh_fst (t : Pt b c p) (v : PV K) (y : Fin 3) :
    (dh b c p t v).1 y = (tg t y : Matrix (Fin 2) (Fin 2) K).mulVec (v.1 y) := rfl

end Basics

section Hop

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem mulVec_eq_zero_of_unit (g : GL (Fin 2) K) {w : Fin 2 → K}
    (h : (g : Matrix (Fin 2) (Fin 2) K).mulVec w = 0) : w = 0 := by
  have h1 : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
      ((g : Matrix (Fin 2) (Fin 2) K).mulVec w) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  exact h1

variable (b c p) in
@[expose] noncomputable def Hop (x : Fin 3) (d : Pt b c p) : PV K →ₗ[K] PV K :=
  ((dh b c p d).toLinearMap ∘ₗ (dh b c p d).toLinearMap) +
    (b * sT (tg d x)) • (dh b c p d).toLinearMap + LinearMap.id

theorem Hop_apply (x : Fin 3) (d : Pt b c p) (v : PV K) :
    Hop b c p x d v = dh b c p d (dh b c p d v) + (b * sT (tg d x)) • dh b c p d v + v := rfl

theorem Hop_fst (x : Fin 3) (d : Pt b c p) (v : PV K) (y : Fin 3) :
    (Hop b c p x d v).1 y =
      (b * (sT (tg d x) + sT (tg d y))) • (tg d y : Matrix (Fin 2) (Fin 2) K).mulVec (v.1 y) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq := Tns_sq_vec (tg_mem_Tns d y) (v.1 y)
  rw [Hop_apply]
  funext i
  have h := congrFun hsq i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
  simp only [Prod.fst_add, Prod.smul_fst, dh_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h -
    (b * sT (tg d y) * (tg d y : Matrix (Fin 2) (Fin 2) K).mulVec (v.1 y) i) * h2

theorem Hop_snd (x : Fin 3) (d : Pt b c p) (v : PV K) :
    (Hop b c p x d v).2 = (b * sT (tg d x)) • v.2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Hop_apply]
  funext i
  simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dh_snd]
  linear_combination v.2 i * h2

end Hop

section Tx

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

variable (b c p) in
@[expose] noncomputable def Tx (D : Subgroup (Pt b c p)) (x : Fin 3) : Submodule K (PV K) :=
  ⨅ d ∈ D, LinearMap.ker (Hop b c p x d)

theorem mem_Tx {D : Subgroup (Pt b c p)} {x : Fin 3} {v : PV K} :
    v ∈ Tx b c p D x ↔ ∀ d ∈ D, Hop b c p x d v = 0 := by
  simp [Tx, Submodule.mem_iInf, LinearMap.mem_ker]

@[expose] def ZeroOn (D : Subgroup (Pt b c p)) (x : Fin 3) : Prop := ∀ d ∈ D, d x = 1

@[expose] def RelOn (D : Subgroup (Pt b c p)) (x y : Fin 3) : Prop :=
  ∀ d ∈ D, sT (tg d x) = sT (tg d y)

theorem sT_tg_ne_zero {t : Pt b c p} {x : Fin 3} (h : t x ≠ 1) : sT (tg t x) ≠ 0 := by
  refine Tns_s_ne_zero (tg_mem_Tns t x) fun h1 => h (Subtype.ext h1)

theorem exists_sT_ne_zero {D : Subgroup (Pt b c p)} {x : Fin 3} (h : ¬ ZeroOn D x) :
    ∃ d ∈ D, sT (tg d x) ≠ 0 := by
  unfold ZeroOn at h
  push Not at h
  obtain ⟨d, hd, hdx⟩ := h
  exact ⟨d, hd, sT_tg_ne_zero hdx⟩

theorem Tx_invariant {D : Subgroup (Pt b c p)} {x : Fin 3} {g : PV K ≃ₗ[K] PV K}
    (hg : ∀ d ∈ D, g * dh b c p d = dh b c p d * g) {v : PV K} (hv : v ∈ Tx b c p D x) :
    g v ∈ Tx b c p D x := by
  rw [mem_Tx] at hv ⊢
  intro d hd
  have hcomm : ∀ w, g (dh b c p d w) = dh b c p d (g w) := fun w =>
    congrArg (fun e : PV K ≃ₗ[K] PV K => e w) (hg d hd)
  have h1 : Hop b c p x d (g v) = g (Hop b c p x d v) := by
    simp only [Hop_apply, map_add, map_smul, hcomm]
  rw [h1, hv d hd, map_zero]

theorem Tx_fst_zero {D : Subgroup (Pt b c p)} {x y : Fin 3}
    (hxy : ∃ d ∈ D, sT (tg d x) ≠ sT (tg d y)) {v : PV K} (hv : v ∈ Tx b c p D x) :
    v.1 y = 0 := by
  obtain ⟨d, hd, hne⟩ := hxy
  have h := mem_Tx.1 hv d hd
  have h1 := congrArg (fun w : PV K => w.1 y) h
  simp only [Hop_fst, Prod.fst_zero, Pi.zero_apply] at h1
  have hscal : b * (sT (tg d x) + sT (tg d y)) ≠ 0 := by
    refine mul_ne_zero (b_ne_zero (c := c)) fun h0 => hne ?_
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h0 - sT (tg d y) * h2
  have h2 := (smul_eq_zero.1 h1).resolve_left hscal
  exact mulVec_eq_zero_of_unit (tg d y) h2

theorem Tx_snd_zero {D : Subgroup (Pt b c p)} {x : Fin 3}
    (hx : ∃ d ∈ D, sT (tg d x) ≠ 0) {v : PV K} (hv : v ∈ Tx b c p D x) : v.2 = 0 := by
  obtain ⟨d, hd, hne⟩ := hx
  have h := mem_Tx.1 hv d hd
  have h1 := congrArg (fun w : PV K => w.2) h
  simp only [Hop_snd, Prod.snd_zero] at h1
  exact (smul_eq_zero.1 h1).resolve_left (mul_ne_zero (b_ne_zero (c := c)) hne)

theorem planeVec_mem_Tx {D : Subgroup (Pt b c p)} {x y : Fin 3} (hxy : RelOn D x y)
    (a : Fin 2 → K) : planeVec y a ∈ Tx b c p D x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [mem_Tx]
  intro d hd
  refine Prod.ext (funext fun y' => ?_) ?_
  · rw [Hop_fst]
    by_cases hy : y' = y
    · subst hy
      have : sT (tg d x) + sT (tg d y') = 0 := by
        rw [hxy d hd]
        linear_combination sT (tg d y') * h2
      simp [planeVec, this]
    · simp [planeVec, Pi.single_eq_of_ne hy]
  · rw [Hop_snd]
    simp [planeVec]

end Tx

section Triv

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

variable (x : Fin 3) in
@[expose] def phi (g : PV K ≃ₗ[K] PV K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (projP x).comp (g.toLinearMap.comp (injP x))

theorem phi_apply (x : Fin 3) (g : PV K ≃ₗ[K] PV K) (a : Fin 2 → K) :
    phi x g a = (g (planeVec x a)).1 x := rfl

theorem planeVec_phi {D : Subgroup (Pt b c p)} {x : Fin 3} (hx : ¬ ZeroOn D x)
    (hxy : ∀ y, y ≠ x → ∃ d ∈ D, sT (tg d x) ≠ sT (tg d y)) {g : PV K ≃ₗ[K] PV K}
    (hg : ∀ d ∈ D, g * dh b c p d = dh b c p d * g) (a : Fin 2 → K) :
    g (planeVec x a) = planeVec x (phi x g a) := by
  have hmem : g (planeVec x a) ∈ Tx b c p D x :=
    Tx_invariant hg (planeVec_mem_Tx (fun d _ => rfl) a)
  refine Prod.ext (funext fun y => ?_) ?_
  · by_cases hy : y = x
    · subst hy
      simp [planeVec, phi_apply]
    · have h0 := Tx_fst_zero (c := c) (hxy y hy) hmem
      show (g (planeVec x a)).1 y = (Pi.single x (phi x g a) : Fin 3 → Fin 2 → K) y
      rw [h0, Pi.single_eq_of_ne hy]
  · have h0 := Tx_snd_zero (c := c) (exists_sT_ne_zero hx) hmem
    simpa [planeVec] using h0

theorem phi_one (x : Fin 3) : phi x (1 : PV K ≃ₗ[K] PV K) = LinearMap.id := by
  ext a
  simp [phi_apply, planeVec]

theorem phi_mul {D : Subgroup (Pt b c p)} {x : Fin 3} (hx : ¬ ZeroOn D x)
    (hxy : ∀ y, y ≠ x → ∃ d ∈ D, sT (tg d x) ≠ sT (tg d y)) {g h : PV K ≃ₗ[K] PV K}
    (hg : ∀ d ∈ D, g * dh b c p d = dh b c p d * g)
    (hh : ∀ d ∈ D, h * dh b c p d = dh b c p d * h) (a : Fin 2 → K) :
    phi x (g * h) a = phi x g (phi x h a) := by
  have h1 : (g * h) (planeVec x a) = planeVec x (phi x g (phi x h a)) := by
    rw [LinearEquiv.mul_apply, planeVec_phi hx hxy hh, planeVec_phi hx hxy hg]
  rw [phi_apply, h1, planeVec]
  simp

theorem phi_commutes {D : Subgroup (Pt b c p)} {x : Fin 3} (hx : ¬ ZeroOn D x)
    (hxy : ∀ y, y ≠ x → ∃ d ∈ D, sT (tg d x) ≠ sT (tg d y)) {g : PV K ≃ₗ[K] PV K}
    (hg : ∀ d ∈ D, g * dh b c p d = dh b c p d * g) {d : Pt b c p} (hd : d ∈ D)
    (a : Fin 2 → K) :
    phi x g ((tg d x : Matrix (Fin 2) (Fin 2) K).mulVec a) =
      (tg d x : Matrix (Fin 2) (Fin 2) K).mulVec (phi x g a) := by
  have h1 : g (dh b c p d (planeVec x a)) = dh b c p d (g (planeVec x a)) :=
    congrArg (fun e : PV K ≃ₗ[K] PV K => e (planeVec x a)) (hg d hd)
  rw [dh_planeVec, planeVec_phi hx hxy hg, planeVec_phi hx hxy hg, dh_planeVec] at h1
  have h2 := congrArg (projP x) h1
  rw [projP_planeVec, projP_planeVec] at h2
  exact h2

end Triv

section TrivPlane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

@[expose] def fixPlane (x : Fin 3) : Subgroup (PV K ≃ₗ[K] PV K) where
  carrier := {g | ∀ a, g (planeVec x a) = planeVec x a}
  one_mem' := fun _ => rfl
  mul_mem' := fun {g h} hg hh a => by
    rw [LinearEquiv.mul_apply, hh a, hg a]
  inv_mem' := fun {g} hg a => by
    have := congrArg g.symm (hg a)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this.symm

theorem mem_fixPlane {x : Fin 3} {g : PV K ≃ₗ[K] PV K} :
    g ∈ fixPlane x ↔ ∀ a, g (planeVec x a) = planeVec x a := Iff.rfl

theorem triv_plane {D : Subgroup (Pt b c p)} {x : Fin 3} (hx : ¬ ZeroOn D x)
    (hxy : ∀ y, y ≠ x → ∃ d ∈ D, sT (tg d x) ≠ sT (tg d y))
    (J : Subgroup (PV K ≃ₗ[K] PV K))
    (hJc : ∀ j ∈ J, ∀ d ∈ D, j * dh b c p d = dh b c p d * j) (hJ : ⁅J, J⁆ = J) :
    J ≤ fixPlane x := by
  obtain ⟨d₀, hd₀, hs₀⟩ := exists_sT_ne_zero hx
  have hg₀1 : tg d₀ x ≠ 1 := fun h => hs₀ (by simp [sT, h])
  have hg₀ : tg d₀ x ∈ Tns b c := tg_mem_Tns d₀ x
  have hphi : ∀ g ∈ J, ∀ a, g (planeVec x a) = planeVec x (phi x g a) :=
    fun g hg a => planeVec_phi hx hxy (hJc g hg) a
  have hcom : ∀ g ∈ J, ∀ g' ∈ J, ∀ a, phi x g (phi x g' a) = phi x g' (phi x g a) := by
    intro g hg g' hg' a
    exact comm_of_commutes hg₀ hg₀1 (φ := phi x g) (ψ := phi x g')
      (fun v => phi_commutes hx hxy (hJc g hg) hd₀ v)
      (fun v => phi_commutes hx hxy (hJc g' hg') hd₀ v) a
  have hinv : ∀ g ∈ J, ∀ a, phi x g (phi x g⁻¹ a) = a := by
    intro g hg a
    have h1 := phi_mul hx hxy (hJc g hg) (hJc g⁻¹ (inv_mem hg)) a
    rw [mul_inv_cancel, phi_one] at h1
    exact h1.symm
  have hle : ⁅J, J⁆ ≤ fixPlane x := by
    rw [Subgroup.commutator_le]
    intro j hj j' hj' a
    have hj1 := inv_mem hj
    have hj'1 := inv_mem hj'
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
    rw [hphi _ hj'1, hphi _ hj1, hphi _ hj', hphi _ hj]
    congr 1
    rw [hcom j' hj' j⁻¹ hj1, hinv j hj, hinv j' hj']
  rw [hJ] at hle
  exact hle

end TrivPlane

section CaseS

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

variable (b c p) in
@[expose] def kerEval (k : Fin 3) : Subgroup (Pt b c p) :=
  (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(Tp b c p)) k).ker

theorem mem_kerEval {k : Fin 3} {t : Pt b c p} : t ∈ kerEval b c p k ↔ t k = 1 := Iff.rfl

theorem card_kerEval (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (k : Fin 3) :
    Nat.card (kerEval b c p k) = p ^ 2 := by
  have hsurj : Function.Surjective (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(Tp b c p)) k) :=
    fun g => ⟨Pi.mulSingle k g, by simp⟩
  have hrange : (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(Tp b c p)) k).range = ⊤ :=
    MonoidHom.range_eq_top.2 hsurj
  have h1 := Subgroup.card_mul_index (kerEval b c p k)
  rw [kerEval, Subgroup.index_ker, hrange, Subgroup.card_top, card_Tp hp hpq,
    card_Pt hp hpq] at h1
  refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
  show Nat.card ↥(Pi.evalMonoidHom (fun _ : Fin 3 => ↥(Tp b c p)) k).ker * p = p ^ 2 * p
  rw [h1]
  ring

theorem eq_kerEval_of_zero (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {D : Subgroup (Pt b c p)} (hcard : Nat.card D = p ^ 2) {k : Fin 3} (hk : ZeroOn D k) :
    D = kerEval b c p k := by
  have hle : D ≤ kerEval b c p k := fun d hd => hk d hd
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_kerEval hp hpq, hcard])

theorem kerEval_eq_iSup (k : Fin 3) :
    kerEval b c p k = ⨆ y, ⨆ (_ : y ≠ k), linePt b c p y := by
  apply le_antisymm
  · intro t ht
    have h : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
      funext x
      fin_cases x <;> simp [Pi.mul_apply]
    have hmem : ∀ y : Fin 3, Pi.mulSingle y (t y) ∈ ⨆ y, ⨆ (_ : y ≠ k), linePt b c p y := by
      intro y
      by_cases hy : y = k
      · subst hy
        rw [mem_kerEval.1 ht]
        simp
      · exact Subgroup.mem_iSup_of_mem y (Subgroup.mem_iSup_of_mem hy ⟨t y, rfl⟩)
    rw [h]
    exact mul_mem (mul_mem (hmem 0) (hmem 1)) (hmem 2)
  · refine iSup₂_le fun y hy => ?_
    rintro _ ⟨g, rfl⟩
    show (Pi.mulSingle y g : Fin 3 → ↥(Tp b c p)) k = 1
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) (Ne.symm hy) g

theorem separated_of_kerEval (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {k i : Fin 3}
    (hik : i ≠ k) :
    ¬ ZeroOn (kerEval b c p k) i ∧
      ∀ y, y ≠ i → ∃ d ∈ kerEval b c p k, sT (tg d i) ≠ sT (tg d y) := by
  have hnt : Nontrivial (Tp b c p) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Tp hp hpq]; exact hp.one_lt)
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : Tp b c p)
  have hd : (Pi.mulSingle i g₀ : Pt b c p) ∈ kerEval b c p k := by
    rw [mem_kerEval]
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) (Ne.symm hik) g₀
  have hs : sT ((g₀ : Tp b c p) : GL (Fin 2) K) ≠ 0 :=
    Tns_s_ne_zero g₀.2.1 (fun h => hg₀ (Subtype.ext h))
  refine ⟨fun h => ?_, fun y hy => ⟨_, hd, ?_⟩⟩
  · have := h _ hd
    rw [Pi.mulSingle_eq_same] at this
    exact hg₀ this
  · have h1 : tg (Pi.mulSingle i g₀ : Pt b c p) i = (g₀ : Tp b c p) := by
      simp [tg]
    have h2 : tg (Pi.mulSingle i g₀ : Pt b c p) y = 1 := by
      simp [tg, Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) hy]
    rw [h1, h2]
    intro h
    apply hs
    rw [h]
    simp [sT]

end CaseS

section CaseS2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem eq_one_of_fix_plane {t : Pt b c p} {x : Fin 3}
    (h : ∀ a, dh b c p t (planeVec x a) = planeVec x a) : t x = 1 := by
  by_contra hne
  have h1 : tg t x ≠ 1 := fun h1 => hne (Subtype.ext h1)
  have h2 : (tg t x : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    have := congrArg (projP x) (h (Pi.single 0 1))
    rwa [dh_planeVec, projP_planeVec, projP_planeVec] at this
  have h3 := Tns_fix (tg_mem_Tns t x) h1 h2
  have := congrFun h3 0
  simp at this

theorem caseS_conclusion (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {D : Subgroup (Pt b c p)} (hcard : Nat.card D = p ^ 2) {k : Fin 3} (hk : ZeroOn D k)
    (J : Subgroup (PV K ≃ₗ[K] PV K))
    (hJc : ∀ j ∈ J, ∀ d ∈ D, j * dh b c p d = dh b c p d * j) (hJ : ⁅J, J⁆ = J) :
    D.map (dh b c p) = ⨆ y, ⨆ (_ : y ≠ k), lineSub b c p y ∧ J ⊓ E0 b c p ≤ lineSub b c p k := by
  have hD := eq_kerEval_of_zero hp hpq hcard hk
  refine ⟨?_, ?_⟩
  · rw [hD, kerEval_eq_iSup]
    simp only [Subgroup.map_iSup, lineSub_eq_map]
  · rintro e ⟨heJ, t, rfl⟩
    have hfix : ∀ y, y ≠ k → t y = 1 := by
      intro y hy
      obtain ⟨h0, h1⟩ := separated_of_kerEval (b := b) (c := c) hp hpq hy
      rw [← hD] at h0 h1
      have := triv_plane h0 h1 J hJc hJ heJ
      exact eq_one_of_fix_plane (mem_fixPlane.1 this)
    have ht : t = Pi.mulSingle k (t k) := by
      funext y
      by_cases hy : y = k
      · subst hy
        simp
      · rw [Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) hy, hfix y hy]
    rw [ht]
    exact ⟨t k, rfl⟩

end CaseS2

section Contra

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem eq_sum_planeVec (v : PV K) :
    v = planeVec 0 (v.1 0) + planeVec 1 (v.1 1) + planeVec 2 (v.1 2) + (0, v.2) := by
  refine Prod.ext (funext fun y => ?_) ?_
  · fin_cases y <;> simp [planeVec]
  · simp [planeVec]

theorem apply_of_fix_planes {s : PV K ≃ₗ[K] PV K} (hs : ∀ x a, s (planeVec x a) = planeVec x a)
    (hH : ∀ h : Fin 2 → K, (s ((0 : Fin 3 → Fin 2 → K), h)).1 = 0) (v : PV K) :
    s v = (v.1, (s ((0 : Fin 3 → Fin 2 → K), v.2)).2) := by
  conv_lhs => rw [eq_sum_planeVec v]
  simp only [map_add, hs]
  refine Prod.ext ?_ ?_
  · funext y
    have := hH v.2
    simp only [Prod.fst_add, Pi.add_apply, this]
    fin_cases y <;> simp [planeVec]
  · simp [planeVec]

theorem false_of_fix_planes {D : Subgroup (Pt b c p)} (hD : ∀ x, ¬ ZeroOn D x)
    (S : Subgroup (PV K ≃ₗ[K] PV K)) (hS1 : S ≠ ⊥) (hSE : S = ⁅S, E0 b c p⁆)
    (hSc : ∀ s ∈ S, ∀ d ∈ D, s * dh b c p d = dh b c p d * s)
    (hSf : ∀ s ∈ S, ∀ x a, s (planeVec x a) = planeVec x a) : False := by
  have hH : ∀ s ∈ S, ∀ h : Fin 2 → K, (s ((0 : Fin 3 → Fin 2 → K), h)).1 = 0 := by
    intro s hs h
    funext y
    obtain ⟨d, hd, hdy⟩ : ∃ d ∈ D, d y ≠ 1 := by
      have := hD y
      unfold ZeroOn at this
      push Not at this
      exact this
    have h1 : dh b c p d ((0 : Fin 3 → Fin 2 → K), h) = ((0 : Fin 3 → Fin 2 → K), h) := by
      refine Prod.ext (funext fun y' => ?_) rfl
      simp [dh_fst]
    have h2 : dh b c p d (s ((0 : Fin 3 → Fin 2 → K), h)) = s ((0 : Fin 3 → Fin 2 → K), h) := by
      have := congrArg (fun e : PV K ≃ₗ[K] PV K => e ((0 : Fin 3 → Fin 2 → K), h)) (hSc s hs d hd)
      simp only [LinearEquiv.mul_apply, h1] at this
      exact this.symm
    have h3 := congrFun (congrArg Prod.fst h2) y
    rw [dh_fst] at h3
    exact Tns_fix (tg_mem_Tns d y) (fun h' => hdy (Subtype.ext h')) h3
  have hcent : S ≤ Subgroup.centralizer (E0 b c p : Set (PV K ≃ₗ[K] PV K)) := by
    intro s hs e he
    obtain ⟨t, rfl⟩ := he
    have hsf := apply_of_fix_planes (hSf s hs) (hH s hs)
    refine LinearEquiv.ext fun v => ?_
    show dh b c p t (s v) = s (dh b c p t v)
    rw [hsf v, hsf (dh b c p t v), dh_snd]
    exact Prod.ext (funext fun y => rfl) rfl
  have : ⁅S, E0 b c p⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  exact hS1 (hSE.trans this)

end Contra

section Fixed

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [Finite V]

theorem two_dvd_card_of_ne_bot (W : Submodule K V) (h : W ≠ ⊥) : 2 ∣ Nat.card W := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W)]
  obtain ⟨n, hn, hcard⟩ := FiniteField.card K 2
  rw [hcard, ← pow_mul]
  have hr : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.2 h
  exact dvd_pow_self 2 (Nat.mul_pos n.pos hr).ne'

theorem exists_fixed_vector {S : Subgroup (V ≃ₗ[K] V)} (hS : IsPGroup 2 S) {W : Submodule K V}
    (hW0 : W ≠ ⊥) (hW : ∀ s ∈ S, ∀ w ∈ W, s w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ s ∈ S, s w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S W :=
    { smul := fun s w => ⟨s.1 w.1, hW s.1 s.2 w.1 w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun s s' w => Subtype.ext rfl }
  have hdvd := two_dvd_card_of_ne_bot (K := K) W hW0
  have h0 : (0 : W) ∈ MulAction.fixedPoints S W := fun s => Subtype.ext (map_zero s.1)
  obtain ⟨w, hw, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  refine ⟨w.1, w.2, fun h => hne (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hw ⟨s, hs⟩)

end Fixed

section QpAdd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem Qp_planeVec_add {x y : Fin 3} (hxy : x ≠ y) (a a' : Fin 2 → K) :
    Qp b c (planeVec x a + planeVec y a') =
      minusTailForm K b c a + minusTailForm K b c a' := by
  simp only [Qp, planeVec, Prod.fst_add, Prod.snd_add, add_zero, zero_mul, Pi.add_apply,
    Pi.zero_apply, Fin.sum_univ_three]
  fin_cases x <;> fin_cases y <;> simp_all <;> ring

theorem minusTailForm_eq_zero {a : Fin 2 → K} (h : minusTailForm K b c a = 0) : a = 0 :=
  anisotropic_minusTailForm (AnisoPair.hirr (b := b) (c := c)) a h

end QpAdd

section WAnalysis

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem fin3_cover : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ y, y = i ∨ y = j ∨ y = k := by
  decide

@[expose] def blk (x y : Fin 3) (g : PV K ≃ₗ[K] PV K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (projP x).comp (g.toLinearMap.comp (injP y))

theorem blk_apply (x y : Fin 3) (g : PV K ≃ₗ[K] PV K) (a : Fin 2 → K) :
    blk x y g a = (g (planeVec y a)).1 x := rfl

theorem blk_one (x : Fin 3) : blk x x (1 : PV K ≃ₗ[K] PV K) = LinearMap.id := phi_one x

theorem Qp_planeVec (x : Fin 3) (a : Fin 2 → K) :
    Qp b c (planeVec x a) = minusTailForm K b c a := by
  simp only [Qp, planeVec, Fin.sum_univ_three, Pi.zero_apply, mul_zero, add_zero]
  fin_cases x <;> simp

theorem planeVec_zero (x : Fin 3) : planeVec x (0 : Fin 2 → K) = 0 := by
  simp [planeVec]

theorem decomp_of_mem {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {v : PV K} (h1 : v.1 k = 0) (h2 : v.2 = 0) :
    v = planeVec i (v.1 i) + planeVec j (v.1 j) := by
  refine Prod.ext (funext fun y => ?_) ?_
  · rcases fin3_cover i j k hij hik hjk y with rfl | rfl | rfl
    · simp [planeVec, Pi.single_eq_of_ne hij]
    · simp [planeVec, Pi.single_eq_of_ne hij.symm]
    · simp [planeVec, Pi.single_eq_of_ne hik.symm, Pi.single_eq_of_ne hjk.symm, h1]
  · simp [planeVec, h2]

theorem fix_other_plane {D : Subgroup (Pt b c p)} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hnj : ¬ ZeroOn D j) {W : Submodule K (PV K)} (hW1 : ∀ v ∈ W, v.1 k = 0)
    (hW2 : ∀ v ∈ W, v.2 = 0) (hWj : ∀ a, planeVec j a ∈ W)
    (S : Subgroup (PV K ≃ₗ[K] PV K)) (hSW : ∀ s ∈ S, ∀ w ∈ W, s w ∈ W) (hSO : S ≤ Oq b c)
    (hSc : ∀ s ∈ S, ∀ d ∈ D, s * dh b c p d = dh b c p d * s) (hS2 : IsPGroup 2 S)
    (hSi : ∀ s ∈ S, ∀ a, s (planeVec i a) = planeVec i a) :
    ∀ s ∈ S, ∀ a, s (planeVec j a) = planeVec j a := by
  have hα : ∀ s ∈ S, ∀ a, s (planeVec j a) =
      planeVec i (blk i j s a) + planeVec j (blk j j s a) := by
    intro s hs a
    have hv := hSW s hs _ (hWj a)
    exact decomp_of_mem hij hik hjk (hW1 _ hv) (hW2 _ hv)
  have hmul : ∀ s ∈ S, ∀ s' ∈ S, blk j j (s * s') = (blk j j s).comp (blk j j s') := by
    intro s hs s' hs'
    refine LinearMap.ext fun a => ?_
    have h1 : (s * s') (planeVec j a) = planeVec i (blk i j s' a) +
        (planeVec i (blk i j s (blk j j s' a)) + planeVec j (blk j j s (blk j j s' a))) := by
      rw [LinearEquiv.mul_apply, hα s' hs' a, map_add, hSi s hs, hα s hs (blk j j s' a)]
    rw [blk_apply, h1]
    simp [planeVec, Pi.single_eq_of_ne hij.symm]
  obtain ⟨d₀, hd₀, hs₀⟩ := exists_sT_ne_zero hnj
  have hg₀1 : tg d₀ j ≠ 1 := fun h => hs₀ (by simp [sT, h])
  have hcomm : ∀ s ∈ S, ∀ a, blk j j s ((tg d₀ j : Matrix (Fin 2) (Fin 2) K).mulVec a) =
      (tg d₀ j : Matrix (Fin 2) (Fin 2) K).mulVec (blk j j s a) := by
    intro s hs a
    have h1 : s (dh b c p d₀ (planeVec j a)) = dh b c p d₀ (s (planeVec j a)) :=
      congrArg (fun e : PV K ≃ₗ[K] PV K => e (planeVec j a)) (hSc s hs d₀ hd₀)
    simp only [dh_planeVec, hα s hs, map_add] at h1
    have h2 := congrArg (projP j) h1
    simpa [projP_planeVec, projP_planeVec_ne hij.symm] using h2
  let Aq : S →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun s => LinearMap.toMatrix' (blk j j (s : PV K ≃ₗ[K] PV K))
      map_one' := by
        show LinearMap.toMatrix' (blk j j (1 : PV K ≃ₗ[K] PV K)) = 1
        rw [blk_one, LinearMap.toMatrix'_id]
      map_mul' := fun s s' => by
        show LinearMap.toMatrix' (blk j j (s.1 * s'.1)) = _
        rw [hmul s.1 s.2 s'.1 s'.2, LinearMap.toMatrix'_comp] }
  have hpsi : ∀ s ∈ S, blk j j s = LinearMap.id := by
    intro s hs
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    have h1 : (Aq ⟨s, hs⟩) ^ (2 ^ m) = 1 := by rw [← map_pow, hm, map_one]
    have hA := eq_Mmat_of_commutes (tg_mem_Tns d₀ j) hg₀1
      (toMatrix'_commute (hcomm s hs))
    have h2 : Aq ⟨s, hs⟩ = Mmat b c ((Aq ⟨s, hs⟩) 0 0, (Aq ⟨s, hs⟩) 1 0) := hA
    rw [h2] at h1
    have h3 := Mmat_eq_one_of_pow h1
    rw [← h2] at h3
    apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_id]
    exact h3
  intro s hs a
  have hform := mem_Oq.1 (hSO hs) (planeVec j a)
  rw [hα s hs a, hpsi s hs, LinearMap.id_apply, Qp_planeVec_add hij, Qp_planeVec] at hform
  have hmu : blk i j s a = 0 := minusTailForm_eq_zero (by
    have h2 : minusTailForm K b c (blk i j s a) + minusTailForm K b c a =
        0 + minusTailForm K b c a := by rw [zero_add]; exact hform
    exact add_right_cancel h2)
  rw [hα s hs a, hpsi s hs, LinearMap.id_apply, hmu, planeVec_zero, zero_add]

end WAnalysis

section LongCase

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

variable (K) in
@[expose] def Wk (k : Fin 3) : Submodule K (PV K) where
  carrier := {v | v.1 k = 0 ∧ v.2 = 0}
  add_mem' := fun {u v} hu hv => ⟨by simp [hu.1, hv.1], by simp [hu.2, hv.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun r v hv => ⟨by simp [hv.1], by simp [hv.2]⟩

theorem planeVec_mem_Wk {k x : Fin 3} (hx : x ≠ k) (a : Fin 2 → K) : planeVec x a ∈ Wk K k :=
  ⟨by simp [planeVec, Pi.single_eq_of_ne hx.symm], rfl⟩

theorem Wk_invariant {D : Subgroup (Pt b c p)} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hrel : RelOn D i j) (hnz : ¬ ZeroOn D i)
    (hk : ∃ d ∈ D, sT (tg d i) ≠ sT (tg d k)) {g : PV K ≃ₗ[K] PV K}
    (hg : ∀ d ∈ D, g * dh b c p d = dh b c p d * g) {v : PV K} (hv : v ∈ Wk K k) :
    g v ∈ Wk K k := by
  have hdec := decomp_of_mem hij hik hjk hv.1 hv.2
  have hmem : v ∈ Tx b c p D i := by
    rw [hdec]
    exact Submodule.add_mem _ (planeVec_mem_Tx (fun d _ => rfl) _) (planeVec_mem_Tx hrel _)
  have hgv := Tx_invariant hg hmem
  exact ⟨Tx_fst_zero (c := c) hk hgv, Tx_snd_zero (c := c) (exists_sT_ne_zero hnz) hgv⟩

theorem plane_in_of_ne (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {i j : Fin 3} (hij : i ≠ j)
    {F : Submodule K (PV K)} (hF : ∀ t : Pt b c p, ∀ v ∈ F, dh b c p t v ∈ F)
    {a b' : Fin 2 → K} (hmem : planeVec i a + planeVec j b' ∈ F) (ha : a ≠ 0) :
    ∀ a', planeVec i a' ∈ F := by
  have hnt : Nontrivial (Tp b c p) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Tp hp hpq]; exact hp.one_lt)
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : Tp b c p)
  have hg₀1 : ((g₀ : Tp b c p) : GL (Fin 2) K) ≠ 1 := fun h => hg₀ (Subtype.ext h)
  have hg₀T : ((g₀ : Tp b c p) : GL (Fin 2) K) ∈ Tns b c := g₀.2.1
  set t₀ : Pt b c p := Pi.mulSingle i g₀ with ht₀
  have htg_i : tg t₀ i = ((g₀ : Tp b c p) : GL (Fin 2) K) := by simp [tg, ht₀]
  have htg_j : tg t₀ j = 1 := by
    simp [tg, ht₀, Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) hij.symm]
  have hact : ∀ a', dh b c p t₀ (planeVec i a') =
      planeVec i ((((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a') := by
    intro a'
    rw [dh_planeVec, htg_i]
  have hactj : ∀ a', dh b c p t₀ (planeVec j a') = planeVec j a' := by
    intro a'
    rw [dh_planeVec, htg_j]
    simp
  let L : Submodule K (Fin 2 → K) := F.comap (injP i)
  have hL : ∀ a', a' ∈ L ↔ planeVec i a' ∈ F := fun a' => Iff.rfl
  have hLinv : ∀ v ∈ L,
      (((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v ∈ L := by
    intro v hv
    rw [hL] at hv ⊢
    have := hF t₀ _ hv
    rwa [hact] at this
  have hcases := invariant_of_Tns hg₀T hg₀1 L hLinv
  have hne : (((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a - a ∈ L := by
    rw [hL]
    have h1 := hF t₀ _ hmem
    rw [map_add, hact, hactj] at h1
    have h2 := F.sub_mem h1 hmem
    have h3 : planeVec i ((((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a) +
        planeVec j b' - (planeVec i a + planeVec j b') =
        planeVec i
          ((((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a - a) := by
      rw [show ((((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a - a) =
        ((((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a + (-a)) by abel,
        planeVec_add, show planeVec i (-a) = -planeVec i a by
          rw [show -a = (-1 : K) • a by simp, planeVec_smul]; simp]
      abel
    rwa [h3] at h2
  have hnz : (((g₀ : Tp b c p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a - a ≠ 0 := by
    intro h0
    exact ha (Tns_fix hg₀T hg₀1 (sub_eq_zero.1 h0))
  rcases hcases with h | h
  · exfalso
    rw [h] at hne
    exact hnz ((Submodule.mem_bot K).1 hne)
  · intro a'
    have : a' ∈ L := by rw [h]; trivial
    exact this

end LongCase

section LongCase2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem Pt_mul_comm (s t : Pt b c p) : s * t = t * s := by
  funext x
  exact Subtype.ext (comm_of_mem_Tns (s x).2.1 (t x).2.1)

theorem dh_mul_comm (s t : Pt b c p) :
    dh b c p s * dh b c p t = dh b c p t * dh b c p s := by
  rw [← map_mul, ← map_mul, Pt_mul_comm]

theorem long_case_fix (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {D : Subgroup (Pt b c p)}
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hrel : RelOn D i j)
    (hnz : ∀ x, ¬ ZeroOn D x) (hik' : ∃ d ∈ D, sT (tg d i) ≠ sT (tg d k))
    (hjk' : ∃ d ∈ D, sT (tg d j) ≠ sT (tg d k)) (S : Subgroup (PV K ≃ₗ[K] PV K))
    (hSO : S ≤ Oq b c) (hSc : ∀ s ∈ S, ∀ d ∈ D, s * dh b c p d = dh b c p d * s)
    (hS2 : IsPGroup 2 S) (hSn : ∀ e ∈ E0 b c p, ∀ s ∈ S, e * s * e⁻¹ ∈ S) :
    ∀ s ∈ S, ∀ a, s (planeVec i a) = planeVec i a ∧ s (planeVec j a) = planeVec j a := by
  have hrel' : RelOn D j i := fun d hd => (hrel d hd).symm
  have hjk'' : ∃ d ∈ D, sT (tg d j) ≠ sT (tg d k) := hjk'
  have hWinv : ∀ s ∈ S, ∀ w ∈ Wk K k, s w ∈ Wk K k := fun s hs w hw =>
    Wk_invariant hij hik hjk hrel (hnz i) hik' (hSc s hs) hw
  let F : Submodule K (PV K) :=
    { carrier := {w | w ∈ Wk K k ∧ ∀ s ∈ S, s w = w}
      add_mem' := fun {u v} hu hv => ⟨Submodule.add_mem _ hu.1 hv.1, fun s hs => by
        rw [map_add, hu.2 s hs, hv.2 s hs]⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun s _ => map_zero s⟩
      smul_mem' := fun r v hv => ⟨Submodule.smul_mem _ r hv.1, fun s hs => by
        rw [map_smul, hv.2 s hs]⟩ }
  have hFmem : ∀ w, w ∈ F ↔ w ∈ Wk K k ∧ ∀ s ∈ S, s w = w := fun w => Iff.rfl
  have hFinv : ∀ t : Pt b c p, ∀ v ∈ F, dh b c p t v ∈ F := by
    intro t v hv
    rw [hFmem] at hv ⊢
    have hmemE : dh b c p t ∈ E0 b c p := ⟨t, rfl⟩
    refine ⟨Wk_invariant hij hik hjk hrel (hnz i) hik' (fun d _ => dh_mul_comm t d) hv.1,
      fun s hs => ?_⟩
    have hs' := hSn (dh b c p t)⁻¹ (inv_mem hmemE) s hs
    have h1 := hv.2 _ hs'
    have h3 : ((dh b c p t)⁻¹ * s * (dh b c p t)⁻¹⁻¹) v =
        (dh b c p t)⁻¹ (s (dh b c p t v)) := by
      rw [inv_inv]
      rfl
    rw [h3] at h1
    have h4 := congrArg (dh b c p t) h1
    have h5 : dh b c p t ((dh b c p t)⁻¹ (s (dh b c p t v))) = s (dh b c p t v) := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [h5] at h4
    exact h4
  have hW0 : Wk K k ≠ ⊥ := by
    intro h
    have := planeVec_mem_Wk hik (Pi.single 0 1 : Fin 2 → K)
    rw [h, Submodule.mem_bot] at this
    have h1 := congrArg (projP i) this
    rw [projP_planeVec, map_zero] at h1
    have := congrFun h1 0
    simp at this
  obtain ⟨w, hwW, hw0, hwS⟩ := exists_fixed_vector hS2 hW0 hWinv
  have hwF : w ∈ F := (hFmem w).2 ⟨hwW, hwS⟩
  have hdec := decomp_of_mem hij hik hjk hwW.1 hwW.2
  have hall : ∀ x, x ≠ k → (∀ a, planeVec x a ∈ F) →
      ∀ s ∈ S, ∀ a, s (planeVec x a) = planeVec x a :=
    fun x _ hxF s hs a => ((hFmem _).1 (hxF a)).2 s hs
  intro s hs a
  by_cases ha : w.1 i = 0
  · have hb : w.1 j ≠ 0 := by
      intro hb
      apply hw0
      rw [hdec, ha, hb, planeVec_zero, planeVec_zero, zero_add]
    have hmem : planeVec j (w.1 j) + planeVec i (w.1 i) ∈ F := by
      rw [add_comm, ← hdec]
      exact hwF
    have hplane := plane_in_of_ne hp hpq hij.symm hFinv hmem hb
    have hSj := hall j hjk hplane
    have hSi := fix_other_plane (D := D) hij.symm hjk hik (hnz i) (W := Wk K k)
      (fun v hv => hv.1) (fun v hv => hv.2) (fun a => planeVec_mem_Wk hik a) S hWinv hSO hSc hS2
      hSj
    exact ⟨hSi s hs a, hSj s hs a⟩
  · have hmem : planeVec i (w.1 i) + planeVec j (w.1 j) ∈ F := by
      rw [← hdec]
      exact hwF
    have hplane := plane_in_of_ne hp hpq hij hFinv hmem ha
    have hSi := hall i hik hplane
    have hSj := fix_other_plane (D := D) hij hik hjk (hnz j) (W := Wk K k)
      (fun v hv => hv.1) (fun v hv => hv.2) (fun a => planeVec_mem_Wk hjk a) S hWinv hSO hSc hS2
      hSi
    exact ⟨hSi s hs a, hSj s hs a⟩

end LongCase2

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

attribute [local instance] Classical.propDecidable

theorem card_le_of_rel3 (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {D : Subgroup (Pt b c p)}
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : ∀ d ∈ D, sT (tg d j) = sT (tg d i)) (hk : ∀ d ∈ D, sT (tg d k) = sT (tg d i)) :
    Nat.card D ≤ 4 * p := by
  let f : D → Tp b c p × Bool × Bool := fun d =>
    (d.1 i, decide (d.1 j = d.1 i), decide (d.1 k = d.1 i))
  have hf : Function.Injective f := by
    intro d d' hdd
    simp only [f, Prod.mk.injEq, decide_eq_decide] at hdd
    obtain ⟨h1, h2, h3⟩ := hdd
    have key : ∀ x : Fin 3, (∀ e ∈ D, sT (tg e x) = sT (tg e i)) →
        (d.1 x = d.1 i ↔ d'.1 x = d'.1 i) → d.1 x = d'.1 x := by
      intro x hx hiff
      have hd := Tns_s_eq (tg_mem_Tns d.1 i) (tg_mem_Tns d.1 x) (hx d d.2).symm
      have hd' := Tns_s_eq (tg_mem_Tns d'.1 i) (tg_mem_Tns d'.1 x) (hx d' d'.2).symm
      by_cases hc : d.1 x = d.1 i
      · have hc' := hiff.1 hc
        rw [hc, hc', h1]
      · have hc' : ¬ d'.1 x = d'.1 i := fun h => hc (hiff.2 h)
        have e1 : d.1 x = (d.1 i)⁻¹ := by
          rcases hd with h | h
          · exact absurd (Subtype.ext h) hc
          · exact Subtype.ext h
        have e2 : d'.1 x = (d'.1 i)⁻¹ := by
          rcases hd' with h | h
          · exact absurd (Subtype.ext h) hc'
          · exact Subtype.ext h
        rw [e1, e2, h1]
    refine Subtype.ext (funext fun y => ?_)
    rcases fin3_cover i j k hij hik hjk y with rfl | rfl | rfl
    · exact h1
    · exact key y hj h2
    · exact key y hk h3
  calc Nat.card D ≤ Nat.card (Tp b c p × Bool × Bool) := Nat.card_le_card_of_injective f hf
    _ = 4 * p := by
      rw [Nat.card_prod, Nat.card_prod, card_Tp hp hpq]
      simp [Nat.card_eq_fintype_card]
      ring

end Core

section Core2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j := by decide

theorem exists_zero_of_data (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    {D : Subgroup (Pt b c p)} (hcard : Nat.card D = p ^ 2) (J S : Subgroup (PV K ≃ₗ[K] PV K))
    (hJO : J ≤ Oq b c) (hJc : ∀ j ∈ J, ∀ d ∈ D, j * dh b c p d = dh b c p d * j)
    (hJ : ⁅J, J⁆ = J) (hSJ : S ≤ J) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hSn : ∀ e ∈ E0 b c p, ∀ s ∈ S, e * s * e⁻¹ ∈ S) (hSE : S = ⁅S, E0 b c p⁆) :
    ∃ k, ZeroOn D k := by
  by_contra hcon
  have hnz : ∀ x, ¬ ZeroOn D x := fun x hx => hcon ⟨x, hx⟩
  have hSc : ∀ s ∈ S, ∀ d ∈ D, s * dh b c p d = dh b c p d * s :=
    fun s hs d hd => hJc s (hSJ hs) d hd
  have hSO : S ≤ Oq b c := hSJ.trans hJO
  by_cases hL : ∃ i j, i ≠ j ∧ RelOn D i j
  · obtain ⟨i, j, hij, hrel⟩ := hL
    obtain ⟨k, hki, hkj⟩ := fin3_third i j hij
    have hik : i ≠ k := hki.symm
    have hjk : j ≠ k := hkj.symm
    have hik' : ∃ d ∈ D, sT (tg d i) ≠ sT (tg d k) := by
      by_contra h
      push Not at h
      have h1 := card_le_of_rel3 hp hpq hij hik hjk (fun d hd => (hrel d hd).symm)
        (fun d hd => (h d hd).symm)
      rw [hcard] at h1
      nlinarith
    have hjk' : ∃ d ∈ D, sT (tg d j) ≠ sT (tg d k) := by
      obtain ⟨d, hd, hne⟩ := hik'
      exact ⟨d, hd, by rwa [← hrel d hd]⟩
    have hJk : J ≤ fixPlane k := by
      refine triv_plane (hnz k) (fun y hy => ?_) J hJc hJ
      rcases fin3_cover i j k hij hik hjk y with rfl | rfl | rfl
      · obtain ⟨d, hd, hne⟩ := hik'
        exact ⟨d, hd, hne.symm⟩
      · obtain ⟨d, hd, hne⟩ := hjk'
        exact ⟨d, hd, hne.symm⟩
      · exact absurd rfl hy
    have hfix := long_case_fix hp hpq hij hik hjk hrel hnz hik' hjk' S hSO hSc hS2 hSn
    refine false_of_fix_planes hnz S hS1 hSE hSc (fun s hs x a => ?_)
    rcases fin3_cover i j k hij hik hjk x with rfl | rfl | rfl
    · exact (hfix s hs a).1
    · exact (hfix s hs a).2
    · exact mem_fixPlane.1 (hJk (hSJ hs)) a
  · push Not at hL
    have hall : ∀ x, J ≤ fixPlane x := by
      intro x
      refine triv_plane (hnz x) (fun y hy => ?_) J hJc hJ
      by_contra h
      push Not at h
      exact hL x y hy.symm h
    exact false_of_fix_planes hnz S hS1 hSE hSc (fun s hs x a => mem_fixPlane.1 (hall x (hSJ hs)) a)

end Core2

end CFSG.RankThree.PartOne.AUTSL.Four

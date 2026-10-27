module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRoot
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentAut
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentWRoots
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}

private def glueIdentWAux_word (n : ℕ) (l : List (Fin n)) : FEMat n :=
  (l.map (feS n)).prod

@[simp] private theorem glueIdentWAux_word_nil (n : ℕ) :
    glueIdentWAux_word n [] = 1 := rfl

@[simp] private theorem glueIdentWAux_word_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) :
    glueIdentWAux_word n (i :: l) = feS n i * glueIdentWAux_word n l := by
  simp [glueIdentWAux_word]

private theorem glueIdentWAux_word_append (n : ℕ) (l₁ l₂ : List (Fin n)) :
    glueIdentWAux_word n (l₁ ++ l₂) =
      glueIdentWAux_word n l₁ * glueIdentWAux_word n l₂ := by
  simp [glueIdentWAux_word, List.map_append, List.prod_append]

private theorem glueIdentWAux_word_reverse_mul (n : ℕ) (l : List (Fin n)) :
    glueIdentWAux_word n l.reverse * glueIdentWAux_word n l = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.reverse_cons, glueIdentWAux_word_append]
      simp only [glueIdentWAux_word_cons, glueIdentWAux_word_nil, mul_one]
      calc (glueIdentWAux_word n l.reverse * feS n i) * (feS n i * glueIdentWAux_word n l)
          = glueIdentWAux_word n l.reverse * (feS n i * feS n i) *
              glueIdentWAux_word n l := by noncomm_ring
        _ = glueIdentWAux_word n l.reverse * glueIdentWAux_word n l := by
              rw [feS_mul_self, mul_one]
        _ = 1 := ih

private def glueIdentWAux_wordSubmonoid (n : ℕ) : Submonoid (FEMat n) where
  carrier := {m | ∃ l : List (Fin n), glueIdentWAux_word n l = m}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro a b ⟨l, rfl⟩ ⟨l', rfl⟩
    exact ⟨l ++ l', by rw [glueIdentWAux_word_append]⟩

private theorem glueIdentWAux_word_mem_closure (n : ℕ) (l : List (Fin n)) :
    glueIdentWAux_word n l ∈ Submonoid.closure (Set.range (feS n)) := by
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons i l ih =>
      rw [glueIdentWAux_word_cons]
      exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨i, rfl⟩) ih

private theorem glueIdentWAux_exists_word {n : ℕ} {m : FEMat n}
    (hm : m ∈ Submonoid.closure (Set.range (feS n))) :
    ∃ l : List (Fin n), glueIdentWAux_word n l = m := by
  have hle : Submonoid.closure (Set.range (feS n)) ≤ glueIdentWAux_wordSubmonoid n := by
    rw [Submonoid.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨[i], by rw [glueIdentWAux_word_cons, glueIdentWAux_word_nil, mul_one]⟩
  exact hle hm

private theorem glueIdentWAux_word_mulVec_mem {L : ℕ} {R : Fin L → FEVec n}
    (hR : FERootList n L R) {v : FEVec n} (hv : v ∈ Set.range R)
    (l : List (Fin n)) :
    (glueIdentWAux_word n l).mulVec v ∈ Set.range R := by
  induction l with
  | nil => simpa using hv
  | cons i l ih =>
      rw [glueIdentWAux_word_cons, ← Matrix.mulVec_mulVec]
      obtain ⟨k, hk⟩ := ih
      rw [← hk]
      exact hR.closed i k

private theorem glueIdentWAux_two_smul_eq_neg {n : ℕ} (v : FEVec n) :
    (2 : ZMod 3) • v = -v := by
  ext i
  show (2 : ZMod 3) • v i = -v i
  rw [show (2 : ZMod 3) = -1 by decide, smul_eq_mul]
  exact neg_one_mul (v i)

private theorem glueIdentWAux_mem_of_neg_eigen {L : ℕ} {R : Fin L → FEVec n}
    (hR : FERootList n L R) {t : FEMat n} (ht : FEConjDer n t)
    {v : FEVec n} (hv0 : v ≠ 0) (htv : t.mulVec v = -v) : v ∈ Set.range R := by
  induction ht generalizing v with
  | base i =>
      have hc : v = (2 * v i) • feCol n i := feS_neg_line n i v htv
      have hvi : v i ≠ 0 := by
        intro h
        apply hv0
        rw [hc, h, mul_zero, zero_smul]
      have hcases : v i = 1 ∨ v i = 2 := by
        have hall : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide +kernel
        exact hall (v i) hvi
      rcases hcases with h | h
      · have h2 : (2 : ZMod 3) * 1 = 2 := by decide
        rw [hc, h, h2, glueIdentWAux_two_smul_eq_neg]
        exact FERootList.neg_of_mem hR (hR.mem_col i)
      · have h2 : (2 : ZMod 3) * 2 = 1 := by decide
        rw [hc, h, h2, one_smul]
        exact hR.mem_col i
  | conj i hr ih =>
      rename_i r
      set s := feS n i with hs
      have hs2 : s * s = 1 := feS_mul_self n i
      have hss : ∀ x : FEVec n, s.mulVec (s.mulVec x) = x := by
        intro x
        rw [Matrix.mulVec_mulVec, hs2, Matrix.one_mulVec]
      have h1 : s.mulVec (r.mulVec (s.mulVec v)) = -v := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        exact htv
      have h2 : r.mulVec (s.mulVec v) = -(s.mulVec v) := by
        have h := congrArg (fun x => s.mulVec x) h1
        rw [hss] at h
        exact h.trans (Matrix.mulVec_neg v s)
      have hv' : s.mulVec v ≠ 0 := by
        intro h
        apply hv0
        rw [← hss v, h, Matrix.mulVec_zero]
      obtain ⟨k, hk⟩ := ih hv' h2
      have hc := hR.closed i k
      rwa [hk, hss v] at hc

private theorem glueIdentWAux_mrange_rho (M : GGFrameModelData Bs n)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n))) :
    MonoidHom.mrange M.ρ = Submonoid.closure (Set.range (feS n)) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact hgen φ
  · rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_mrange.mpr
      ⟨Classical.choose (M.simple i), Classical.choose_spec (M.simple i)⟩

private noncomputable def glueIdentWAux_psiEquiv (M : GGFrameModelData Bs n) :
    ↥Bs ≃ FEVec n where
  toFun b := M.ψ (Additive.ofMul b)
  invFun v := Additive.toMul (M.ψ.symm v)
  left_inv b := by simp
  right_inv v := by simp

private theorem glueIdentWAux_psiEquiv_apply (M : GGFrameModelData Bs n) (b : ↥Bs) :
    glueIdentWAux_psiEquiv M b = M.ψ (Additive.ofMul b) := rfl

private theorem glueIdentWAux_mem_psi_range {L : ℕ} {R : Fin L → FEVec n}
    (hR : FERootList n L R) (M : GGFrameModelData Bs n) {z : G}
    (hz : M.IsRoot z) :
    M.ψ (Additive.ofMul (⟨z, hz.1⟩ : ↥Bs)) ∈ Set.range R := by
  have hz1 : z ≠ 1 := hz.2.1
  obtain ⟨t, ht, htv⟩ := hz.2.2
  have hv0 : M.ψ (Additive.ofMul (⟨z, hz.1⟩ : ↥Bs)) ≠ 0 := by
    intro h
    apply hz1
    have hb : (⟨z, hz.1⟩ : ↥Bs) = 1 := by
      have h0 : Additive.ofMul (⟨z, hz.1⟩ : ↥Bs) = 0 :=
        M.ψ.injective (by simpa using h)
      exact Additive.ofMul.injective (by simpa using h0)
    exact congrArg Subtype.val hb
  exact glueIdentWAux_mem_of_neg_eigen hR ht hv0 htv

private theorem glueIdentWAux_exists_word_get {L : ℕ} {R : Fin L → FEVec n}
    (hR : FERootList n L R) (h0 : 0 < L) :
    ∀ k : Fin L, ∃ l : List (Fin n),
      (glueIdentWAux_word n l).mulVec (R ⟨0, h0⟩) = R k := by
  intro k
  obtain ⟨k', hk'⟩ := k
  revert hk'
  refine Nat.strong_induction_on k' ?_
  intro k' ih hk'
  by_cases hk0 : k' = 0
  · subst hk0
    exact ⟨[], by rw [glueIdentWAux_word_nil, Matrix.one_mulVec]⟩
  · have hkpos : 0 < k' := Nat.pos_of_ne_zero hk0
    obtain ⟨i, j, hjk, hspec⟩ := hR.reach ⟨k', hk'⟩ hkpos
    obtain ⟨l, hl⟩ := ih j.val hjk j.isLt
    refine ⟨i :: l, ?_⟩
    rw [glueIdentWAux_word_cons, ← Matrix.mulVec_mulVec, hl, hspec, Matrix.mulVec_mulVec,
      feS_mul_self n i, Matrix.one_mulVec]

private theorem glueIdentWAux_psi_image_orbit {L : ℕ} {R : Fin L → FEVec n}
    (hR : FERootList n L R) (h0 : 0 < L) (M : GGFrameModelData Bs n)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    {z : G} (hz : M.IsRoot z) :
    glueIdentWAux_psiEquiv M ''
        (MulAction.orbit ↥M.A (⟨z, hz.1⟩ : ↥Bs)) = Set.range R := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨φ, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    rw [glueIdentWAux_psiEquiv_apply, Subgroup.smul_def, MulAut.smul_def]
    rw [← M.act φ (⟨z, hz.1⟩ : ↥Bs)]
    obtain ⟨l, hl⟩ := glueIdentWAux_exists_word (hgen φ)
    rw [← hl]
    exact glueIdentWAux_word_mulVec_mem hR (glueIdentWAux_mem_psi_range hR M hz) l
  · intro v hv
    obtain ⟨k, hk⟩ := hv
    obtain ⟨lk, hlk⟩ := glueIdentWAux_exists_word_get hR h0 k
    obtain ⟨k0, hk0⟩ := glueIdentWAux_mem_psi_range hR M hz
    obtain ⟨l0, hl0⟩ := glueIdentWAux_exists_word_get hR h0 k0
    have h0rev : (glueIdentWAux_word n l0.reverse).mulVec
        (M.ψ (Additive.ofMul (⟨z, hz.1⟩ : ↥Bs))) = R ⟨0, h0⟩ := by
      rw [← hk0, ← hl0, Matrix.mulVec_mulVec, glueIdentWAux_word_reverse_mul,
        Matrix.one_mulVec]
    have hv' : v = (glueIdentWAux_word n (lk ++ l0.reverse)).mulVec
        (M.ψ (Additive.ofMul (⟨z, hz.1⟩ : ↥Bs))) := by
      rw [glueIdentWAux_word_append, ← Matrix.mulVec_mulVec, h0rev, hlk, hk]
    have hmr : glueIdentWAux_word n (lk ++ l0.reverse) ∈ MonoidHom.mrange M.ρ := by
      rw [glueIdentWAux_mrange_rho M hgen]
      exact glueIdentWAux_word_mem_closure n _
    obtain ⟨φ, hφ⟩ := MonoidHom.mem_mrange.mp hmr
    refine ⟨φ • (⟨z, hz.1⟩ : ↥Bs), MulAction.mem_orbit _ φ, ?_⟩
    rw [glueIdentWAux_psiEquiv_apply, Subgroup.smul_def, MulAut.smul_def, ← M.act φ _, hφ]
    exact hv'.symm

private noncomputable def glueIdentWAux_stabEquiv (M : GGFrameModelData Bs n) (b : ↥Bs) :
    ↥(MulAction.stabilizer ↥M.A b) ≃
      ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b) where
  toFun x :=
    ⟨x.val.val, ⟨x.val.property, MulAction.mem_stabilizer_iff.mpr (by
      have h := MulAction.mem_stabilizer_iff.mp x.property
      simpa [Subgroup.smul_def, MulAut.smul_def] using h)⟩⟩
  invFun y :=
    ⟨⟨y.val, y.property.1⟩, MulAction.mem_stabilizer_iff.mpr (by
      have h := MulAction.mem_stabilizer_iff.mp y.property.2
      simpa [Subgroup.smul_def, MulAut.smul_def] using h)⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

private theorem glueIdentWAux_card_stabilizer_gen (M : GGFrameModelData Bs n)
    (hn : n = 7 ∨ n = 8)
    (hA : Nat.card M.A = if n = 7 then 2903040 else 696729600)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    {L : ℕ} {R : Fin L → FEVec n} (hR : FERootList n L R)
    (hL : L = if n = 7 then 126 else 240) (hL0 : 0 < L)
    {z : G} (hz : M.IsRoot z) :
    Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz.1⟩ : ↥Bs)) =
      if n = 7 then 23040 else 2903040 := by
  classical
  let b0 : ↥Bs := ⟨z, hz.1⟩
  have himage : glueIdentWAux_psiEquiv M '' (MulAction.orbit ↥M.A b0) = Set.range R := by
    simpa [b0] using glueIdentWAux_psi_image_orbit hR hL0 M hgen hz
  have hcard_range : Nat.card (Set.range R) = L := by
    calc Nat.card (Set.range R) = Nat.card (Fin L) :=
          (Nat.card_congr (Equiv.ofInjective R hR.injective)).symm
      _ = L := Nat.card_fin L
  let orbitEquiv : MulAction.orbit ↥M.A b0 ≃ Set.range R :=
    (Equiv.image (glueIdentWAux_psiEquiv M) (MulAction.orbit ↥M.A b0)).trans
      (Set.equivOfEq himage)
  have hOS' : Nat.card (MulAction.orbit ↥M.A b0) *
      Nat.card ↥(MulAction.stabilizer ↥M.A b0) = Nat.card ↥M.A := by
    rw [mul_comm, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.card_mul_index _
  have horbit : Nat.card (MulAction.orbit ↥M.A b0) = L := by
    calc Nat.card (MulAction.orbit ↥M.A b0) = Nat.card (Set.range R) :=
          Nat.card_congr orbitEquiv
      _ = L := hcard_range
  have hstab : Nat.card ↥(MulAction.stabilizer ↥M.A b0) =
      Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0) :=
    Nat.card_congr (glueIdentWAux_stabEquiv M b0)
  have hmain : L * Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0) =
      Nat.card ↥M.A := by
    rw [← horbit, ← hstab, hOS']
  rcases hn with rfl | rfl
  · have hL' : L = 126 := by simpa using hL
    have hAcard : Nat.card ↥M.A = 2903040 := by simpa using hA
    rw [hL', hAcard] at hmain
    have : Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0) = 23040 := by omega
    simpa [b0] using this
  · have hL' : L = 240 := by simpa using hL
    have hAcard : Nat.card ↥M.A = 696729600 := by simpa using hA
    rw [hL', hAcard] at hmain
    have : Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0) = 2903040 := by omega
    simpa [b0] using this

theorem card_stabilizer_isRoot (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hA : Nat.card M.A = if n = 7 then 2903040 else 696729600)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    {z : G} (hz : M.IsRoot z) :
    Nat.card ↥(M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz.1⟩ : ↥Bs)) =
      if n = 7 then 23040 else 2903040 := by
  rcases hn with rfl | rfl
  · exact glueIdentWAux_card_stabilizer_gen M (Or.inl rfl) hA hgen
      feRootList_seven (by norm_num) (by norm_num) hz
  · exact glueIdentWAux_card_stabilizer_gen M (Or.inr rfl) hA hgen
      feRootList_eight (by norm_num) (by norm_num) hz

private theorem glueIdentWAux_stab_le_automizer (M : GGFrameModelData Bs n) {z : G}
    (hz : M.IsRoot z) :
    M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz.1⟩ : ↥Bs) ≤
      ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
  intro φ hφ
  obtain ⟨hφA, hφstab⟩ := hφ
  obtain ⟨g, -, hgN, hgconj⟩ := M.induced φ hφA
  rw [mem_ggAutomizer_iff]
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hgN, hgconj⟩
  have hφb : (φ : MulAut ↥Bs) (⟨z, hz.1⟩ : ↥Bs) = ⟨z, hz.1⟩ := by
    have h := MulAction.mem_stabilizer_iff.mp hφstab
    simpa [MulAut.smul_def] using h
  have hgz : z = g * z * g⁻¹ := by
    have h := hgconj (⟨z, hz.1⟩ : ↥Bs)
    rwa [hφb] at h
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [← hgz]

theorem exists_weyl_le_automizer_of_isRoot [Finite G] (M : GGFrameModelData Bs n)
    (hn : n = 7 ∨ n = 8) (hA : Nat.card M.A = if n = 7 then 2903040 else 696729600)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) {z : G} (hz : M.IsRoot z)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    ∃ W : Subgroup (MulAut ↥(ggGamma K hN).range),
      W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range ∧
        Nat.card W = if n = 7 then 23040 else 2903040 := by
  let b0 : ↥Bs := ⟨z, hz.1⟩
  have hS : M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0 ≤
      ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
    simpa [b0] using glueIdentWAux_stab_le_automizer M hz
  obtain ⟨W, hW, hcard⟩ :=
    exists_le_automizer_of_le_centralizer hBs hz.1 hNT hN hNK hker
      (S := M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b0) hS
  refine ⟨W, hW, ?_⟩
  rw [hcard]
  simpa [b0] using card_stabilizer_isRoot M hn hA hgen hz

end CFSG.StandardType.FrameRoute

end

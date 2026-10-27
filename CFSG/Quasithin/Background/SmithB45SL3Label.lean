module

public import CFSG.Quasithin.Background.SmithB42SL3Label

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply dualMat MatIso)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

section Package

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem exists_label_pkg (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) (hnt : ∃ x, ρ x ≠ 1) :
    ∃ (a b : Fin f → Bool) (Wj : ℕ → Subrepresentation
        (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))),
      (a ≠ zeros f ∨ b ≠ zeros f) ∧
      (∀ j, (Wj j).toRepresentation.IsIrreducible) ∧
      (∀ j, Nonempty ((Wj j).toRepresentation.Equiv
        (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))))) ∧
      (⨆ j, (Wj j).toSubmodule = ⊤) ∧
      (∀ c ∈ pairOrbit f (a, b), 0 < repMultiplicity
        (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))
        (matRep (tensorRep (F := F) F c.1 c.2))) ∧
      (Nonempty (ρ.Equiv ρ.dual) →
        ∃ j₀ : ℕ, (shiftBits f)^[j₀] a = b ∧ (shiftBits f)^[j₀] b = a) := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set ρ₀ := toMatRep ρ bas with hρ₀
  set PF := matMap φ ρ₀ with hPF
  have hirr₀ := invariant_dichotomy ρ hirr bas
  have hnt₀ : ∃ g, ρ₀ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h1 => hg ?_⟩
    have h3 : LinearMap.toMatrix bas bas (ρ g) = LinearMap.toMatrix bas bas 1 := by
      rw [LinearMap.toMatrix_one]
      exact h1
    exact (LinearMap.toMatrix bas bas).injective h3
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      obtain ⟨g, hg⟩ := hnt₀
      exact absurd (Subsingleton.elim _ _) hg
    · exact h
  obtain ⟨a, b, Wj, hWj, heq, hMtop⟩ := exists_galois_family hF hf ρ₀ hn hirr₀
  have hmult : ∀ j : ℕ, 0 < repMultiplicity (matRep PF)
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))) := by
    intro j
    obtain ⟨e⟩ := heq j
    have h1 := CFSG.QuasithinUnique.Setup.X7b.repMultiplicity_sub_quot (matRep PF) (Wj j)
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))
    have h2 : repMultiplicity (Wj j).toRepresentation
        (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))) = 1 := by
      rw [repMultiplicity_congr_left e, repMultiplicity_of_isIrreducible
        ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 _ _).1]
      have hrefl : Nonempty (Representation.Equiv
          (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))
          (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))) :=
        ⟨Representation.Equiv.refl _⟩
      simp [hrefl]
    omega
  have hne : a ≠ zeros f ∨ b ≠ zeros f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    have htriv : ∀ j, ∀ v ∈ (Wj j).toSubmodule, ∀ g, matRep PF g v = v := by
      intro j v hv g
      obtain ⟨e⟩ := heq j
      rw [shiftBits_iterate_zeros] at e
      let v' : (Wj j).toSubmodule := ⟨v, hv⟩
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v'
      rw [matRep_apply, tensorRep_zeros_apply, Matrix.one_mulVec] at h1
      have h2 : (Wj j).toRepresentation g v' = v' := e.toLinearEquiv.injective h1
      exact congrArg Subtype.val h2
    have hall : ∀ g, ∀ v : Fin n → F, matRep PF g v = v := by
      intro g v
      have hv : v ∈ ⨆ j, (Wj j).toSubmodule := by rw [hMtop]; exact Submodule.mem_top
      exact Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
        (motive := fun v => matRep PF g v = v) hv (fun j v hv => htriv j v hv g)
        (by simp) (fun x y hx hy => by rw [map_add, hx, hy])
    obtain ⟨g, hg⟩ := hnt₀
    apply hg
    have h1 : PF g = 1 := by
      ext i j
      have := congrFun (hall g (Pi.single j 1)) i
      simpa [matRep_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have h2 : (ρ₀ g).map φ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map φ := by
      rw [Matrix.map_one φ (map_zero φ) (map_one φ)]
      exact h1
    exact Matrix.map_injective φ.injective h2
  have hO : ∀ c ∈ pairOrbit f (a, b), 0 < repMultiplicity (matRep PF)
      (matRep (tensorRep (F := F) F c.1 c.2)) := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    rw [shiftPair_iterate]
    exact hmult s
  refine ⟨a, b, Wj, hne, hWj, heq, hMtop, hO, fun hsd => ?_⟩
  obtain ⟨P₀, Q₀, hP₀⟩ := exists_matIso_dual ρ bas hsd.some
  have hdm : matMap φ (dualMat (toMatRep ρ bas)) = dualMat (matMap φ (toMatRep ρ bas)) := by
    refine MonoidHom.ext fun g => ?_
    simp [matMap_apply, CFSG.QuasithinUnique.Setup.X7.dualMat_apply, Matrix.transpose_map]
  have hP := hP₀.map φ
  rw [hdm] at hP
  have h0 : Nonempty ((Wj 0).toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :=
    heq 0
  obtain ⟨e0⟩ := h0
  obtain ⟨π, hπ⟩ := exists_dual_surjection PF hP (Wj 0) a b e0.symm
  obtain ⟨j₀, ⟨e₀⟩⟩ := exists_iso_of_surj_onto_irred
    ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 b a).1 π hπ Wj hWj hMtop
  obtain ⟨e₁⟩ := heq j₀
  have hlast := (tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _
    ⟨e₁.symm.trans e₀⟩
  exact ⟨j₀, hlast.1, hlast.2⟩

theorem sum_rank_le (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (O : Finset ((Fin f → Bool) × (Fin f → Bool)))
    (hO : ∀ c ∈ O, 0 < repMultiplicity
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))
      (matRep (tensorRep (F := F) F c.1 c.2))) (z : SL(3, F)) :
    ∑ c ∈ O, (tensorRep (F := F) F c.1 c.2 z - 1).rank ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set ρ₀ := toMatRep ρ bas with hρ₀
  set PF := matMap φ ρ₀ with hPF
  have hsum := sum_rank_le3 hF hf PF z O hO
  have hrank : (PF z - 1).rank ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) := by
    have e1 : PF z - 1 = (ρ₀ z - 1).map φ := by
      ext i j
      by_cases hij : i = j <;> simp [PF, matMap_apply, hij]
    have e2 : (ρ₀ z - 1).rank = Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) := by
      have e3 : ρ₀ z - 1 = LinearMap.toMatrix bas bas (ρ z - 1) := by
        rw [map_sub, LinearMap.toMatrix_one]
        rfl
      rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
    rw [← e2, e1]
    exact CFSG.QuasithinUnique.Setup.X7b.rank_map_ringHom_le φ _
  exact hsum.trans hrank

end Package

section Combinatorics

variable {f : ℕ}

theorem eight_mul_add_three_le_three_pow {s : ℕ} (hs : 3 ≤ s) : 8 * s + 3 ≤ 3 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    omega

theorem eight_mul_add_three_le {s h : ℕ} (hh : 1 ≤ h) (hsh : ¬ (s = 0 ∧ h = 1)) :
    8 * h + 3 ≤ 3 ^ s * 8 ^ h := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have h2 : 2 ≤ h := by omega
    rw [pow_zero, one_mul]
    induction h, h2 using Nat.le_induction with
    | base => norm_num
    | succ h hh ih =>
      rw [pow_succ]
      omega
  · have h3 : 3 ≤ 3 ^ s := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    have h8 : 8 * h ≤ 8 ^ h := eight_mul_le_eight_pow hh
    nlinarith

theorem card_pairOrbit_le (c : (Fin f → Bool) × (Fin f → Bool)) : (pairOrbit f c).card ≤ f :=
  Finset.card_image_le.trans (Finset.card_range f).le

theorem label_cases' (hf : 1 ≤ f) (a b : Fin f → Bool) (hne : a ≠ zeros f ∨ b ≠ zeros f)
    (rk : (Fin f → Bool) × (Fin f → Bool) → ℕ)
    (hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤ 2 * rk c + 1)
    {R : ℕ} (hR : ∑ c ∈ pairOrbit f (a, b), rk c ≤ R) :
    (cntS a b = 1 ∧ cntH a b = 0) ∨
      (cntS a b = 2 ∧ cntH a b = 0 ∧ 4 * (pairOrbit f (a, b)).card ≤ R ∧
        f ≤ 2 * (pairOrbit f (a, b)).card) ∨
      (cntS a b = 0 ∧ cntH a b = 1 ∧ (pairOrbit f (a, b)).card = f ∧ 4 * f ≤ R) ∨
      4 * f + 1 ≤ R := by
  classical
  let c₀ : (Fin f → Bool) × (Fin f → Bool) := (a, b)
  let pH : Bool × Bool → Prop := fun x => x.1 = true ∧ x.2 = true
  let pS : Bool × Bool → Prop := fun x => x.1 ≠ x.2
  set o := (pairOrbit f c₀).card with ho
  have ho1 : 1 ≤ o := B42SL3.card_pairOrbit_pos hf c₀
  have hof : o ≤ f := card_pairOrbit_le c₀
  have hcntH : ∀ c ∈ pairOrbit f c₀, cntH c.1 c.2 = cntH a b := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    exact card_feat_iterate pH c₀ s
  have hcntS : ∀ c ∈ pairOrbit f c₀, cntS c.1 c.2 = cntS a b := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    exact card_feat_iterate pS c₀ s
  have hsum : ∀ B : ℕ, (∀ c ∈ pairOrbit f c₀, B ≤ rk c) → o * B ≤ R := by
    intro B hB
    calc o * B = ∑ _c ∈ pairOrbit f c₀, B := by simp [ho]
      _ ≤ ∑ c ∈ pairOrbit f c₀, rk c := Finset.sum_le_sum hB
      _ ≤ R := hR
  have hrk : ∀ c ∈ pairOrbit f c₀, 3 ^ cntS a b * 8 ^ cntH a b ≤ 2 * rk c + 1 := by
    intro c hc
    have := hdim c
    rwa [hcntS c hc, hcntH c hc] at this
  set S := cntS a b with hS
  set H := cntH a b with hH
  by_cases hH0 : H = 0
  ·
    have hfS : 0 < S → f ≤ o * S := fun hpos =>
      orbit_cover hf pS c₀ (Finset.card_pos.mp hpos)
    rcases Nat.lt_or_ge S 3 with hS3' | hS3'
    · interval_cases S
      ·
        exfalso
        have hall : ∀ i, a i = false ∧ b i = false := by
          intro i
          have hSi : a i = b i := by
            by_contra hab
            have : i ∈ Finset.univ.filter fun i => a i ≠ b i := by simp [hab]
            have h0 : (Finset.univ.filter fun i => a i ≠ b i).card = 0 := hS.symm
            rw [Finset.card_eq_zero] at h0
            rw [h0] at this
            simp at this
          have hHi : ¬ (a i = true ∧ b i = true) := by
            intro hab
            have : i ∈ Finset.univ.filter fun i => a i = true ∧ b i = true := by simp [hab]
            have h0 : (Finset.univ.filter fun i => a i = true ∧ b i = true).card = 0 := hH0
            rw [Finset.card_eq_zero] at h0
            rw [h0] at this
            simp at this
          cases ha : a i <;> cases hb : b i <;> simp_all
        rcases hne with h | h
        · exact h (funext fun i => (hall i).1)
        · exact h (funext fun i => (hall i).2)
      · exact Or.inl ⟨rfl, hH0⟩
      · refine Or.inr (Or.inl ⟨rfl, hH0, ?_, ?_⟩)
        · have h4 : ∀ c ∈ pairOrbit f c₀, 4 ≤ rk c := by
            intro c hc
            have := hrk c hc
            rw [hH0, pow_zero, mul_one] at this
            norm_num at this
            omega
          have := hsum 4 h4
          rw [mul_comm] at this
          exact this
        · have := hfS (by norm_num)
          rw [mul_comm] at this
          exact this
    · right; right; right
      have hb : ∀ c ∈ pairOrbit f c₀, 4 * S + 1 ≤ rk c := by
        intro c hc
        have h1 := hrk c hc
        rw [hH0, pow_zero, mul_one] at h1
        have h2 := eight_mul_add_three_le_three_pow hS3'
        omega
      have h1 := hsum _ hb
      have h2 := hfS (by omega)
      nlinarith
  ·
    have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hH0
    have hfH : f ≤ o * H := orbit_cover hf pH c₀ (Finset.card_pos.mp (show 0 < H by omega))
    by_cases hS01 : S = 0 ∧ H = 1
    · obtain ⟨hS0, hH1'⟩ := hS01
      right; right; left
      have hof' : o = f := by
        rw [hH1', mul_one] at hfH
        omega
      refine ⟨hS0, hH1', hof', ?_⟩
      have h4 : ∀ c ∈ pairOrbit f c₀, 4 ≤ rk c := by
        intro c hc
        have := hrk c hc
        rw [hS0, hH1', pow_zero, one_mul] at this
        norm_num at this
        omega
      have := hsum 4 h4
      rw [hof'] at this
      omega
    · right; right; right
      have hb : ∀ c ∈ pairOrbit f c₀, 4 * H + 1 ≤ rk c := by
        intro c hc
        have h1 := hrk c hc
        have h2 := eight_mul_add_three_le hH1 hS01
        omega
      have h1 := hsum _ hb
      nlinarith

end Combinatorics

end B45SL3

end CFSG.Quasithin

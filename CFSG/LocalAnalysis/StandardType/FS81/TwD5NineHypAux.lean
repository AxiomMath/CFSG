module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Main
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixInv
public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OE6
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainAlg
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.StandardType.FrameRoute.FS81.NineHyp

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open scoped Matrix

theorem gl_mul_inv_eq_one (x : GL (Fin (5 + 1)) (ZMod 3)) :
    ((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *
      (((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))) = 1 := by
  change (((x * x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
    Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) = 1)
  rw [mul_inv_cancel, Units.val_one]

theorem gl_inv_mul_eq_one (x : GL (Fin (5 + 1)) (ZMod 3)) :
    (((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *
      ((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))) = 1 := by
  change (((x⁻¹ * x : GL (Fin (5 + 1)) (ZMod 3)) :
    Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) = 1)
  rw [inv_mul_cancel, Units.val_one]

abbrev glMat (y : GL (Fin (5 + 1)) (ZMod 3)) :
    Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
  (y : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))

theorem gl_mulVec_inv_mul (x : GL (Fin (5 + 1)) (ZMod 3)) (v : Coords (5 + 1)) :
    ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ
      ((x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec]
  change (((x⁻¹ * x : GL (Fin (5 + 1)) (ZMod 3)) :
    Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ v) = v
  have h : ((x⁻¹ * x : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) = 1 := by
    rw [show x⁻¹ * x = (1 : GL (Fin (5 + 1)) (ZMod 3)) from inv_mul_cancel x,
      Units.val_one]
  rw [h, Matrix.one_mulVec]

@[expose] def e06 : Coords (5 + 1) := Pi.single 0 1

@[expose] def e01 : Coords (5 + 1) := Pi.single 0 1 + Pi.single 1 1

theorem isSign_one {k : ℕ} : IsSign (fun _ : Fin k => (1 : ZMod 3)) := fun _ => Or.inl rfl

theorem spMatGL_one_inv (σ : Equiv.Perm (Fin (5 + 1))) :
    ((spMatGL σ (fun _ => (1 : ZMod 3)) isSign_one)⁻¹ :
      GL (Fin (5 + 1)) (ZMod 3)) =
      spMatGL σ.symm (fun _ => (1 : ZMod 3)) isSign_one := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, spMatGL_val, spMatGL_val, spMat_mul]
  rw [show σ * σ.symm = 1 from mul_inv_cancel σ]
  simp [spMat_one]

theorem spMatGL_one_mulVec_e06 (σ : Equiv.Perm (Fin (5 + 1))) (hσ0 : σ 0 = 0) :
    (((spMatGL σ (fun _ => (1 : ZMod 3)) isSign_one :
        GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06) = e06 := by
  rw [spMatGL_val, e06, spMat_mulVec_single, hσ0, one_mul]

@[expose] def e02 : Coords (5 + 1) := Pi.single 0 1 + Pi.single 2 1

theorem wt_e01_add (w : Coords (5 + 1)) (h0 : w 0 = 0) (h1 : w 1 = 0) :
    wt (e01 + w) = 2 + wt w := by
  revert w
  decide +kernel

theorem wt_neg_e01_add (w : Coords (5 + 1)) (h0 : w 0 = 0) (h1 : w 1 = 0) :
    wt (-e01 + w) = 2 + wt w := by
  revert w
  decide +kernel

theorem full_support_of_wt_four (w : Coords (5 + 1)) (h0 : w 0 = 0) (h1 : w 1 = 0)
    (hw : wt w = 4) : ∀ k : Fin 4, w k.succ.succ ≠ 0 := by
  revert w
  decide +kernel

theorem exists_gl_moves_e0 {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)}
    {b₀ : G} {K E : Subgroup G} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hfus : Fus42 B b₀) :
    ∃ x : GL (Fin (5 + 1)) (ZMod 3),
      x ∈ (ggAutomizer ⊤ B.span).map B.glHom ∧
        (((x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = e01) ∨
          ((x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = -e01)) := by
  classical
  have he01 : e01 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [e01] at h0
  have hshape : (wt e01 ≤ 2 ∧ e01 0 ≠ 0) ∨ (wt e01 = 6 ∧ ∏ i, e01 i = 1) := by
    decide +kernel
  have hline : IsConjLine b₀ (B.line e01) :=
    (hrec.2.2.2 e01 he01).mpr hshape
  have hline' : IsConjLineIn B.span b₀ (B.line e01) :=
    (B.isConjLine_iff_isConjLineIn hfus e01).mp hline
  have hb0 : B.vec e06 = b₀ := by
    rw [e06, B.vec_single, hB.2.1]
  rw [← hb0, B.isConjLineIn_iff_exists_mulVec e06 he01] at hline'
  rcases hline' with ⟨x, hx, hxmov⟩ | ⟨x, hx, hxmov⟩
  · exact ⟨x, hx, Or.inl hxmov⟩
  · exact ⟨x, hx, Or.inr hxmov⟩

@[expose] def tMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.diagonal fun i => if i = 0 ∨ i = 1 then -1 else 1

@[expose] def tSign : Fin 6 → ZMod 3 := fun i => if i = 0 ∨ i = 1 then -1 else 1

theorem tMat_eq_spMat : tMat = spMat (1 : Equiv.Perm (Fin 6)) tSign := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [tMat, tSign, spMat_apply]
  · simp [tMat, spMat_apply, hij]

theorem conj_tMat_mulVec_e06 (x : GL (Fin (5 + 1)) (ZMod 3))
    (hmove : ((((x : GL (Fin (5 + 1)) (ZMod 3)) :
          Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = e01) ∨
      (((x : GL (Fin (5 + 1)) (ZMod 3)) :
          Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = -e01))) :
    ((((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
          Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) * tMat *
        (x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))) *ᵥ e06) = -e06 := by
  have ht : tMat *ᵥ e01 = -e01 := by decide +kernel
  rcases hmove with h | h
  · have hxinv : ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e01 = e06 := by
      rw [← h, gl_mulVec_inv_mul]
    rw [← Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_neg, hxinv]
  · have hxneg : ((x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ (-e06)) = e01 := by
      rw [Matrix.mulVec_neg, h, neg_neg]
    have hxinv : ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e01 = -e06 := by
      rw [← hxneg, gl_mulVec_inv_mul]
    rw [← Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg, ht, neg_neg,
      hxinv]

theorem conj_swap_tMat (j : Fin 6) (hj : j ≠ 0) :
    spMat (Equiv.swap 1 j) (fun _ => (1 : ZMod 3)) * tMat *
        spMat (Equiv.swap 1 j).symm (fun _ => (1 : ZMod 3)) =
      Matrix.diagonal (fun i => if i = 0 ∨ i = j then -1 else 1) := by
  revert j
  decide +kernel

theorem tMat_mul_self : tMat * tMat = 1 := by
  rw [tMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = 0 ∨ i = 1 <;> simp [h]

theorem pow_two_eq_inv_of_orderOf_three {G : Type} [Group G] {b : G} (hb : orderOf b = 3) :
    b ^ 2 = b⁻¹ := by
  have h3 : b ^ 3 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have h : b ^ 2 * b = 1 := by simpa [pow_succ] using h3
  exact eq_inv_of_mul_eq_one_left h

theorem acts_tMat_of {G : Type} [Group G] {B : Basis3 G (5 + 1)} {t : G}
    (ht : orderOf t = 2)
    (ht0 : t * B.b 0 * t⁻¹ = (B.b 0)⁻¹) (ht1 : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹)
    (ht2 : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) :
    B.Acts t tMat := by
  have ht2sq : t * t = 1 := by simpa [ht, pow_two] using pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2sq
  rw [tMat_eq_spMat, B.acts_spMat_iff]
  intro j
  by_cases hj0 : j = 0
  · subst hj0
    rw [ht0, tSign]
    simp only [true_or, if_true]
    exact (pow_two_eq_inv_of_orderOf_three (B.ord 0)).symm
  · by_cases hj1 : j = 1
    · subst hj1
      rw [ht1, tSign]
      simp only [Fin.isValue, or_true, ↓reduceIte]
      exact (pow_two_eq_inv_of_orderOf_three (B.ord 1)).symm
    · have hj2 : 2 ≤ j.val := by
        have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
        have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext (by simpa using h))
        omega
      have hsign : tSign j = 1 := by
        simp only [tSign]
        rw [if_neg (by rintro (h | h); exacts [hj0 h, hj1 h])]
      rw [ht2 j hj2, htinv, hsign, ZMod.val_one, pow_one]
      rw [mul_assoc, ht2sq, mul_one]
      simp

theorem mem_centralizer_span_of_acts_one {G : Type} [Group G] {B : Basis3 G (5 + 1)}
    {h : G} (hActs : B.Acts h 1) :
    h ∈ Subgroup.centralizer (B.span : Set G) := by
  have hle : B.span ≤ Subgroup.centralizer ({h} : Set G) := by
    rw [Basis3.span, Subgroup.closure_le]
    rintro y ⟨j, rfl⟩
    have hj := hActs j
    have hcol : (fun i => (1 : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) i j) =
        Pi.single j 1 := by
      ext i
      simp [Matrix.one_apply, Pi.single_apply]
    rw [hcol, Basis3.vec_single] at hj
    change B.b j ∈ Subgroup.centralizer ({h} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc B.b j * h = (h * B.b j * h⁻¹) * h := by rw [hj]
      _ = h * B.b j := by group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem exists_centralizer_acts_of_commute {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {t : G} (ht : orderOf t = 2) (hActsT : B.Acts t tMat)
    {g : G} (hgN : g ∈ Subgroup.normalizer (B.span : Set G))
    {A : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)} (hActsG : B.Acts g A)
    (hcomm : A * tMat = tMat * A) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), B.Acts c A := by
  classical
  have ht2sq : t * t = 1 := by simpa [ht, pow_two] using pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2sq
  obtain ⟨M, hActsGinv⟩ := B.exists_acts (Subgroup.inv_mem _ hgN)
  have hAM : A * M = 1 := by
    have h1 : B.Acts (g * g⁻¹) (A * M) := B.acts_mul hActsG hActsGinv
    rw [mul_inv_cancel] at h1
    exact B.acts_unique h1 B.acts_one
  have hActsTinv : B.Acts t⁻¹ tMat := by rwa [htinv]
  have hActsGtg : B.Acts (g * t * g⁻¹) tMat := by
    have h1 : B.Acts (g * t) (A * tMat) := B.acts_mul hActsG hActsT
    have h2 : B.Acts ((g * t) * g⁻¹) ((A * tMat) * M) := B.acts_mul h1 hActsGinv
    have hmat : (A * tMat) * M = tMat := by
      calc (A * tMat) * M = (tMat * A) * M := by rw [hcomm]
        _ = tMat * (A * M) := by rw [mul_assoc]
        _ = tMat := by rw [hAM, mul_one]
    rw [hmat] at h2
    simpa only [mul_assoc] using h2
  have hActsH : B.Acts ((g * t * g⁻¹) * t⁻¹) 1 := by
    have h := B.acts_mul hActsGtg hActsTinv
    rw [tMat_mul_self] at h
    simpa only [mul_assoc] using h
  have htN : t ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hActsT
  have hN : (g * t * g⁻¹) * t⁻¹ ∈ Subgroup.normalizer (B.span : Set G) :=
    (Subgroup.normalizer (B.span : Set G)).mul_mem
      ((Subgroup.normalizer (B.span : Set G)).mul_mem
        ((Subgroup.normalizer (B.span : Set G)).mul_mem hgN htN)
        ((Subgroup.normalizer (B.span : Set G)).inv_mem hgN))
      ((Subgroup.normalizer (B.span : Set G)).inv_mem htN)
  set h : G := (g * t * g⁻¹) * t⁻¹ with hhdef
  have hActsH' : B.Acts h 1 := hActsH
  have hhC : h ∈ Subgroup.centralizer (B.span : Set G) :=
    mem_centralizer_span_of_acts_one hActsH'
  have hhOdd : Odd (orderOf h) :=
    Odd.of_dvd_nat hodd
      (Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (B.span : Set G)) hhC)
  have hg_conj : g * t * g⁻¹ = h * t := by
    rw [hhdef]
    group
  set h' : G := g⁻¹ * h⁻¹ * g with hh'def
  have hh'C : h' ∈ Subgroup.centralizer (B.span : Set G) := by
    have hhCinv : h⁻¹ ∈ Subgroup.centralizer (B.span : Set G) :=
      (Subgroup.centralizer (B.span : Set G)).inv_mem hhC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hgy : g * y * g⁻¹ ∈ B.span :=
      (Subgroup.mem_normalizer_iff.mp hgN y).mp hy
    have hcomm := Subgroup.mem_centralizer_iff.mp hhCinv (g * y * g⁻¹) hgy
    rw [hh'def]
    calc y * (g⁻¹ * h⁻¹ * g) = g⁻¹ * (g * y * g⁻¹) * h⁻¹ * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * h⁻¹) * g := by group
      _ = g⁻¹ * (h⁻¹ * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * h⁻¹ * g) * y := by group
  have hh'Ord : orderOf h' = orderOf h := by
    rw [hh'def]
    have h1 : orderOf (g⁻¹ * h⁻¹ * g) = orderOf h⁻¹ := by
      simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) h⁻¹)
    rw [h1, orderOf_inv]
  have hh'Odd : Odd (orderOf h') := by rw [hh'Ord]; exact hhOdd
  have ht_gt : g⁻¹ * t * g = h' * t := by
    have h1 : t = (g⁻¹ * h * g) * (g⁻¹ * t * g) := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * (h * t) * g := by rw [hg_conj]
        _ = (g⁻¹ * h * g) * (g⁻¹ * t * g) := by group
    have h2 : g⁻¹ * h * g = h'⁻¹ := by
      rw [hh'def]
      group
    rw [h2] at h1
    have hX : h' * t = g⁻¹ * t * g := by
      conv_lhs => rw [h1]
      group
    exact hX.symm
  have ht_h' : t * h' * t = h'⁻¹ := by
    have h2 : (h' * t) * (h' * t) = 1 := by
      have ht' : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
        calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [ht2sq]; group
      simpa only [ht_gt] using ht'
    have h3 : t * h' * t = h'⁻¹ := by
      have h4 := congrArg (fun x => h'⁻¹ * x) h2
      simpa [mul_assoc] using h4
    exact h3
  have ht_h'_inv : t * h'⁻¹ = h' * t := by
    have h4 : t * h'⁻¹ * t = h' := by
      have h5 := congrArg Inv.inv ht_h'
      simpa [htinv, mul_assoc] using h5
    calc t * h'⁻¹ = (t * h'⁻¹) * (t * t) := by rw [ht2sq, mul_one]
      _ = (t * h'⁻¹ * t) * t := by group
      _ = h' * t := by rw [h4]
  set n : ℕ := orderOf h' with hn_def
  have hn_odd : Odd n := hh'Odd
  have hn_pos : 0 < n := orderOf_pos h'
  set m : ℕ := (n + 1) / 2 with hm_def
  have h2m : 2 * m = n + 1 := by
    rcases hn_odd with ⟨r, hr⟩
    dsimp [m]
    omega
  set k : G := h' ^ m with hk_def
  have hk_sq : k * k = h' := by
    rw [hk_def]
    calc h' ^ m * h' ^ m = h' ^ (m + m) := (pow_add h' m m).symm
      _ = h' ^ (2 * m) := by ring_nf
      _ = h' ^ (n + 1) := by rw [h2m]
      _ = h' ^ n * h' := pow_succ h' n
      _ = h' := by rw [show h' ^ n = 1 by simp [n], one_mul]
  have hconj_pow : ∀ q : ℕ, t * h' ^ q * t = (h' ^ q)⁻¹ := by
    intro q
    have hconj : MulAut.conj t h' = h'⁻¹ := by
      rw [MulAut.conj_apply, htinv]
      exact ht_h'
    calc t * h' ^ q * t = MulAut.conj t (h' ^ q) := by rw [MulAut.conj_apply, htinv]
      _ = (MulAut.conj t h') ^ q := map_pow _ _ _
      _ = (h'⁻¹) ^ q := by rw [hconj]
      _ = (h' ^ q)⁻¹ := inv_pow h' q
  have hk_t : k * t = t * k⁻¹ := by
    have h := hconj_pow m
    calc k * t = (t * t) * (k * t) := by rw [ht2sq, one_mul]
      _ = t * (t * k * t) := by group
      _ = t * k⁻¹ := by rw [h]
  have hk_conj_t : k * t * k⁻¹ = h' * t := by
    calc k * t * k⁻¹ = (t * k⁻¹) * k⁻¹ := by rw [hk_t]
      _ = t * (k⁻¹ * k⁻¹) := by group
      _ = t * (k * k)⁻¹ := by rw [← mul_inv_rev]
      _ = t * h'⁻¹ := by rw [hk_sq]
      _ = h' * t := ht_h'_inv
  have hgh' : g * h' * g⁻¹ = h⁻¹ := by
    have h1 : t = (g * h' * g⁻¹) * (g * t * g⁻¹) := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = g * (h' * t) * g⁻¹ := by rw [ht_gt]
        _ = (g * h' * g⁻¹) * (g * t * g⁻¹) := by group
    rw [hg_conj] at h1
    have hA : g * h' * g⁻¹ = t * (h * t)⁻¹ := by
      nth_rewrite 1 [h1]
      group
    have hcalc : t * (h * t)⁻¹ = h⁻¹ := by
      rw [mul_inv_rev, htinv, ← mul_assoc, ht2sq, one_mul]
    calc g * h' * g⁻¹ = t * (h * t)⁻¹ := hA
      _ = h⁻¹ := hcalc
  have hc_eq : (g * k) * t * (g * k)⁻¹ = t := by
    calc (g * k) * t * (g * k)⁻¹ = g * (k * t * k⁻¹) * g⁻¹ := by group
      _ = g * (h' * t) * g⁻¹ := by rw [hk_conj_t]
      _ = (g * h' * g⁻¹) * (g * t * g⁻¹) := by group
      _ = h⁻¹ * (h * t) := by rw [hgh', hg_conj]
      _ = t := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨g * k, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * k) * t = ((g * k) * t * (g * k)⁻¹) * (g * k) := by group
      _ = t * (g * k) := by rw [hc_eq]
  · have hkC : k ∈ Subgroup.centralizer (B.span : Set G) :=
      Subgroup.pow_mem _ hh'C m
    have hkActs : B.Acts k 1 := by
      intro j
      have hcol : (fun i => (1 : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) i j) =
          Pi.single j 1 := by
        ext i
        simp [Matrix.one_apply, Pi.single_apply]
      rw [hcol, Basis3.vec_single]
      have hcommk := Subgroup.mem_centralizer_iff.mp hkC (B.b j) (B.b_mem_span j)
      calc k * B.b j * k⁻¹ = (B.b j * k) * k⁻¹ := by rw [hcommk]
        _ = B.b j := by group
    have h := B.acts_mul hActsG hkActs
    simpa only [mul_one] using h

@[expose] def e62 : Fin 6 ⊕ Fin 2 ≃ Fin 8 := finSumFinEquiv

@[expose] noncomputable def ext2 (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) e62 (Matrix.fromBlocks M 0 0 (-1))

@[expose] def extPerm (σ : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 8) :=
  e62.symm.trans ((Equiv.sumCongr σ (Equiv.refl (Fin 2))).trans e62)

@[expose] def extSign (s : Fin 6 → ZMod 3) : Fin 8 → ZMod 3 :=
  fun i => Sum.elim s (fun _ => -1) (e62.symm i)

theorem ext2_spMat (σ : Equiv.Perm (Fin 6)) (s : Fin 6 → ZMod 3) :
    ext2 (spMat σ s) = spMat (extPerm σ) (extSign s) := by
  classical
  ext i j
  rcases hi : e62.symm i with a | a <;> rcases hj : e62.symm j with b | b
  · have hia : i = e62 (Sum.inl a) := by rw [← hi]; simp
    have hjb : j = e62 (Sum.inl b) := by rw [← hj]; simp
    rw [hia, hjb]
    simp [ext2, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.fromBlocks,
      spMat, extPerm, extSign]
  · have hia : i = e62 (Sum.inl a) := by rw [← hi]; simp
    have hjb : j = e62 (Sum.inr b) := by rw [← hj]; simp
    rw [hia, hjb]
    simp [ext2, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.fromBlocks,
      spMat, extPerm]
  · have hia : i = e62 (Sum.inr a) := by rw [← hi]; simp
    have hjb : j = e62 (Sum.inl b) := by rw [← hj]; simp
    rw [hia, hjb]
    simp [ext2, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.fromBlocks,
      spMat, extPerm]
  · have hia : i = e62 (Sum.inr a) := by rw [← hi]; simp
    have hjb : j = e62 (Sum.inr b) := by rw [← hj]; simp
    rw [hia, hjb]
    simp [ext2, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.fromBlocks,
      Matrix.neg_apply, Matrix.one_apply, spMat, extPerm, extSign]
    by_cases hab : a = b <;> simp [hab]

theorem e62_symm_zero : e62.symm (0 : Fin 8) = Sum.inl 0 := by
  change Fin.addCases Sum.inl Sum.inr (Fin.castAdd 2 (0 : Fin 6) : Fin 8) = Sum.inl 0
  rw [Fin.addCases_left]

theorem e62_inl_zero : e62 (Sum.inl (0 : Fin 6)) = (0 : Fin 8) := by
  change (Fin.castAdd 2 (0 : Fin 6) : Fin 8) = 0
  rfl

theorem ext2_mem_evenFix0 {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ evenFix0 5) :
    ext2 M ∈ evenFix0 7 := by
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hprod5⟩, rfl⟩ := hM
  rw [ext2_spMat]
  have hprod6 : ∏ i : Fin 6, s i = 1 := by
    rw [Fin.prod_univ_succ, hs0, one_mul]
    exact hprod5
  have hprod8 : ∏ i : Fin 8, extSign s i = 1 := by
    rw [show (∏ i : Fin 8, extSign s i) =
        ∏ x : Fin 6 ⊕ Fin 2, Sum.elim s (fun _ => -1) x by
      simp [extSign, Equiv.prod_comp]]
    rw [Fintype.prod_sumElim, hprod6]
    simp
  refine ⟨extPerm σ, extSign s, ?_, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro i
    rcases hi : e62.symm i with a | a
    · simpa [extSign, hi] using hs a
    · have hneg : extSign s i = -1 := by simp [extSign, hi]
      exact Or.inr hneg
  · simp only [extPerm, Equiv.coe_trans, Function.comp_apply]
    rw [e62_symm_zero]
    simp only [Equiv.sumCongr_apply]
    change e62 (Sum.inl (σ 0)) = 0
    rw [hσ0, e62_inl_zero]
  · show extSign s 0 = 1
    simp only [extSign]
    rw [e62_symm_zero]
    simpa using hs0
  · have h0 : extSign s 0 = 1 := by
      show extSign s 0 = 1
      simp only [extSign]
      rw [e62_symm_zero]
      simpa using hs0
    have h7 := hprod8
    rw [Fin.prod_univ_succ, h0, one_mul] at h7
    exact h7

@[expose] def E2 {G : Type} [Group G] (B : Basis3 G (5 + 1)) : Subgroup G :=
  Subgroup.closure (Set.range fun i : Fin 4 => B.b i.succ.succ)

@[expose] def ext4 (w : Fin 4 → ZMod 3) : Coords (5 + 1) :=
  Fin.cons 0 (Fin.cons 0 w)

theorem ext4_single (i : Fin 4) :
    ext4 (Pi.single i 1) = Pi.single i.succ.succ 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem vec_ext4 {G : Type} [Group G] {B : Basis3 G (5 + 1)} (w : Fin 4 → ZMod 3) :
    B.vec (ext4 w) =
      (List.ofFn fun i : Fin 4 => B.b i.succ.succ ^ (w i).val).prod := by
  unfold Basis3.vec ext4
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Fin.cons_zero,
    Fin.cons_succ, Fin.succ_zero_eq_one, pow_zero, one_mul, ZMod.val_zero]

theorem vec_ext4_mem {G : Type} [Group G] {B : Basis3 G (5 + 1)} (w : Fin 4 → ZMod 3) :
    B.vec (ext4 w) ∈ E2 B := by
  rw [vec_ext4]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (Subgroup.closure (Set.range fun i : Fin 4 => B.b i.succ.succ)).pow_mem
    (Subgroup.subset_closure ⟨i, rfl⟩) _

theorem coord_special (f : Fin 4 → ZMod 3) (_hf : f ≠ 0) :
    ∃ w : Fin 4 → ZMod 3, (∑ i, f i * w i = 0) ∧
      ((∃ i, w = Pi.single i 1) ∨ ∀ i, w i ≠ 0) := by
  classical
  by_cases hzero : ∃ i, f i = 0
  · obtain ⟨i, hi⟩ := hzero
    refine ⟨Pi.single i 1, ?_, Or.inl ⟨i, rfl⟩⟩
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · push Not at hzero
    let eps : Fin 4 → ZMod 3 := ![1, 1, -1, -1]
    refine ⟨fun i => eps i * (f i)⁻¹, ?_, Or.inr ?_⟩
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, eps]
      field_simp [hzero 0, hzero 1, hzero 2, hzero 3]
      norm_num
    · intro i
      fin_cases i <;> simp [eps, hzero]

theorem index_subgroupOf_E2 {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)}
    {H : Subgroup G} (hH : H ∈ Coprime.hyperplanes 3 (E2 B)) :
    (H.subgroupOf (E2 B)).index = 3 := by
  obtain ⟨hHle, hHcard⟩ := hH
  have hsubcard : Nat.card (H.subgroupOf (E2 B)) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  have hmul := (H.subgroupOf (E2 B)).index_mul_card
  rw [hsubcard, hHcard] at hmul
  exact Nat.mul_right_cancel Nat.card_pos hmul

theorem isElemAbelian_E2 {G : Type} [Group G] {B : Basis3 G (5 + 1)} :
    CFSG.Open.IsElemAbelian 3 (E2 B) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact B.comm _ _
  · rintro a ⟨i, rfl⟩
    have h3 : B.b i.succ.succ ^ 3 = 1 := by
      rw [← B.ord i.succ.succ]
      exact pow_orderOf_eq_one _
    exact h3

theorem E2_comm {G : Type} [Group G] {B : Basis3 G (5 + 1)} {x y : G}
    (hx : x ∈ E2 B) (hy : y ∈ E2 B) : x * y = y * x :=
  (isElemAbelian_E2 (B := B)).comm hx hy

theorem hyperplane_special {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)}
    {H : Subgroup G} (hH : H ∈ Coprime.hyperplanes 3 (E2 B)) :
    ∃ w : Fin 4 → ZMod 3, B.vec (ext4 w) ∈ H ∧
      ((∃ i, w = Pi.single i 1) ∨ ∀ i, w i ≠ 0) := by
  classical
  let D := H.subgroupOf (E2 B)
  have hDidx : D.index = 3 := index_subgroupOf_E2 hH
  have hE := isElemAbelian_E2 (B := B)
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup (E2 B) := { mul_comm := fun a b => Subtype.ext (E2_comm (B := B) a.2 b.2) }
  let _ : CFSG.IsElementaryAbelian 3 (E2 B) := hE.isElementaryAbelian
  let _ : Module (ZMod 3) (Additive (E2 B)) := CFSG.IsElementaryAbelian.isVectorSpace 3
  let p : Submodule (ZMod 3) (Additive (E2 B)) :=
    AddSubgroup.toZModSubmodule (n := 3) D.toAddSubgroup
  have hp : p.toAddSubgroup.index = 3 := by
    simpa [p] using hDidx
  have hcoat : IsCoatom p :=
    (CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.coatom_iff_index p).mpr hp
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top p hcoat.lt_top
  have hkerCoat := LinearMap.isCoatom_ker_of_surjective
    (LinearMap.surjective_of_ne_zero hf)
  have hpker : p = f.ker := ((hcoat.le_iff_eq hkerCoat.1).mp hle).symm
  let Φadd : (Fin 4 → ZMod 3) →+ Additive (E2 B) :=
    { toFun := fun w => Additive.ofMul ⟨B.vec (ext4 w), vec_ext4_mem (B := B) w⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change B.vec (ext4 (0 : Fin 4 → ZMod 3)) = 1
        rw [show ext4 (0 : Fin 4 → ZMod 3) = 0 by
          ext j
          fin_cases j <;> rfl, B.vec_zero]
      map_add' := by
        intro w w'
        apply Additive.toMul.injective
        apply Subtype.ext
        change B.vec (ext4 (w + w')) = B.vec (ext4 w) * B.vec (ext4 w')
        rw [show ext4 (w + w') = ext4 w + ext4 w' by
          ext j
          fin_cases j <;> rfl]
        exact B.vec_add _ _ }
  let Φ : (Fin 4 → ZMod 3) →ₗ[ZMod 3] Additive (E2 B) :=
    AddMonoidHom.toZModLinearMap 3 Φadd
  let f0 : Fin 4 → ZMod 3 := fun i => f (Φ (Pi.single i 1))
  have hg : ∀ w : Fin 4 → ZMod 3, f (Φ w) = ∑ i, f0 i * w i := by
    intro w
    have hw : w = ∑ i : Fin 4, w i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc f (Φ w) = f (Φ (∑ i : Fin 4, w i • Pi.single i 1)) := by
          conv_lhs => rw [hw]
      _ = f (∑ i : Fin 4, w i • Φ (Pi.single i 1)) := by
          congr 1
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
      _ = ∑ i : Fin 4, w i • f (Φ (Pi.single i 1)) := by
          rw [map_sum]
          simp only [map_smul]
      _ = ∑ i : Fin 4, f0 i * w i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_eq_mul, mul_comm]
  have mem_H_of_mem_ker : ∀ {w : Fin 4 → ZMod 3}, Φ w ∈ f.ker → B.vec (ext4 w) ∈ H := by
    intro w hmem
    rw [← hpker] at hmem
    have hΦ : Additive.toMul (Φ w) =
        (⟨B.vec (ext4 w), vec_ext4_mem (B := B) w⟩ : E2 B) := rfl
    have hmemD : (⟨B.vec (ext4 w), vec_ext4_mem (B := B) w⟩ : E2 B) ∈ D := by
      simpa [p, hΦ] using hmem
    simpa [D, Subgroup.mem_subgroupOf] using hmemD
  by_cases hf0 : f0 = 0
  · refine ⟨Pi.single 0 1, ?_, Or.inl ⟨0, rfl⟩⟩
    apply mem_H_of_mem_ker
    rw [LinearMap.mem_ker, hg, hf0]
    simp
  · obtain ⟨w, hwsum, hw⟩ := coord_special f0 hf0
    refine ⟨w, ?_, hw⟩
    apply mem_H_of_mem_ker
    rw [LinearMap.mem_ker, hg w, hwsum]

theorem neg_mem_evenFix0_of_mem_evenAll0 {u : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hu : u ∈ evenAll0 5) (hu0 : u *ᵥ Pi.single 0 1 = -Pi.single 0 1) :
    -u ∈ evenFix0 5 := by
  obtain ⟨σ, s, hs, ⟨hσ0, hprod⟩, rfl⟩ := hu
  have hs0 : s 0 = -1 := by
    have h := congrFun hu0 0
    rw [spMat_mulVec_single] at h
    rw [hσ0] at h
    simpa using h
  have hprod_succ : ∏ i : Fin 5, s i.succ = -1 := by
    have h := hprod
    rw [Fin.prod_univ_succ, hs0] at h
    have h' : (-1 : ZMod 3) * (∏ i : Fin 5, s i.succ) = 1 := h
    calc ∏ i : Fin 5, s i.succ = (-1 : ZMod 3) * ((-1) * ∏ i : Fin 5, s i.succ) := by
          ring
      _ = (-1) * 1 := by rw [h']
      _ = -1 := by decide
  have hnegprod : ∏ i : Fin 5, (-s i.succ) = 1 := by
    rw [show (fun i : Fin 5 => -s i.succ) = fun i : Fin 5 => (-1 : ZMod 3) * s i.succ by
      funext i; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin, hprod_succ]
    norm_num
  refine ⟨σ, fun i => -s i, ?_, ⟨hσ0, ?_, hnegprod⟩, ?_⟩
  · intro i
    change -s i = 1 ∨ -s i = -1
    rcases hs i with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; decide)
  · change -s 0 = 1
    rw [hs0]
    decide
  · ext i j
    by_cases h : i = σ j <;> simp [spMat, h]

theorem ext2_injective : Function.Injective ext2 := by
  intro A B h
  have h1 : Matrix.fromBlocks A 0 0 (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      Matrix.fromBlocks B 0 0 (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
    (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) e62).injective h
  exact (Matrix.fromBlocks_inj.mp h1).1

theorem exists_missing_first6 (T : Finset (Fin 8)) (h0 : (0 : Fin 8) ∉ T)
    (hcard : T.card = 6) (h6 : e62 (Sum.inr 0) ∈ T) (h7 : e62 (Sum.inr 1) ∈ T) :
    ∃ j : Fin 6, j ≠ 0 ∧ Tᶜ = ({0, e62 (Sum.inl j)} : Finset (Fin 8)) := by
  classical
  revert T
  decide +kernel

theorem ext2_diagonal_pos_eq_sgn_compl (j : Fin 6) (hj : j ≠ 0) :
    ext2 (Matrix.diagonal fun i => if i = 0 ∨ i = j then 1 else -1) =
      sgn (({0, e62 (Sum.inl j)} : Finset (Fin 8))ᶜ) := by
  revert j
  decide +kernel

theorem ext2_neg_tMat : ext2 (-tMat) = sgn ({2, 3, 4, 5, 6, 7} : Finset (Fin 8)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem fixCount_ext2_neg_tMat : fixCount (ext2 (-tMat)) = 9 := by
  rw [ext2_neg_tMat, q2nN7_fixCount_sgn]
  norm_num

theorem ext2_mul (A B : Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    ext2 A * ext2 B =
      Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) e62
        (Matrix.fromBlocks (A * B) 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) := by
  rw [ext2, ext2, ← map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

theorem ext2_mul_inv {A : Matrix (Fin 6) (Fin 6) (ZMod 3)} {B : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hAB : A * B = 1) : ext2 A * ext2 B = 1 := by
  rw [ext2_mul, hAB]
  simp [Matrix.fromBlocks_one]

theorem ext2_mul_three (A B C : Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    ext2 A * ext2 B * ext2 C = ext2 (A * B * C) := by
  simp [ext2, Matrix.fromBlocks_multiply, mul_assoc]

theorem ext2_apply_inr_self (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (a : Fin 2) :
    ext2 M (e62 (Sum.inr a)) (e62 (Sum.inr a)) = -1 := by
  simp [ext2, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.fromBlocks,
    Matrix.neg_apply]

theorem exists_y_full_support {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)}
    {b₀ : G} {K E : Subgroup G} (_hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    {t : G} (_hActsT : B.Acts t tMat)
    (x : GL (Fin (5 + 1)) (ZMod 3))
    (hxX : x ∈ (ggAutomizer ⊤ B.span).map B.glHom)
    (hmove : ((((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = e01) ∨
      (((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = -e01)))
    (j : Fin 6) (hj : j ≠ 0)
    (u : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
    (hu_eq : u = ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) * tMat *
        ((x : GL (Fin (5 + 1)) (ZMod 3)) :
          Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)))
    (hdiag : u = Matrix.diagonal (fun i => if i = 0 ∨ i = j then -1 else 1)) :
    ∃ (y : GL (Fin (5 + 1)) (ZMod 3)),
      glMat y * tMat = tMat * glMat y ∧
      (glMat y *ᵥ e06 = e01 ∨ glMat y *ᵥ e06 = -e01) ∧
      (∀ k : Fin 4, (glMat y *ᵥ Pi.single 2 1) k.succ.succ ≠ 0) ∧
      ∃ gy ∈ Subgroup.normalizer (B.span : Set G), B.Acts gy (glMat y) := by
  classical
  let σ : Equiv.Perm (Fin (5 + 1)) := Equiv.swap 1 j
  have hσ0 : σ 0 = 0 := by
    rw [Equiv.swap_apply_def]
    simp [Ne.symm hj]
  let n : GL (Fin (5 + 1)) (ZMod 3) :=
    spMatGL σ (fun _ => (1 : ZMod 3)) isSign_one
  let X : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((x : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  let N : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((n : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  let Y : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  let Ninv : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((n⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  have huX : u = Y * tMat * X := hu_eq
  have hNmat : N = spMat σ (fun _ => (1 : ZMod 3)) := spMatGL_val σ _ isSign_one
  have hNinv : Ninv = spMat σ.symm (fun _ => (1 : ZMod 3)) := by
    dsimp only [Ninv, n]
    rw [spMatGL_one_inv σ, spMatGL_val]
  have hN0 : N *ᵥ e06 = e06 := by
    rw [hNmat, ← spMatGL_val σ (fun _ => (1 : ZMod 3)) isSign_one]
    exact spMatGL_one_mulVec_e06 σ hσ0
  have huN : N * tMat * Ninv = u := by
    rw [hNmat, hNinv, conj_swap_tMat j hj, hdiag]
  have hNt : N * tMat = u * N := by
    calc N * tMat = ((N * tMat) * Ninv) * N := by
          rw [mul_assoc, gl_inv_mul_eq_one n, mul_one]
      _ = u * N := by rw [huN]
  have hXY : X * Y = 1 := gl_mul_inv_eq_one x
  have hXu : X * u = tMat * X := by
    rw [huX]
    calc X * (Y * tMat * X) = (X * Y) * tMat * X := by noncomm_ring
      _ = tMat * X := by rw [hXY, one_mul]
  let y : GL (Fin (5 + 1)) (ZMod 3) := x * n
  have hyMat : glMat y = X * N := by
    dsimp only [y, glMat]
    rw [Units.val_mul]
  have hy_comm : glMat y * tMat = tMat * glMat y := by
    rw [hyMat]
    calc (X * N) * tMat = X * (N * tMat) := by rw [mul_assoc]
      _ = X * (u * N) := by rw [hNt]
      _ = (X * u) * N := by rw [mul_assoc]
      _ = (tMat * X) * N := by rw [hXu]
      _ = tMat * (X * N) := by rw [mul_assoc]
  have hy_comm' : (X * N) * tMat = tMat * (X * N) := by
    rw [← hyMat]
    exact hy_comm
  have hy0 : (glMat y *ᵥ e06 = e01 ∨ glMat y *ᵥ e06 = -e01) := by
    rw [hyMat, ← Matrix.mulVec_mulVec, hN0]
    exact hmove
  have he02 : e02 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [e02] at h0
  have h02shape : (wt e02 ≤ 2 ∧ e02 0 ≠ 0) ∨ (wt e02 = 6 ∧ ∏ i, e02 i = 1) := by
    decide +kernel
  have hline02 : IsConjLine b₀ (B.line e02) :=
    (hrec.2.2.2 e02 he02).mpr h02shape
  obtain ⟨gx, hgxN, hgxActs⟩ := B.exists_conj_of_mem_xg hxX
  have hgxActs' : B.Acts gx X := by
    intro j
    have h1 := hgxActs (Pi.single j 1)
    rw [Basis3.vec_single, Matrix.mulVec_single_one] at h1
    dsimp [X]
    exact h1
  have hnEven : N ∈ evenAll0 5 := by
    rw [hNmat]
    refine ⟨σ, fun _ => (1 : ZMod 3), isSign_one, ⟨hσ0, ?_⟩, rfl⟩
    simp
  have hnReal : N ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    rw [hrec.2.1]
    exact hnEven
  obtain ⟨gn, hgnN, hgnActs⟩ := hnReal
  have hActsY : B.Acts (gx * gn) (X * N) := B.acts_mul hgxActs' hgnActs
  have hlineY : IsConjLine b₀ (B.line ((X * N) *ᵥ e02)) := by
    obtain ⟨g, hg⟩ := hline02
    refine ⟨(gx * gn) * g, ?_⟩
    rw [Basis3.line]
    have hmap := congrArg (fun K : Subgroup G =>
      K.map (MulAut.conj (gx * gn)).toMonoidHom) hg
    rw [Basis3.line, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    change Subgroup.zpowers ((MulAut.conj (gx * gn)) (g * b₀ * g⁻¹)) =
      Subgroup.zpowers ((MulAut.conj (gx * gn)) (B.vec e02)) at hmap
    rw [MulAut.conj_apply, MulAut.conj_apply] at hmap
    rw [show (gx * gn) * B.vec e02 * (gx * gn)⁻¹ = B.vec ((X * N) *ᵥ e02) by
      simpa [MulAut.conj_apply] using B.acts_vec hActsY e02] at hmap
    convert hmap using 1; group
  have hy2ne : ((X * N) *ᵥ Pi.single 2 1) ≠ 0 := by
    have h := gl_mulVec_ne_zero y (by decide : (Pi.single 2 1 : Coords (5 + 1)) ≠ 0)
    have h' : (X * N) *ᵥ Pi.single 2 1 ≠ 0 := by
      rw [← hyMat]
      exact h
    exact h'
  have hy2_0 : ((X * N) *ᵥ Pi.single 2 1) 0 = 0 := by
    have hv : tMat *ᵥ (Pi.single 2 1 : Coords (5 + 1)) = Pi.single 2 1 := by
      decide +kernel
    have hfix : tMat *ᵥ ((X * N) *ᵥ Pi.single 2 1) = (X * N) *ᵥ Pi.single 2 1 := by
      calc tMat *ᵥ ((X * N) *ᵥ Pi.single 2 1)
          = (tMat * (X * N)) *ᵥ Pi.single 2 1 := by rw [Matrix.mulVec_mulVec]
        _ = ((X * N) * tMat) *ᵥ Pi.single 2 1 := by rw [hy_comm']
        _ = (X * N) *ᵥ (tMat *ᵥ Pi.single 2 1) := by rw [← Matrix.mulVec_mulVec]
        _ = (X * N) *ᵥ Pi.single 2 1 := by rw [hv]
    have h := congrFun hfix 0
    simp [tMat, Matrix.mulVec_diagonal] at h
    exact eq_zero_of_neg_eq_self (by simpa [Matrix.mulVec_single_one] using h)
  have hy2_1 : ((X * N) *ᵥ Pi.single 2 1) 1 = 0 := by
    have hv : tMat *ᵥ (Pi.single 2 1 : Coords (5 + 1)) = Pi.single 2 1 := by
      decide +kernel
    have hfix : tMat *ᵥ ((X * N) *ᵥ Pi.single 2 1) = (X * N) *ᵥ Pi.single 2 1 := by
      calc tMat *ᵥ ((X * N) *ᵥ Pi.single 2 1)
          = (tMat * (X * N)) *ᵥ Pi.single 2 1 := by rw [Matrix.mulVec_mulVec]
        _ = ((X * N) * tMat) *ᵥ Pi.single 2 1 := by rw [hy_comm']
        _ = (X * N) *ᵥ (tMat *ᵥ Pi.single 2 1) := by rw [← Matrix.mulVec_mulVec]
        _ = (X * N) *ᵥ Pi.single 2 1 := by rw [hv]
    have h := congrFun hfix 1
    simp [tMat, Matrix.mulVec_diagonal] at h
    exact eq_zero_of_neg_eq_self (by simpa [Matrix.mulVec_single_one] using h)
  let w : Coords (5 + 1) := (X * N) *ᵥ Pi.single 2 1
  have hw0 : w 0 = 0 := hy2_0
  have hw1 : w 1 = 0 := hy2_1
  have hwne : w ≠ 0 := hy2ne
  have hwt : wt ((X * N) *ᵥ e02) = 2 + wt w := by
    rcases hy0 with h | h
    · have h0 : (X * N) *ᵥ Pi.single 0 1 = e01 := by
        simpa [e06, hyMat] using h
      have hvec : (X * N) *ᵥ e02 = e01 + w := by
        dsimp [e02]
        rw [Matrix.mulVec_add, h0]
      rw [hvec]
      exact wt_e01_add w hw0 hw1
    · have h0 : (X * N) *ᵥ Pi.single 0 1 = -e01 := by
        simpa [e06, hyMat] using h
      have hvec : (X * N) *ᵥ e02 = -e01 + w := by
        dsimp [e02]
        rw [Matrix.mulVec_add, h0]
      rw [hvec]
      exact wt_neg_e01_add w hw0 hw1
  have hpos : 0 < wt w := by
    unfold wt
    exact Finset.card_pos.mpr (by
      by_contra hcon
      apply hwne
      ext i
      by_contra hi
      exact hcon ⟨i, by simpa using hi⟩)
  have hshapeY := (hrec.2.2.2 ((X * N) *ᵥ e02) (by
    have hwtne : wt ((X * N) *ᵥ e02) ≠ 0 := by
      rw [hwt]
      omega
    intro hzero
    exact hwtne (RootLineAux.wt_eq_zero_iff.mpr hzero))).mp hlineY
  have hwt6 : wt ((X * N) *ᵥ e02) = 6 := by
    rcases hshapeY with h | h
    · rw [hwt] at h
      omega
    · exact h.1
  have hwt4 : wt w = 4 := by omega
  have hfull : ∀ k : Fin 4, w k.succ.succ ≠ 0 :=
    full_support_of_wt_four w hw0 hw1 hwt4
  have hgyN : gx * gn ∈ Subgroup.normalizer (B.span : Set G) :=
    (Subgroup.normalizer (B.span : Set G)).mul_mem hgxN
      (B.mem_normalizer_of_acts hgnActs)
  have hgyActs : B.Acts (gx * gn) (glMat y) := by
    simpa [hyMat] using hActsY
  refine ⟨y, hy_comm, hy0, ?_, gx * gn, hgyN, hgyActs⟩
  intro k
  simpa [w, hyMat] using hfull k

theorem spMat_commute_tMat {ρ : Equiv.Perm (Fin (5 + 1))} {r : Fin (5 + 1) → ZMod 3}
    (hρ0 : ρ 0 = 0) (hρ1 : ρ 1 = 1) (_hr : IsSign r) :
    spMat ρ r * tMat = tMat * spMat ρ r := by
  have hne0 : ∀ j, j ≠ 0 → ρ j ≠ 0 := by
    intro j hj h
    exact hj (ρ.injective (by rw [h, hρ0]))
  have hne1 : ∀ j, j ≠ 1 → ρ j ≠ 1 := by
    intro j hj h
    exact hj (ρ.injective (by rw [h, hρ1]))
  have ht : ∀ j, tSign (ρ j) = tSign j := by
    intro j
    fin_cases j
    · simp [tSign, hρ0]
    · simp [tSign, hρ1]
    · have h0 := hne0 2 (by decide)
      have h1 := hne1 2 (by decide)
      simp [tSign, h0, h1]
    · have h0 := hne0 3 (by decide)
      have h1 := hne1 3 (by decide)
      simp [tSign, h0, h1]
    · have h0 := hne0 4 (by decide)
      have h1 := hne1 4 (by decide)
      simp [tSign, h0, h1]
    · have h0 := hne0 5 (by decide)
      have h1 := hne1 5 (by decide)
      simp [tSign, h0, h1]
  rw [tMat_eq_spMat, spMat_mul, spMat_mul]
  congr 1
  funext j
  rw [ht j]
  simp only [Equiv.Perm.one_apply]
  exact mul_comm (r j) (tSign j)

theorem isSign_mul_prod_inv {s : Fin (5 + 1) → ZMod 3} (hs : IsSign s) :
    s 0 * (∏ i, s i)⁻¹ = 1 ∨ s 0 * (∏ i, s i)⁻¹ = -1 := by
  have hsne : ∀ i, s i ≠ 0 := by
    intro i
    rcases hs i with h | h <;> rw [h] <;> decide
  have h0 := eq_one_or_of_ne_zero (hsne 0)
  have hPne : (∏ i, s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hsne i)
  have hP := eq_one_or_of_ne_zero hPne
  rcases h0 with h0 | h0 <;> rcases hP with hP | hP <;> simp [h0, hP]

theorem prod_update_zero_eq_one (s : Fin (5 + 1) → ZMod 3) (hs : IsSign s) :
    (∏ i, (if i = 0 then s 0 * (∏ j, s j)⁻¹ else s i)) = 1 := by
  rw [Fin.prod_univ_six, Fin.prod_univ_six]
  simp only [Fin.isValue, if_true,
    if_neg (by decide : (1 : Fin (5 + 1)) ≠ 0),
    if_neg (by decide : (2 : Fin (5 + 1)) ≠ 0),
    if_neg (by decide : (3 : Fin (5 + 1)) ≠ 0),
    if_neg (by decide : (4 : Fin (5 + 1)) ≠ 0),
    if_neg (by decide : (5 : Fin (5 + 1)) ≠ 0)]
  have hsne : ∀ i, s i ≠ 0 := by
    intro i
    rcases hs i with h | h <;> rw [h] <;> decide
  have hPne : (s 0 * s 1 * s 2 * s 3 * s 4 * s 5) ≠ 0 := by
    have h := (Finset.prod_ne_zero_iff (s := (Finset.univ : Finset (Fin (5 + 1))))).mpr
      (fun i _ => hsne i)
    simpa [Fin.prod_univ_six] using h
  field_simp [hsne 0, hsne 1, hsne 2, hsne 3, hsne 4, hsne 5]

theorem isSign_update_zero (s : Fin (5 + 1) → ZMod 3) (hs : IsSign s) :
    IsSign (fun i => if i = 0 then s 0 * (∏ j, s j)⁻¹ else s i) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    simp only [if_true]
    exact isSign_mul_prod_inv hs
  · simp only [if_neg hi]
    exact hs i

theorem spMat_update_zero_mulVec (σ : Equiv.Perm (Fin (5 + 1)))
    (_hσ0 : σ 0 = 0) (s : Fin (5 + 1) → ZMod 3) (u : Coords (5 + 1)) (hu0 : u 0 = 0) :
    spMat σ (fun i => if i = 0 then s 0 * (∏ j, s j)⁻¹ else s i) *ᵥ u =
      spMat σ s *ᵥ u := by
  funext i
  simp only [spMat_mulVec]
  by_cases h : σ.symm i = 0
  · rw [h, hu0, mul_zero, mul_zero]
  · rw [if_neg h]

theorem exists_evenAll0_map_of_zero_one {u v : Coords (5 + 1)} (hwt : wt u = wt v)
    (hu0 : u 0 = 0) (hu1 : u 1 = 0) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    ∃ A ∈ evenAll0 5, A *ᵥ u = v ∧ A * tMat = tMat * A := by
  obtain ⟨σ, s, hs, hσ0, hsu⟩ := exists_spMat_mulVec_eq_fix hwt hu0 hv0
  let r : Fin (5 + 1) := σ 1
  have h10 : (1 : Fin (5 + 1)) ≠ 0 := by decide
  have hr0 : r ≠ 0 := by
    intro h
    have h' : σ 1 = σ 0 := by
      dsimp only [r] at h
      rw [h, hσ0]
    exact h10 (σ.injective h')
  let τ : Equiv.Perm (Fin (5 + 1)) := Equiv.swap 1 r
  let s' : Fin (5 + 1) → ZMod 3 := fun i => if i = 0 then s 0 * (∏ j, s j)⁻¹ else s i
  have hτ0 : τ 0 = 0 := by
    dsimp [τ]
    exact Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin (5 + 1)) ≠ 1) (Ne.symm hr0)
  have hτr : τ r = 1 := by
    dsimp [τ]
    rw [Equiv.swap_apply_right]
  have hvr : v r = 0 := by
    have h := congrFun hsu r
    rw [spMat_mulVec] at h
    simp [r, Equiv.symm_apply_apply, hu1] at h
    exact h.symm
  have hτv : spMat τ (fun _ => (1 : ZMod 3)) *ᵥ v = v := by
    funext i
    rw [spMat_mulVec]
    dsimp [τ]
    simp only [one_mul]
    by_cases hi1 : i = 1
    · subst hi1
      rw [Equiv.swap_apply_left, hvr, hv1]
    · by_cases hir : i = r
      · subst hir
        rw [Equiv.swap_apply_right, hv1, hvr]
      · rw [Equiv.swap_apply_of_ne_of_ne hi1 hir]
  have hσ'0 : (τ * σ) 0 = 0 := by
    change τ (σ 0) = 0
    rw [hσ0, hτ0]
  have hσ'1 : (τ * σ) 1 = 1 := by
    change τ (σ 1) = 1
    rw [hτr]
  have hs' : IsSign s' := isSign_update_zero s hs
  have hprod : (∏ i, s' i) = 1 := prod_update_zero_eq_one s hs
  have h_eq : spMat σ s' *ᵥ u = v := by
    rw [spMat_update_zero_mulVec σ hσ0 s u hu0]
    exact hsu
  have hAprod : spMat (τ * σ) s' = spMat τ (fun _ => (1 : ZMod 3)) * spMat σ s' := by
    rw [spMat_mul]
    congr 1
    funext j
    simp
  refine ⟨spMat (τ * σ) s', ⟨τ * σ, s', hs', ⟨hσ'0, hprod⟩, rfl⟩, ?_, ?_⟩
  · rw [hAprod, ← Matrix.mulVec_mulVec, h_eq, hτv]
  · exact spMat_commute_tMat hσ'0 hσ'1 hs'

theorem ext2_mul_self {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (h : M * M = 1) :
    ext2 M * ext2 M = 1 := by
  rw [ext2_mul, h]
  simp [Matrix.fromBlocks_one]

theorem exists_diagonal_of_conj_tMat {u Y X : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hu : u ∈ evenAll0 5) (hu0 : u *ᵥ Pi.single 0 1 = -Pi.single 0 1)
    (hXY : X * Y = 1) (hYX : Y * X = 1) (hu_eq : u = Y * tMat * X) :
    ∃ j : Fin 6, j ≠ 0 ∧
      u = Matrix.diagonal fun i => if i = 0 ∨ i = j then -1 else 1 := by
  have hu2 : u * u = 1 := by
    rw [hu_eq]
    calc Y * tMat * X * (Y * tMat * X) = Y * tMat * (X * Y) * tMat * X := by
          noncomm_ring
      _ = Y * tMat * 1 * tMat * X := by rw [hXY]
      _ = Y * (tMat * tMat) * X := by noncomm_ring
      _ = Y * 1 * X := by rw [tMat_mul_self]
      _ = 1 := by rw [mul_one, hYX]
  have hMfix : -u ∈ evenFix0 5 := neg_mem_evenFix0_of_mem_evenAll0 hu hu0
  have hM2 : (-u) * (-u) = 1 := by
    rw [neg_mul_neg, hu2]
  have hSfix : ext2 (-u) ∈ evenFix0 7 := ext2_mem_evenFix0 hMfix
  have hS2 : ext2 (-u) * ext2 (-u) = 1 := ext2_mul_self hM2
  have hS_eq : ext2 (-u) = ext2 Y * ext2 (-tMat) * ext2 X := by
    rw [hu_eq]
    rw [show -(Y * tMat * X) = Y * (-tMat) * X by noncomm_ring]
    exact (ext2_mul_three Y (-tMat) X).symm
  have hSfixCount : fixCount (ext2 (-u)) = 9 := by
    rw [hS_eq]
    rw [fixCount_conj (g := ext2 Y) (g' := ext2 X)]
    · exact fixCount_ext2_neg_tMat
    · exact ext2_mul_inv hYX
    · exact ext2_mul_inv hXY
  obtain ⟨T, h0T, hcardT, hTeq⟩ := mem_E6set_of_fixCount hSfix hS2 hSfixCount
  have h6T : e62 (Sum.inr 0) ∈ T := by
    have h := congrFun (congrFun hTeq (e62 (Sum.inr 0))) (e62 (Sum.inr 0))
    rw [ext2_apply_inr_self] at h
    by_contra hnot
    have hdiag : sgn T (e62 (Sum.inr 0)) (e62 (Sum.inr 0)) = 1 := by
      simp [sgn, Matrix.diagonal_apply_eq, hnot]
    rw [hdiag] at h
    exact (by decide : (-1 : ZMod 3) ≠ 1) h
  have h7T : e62 (Sum.inr 1) ∈ T := by
    have h := congrFun (congrFun hTeq (e62 (Sum.inr 1))) (e62 (Sum.inr 1))
    rw [ext2_apply_inr_self] at h
    by_contra hnot
    have hdiag : sgn T (e62 (Sum.inr 1)) (e62 (Sum.inr 1)) = 1 := by
      simp [sgn, Matrix.diagonal_apply_eq, hnot]
    rw [hdiag] at h
    exact (by decide : (-1 : ZMod 3) ≠ 1) h
  obtain ⟨j, hj0, hcompl⟩ := exists_missing_first6 T h0T hcardT h6T h7T
  refine ⟨j, hj0, ?_⟩
  have hT : T = ({0, e62 (Sum.inl j)} : Finset (Fin 8))ᶜ := by
    rw [← hcompl]
    simp
  have hD : ext2 (Matrix.diagonal fun i => if i = 0 ∨ i = j then (1 : ZMod 3) else -1) =
      sgn T := by
    rw [hT, ext2_diagonal_pos_eq_sgn_compl j hj0]
  have hSu : ext2 (-u) = ext2 (Matrix.diagonal fun i =>
      if i = 0 ∨ i = j then (1 : ZMod 3) else -1) := by
    rw [hTeq, hD]
  have hnu : -u = Matrix.diagonal fun i => if i = 0 ∨ i = j then (1 : ZMod 3) else -1 :=
    ext2_injective hSu
  have hu_eq' : u = -Matrix.diagonal fun i => if i = 0 ∨ i = j then (1 : ZMod 3) else -1 := by
    have := congrArg Neg.neg hnu
    simpa using this
  rw [hu_eq']
  ext i k
  by_cases hik : i = k
  · subst hik
    simp only [Matrix.neg_apply, Matrix.diagonal_apply_eq]
    split_ifs <;> decide
  · simp [Matrix.diagonal_apply_ne _ hik]

theorem exists_diagonal_fusing {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)}
    {b₀ : G} {K E : Subgroup G} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    {t : G} (hActsT : B.Acts t tMat)
    (x : GL (Fin (5 + 1)) (ZMod 3))
    (hxX : x ∈ (ggAutomizer ⊤ B.span).map B.glHom)
    (hmove : ((((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = e01) ∨
      (((x : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ e06 = -e01))) :
    ∃ (j : Fin 6) (u : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)),
      j ≠ 0 ∧ u = ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) * tMat *
          ((x : GL (Fin (5 + 1)) (ZMod 3)) :
            Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) ∧
      u ∈ evenAll0 5 ∧ u *ᵥ e06 = -e06 ∧
      u = Matrix.diagonal (fun i => if i = 0 ∨ i = j then -1 else 1) := by
  classical
  let X : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((x : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  let Y : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) :=
    ((x⁻¹ : GL (Fin (5 + 1)) (ZMod 3)) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3))
  let u : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) := Y * tMat * X
  have hu0 : u *ᵥ e06 = -e06 := by
    simpa [u, X, Y] using conj_tMat_mulVec_e06 x hmove
  obtain ⟨g, hgN, hgActs⟩ := B.exists_conj_of_mem_xg hxX
  have hxinvX : x⁻¹ ∈ (ggAutomizer ⊤ B.span).map B.glHom :=
    (Subgroup.map B.glHom (ggAutomizer ⊤ B.span)).inv_mem hxX
  obtain ⟨h, hhN, hhActs⟩ := B.exists_conj_of_mem_xg hxinvX
  have hActsU : B.Acts (h * t * g) u := by
    have hhActs' : B.Acts h Y := by
      intro j
      have h1 := hhActs (Pi.single j 1)
      rw [Basis3.vec_single, Matrix.mulVec_single_one] at h1
      dsimp [Y]
      exact h1
    have hgActs' : B.Acts g X := by
      intro j
      have h1 := hgActs (Pi.single j 1)
      rw [Basis3.vec_single, Matrix.mulVec_single_one] at h1
      dsimp [X]
      exact h1
    have h1 : B.Acts (h * t) (Y * tMat) := B.acts_mul hhActs' hActsT
    have h2 : B.Acts ((h * t) * g) ((Y * tMat) * X) := B.acts_mul h1 hgActs'
    simpa [u, X, Y, mul_assoc] using h2
  have htN : t ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hActsT
  have hUN : h * t * g ∈ Subgroup.normalizer (B.span : Set G) :=
    (Subgroup.normalizer (B.span : Set G)).mul_mem
      ((Subgroup.normalizer (B.span : Set G)).mul_mem hhN htN) hgN
  have hUb0 : (h * t * g) * b₀ * (h * t * g)⁻¹ = b₀⁻¹ := by
    calc (h * t * g) * b₀ * (h * t * g)⁻¹ =
        (h * t * g) * B.vec e06 * (h * t * g)⁻¹ := by
          rw [e06, B.vec_single, hB.2.1]
      _ = B.vec (u *ᵥ e06) := B.acts_vec hActsU e06
      _ = B.vec (-e06) := by rw [hu0]
      _ = (B.vec e06)⁻¹ := B.vec_neg _
      _ = b₀⁻¹ := by rw [e06, B.vec_single, hB.2.1]
  have hUzp : h * t * g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    refine Basis3.mem_normalizer_zpowers_of_conj ?_
    rw [hUb0]
    exact (Subgroup.zpowers b₀).inv_mem (Subgroup.mem_zpowers b₀)
  have huEven : u ∈ evenAll0 5 := by
    have huReal : u ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
      ⟨h * t * g, hUzp, hActsU⟩
    rw [hrec.2.1] at huReal
    exact huReal
  have hXY : X * Y = 1 := gl_mul_inv_eq_one x
  have hYX : Y * X = 1 := gl_inv_mul_eq_one x
  obtain ⟨j, hj0, hdiag⟩ := exists_diagonal_of_conj_tMat huEven hu0 hXY hYX (by rfl)
  exact ⟨j, u, hj0, rfl, huEven, hu0, hdiag⟩

theorem exists_centralizer_acts_evenAll0 {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} {b₀ : G} (hrec : RecOutTwD5 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {t : G} (ht : orderOf t = 2) (hActsT : B.Acts t tMat)
    {A : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)}
    (hA : A ∈ evenAll0 5) (hcomm : A * tMat = tMat * A) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), B.Acts c A := by
  have hreal : A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    rw [hrec.2.1]
    exact hA
  obtain ⟨g, -, hgActs⟩ := hreal
  exact exists_centralizer_acts_of_commute hodd ht hActsT
    (B.mem_normalizer_of_acts hgActs) hgActs hcomm

theorem exists_centralizer_conj_b2_full {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {t : G} (ht : orderOf t = 2) (hActsT : B.Acts t tMat) :
    ∃ (w : Coords (5 + 1)) (c : G),
      c ∈ Subgroup.centralizer ({t} : Set G) ∧
      (∀ k : Fin 4, w k.succ.succ ≠ 0) ∧
      w 0 = 0 ∧ w 1 = 0 ∧
      c * B.b 2 * c⁻¹ = B.vec w := by
  classical
  obtain ⟨x, hxX, hmove⟩ := exists_gl_moves_e0 (K := K) (E := E) hB hrec hfus
  obtain ⟨j, u, hj0, hu_eq, huEven, hu0, hdiag⟩ :=
    exists_diagonal_fusing (K := K) (E := E) hB hrec hActsT x hxX hmove
  obtain ⟨y, hy_comm, hy0, hfull, gy, hgyN, hgyActs⟩ :=
    exists_y_full_support (K := K) (E := E) hB hrec hActsT x hxX hmove j hj0 u hu_eq hdiag
  obtain ⟨c, hcC, hcActs⟩ :=
    exists_centralizer_acts_of_commute hodd ht hActsT hgyN hgyActs hy_comm
  have hv : tMat *ᵥ (Pi.single 2 1 : Coords (5 + 1)) = Pi.single 2 1 := by
    decide +kernel
  have hfix : tMat *ᵥ (glMat y *ᵥ Pi.single 2 1) = glMat y *ᵥ Pi.single 2 1 := by
    calc tMat *ᵥ (glMat y *ᵥ Pi.single 2 1)
        = (tMat * glMat y) *ᵥ Pi.single 2 1 := by rw [← Matrix.mulVec_mulVec]
      _ = (glMat y * tMat) *ᵥ Pi.single 2 1 := by rw [hy_comm]
      _ = glMat y *ᵥ (tMat *ᵥ Pi.single 2 1) := by rw [Matrix.mulVec_mulVec]
      _ = glMat y *ᵥ Pi.single 2 1 := by rw [hv]
  have hw0 : (glMat y *ᵥ Pi.single 2 1) 0 = 0 := by
    have h := congrFun hfix 0
    rw [Matrix.mulVec_single_one] at h ⊢
    simp [tMat, Matrix.mulVec_diagonal] at h
    exact eq_zero_of_neg_eq_self h
  have hw1 : (glMat y *ᵥ Pi.single 2 1) 1 = 0 := by
    have h := congrFun hfix 1
    rw [Matrix.mulVec_single_one] at h ⊢
    simp [tMat, Matrix.mulVec_diagonal] at h
    exact eq_zero_of_neg_eq_self h
  refine ⟨glMat y *ᵥ Pi.single 2 1, c, hcC, ?_, hw0, hw1, ?_⟩
  · intro k
    exact hfull k
  · rw [Matrix.mulVec_single_one]
    exact hcActs 2

theorem exists_centralizer_conj_b2_coord {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} {b₀ : G} (hrec : RecOutTwD5 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {t : G} (ht : orderOf t = 2) (hActsT : B.Acts t tMat) (i : Fin 4) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G),
      c * B.b 2 * c⁻¹ = B.vec (Pi.single i.succ.succ 1) := by
  classical
  let k : Fin (5 + 1) := i.succ.succ
  let ρ : Equiv.Perm (Fin (5 + 1)) := Equiv.swap 2 k
  have hρ0 : ρ 0 = 0 := by
    dsimp [ρ, k]
    rw [Equiv.swap_apply_def]
    fin_cases i <;> simp
  have hρ1 : ρ 1 = 1 := by
    dsimp [ρ, k]
    rw [Equiv.swap_apply_def]
    fin_cases i <;> simp
  let A : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3) := spMat ρ (fun _ => 1)
  have hAmem : A ∈ evenAll0 5 :=
    ⟨ρ, fun _ => (1 : ZMod 3), isSign_one, ⟨hρ0, by simp⟩, rfl⟩
  have hAcomm : A * tMat = tMat * A := spMat_commute_tMat hρ0 hρ1 isSign_one
  obtain ⟨c, hcC, hcActs⟩ :=
    exists_centralizer_acts_evenAll0 hrec hodd ht hActsT hAmem hAcomm
  refine ⟨c, hcC, ?_⟩
  have h2 := hcActs 2
  rw [h2]
  congr 1
  have hcol : (fun j => A j 2) = A *ᵥ Pi.single 2 1 := by
    ext j
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  have hAe : A *ᵥ Pi.single 2 1 = Pi.single k 1 := by
    dsimp [A, ρ]
    rw [spMat_mulVec]
    ext j
    fin_cases i <;> fin_cases j <;> decide +kernel
  rw [hAe]

end CFSG.StandardType.FrameRoute.FS81.NineHyp

end

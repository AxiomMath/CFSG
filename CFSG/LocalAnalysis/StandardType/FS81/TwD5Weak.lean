module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Transfer
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvUnique
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvMain
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}

def wE6FixBound (ε : ZMod 3) : Prop :=
  ∀ A : Subgroup (GL (Fin 6) (ZMod 3)), A ≤ wE6 ε → IsElemAbelian 3 A → A ≠ ⊥ →
    Nat.card {v : Fin 6 → ZMod 3 // v 0 = 0 ∧
      ∀ a ∈ A, (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card A < 3 ^ 5

theorem card_E_eq_three_mul_card_inf_of_std (hstd : StdTwD5 b₀ K E) :
    Nat.card E = 3 * Nat.card ↥(E ⊓ K) := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, -, -, -, -, -, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨hdisj, hsup, -, hEKcard, -⟩ := hcanon
  have hb0E : b₀ ∈ E := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hA : E ⊓ K ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b₀ : Set G))
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute b₀ a from hEmax.2.1.comm hb0E ha.1).zpow_left n).eq
  have hcard : Nat.card ↥(Subgroup.zpowers b₀) = 3 := by
    rw [Nat.card_zpowers, hord]
  conv_lhs => rw [← hsup]
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hA hdisj,
    hcard, hEKcard]

theorem conj_b0_mem_inf_of_wE6 {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K := by
  obtain ⟨-, hhyp, -⟩ := hstd
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, -, -, -⟩ := hhyp
  have hb0E : b₀ ∈ E := by
    rw [← hB.2.1, ← hB.1]
    exact B.b_mem_span 0
  set w : G := (g * b₀ * g⁻¹) * b₀⁻¹ with hw
  have hwA : w ∈ E ⊓ K := conj_mul_inv_mem_inf_of_mem_normalizer hB hX hg hb0E
  have hcomm : Commute b₀ w :=
    (show Commute w b₀ from hEmax.2.1.comm hwA.1 hb0E).symm
  have h1 : b₀⁻¹ * (g * b₀ * g⁻¹) = w := by
    calc b₀⁻¹ * (g * b₀ * g⁻¹) = b₀⁻¹ * (w * b₀) := by
          rw [hw]; group
      _ = (b₀⁻¹ * w) * b₀ := by group
      _ = (w * b₀⁻¹) * b₀ := by rw [hcomm.inv_left.eq]
      _ = w := by group
  rw [h1]
  exact hwA

theorem mulVec_eq_add_of_fixes_hyperplane {M : GL (Fin 6) (ZMod 3)}
    (hfix : ∀ v : Coords 6, v 0 = 0 → (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v)
    (v : Coords 6) :
    (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v =
      v + v 0 • ((M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1 - Pi.single 0 1) := by
  have hv : v = v 0 • Pi.single 0 1 + (v - v 0 • Pi.single 0 1) := by abel
  have h1 : (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (v 0 • Pi.single 0 1) =
      v 0 • ((M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1) :=
    Matrix.mulVec_smul _ _ _
  have h2 : (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (v - v 0 • Pi.single 0 1) =
      v - v 0 • Pi.single 0 1 := hfix _ (by simp)
  conv_lhs => rw [hv]
  rw [Matrix.mulVec_add, h1, h2]
  rw [show (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1 =
      ((M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1 - Pi.single 0 1) +
        Pi.single 0 1 from by abel]
  rw [smul_add]
  abel

theorem pow_three_eq_one_of_fixes_hyperplane {M : GL (Fin 6) (ZMod 3)}
    (hfix : ∀ v : Coords 6, v 0 = 0 → (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v)
    (hrow : ∀ v : Coords 6, ((M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0 = v 0) :
    M ^ 3 = 1 := by
  let a : Coords 6 := (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1 - Pi.single 0 1
  have hM00 : (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 = 1 := by
    have h1 := hrow (Pi.single 0 1)
    rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] at h1
  have ha0 : a 0 = 0 := by simp [a, Pi.sub_apply, hM00]
  have hpow : ∀ k : ℕ, ∀ v : Coords 6,
      (((M ^ k : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) =
        v + (k : ZMod 3) • (v 0 • a) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, ih,
        mulVec_eq_add_of_fixes_hyperplane hfix]
      have h1 : ((v + v 0 •
          ((M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Pi.single 0 1 - Pi.single 0 1)) : Coords 6) 0 =
          v 0 := by
        simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hM00]
      rw [h1]
      change v + v 0 • a + (k : ZMod 3) • (v 0 • a) =
        v + ((k + 1 : ℕ) : ZMod 3) • (v 0 • a)
      rw [Nat.cast_succ, add_smul, one_smul]
      abel
  refine Units.ext ?_
  rw [Units.val_one]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have h := hpow 3 (Pi.single j 1)
  rw [Matrix.one_mulVec]
  simpa [show (3 : ZMod 3) = 0 from rfl] using h

noncomputable def coordsZeroEquiv (n : ℕ) :
    {v : Fin (n + 1) → ZMod 3 // v 0 = 0} ≃ (Fin n → ZMod 3) where
  toFun v i := v.1 i.succ
  invFun w := ⟨fun j => if h : j = 0 then 0 else w (j.pred h), by simp⟩
  left_inv v := by
    ext j
    by_cases hj : j = 0
    · subst hj; simp [v.2]
    · simp [hj]
  right_inv w := by
    ext i
    simp

theorem card_coords_zero (n : ℕ) :
    Nat.card {v : Fin (n + 1) → ZMod 3 // v 0 = 0} = 3 ^ n := by
  rw [Nat.card_congr (coordsZeroEquiv n), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def normalizerToBspan {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) :
    ↥(Subgroup.normalizer (E : Set G)) →* ↥(Subgroup.normalizer (B.span : Set G)) where
  toFun x := ⟨x.1, hB.1 ▸ x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

omit [Finite G] in
theorem normalizerToBspan_surjective {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) : Function.Surjective (normalizerToBspan hB) :=
  fun y => ⟨⟨y.1, hB.1 ▸ y.2⟩, Subtype.ext rfl⟩

@[expose] noncomputable def conjMatHom {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) :
    ↥(Subgroup.normalizer (E : Set G)) →* GL (Fin 6) (ZMod 3) :=
  B.glHom.comp (B.span.normalizerMonoidHom.comp (normalizerToBspan hB))

omit [Finite G] in
theorem conjMatHom_apply {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (x : ↥(Subgroup.normalizer (E : Set G))) :
    ((conjMatHom hB x : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      B.matOf (B.span.normalizerMonoidHom (normalizerToBspan hB x)) := by
  rw [conjMatHom, MonoidHom.comp_apply, MonoidHom.comp_apply, B.coe_glHom]

omit [Finite G] in
theorem conjMatHom_range {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) :
    (conjMatHom hB).range = wE6 ε := by
  rw [conjMatHom, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (normalizerToBspan_surjective hB), Subgroup.map_top,
    normalizerMonoidHom_range_eq_ggAutomizer, hX]

@[expose] noncomputable def wE6ConjHom {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) :
    ↥(Subgroup.normalizer (E : Set G)) →* ↥(wE6 ε) :=
  (conjMatHom hB).codRestrict (wE6 ε) fun x => by
    have h : conjMatHom hB x ∈ (conjMatHom hB).range := ⟨x, rfl⟩
    rwa [conjMatHom_range hB hX] at h

omit [Finite G] in
theorem wE6ConjHom_apply {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (x : ↥(Subgroup.normalizer (E : Set G))) :
    ((wE6ConjHom hB hX x : ↥(wE6 ε)) : GL (Fin 6) (ZMod 3)) = conjMatHom hB x := rfl

omit [Finite G] in
theorem wE6ConjHom_acts {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (x : ↥(Subgroup.normalizer (E : Set G))) :
    B.Acts (x : G) ((wE6ConjHom hB hX x : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  rw [wE6ConjHom_apply, conjMatHom_apply]
  exact B.acts_matOf (fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe B.span (normalizerToBspan hB x) y)

omit [Finite G] in
theorem wE6ConjHom_ker {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) :
    (wE6ConjHom hB hX).ker = (Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hyS : y ∈ B.span := by rwa [hB.1]
    have hxS : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := by
      rw [hB.1]
      exact x.2
    have hacts := wE6ConjHom_acts hB hX x
    have h1 : (x : G) * y * (x : G)⁻¹ =
        B.vec (((wE6ConjHom hB hX x : GL (Fin 6) (ZMod 3)) :
          Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ B.coords ⟨y, hyS⟩) := by
      have h := B.acts_vec' hxS hacts (B.coords ⟨y, hyS⟩)
      rwa [B.vec_coords] at h
    rw [hx] at h1
    have h1' : (x : G) * y * (x : G)⁻¹ = y := by
      simpa [B.vec_coords, Matrix.one_mulVec] using h1
    have h2 : (x : G) * y = y * (x : G) := by
      calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * (x : G) := by group
        _ = y * (x : G) := by rw [h1']
    exact h2.symm
  · intro hx
    apply Subtype.ext
    apply Units.ext
    change ((wE6ConjHom hB hX x : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) = 1
    rw [wE6ConjHom_apply, conjMatHom_apply]
    refine B.matOf_eq_of_acts (g := (x : G)) (fun y => ?_) ?_
    · exact Subgroup.normalizerMonoidHom_apply_apply_coe B.span (normalizerToBspan hB x) y
    · intro j
      rw [show (fun i => (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j) = Pi.single j 1 from by
        funext i
        simp [Matrix.one_apply, Pi.single_apply]]
      rw [B.vec_single]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx (B.b j) (by
        rw [← hB.1]; exact B.b_mem_span j)).symm
      calc (x : G) * B.b j * (x : G)⁻¹ = B.b j * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = B.b j := by group

def fixingSubgroup (v : Coords 6) : Subgroup (GL (Fin 6) (ZMod 3)) where
  carrier := {a | ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v}
  mul_mem' := by
    intro a b ha hb
    change (((a * b : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ v = v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ v = v
    calc (((a⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ v
        = (((a⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ
            (((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) := by
            rw [ha]
      _ = ((((a⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *
            ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) *ᵥ v := by
            rw [Matrix.mulVec_mulVec]
      _ = v := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit [Finite G] in
theorem matrix_eq_one_of_fixes_hyperplane {M : GL (Fin 6) (ZMod 3)} {ε : ZMod 3}
    (hMmem : M ∈ wE6 ε) (hMfix : ∀ v : Coords 6, v 0 = 0 → M *ᵥ v = v)
    (hMrow : ∀ v : Coords 6,
      (((M : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0 = v 0)
    (hoff : wE6FixBound ε) : M = 1 := by
  by_contra hM1
  have hM3 : M ^ 3 = 1 := pow_three_eq_one_of_fixes_hyperplane hMfix hMrow
  let Z : Subgroup (GL (Fin 6) (ZMod 3)) := Subgroup.zpowers M
  have hZle : Z ≤ wE6 ε := by
    intro a ha
    exact Subgroup.zpowers_le.mpr hMmem ha
  have hZel : IsElemAbelian 3 Z := isElemAbelian_zpowers hM3
  have hZne : Z ≠ ⊥ := by
    intro hbot
    apply hM1
    have h : M ∈ Z := Subgroup.mem_zpowers M
    rw [hbot] at h
    exact Subgroup.mem_bot.mp h
  have hZcard : Nat.card Z = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf M ∣ 3 := orderOf_dvd_of_pow_eq_one hM3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hM1
    · exact h3
  have hfixZ : ∀ v : Coords 6, v 0 = 0 →
      ∀ a ∈ Z, ((a : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v := by
    intro v hv a ha
    have hZK : Z ≤ fixingSubgroup v := Subgroup.zpowers_le.mpr (by
      change ((M : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v
      exact hMfix v hv)
    exact hZK ha
  have hcard : Nat.card {v : Coords 6 // v 0 = 0 ∧
      ∀ a ∈ Z, ((a : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} = 3 ^ 5 := by
    have hpred : ∀ v : Coords 6,
        (v 0 = 0 ∧ ∀ a ∈ Z, ((a : GL (Fin 6) (ZMod 3)) :
          Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v) ↔ v 0 = 0 := by
      intro v
      exact ⟨fun h => h.1, fun hv => ⟨hv, hfixZ v hv⟩⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hpred), card_coords_zero 5]
  have h := hoff Z hZle hZel hZne
  rw [hcard, hZcard] at h
  norm_num at h

omit [Finite G] in
theorem conjMatHom_eq_one_of_mem_transvN1 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) (hoff : wE6FixBound ε) {x : G}
    (hx : x ∈ transvN1 b₀ K E) : conjMatHom hB ⟨x, hx.1⟩ = 1 := by
  rw [mem_transvN1] at hx
  have hMmem : conjMatHom hB ⟨x, hx.1⟩ ∈ wE6 ε := by
    have h : conjMatHom hB ⟨x, hx.1⟩ ∈ (conjMatHom hB).range := ⟨⟨x, hx.1⟩, rfl⟩
    rwa [conjMatHom_range hB hX] at h
  have hMfix : ∀ v : Coords 6, v 0 = 0 → conjMatHom hB ⟨x, hx.1⟩ *ᵥ v = v := by
    intro v hv
    have hvE : B.vec v ∈ E := by rw [← hB.1]; exact B.vec_mem_span v
    have hvK : B.vec v ∈ K := B.vec_mem_of_zero hB.2.2 hv
    have hxA : x * B.vec v * x⁻¹ = B.vec v := hx.2.1 _ ⟨hvE, hvK⟩
    have hxS : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := by
      rw [hB.1]; exact hx.1
    have hacts := wE6ConjHom_acts hB hX ⟨x, hx.1⟩
    have h1 : x * B.vec v * x⁻¹ = B.vec (conjMatHom hB ⟨x, hx.1⟩ *ᵥ v) := by
      have h := B.acts_vec' hxS hacts v
      rwa [wE6ConjHom_apply] at h
    rw [hxA] at h1
    exact B.vec_injective h1.symm
  have hMrow : ∀ v : Coords 6,
      (((conjMatHom hB ⟨x, hx.1⟩ : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0 = v 0 :=
    fun v => wE6_mulVec_zero ε hMmem v
  exact matrix_eq_one_of_fixes_hyperplane hMmem hMfix hMrow hoff

omit [Finite G] in
theorem transvN1_le_centralizer_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (hoff : wE6FixBound ε) :
    transvN1 b₀ K E ≤ Subgroup.centralizer (E : Set G) := by
  intro x hx
  have hM1 := conjMatHom_eq_one_of_mem_transvN1 hB hX hoff hx
  have hker : (⟨x, hx.1⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈
      (wE6ConjHom hB hX).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [wE6ConjHom_apply]
    exact hM1
  rw [wE6ConjHom_ker hB hX, Subgroup.mem_subgroupOf] at hker
  exact hker

omit [Finite G] in
theorem relIndex_eq_card_image_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) {F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hcent : transvN1 b₀ K E ≤ Subgroup.centralizer (E : Set G))
    (hFb : ∀ f ∈ F, b₀⁻¹ * (f * b₀ * f⁻¹) ∈ E ⊓ K) :
    (F ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)).relIndex F =
      Nat.card (((F.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (wE6ConjHom hB hX)).map (Subgroup.subtype (wE6 ε))) := by
  let N := Subgroup.normalizer (E : Set G)
  let C := Subgroup.centralizer (E : Set G)
  let fF : ↥F →* ↥(wE6 ε) := (wE6ConjHom hB hX).comp (Subgroup.inclusion hFN)
  have hfFker : fF.ker = (F ⊓ C).subgroupOf F := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, wE6ConjHom_ker hB hX]
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hindexFE : (F ⊓ C).relIndex F = Nat.card fF.range := by
    rw [← Subgroup.index_ker fF, hfFker]
    rfl
  have hsub : F ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) = F ⊓ C := by
    refine le_antisymm ?_ ?_
    · intro y hy
      refine ⟨hy.1, hcent ?_⟩
      refine ⟨hFN hy.1, ?_, hFb y hy.1⟩
      intro a ha
      have hcomm := Subgroup.mem_centralizer_iff.mp hy.2 a ha
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [hcomm.symm]
        _ = a := by group
    · intro y hy
      refine ⟨hy.1, ?_⟩
      exact Subgroup.centralizer_le (by intro z hz; exact hz.1) hy.2
  have hrange : fF.range = (F.subgroupOf N).map (wE6ConjHom hB hX) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  calc (F ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)).relIndex F
      = (F ⊓ C).relIndex F := by rw [hsub]
    _ = Nat.card fF.range := hindexFE
    _ = Nat.card ((F.subgroupOf N).map (wE6ConjHom hB hX)) := by rw [hrange]
    _ = Nat.card (((F.subgroupOf N).map (wE6ConjHom hB hX)).map
          (Subgroup.subtype (wE6 ε))) := (Subgroup.card_map_of_injective
          (Subgroup.subtype_injective (wE6 ε))).symm

omit [Finite G] in
theorem coords_fixed_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) {F : Subgroup G}
    (_hFN : F ≤ Subgroup.normalizer (E : Set G))
    (a : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)))
    {M : GL (Fin 6) (ZMod 3)}
    (hM : M ∈ ((F.subgroupOf (Subgroup.normalizer (E : Set G))).map
      (wE6ConjHom hB hX)).map (Subgroup.subtype (wE6 ε))) :
    M *ᵥ B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ =
      B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ := by
  set v : Coords 6 := B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ with hvdef
  change M *ᵥ v = v
  have hv : B.vec v = a.1 := B.vec_coords _
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hM
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
  have hcomm := Subgroup.mem_centralizer_iff.mp a.2.2 (x : G) hxF
  have hconj : (x : G) * a.1 * (x : G)⁻¹ = a.1 := by
    calc (x : G) * a.1 * (x : G)⁻¹ = a.1 * (x : G) * (x : G)⁻¹ := by
          rw [hcomm.symm]
      _ = a.1 := by group
  have hxS : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hB.1]
    exact x.2
  have hacts := wE6ConjHom_acts hB hX x
  have h1 : (x : G) * B.vec v * (x : G)⁻¹ =
      B.vec (((wE6ConjHom hB hX x : ↥(wE6 ε)) : GL (Fin 6) (ZMod 3)) *ᵥ v) := by
    have h := B.acts_vec' hxS hacts v
    rwa [wE6ConjHom_apply] at h
  have h2 : B.vec (((wE6ConjHom hB hX x : ↥(wE6 ε)) : GL (Fin 6) (ZMod 3)) *ᵥ v) =
      a.1 := by
    calc B.vec (((wE6ConjHom hB hX x : ↥(wE6 ε)) : GL (Fin 6) (ZMod 3)) *ᵥ v)
        = (x : G) * B.vec v * (x : G)⁻¹ := h1.symm
      _ = (x : G) * a.1 * (x : G)⁻¹ := by rw [hv]
      _ = a.1 := hconj
  exact B.vec_injective (by
    have h3 : B.vec (((wE6ConjHom hB hX x : ↥(wE6 ε)) : GL (Fin 6) (ZMod 3)) *ᵥ v) =
        B.vec v := by rw [h2, hv]
    simpa using h3)

omit [Finite G] in
theorem card_centralizer_le_card_fixed_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) {F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (E : Set G)) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) :
    Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) ≤
      Nat.card {v : Coords 6 // v 0 = 0 ∧
        ∀ a ∈ ((F.subgroupOf (Subgroup.normalizer (E : Set G))).map
          (wE6ConjHom hB hX)).map (Subgroup.subtype (wE6 ε)),
          ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} := by
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by rwa [hB.1]
  let vOf : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) → Coords 6 := fun a =>
    B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩
  have hvOf : ∀ a, B.vec (vOf a) = a.1 := fun a => B.vec_coords _
  let Φ : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) →
      {v : Coords 6 // v 0 = 0 ∧
        ∀ a ∈ ((F.subgroupOf (Subgroup.normalizer (E : Set G))).map
          (wE6ConjHom hB hX)).map (Subgroup.subtype (wE6 ε)),
          ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} :=
    fun a => ⟨vOf a,
      B.coords_zero_of_mem hB.2.1 hord hB.2.2 hdisj'
        ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ a.2.1.2,
      by
        intro M hM
        exact coords_fixed_of_wE6 hB hX hFN a hM⟩
  refine Nat.card_le_card_of_injective Φ ?_
  intro a b hab
  apply Subtype.ext
  have hv : vOf a = vOf b := congrArg Subtype.val hab
  have h1 : a.1 = b.1 := by
    have := congrArg B.vec hv
    rwa [hvOf a, hvOf b] at this
  exact h1

theorem sylowN1_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) (hε0 : ε ≠ 0)
    (hcent : transvN1 b₀ K E ≤ Subgroup.centralizer (E : Set G)) :
    SylowN1 b₀ K E E := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, hb0E, -, -⟩ := hhyp
  obtain ⟨hdisj, hsup, -, -, hCK⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  have hnorm := not_normalizer_le_normalizer_zpowers_of_wE6 hB hX hε0
  have hE_le : E ≤ transvN1 b₀ K E := by
    intro e he
    refine ⟨Subgroup.le_normalizer he, ?_, ?_⟩
    · intro a ha
      calc e * a * e⁻¹ = a * e * e⁻¹ := by rw [hEmax.2.1.comm he ha.1]
        _ = a := by group
    · have hcomm : e * b₀ * e⁻¹ = b₀ := by
        rw [hEmax.2.1.comm he hb0E]
        group
      rw [hcomm, inv_mul_cancel]
      exact Subgroup.one_mem _
  refine sylowN1_of_forall_pow_mem hE_le hEmax.2.1.isPGroup le_rfl ?_
  intro y hy k hyk
  exact fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hCK hEmax.2.1 hnorm (hcent hy) hyk

theorem noOffenderA_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) (hoff : wE6FixBound ε) :
    NoOffenderA b₀ K E := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, -, -, -, -, -, -, -, -, -, -, -⟩ := hhyp
  obtain ⟨hdisj, -, -, hEKcard, -⟩ := hcanon
  have hcent := transvN1_le_centralizer_of_wE6 hB hX hoff
  intro F hFN hF hFb hFA
  let N := Subgroup.normalizer (E : Set G)
  let Fbar : Subgroup (GL (Fin 6) (ZMod 3)) :=
    ((F.subgroupOf N).map (wE6ConjHom hB hX)).map (Subgroup.subtype (wE6 ε))
  have hFbar_le : Fbar ≤ wE6 ε := Subgroup.map_subtype_le _
  have hFw : IsElemAbelian 3 ((F.subgroupOf N).map (wE6ConjHom hB hX)) :=
    (hF.subgroupOf N).map (wE6ConjHom hB hX)
  have hFbar_el : IsElemAbelian 3 Fbar := hFw.map (Subgroup.subtype (wE6 ε))
  have hFbar_ne : Fbar ≠ ⊥ := by
    intro hbot
    apply hFA
    intro y hy
    have hrange : (F.subgroupOf N).map (wE6ConjHom hB hX) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective (wE6 ε))).mp hbot
    have hy1 : wE6ConjHom hB hX ⟨y, hFN hy⟩ = 1 := by
      have h : wE6ConjHom hB hX ⟨y, hFN hy⟩ ∈ (F.subgroupOf N).map (wE6ConjHom hB hX) :=
        Subgroup.mem_map.mpr ⟨⟨y, hFN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rw [hrange] at h
      exact Subgroup.mem_bot.mp h
    have hyker : ⟨y, hFN hy⟩ ∈ (wE6ConjHom hB hX).ker := hy1
    rw [wE6ConjHom_ker hB hX, Subgroup.mem_subgroupOf] at hyker
    exact Subgroup.centralizer_le (by intro z hz; exact hz.1) hyker
  have hbound := hoff Fbar hFbar_le hFbar_el hFbar_ne
  have hcard := card_centralizer_le_card_fixed_of_wE6 hB hX hFN hord hdisj
  have hidx := relIndex_eq_card_image_of_wE6 hB hX hFN hcent hFb
  calc Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) *
        (F ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)).relIndex F
      ≤ Nat.card {v : Coords 6 // v 0 = 0 ∧
          ∀ a ∈ Fbar, ((a : GL (Fin 6) (ZMod 3)) :
            Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card Fbar :=
        Nat.mul_le_mul hcard (le_of_eq hidx)
    _ < 3 ^ 5 := hbound
    _ = Nat.card ↥(E ⊓ K) := hEKcard.symm

theorem mem_commutator_normalizer_of_wE6 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (hoff : ∀ A : Subgroup (GL (Fin 6) (ZMod 3)), A ≤ wE6 ε → IsElemAbelian 3 A → A ≠ ⊥ →
      Nat.card {v : Fin 6 → ZMod 3 // v 0 = 0 ∧
        ∀ a ∈ A, (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card A < 3 ^ 5)
    (hb : b₀ ∈ E) :
    (⟨b₀, Subgroup.le_normalizer hb⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈
      commutator ↥(Subgroup.normalizer (E : Set G)) := by
  have hstd' : StdTwD5 b₀ K E := hstd
  obtain ⟨hsimple, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨hdisj, -, -, hEKcard, -⟩ := hcanon
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> decide
  have hoff' : wE6FixBound ε := hoff
  have hcent := transvN1_le_centralizer_of_wE6 hB hX hoff'
  have hfixN : ∀ g ∈ Subgroup.normalizer (E : Set G),
      b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K :=
    fun g hg => conj_b0_mem_inf_of_wE6 hstd' hB hX hg
  have hEA := card_E_eq_three_mul_card_inf_of_std hstd'
  have hsyl := sylowN1_of_wE6 hstd' hB hX hε0 hcent
  have hΩ : ∀ y ∈ E, y ^ 3 = 1 → y ∈ E := fun _ hy _ => hy
  have hoffA := noOffenderA_of_wE6 hstd' hB hX hoff'
  obtain ⟨S, hES, hSN, hwc⟩ :=
    TransvP1.exists_sylow_weaklyClosed hEmax.2.1 hsyl hfixN hΩ hoffA hEA
  have hb3 : b₀ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one b₀
  have hAbot : E ⊓ K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEKcard
    norm_num at hEKcard
  have hbG := fs81Nt_mem_commutator hsimple hord hdisj hAbot
  exact CFSG.RankThree.Transfer.WCP.mem_commutator_of_weaklyClosed S hES hSN hwc
    (fun a ha b hb => hEmax.2.1.comm ha hb) hb hb3 hbG

end CFSG.StandardType.FrameRoute.FS81

end

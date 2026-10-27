module

public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourGL32
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourFactsB
public import CFSG.LocalAnalysis.WeakClosure81.Thirteen
public import CFSG.Quasithin.Background.F918Z4bPrime
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped MatrixGroups

section Config

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] def IsNatCoord (K : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W)
    (e : ↥K ≃* GL (Fin 3) (ZMod 2)) (φ : ↥U ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) : Prop :=
  Invariant K U ∧ ∀ (k : ↥K) (u v : ↥U), (v : W) = (k : LGL 2 W) (u : W) →
    φ v = Matrix.mulVec ((e k : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ u)

@[expose] def IsDualPair (K : Subgroup (LGL 2 W)) (U₁ U₂ : Submodule (ZMod 2) W) : Prop :=
  Invariant K U₂ ∧ ∃ β : W → W → ZMod 2,
    (∀ u₁ ∈ U₁, ∀ u₂ ∈ U₁, ∀ v ∈ U₂, β (u₁ + u₂) v = β u₁ v + β u₂ v) ∧
    (∀ u ∈ U₁, ∀ v₁ ∈ U₂, ∀ v₂ ∈ U₂, β u (v₁ + v₂) = β u v₁ + β u v₂) ∧
    (∀ u ∈ U₁, (∀ v ∈ U₂, β u v = 0) → u = 0) ∧
    (∀ v ∈ U₂, (∀ u ∈ U₁, β u v = 0) → v = 0) ∧
    ∀ k ∈ K, ∀ u ∈ U₁, ∀ v ∈ U₂, β (k u) (k v) = β u v

structure PGLConfig (Y K : Subgroup (LGL 2 W)) (U₁ U₂ : Submodule (ZMod 2) W) : Prop where
  le : K ≤ Y
  relIndex_eq : K.relIndex Y = 2
  disjoint : Disjoint U₁ U₂
  swap₁ : ∀ y ∈ Y, y ∉ K → ∀ u ∈ U₁, y u ∈ U₂
  swap₂ : ∀ y ∈ Y, y ∉ K → ∀ u ∈ U₂, y u ∈ U₁
  coord : ∃ (e : ↥K ≃* GL (Fin 3) (ZMod 2)) (φ : ↥U₁ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    IsNatCoord K U₁ e φ
  dual : IsDualPair K U₁ U₂

variable {Y K : Subgroup (LGL 2 W)} {U₁ U₂ : Submodule (ZMod 2) W}

theorem mem_centralizerOn_span_singleton {c : W} {y : LGL 2 W} :
    y ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) ↔ y ∈ Y ∧ y c = c := by
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, h c (Submodule.subset_span rfl)⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun u hu => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, h]

theorem PGLConfig.card_K (h : PGLConfig Y K U₁ U₂) : Nat.card K = 168 := by
  obtain ⟨e, -, -⟩ := h.coord
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_three]

theorem PGLConfig.exists_coords (h : PGLConfig Y K U₁ U₂) :
    ∃ (e : ↥K ≃* GL (Fin 3) (ZMod 2)) (φ₁ : ↥U₁ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (φ₂ : ↥U₂ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ (k : ↥K) (u : ↥U₁), (k : LGL 2 W) (u : W) = (u : W) ↔
        Matrix.mulVec ((e k : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ₁ u) =
          φ₁ u) ∧
      ∀ (k : ↥K) (v : ↥U₂), (k : LGL 2 W) (v : W) = (v : W) ↔
        Matrix.vecMul (φ₂ v) ((e k : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          φ₂ v := by
  obtain ⟨e, φ₁, hnat⟩ := h.coord
  obtain ⟨hinv, β, hb1, hb2, hl, hr, hβ⟩ := h.dual
  obtain ⟨φ₂, hkey⟩ := pgl_dual_equiv φ₁ β hb1 hb2 hl hr
  refine ⟨e, φ₁, φ₂, ?_, ?_⟩
  · intro k u
    set u' : ↥U₁ := ⟨(k : LGL 2 W) (u : W), hnat.1 k k.2 u u.2⟩ with hu'def
    have hnat_u : φ₁ u' = Matrix.mulVec ((e k : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ₁ u) := hnat.2 k u u' rfl
    constructor
    · intro hku
      have h1 : φ₁ u' = φ₁ u := by rw [show u' = u from Subtype.ext hku]
      exact hnat_u.symm.trans h1
    · intro hfix
      have h1 : φ₁ u' = φ₁ u := hnat_u.trans hfix
      exact congrArg Subtype.val (φ₁.injective h1)
  · intro k v
    set M : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
      ((e k : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hMdef
    set v' : ↥U₂ := ⟨(k : LGL 2 W) (v : W), hinv k k.2 v v.2⟩ with hv'def
    have hk : ∀ x : Fin 3 → ZMod 2,
        (φ₁.symm (Matrix.mulVec M x) : W) = (k : LGL 2 W) (φ₁.symm x : W) := by
      intro x
      have h2 := hnat.2 k (φ₁.symm x)
        ⟨(k : LGL 2 W) (φ₁.symm x : W), hnat.1 k k.2 _ (φ₁.symm x).2⟩ rfl
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [← h2, LinearEquiv.symm_apply_apply]
    have hrel : Matrix.vecMul (φ₂ v') M = φ₂ v := by
      have hdot : ∀ x : Fin 3 → ZMod 2,
          dotProduct (Matrix.vecMul (φ₂ v') M) x = dotProduct (φ₂ v) x := by
        intro x
        calc dotProduct (Matrix.vecMul (φ₂ v') M) x
            = dotProduct (φ₂ v') (Matrix.mulVec M x) := by
              rw [← Matrix.dotProduct_mulVec (φ₂ v') M x]
          _ = dotProduct (Matrix.mulVec M x) (φ₂ v') := dotProduct_comm _ _
          _ = β (φ₁.symm (Matrix.mulVec M x)) (v' : W) := (hkey (Matrix.mulVec M x) v').symm
          _ = β ((k : LGL 2 W) (φ₁.symm x : W)) (v' : W) := by rw [hk x]
          _ = β ((k : LGL 2 W) (φ₁.symm x : W)) ((k : LGL 2 W) (v : W)) := rfl
          _ = β (φ₁.symm x) (v : W) := hβ k k.2 (φ₁.symm x) (φ₁.symm x).2 v v.2
          _ = dotProduct x (φ₂ v) := hkey x v
          _ = dotProduct (φ₂ v) x := dotProduct_comm _ _
      funext j
      have hj := hdot (Pi.single j (1 : ZMod 2))
      rwa [dotProduct_single_one, dotProduct_single_one] at hj
    constructor
    · intro hkv
      have hvv : v' = v := Subtype.ext hkv
      rw [hvv] at hrel
      exact hrel
    · intro hfix
      have hvv : φ₂ v' = φ₂ v := by
        have hMN : M * (((e k)⁻¹ : GL (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          rw [hMdef]
          simpa using congrArg (fun u : GL (Fin 3) (ZMod 2) =>
            (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) (mul_inv_cancel (e k))
        have h1 : Matrix.vecMul (φ₂ v') M = Matrix.vecMul (φ₂ v) M :=
          hrel.trans hfix.symm
        have h2 := congrArg (fun w => Matrix.vecMul w
          (((e k)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
        rwa [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one,
          Matrix.vecMul_one] at h2
      exact congrArg Subtype.val (φ₂.injective hvv)

theorem PGLConfig.stab_le_and_card (h : PGLConfig Y K U₁ U₂) {c : W} (hc : c ∈ U₁ ∨ c ∈ U₂)
    (hc0 : c ≠ 0) :
    centralizerOn Y (Submodule.span (ZMod 2) {c}) ≤ K ∧
      Nat.card ↥(centralizerOn Y (Submodule.span (ZMod 2) {c})) = 24 := by
  classical
  have hmem : ∀ y : LGL 2 W,
      y ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) ↔ y ∈ Y ∧ y c = c :=
    fun y => mem_centralizerOn_span_singleton
  have hSK : centralizerOn Y (Submodule.span (ZMod 2) {c}) ≤ K := by
    intro y hy
    by_contra hyK
    obtain ⟨hyY, hyc⟩ := (hmem y).1 hy
    rcases hc with hcU₁ | hcU₂
    · have hycU₂ : y c ∈ U₂ := h.swap₁ y hyY hyK c hcU₁
      rw [hyc] at hycU₂
      exact hc0 ((Submodule.disjoint_def.mp h.disjoint) c hcU₁ hycU₂)
    · have hycU₁ : y c ∈ U₁ := h.swap₂ y hyY hyK c hcU₂
      rw [hyc] at hycU₁
      exact hc0 ((Submodule.disjoint_def.mp h.disjoint) c hycU₁ hcU₂)
  refine ⟨hSK, ?_⟩
  obtain ⟨e, φ₁, φ₂, h₁, h₂⟩ := h.exists_coords
  have hSKeq : Nat.card ↥(centralizerOn Y (Submodule.span (ZMod 2) {c})) =
      Nat.card {k : ↥K // (k : LGL 2 W) c = c} := Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, hSK s.2⟩, ((hmem s.1).1 s.2).2⟩
      invFun := fun k => ⟨k.1.1, (hmem k.1.1).2 ⟨h.le k.1.2, k.2⟩⟩
      left_inv := fun s => by ext; rfl
      right_inv := fun k => by ext; rfl }
  rcases hc with hcU₁ | hcU₂
  · have hcU₁' : φ₁ ⟨c, hcU₁⟩ ≠ 0 := fun hzero => hc0 (by
      have h : (⟨c, hcU₁⟩ : ↥U₁) = 0 := φ₁.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    have hcard : Nat.card {k : ↥K // (k : LGL 2 W) c = c} =
        Nat.card {M : GL (Fin 3) (ZMod 2) // Matrix.mulVec
          (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ₁ ⟨c, hcU₁⟩) = φ₁ ⟨c, hcU₁⟩} :=
      Nat.card_congr
        { toFun := fun k => ⟨e k.1, (h₁ k.1 ⟨c, hcU₁⟩).mp k.2⟩
          invFun := fun M => ⟨e.symm M.1, (h₁ (e.symm M.1) ⟨c, hcU₁⟩).mpr (by
            rw [MulEquiv.apply_symm_apply]; exact M.2)⟩
          left_inv := fun k => by ext; simp
          right_inv := fun M => by ext; simp }
    rw [hSKeq, hcard]
    exact GL32Fix.card_col (φ₁ ⟨c, hcU₁⟩) hcU₁'
  · have hcU₂' : φ₂ ⟨c, hcU₂⟩ ≠ 0 := fun hzero => hc0 (by
      have h : (⟨c, hcU₂⟩ : ↥U₂) = 0 := φ₂.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    have hcard : Nat.card {k : ↥K // (k : LGL 2 W) c = c} =
        Nat.card {M : GL (Fin 3) (ZMod 2) // Matrix.vecMul
          (φ₂ ⟨c, hcU₂⟩) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ₂ ⟨c, hcU₂⟩} :=
      Nat.card_congr
        { toFun := fun k => ⟨e k.1, (h₂ k.1 ⟨c, hcU₂⟩).mp k.2⟩
          invFun := fun M => ⟨e.symm M.1, (h₂ (e.symm M.1) ⟨c, hcU₂⟩).mpr (by
            rw [MulEquiv.apply_symm_apply]; exact M.2)⟩
          left_inv := fun k => by ext; simp
          right_inv := fun M => by ext; simp }
    rw [hSKeq, hcard]
    exact GL32Fix.card_row (φ₂ ⟨c, hcU₂⟩) hcU₂'

theorem PGLConfig.not_mem_normalizer_stab (h : PGLConfig Y K U₁ U₂) {c : W}
    (hc : c ∈ U₁ ∨ c ∈ U₂) (hc0 : c ≠ 0) {y : LGL 2 W} (hy : y ∈ Y) (hyK : y ∉ K) :
    y ∉ Subgroup.normalizer
      ((centralizerOn Y (Submodule.span (ZMod 2) {c}) : Subgroup (LGL 2 W)) : Set (LGL 2 W)) := by
  classical
  intro hynorm
  obtain ⟨hSK, -⟩ := h.stab_le_and_card hc hc0
  have hmem : ∀ z : LGL 2 W,
      z ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) ↔ z ∈ Y ∧ z c = c :=
    fun z => mem_centralizerOn_span_singleton
  have hfix : ∀ s ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}), s (y c) = y c := by
    intro s hs
    have hconj : y⁻¹ * s * y ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) :=
      (Subgroup.mem_normalizer_iff''.1 hynorm s).1 hs
    have hc' : (y⁻¹ * s * y) c = c := ((hmem _).1 hconj).2
    have := congrArg y hc'
    simpa using this
  have hyc_ne : y c ≠ 0 := fun hzero => hc0 (y.injective (by simp [hzero]))
  obtain ⟨e, φ₁, φ₂, h₁, h₂⟩ := h.exists_coords
  rcases hc with hcU₁ | hcU₂
  · have hycU₂ : y c ∈ U₂ := h.swap₁ y hy hyK c hcU₁
    have hc1 : φ₁ ⟨c, hcU₁⟩ ≠ 0 := fun hzero => hc0 (by
      have h : (⟨c, hcU₁⟩ : ↥U₁) = 0 := φ₁.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    have hyc2 : φ₂ ⟨y c, hycU₂⟩ ≠ 0 := fun hzero => hyc_ne (by
      have h : (⟨y c, hycU₂⟩ : ↥U₂) = 0 := φ₂.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    obtain ⟨M, hM1, hM2⟩ := GL32Fix.exists_col_not_row (φ₁ ⟨c, hcU₁⟩)
      (φ₂ ⟨y c, hycU₂⟩) hc1 hyc2
    set k : ↥K := e.symm M with hkdef
    have hkM : e k = M := by rw [hkdef]; exact MulEquiv.apply_symm_apply e M
    have hkc : (k : LGL 2 W) c = c := (h₁ k ⟨c, hcU₁⟩).mpr (by
      rw [show e k = M from hkM]; exact hM1)
    have hkS : (k : LGL 2 W) ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) :=
      (hmem _).2 ⟨h.le k.2, hkc⟩
    have hmove : (k : LGL 2 W) (y c) = y c := hfix _ hkS
    have hmat : Matrix.vecMul (φ₂ ⟨y c, hycU₂⟩) ((e k : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ₂ ⟨y c, hycU₂⟩ :=
      (h₂ k ⟨y c, hycU₂⟩).mp hmove
    exact hM2 (by simpa [hkM] using hmat)
  · have hycU₁ : y c ∈ U₁ := h.swap₂ y hy hyK c hcU₂
    have hc2 : φ₂ ⟨c, hcU₂⟩ ≠ 0 := fun hzero => hc0 (by
      have h : (⟨c, hcU₂⟩ : ↥U₂) = 0 := φ₂.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    have hyc1 : φ₁ ⟨y c, hycU₁⟩ ≠ 0 := fun hzero => hyc_ne (by
      have h : (⟨y c, hycU₁⟩ : ↥U₁) = 0 := φ₁.injective (by rw [hzero, map_zero])
      simpa using congrArg Subtype.val h)
    obtain ⟨M, hM1, hM2⟩ := GL32Fix.exists_row_not_col (φ₂ ⟨c, hcU₂⟩)
      (φ₁ ⟨y c, hycU₁⟩) hc2 hyc1
    set k : ↥K := e.symm M with hkdef
    have hkM : e k = M := by rw [hkdef]; exact MulEquiv.apply_symm_apply e M
    have hkc : (k : LGL 2 W) c = c := (h₂ k ⟨c, hcU₂⟩).mpr (by
      rw [show e k = M from hkM]; exact hM1)
    have hkS : (k : LGL 2 W) ∈ centralizerOn Y (Submodule.span (ZMod 2) {c}) :=
      (hmem _).2 ⟨h.le k.2, hkc⟩
    have hmove : (k : LGL 2 W) (y c) = y c := hfix _ hkS
    have hmat : Matrix.mulVec ((e k : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ₁ ⟨y c, hycU₁⟩) = φ₁ ⟨y c, hycU₁⟩ :=
      (h₁ k ⟨y c, hycU₁⟩).mp hmove
    exact hM2 (by simpa [hkM] using hmat)

private theorem pgl_mem_fixSub_zpowers {x : LGL 2 W} {u : W} (hxu : x u = u) :
    u ∈ fixSub (Subgroup.zpowers x) := by
  intro z hz
  let H : Subgroup (LGL 2 W) :=
    { carrier := {z | z u = u}
      mul_mem' := fun {p q} hp hq => by
        have hp' : p u = u := hp
        have hq' : q u = u := hq
        change (p * q) u = u
        rw [LinearEquiv.mul_apply, hq', hp']
      one_mem' := rfl
      inv_mem' := fun {p} hp => by
        have hp' : p u = u := hp
        have h := LinearEquiv.symm_apply_apply p u
        rwa [hp'] at h }
  exact Subgroup.zpowers_le.2 (show x ∈ H from hxu) hz

theorem PGLConfig.exists_vector (h : PGLConfig Y K U₁ U₂) {A : Subgroup (LGL 2 W)} (hAK : A ≤ K)
    (hA4 : Nat.card A = 4) (hAe : IsElemAbelian 2 A) :
    ∃ (B : Subgroup (LGL 2 W)) (c : W), B ≤ A ∧ mOf A B = 1 ∧ c ≠ 0 ∧ (c ∈ U₁ ∨ c ∈ U₂) ∧
      c ∈ CFSG.Quasithin.G11.commSpace A (fixSub B) := by
  classical
  haveI : Fintype ↥A := Fintype.ofFinite _
  obtain ⟨e, φ₁, φ₂, h₁, h₂⟩ := h.exists_coords
  obtain ⟨_e, _φ, hnat⟩ := h.coord
  have hcardA : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hA4
  have h3 : 1 < ((Finset.univ : Finset ↥A).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hcardA]
    norm_num
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h3
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
  have hxA : (a : LGL 2 W) ∈ A := a.2
  have hyA : (b : LGL 2 W) ∈ A := b.2
  have ha1' : (a : LGL 2 W) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : LGL 2 W) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcommA : a * b = b * a := by
    haveI : IsMulCommutative ↥A := hAe.1
    exact mul_comm' a b
  have hcomm : (a : LGL 2 W) * (b : LGL 2 W) = (b : LGL 2 W) * (a : LGL 2 W) :=
    congrArg Subtype.val hcommA
  have ha2 : (a : LGL 2 W) * (a : LGL 2 W) = 1 := by
    rw [← pow_two]; exact hAe.2 (a : LGL 2 W) hxA
  have hb2 : (b : LGL 2 W) * (b : LGL 2 W) = 1 := by
    rw [← pow_two]; exact hAe.2 (b : LGL 2 W) hyA
  set ax : ↥K := ⟨(a : LGL 2 W), hAK hxA⟩ with haxdef
  set bx : ↥K := ⟨(b : LGL 2 W), hAK hyA⟩ with hbxdef
  have hex1 : e ax ≠ 1 := fun h =>
    ha1' (congrArg (fun k : ↥K => (k : LGL 2 W)) (e.injective (by simpa using h)))
  have hey1 : e bx ≠ 1 := fun h =>
    hb1' (congrArg (fun k : ↥K => (k : LGL 2 W)) (e.injective (by simpa using h)))
  have hexy : e ax ≠ e bx := fun h =>
    hab (Subtype.ext (congrArg (fun k : ↥K => (k : LGL 2 W)) (e.injective h)))
  have hex2 : e ax * e ax = 1 := by
    rw [← map_mul, show ax * ax = 1 from Subtype.ext ha2, map_one]
  have hey2 : e bx * e bx = 1 := by
    rw [← map_mul, show bx * bx = 1 from Subtype.ext hb2, map_one]
  have hecomm : e ax * e bx = e bx * e ax := by
    rw [← map_mul, ← map_mul, show ax * bx = bx * ax from Subtype.ext hcomm]
  have hcardB : Nat.card (Subgroup.zpowers (a : LGL 2 W)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1'
  have hcard_sub : Nat.card ↥((Subgroup.zpowers (a : LGL 2 W)).subgroupOf A) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hxA)).toEquiv]
    exact hcardB
  have hmOf : mOf A (Subgroup.zpowers (a : LGL 2 W)) = 1 := by
    rw [mOf, Subgroup.index_eq_card_div, hA4, hcard_sub]
    decide
  obtain hu | hw := GL32Fix.exists_klein (e ax) (e bx) hex1 hey1 hexy hex2 hey2 hecomm
  · obtain ⟨u, hu1, hu2⟩ := hu
    set u' : ↥U₁ := φ₁.symm u with hu'def
    have hux : (ax : LGL 2 W) (u' : W) = (u' : W) :=
      (h₁ ax u').mpr (by simpa [u'] using hu1)
    have huy : ¬ ((bx : LGL 2 W) (u' : W) = (u' : W)) := fun hcontra =>
      hu2 (by simpa [u'] using (h₁ bx u').mp hcontra)
    have hfixB : (u' : W) ∈ fixSub (Subgroup.zpowers (a : LGL 2 W)) :=
      pgl_mem_fixSub_zpowers (x := (a : LGL 2 W)) hux
    refine ⟨Subgroup.zpowers (a : LGL 2 W), (b : LGL 2 W) (u' : W) - (u' : W),
      Subgroup.zpowers_le.2 hxA, hmOf, ?_, Or.inl ?_, ?_⟩
    · intro hzero
      exact huy (sub_eq_zero.mp hzero)
    · exact Submodule.sub_mem U₁ (hnat.1 _ (hAK hyA) _ (u').2) (u').2
    · exact Submodule.subset_span ⟨(b : LGL 2 W), hyA, (u' : W), hfixB, rfl⟩
  · obtain ⟨w, hw1, hw2⟩ := hw
    set v' : ↥U₂ := φ₂.symm w with hv'def
    have hvx : (ax : LGL 2 W) (v' : W) = (v' : W) :=
      (h₂ ax v').mpr (by simpa [v'] using hw1)
    have hvy : ¬ ((bx : LGL 2 W) (v' : W) = (v' : W)) := fun hcontra =>
      hw2 (by simpa [v'] using (h₂ bx v').mp hcontra)
    have hfixB : (v' : W) ∈ fixSub (Subgroup.zpowers (a : LGL 2 W)) :=
      pgl_mem_fixSub_zpowers (x := (a : LGL 2 W)) hvx
    refine ⟨Subgroup.zpowers (a : LGL 2 W), (b : LGL 2 W) (v' : W) - (v' : W),
      Subgroup.zpowers_le.2 hxA, hmOf, ?_, Or.inr ?_, ?_⟩
    · intro hzero
      exact hvy (sub_eq_zero.mp hzero)
    · exact Submodule.sub_mem U₂ (h.dual.1 _ (hAK hyA) _ (v').2) (v').2
    · exact Submodule.subset_span ⟨(b : LGL 2 W), hyA, (v' : W), hfixB, rfl⟩

end Config

theorem exists_mem_normalizer_not_mem {X : Type*} [Group X] [Finite X] {Y K P : Subgroup X}
    (hKY : K ≤ Y) (hidx : K.relIndex Y = 2) (hcardK : Nat.card K = 168) (hPK : P ≤ K)
    (hcardP : Nat.card P = 3) :
    ∃ n ∈ Y, n ∈ Subgroup.normalizer (P : Set X) ∧ n ∉ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx' : (K.subgroupOf Y).index = 2 := hidx
  haveI : (K.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hidx'
  have hcardY : Nat.card ↥Y = 336 := by
    have hc : Nat.card (K.subgroupOf Y) = 168 := by
      rw [← hcardK]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
    have h := Subgroup.index_mul_card (K.subgroupOf Y)
    rw [hidx', hc] at h
    omega
  have hcardPY : Nat.card (P.subgroupOf Y) = 3 := by
    rw [← hcardP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPK.trans hKY)).toEquiv
  have hP1 : IsPGroup 3 (P.subgroupOf Y) :=
    IsPGroup.of_card (n := 1) (by rw [hcardPY]; norm_num)
  have hnotdvd : ¬ 3 ∣ (P.subgroupOf Y).index := by
    rw [Subgroup.index_eq_card_div, hcardPY, hcardY]
    norm_num
  let P₀ : Sylow 3 ↥Y := hP1.toSylow hnotdvd
  have hP₀mem : ∀ z : ↥Y, z ∈ P₀ ↔ (z : X) ∈ P := by
    intro z
    rw [IsPGroup.mem_toSylow hP1 hnotdvd, Subgroup.mem_subgroupOf]
  have hP₀le : P₀ ≤ K.subgroupOf Y := by
    intro x hx
    exact hPK ((hP₀mem x).1 hx)
  have hfrattini : Subgroup.normalizer (P₀ : Set ↥Y) ⊔ K.subgroupOf Y = ⊤ :=
    Sylow.normalizer_sup_eq_top' P₀ hP₀le
  have hex : ∃ n : ↥Y, n ∈ Subgroup.normalizer (P₀ : Set ↥Y) ∧ n ∉ K.subgroupOf Y := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.normalizer (P₀ : Set ↥Y) ≤ K.subgroupOf Y := fun n hn => hcon n hn
    have htop : (⊤ : Subgroup ↥Y) ≤ K.subgroupOf Y := hfrattini ▸ sup_le hle le_rfl
    have hKYtop : K.subgroupOf Y = ⊤ := top_unique htop
    rw [hKYtop, Subgroup.index_top] at hidx'
    norm_num at hidx'
  obtain ⟨n, hnN, hnK⟩ := hex
  refine ⟨n.1, n.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxP
      have hxY : x ∈ Y := hPK.trans hKY hxP
      have hmem : (⟨x, hxY⟩ : ↥Y) ∈ P₀ := (hP₀mem _).2 hxP
      have hconj : n * (⟨x, hxY⟩ : ↥Y) * n⁻¹ ∈ P₀ :=
        (Subgroup.mem_normalizer_iff.1 hnN (⟨x, hxY⟩ : ↥Y)).1 hmem
      exact (hP₀mem _).1 hconj
    · intro hconj
      have hconjY : n.1 * x * n.1⁻¹ ∈ Y := hPK.trans hKY hconj
      have hxY : x ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem n.2) hconjY) n.2
        simpa [mul_assoc] using this
      have hmem : n * (⟨x, hxY⟩ : ↥Y) * n⁻¹ ∈ P₀ := (hP₀mem _).2 hconj
      exact (hP₀mem _).1 ((Subgroup.mem_normalizer_iff.1 hnN (⟨x, hxY⟩ : ↥Y)).2 hmem)
  · exact hnK

theorem sup_inf_normalizer_eq_of_outer {X : Type*} [Group X] [Finite X] {Y K S P : Subgroup X}
    (hKY : K ≤ Y) (hidx : K.relIndex Y = 2) (hcardK : Nat.card K = 168) (hSK : S ≤ K)
    (hcardS : Nat.card S = 24) (hPS : P ≤ S) (hcardP : Nat.card P = 3)
    (hout : ∀ y ∈ Y, y ∉ K → y ∉ Subgroup.normalizer (S : Set X)) :
    S ⊔ (Y ⊓ Subgroup.normalizer (P : Set X)) = Y := by
  classical
  obtain ⟨n, hny, hnN, hnK⟩ :=
    exists_mem_normalizer_not_mem hKY hidx hcardK (hPS.trans hSK) hcardP
  set X' : Subgroup X := S ⊔ (Y ⊓ Subgroup.normalizer (P : Set X)) with hX'def
  have hX'le : X' ≤ Y := sup_le (hSK.trans hKY) inf_le_left
  have hnX' : n ∈ X' := Subgroup.mem_sup_right ⟨hny, hnN⟩
  have hmax : ∀ T : Subgroup X, S ≤ T → T ≤ K → T = S ∨ T = K := by
    intro T hST hTK
    have hdvd1 : Nat.card S ∣ Nat.card T := by
      have h := Subgroup.card_subgroup_dvd_card (S.subgroupOf T)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv] at h
    have hdvd2 : Nat.card T ∣ Nat.card K := by
      have h := Subgroup.card_subgroup_dvd_card (T.subgroupOf K)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv] at h
    rw [hcardS] at hdvd1
    rw [hcardK] at hdvd2
    obtain ⟨d, hd⟩ := hdvd1
    have hd7 : d ∣ 7 := by
      have h : 24 * d ∣ 168 := by rwa [← hd]
      rw [show (168 : ℕ) = 24 * 7 from by norm_num] at h
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 24)).1 h
    rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd d hd7 with h1 | h7
    · left
      have hcardT : Nat.card T = 24 := by rw [hd, h1, mul_one]
      exact (Subgroup.eq_of_le_of_card_ge hST (by rw [hcardT, hcardS])).symm
    · right
      have hcardT : Nat.card T = 168 := by rw [hd, h7]
      exact Subgroup.eq_of_le_of_card_ge hTK (by rw [hcardK, hcardT])
  rcases hmax (X' ⊓ K) (le_inf le_sup_left hSK) inf_le_right with hcase | hcase
  · exfalso
    haveI : (K.subgroupOf Y).Normal :=
      Subgroup.normal_of_index_eq_two (show (K.subgroupOf Y).index = 2 from hidx)
    let f : ↥X' →* ↥Y ⧸ (K.subgroupOf Y) :=
      (QuotientGroup.mk' (K.subgroupOf Y)).comp (Subgroup.inclusion hX'le)
    have hf_ker : f.ker = S.subgroupOf X' := by
      ext z
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      have hx : (QuotientGroup.mk' (K.subgroupOf Y)) (Subgroup.inclusion hX'le z) = 1 ↔
          (Subgroup.inclusion hX'le z) ∈ K.subgroupOf Y := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      rw [hx, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hzK
        have hz : (z : X) ∈ X' ⊓ K := ⟨z.2, hzK⟩
        rwa [hcase] at hz
      · intro hzS
        exact hSK hzS
    have hf_range_ne : f.range ≠ ⊥ := by
      intro hbot
      have hmem : f ⟨n, hnX'⟩ ∈ f.range := ⟨⟨n, hnX'⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have hx : (QuotientGroup.mk' (K.subgroupOf Y)) (Subgroup.inclusion hX'le ⟨n, hnX'⟩) = 1 ↔
          (Subgroup.inclusion hX'le ⟨n, hnX'⟩) ∈ K.subgroupOf Y := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hnK (by simpa [Subgroup.mem_subgroupOf] using hx.1 hmem)
    have hrange_dvd : Nat.card f.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card f.range
      rw [← Subgroup.index_eq_card (K.subgroupOf Y)] at h
      rwa [show (K.subgroupOf Y).index = 2 from hidx] at h
    have hrange_card : Nat.card f.range = 2 := by
      have hne1 : Nat.card f.range ≠ 1 := fun h1 =>
        hf_range_ne (Subgroup.eq_bot_of_card_eq (H := f.range) h1)
      rcases (Nat.prime_two).eq_one_or_self_of_dvd (Nat.card f.range) hrange_dvd with h1 | h2
      · exact absurd h1 hne1
      · exact h2
    have hidxS : (S.subgroupOf X').index = 2 := by
      rw [← hf_ker, Subgroup.index_ker]
      exact hrange_card
    haveI : (S.subgroupOf X').Normal := Subgroup.normal_of_index_eq_two hidxS
    have hle : X' ≤ Subgroup.normalizer (S : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 inferInstance
    exact hout n hny hnK (hle hnX')
  · have hKX' : K ≤ X' := hcase ▸ inf_le_left
    have hYX' : Y ≤ X' := by
      intro y hy
      by_cases hyK : y ∈ K
      · exact hKX' hyK
      · have hmem : (⟨y, hy⟩⁻¹ : ↥Y) * ⟨n, hny⟩ ∈ K.subgroupOf Y := by
          rw [Subgroup.mul_mem_iff_of_index_two
            (show (K.subgroupOf Y).index = 2 from hidx)]
          simp [Subgroup.mem_subgroupOf, inv_mem_iff, hyK, hnK]
        have hyn : y⁻¹ * n ∈ K := by
          have := hmem
          simpa [Subgroup.mem_subgroupOf] using this
        have heq : y = n * (y⁻¹ * n)⁻¹ := by group
        rw [heq]
        exact X'.mul_mem hnX' (X'.inv_mem (hKX' hyn))
    exact hX'def ▸ le_antisymm hX'le hYX'

section Config

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
variable {Y K : Subgroup (LGL 2 W)} {U₁ U₂ : Submodule (ZMod 2) W}

theorem PGLConfig.sup_eq (h : PGLConfig Y K U₁ U₂) {c : W} (hc : c ∈ U₁ ∨ c ∈ U₂) (hc0 : c ≠ 0)
    {P : Subgroup (LGL 2 W)} (hPS : P ≤ centralizerOn Y (Submodule.span (ZMod 2) {c}))
    (hP : Nat.card P = 3) :
    centralizerOn Y (Submodule.span (ZMod 2) {c}) ⊔
      (Y ⊓ Subgroup.normalizer (P : Set (LGL 2 W))) = Y := by
  obtain ⟨hSK, hcardS⟩ := h.stab_le_and_card hc hc0
  exact sup_inf_normalizer_eq_of_outer h.le h.relIndex_eq h.card_K hSK hcardS hPS hP
    fun y hy hyK => h.not_mem_normalizer_stab hc hc0 hy hyK

end Config

theorem card_le_four_of_isPGL2 {X : Type} [Group X] {Y A : Subgroup X}
    (hY : CFSG.Quasithin.F6.IsPGL2 7 ↥Y) (hA : A ≤ Y) (hAe : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  classical
  obtain ⟨F, hfield, hfinite, hFcard, ⟨e⟩⟩ := hY
  letI : Field F := hfield
  letI : Finite F := hfinite
  have hcenter : StatedScalars (Fin 2) F = Subgroup.center (GL (Fin 2) F) :=
    CFSG.Open.StatedAPI.statedScalars_eq_center (Fin 2) F
  let ε : GL (Fin 2) F ⧸ StatedScalars (Fin 2) F ≃* CFSG.GorensteinWalter.PGL2 F :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  let A' : Subgroup ↥Y := A.subgroupOf Y
  let B : Subgroup (CFSG.GorensteinWalter.PGL2 F) := A'.map (e.trans ε).toMonoidHom
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hBcard : Nat.card B = Nat.card A' :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A' (e.trans ε).toMonoidHom
      (e.trans ε).injective).toEquiv).symm
  have hB2 : CFSG.Quasithin.IsElemAb2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      haveI : IsMulCommutative ↥A := hAe.1
      have hcommA : (⟨a.1, ha⟩ : ↥A) * ⟨b.1, hb⟩ = ⟨b.1, hb⟩ * ⟨a.1, ha⟩ :=
        mul_comm' _ _
      rw [← map_mul, ← map_mul, show a * b = b * a from
        Subtype.ext (congrArg (fun u : ↥A => (u : X)) hcommA)]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (hAe.2 a.1 ha), map_one]
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by norm_num, by norm_num, le_rfl, by rw [hFcard]; norm_num⟩
  have h := CFSG.Quasithin.card_le_four_of_isElemAb2_pgl2 hodd hB2
  rwa [hBcard, hA'card] at h

end CFSG.LocalAnalysis.WeakClosure81

end

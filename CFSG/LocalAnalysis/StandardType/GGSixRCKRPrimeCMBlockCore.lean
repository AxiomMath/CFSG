module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDConversePSL
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag)
open scoped commutatorElement

private theorem rckMapConj_le_of_map_eq {U X : Type} [Group U] [Group X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U} (hperf : ⁅J', J'⁆ = J') {u : U}
    (hu : (J'.map (MulAut.conj u).toMonoidHom).map ψ = J'.map ψ) :
    J'.map (MulAut.conj u).toMonoidHom ≤ J' := by
  set f : U →* U := (MulAut.conj u).toMonoidHom with hf
  set J'' : Subgroup U := J'.map f with hJ''
  have hperf'' : ⁅J'', J''⁆ = J'' := by
    rw [hJ'', ← Subgroup.map_commutator, hperf]
  rw [← hperf'']
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have hdec : ∀ x ∈ J'', ∃ j ∈ J', ∃ z ∈ ψ.ker, x = j * z := by
    intro x hx
    have hx' : ψ x ∈ J'.map ψ := by
      rw [← hu]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hψj⟩ := Subgroup.mem_map.mp hx'
    refine ⟨j, hj, j⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψj]
    group
  obtain ⟨ja, hja, za, hza, rfl⟩ := hdec a ha
  obtain ⟨jb, hjb, zb, hzb, rfl⟩ := hdec b hb
  have hcomm : ∀ x ∈ J', ∀ y ∈ ψ.ker, x * y = y * x :=
    fun x _ y hy => Subgroup.mem_center_iff.mp (hker hy) x
  rw [CFSG.GroupTheory.commutatorElement_mul_of_commute (A := J') (B := ψ.ker)
    hcomm hja hjb hza hzb]
  have hz : ⁅za, zb⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hker hza) zb).symm
  rw [hz, mul_one]
  exact hperf ▸ Subgroup.commutator_mem_commutator hja hjb

theorem rckNormalizes_of_map_eq {U X : Type} [Group U] [Group X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U} (hperf : ⁅J', J'⁆ = J') {s : U}
    (hs : (J'.map (MulAut.conj s).toMonoidHom).map ψ = J'.map ψ) :
    s ∈ Subgroup.normalizer (J' : Set U) := by
  have hconj : ∀ g x : U, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun _ _ => rfl
  have h1 : J'.map (MulAut.conj s).toMonoidHom ≤ J' :=
    rckMapConj_le_of_map_eq hker hperf hs
  have hle : J' ≤ J'.map (MulAut.conj s⁻¹).toMonoidHom := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨s * y * s⁻¹, h1 (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩), ?_⟩
    rw [hconj]
    group
  have h2 : J'.map (MulAut.conj s⁻¹).toMonoidHom ≤ J' := by
    apply rckMapConj_le_of_map_eq hker hperf
    rw [← hs]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨y₁, hy₁, rfl⟩ := Subgroup.mem_map.mp hy
      have hmem : ψ y₁ ∈ (J'.map (MulAut.conj s).toMonoidHom).map ψ := by
        rw [hs]
        exact Subgroup.mem_map.mpr ⟨y₁, hy₁, rfl⟩
      obtain ⟨a, ha, hψa⟩ := Subgroup.mem_map.mp hmem
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp ha
      have hψa' : ψ s * ψ y₀ * (ψ s)⁻¹ = ψ y₁ := by
        rw [← hψa, hconj, map_mul, map_mul, map_inv]
      have hval : ψ ((MulAut.conj s⁻¹).toMonoidHom y₁) = ψ y₀ := by
        rw [hconj]
        simp only [map_mul, map_inv, inv_inv]
        rw [← hψa']
        group
      rw [hval, hs]
      exact Subgroup.mem_map.mpr ⟨y₀, hy₀, rfl⟩
    · rw [hs]
      exact Subgroup.map_mono hle
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact h1 (Subgroup.mem_map.mpr ⟨n, hn, by rw [hconj]⟩)
  · intro hn
    have hm : (MulAut.conj s⁻¹).toMonoidHom (s * n * s⁻¹) ∈
        J'.map (MulAut.conj s⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨s * n * s⁻¹, hn, rfl⟩
    have h3 : (MulAut.conj s⁻¹).toMonoidHom (s * n * s⁻¹) = n := by
      rw [hconj]
      group
    exact h2 (h3 ▸ hm)

theorem rckIsComponentOf_top_of_commutator {U : Type} [Group U] {G J' : Subgroup U}
    (hJ' : IsComponentOf J' ⁅G, G⁆) : IsComponentOf (J'.subgroupOf G) ⊤ := by
  obtain ⟨hle, hsub, hq⟩ := hJ'
  have hcommG : ⁅G, G⁆ ≤ G :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)
  have hJG : J' ≤ G := hle.trans hcommG
  have hGN : G ≤ Subgroup.normalizer ((⁅G, G⁆ : Subgroup U) : Set U) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_commutator (H₁ := G) (H₂ := G) (f := (↑(MulAut.conj k) : U →* U))]
    have hGmap : G.map (↑(MulAut.conj k) : U →* U) = G := by
      refine le_antisymm ?_ ?_
      · rintro x ⟨a, ha, rfl⟩
        exact G.mul_mem (G.mul_mem hk ha) (G.inv_mem hk)
      · intro a ha
        exact ⟨k⁻¹ * a * k, G.mul_mem (G.mul_mem (G.inv_mem hk) ha) hk, by
          show (MulAut.conj k) (k⁻¹ * a * k) = a
          rw [MulAut.conj_apply]
          group⟩
    rw [hGmap]
  have hcommNormal : (⁅G, G⁆.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommG).2 hGN
  have hA2 : CFSG.Assembly.IsSubnormal ⁅G, G⁆ G :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hcommG).mpr hcommNormal.isSubnormal
  have hsubG : CFSG.Assembly.IsSubnormal J' G := hsub.trans hA2
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Assembly.IsSubnormal.of_mathlib
      (CFSG.Assembly.IsSubnormal.subgroupOf hsubG)
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG) hq

section Genuine


@[expose] def RCKModelConverse {M : Type} [Group M] (C : Subgroup M) (t : StatedLieTag) (m g : ℕ)
    (κ : (ggU t m g).K →* M) : Prop :=
  Function.Injective κ ∧ κ.range = C ∧
    ∀ c ∈ Subgroup.normalizer (C : Set M), ∀ (X : Type) [Group X]
      (φ : (ggU t m g).K →* X) (b : X),
      (∀ z z', κ z' = c * κ z * c⁻¹ → b⁻¹ * φ z * b = φ z') → GGPsiInnerDiag (ggU t m g).D φ b

theorem rckModelConverse_map {M M' : Type} [Group M] [Group M'] (Φ : M ≃* M')
    {C : Subgroup M} {t : StatedLieTag} {m g : ℕ} {κ : (ggU t m g).K →* M}
    (h : RCKModelConverse C t m g κ) :
    RCKModelConverse (C.map Φ.toMonoidHom) t m g (Φ.toMonoidHom.comp κ) := by
  obtain ⟨hinj, hrange, hconv⟩ := h
  refine ⟨Φ.injective.comp hinj, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro c' hc' X _ φ b hb
    have hc'' : Φ.symm c' ∈ Subgroup.normalizer (C : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp
          ((Subgroup.mem_normalizer_iff.mp hc' (Φ n)).mp
            (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩))
        have hΦ : Φ ((Φ.symm c') * n * (Φ.symm c')⁻¹) = Φ m := by
          simpa using hmn.symm
        rw [Φ.injective hΦ]
        exact hm
      · intro hn
        have h2 : c' * Φ n * c'⁻¹ ∈ C.map Φ.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(Φ.symm c') * n * (Φ.symm c')⁻¹, hn, by simp⟩
        obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp
          ((Subgroup.mem_normalizer_iff.mp hc' (Φ n)).mpr h2)
        rwa [← Φ.injective hmn]
    refine hconv (Φ.symm c') hc'' X φ b ?_
    intro z z' hzz'
    apply hb z z'
    simpa using congrArg (fun x => Φ x) hzz'

theorem rckModelConverse_of_inner {M : Type} [Group M] {C : Subgroup M} {t : StatedLieTag}
    {m g : ℕ} {κ : (ggU t m g).K →* M} (hinj : Function.Injective κ) (hrange : κ.range = C)
    (hinner : ∀ c ∈ Subgroup.normalizer (C : Set M),
      ∃ c₀ ∈ C, ∀ x ∈ C, c * x * c⁻¹ = c₀ * x * c₀⁻¹) :
    RCKModelConverse C t m g κ := by
  refine ⟨hinj, hrange, ?_⟩
  intro c hc X _ φ b hb
  obtain ⟨c₀, hc₀, hc₀eq⟩ := hinner c hc
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hc₀)
  have hkey : ∀ y, b⁻¹ * φ y * b = φ y₀ * φ y * (φ y₀)⁻¹ := by
    intro y
    have hyC : κ y ∈ C := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
    have hcc : c * κ y * c⁻¹ = c₀ * κ y * c₀⁻¹ := hc₀eq (κ y) hyC
    have hz' : κ (y₀ * y * y₀⁻¹) = c * κ y * c⁻¹ := by
      rw [map_mul, map_mul, map_inv, hy₀]
      exact hcc.symm
    simpa only [map_mul, map_inv] using hb y (y₀ * y * y₀⁻¹) hz'
  refine CFSG.StandardType.RootDetect.ggPsiInnerDiag_of_centralizes (ggU t m g).D (ψ := φ)
    (c := b) (a := y₀) ?_
  intro y
  have h := hkey y
  have hu : b * φ y₀ * φ y * (b * φ y₀)⁻¹ = φ y := by
    calc b * φ y₀ * φ y * (b * φ y₀)⁻¹
        = b * (φ y₀ * φ y * (φ y₀)⁻¹) * b⁻¹ := by group
      _ = b * (b⁻¹ * φ y * b) * b⁻¹ := by rw [← h]
      _ = φ y := by group
  calc (b * φ y₀)⁻¹ * φ y * (b * φ y₀)
      = (b * φ y₀)⁻¹ * ((b * φ y₀) * φ y * (b * φ y₀)⁻¹) * (b * φ y₀) := by rw [hu]
    _ = φ y := by group

theorem rckModelConverse_top {M : Type} [Group M] {t : StatedLieTag} {m g : ℕ}
    {κ : (ggU t m g).K →* M} (hinj : Function.Injective κ) (hsurj : Function.Surjective κ) :
    RCKModelConverse ⊤ t m g κ := by
  refine rckModelConverse_of_inner hinj (MonoidHom.range_eq_top.mpr hsurj) ?_
  intro c _
  exact ⟨c, Subgroup.mem_top c, fun _ _ => rfl⟩

private theorem rckConverse_SL_inner {k g : ℕ} {E : Type} [Field E] [Finite E]
    (σ : GaloisField 2 g ≃+* E) :
    ∀ c ∈ Subgroup.normalizer (CFSG.Open.StatedSL (k + 1) E : Set (GL (Fin (k + 1)) E)),
      ∀ (X : Type) [Group X]
        (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →* X) (b : X),
      (∀ z z', (Matrix.SpecialLinearGroup.toGL.comp
          (Matrix.SpecialLinearGroup.map σ.toRingHom) :
        Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →*
          GL (Fin (k + 1)) E) z' = c *
        (Matrix.SpecialLinearGroup.toGL.comp
          (Matrix.SpecialLinearGroup.map σ.toRingHom) :
        Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →*
          GL (Fin (k + 1)) E) z * c⁻¹ →
        b⁻¹ * φ z * b = φ z') →
      GGPsiInnerDiag (SpecialLinear.rootDatum k (GaloisField 2 g)) φ b := by
  intro c hc X _ φ b hb
  let κ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →* GL (Fin (k + 1)) E :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  have hmap_conjSL : ∀ (A : GL (Fin (k + 1)) (GaloisField 2 g))
      (u : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g)),
      Matrix.SpecialLinearGroup.map σ.toRingHom (InnerDiagA.conjSL A u) =
        InnerDiagA.conjSL (Matrix.GeneralLinearGroup.map σ.toRingHom A)
          (Matrix.SpecialLinearGroup.map σ.toRingHom u) := by
    intro A u
    apply Subtype.ext
    change ((InnerDiagA.conjSL A u : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 g)).map σ.toRingHom = _
    rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL, Matrix.map_mul, Matrix.map_mul,
      ← map_inv]
    rfl
  have hconjGL : ∀ (A : GL (Fin (k + 1)) E)
      (u : Matrix.SpecialLinearGroup (Fin (k + 1)) E),
      Matrix.SpecialLinearGroup.toGL (InnerDiagA.conjSL A u) =
        A * Matrix.SpecialLinearGroup.toGL u * A⁻¹ := by
    intro A u
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      InnerDiagA.coe_conjSL]
  let t : GL (Fin (k + 1)) (GaloisField 2 g) := Matrix.GeneralLinearGroup.map σ.symm.toRingHom c
  have ht : Matrix.GeneralLinearGroup.map σ.toRingHom t = c := by
    rw [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
    have hcomp : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id E := by
      ext x
      exact σ.apply_symm_apply x
    rw [hcomp, Matrix.GeneralLinearGroup.map_id]
    rfl
  have hb' : ∀ y : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g),
      b⁻¹ * φ y * b = φ (InnerDiagA.conjSL t y) := by
    intro y
    have hκ : κ (InnerDiagA.conjSL t y) = c * κ y * c⁻¹ := by
      calc κ (InnerDiagA.conjSL t y)
          = Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom
              (InnerDiagA.conjSL t y)) := rfl
        _ = Matrix.SpecialLinearGroup.toGL (InnerDiagA.conjSL
              (Matrix.GeneralLinearGroup.map σ.toRingHom t)
              (Matrix.SpecialLinearGroup.map σ.toRingHom y)) := by rw [hmap_conjSL]
        _ = (Matrix.GeneralLinearGroup.map σ.toRingHom t) *
              Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom y) *
              (Matrix.GeneralLinearGroup.map σ.toRingHom t)⁻¹ := hconjGL _ _
        _ = c * κ y * c⁻¹ := by rw [ht]; rfl
    exact hb y (InnerDiagA.conjSL t y) hκ
  exact CFSG.StandardType.ClassicalPosition.ggPsiInnerDiag_of_conjSL (k := k)
    (F := GaloisField 2 g) (φ := φ) (t := t) hb'

private theorem rckModelConverse_SL_aux {k g : ℕ} {E : Type} [Field E] [Finite E]
    (σ : GaloisField 2 g ≃+* E) :
    RCKModelConverse (CFSG.Open.StatedSL (k + 1) E) .PSL (k + 1) g
      (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map σ.toRingHom) :
        (ggU .PSL (k + 1) g).K →* GL (Fin (k + 1)) E) := by
  classical
  change RCKModelConverse (CFSG.Open.StatedSL (k + 1) E) .PSL (k + 1) g
    (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map σ.toRingHom) :
      (ggU .PSL (k + 1) g).K →* GL (Fin (k + 1)) E)
  let κ : (ggU .PSL (k + 1) g).K →* GL (Fin (k + 1)) E :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  have hinj : Function.Injective κ := by
    have hmapinj : Function.Injective
        (Matrix.SpecialLinearGroup.map σ.toRingHom :
          Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →
            Matrix.SpecialLinearGroup (Fin (k + 1)) E) := by
      intro x y hxy
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (k + 1)) E =>
        ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) E)) i j) hxy
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at h
      exact σ.injective h
    exact Matrix.SpecialLinearGroup.toGL_injective.comp hmapinj
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map σ.toRingHom :
        Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →
          Matrix.SpecialLinearGroup (Fin (k + 1)) E) := by
    intro A
    have hdet : ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) E).map σ.symm.toRingHom).det = 1 := by
      have hd := RingHom.map_det σ.symm.toRingHom
        (A : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
      rw [Matrix.SpecialLinearGroup.det_coe, map_one] at hd
      show (RingHom.mapMatrix σ.symm.toRingHom (A : Matrix (Fin (k + 1)) (Fin (k + 1)) E)).det = 1
      exact hd.symm
    let z : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) :=
      ⟨(A : Matrix (Fin (k + 1)) (Fin (k + 1)) E).map σ.symm.toRingHom, hdet⟩
    refine ⟨z, ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact σ.apply_symm_apply ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) E) i j)
  have hrangeSL : (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map σ.toRingHom :
        Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →*
          Matrix.SpecialLinearGroup (Fin (k + 1)) E)).range =
      CFSG.Open.StatedSL (k + 1) E := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      ← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  have hrange : κ.range = CFSG.Open.StatedSL (k + 1) E := hrangeSL
  refine ⟨hinj, hrange, ?_⟩
  intro c hc X _ φ b hb
  exact rckConverse_SL_inner σ c hc X φ b hb

theorem exists_rckModelConverse_SL {k g : ℕ} (hg : 1 ≤ g) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ^ g) :
    ∃ κ : (ggU .PSL (k + 1) g).K →* GL (Fin (k + 1)) E,
      RCKModelConverse (CFSG.Open.StatedSL (k + 1) E) .PSL (k + 1) g κ := by
  classical
  have hFcard : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
  haveI : Fintype (GaloisField 2 g) := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Nat.card (GaloisField 2 g) = Nat.card E := by rw [hFcard, hE]
  let σ : GaloisField 2 g ≃+* E := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ⟨Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map σ.toRingHom),
    rckModelConverse_SL_aux σ⟩

theorem rckClassicalModelID_of_block {X : Type} [Group X] {U : Type} [Group U] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) {G J' : Subgroup U} (hJ'G : J' ≤ G) {t : StatedLieTag}
    {m g : ℕ} {κ : (ggU t m g).K →* G} (hκ : RCKModelConverse (J'.subgroupOf G) t m g κ)
    (ht : RCKClassicalTag t) (hg : 1 ≤ g) {K B : Subgroup X} (hK : J'.map ψ = K)
    (hB : ∀ b ∈ B, ∃ s ∈ G, s ∈ Subgroup.normalizer (J' : Set U) ∧
      ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s * y * s⁻¹)) :
    RCKClassicalModelID K B := by
  obtain ⟨hκinj, hκrange, hκconv⟩ := hκ
  refine ⟨t, m, g, ψ.comp (G.subtype.comp κ), ht, hg, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_comp, hκrange,
      Subgroup.map_subgroupOf_eq_of_le hJ'G, hK]
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hzU : ((κ z : G) : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hz
    have hcz : ∀ u : U, u * ((κ z : G) : U) = ((κ z : G) : U) * u :=
      Subgroup.mem_center_iff.mp (hker hzU)
    apply hκinj
    simp only [map_mul]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hcz ((κ w : G) : U)
  · intro b hb
    obtain ⟨s, hsG, hsN, hconj⟩ := hB b hb
    let c : G := ⟨s, hsG⟩
    have hcN : c ∈ Subgroup.normalizer ((J'.subgroupOf G : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have hcoe : ((c * n * c⁻¹ : G) : U) = s * (n : U) * s⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe]
      exact Subgroup.mem_normalizer_iff.mp hsN (n : U)
    refine hκconv c hcN X (ψ.comp (G.subtype.comp κ)) b ?_
    intro z z' hzz'
    have hzJ : ((κ z : G) : U) ∈ J' := by
      have hmem : κ z ∈ J'.subgroupOf G := by
        rw [← hκrange]
        exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    have hval : ((κ z' : G) : U) = s * ((κ z : G) : U) * s⁻¹ := by
      have := congrArg (fun x : G => (x : U)) hzz'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    calc b⁻¹ * (ψ.comp (G.subtype.comp κ)) z * b
        = b⁻¹ * ψ ((κ z : G) : U) * b := rfl
      _ = ψ (s * ((κ z : G) : U) * s⁻¹) := hconj _ hzJ
      _ = ψ ((κ z' : G) : U) := by rw [hval]
      _ = (ψ.comp (G.subtype.comp κ)) z' := rfl

end Genuine

end CFSG.StandardType.RCKRP


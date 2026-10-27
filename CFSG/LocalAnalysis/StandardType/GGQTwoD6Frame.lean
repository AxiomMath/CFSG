module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6LinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumDet
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace QTwoD6

open Module CFSG.StandardType.QTwoLin

structure GGQ2D6Frame {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    (N : GGQ2NbrDatum 3 Bs K) (b : N.Λ) (hy : y ∈ Bs) where
  e : Fin 6 ≃ N.Λ
  coxeter_eq : N.coxeter = (ggCoxeterMatrixD 6).reindex e
  b_eq : b = e 4
  F : N.V ≃ₗ[ZMod 3] V7
  F_y : F (N.model (Additive.ofMul ⟨y, hy⟩)) = e0
  F_coroot : ∀ i, F (N.coroot (e i)) = hvec i
  F_root : ∀ (i : Fin 6) (v : N.V), N.root (e i) v = avec i (F v)

@[expose] noncomputable def ggCoord {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (F : N.V ≃ₗ[ZMod 3] V7) :
    MulAut ↥Bs →* (V7 ≃ₗ[ZMod 3] V7) :=
  (ggLinConj F).toMonoidHom.comp (ggLin (p := 3) N.model)

@[expose] noncomputable def ggEll {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {x : G}
    (N : GGQ2NbrDatum 3 Bs K) (F : N.V ≃ₗ[ZMod 3] V7) (hx : x ∈ Bs) : V7 :=
  F (N.model (Additive.ofMul ⟨x, hx⟩))

theorem ggQ2_d6_coord_apply {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (F : N.V ≃ₗ[ZMod 3] V7) (φ : MulAut ↥Bs) (v : V7) :
    ggCoord N F φ v = F (ggLin (p := 3) N.model φ (F.symm v)) := by
  rfl

theorem ggQ2d6_zpowers_subtype_iff {G : Type} [Group G] {Bs : Subgroup G} {y : G}
    (hy : y ∈ Bs) (b : ↥Bs) :
    (b : G) ∈ Subgroup.zpowers y ↔ b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem ggQ2d6_model_span_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {y : G} (hy : y ∈ Bs) (b : ↥Bs) :
    ι (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} ↔
      b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have h1 : c.val • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = ι (Additive.ofMul b) := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val, ZMod.natCast_zmod_val]
      exact hc
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, show ι (c.val • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        c.val • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from
      (ι.toAddMonoidHom).map_nsmul c.val (Additive.ofMul (⟨y, hy⟩ : ↥Bs))]
    exact h1
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hk]
    have h1 : ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k)) =
        k • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      rw [ofMul_zpow]
      exact (ι.toAddMonoidHom).map_zsmul k (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
    rw [h1, ← Int.cast_smul_eq_zsmul (R := ZMod p) k]
    exact Submodule.smul_mem _ (k : ZMod p) (Submodule.mem_span_singleton_self _)

theorem ggQ2d6_fix_weyl {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (N : GGQ2NbrDatum 3 Bs K) (hK1 : GGQTwoK1 3 B Bs x D J) (hy : y ∈ Bs) :
    ∀ v : N.V, (∀ g ∈ N.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} := by
  have hweyl : N.toWDatum.weyl = (ggAutomizer K Bs).map (ggLin (p := 3) N.model) :=
    GGQ2NbrDatum.weyl_eq_map N
  intro v
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, N.model (Additive.ofMul b) = v :=
    ⟨Additive.toMul (N.model.symm v), by simp⟩
  rw [hweyl]
  have hmapfix : (∀ g ∈ (ggAutomizer K Bs).map (ggLin (p := 3) N.model),
      g (N.model (Additive.ofMul b)) = N.model (Additive.ofMul b)) ↔
      N.model (Additive.ofMul b) ∈ ggFixedSubmodule (p := 3) N.model (ggAutomizer K Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    constructor
    · intro h ψ hψ
      exact h (ggLin (p := 3) N.model ψ) (Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩)
    · rintro h g hg
      obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h ψ hψ
  have hZiff : (b : G) ∈ ggBarCentralizer 3 Bs K ↔
      b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
    constructor
    · intro hb
      exact (ggQ2d6_zpowers_subtype_iff hy b).mp (hK1 y K hnb (b : G) hb.1 hb.2.2)
    · intro hb
      have hby : (b : G) ∈ Subgroup.zpowers y := (ggQ2d6_zpowers_subtype_iff hy b).mpr hb
      have htr := (hnb.1.2.2.2.2.2 (b : G)).mpr hby
      exact ⟨b.2, htr.2.1, htr.2.2⟩
  exact hmapfix.trans ((N.fixed_ZK b).trans
    (hZiff.trans (ggQ2d6_model_span_iff (p := 3) N.model hy b).symm))

theorem ggQ2d6_cartan_reindex {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (e : Fin 6 ≃ N.Λ)
    (hcox : N.coxeter = (ggCoxeterMatrixD 6).reindex e) :
    ∀ i j, N.cartan (e i) (e j) = cartanD6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [N.isCartan.1, cartanD6_eq]
    simp [CartanMatrix.D]
  · have hC1 : GGIntCartan ((ggCoxeterMatrixD 6).reindex e) N.cartan := hcox ▸ N.isCartan
    have hC2 : GGIntCartan ((ggCoxeterMatrixD 6).reindex e)
        (Matrix.of (fun a b : N.Λ => cartanD6 (e.symm a) (e.symm b))) := by
      rw [cartanD6_eq]
      exact (ggIntCartan_D 6).reindex e
    have hle : ((ggCoxeterMatrixD 6).reindex e) (e i) (e j) ≤ 3 := by
      rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        ggCoxeterMatrixD_apply]
      split_ifs <;> omega
    have hp := (hC1.pair hC2 (e.injective.ne hij)).2 hle
    rw [hp.1]
    simp only [Matrix.of_apply, Equiv.symm_apply_apply]

private theorem ggQ2d6l_det {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (e : Fin 6 ≃ N.Λ)
    (hcart : ∀ i j, N.cartan (e i) (e j) = cartanD6 i j) :
    ((N.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
  have heq : N.cartan = Matrix.of (fun a b : N.Λ => cartanD6 (e.symm a) (e.symm b)) := by
    ext a b
    obtain ⟨i, rfl⟩ := e.surjective a
    obtain ⟨j, rfl⟩ := e.surjective b
    rw [hcart i j]
    simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  have hdet_eq : (Matrix.of (fun a b : N.Λ => cartanD6 (e.symm a) (e.symm b))).det =
      cartanD6.det := Matrix.det_reindex_self e cartanD6
  rw [heq, hdet_eq, cartanD6_eq]
  have h : (CartanMatrix.D 6).det = 4 := by decide +kernel
  rw [h]
  decide

private theorem ggQ2d6l_avec_hvec (i k : Fin 6) :
    avec i (hvec k) = (cartanD6 k i : ZMod 3) := by
  simp only [avec, hvec, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    have h : (l.succ : Fin 7) ≠ k.succ := fun hh => hlk (Fin.succ_injective 6 hh)
    simp [h]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem ggQ2d6l_cartanD6_symm (i k : Fin 6) : cartanD6 i k = cartanD6 k i := by
  rw [cartanD6_eq]
  exact (CartanMatrix.D_isSymm 6).apply k i

private theorem ggQ2d6l_coroot_li {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (e : Fin 6 ≃ N.Λ)
    (hcart : ∀ i j, N.cartan (e i) (e j) = cartanD6 i j) :
    LinearIndependent (ZMod 3) (fun i : Fin 6 => N.coroot (e i)) := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  have hCdet : ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6).det ≠ 0 := by
    rw [← RingHom.map_det, cartanD6_eq]
    have h : (CartanMatrix.D 6).det = 4 := by decide +kernel
    rw [h]
    decide
  have h0 : ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6).mulVec c = 0 := by
    funext j
    have hj := congrArg (N.root (e j)) hc
    simp only [map_sum, map_smul, map_zero, N.pairing, smul_eq_mul] at hj
    change (∑ i, ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6) j i * c i) = 0
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hcart j i]
    exact mul_comm _ _
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hCdet h0) i

private theorem ggQ2d6l_yV_not_mem {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (e : Fin 6 ≃ N.Λ)
    (hcart : ∀ i j, N.cartan (e i) (e j) = cartanD6 i j) {y : G} (hy : y ∈ Bs)
    (hroot : ∀ i : N.Λ, N.root i (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0)
    (hyV0 : N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ≠ 0) :
    N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∉
      Submodule.span (ZMod 3) (Set.range (fun i : Fin 6 => N.coroot (e i))) := by
  intro hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hCdet : ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6).det ≠ 0 := by
    rw [← RingHom.map_det, cartanD6_eq]
    have h : (CartanMatrix.D 6).det = 4 := by decide +kernel
    rw [h]
    decide
  have h0 : ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6).mulVec c = 0 := by
    funext j
    have hj := congrArg (N.root (e j)) hc
    simp only [map_sum, map_smul, N.pairing, smul_eq_mul] at hj
    rw [hroot (e j)] at hj
    change (∑ i, ((Int.castRingHom (ZMod 3)).mapMatrix cartanD6) j i * c i) = 0
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hcart j i]
    exact mul_comm _ _
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hCdet h0
  have hz : N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = 0 := by
    rw [← hc, hc0]
    simp
  exact hyV0 hz

private theorem ggQ2d6l_root_yV {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) {y : G} (hy : y ∈ Bs)
    (hfix : ∀ v : N.V, (∀ g ∈ N.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))}) :
    ∀ i : N.Λ, N.root i (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
  have hweyl : N.toWDatum.weyl = (ggAutomizer K Bs).map (ggLin (p := 3) N.model) :=
    GGQ2NbrDatum.weyl_eq_map N
  intro i
  have hyVfix : ∀ g ∈ N.toWDatum.weyl,
      g (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) :=
    (hfix _).mpr (Submodule.mem_span_singleton_self _)
  have hmem : ggLin (p := 3) N.model (N.simple i) ∈ N.toWDatum.weyl := by
    rw [hweyl]
    exact Subgroup.mem_map.mpr ⟨N.simple i,
      by rw [N.automizer_K]; exact Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
  have h1 : ggLin (p := 3) N.model (N.simple i)
      (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
      N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := hyVfix _ hmem
  rw [N.simple_apply] at h1
  have h2 : N.root i (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • N.coroot i = 0 :=
    sub_eq_self.mp h1
  rcases smul_eq_zero.mp h2 with h | h
  · exact h
  · exfalso
    have h3 := N.pairing i i
    rw [h, map_zero, N.isCartan.1] at h3
    exact (by decide : (0 : ZMod 3) ≠ 2) h3

private theorem ggQ2d6l_exists_F {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (N : GGQ2NbrDatum 3 Bs K) (hK1 : GGQTwoK1 3 B Bs x D J) (hy : y ∈ Bs)
    (hfin : Module.finrank (ZMod 3) N.V = 7) (e : Fin 6 ≃ N.Λ)
    (hcox : N.coxeter = (ggCoxeterMatrixD 6).reindex e) :
    ∃ (F : N.V ≃ₗ[ZMod 3] V7),
      F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = e0 ∧
      (∀ i, F (N.coroot (e i)) = hvec i) ∧
      (∀ (i : Fin 6) (v : N.V), N.root (e i) v = avec i (F v)) := by
  have hcart := ggQ2d6_cartan_reindex N e hcox
  have hfix := ggQ2d6_fix_weyl hnb N hK1 hy
  have hroot := ggQ2d6l_root_yV N hy hfix
  let yV : N.V := N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hyV0 : yV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 :=
      N.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1)
  have hli := ggQ2d6l_coroot_li N e hcart
  have hnot := ggQ2d6l_yV_not_mem N e hcart hy hroot hyV0
  have hli' : LinearIndependent (ZMod 3) (Fin.cons yV (fun i : Fin 6 => N.coroot (e i))) :=
    LinearIndependent.fin_cons hli hnot
  have hcard : Fintype.card (Fin 7) = Module.finrank (ZMod 3) N.V := by
    rw [hfin, Fintype.card_fin]
  let B := basisOfLinearIndependentOfCardEqFinrank hli' hcard
  let F : N.V ≃ₗ[ZMod 3] V7 := B.equiv (Pi.basisFun (ZMod 3) (Fin 7)) (Equiv.refl (Fin 7))
  have hB : ⇑B = Fin.cons yV (fun i : Fin 6 => N.coroot (e i)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli' hcard
  have hF : ∀ i : Fin 7, F (B i) = Pi.single i 1 := by
    intro i
    simp only [F, Basis.equiv_apply, Equiv.refl_apply, Pi.basisFun_apply]
  have hFy : F yV = e0 := by
    have hyB : yV = B 0 := by rw [hB]; rfl
    rw [hyB, hF 0]
    rfl
  have hFcoroot : ∀ i, F (N.coroot (e i)) = hvec i := by
    intro i
    have hcB : N.coroot (e i) = B i.succ := by rw [hB]; rfl
    rw [hcB, hF i.succ]
    rfl
  refine ⟨F, hFy, hFcoroot, ?_⟩
  intro i v
  have hroot_eq : N.root (e i) = (avec i).comp F.toLinearMap := by
    refine B.ext fun j => ?_
    rw [hB]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero, LinearMap.comp_apply]
      change (N.root (e i)) yV = (avec i) (F yV)
      rw [hFy, hroot (e i)]
      simp [avec, e0]
    · simp only [Fin.cons_succ, LinearMap.comp_apply]
      change (N.root (e i)) (N.coroot (e k)) = (avec i) (F (N.coroot (e k)))
      rw [hFcoroot k, N.pairing, hcart i k, ggQ2d6l_avec_hvec i k,
        ggQ2d6l_cartanD6_symm i k]
  exact LinearMap.congr_fun hroot_eq v

theorem ggQ2_d6_coord_simple {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs}
    (Fr : GGQ2D6Frame N b hy) (i : Fin 6) :
    ggCoord N Fr.F (N.simple (Fr.e i)) = simpleD6 i := by
  refine LinearEquiv.ext fun v => ?_
  rw [ggQ2_d6_coord_apply, N.simple_apply, map_sub, map_smul, Fr.F_coroot, Fr.F_root,
    LinearEquiv.apply_symm_apply, simpleD6, Module.reflection_apply]
  rfl

theorem ggQ2_d6_finrank {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (N : GGQ2NbrDatum 3 Bs K) (b : N.Λ) (hb : N.IsD6Fork b)
    (hK1 : GGQTwoK1 3 B Bs x D J) (hy : y ∈ Bs) : Module.finrank (ZMod 3) N.V = 7 := by
  obtain ⟨e, hcox, -⟩ := hb
  have hcart := ggQ2d6_cartan_reindex N e hcox
  have hfix := ggQ2d6_fix_weyl hnb N hK1 hy
  have hroot := ggQ2d6l_root_yV N hy hfix
  let yV : N.V := N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hyV0 : yV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 :=
      N.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1)
  let Φ : N.V →ₗ[ZMod 3] (N.Λ →₀ ZMod 3) :=
    { toFun := fun v => Finsupp.equivFunOnFinite.symm (fun i => N.root i v)
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro c a; ext i; simp }
  have hΦ : ∀ (v : N.V) (i : N.Λ), (Φ v) i = N.root i v := by
    intro v i
    simp [Φ]
  have : Finite N.V := Finite.of_equiv (Additive ↥Bs) N.model.toEquiv
  have : FiniteDimensional (ZMod 3) N.V := Finite.of_finite
  have hweyl : N.toWDatum.weyl = (ggAutomizer K Bs).map (ggLin (p := 3) N.model) :=
    GGQ2NbrDatum.weyl_eq_map N
  have hker : LinearMap.ker Φ = Submodule.span (ZMod 3) {yV} := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [← hfix v]
      have hv0 : ∀ i : N.Λ, N.root i v = 0 := by
        intro i
        have hvi := DFunLike.congr_fun (LinearMap.mem_ker.mp hv) i
        rwa [hΦ] at hvi
      intro g hg
      rw [hweyl] at hg
      obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
      have hψ' : ψ ∈ Subgroup.closure (Set.range N.simple) := by
        rw [← N.automizer_K]; exact hψ
      refine Subgroup.closure_induction (p := fun ψ _ => ggLin (p := 3) N.model ψ v = v)
        ?_ ?_ ?_ ?_ hψ'
      · rintro ψ ⟨i, rfl⟩
        rw [N.simple_apply, hv0 i, zero_smul, sub_zero]
      · simp
      · intro a b _ _ ha hb
        rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      · intro a _ ha
        rw [map_inv]
        have h1 : (ggLin (p := 3) N.model a)⁻¹ ((ggLin (p := 3) N.model a) v) = v := by
          rw [← LinearEquiv.mul_apply, inv_mul_cancel]
          rfl
        rw [ha] at h1
        exact h1
    · rw [Submodule.span_le]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      change Φ yV = 0
      ext i
      rw [hΦ, hroot i]
      simp
  have hfin_ker : Module.finrank (ZMod 3) (LinearMap.ker Φ) = 1 := by
    rw [hker, finrank_span_singleton hyV0]
  have hli_im : LinearIndependent (ZMod 3) (fun i : N.Λ => Φ (N.coroot i)) := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hc i
    have hCdet : ((Int.castRingHom (ZMod 3)).mapMatrix N.cartan).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact ggQ2d6l_det N e hcart
    have h0 : ((Int.castRingHom (ZMod 3)).mapMatrix N.cartan).mulVec c = 0 := by
      funext j
      have hj := DFunLike.congr_fun hc j
      simp only [Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Finsupp.coe_zero, Pi.zero_apply, hΦ, N.pairing, smul_eq_mul] at hj
      rw [Matrix.mulVec, dotProduct]
      rw [show (∑ i, ((Int.castRingHom (ZMod 3)).mapMatrix N.cartan) j i * c i) =
          ∑ i, c i * (N.cartan j i : ZMod 3) by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RingHom.mapMatrix_apply, Matrix.map_apply]
        exact mul_comm _ _]
      exact hj
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hCdet h0) i
  have hcard : Fintype.card N.Λ = 6 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hfin_range : Module.finrank (ZMod 3) (LinearMap.range Φ) = 6 := by
    have hsp : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range (fun i : N.Λ => Φ (N.coroot i)))) = 6 := by
      rw [finrank_span_eq_card hli_im, hcard]
    have hle : Submodule.span (ZMod 3) (Set.range (fun i : N.Λ => Φ (N.coroot i))) ≤
        LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact ⟨N.coroot i, rfl⟩
    have hmono : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range (fun i : N.Λ => Φ (N.coroot i)))) ≤
        Module.finrank (ZMod 3) (LinearMap.range Φ) := Submodule.finrank_mono hle
    have htop : Module.finrank (ZMod 3) (LinearMap.range Φ) ≤ 6 := by
      have h := Submodule.finrank_le (LinearMap.range Φ)
      rwa [Module.finrank_finsupp_self, hcard] at h
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  omega

theorem ggQ2_d6_frame {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (N : GGQ2NbrDatum 3 Bs K) (b : N.Λ) (hb : N.IsD6Fork b)
    (hK1 : GGQTwoK1 3 B Bs x D J) (hy : y ∈ Bs) :
    Nonempty (GGQ2D6Frame N b hy) := by
  obtain ⟨e₀, hcox₀, hb4 | hb5⟩ := hb
  · have hfin := ggQ2_d6_finrank hnb N b ⟨e₀, hcox₀, Or.inl hb4⟩ hK1 hy
    obtain ⟨F, hFy, hFcoroot, hFroot⟩ := ggQ2d6l_exists_F hnb N hK1 hy hfin e₀ hcox₀
    exact ⟨⟨e₀, hcox₀, hb4, F, hFy, hFcoroot, hFroot⟩⟩
  · let σ : Fin 6 ≃ Fin 6 := Equiv.swap 4 5
    let e : Fin 6 ≃ N.Λ := σ.trans e₀
    have he4 : e 4 = e₀ 5 := by simp [e, σ]
    have hbeq : b = e 4 := by rw [hb5, he4]
    have hσ : (ggCoxeterMatrixD 6).reindex σ = ggCoxeterMatrixD 6 := by
      ext i j
      fin_cases i <;> fin_cases j <;> decide
    have hσ' : ∀ a b, (ggCoxeterMatrixD 6) (σ.symm a) (σ.symm b) =
        (ggCoxeterMatrixD 6) a b := by
      intro a b
      have h := congrFun (congrFun (congrArg CoxeterMatrix.M hσ) a) b
      simpa only [CoxeterMatrix.reindex_apply] using h
    have hcox : N.coxeter = (ggCoxeterMatrixD 6).reindex e := by
      rw [hcox₀]
      dsimp only [e]
      apply CoxeterMatrix.ext
      ext i j
      rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply]
      exact (hσ' (e₀.symm i) (e₀.symm j)).symm
    have hfin := ggQ2_d6_finrank hnb N b ⟨e, hcox, Or.inl hbeq⟩ hK1 hy
    obtain ⟨F, hFy, hFcoroot, hFroot⟩ := ggQ2d6l_exists_F hnb N hK1 hy hfin e hcox
    exact ⟨⟨e, hcox, hbeq, F, hFy, hFcoroot, hFroot⟩⟩

end QTwoD6

end CFSG.StandardType

end

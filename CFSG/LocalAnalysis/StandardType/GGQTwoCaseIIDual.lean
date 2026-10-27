module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def GGQ2Lin.dual {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) : GGQ2Lin p where
  ι := D.ι
  coxeter := D.coxeter
  cartan := D.cartan
  V := Module.Dual (ZMod p) D.V
  coroot := D.root
  root := fun k => Module.Dual.eval (ZMod p) D.V (D.coroot k)
  a := D.a
  b := D.b
  a_ne_b := D.a_ne_b
  a_leaf := D.a_leaf
  isWeyl := D.isWeyl
  isCartan := D.isCartan
  pairing := fun i j => by
    simp [D.pairing, hsym j i]

@[expose] noncomputable def ggContra {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] :
    (V ≃ₗ[ZMod p] V) →* (Module.Dual (ZMod p) V ≃ₗ[ZMod p] Module.Dual (ZMod p) V) where
  toFun g := g.symm.dualMap
  map_one' := by
    ext f v
    change f ((LinearEquiv.refl (ZMod p) V).symm v) = f v
    rw [LinearEquiv.refl_symm]
    rfl
  map_mul' g h := by
    ext f v
    rw [LinearEquiv.mul_apply, LinearEquiv.dualMap_apply, LinearEquiv.dualMap_apply,
      LinearEquiv.dualMap_apply]
    have hsym : (g * h).symm v = h.symm (g.symm v) := by
      apply (g * h).injective
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    rw [hsym]

theorem ggContra_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) (f : Module.Dual (ZMod p) V) (v : V) :
    ggContra g f v = f (g.symm v) :=
  LinearEquiv.dualMap_apply g.symm f v

private theorem ggQ2xCD_contra_reflection {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (c : V) (φ : Dual (ZMod p) V) (h : φ c = 2) :
    ggContra (Module.reflection h) =
      Module.reflection (show (Dual.eval (ZMod p) V) c φ = 2 by simpa using h) := by
  ext f v
  rw [ggContra_apply, Module.reflection_symm h, Module.reflection_apply v h,
    Module.reflection_apply f (show (Dual.eval (ZMod p) V) c φ = 2 by simpa using h)]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Dual.eval_apply,
    smul_eq_mul]
  ring

private theorem ggQ2xCD_contra_isReflLin_forward {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {g : V ≃ₗ[ZMod 3] V} (h : IsReflLin g) : IsReflLin (ggContra g) := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  exact ⟨φ, (Dual.eval (ZMod 3) V) c,
    show (Dual.eval (ZMod 3) V) c φ = 2 by simpa using hc,
    ggQ2xCD_contra_reflection c φ hc⟩

private theorem ggQ2xCD_contra_contra_eq_linConj {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] (g : V ≃ₗ[ZMod 3] V) :
    ggContra (ggContra g) = ggLinConj (Module.evalEquiv (ZMod 3) V) g := by
  refine LinearEquiv.ext (fun Φ => ?_)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv (ZMod 3) V).surjective Φ
  rw [ggLinConj_apply, LinearEquiv.symm_apply_apply, Module.evalEquiv_apply]
  refine LinearMap.ext (fun w => ?_)
  rw [ggContra_apply, Dual.eval_apply]
  have hsym : (ggContra g).symm = g.dualMap := by
    have h1 : ggContra g = g.symm.dualMap := rfl
    rw [h1, LinearEquiv.dualMap_symm, LinearEquiv.symm_symm]
  rw [hsym, LinearEquiv.dualMap_apply, Module.evalEquiv_apply, Dual.eval_apply]

private theorem ggQ2xCD_linConj_isTransvectionLin {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    IsTransvectionLin (ggLinConj τ g) ↔ IsTransvectionLin g := by
  constructor
  · rintro ⟨u', ψ', hu', hψ', hψ'u', hg'⟩
    refine ⟨τ.symm u', ψ'.comp (τ : V ≃ₗ[ZMod p] V').toLinearMap, ?_, ?_, ?_, fun v => ?_⟩
    · simpa using τ.symm.injective.ne hu'
    · intro h0
      apply hψ'
      ext w
      obtain ⟨w', rfl⟩ := τ.surjective w
      have := congrArg (fun θ => θ w') h0
      simpa using this
    · simp [hψ'u']
    · have h := hg' (τ v)
      rw [ggLinConj_apply, LinearEquiv.symm_apply_apply] at h
      apply τ.injective
      rw [h, map_add, map_smul, LinearEquiv.apply_symm_apply]
      rfl
  · rintro ⟨u, ψ, hu, hψ, hψu, hg⟩
    refine ⟨τ u, ψ.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap, ?_, ?_, ?_, fun v' => ?_⟩
    · simpa using τ.injective.ne hu
    · intro h0
      apply hψ
      ext w
      obtain ⟨w', rfl⟩ := τ.symm.surjective w
      have := congrArg (fun θ => θ w') h0
      simpa using this
    · simp [hψu]
    · rw [ggLinConj_apply, hg (τ.symm v')]
      simp

private theorem ggQ2xCD_contra_isTransvectionLin_forward {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {g : V ≃ₗ[ZMod 3] V} (h : IsTransvectionLin g) :
    IsTransvectionLin (ggContra g) := by
  obtain ⟨u, ψ, hu, hψ, hψu, hg⟩ := h
  refine ⟨ψ, -(Dual.eval (ZMod 3) V) u, hψ, ?_, ?_, fun f => ?_⟩
  · intro h0
    refine hu ((Module.forall_dual_apply_eq_zero_iff (ZMod 3) u).mp (fun f => ?_))
    have := congrArg (fun θ : Dual (ZMod 3) (Dual (ZMod 3) V) => θ f) h0
    simpa [LinearMap.neg_apply, Dual.eval_apply] using this
  · simp [LinearMap.neg_apply, Dual.eval_apply, hψu]
  · ext v
    have hsym : g.symm v = v - ψ v • u := by
      have h1 : g (v - ψ v • u) = v := by
        rw [hg]
        simp [map_sub, map_smul, hψu]
      conv_lhs => rw [← h1]
      rw [LinearEquiv.symm_apply_apply]
    rw [ggContra_apply, hsym, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Dual.eval_apply, smul_eq_mul, smul_eq_mul]
    ring

private theorem ggQ2xCD_contra_isTransvectionLin_iff {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] (g : V ≃ₗ[ZMod 3] V) :
    IsTransvectionLin (ggContra g) ↔ IsTransvectionLin g := by
  refine ⟨fun h => ?_, ggQ2xCD_contra_isTransvectionLin_forward⟩
  have h1 : IsTransvectionLin (ggContra (ggContra g)) :=
    ggQ2xCD_contra_isTransvectionLin_forward h
  rw [ggQ2xCD_contra_contra_eq_linConj g] at h1
  exact (ggQ2xCD_linConj_isTransvectionLin (Module.evalEquiv (ZMod 3) V) g).mp h1

private theorem ggQ2xCD_weyl_le_reflGp {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) : D.weyl ≤ reflGp A := by
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, Subgroup.closure_le]
  rintro t ⟨k, -, rfl⟩
  exact Subgroup.subset_closure
    ⟨hW (Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩),
      ⟨D.coroot k, D.root k, D.root_coroot_self k, rfl⟩⟩

theorem ggContra_injective {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] :
    Function.Injective (ggContra (p := p) (V := V)) := by
  intro g h hgh
  have hsym : g.symm = h.symm := by
    ext v
    exact sub_eq_zero.mp
      ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (g.symm v - h.symm v)).mp (fun f => by
        have hfv : f (g.symm v) = f (h.symm v) := by
          have hcong := congrArg (fun θ : Dual (ZMod p) V => θ v)
            (congrArg (fun e : Dual (ZMod p) V ≃ₗ[ZMod p] Dual (ZMod p) V => e f) hgh)
          rwa [ggContra_apply, ggContra_apply] at hcong
        rw [map_sub, hfv, sub_self]))
  simpa using congrArg LinearEquiv.symm hsym

theorem ggContra_neg {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (g h : V ≃ₗ[ZMod p] V) (hh : ∀ v, h v = -(g v)) :
    ∀ f, ggContra h f = -(ggContra g f) := by
  intro f
  ext v
  have h1 : v = -(g (h.symm v)) := by
    have := hh (h.symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h3 : g.symm v = -(h.symm v) := by
    conv_lhs => rw [h1]
    rw [map_neg, LinearEquiv.symm_apply_apply]
  have h2 : h.symm v = -(g.symm v) := by
    rw [h3]
    simp
  rw [ggContra_apply, LinearMap.neg_apply, ggContra_apply, h2, map_neg]

theorem ggContra_simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) (k : D.ι) :
    ggContra (D.simpleRefl k) = (D.dual hsym).simpleRefl k := by
  have h_ours : (Dual.eval (ZMod p) D.V) (D.coroot k) (D.root k) = 2 := by
    simpa using D.root_coroot_self k
  ext f v
  rw [ggContra_apply]
  change f ((Module.reflection (D.root_coroot_self k)).symm v) =
    (Module.reflection h_ours) f v
  rw [Module.reflection_symm (D.root_coroot_self k),
    Module.reflection_apply v (D.root_coroot_self k), Module.reflection_apply f h_ours]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Dual.eval_apply,
    smul_eq_mul]
  ring

theorem ggContra_weyl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) :
    D.weyl.map ggContra = (D.dual hsym).weyl := by
  rw [GGQ2Lin.weyl, GGQ2Lin.weyl, GGQ2Lin.parab, GGQ2Lin.parab, MonoidHom.map_closure]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr (fun k _ => ggContra_simpleRefl D hsym k)

theorem ggContra_isReflLin_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (g : V ≃ₗ[ZMod 3] V) :
    IsReflLin (ggContra g) ↔ IsReflLin g := by
  refine ⟨fun h => ?_, ggQ2xCD_contra_isReflLin_forward⟩
  have h1 : IsReflLin (ggContra (ggContra g)) := ggQ2xCD_contra_isReflLin_forward h
  rw [ggQ2xCD_contra_contra_eq_linConj g] at h1
  exact (ggLinConj_isReflLin (Module.evalEquiv (ZMod 3) V) g).mp h1

theorem ggContra_transvectionFree {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : TransvectionFree A) :
    TransvectionFree (A.map ggContra) := by
  intro g' hg' htr
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
  exact hA g hg ((ggQ2xCD_contra_isTransvectionLin_iff g).mp htr)

theorem ggQ2_dual_basis_iff {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) [FiniteDimensional (ZMod p) D.V]
    (hdim : Fintype.card D.ι = Module.finrank (ZMod p) D.V) :
    (D.dual hsym).Basis ↔ ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0 := by
  change LinearIndependent (ZMod p) D.root ∧
      Fintype.card D.ι = Module.finrank (ZMod p) (Dual (ZMod p) D.V) ↔
    ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0
  constructor
  · intro hbas
    haveI : Nonempty D.ι := ⟨D.a⟩
    have hspan : Submodule.span (ZMod p) (Set.range D.root) = ⊤ :=
      LinearIndependent.span_eq_top_of_card_eq_finrank hbas.1 hbas.2
    intro v hv
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) v).mp (fun φ => ?_)
    have hker : Submodule.span (ZMod p) (Set.range D.root) ≤
        LinearMap.ker (Dual.eval (ZMod p) D.V v) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change (Dual.eval (ZMod p) D.V v) (D.root k) = 0
      rw [Dual.eval_apply]
      exact hv k
    have htop : LinearMap.ker (Dual.eval (ZMod p) D.V v) = ⊤ :=
      top_le_iff.mp (hspan ▸ hker)
    have hmem : φ ∈ LinearMap.ker (Dual.eval (ZMod p) D.V v) := by
      rw [htop]
      exact Submodule.mem_top
    rwa [LinearMap.mem_ker, Dual.eval_apply] at hmem
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro c hc k
      let ev : D.V →ₗ[ZMod p] (D.ι → ZMod p) := LinearMap.pi (fun k => D.root k)
      have hev_inj : Function.Injective ev := by
        intro u v huv
        have h0 : ev (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have h1 : u - v = 0 := h (u - v) (fun k => by
          have := congrFun h0 k
          simpa [ev, LinearMap.pi_apply] using this)
        exact sub_eq_zero.mp h1
      have hrank : Module.finrank (ZMod p) D.V =
          Module.finrank (ZMod p) (D.ι → ZMod p) := by
        rw [Module.finrank_pi]
        exact hdim.symm
      have hev_surj : Function.Surjective ev :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ev) hrank).mp hev_inj
      obtain ⟨v, hv⟩ := hev_surj (Pi.single k (1 : ZMod p))
      have hcv : (∑ j, c j • D.root j) v = 0 := by rw [hc, LinearMap.zero_apply]
      have h2 : ∀ j, D.root j v = (Pi.single k (1 : ZMod p) : D.ι → ZMod p) j := by
        intro j
        rw [← congrFun hv j]
        simp [ev, LinearMap.pi_apply]
      have hsum : ∑ j, c j * (Pi.single k (1 : ZMod p) : D.ι → ZMod p) j = 0 := by
        simpa [h2, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hcv
      have hsingle : ∑ j, c j * (Pi.single k (1 : ZMod p) : D.ι → ZMod p) j = c k := by
        trans c k * (Pi.single k (1 : ZMod p) : D.ι → ZMod p) k
        · apply Finset.sum_eq_single k
          · intro b _ hb
            rw [Pi.single_eq_of_ne hb, mul_zero]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
        · simp
      rw [hsingle] at hsum
      exact hsum
    · rw [Subspace.dual_finrank_eq]
      exact hdim

theorem ggQ2_P3_of_dual_pm {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (x : D.V)
    (hpm : ∀ a ∈ A.map ggContra, ∃ g ∈ (D.dual hsym).weyl,
      (∀ f, a f = g f) ∨ (∀ f, a f = -(g f))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod p) {φ x} = Submodule.span (ZMod p) {r x} := by
  apply ggQ2_P3_of_pm A x
  intro φ hφ
  obtain ⟨g, hgW, hgcase⟩ := hpm (ggContra φ) (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
  let g' : Dual (ZMod p) D.V ≃ₗ[ZMod p] Dual (ZMod p) D.V := g
  have hgW' : g' ∈ (D.dual hsym).weyl := hgW
  have hgcase' : (∀ f : Dual (ZMod p) D.V, ggContra φ f = g' f) ∨
      (∀ f : Dual (ZMod p) D.V, ggContra φ f = -(g' f)) := hgcase
  have hgmap : g' ∈ D.weyl.map ggContra := by
    rw [ggContra_weyl D hsym]
    exact hgW'
  obtain ⟨w, hwW, hwg⟩ := Subgroup.mem_map.mp hgmap
  refine ⟨w, ggQ2xCD_weyl_le_reflGp D A hW hwW, ?_⟩
  rcases hgcase' with h1 | h2
  · left
    have heq : ggContra φ = ggContra w := by
      ext f x
      rw [h1 f]
      exact congrArg (fun θ : Dual (ZMod p) D.V => θ x)
        (congrArg (fun e : Dual (ZMod p) D.V ≃ₗ[ZMod p] Dual (ZMod p) D.V => e f) hwg).symm
    intro v
    exact congrArg (fun e : D.V ≃ₗ[ZMod p] D.V => e v) (ggContra_injective heq)
  · right
    let hneg : D.V ≃ₗ[ZMod p] D.V := w.trans (LinearEquiv.neg (ZMod p))
    have hhn : ∀ v, hneg v = -(w v) := by
      intro v
      simp [hneg, LinearEquiv.trans_apply, LinearEquiv.neg_apply]
    have hnegc : ∀ f, ggContra hneg f = -(ggContra w f) := ggContra_neg w hneg hhn
    have heq : ggContra φ = ggContra hneg := by
      ext f x
      rw [h2 f, hnegc f, LinearMap.neg_apply, LinearMap.neg_apply,
        congrArg (fun θ : Dual (ZMod p) D.V => θ x)
          (congrArg (fun e : Dual (ZMod p) D.V ≃ₗ[ZMod p] Dual (ZMod p) D.V => e f) hwg)]
    intro v
    rw [congrArg (fun e : D.V ≃ₗ[ZMod p] D.V => e v) (ggContra_injective heq), hhn v]

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem exists_perp_natCard_isIsom_le [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : U}
    (hx : Q x ≠ 0) :
    ∃ W : Submodule (ZMod p) U, Module.finrank (ZMod p) W + 1 = Module.finrank (ZMod p) U ∧
      (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate ∧
      Nat.card {g : W ≃ₗ[ZMod p] W // IsIsom p (Q.comp W.subtype) g} ≤
        Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
          MulAction.stabilizer (U ≃ₗ[ZMod p] U) x) := by
  classical
  let B := QuadraticMap.polarBilin Q
  let W := LinearMap.BilinForm.orthogonal B ((ZMod p) ∙ x)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, QuadraticMap.map_zero])
  have hxx : B x x ≠ 0 := by
    show QuadraticMap.polar Q x x ≠ 0
    rw [QuadraticMap.polar_self]
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_ne_zero h2 hx
  have hsymm : B.IsSymm := ⟨fun a b => by
    show QuadraticMap.polar Q a b = QuadraticMap.polar Q b a
    exact QuadraticMap.polar_comm Q a b⟩
  have hcompl : IsCompl ((ZMod p) ∙ x) W :=
    LinearMap.BilinForm.isCompl_span_singleton_orthogonal hxx
  have hWnd : (LinearMap.BilinForm.restrict B W).Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hQ
      hsymm.isRefl hxx
  have hWpolar : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate := by
    have hEq : QuadraticMap.polarBilin (Q.comp W.subtype) = LinearMap.BilinForm.restrict B W := by
      rw [QuadraticMap.polarBilin_comp]
      ext u v
      rfl
    rwa [hEq]
  have hfin : Module.finrank (ZMod p) W + 1 = Module.finrank (ZMod p) U := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [finrank_span_singleton hx0] at h
    omega
  let e : (((ZMod p) ∙ x) × W) ≃ₗ[ZMod p] U :=
    Submodule.prodEquivOfIsCompl ((ZMod p) ∙ x) W hcompl
  let ext : (W ≃ₗ[ZMod p] W) → (U ≃ₗ[ZMod p] U) := fun h =>
    e.symm ≪≫ₗ (LinearEquiv.refl (ZMod p) ((ZMod p) ∙ x)).prodCongr h ≪≫ₗ e
  have ext_apply (h : W ≃ₗ[ZMod p] W) (c : (ZMod p) ∙ x) (w : W) :
      ext h (e (c, w)) = e (c, h w) := by
    simp [ext]
  have e_apply (c : (ZMod p) ∙ x) (w : W) : e (c, w) = (c : U) + (w : U) :=
    Submodule.coe_prodEquivOfIsCompl' (p := (ZMod p) ∙ x) (q := W) hcompl (c, w)
  have ext_isom (h : W ≃ₗ[ZMod p] W) (hh : IsIsom p (Q.comp W.subtype) h) :
      IsIsom p Q (ext h) := by
    intro v
    let c : (ZMod p) ∙ x := (e.symm v).1
    let w : W := (e.symm v).2
    have hve : v = e (c, w) := by
      rw [← e.apply_symm_apply v]
    have hgv : ext h v = (c : U) + (h w : U) := by
      rw [hve, ext_apply, e_apply]
    have hcw : QuadraticMap.polar Q (c : U) (w : U) = 0 := by
      simpa [B] using w.2 c c.2
    have hchw : QuadraticMap.polar Q (c : U) ((h w : W) : U) = 0 := by
      simpa [B] using (h w).2 c c.2
    calc
      Q (ext h v) = Q ((c : U) + (h w : U)) := by rw [hgv]
      _ = Q (c : U) + Q ((h w : W) : U) +
            QuadraticMap.polar Q (c : U) ((h w : W) : U) :=
        QuadraticMap.map_add Q _ _
      _ = Q (c : U) + Q (w : U) + 0 := by
        rw [hchw, show Q ((h w : W) : U) = Q (w : U) from hh w]
      _ = Q (c : U) + Q (w : U) + QuadraticMap.polar Q (c : U) (w : U) := by
        rw [hcw]
      _ = Q ((c : U) + (w : U)) := (QuadraticMap.map_add Q _ _).symm
      _ = Q v := by rw [hve, e_apply]
  have ext_fix (h : W ≃ₗ[ZMod p] W) : ext h x = x := by
    have hx_symm : e.symm x = (⟨x, Submodule.mem_span_singleton_self x⟩, 0) := by
      rw [LinearEquiv.symm_apply_eq, e_apply]
      simp
    change e ((LinearEquiv.refl (ZMod p) ((ZMod p) ∙ x)).prodCongr h (e.symm x)) = x
    rw [hx_symm]
    rw [show (LinearEquiv.refl (ZMod p) ((ZMod p) ∙ x)).prodCongr h
        (⟨x, Submodule.mem_span_singleton_self x⟩, 0) =
        (⟨x, Submodule.mem_span_singleton_self x⟩, h 0) from rfl]
    rw [e_apply]
    simp
  have ext_apply_w (h : W ≃ₗ[ZMod p] W) (w : W) : ext h (w : U) = (h w : U) := by
    have hw_symm : e.symm (w : U) = (0, w) := by
      rw [LinearEquiv.symm_apply_eq, e_apply]
      simp
    change e ((LinearEquiv.refl (ZMod p) ((ZMod p) ∙ x)).prodCongr h (e.symm (w : U))) =
      (h w : U)
    rw [hw_symm]
    rw [show (LinearEquiv.refl (ZMod p) ((ZMod p) ∙ x)).prodCongr h (0, w) = (0, h w) from rfl]
    rw [e_apply]
    simp
  let F : {g : W ≃ₗ[ZMod p] W // IsIsom p (Q.comp W.subtype) g} →
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        MulAction.stabilizer (U ≃ₗ[ZMod p] U) x) := fun g =>
    ⟨ext g.1, by
      refine ⟨?_, ?_⟩
      · change ext g.1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        exact ext_isom g.1 g.2
      · change ext g.1 ∈ MulAction.stabilizer (U ≃ₗ[ZMod p] U) x
        rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
        exact ext_fix g.1⟩
  have hF : Function.Injective F := by
    intro g₁ g₂ hg
    apply Subtype.ext
    ext w
    have h1 := congrArg (fun k => (k.1 : U ≃ₗ[ZMod p] U) (w : U)) hg
    have h2 : ((g₁.1 w : W) : U) = ((g₂.1 w : W) : U) := by
      simpa [F, ext_apply_w g₁.1 w, ext_apply_w g₂.1 w] using h1
    exact h2
  refine ⟨W, hfin, hWpolar, ?_⟩
  haveI : Finite (U ≃ₗ[ZMod p] U) := by
    haveI : Finite (U →ₗ[ZMod p] U) := Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U))
      fun _ _ h => LinearEquiv.ext fun x => congrArg (fun g : U →ₗ[ZMod p] U => g x) h
  exact Nat.card_le_card_of_injective F hF

private lemma natCard_stabilizer_orthogonalGroup_eq (Q : QuadraticForm (ZMod p) U) (x : U) :
    Nat.card ↥(MulAction.stabilizer ↥(TauCeti.QuadraticMap.orthogonalGroup Q) x) =
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        MulAction.stabilizer (U ≃ₗ[ZMod p] U) x) := by
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let S := O ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) x
  change Nat.card ↥(MulAction.stabilizer ↥O x) = Nat.card ↥S
  refine Nat.card_congr ?_
  refine
    { toFun := fun g => ⟨(g.1 : U ≃ₗ[ZMod p] U), ?_⟩
      invFun := fun g => ⟨⟨(g.1 : U ≃ₗ[ZMod p] U), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨g.1.2, ?_⟩
    change (g.1 : U ≃ₗ[ZMod p] U) • x = x
    simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using
      MulAction.mem_stabilizer_iff.mp g.2
  · exact g.2.1
  · change (⟨(g.1 : U ≃ₗ[ZMod p] U), g.2.1⟩ : ↥O) • x = x
    simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using
      MulAction.mem_stabilizer_iff.mp g.2.2
  · intro g
    rfl
  · intro g
    rfl

theorem natCard_orthogonalGroup_le_mul [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) {x : U} (hx : x ≠ 0) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ≤
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
          MulAction.stabilizer (U ≃ₗ[ZMod p] U) x) *
        Nat.card {v : U // v ≠ 0 ∧ Q v = Q x} := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let S := O ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) x
  change Nat.card ↥O ≤ Nat.card ↥S * Nat.card {v : U // v ≠ 0 ∧ Q v = Q x}
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  haveI : Finite (U ≃ₗ[ZMod p] U) := by
    haveI : Finite (U →ₗ[ZMod p] U) := Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U))
      fun _ _ h => LinearEquiv.ext fun x => congrArg (fun g : U →ₗ[ZMod p] U => g x) h
  have hstab := natCard_stabilizer_orthogonalGroup_eq Q x
  have hcard : Nat.card ↥O = Nat.card (MulAction.orbit ↥O x) * Nat.card ↥S := by
    rw [← hstab]
    haveI : Fintype ↥O := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit ↥O x) := Fintype.ofFinite _
    haveI : Fintype ↥(MulAction.stabilizer ↥O x) := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥O) (X := U) x).symm
  let f : MulAction.orbit ↥O x → {v : U // v ≠ 0 ∧ Q v = Q x} := fun v =>
    ⟨v.1, by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp v.2
      have hg' : (g : U ≃ₗ[ZMod p] U) x = v.1 := by
        simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hg
      rw [← hg']
      exact fun h => hx (by
        have h' : (g : U ≃ₗ[ZMod p] U) x = 0 := h
        exact (g : U ≃ₗ[ZMod p] U).injective (by simpa using h')),
     by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp v.2
      have hg' : (g : U ≃ₗ[ZMod p] U) x = v.1 := by
        simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hg
      rw [← hg']
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 x⟩
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : {v : U // v ≠ 0 ∧ Q v = Q x} => z.1) h)
  calc
    Nat.card ↥O = Nat.card (MulAction.orbit ↥O x) * Nat.card ↥S := hcard
    _ ≤ Nat.card {v : U // v ≠ 0 ∧ Q v = Q x} * Nat.card ↥S :=
      Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)
    _ = Nat.card ↥S * Nat.card {v : U // v ≠ 0 ∧ Q v = Q x} := Nat.mul_comm _ _

theorem two_mul_natCard_stabilizer_dvd [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (Q : QuadraticForm (ZMod p) U) {x : U} (hx : x ≠ 0) :
    2 * Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        MulAction.stabilizer (U ≃ₗ[ZMod p] U) x) ∣
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let S := O ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) x
  let n : U ≃ₗ[ZMod p] U := LinearEquiv.neg (ZMod p)
  change 2 * Nat.card ↥S ∣ Nat.card ↥O
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  haveI : Finite (U ≃ₗ[ZMod p] U) := by
    haveI : Finite (U →ₗ[ZMod p] U) := Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U))
      fun _ _ h => LinearEquiv.ext fun x => congrArg (fun g : U →ₗ[ZMod p] U => g x) h
  haveI : Fintype (MulAction.orbit ↥O x) := Fintype.ofFinite _
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hnO : n ∈ O := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    simp [n, LinearEquiv.neg_apply]
  have hn2 : n * n = 1 := by
    ext v
    simp [n]
  have hcard : Nat.card ↥O = Nat.card (MulAction.orbit ↥O x) * Nat.card ↥S := by
    rw [← natCard_stabilizer_orthogonalGroup_eq Q x]
    haveI : Fintype ↥O := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit ↥O x) := Fintype.ofFinite _
    haveI : Fintype ↥(MulAction.stabilizer ↥O x) := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥O) (X := U) x).symm
  have hX : ∀ v : MulAction.orbit ↥O x, (v : U) ≠ 0 := by
    intro v hv
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp v.2
    have hg' : (g : U ≃ₗ[ZMod p] U) x = v.1 := by
      simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hg
    rw [← hg'] at hv
    exact hx ((g : U ≃ₗ[ZMod p] U).injective (by simpa using hv))
  let τ : MulAction.orbit ↥O x → MulAction.orbit ↥O x := fun v =>
    ⟨n • (v : U), by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp v.2
      have hg' : (g : U ≃ₗ[ZMod p] U) x = v.1 := by
        simpa [MulAction.subgroup_smul_def, LinearEquiv.smul_def] using hg
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨n * g, mul_mem hnO g.2⟩, ?_⟩
      rw [MulAction.subgroup_smul_def, mul_smul]
      change n • ((g : U ≃ₗ[ZMod p] U) x) = n • (v : U)
      rw [hg']⟩
  have hτ : Function.Involutive τ := by
    intro v
    apply Subtype.ext
    change n • (n • (v : U)) = (v : U)
    rw [smul_smul, hn2]
    simp
  have heven : 2 ∣ Nat.card (MulAction.orbit ↥O x) := by
    have h2supp : 2 ∣ (hτ.toPerm τ).support.card := by
      refine Equiv.Perm.two_dvd_card_support ?_
      ext v
      exact congrArg Subtype.val (hτ v)
    have hsupp : (hτ.toPerm τ).support = Finset.univ := by
      ext v
      simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
      intro hv
      apply hX v
      have hv' : n • (v : U) = (v : U) := congrArg Subtype.val hv
      have hneg : -(v : U) = (v : U) := by
        simpa [n, LinearEquiv.neg_apply] using hv'
      have h2smul : (2 : ZMod p) • (v : U) = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← hneg]
        exact neg_add_cancel _
      exact (smul_eq_zero.mp h2smul).resolve_left h2
    simpa [hsupp, Nat.card_eq_fintype_card] using h2supp
  rw [hcard]
  exact mul_dvd_mul_right heven (Nat.card ↥S)

private lemma natCard_singular_smul {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (Q : QuadraticForm (ZMod p) V) {d : ZMod p} (hd : d ≠ 0) :
    Nat.card {v : V // (d • Q) v = 0} = Nat.card {v : V // Q v = 0} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl V) ?_)
  intro v
  change d • Q v = 0 ↔ Q v = 0
  rw [smul_eq_mul, mul_eq_zero]
  simp [hd]

private lemma natCard_singular_eq_of_isometry {V V' : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    {Q : QuadraticForm (ZMod p) V} {Q' : QuadraticForm (ZMod p) V'}
    (e : Q.IsometryEquiv Q') :
    Nat.card {v : V // Q v = 0} = Nat.card {v : V' // Q' v = 0} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun v => ⟨e v.1, by rw [e.map_app, v.2]⟩
      invFun := fun w => ⟨e.symm w.1, ?_⟩
      left_inv := fun v => Subtype.ext (e.toLinearEquiv.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (e.toLinearEquiv.apply_symm_apply w.1) }
  have h := e.map_app (e.symm w.1)
  have h' : e (e.symm w.1) = w.1 := e.toLinearEquiv.apply_symm_apply w.1
  rw [h', w.2] at h
  exact h.symm

private lemma natCard_nonzero_singular_add_one {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (Q : QuadraticForm (ZMod p) V) :
    Nat.card {v : V // v ≠ 0 ∧ Q v = 0} + 1 = Nat.card {v : V // Q v = 0} := by
  classical
  let z : {v : V // Q v = 0} := ⟨0, QuadraticMap.map_zero Q⟩
  let f : Option {v : V // v ≠ 0 ∧ Q v = 0} → {v : V // Q v = 0}
    | none => z
    | some a => ⟨a.1, a.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (_ | a) (_ | b) h
      · rfl
      · have h0 : (0 : V) = b.1 := congrArg (fun z : {v : V // Q v = 0} => z.1) h
        exact absurd h0.symm b.2.1
      · have h0 : a.1 = (0 : V) := congrArg (fun z : {v : V // Q v = 0} => z.1) h
        exact absurd h0 a.2.1
      · have hab : a.1 = b.1 := congrArg (fun z : {v : V // Q v = 0} => z.1) h
        exact congrArg some (Subtype.ext hab)
    · rintro ⟨v, hv⟩
      by_cases h0 : v = 0
      · exact ⟨none, Subtype.ext h0.symm⟩
      · exact ⟨some ⟨v, h0, hv⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hcard, Finite.card_option]

theorem natCard_singular_of_finrank_eq_odd [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn : Module.finrank (ZMod p) U = 2 * n + 1) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nat.card {v : U // v ≠ 0 ∧ Q v = 0} = p ^ (2 * n) - 1 := by
  classical
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  have h2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  obtain ⟨d, hd, ⟨e⟩⟩ :=
    CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd (K := ZMod p) h2 Q hQ hn
  have hquad : Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → ZMod p //
      CFSG.LieType.Universal.Spin.quadOdd n (ZMod p) v = 0} = p ^ (2 * n) := by
    have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have h := CFSG.ClassicalInvolution.card_singular_quadOdd_of_two_ne_zero
      (K := ZMod p) h2' n
    rw [Nat.card_zmod] at h
    have hcast : ((Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → ZMod p //
        CFSG.LieType.Universal.Spin.quadOdd n (ZMod p) v = 0} : ℕ) : ℤ) =
        ((p ^ (2 * n) : ℕ) : ℤ) := by
      push_cast
      exact h
    exact_mod_cast hcast
  have hBQ : Nat.card {v : U // Q v = 0} =
      Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → ZMod p //
        CFSG.LieType.Universal.Spin.quadOdd n (ZMod p) v = 0} := by
    calc
      Nat.card {v : U // Q v = 0} = Nat.card {v : U // (d • Q) v = 0} :=
        (natCard_singular_smul Q hd).symm
      _ = Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → ZMod p //
            CFSG.LieType.Universal.Spin.quadOdd n (ZMod p) v = 0} :=
        natCard_singular_eq_of_isometry e
  have hN : Nat.card {v : U // v ≠ 0 ∧ Q v = 0} + 1 = p ^ (2 * n) := by
    rw [natCard_nonzero_singular_add_one Q, hBQ, hquad]
  have hpos : 1 ≤ p ^ (2 * n) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  omega

theorem natCard_singular_of_isPlusType [Module.Finite (ZMod p) U] {n : ℕ} (hn1 : 1 ≤ n)
    (hn : Module.finrank (ZMod p) U = 2 * n) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card {v : U // v ≠ 0 ∧ Q v = 0} = (p ^ n - 1) * (p ^ (n - 1) + 1) := by
  classical
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsub : (m + 1) - 1 = m := by omega
  rw [hsub]
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
    (K := ZMod p) (n := m + 1) hQ hn hplus
  have hquad : Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → ZMod p //
      CFSG.LieType.Universal.Spin.quadPlus (m + 1) (ZMod p) v = 0} =
      1 + (p ^ (m + 1) - 1) * (p ^ m + 1) := by
    have h := CFSG.ClassicalInvolution.card_singular_quadPlus (K := ZMod p) m
    rw [Nat.card_zmod] at h
    have hcast : ((Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → ZMod p //
        CFSG.LieType.Universal.Spin.quadPlus (m + 1) (ZMod p) v = 0} : ℕ) : ℤ) =
        ((1 + (p ^ (m + 1) - 1) * (p ^ m + 1) : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub
        (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), Nat.cast_add, Nat.cast_one,
        Nat.cast_pow, Nat.cast_pow]
      exact h
    exact_mod_cast hcast
  have hBQ : Nat.card {v : U // Q v = 0} =
      Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → ZMod p //
        CFSG.LieType.Universal.Spin.quadPlus (m + 1) (ZMod p) v = 0} :=
    natCard_singular_eq_of_isometry e
  have hN : Nat.card {v : U // v ≠ 0 ∧ Q v = 0} + 1 =
      1 + (p ^ (m + 1) - 1) * (p ^ m + 1) := by
    rw [natCard_nonzero_singular_add_one Q, hBQ, hquad]
  omega

theorem natCard_singular_of_not_isPlusType [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : Module.finrank (ZMod p) U = 2 * n) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card {v : U // v ≠ 0 ∧ Q v = 0} = (p ^ n + 1) * (p ^ (n - 1) - 1) := by
  classical
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsub : (m + 1) - 1 = m := by omega
  rw [hsub]
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
    (K := ZMod p) Q hQ (by omega : 1 ≤ m + 1) hn with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
  · exfalso
    exact hminus (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv e.symm
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (K := ZMod p) (m + 1)))
  · have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hquad : Nat.card {v : Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 → ZMod p //
        CFSG.LieType.Universal.Spin.quadMinus (m + 1) (ZMod p) b c v = 0} =
        1 + (p ^ (m + 1) + 1) * (p ^ m - 1) := by
      have h := CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero
        (K := ZMod p) h2' hirr m
      rw [Nat.card_zmod] at h
      have hcast : ((Nat.card {v : Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 →
          ZMod p // CFSG.LieType.Universal.Spin.quadMinus (m + 1) (ZMod p) b c v = 0} : ℕ) :
          ℤ) = ((1 + (p ^ (m + 1) + 1) * (p ^ m - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos),
          Nat.cast_pow, Nat.cast_pow]
        exact h
      exact_mod_cast hcast
    have hBQ : Nat.card {v : U // Q v = 0} =
        Nat.card {v : Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 → ZMod p //
          CFSG.LieType.Universal.Spin.quadMinus (m + 1) (ZMod p) b c v = 0} :=
      natCard_singular_eq_of_isometry e
    have hN : Nat.card {v : U // v ≠ 0 ∧ Q v = 0} + 1 =
        1 + (p ^ (m + 1) + 1) * (p ^ m - 1) := by
      rw [natCard_nonzero_singular_add_one Q, hBQ, hquad]
    omega

theorem natCard_inf_le_two_mul {G : Type*} [Group G] {O A : Subgroup G} [Finite ↥O]
    (hAO : A ≤ O) (h : ∀ g ∈ O, ∀ g' ∈ O, g ∉ A → g' ∉ A → g⁻¹ * g' ∈ A) (S : Subgroup G) :
    Nat.card ↥(O ⊓ S) ≤ 2 * Nat.card ↥(A ⊓ S) := by
  classical
  haveI : Finite ↥(A ⊓ S) := by
    refine Finite.of_injective
      (fun x : ↥(A ⊓ S) => (⟨x.1, hAO x.2.1⟩ : ↥O)) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥O => (z : G)) hxy
  by_cases hle : O ⊓ S ≤ A
  · have hEq : O ⊓ S = A ⊓ S := by
      refine le_antisymm ?_ ?_
      · intro x hx
        exact ⟨hle hx, hx.2⟩
      · intro x hx
        exact ⟨hAO hx.1, hx.2⟩
    rw [hEq]
    omega
  · obtain ⟨g0, hg0OS, hg0A⟩ := Set.not_subset.mp hle
    have hg0O : g0 ∈ O := hg0OS.1
    have hg0S : g0 ∈ S := hg0OS.2
    let f : ↥(O ⊓ S) → ↥(A ⊓ S) ⊕ ↥(A ⊓ S) := fun y =>
      if hy : y.1 ∈ A then
        Sum.inl ⟨y.1, ⟨hy, y.2.2⟩⟩
      else
        Sum.inr ⟨g0⁻¹ * y.1, ⟨h g0 hg0O y.1 y.2.1 hg0A hy,
          S.mul_mem (S.inv_mem hg0S) y.2.2⟩⟩
    have hf : Function.Injective f := by
      intro y y' hyy'
      by_cases hyA : y.1 ∈ A <;> by_cases hyA' : y'.1 ∈ A
      · have hyy'' : (Sum.inl (⟨y.1, ⟨hyA, y.2.2⟩⟩ : ↥(A ⊓ S)) :
            ↥(A ⊓ S) ⊕ ↥(A ⊓ S)) = Sum.inl ⟨y'.1, ⟨hyA', y'.2.2⟩⟩ := by
          simpa [f, hyA, hyA'] using hyy'
        have hEq : (⟨y.1, ⟨hyA, y.2.2⟩⟩ : ↥(A ⊓ S)) =
            ⟨y'.1, ⟨hyA', y'.2.2⟩⟩ :=
          Sum.inl_injective (α := ↥(A ⊓ S)) (β := ↥(A ⊓ S)) hyy''
        exact Subtype.ext (congrArg (fun z : ↥(A ⊓ S) => (z : G)) hEq)
      · exact (by simpa [f, hyA, hyA'] using hyy' : False).elim
      · exact (by simpa [f, hyA, hyA'] using hyy' : False).elim
      · have hyy'' : (Sum.inr (⟨g0⁻¹ * y.1, ⟨h g0 hg0O y.1 y.2.1 hg0A hyA,
              S.mul_mem (S.inv_mem hg0S) y.2.2⟩⟩ : ↥(A ⊓ S)) :
            ↥(A ⊓ S) ⊕ ↥(A ⊓ S)) = Sum.inr ⟨g0⁻¹ * y'.1,
              ⟨h g0 hg0O y'.1 y'.2.1 hg0A hyA', S.mul_mem (S.inv_mem hg0S) y'.2.2⟩⟩ := by
          simpa [f, hyA, hyA'] using hyy'
        have hEq : (⟨g0⁻¹ * y.1, ⟨h g0 hg0O y.1 y.2.1 hg0A hyA,
              S.mul_mem (S.inv_mem hg0S) y.2.2⟩⟩ : ↥(A ⊓ S)) =
            ⟨g0⁻¹ * y'.1, ⟨h g0 hg0O y'.1 y'.2.1 hg0A hyA',
              S.mul_mem (S.inv_mem hg0S) y'.2.2⟩⟩ :=
          Sum.inr_injective (α := ↥(A ⊓ S)) (β := ↥(A ⊓ S)) hyy''
        have hmul : g0⁻¹ * y.1 = g0⁻¹ * y'.1 :=
          congrArg (fun z : ↥(A ⊓ S) => (z : G)) hEq
        exact Subtype.ext (mul_left_cancel hmul)
    calc
      Nat.card ↥(O ⊓ S) ≤ Nat.card (↥(A ⊓ S) ⊕ ↥(A ⊓ S)) :=
        Nat.card_le_card_of_injective f hf
      _ = Nat.card ↥(A ⊓ S) + Nat.card ↥(A ⊓ S) := Nat.card_sum
      _ = 2 * Nat.card ↥(A ⊓ S) := by omega

end CFSG.StandardType.ZS

end

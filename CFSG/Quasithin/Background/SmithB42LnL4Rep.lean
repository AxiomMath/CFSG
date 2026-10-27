module

public import CFSG.Quasithin.Background.SmithB42LnL4Gen
public import CFSG.Quasithin.Background.SmithB42LnL5Rep
public import CFSG.Quasithin.Background.SmithB42LnBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.SmithB42LnL5Curtis
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.Assembly.LowTwoRank

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

noncomputable abbrev E4 : G4 ≃* ↥(StatedSL 4 (ZMod 2)) := specialLinearGroupEquivStatedSL 4 (ZMod 2)

theorem coe_E4_symm (y : ↥(StatedSL 4 (ZMod 2))) : ((E4.symm y : G4) : 𝕄₄) = B5.Ln.mat y := by
  conv_rhs => rw [← E4.apply_symm_apply y]
  rfl

theorem det_eq_one_GL4 (M : GL (Fin 4) (ZMod 2)) : (M : 𝕄₄).det = 1 := by
  have hu : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact hu _

@[expose] def ofGL4 (M : GL (Fin 4) (ZMod 2)) : G4 := ⟨M, det_eq_one_GL4 M⟩

theorem GL4_mul_inv (M : GL (Fin 4) (ZMod 2)) :
    (M : 𝕄₄) * ((M⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem GL4_inv_mul (M : GL (Fin 4) (ZMod 2)) :
    ((M⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) * (M : 𝕄₄) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem ofGL4_inv (M : GL (Fin 4) (ZMod 2)) : (ofGL4 M)⁻¹ = ofGL4 M⁻¹ :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (GL4_mul_inv M))

variable {V : Type} [CommGroup V] {G L A : Subgroup (MulAut V)}

noncomputable abbrev phiOf4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : ↥L ≃* G4 := e.trans E4.symm

theorem phiOf4_symm_apply (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (x : G4) :
    (phiOf4 e).symm x = e.symm (E4 x) := by
  simp [phiOf4]

noncomputable abbrev fL4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : G4 →* MulAut V :=
  L.subtype.comp (phiOf4 e).symm.toMonoidHom

theorem fL4_apply (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (g : G4) :
    fL4 e g = (((phiOf4 e).symm g : ↥L) : MulAut V) := rfl

theorem fL4_injective (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : Function.Injective (fL4 e) :=
  fun _ _ h => (phiOf4 e).symm.injective (Subtype.ext h)

theorem fL4_mem (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (g : G4) : fL4 e g ∈ L :=
  ((phiOf4 e).symm g).2

theorem fL4_phiOf (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {x : MulAut V} (hx : x ∈ L) :
    fL4 e (phiOf4 e ⟨x, hx⟩) = x := by
  rw [fL4_apply, MulEquiv.symm_apply_apply]

theorem exists_fL4_eq (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {x : MulAut V} (hx : x ∈ L) :
    ∃ g, fL4 e g = x :=
  ⟨phiOf4 e ⟨x, hx⟩, fL4_phiOf e hx⟩

theorem card_comap4_eq (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hAL : A ≤ L) :
    Nat.card (A.comap (fL4 e)) = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨fL4 e g, g.2⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h' : fL4 e g = fL4 e g' := congrArg (fun z : ↥A => (z : MulAut V)) h
    exact Subtype.ext (fL4_injective e h')
  · rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := exists_fL4_eq e (hAL hx)
    exact ⟨⟨g, hx⟩, rfl⟩

theorem comm_of_comap4 {e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))} (hA : IsElemAbelian2 A) :
    ∀ a ∈ A.comap (fL4 e), ∀ b ∈ A.comap (fL4 e), a * b = b * a := by
  intro a ha b hb
  apply fL4_injective e
  rw [map_mul, map_mul]
  exact hA.1 _ ha _ hb

theorem sq_of_comap4 {e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))} (hA : IsElemAbelian2 A) :
    ∀ a ∈ A.comap (fL4 e), a * a = 1 := by
  intro a ha
  apply fL4_injective e
  rw [map_mul, map_one, ← pow_two]
  exact hA.2 _ ha

theorem x4_mul_y4_ne : x4 0 * y4 0 ≠ y4 0 * x4 0 := by
  intro h
  have h1 := congrArg (fun g : G4 => (g : 𝕄₄) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_x4, coe_y4] at h1
  revert h1
  decide

theorem exists_not_comm4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : ∃ a b : ↥L, a * b ≠ b * a :=
  ⟨(phiOf4 e).symm (x4 0), (phiOf4 e).symm (y4 0), fun h =>
    x4_mul_y4_ne ((phiOf4 e).symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem nontrivial_of_equiv4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨a, b, hab⟩ := exists_not_comm4 e
  exact hab (Subtype.ext (MulEquiv.ext fun v => Subsingleton.elim _ _))

section Rep

variable [Module (ZMod 2) (Additive V)]

noncomputable abbrev repOf4 (φ : ↥L ≃* G4) : Representation (ZMod 2) G4 (Additive V) :=
  JonesParshall.repOfEnd (mulAutAdd.comp (L.subtype.comp φ.symm.toMonoidHom))

theorem repOf4_apply (φ : ↥L ≃* G4) (g : G4) (v : V) :
    repOf4 φ g (Additive.ofMul v) = Additive.ofMul (((φ.symm g : ↥L) : MulAut V) v) := rfl

theorem repOf4_apply_iso (φ : ↥L ≃* G4) (h : ↥L) (v : V) :
    repOf4 φ (φ h) (Additive.ofMul v) = Additive.ofMul ((h : MulAut V) v) := by
  rw [repOf4_apply, MulEquiv.symm_apply_apply]

theorem isSimpleRep_repOf4 [Nontrivial V] (φ : ↥L ≃* G4)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ L, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    SmithCurtis.IsSimpleRep (repOf4 φ) := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  let W' : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ W}
      mul_mem' := fun ha hb => W.add_mem ha hb
      one_mem' := W.zero_mem
      inv_mem' := fun ha => W.neg_mem ha }
  have hinv : ∀ h ∈ L, ∀ w ∈ W', (h : MulAut V) w ∈ W' := by
    intro h hh w hw
    have := hW (φ ⟨h, hh⟩) (Additive.ofMul w) hw
    rw [repOf4_apply_iso] at this
    exact this
  rcases hirr W' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : Additive.toMul x ∈ W' := hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hx'
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : Additive.toMul x ∈ W' := h ▸ Subgroup.mem_top _
    exact hx'

theorem not_trivial4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (h : ∀ g w, repOf4 (phiOf4 e) g w = w) : False := by
  have h1 : ∀ g : G4, fL4 e g = 1 := fun g => MulEquiv.ext fun v => by
    have := h g (Additive.ofMul v)
    rw [repOf4_apply] at this
    exact Additive.ofMul.injective this
  apply x4_mul_y4_ne
  apply fL4_injective e
  rw [map_mul, map_mul, h1, h1]

end Rep

variable [Finite V]

@[expose] noncomputable def conjG4_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    {g : MulAut V} (hg : g ∈ G) : G4 ≃* G4 :=
  (E4.trans (conjAut_core h e hg)).trans E4.symm

@[expose] noncomputable def conjG4 (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    {g : MulAut V} (hg : g ∈ G) : G4 ≃* G4 :=
  conjG4_core h.core e hg

theorem E4_conjG4_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G4) : E4 (conjG4_core h e hg x) = conjAut_core h e hg (E4 x) := by
  simp [conjG4_core]

theorem conjG4_spec_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G4) :
    (((phiOf4 e).symm (conjG4_core h e hg x) : ↥L) : MulAut V) =
      g * (((phiOf4 e).symm x : ↥L) : MulAut V) * g⁻¹ := by
  rw [phiOf4_symm_apply, phiOf4_symm_apply, E4_conjG4_core, conjAut_spec_core]

theorem conjG4_spec (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G4) :
    (((phiOf4 e).symm (conjG4 h e hg x) : ↥L) : MulAut V) =
      g * (((phiOf4 e).symm x : ↥L) : MulAut V) * g⁻¹ :=
  conjG4_spec_core h.core e hg x

theorem coe_conjG4_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G4) :
    ((conjG4_core h e hg x : G4) : 𝕄₄) = B5.Ln.mat (conjAut_core h e hg (E4 x)) := by
  rw [← E4_conjG4_core]
  rfl

theorem exists_conjG4_eq_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (hgL : g ∉ L) :
    ∃ P : GL (Fin 4) (ZMod 2), ∀ x : G4, ((conjG4_core h e hg x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) := by
  obtain ⟨P, hP⟩ := outer_of_not_mem_core h hZ (by norm_num) e hg hgL
  refine ⟨P, fun x => ?_⟩
  rw [coe_conjG4_core, hP, B5.Ln.dmat, ← map_inv]
  rfl

theorem exists_conjG4_eq (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (hgL : g ∉ L) :
    ∃ P : GL (Fin 4) (ZMod 2), ∀ x : G4, ((conjG4 h e hg x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) :=
  exists_conjG4_eq_core h.core hZ e hg hgL

theorem mem_of_conjG4_eq_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (M : GL (Fin 4) (ZMod 2))
    (hM : ∀ x : G4, ((conjG4_core h e hg x : G4) : 𝕄₄) =
      (M : 𝕄₄) * (x : 𝕄₄) * ((M⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) : g ∈ L := by
  set m : G4 := ofGL4 M
  have hm : ∀ x : G4, conjG4_core h e hg x = m * x * m⁻¹ := fun x => by
    apply Subtype.ext
    rw [hM, ofGL4_inv]
    rfl
  refine mem_of_inner_core h hZ hg ((phiOf4 e).symm m).2 fun x hx => ?_
  obtain ⟨y, hy⟩ := (phiOf4 e).symm.surjective ⟨x, hx⟩
  have hx' : x = (((phiOf4 e).symm y : ↥L) : MulAut V) := by rw [hy]
  rw [hx', ← conjG4_spec_core h e hg y, hm y, map_mul, map_mul, map_inv]
  rfl

theorem mul_mem_of_not_mem4_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g₁ g₂ : MulAut V} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G)
    (h₁ : g₁ ∉ L) (h₂ : g₂ ∉ L) : g₁ * g₂ ∈ L := by
  obtain ⟨P₁, hP₁⟩ := exists_conjG4_eq_core h hZ e hg₁ h₁
  obtain ⟨P₂, hP₂⟩ := exists_conjG4_eq_core h hZ e hg₂ h₂
  have hcomp : ∀ x, conjG4_core h e (G.mul_mem hg₁ hg₂) x =
      conjG4_core h e hg₁ (conjG4_core h e hg₂ x) := by
    intro x
    apply (phiOf4 e).symm.injective
    apply Subtype.ext
    rw [conjG4_spec_core, conjG4_spec_core, conjG4_spec_core]
    group
  refine mem_of_conjG4_eq_core h hZ e (G.mul_mem hg₁ hg₂) (P₁ * B5.Ln.invT P₂) fun x => ?_
  rw [hcomp, hP₁, ← map_inv, hP₂, inv_inv]
  have e1 : ((P₁ * B5.Ln.invT P₂ : GL (Fin 4) (ZMod 2)) : 𝕄₄) =
      (P₁ : 𝕄₄) * ((P₂⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)ᵀ := rfl
  have e2 : (((P₁ * B5.Ln.invT P₂)⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) =
      (P₂ : 𝕄₄)ᵀ * ((P₁⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) := rfl
  rw [e1, e2, transpose_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem transpose_P4_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (hg2 : g * g = 1) {P : GL (Fin 4) (ZMod 2)}
    (hP : ∀ x : G4, ((conjG4_core h e hg x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) :
    (P : 𝕄₄)ᵀ = P := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hinv : ∀ x, conjG4_core h e hg (conjG4_core h e hg x) = x := by
    intro x
    apply (phiOf4 e).symm.injective
    apply Subtype.ext
    rw [conjG4_spec_core, conjG4_spec_core, hginv]
    calc g * (g * (((phiOf4 e).symm x : ↥L) : MulAut V) * g) * g =
        (g * g) * (((phiOf4 e).symm x : ↥L) : MulAut V) * (g * g) := by group
      _ = (((phiOf4 e).symm x : ↥L) : MulAut V) := by rw [hg2, one_mul, mul_one]
  set p : 𝕄₄ := (P : 𝕄₄) with hp
  set q : 𝕄₄ := ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) with hq
  have hqp : q * p = 1 := GL4_inv_mul P
  have hN : ∀ x : G4, p * qᵀ * (x : 𝕄₄) = (x : 𝕄₄) * (p * qᵀ) := by
    intro x
    have h1 : ((conjG4_core h e hg (conjG4_core h e hg x) : G4) : 𝕄₄) = (x : 𝕄₄) := by
      rw [hinv x]
    rw [hP, ← map_inv, hP, inv_inv, transpose_mul, transpose_mul, transpose_transpose] at h1
    conv_rhs => rw [← h1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc q p, hqp, Matrix.one_mul, ← transpose_mul, hqp, transpose_one,
      Matrix.mul_one]
  have hN1 : P * B5.Ln.invT P = 1 := by
    have h1 := B5.Ln.eq_one_of_forall_commute (n := 4) (z := B5.Ln.ofGL (P * B5.Ln.invT P))
      fun γ => by
        apply B5.Ln.mat_injective
        rw [B5.Ln.mat_mul, B5.Ln.mat_mul, B5.Ln.mat_ofGL, ← coe_E4_symm γ]
        exact hN (E4.symm γ)
    have h2 := congrArg B5.Ln.mat h1
    rw [B5.Ln.mat_ofGL, B5.Ln.mat_one] at h2
    exact Units.ext h2
  have h3 : p * qᵀ = 1 := congrArg (fun M : GL (Fin 4) (ZMod 2) => (M : 𝕄₄)) hN1
  have h4 : qᵀ * p = 1 := (mul_eq_one_comm_of_card_eq (Fin 4) (Fin 4) (ZMod 2) rfl).mp h3
  calc pᵀ = pᵀ * (qᵀ * p) := by rw [h4, Matrix.mul_one]
    _ = (q * p)ᵀ * p := by rw [transpose_mul, Matrix.mul_assoc]
    _ = p := by rw [hqp, transpose_one, Matrix.one_mul]

theorem transpose_P4 (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (hg2 : g * g = 1) {P : GL (Fin 4) (ZMod 2)}
    (hP : ∀ x : G4, ((conjG4 h e hg x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) :
    (P : 𝕄₄)ᵀ = P :=
  transpose_P4_core h.core e hg hg2 hP

theorem card_le_two_mul_comap4_core (hHyp : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hAG : A ≤ G) :
    Nat.card A ≤ 2 * Nat.card (A.comap (fL4 e)) := by
  classical
  by_cases hAL : A ≤ L
  · rw [card_comap4_eq e hAL]
    omega
  · obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    have ha₀L' : a₀⁻¹ ∉ L := fun h => ha₀L (by simpa using L.inv_mem h)
    have key : ∀ x : ↥A, (x : MulAut V) ∉ L → a₀⁻¹ * x ∈ L := fun x hx =>
      mul_mem_of_not_mem4_core hHyp hZ e (G.inv_mem (hAG ha₀)) (hAG x.2) ha₀L' hx
    have hm1 : ∀ (x : ↥A) (hx : (x : MulAut V) ∈ L), phiOf4 e ⟨x, hx⟩ ∈ A.comap (fL4 e) :=
      fun x hx => by
        show fL4 e (phiOf4 e ⟨x, hx⟩) ∈ A
        rw [fL4_phiOf]
        exact x.2
    have hm2 : ∀ (x : ↥A) (hx : (x : MulAut V) ∉ L),
        phiOf4 e ⟨a₀⁻¹ * x, key x hx⟩ ∈ A.comap (fL4 e) := fun x hx => by
      show fL4 e (phiOf4 e ⟨a₀⁻¹ * x, key x hx⟩) ∈ A
      rw [fL4_phiOf]
      exact A.mul_mem (A.inv_mem ha₀) x.2
    let F : ↥A → ↥(A.comap (fL4 e)) × Bool := fun x =>
      if hx : (x : MulAut V) ∈ L then (⟨phiOf4 e ⟨x, hx⟩, hm1 x hx⟩, false)
      else (⟨phiOf4 e ⟨a₀⁻¹ * x, key x hx⟩, hm2 x hx⟩, true)
    have hF : Function.Injective F := by
      intro x y hxy
      by_cases hx : (x : MulAut V) ∈ L <;> by_cases hy : (y : MulAut V) ∈ L
      · simp only [F, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have h1 := (phiOf4 e).injective
          (congrArg (fun z : ↥(A.comap (fL4 e)) => (z : G4)) hxy.1)
        exact Subtype.ext (congrArg (fun z : ↥L => (z : MulAut V)) h1)
      · simp [F, hx, hy] at hxy
      · simp [F, hx, hy] at hxy
      · simp only [F, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have h1 := congrArg (fun z : ↥L => (z : MulAut V)) ((phiOf4 e).injective
          (congrArg (fun z : ↥(A.comap (fL4 e)) => (z : G4)) hxy.1))
        exact Subtype.ext (mul_left_cancel h1)
    have : Finite ↥(A.comap (fL4 e)) := Finite.of_injective _ (Subtype.val_injective)
    have h := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
    linarith

theorem card_le_two_mul_comap4 (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hAG : A ≤ G) :
    Nat.card A ≤ 2 * Nat.card (A.comap (fL4 e)) :=
  card_le_two_mul_comap4_core hHyp.core hZ e hAG

theorem conjG4_fix_core (hHyp : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hA : IsElemAbelian2 A) {a : MulAut V} (haA : a ∈ A) (haG : a ∈ G) :
    ∀ b ∈ A.comap (fL4 e), conjG4_core hHyp e haG b = b := by
  intro b hb
  apply (phiOf4 e).symm.injective
  apply Subtype.ext
  rw [conjG4_spec_core, ← fL4_apply, hA.1 a haA _ hb, mul_inv_cancel_right]

theorem conjG4_fix (hHyp : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hA : IsElemAbelian2 A) {a : MulAut V} (haA : a ∈ A) (haG : a ∈ G) :
    ∀ b ∈ A.comap (fL4 e), conjG4 hHyp e haG b = b :=
  conjG4_fix_core hHyp.core e hA haA haG

omit [Finite V] in
theorem le_iSup_conj (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {k m : ℕ} (C : Fin k → G4)
    (F : Fin m → G4) (D : G4) (hF : ∀ j, fL4 e (D⁻¹ * F j * D) ∈ A) :
    Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹} ≤
      (⨆ i, A.map (MulAut.conj (fL4 e (C i * D))).toMonoidHom).comap (fL4 e) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, j, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  refine Subgroup.mem_iSup_of_mem i ?_
  rw [Subgroup.mem_map]
  refine ⟨fL4 e (D⁻¹ * F j * D), hF j, ?_⟩
  have e1 : C i * D * (D⁻¹ * F j * D) * (C i * D)⁻¹ = C i * F j * (C i)⁻¹ := by
    simp only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, e1]

theorem index_le_pow_of_entry (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {k m : ℕ} (C : Fin k → G4)
    (F : Fin m → G4) (D : G4) (hF : ∀ j, fL4 e (D⁻¹ * F j * D) ∈ A) {X : Subgroup G4}
    (hX : X ≤ Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹}) :
    (fixV (X.map (fL4 e))).index ≤ (fixV A).index ^ k := by
  have h := index_fixV_le_prod (fun i => A.map (MulAut.conj (fL4 e (C i * D))).toMonoidHom)
    (X := X.map (fL4 e)) (Subgroup.map_le_iff_le_comap.2 (hX.trans (le_iSup_conj e C F D hF)))
  simp only [CFSG.QuasithinUnique.B42A57.index_fixV_conj, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h
  exact h

theorem card_le_pow_of_entry (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hfixL : fixV L = ⊥)
    {k m : ℕ} (C : Fin k → G4) (F : Fin m → G4)
    (hgen : Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹} = ⊤) (D : G4)
    (hF : ∀ j, fL4 e (D⁻¹ * F j * D) ∈ A) : Nat.card V ≤ (fixV A).index ^ k := by
  have h := index_le_pow_of_entry e C F D hF (X := ⊤) hgen.ge
  have hL : (⊤ : Subgroup G4).map (fL4 e) = L := by
    rw [← MonoidHom.range_eq_map]
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact fL4_mem e g
    · intro hx
      obtain ⟨g, hg⟩ := exists_fL4_eq e hx
      exact ⟨g, hg⟩
  rwa [hL, hfixL, Subgroup.index_bot] at h

end CFSG.Quasithin.B42Ln

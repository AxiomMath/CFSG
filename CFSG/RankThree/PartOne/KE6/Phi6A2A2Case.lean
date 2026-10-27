module

public import CFSG.RankThree.PartOne.KE6.Phi6A2A2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open Matrix
open scoped Matrix MatrixGroups Pointwise commutatorElement

variable {Ω : Type} [Field Ω]

section Transport

variable {Fr : Ω →+* Ω}

theorem phi6_A2A2_transport [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi6TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ w : WeylGroup Tag.E6,
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ∧
      ∃ π π' : Equiv.Perm (Fin 3),
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c)) ∧
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain13 (π' i) (π' j)) (e * Fr c)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (q : ZMod p) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2A2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (q : ZMod p) a b)).Nonempty := by
    have h1 : (parabolicRoots Tag.E6 supportA2A2).Nonempty := by
      rw [parabolicRoots_supportA2A2]
      exact ⟨_, Or.inl (chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide))⟩
    rw [← hw₀] at h1
    exact Set.image_nonempty.1 h1
  have hcard := ncard_rootKernel_of_image hw₀
  rw [ncard_parabolicRoots_supportA2A2] at hcard
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hline, -, hA2A2', hA2'⟩ := h8 p hp3 _ hr
  obtain ⟨k, hk⟩ := (hline a b hab0).1 hne
  have hk4 : k.val < 4 := by
    by_contra h
    obtain ⟨w', hw', -⟩ := hA2' k (by omega)
    have := (hw' a b hab0 hk).2
    omega
  obtain ⟨w, hw, -, -, ⟨π, hπ⟩, ⟨π', hπ'⟩⟩ := hA2A2' k hk4
  have hwker := (hw a b hab0 hk).1
  refine ⟨w, ?_, π, π', fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [hker0, (canonical_weyl_root_transport Tag.E6 Ω).1 w _ fun α hα => hα.1, hwker,
      rootSpan_supportA2A2]
  · have hβ : IsRoot Tag.E6 (chainRoot chain13 i j) := (chainRoot13_mem_parabolicRoots hij).1
    obtain ⟨e, he, hθ⟩ := exists_conj_phi6Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain56 (π i) (π j) := hπ i j
    exact ⟨e, he, fun c => by rw [hθ, hπij]⟩
  · have hβ : IsRoot Tag.E6 (chainRoot chain56 i j) := isRoot_chainRoot56 hij
    obtain ⟨e, he, hθ⟩ := exists_conj_phi6Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain56 i j =
        chainRoot chain13 (π' i) (π' j) := hπ' i j
    exact ⟨e, he, fun c => by rw [hθ, hπij]⟩

end Transport


section TransferFix

variable {Fr : Ω →+* Ω}

theorem map_conj_phi6Qθ {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    {Q' : Subgroup (ModGL Tag.E6 Ω)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom = Q')
    (θ : ↥Q' ≃* ↥Q') (hθ : ∀ g, (θ g : ModGL Tag.E6 Ω) = phi6ThetaConj Ω Fr w g) :
    (phi6Qθ Ω Fr S).map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      (fixSubgroup θ).map Q'.subtype := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxR⟩, rfl⟩
    have hy : (MulAut.conj n).toMonoidHom x ∈ Q' := by
      rw [← hQ]
      exact ⟨x, hxS, rfl⟩
    refine ⟨⟨_, hy⟩, ?_, rfl⟩
    change θ ⟨_, hy⟩ = ⟨_, hy⟩
    apply Subtype.ext
    rw [hθ]
    change phi6ThetaConj Ω Fr w (n * x * n⁻¹) = n * x * n⁻¹
    have hxR' : phi6Theta Ω Fr x = x := hxR
    rw [phi6ThetaConj_conj, hxR']
  · rintro ⟨g, hg, rfl⟩
    have hgQ : (g : ModGL Tag.E6 Ω) ∈ (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom := by
      rw [hQ]
      exact g.2
    obtain ⟨x, hxS, hx⟩ := hgQ
    change n * x * n⁻¹ = (g : ModGL Tag.E6 Ω) at hx
    have hθg : phi6ThetaConj Ω Fr w g = g := by
      rw [← hθ]
      exact congrArg Subtype.val (hg : θ g = g)
    rw [← hx, phi6ThetaConj_conj] at hθg
    refine ⟨x, ⟨hxS, ?_⟩, ?_⟩
    · exact mul_left_cancel (mul_right_cancel hθg)
    · change n * x * n⁻¹ = g
      exact hx

end TransferFix

theorem phi6_twoA2_key {h z₁ z₂ : ModGL Tag.E6 Ω}
    (hh : h ∈ torusGroup Tag.E6 Ω) (hz₁ : z₁ ∈ subsystemGroup Tag.E6 Ω support13)
    (hz₂ : z₂ ∈ subsystemGroup Tag.E6 Ω support56) (S : Set (SL(3, Ω) × SL(3, Ω)))
    (hS : ∀ s ∈ S, (h * z₁ * z₂) * twoA2Mul Ω s = twoA2Mul Ω s * (h * z₁ * z₂))
    (g₁ g₂ : SL(3, Ω))
    (hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.1 = g₁ * Matrix.SpecialLinearGroup.transvection hij 1 * g₁⁻¹)
    (hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∃ s ∈ S, s.2 = g₂ * Matrix.SpecialLinearGroup.transvection hij 1 * g₂⁻¹) :
    z₁ ∈ torusGroup Tag.E6 Ω ∧ z₂ ∈ torusGroup Tag.E6 Ω ∧
      ∀ g ∈ subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56,
        (h * z₁ * z₂) * g = g * (h * z₁ * z₂) := by
  obtain ⟨χ, hχ, -⟩ := exists_simple_root_characters hh
  set s₁ := χ (e6Index 0)
  set t₁ := χ (e6Index 2)
  set s₂ := χ (e6Index 4)
  set t₂ := χ (e6Index 5)
  let D₁ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₁ t₁).1, (diagonal_inv_pair s₁ t₁).2⟩
  let D₂ : GL (Fin 3) Ω := ⟨_, _, (diagonal_inv_pair s₂ t₂).1, (diagonal_inv_pair s₂ t₂).2⟩
  set ρz₁ := a2Rep₁ Ω ⟨z₁, hz₁⟩
  set ρz₂ := a2Rep₂ Ω ⟨z₂, hz₂⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M : GL (Fin 3) Ω, M = D₁ * Matrix.SpecialLinearGroup.toGL ρz₁ :=
    ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M : GL (Fin 3) Ω, M = D₂ * Matrix.SpecialLinearGroup.toGL ρz₂ :=
    ⟨_, rfl⟩
  have hM₁v : (M₁ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁ := by
    rw [hM₁, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₁]
  have hM₂v : (M₂ : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂ := by
    rw [hM₂, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₂]
  have hM₁i : (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₁, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₁]
    rfl
  have hM₂i : (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1] := by
    rw [hM₂, _root_.mul_inv_rev, Units.val_mul, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv, coe_a2Rep₂]
    rfl
  have hdisc : ∀ s ∈ S, ∃ c : Ω,
      (M₁ : Matrix (Fin 3) (Fin 3) Ω) * s.1 * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.1 : Matrix (Fin 3) (Fin 3) Ω) ∧
      (M₂ : Matrix (Fin 3) (Fin 3) Ω) * s.2 * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) =
        c • (s.2 : Matrix (Fin 3) (Fin 3) Ω) := by
    rintro ⟨X, Y⟩ hs
    set u := ((a2Equiv₁ Ω).symm X : ModGL Tag.E6 Ω)
    set v := ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω)
    have hu : u ∈ subsystemGroup Tag.E6 Ω support13 := ((a2Equiv₁ Ω).symm X).2
    have hv : v ∈ subsystemGroup Tag.E6 Ω support56 := ((a2Equiv₂ Ω).symm Y).2
    have hau : a2Mat₁ u = X := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₁ Ω) X)
      simpa only [a2Equiv₁_apply, coe_a2Rep₁] using this
    have hav : a2Mat₂ v = Y := by
      have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
        (MulEquiv.apply_symm_apply (a2Equiv₂ Ω) Y)
      simpa only [a2Equiv₂_apply, coe_a2Rep₂] using this
    obtain ⟨hu', hau'⟩ := a2Mat₁_conj_formula hh (hχ (e6Index 0)) (hχ (e6Index 2)) hz₁ hu
    obtain ⟨hv', hav'⟩ := a2Mat₂_conj_formula hh (hχ (e6Index 4)) (hχ (e6Index 5)) hz₂ hv
    set u' := h * (z₁ * u * z₁⁻¹) * h⁻¹
    set v' := h * (z₂ * v * z₂⁻¹) * h⁻¹
    have hcomm := hS (X, Y) hs
    rw [twoA2Mul_apply] at hcomm
    have c1 : z₂ * u = u * z₂ := (commute_Q₁_Q₂ hu hz₂).eq.symm
    have hzvz : z₂ * v * z₂⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
      mul_mem (mul_mem hz₂ hv) (inv_mem hz₂)
    have c2 : z₁⁻¹ * (z₂ * v * z₂⁻¹) = (z₂ * v * z₂⁻¹) * z₁⁻¹ :=
      (commute_Q₁_Q₂ (inv_mem hz₁) hzvz).eq
    have huv : u' * v' = u * v := by
      calc u' * v' = h * z₁ * u * (z₁⁻¹ * (z₂ * v * z₂⁻¹)) * h⁻¹ := by
            simp only [u', v']
            group
        _ = h * z₁ * u * ((z₂ * v * z₂⁻¹) * z₁⁻¹) * h⁻¹ := by rw [c2]
        _ = h * z₁ * (u * z₂) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by group
        _ = h * z₁ * (z₂ * u) * v * z₂⁻¹ * z₁⁻¹ * h⁻¹ := by rw [c1]
        _ = (h * z₁ * z₂) * (u * v) * (h * z₁ * z₂)⁻¹ := by group
        _ = u * v := by rw [hcomm, mul_inv_cancel_right]
    have h1 : u⁻¹ * u' ∈ subsystemGroup Tag.E6 Ω support13 := mul_mem (inv_mem hu) hu'
    have h2 : v' * v⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := mul_mem hv' (inv_mem hv)
    have hone : twoA2Mul Ω (a2Equiv₁ Ω ⟨_, h1⟩, a2Equiv₂ Ω ⟨_, h2⟩) = 1 := by
      rw [twoA2Mul_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      change u⁻¹ * u' * (v' * v⁻¹) = 1
      calc u⁻¹ * u' * (v' * v⁻¹) = u⁻¹ * (u' * v') * v⁻¹ := by group
        _ = 1 := by rw [huv]; group
    obtain ⟨c, -, hc₁, hc₂⟩ := (twoA2Mul_eq_one_iff _ _).1 hone
    rw [a2Equiv₁_apply, coe_a2Rep₁] at hc₁
    rw [a2Equiv₂_apply, coe_a2Rep₂] at hc₂
    change a2Mat₁ (u⁻¹ * u') = scalar (Fin 3) c at hc₁
    change a2Mat₂ (v' * v⁻¹) = scalar (Fin 3) c at hc₂
    rw [a2Mat₁_mul (inv_mem hu) hu'] at hc₁
    rw [a2Mat₂_mul hv' (inv_mem hv)] at hc₂
    have hinvu : a2Mat₁ u * a2Mat₁ u⁻¹ = 1 := by
      rw [← a2Mat₁_mul hu (inv_mem hu), mul_inv_cancel, a2Mat₁_one]
    have hinvv : a2Mat₂ v⁻¹ * a2Mat₂ v = 1 := by
      rw [← a2Mat₂_mul (inv_mem hv) hv, inv_mul_cancel, a2Mat₂_one]
    refine ⟨c, ?_, ?_⟩
    ·
      change (M₁ : Matrix (Fin 3) (Fin 3) Ω) * X * (↑M₁⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₁v, hM₁i, ← hau, ← hau']
      calc a2Mat₁ u' = a2Mat₁ u * (a2Mat₁ u⁻¹ * a2Mat₁ u') := by
            rw [← Matrix.mul_assoc, hinvu, Matrix.one_mul]
        _ = c • a2Mat₁ u := by
            rw [hc₁, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
              Matrix.mul_one]
    · change (M₂ : Matrix (Fin 3) (Fin 3) Ω) * Y * (↑M₂⁻¹ : Matrix (Fin 3) (Fin 3) Ω) = _
      rw [hM₂v, hM₂i, ← hav, ← hav']
      calc a2Mat₂ v' = (a2Mat₂ v' * a2Mat₂ v⁻¹) * a2Mat₂ v := by
            rw [Matrix.mul_assoc, hinvv, Matrix.mul_one]
        _ = c • a2Mat₂ v := by
            rw [hc₂, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
              Matrix.one_mul]
  obtain ⟨c₁, hc₁⟩ := exists_eq_scalar_of_discrepancy M₁ g₁ (Prod.fst '' S)
    (fun X hX => by
      obtain ⟨s, hs, rfl⟩ := hX
      obtain ⟨c, hc, -⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs1⟩ := hT₁ i j hij
      exact ⟨s, hs, hs1⟩)
  obtain ⟨c₂, hc₂⟩ := exists_eq_scalar_of_discrepancy M₂ g₂ (Prod.snd '' S)
    (fun Y hY => by
      obtain ⟨s, hs, rfl⟩ := hY
      obtain ⟨c, -, hc⟩ := hdisc s hs
      exact ⟨c, hc⟩)
    (fun i j hij => by
      obtain ⟨s, hs, hs2⟩ := hT₂ i j hij
      exact ⟨s, hs, hs2⟩)
  rw [hM₁v] at hc₁
  rw [hM₂v] at hc₂
  have hz₁H := mem_torusGroup_of_diagonal_mul_eq_scalar hz₁ s₁ t₁ hc₁
  have hz₂H := mem_torusGroup_of_diagonal_mul_eq_scalar₂ hz₂ s₂ t₂ hc₂
  refine ⟨hz₁H, hz₂H, ?_⟩
  have hQ₁ : ∀ u ∈ subsystemGroup Tag.E6 Ω support13,
      (h * z₁ * z₂) * u = u * (h * z₁ * z₂) := by
    intro u hu
    obtain ⟨hmem, hform⟩ := a2Mat₁_conj_formula hh (hχ (e6Index 0)) (hχ (e6Index 2)) hz₁ hu
    have hρρ : a2Mat₁ z₁ * a2Mat₁ z₁⁻¹ = 1 := by
      rw [← a2Mat₁_mul hz₁ (inv_mem hz₁), mul_inv_cancel, a2Mat₁_one]
    have hAM : (diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁) *
        (a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1]) = 1 := by
      calc (diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * a2Mat₁ z₁) *
          (a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1]) =
          diagonal ![((s₁ * t₁ : Ωˣ) : Ω), (t₁ : Ω), 1] * (a2Mat₁ z₁ * a2Mat₁ z₁⁻¹) *
            diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1] := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hρρ, Matrix.mul_one, (diagonal_inv_pair s₁ t₁).1]
    have hres : a2Mat₁ (h * (z₁ * u * z₁⁻¹) * h⁻¹) = a2Mat₁ u := by
      rw [hform, hc₁]
      calc scalar (Fin 3) c₁ * a2Mat₁ u *
            (a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1]) =
          a2Mat₁ u * (scalar (Fin 3) c₁ *
            (a2Mat₁ z₁⁻¹ * diagonal ![(((s₁ * t₁)⁻¹ : Ωˣ) : Ω), ((t₁⁻¹ : Ωˣ) : Ω), 1])) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (scalar (Fin 3) c₁),
              (Matrix.scalar_commute c₁ (fun r => Commute.all _ r) _).eq, Matrix.mul_assoc]
        _ = a2Mat₁ u := by
            rw [← hc₁, hAM, Matrix.mul_one]
    have hu' : h * (z₁ * u * z₁⁻¹) * h⁻¹ = u := by
      have h1 : a2Rep₁ Ω ⟨_, hmem⟩ = a2Rep₁ Ω ⟨u, hu⟩ := by
        apply Subtype.ext
        rw [coe_a2Rep₁, coe_a2Rep₁]
        exact hres
      exact congrArg Subtype.val (a2Rep₁_injective h1)
    have h2 : h * z₁ * u = u * (h * z₁) := by
      calc h * z₁ * u = (h * (z₁ * u * z₁⁻¹) * h⁻¹) * (h * z₁) := by group
        _ = u * (h * z₁) := by rw [hu']
    calc (h * z₁ * z₂) * u = h * z₁ * (z₂ * u) := by group
      _ = h * z₁ * (u * z₂) := by rw [(commute_Q₁_Q₂ hu hz₂).eq]
      _ = (h * z₁ * u) * z₂ := by group
      _ = (u * (h * z₁)) * z₂ := by rw [h2]
      _ = u * (h * z₁ * z₂) := by group
  have hQ₂ : ∀ v ∈ subsystemGroup Tag.E6 Ω support56,
      (h * z₁ * z₂) * v = v * (h * z₁ * z₂) := by
    intro v hv
    obtain ⟨hmem, hform⟩ := a2Mat₂_conj_formula hh (hχ (e6Index 4)) (hχ (e6Index 5)) hz₂ hv
    have hρρ : a2Mat₂ z₂ * a2Mat₂ z₂⁻¹ = 1 := by
      rw [← a2Mat₂_mul hz₂ (inv_mem hz₂), mul_inv_cancel, a2Mat₂_one]
    have hAM : (diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂) *
        (a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1]) = 1 := by
      calc (diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * a2Mat₂ z₂) *
          (a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1]) =
          diagonal ![((s₂ * t₂ : Ωˣ) : Ω), (t₂ : Ω), 1] * (a2Mat₂ z₂ * a2Mat₂ z₂⁻¹) *
            diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1] := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hρρ, Matrix.mul_one, (diagonal_inv_pair s₂ t₂).1]
    have hres : a2Mat₂ (h * (z₂ * v * z₂⁻¹) * h⁻¹) = a2Mat₂ v := by
      rw [hform, hc₂]
      calc scalar (Fin 3) c₂ * a2Mat₂ v *
            (a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1]) =
          a2Mat₂ v * (scalar (Fin 3) c₂ *
            (a2Mat₂ z₂⁻¹ * diagonal ![(((s₂ * t₂)⁻¹ : Ωˣ) : Ω), ((t₂⁻¹ : Ωˣ) : Ω), 1])) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (scalar (Fin 3) c₂),
              (Matrix.scalar_commute c₂ (fun r => Commute.all _ r) _).eq, Matrix.mul_assoc]
        _ = a2Mat₂ v := by
            rw [← hc₂, hAM, Matrix.mul_one]
    have hv' : h * (z₂ * v * z₂⁻¹) * h⁻¹ = v := by
      have h1 : a2Rep₂ Ω ⟨_, hmem⟩ = a2Rep₂ Ω ⟨v, hv⟩ := by
        apply Subtype.ext
        rw [coe_a2Rep₂, coe_a2Rep₂]
        exact hres
      exact congrArg Subtype.val (a2Rep₂_injective h1)
    have h2 : h * z₂ * v = v * (h * z₂) := by
      calc h * z₂ * v = (h * (z₂ * v * z₂⁻¹) * h⁻¹) * (h * z₂) := by group
        _ = v * (h * z₂) := by rw [hv']
    have hcz : z₁ * z₂ = z₂ * z₁ := (commute_Q₁_Q₂ hz₁ hz₂).eq
    have hcv : z₁ * v = v * z₁ := (commute_Q₁_Q₂ hz₁ hv).eq
    calc (h * z₁ * z₂) * v = h * z₂ * z₁ * v := by rw [mul_assoc h z₁ z₂, hcz, ← mul_assoc]
      _ = h * z₂ * (z₁ * v) := by group
      _ = h * z₂ * (v * z₁) := by rw [hcv]
      _ = (h * z₂ * v) * z₁ := by group
      _ = (v * (h * z₂)) * z₁ := by rw [h2]
      _ = v * (h * z₂ * z₁) := by group
      _ = v * (h * z₁ * z₂) := by rw [mul_assoc h z₂ z₁, ← hcz, mul_assoc h z₁ z₂]
  have hle : subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ≤
      Subgroup.centralizer ({h * z₁ * z₂} : Set (ModGL Tag.E6 Ω)) :=
    sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hQ₁ u hu).symm)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (hQ₂ v hv).symm)
  exact fun g hg => (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm




section A2A2Case

variable {Fr : Ω →+* Ω}

variable (Ω Fr) in
@[expose] def phi6P
    (S : Set (Fin Tag.E6.rank → ℤ)) : Subgroup (ModGL Tag.E6 Ω) :=
  ⁅phi6Qθ Ω Fr S, phi6Qθ Ω Fr S⁆

theorem phi6_A2A2_case {K : Type} [Field K] [Finite K] [Algebra K Ω] [IsAlgClosure K Ω]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    Finite ↥(phi6P Ω Fr (torusRootKernel x)) ∧
    CFSG.IsQuasisimple ↥(phi6P Ω Fr (torusRootKernel x)) ∧
    Nat.card (Subgroup.center ↥(phi6P Ω Fr (torusRootKernel x))) =
      Nat.gcd 3 ((ℓ ^ f) ^ 2 - 1) / Nat.gcd 3 (ℓ ^ f - 1) ∧
    (∀ a ∈ phi6Qθ Ω Fr (torusRootKernel x), ∀ b ∈ phi6Qθ Ω Fr (torusRootKernel x),
      a * b * a⁻¹ * b⁻¹ ∈ phi6P Ω Fr (torusRootKernel x)) ∧
    (phi6P Ω Fr (torusRootKernel x)).relIndex (phi6Qθ Ω Fr (torusRootKernel x)) ∣
      Nat.gcd 3 (ℓ ^ f - 1) ∧
    (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
        Subgroup.centralizer (↑(phi6P Ω Fr (torusRootKernel x)) : Set (ModGL Tag.E6 Ω)) ≤
      torusGroup Tag.E6 Ω ∧
    ∀ y ∈ torusGroup Tag.E6 Ω, (∀ u ∈ phi6P Ω Fr (torusRootKernel x), y * u = u * y) →
      ∀ g ∈ rootSpan Tag.E6 Ω (torusRootKernel x), y * g = g * y := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁₂, π, π', h12, h21⟩ := phi6_A2A2_transport hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer_pos hFrs (phi6ThetaConj Ω Fr w)
    (phi6ThetaConj_injective w) π π' h12 h21
  obtain ⟨k₂, hk₂, h₁, h₂, ψ, hψ, hψfix, -, hqs9, -, -, -, hcardcenter9, hfin9, hindex9, hder9⟩ := CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer hℓ hf hK Fr
    hFr twoA2MulSup twoA2MulSup_surjective (fun xy => twoA2MulSup_eq_one_iff xy.1 xy.2) θ a b hab
  set Y := phi6Qθ Ω Fr (torusRootKernel x) with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_phi6Qθ hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hF : Function.Injective F := (MulAut.conj n).symm.injective.comp Subtype.val_injective
  have hFapp : ∀ y, F y = n⁻¹ * (y : ModGL Tag.E6 Ω) * n := fun y => by
    simp [F, MulAut.conj_symm_apply]
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hder' : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hψfix, ← hder9, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder', MonoidHom.range_comp]
  have hψ'1 : ∀ A, ψ' A = 1 ↔ ψ A = 1 := fun A => map_eq_one_iff F hF
  let E : ↥ψ.range ≃* ↥⁅Y, Y⁆ := (Subgroup.equivMapOfInjective ψ.range F hF).trans
    (MulEquiv.subgroupCongr (by rw [← MonoidHom.range_comp]; exact hrange))
  have hqsP : CFSG.IsQuasisimple ↥⁅Y, Y⁆ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv E hqs9
  have hidx : ⁅Y, Y⁆.relIndex Y = (ψ.range.subgroupOf (fixSubgroup θ)).index := by
    rw [← hrange, ← hYf, MonoidHom.range_comp, Subgroup.relIndex_map_map_of_injective _ _ hF]
    rfl
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) :=
    CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hkeyP : ∀ {h z : ModGL Tag.E6 Ω}, h ∈ torusGroup Tag.E6 Ω →
      z ∈ rootSpan Tag.E6 Ω (torusRootKernel x) →
      (∀ u ∈ ⁅Y, Y⁆, h * z * u = u * (h * z)) →
      z ∈ torusGroup Tag.E6 Ω ∧ ∀ g ∈ rootSpan Tag.E6 Ω (torusRootKernel x),
        (h * z) * g = g * (h * z) := by
    intro h z hh hz hc
    have hnN := canonicalRep_mem_normalizer (R := Ω) w
    have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
    have hz' : n * z * n⁻¹ ∈ (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
        (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
      rw [← coe_sup_subsystemGroup, ← hQ₁₂]
      exact ⟨z, hz, rfl⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := hz'
    replace hz12 : z₁ * z₂ = n * z * n⁻¹ := hz12
    set S : Set (SL(3, Ω) × SL(3, Ω)) := Set.range fun A : SL(3, k₂) =>
      (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹) with hSdef
    have hS : ∀ s ∈ S, (n * h * n⁻¹ * z₁ * z₂) * twoA2Mul Ω s =
        twoA2Mul Ω s * (n * h * n⁻¹ * z₁ * z₂) := by
      rintro _ ⟨A, rfl⟩
      have hPA : twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
            h₂⁻¹) = (ψ A : ModGL Tag.E6 Ω) := by
        rw [hψ A]
        rfl
      rw [hPA]
      have hmem : ψ' A ∈ ⁅Y, Y⁆ := hrange ▸ ⟨A, rfl⟩
      have hc0 := hc (ψ' A) hmem
      change h * z * F (ψ A) = F (ψ A) * (h * z) at hc0
      rw [hFapp] at hc0
      have key : n * h * n⁻¹ * z₁ * z₂ = n * (h * z) * n⁻¹ := by
        rw [mul_assoc (n * h * n⁻¹) z₁ z₂, hz12]
        group
      rw [key]
      calc n * (h * z) * n⁻¹ * (ψ A : ModGL Tag.E6 Ω) =
          n * (h * z * (n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n)) * n⁻¹ := by group
        _ = n * (n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n * (h * z)) * n⁻¹ := by rw [hc0]
        _ = (ψ A : ModGL Tag.E6 Ω) * (n * (h * z) * n⁻¹) := by group
    have hT₁ : ∀ (i j : Fin 3) (hij : i ≠ j),
        ∃ s ∈ S, s.1 = h₁ * Matrix.SpecialLinearGroup.transvection hij 1 * h₁⁻¹ :=
      fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij 1, rfl⟩, by
        dsimp only
        rw [Matrix.SpecialLinearGroup.map_transvection, map_one]⟩
    have hT₂ : ∀ (i j : Fin 3) (hij : i ≠ j),
        ∃ s ∈ S, s.2 = h₂ * Matrix.SpecialLinearGroup.transvection hij 1 * h₂⁻¹ :=
      fun i j hij => ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij 1, rfl⟩, by
        dsimp only
        rw [Matrix.SpecialLinearGroup.map_transvection, map_one,
          Matrix.SpecialLinearGroup.map_transvection, map_one]⟩
    obtain ⟨hz₁H, hz₂H, hcent⟩ := phi6_twoA2_key hh' hz₁ hz₂ S hS h₁ h₂ hT₁ hT₂
    have hz'H : n * z * n⁻¹ ∈ torusGroup Tag.E6 Ω := hz12 ▸ mul_mem hz₁H hz₂H
    refine ⟨?_, fun g hg => ?_⟩
    · have h3 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) (n * z * n⁻¹)).1 hz'H
      rwa [show n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z by group] at h3
    · have hg' : n * g * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 ⊔
          subsystemGroup Tag.E6 Ω support56 := by
        rw [← hQ₁₂]
        exact ⟨g, hg, rfl⟩
      have h4 := hcent _ hg'
      have key : n * h * n⁻¹ * z₁ * z₂ = n * (h * z) * n⁻¹ := by
        rw [mul_assoc (n * h * n⁻¹) z₁ z₂, hz12]
        group
      rw [key] at h4
      calc (h * z) * g = n⁻¹ * (n * (h * z) * n⁻¹ * (n * g * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * g * n⁻¹) * (n * (h * z) * n⁻¹)) * n := by rw [h4]
        _ = g * (h * z) := by group
  have hfinψ : Finite ↥ψ.range :=
    Finite.of_injective (Subgroup.inclusion hψfix) (Subgroup.inclusion_injective hψfix)
  refine ⟨Finite.of_equiv _ E.toEquiv, hqsP, (natCard_center_eq_of_mulEquiv E.symm).trans
    hcardcenter9, fun a ha b hb => ?_, ?_, ?_, ?_⟩
  · have h := Subgroup.commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at h
  · change ⁅Y, Y⁆.relIndex Y ∣ _
    rw [hidx]
    exact hindex9
  · rintro y ⟨hyHQ, hyc⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
    have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
        (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
      rw [← hmul]
      exact hyHQ
    obtain ⟨h, hh, z, hz, rfl⟩ := hy'
    exact mul_mem hh (hkeyP hh hz fun u hu =>
      ((Subgroup.mem_centralizer_iff.1 hyc) u hu).symm).1
  · intro y hy hc g hg
    have := (hkeyP (h := y) (z := 1) hy (one_mem _) (fun u hu => by
      rw [mul_one]
      exact hc u hu)).2 g hg
    simpa using this

end A2A2Case

end CFSG.RankThree.PartOne.KE6

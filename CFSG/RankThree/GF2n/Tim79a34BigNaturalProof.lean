module

public import CFSG.RankThree.GF2n.Tim79a34BigNaturalPoint
public import CFSG.RankThree.GF2n.Tim79a34BigSL2Nat
public import CFSG.RankThree.GF2n.Tim79a34BigNatural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem BigEndHyp.exists_naturalModule (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) :
    ∃ (f n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)),
      2 ≤ n ∧ 2 ≤ f ∧ 2 ^ f = qBar V H ∧
      (∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 f),
        ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f)
          (Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x)) *ᵥ v)) : ↥(wOf V H)) : G) =
          (x : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (x : G)⁻¹) ∧
      (∃ (a : Fin n ⊕ Fin n → GaloisField 2 f)
          (T : Subgroup ↥(StatedSp n (GaloisField 2 f))),
        a ≠ 0 ∧ IsTransGroup a T ∧ T.map Φ.toMonoidHom = Vy V H ∧
        (∀ c : GaloisField 2 f,
          ((Additive.toMul (ψ (c • a)) : ↥(wOf V H)) : G) ∈ V) ∧
        ∀ w ∈ V ⊓ wOf V H, ∃ c : GaloisField 2 f,
          ((Additive.toMul (ψ (c • a)) : ↥(wOf V H)) : G) = w) := by
  obtain ⟨f, n, k, Φ, g, θ, hn, hf, h2f, ⟨T, hT, hTmap⟩, hadd, hinj, hmemW, hmemV,
    hsurj, hequiv⟩ := h.exists_sl2_natural hZ (h.wOf_inf_centralizer_eq)
  let D : BigNatData h hZ :=
    { f := f, n := n, k := k, Φ := Φ, g := g, θ := θ, hn := hn, hf := hf, h2f := h2f,
      T := T, hT := hT, hTmap := hTmap, hadd := hadd, hinj := hinj, hmemW := hmemW,
      hmemV := hmemV, hsurj := hsurj, hequiv := hequiv }
  let ψhom : (Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) →+ Additive ↥(wOf V H) :=
    { toFun := fun v => Additive.ofMul (D.psi0W v)
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact D.psi0_zero
      map_add' := fun v v' => by
        apply Additive.toMul.injective
        exact D.psi0W_add v v' }
  have hψbij : Function.Bijective ψhom := by
    constructor
    · intro v v' h
      exact D.psi0W_bijective.1 (Additive.ofMul.injective h)
    · intro y
      obtain ⟨v, hv⟩ := D.psi0W_bijective.2 (Additive.toMul y)
      refine ⟨v, ?_⟩
      apply Additive.toMul.injective
      simpa [ψhom] using hv
  let ψ : (Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) ≃+ Additive ↥(wOf V H) :=
    AddEquiv.ofBijective ψhom hψbij
  have hψ : ∀ v, Additive.toMul (ψ v) = D.psi0W v := fun v => rfl
  have hTa : IsTransGroup D.a D.T := by
    simpa [BigNatData.a] using D.hT
  have hline : ∀ c : GaloisField 2 D.f,
      ((Additive.toMul (ψ (c • D.a)) : ↥(wOf V H)) : G) ∈ V := by
    intro c
    have hplane : D.psi0 (c • D.a) = D.θ ![c, 0] := by
      have := D.psi0_plane ![c, 0]
      simpa using this
    simpa [hψ, BigNatData.psi0W, hplane] using D.hmemV c
  have hline_surj : ∀ w ∈ V ⊓ wOf V H, ∃ c : GaloisField 2 D.f,
      ((Additive.toMul (ψ (c • D.a)) : ↥(wOf V H)) : G) = w := by
    intro w hw
    obtain ⟨c, hc⟩ := D.hsurj w hw
    refine ⟨c, ?_⟩
    have hplane : D.psi0 (c • D.a) = D.θ ![c, 0] := by
      have := D.psi0_plane ![c, 0]
      simpa using this
    simpa [hψ, BigNatData.psi0W, hplane, hc]
  refine ⟨D.f, D.n, D.Φ, ψ, D.hn, D.hf, D.h2f, ?_,
    ⟨D.a, D.T, D.a_ne_zero, hTa, D.hTmap, hline, hline_surj⟩⟩
  · intro x v
    have hx := D.psi0_conj_x x v
    simpa [hψ, BigNatData.psi0W] using hx.symm

theorem bigNaturalStatement_holds : BigNaturalStatement := by
  intro G _ _ M V Q P H h hZ
  obtain ⟨f, n, Φ, ψ, hn, -, h2f, hequiv, ⟨a, T, ha, hT, hTmap, hline, hsurj⟩⟩ :=
    h.exists_naturalModule hZ
  refine ⟨n, f, Φ, ψ, hn, h2f, hequiv, ⟨a, T, ha, hT, hTmap⟩, ?_⟩
  intro a' T' ha' hT' hTmap'
  have hT_eq : T' = T := by
    apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
    rw [hTmap', hTmap]
  have hT'' : IsTransGroup a' T := hT_eq ▸ hT'
  obtain ⟨mu, -, haeq⟩ := IsTransGroup.exists_eq_smul (X := T) hT'' hT ha'
  rw [haeq]
  exact hline mu

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.H13.VolII16SLNat
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
open scoped Matrix


private theorem s16c11_v1_minusQuadCore_map {m : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (b c : K) (hb : e.symm b = 1) (hc : e.symm c = 1) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    CFSG.MatrixModel.minusQuadCore m (ZMod 2) 1 1 (fun i => e.symm (v i)) =
      e.symm (CFSG.MatrixModel.minusQuadCore m K b c v) := by
  simp only [CFSG.MatrixModel.minusQuadCore, map_add, map_mul, map_pow, map_sum, map_one, hb, hc,
    one_mul]

private theorem s16c11_v1_zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem s16c11_v1_statedOmega_minus_ringEquiv {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (θ : (Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
      (ψ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K ≃* GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)),
      (∀ (γ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K),
        θ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) K γ v) =
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)
            (ψ γ) (θ v)) ∧
      ∀ γ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K,
        γ ∈ StatedOmega (StatedQuadMinus (m + 1) K b c) ↔
          ψ γ ∈ StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
  let θ : (Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃+
      (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    AddEquiv.piCongrRight (fun _ => (e.symm : K ≃+ ZMod 2))
  let ψ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K ≃*
      GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
    Units.mapEquiv (RingEquiv.mapMatrix e.symm).toMulEquiv
  have hθ : ∀ v : Fin m ⊕ Fin m ⊕ Fin 2 → K, θ v = fun i => e.symm (v i) := fun _ => rfl
  have hψ : ∀ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) K,
      ((ψ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) =
        (A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K).map e.symm :=
    fun _ => rfl
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e.symm b * t + e.symm c ≠ 0 := by
    intro t h0
    apply hpoly (e t)
    have h1 : e.symm ((e t) ^ 2 + b * e t + c) = 0 := by
      rw [map_add, map_add, map_mul, map_pow]
      simpa using h0
    have h2 : (e t) ^ 2 + b * e t + c = 0 := by
      have := congrArg e h1
      rwa [e.apply_symm_apply, map_zero] at this
    exact h2
  have hc1 : e.symm c = 1 := by
    rcases s16c11_v1_zmod2_eq_zero_or_eq_one (e.symm c) with h | h
    · exfalso
      have hzero : (0 : ZMod 2) ^ 2 + e.symm b * 0 + e.symm c = 0 := by
        rw [h]; simp
      exact hpoly' 0 hzero
    · exact h
  have hb1 : e.symm b = 1 := by
    rcases s16c11_v1_zmod2_eq_zero_or_eq_one (e.symm b) with h | h
    · exfalso
      have hzero : (1 : ZMod 2) ^ 2 + e.symm b * 1 + e.symm c = 0 := by
        rw [h, hc1]; decide
      exact hpoly' 1 hzero
    · exact h
  have hbc : e.symm b = 1 ∧ e.symm c = 1 := ⟨hb1, hc1⟩
  have hQrel : ∀ v : Fin m ⊕ Fin m ⊕ Fin 2 → K,
      StatedQuadMinus (m + 1) (ZMod 2) 1 1 (θ v) =
        e.symm (StatedQuadMinus (m + 1) K b c v) := by
    intro v
    rw [hθ]
    exact s16c11_v1_minusQuadCore_map e b c hbc.1 hbc.2 v
  have hconj : ∀ (A : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)
      (v : Fin m ⊕ Fin m ⊕ Fin 2 → K),
      θ ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v) =
        ((ψ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ θ v := by
    intro A v
    funext i
    rw [hθ, hψ, hθ]
    exact RingHom.map_mulVec (e.symm : K →+* ZMod 2)
      (A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) v i
  have hset : ∀ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) K,
      (∀ v, StatedQuadMinus (m + 1) K b c
          ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v) =
        StatedQuadMinus (m + 1) K b c v) ↔
      (∀ w, StatedQuadMinus (m + 1) (ZMod 2) 1 1
          (((ψ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ w) =
        StatedQuadMinus (m + 1) (ZMod 2) 1 1 w) := by
    intro A
    constructor
    · intro hA w
      obtain ⟨v, rfl⟩ := θ.surjective w
      calc StatedQuadMinus (m + 1) (ZMod 2) 1 1
              (((ψ A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
                Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ θ v)
          = StatedQuadMinus (m + 1) (ZMod 2) 1 1
              (θ ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v)) := by
            rw [hconj]
        _ = e.symm (StatedQuadMinus (m + 1) K b c
              ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v)) :=
            hQrel _
        _ = e.symm (StatedQuadMinus (m + 1) K b c v) := by rw [hA]
        _ = StatedQuadMinus (m + 1) (ZMod 2) 1 1 (θ v) := (hQrel v).symm
    · intro hA v
      apply e.symm.injective
      rw [← hQrel ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v),
        ← hQrel v, hconj]
      exact hA (θ v)
  have hcore : CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) (ZMod 2) 1 1) =
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c)).map ψ.toMonoidHom := by
    apply le_antisymm
    · rw [CFSG.MatrixModel.isometryCore, Subgroup.closure_le]
      intro B hB
      refine Subgroup.mem_map.2 ⟨ψ.symm B, ?_, by simp⟩
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure ((hset (ψ.symm B)).2 (by simpa using hB))
    · rw [CFSG.MatrixModel.isometryCore, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      intro A hA
      change ψ A ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) (ZMod 2) 1 1)
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure ((hset A).1 hA)
  refine ⟨θ, ψ, hconj, ?_⟩
  intro γ
  have hOmega : StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1) =
      (StatedOmega (StatedQuadMinus (m + 1) K b c)).map ψ.toMonoidHom := by
    change ⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) (ZMod 2) 1 1),
        CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) (ZMod 2) 1 1)⁆ =
      (⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c),
        CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c)⁆).map ψ.toMonoidHom
    rw [hcore, Subgroup.map_commutator]
  rw [hOmega, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem s16c11_v1_omegaMinus_data {m : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (h : (FFModel.nat (StatedOmega (StatedQuadMinus (m + 1) K b c))).Realizes H ⊤ Z) :
    ∃ (ρ : ↥(omegaMinusTwo m) →* MulAut W)
      (β : W →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)),
      (∀ g, ρ g ∈ H) ∧ (∀ x ∈ H, ∃ g, ρ g = x) ∧ Function.Surjective β ∧
        (∀ w, β w = 1 ↔ w ∈ Z) ∧
        ∀ g w, Multiplicative.toAdd (β (ρ g w)) =
          ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (β w) := by
  classical
  obtain ⟨θ, ψ, hconj, hψmem⟩ := s16c11_v1_statedOmega_minus_ringEquiv (m := m) hK hirr
  let Γ := StatedOmega (CFSG.PGLModel.minusQuadForm m b c)
  obtain ⟨π, bw, hπs, hbs, hbk, hbe⟩ :=
    CFSG.Quasithin.H13.VolI.topBot_data (D := FFModel.nat Γ) rfl rfl h
  let π' : ↥Γ →* ↥H := π
  let b : W →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → K) :=
    { toFun := bw, map_one' := map_one bw, map_mul' := map_mul bw }
  have hbe' : ∀ (γ : ↥Γ) (w : W), b (((π' γ : ↥H) : MulAut W) w) =
      Multiplicative.ofAdd
        ((((γ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (b w))) := by
    intro γ w
    have h := hbe γ w
    change b (((π' γ : ↥H) : MulAut W) w) =
      Multiplicative.ofAdd
        ((((γ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (b w))) at h ⊢
    exact h
  have hOm : StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1) = omegaMinusTwo m :=
    (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega m).symm
  let ψΩ : ↥(omegaMinusTwo m) →* ↥Γ :=
    (ψ.symm.toMonoidHom.comp (Subgroup.subtype (omegaMinusTwo m))).codRestrict Γ
      (fun g => (hψmem (ψ.symm (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)))).2 (by
        rw [MulEquiv.apply_symm_apply]
        exact hOm.symm ▸ g.2))
  have hψΩco : ∀ g : ↥(omegaMinusTwo m),
      ψ (ψΩ g : ↥Γ) = (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) := by
    intro g
    change ψ (ψ.symm (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))) = _
    rw [MulEquiv.apply_symm_apply]
  let ce : Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃*
      Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) := AddEquiv.toMultiplicative θ
  have hc : ∀ x : Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → K),
      Multiplicative.toAdd (ce x) = θ (Multiplicative.toAdd x) := by
    intro x
    simp [ce]
  let ρ : ↥(omegaMinusTwo m) →* MulAut W := H.subtype.comp (π'.comp ψΩ)
  let β : W →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) := ce.toMonoidHom.comp b
  refine ⟨ρ, β, fun g => (π' (ψΩ g)).2, fun x hx => ?_, ?_, ?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    let γ' : ↥Γ := γ
    have hγ' : π' γ' = ⟨x, hx⟩ := hγ
    let g : ↥(omegaMinusTwo m) :=
      ⟨ψ (γ' : GL (Fin m ⊕ Fin m ⊕ Fin 2) K),
        hOm ▸ (hψmem (γ' : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)).1 γ'.2⟩
    have hψΩg : ψΩ g = γ' := by
      apply Subtype.ext
      change ψ.symm (ψ (γ' : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) = (γ' : GL _ K)
      rw [MulEquiv.symm_apply_apply]
    refine ⟨g, ?_⟩
    have hπg : π' (ψΩ g) = ⟨x, hx⟩ := by rw [hψΩg, hγ']
    exact congrArg Subtype.val hπg
  · exact ce.surjective.comp (show Function.Surjective b from hbs)
  · intro w
    change ce (b w) = 1 ↔ w ∈ Z
    rw [ce.map_eq_one_iff]
    exact hbk w
  · intro g w
    have hbγ := hbe' (ψΩ g) w
    have hbγ' : Multiplicative.toAdd (b (((π' (ψΩ g) : ↥H) : MulAut W) w)) =
        ((ψΩ g : ↥Γ) : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd (b w) := by
      rw [hbγ]
      rfl
    show Multiplicative.toAdd (ce (b (((π' (ψΩ g) : ↥H) : MulAut W) w))) =
      ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (ce (b w))
    rw [hc, hbγ']
    have hθ := hconj (ψΩ g) (Multiplicative.toAdd (b w))
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at hθ
    rw [hθ, hψΩco g, hc (b w)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

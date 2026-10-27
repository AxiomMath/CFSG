module

public import CFSG.Quasithin.Background.Harris.L2.Cases
public import CFSG.Quasithin.Background.Harris.L2.Steinberg8Coord
public import CFSG.Quasithin.Background.Harris.L2.Steinberg8Tensor
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.ConjTransport
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups TensorProduct

local notation "K8" => GaloisField 2 3

section Descent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_steinberg_coord {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) (φ : ↥L ≃* SL(2, K8))
    (hD : Nat.card (EndRing (repOf L φ)) = 2)
    (hdim : Module.finrank (EndRing (repOf L φ)) V = 8) :
    ∃ ψ : (K8 ⊗[ZMod 2] V) ≃ₗ[K8] ((Fin 3 → Fin 2) → K8),
      ∀ (l : ↥L) (x : K8 ⊗[ZMod 2] V),
        ψ (LinearMap.baseChange K8 ((l : GLV V) : V →ₗ[ZMod 2] V) x) =
          tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) (φ l) (ψ x) := by
  classical
  have hFin : Fintype K8 := Fintype.ofFinite _
  have hF : Fintype.card K8 = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by omega)]
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hL⟩
  have hnt : Nontrivial SL(2, K8) := by
    refine ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩⟩
    have := congrArg (fun A : SL(2, K8) => (A : Matrix (Fin 2) (Fin 2) K8) 0 1) h
    simp at this
  have : Finite (EndRing (repOf L φ)) := finite_endRing (repOf L φ)
  have : Module.Finite (EndRing (repOf L φ)) V := Module.Finite.of_finite
  have : Fintype (EndRing (repOf L φ)) := Fintype.ofFinite _
  have hcard : Fintype.card (EndRing (repOf L φ)) = 2 := by
    rw [Fintype.card_eq_nat_card]; exact hD
  let e : ZMod 2 ≃+* EndRing (repOf L φ) := ZMod.ringEquivOfPrime _ Nat.prime_two hcard
  let ιD : EndRing (repOf L φ) →+* K8 := (ZMod.castHom (dvd_refl 2) K8).comp e.symm.toRingHom
  let b := Module.finBasis (EndRing (repOf L φ)) V
  have hm : Module.finrank (ZMod 2) V = Module.finrank (EndRing (repOf L φ)) V := by
    have := finrank_eq_mul_of_card (V := V) (D := EndRing (repOf L φ)) (d := 1) (by simpa using hD)
    simpa using this
  obtain ⟨J, -, hJn, ⟨Φ⟩, -, hJdim⟩ := descent_core (n := 3) (by norm_num) hF (repOf L φ)
    (repOf_nontrivial L φ) (d := 1) (by simpa using hD) b (RingHom.id K8) ιD
  have hJ : J = Finset.range 3 := by
    have hc : J.card = 3 := by
      have : 2 ^ J.card = 2 ^ 3 := by rw [← hJdim, hdim]; norm_num
      exact Nat.pow_right_injective le_rfl this
    refine Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_range.mpr (hJn i hi)) ?_
    rw [hc]; simp
  subst hJ
  let σ : ↥(Finset.range 3) ≃ Fin 3 :=
    { toFun := fun x => ⟨x.1, Finset.mem_range.mp x.2⟩
      invFun := fun i => ⟨i.1, by simp⟩
      left_inv := fun x => rfl
      right_inv := fun i => rfl }
  let R := reindexEquiv (F := K8) (k := K8) σ (fun i : ↥(Finset.range 3) => (i : ℕ))
    (fun i : Fin 3 => (i : ℕ)) (fun _ => rfl)
  have hbij := baseCoord_bijective b ιD hm
  let ψ₀ := LinearEquiv.ofBijective (baseCoord b ιD) hbij
  refine ⟨ψ₀.trans (Φ.toLinearEquiv.trans R.toLinearEquiv), fun l x => ?_⟩
  have h1 : ψ₀ (LinearMap.baseChange K8 ((l : GLV V) : V →ₗ[ZMod 2] V) x) =
      matRepE b ιD (φ l) (ψ₀ x) := by
    have : ((l : GLV V) : V →ₗ[ZMod 2] V) = repOf L φ (φ l) := by
      ext v; simp [repOf_apply]
    rw [this]
    exact baseCoord_rep b ιD (φ l) x
  simp only [LinearEquiv.trans_apply]
  rw [h1]
  exact (congrArg R (equiv_apply Φ (φ l) (ψ₀ x))).trans (equiv_apply R (φ l) (Φ (ψ₀ x)))

end Descent

section Models

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isL28_of_coord {L : Subgroup (GLV V)} (φ : ↥L ≃* SL(2, K8))
    (ψ : (K8 ⊗[ZMod 2] V) ≃ₗ[K8] ((Fin 3 → Fin 2) → K8))
    (hψ : ∀ (l : ↥L) (x : K8 ⊗[ZMod 2] V),
        ψ (LinearMap.baseChange K8 ((l : GLV V) : V →ₗ[ZMod 2] V) x) =
          tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) (φ l) (ψ x)) :
    IsL28TwistedTensorModule L := by
  obtain ⟨θ, hθ⟩ := exists_tensorN3_equiv
  refine ⟨φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K8),
    ψ.trans θ, fun l x => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [hψ]
  exact hθ (φ l) (ψ x)

end Models

section Dual

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_invariant {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] E)
    (hβ : ∀ l ∈ L, ∀ v w, β (l v) (l w) = β v w) (hne : ∃ v w, β v w ≠ 0) :
    SelfDual L ⊤ := by
  obtain ⟨v₀, w₀, h0⟩ := hne
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual (ZMod 2) E, lam (β v₀ w₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hcon)
  let f₀ : LinearMap.BilinForm (ZMod 2) V := β.compr₂ lam
  have hf₀ : ∀ l ∈ L, ∀ v w, f₀ (l v) (l w) = f₀ v w := fun l hl v w => by
    simp only [f₀, LinearMap.compr₂_apply, hβ l hl]
  have hinv : ∀ l ∈ L, ∀ w : V, (l : GLV V) ((l⁻¹ : GLV V) w) = w := fun l _ w => by simp
  have hirr := hL.2.2
  have hne₀ : f₀ v₀ w₀ ≠ 0 := hlam
  have hleft : ∀ v, (∀ w, f₀ v w = 0) → v = 0 := by
    let R : Submodule (ZMod 2) V := LinearMap.ker f₀
    have hR : Invariant L R := fun l hl v hv => by
      have hv' : ∀ w, f₀ v w = 0 := fun w => LinearMap.congr_fun hv w
      show f₀ (l v) = 0
      refine LinearMap.ext fun w => ?_
      have := hf₀ l hl v ((l⁻¹ : GLV V) w)
      rw [hinv l hl, hv'] at this
      simpa using this
    rcases hirr R hR bot_le le_top with h | h
    · intro v hv
      have : v ∈ R := LinearMap.ext hv
      rw [h] at this
      simpa using this
    · exfalso
      have hv : v₀ ∈ R := by rw [h]; trivial
      exact hne₀ (LinearMap.congr_fun hv w₀)
  have hright : ∀ w, (∀ v, f₀ v w = 0) → w = 0 := by
    let R : Submodule (ZMod 2) V := LinearMap.ker f₀.flip
    have hR : Invariant L R := fun l hl w hw => by
      have hw' : ∀ v, f₀ v w = 0 := fun v => LinearMap.congr_fun hw v
      show f₀.flip (l w) = 0
      refine LinearMap.ext fun v => ?_
      have := hf₀ l hl ((l⁻¹ : GLV V) v) w
      rw [hinv l hl, hw'] at this
      simpa using this
    rcases hirr R hR bot_le le_top with h | h
    · intro w hw
      have : w ∈ R := LinearMap.ext hw
      rw [h] at this
      simpa using this
    · exfalso
      have hw : w₀ ∈ R := by rw [h]; trivial
      exact hne₀ (LinearMap.congr_fun hw v₀)
  refine ⟨f₀.compl₁₂ (⊤ : Submodule (ZMod 2) V).subtype (⊤ : Submodule (ZMod 2) V).subtype,
    ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  · refine Subtype.ext (hleft x fun w => ?_)
    simpa using hx ⟨w, trivial⟩
  · refine Subtype.ext (hright y fun v => ?_)
    simpa using hy ⟨v, trivial⟩
  · intro k hk i j i' j' hi hj
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply]
    rw [← hi, ← hj]
    exact hf₀ k hk i j

end Dual

section Concrete

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def tfBil : ((Fin 3 → Fin 2) → K8) →ₗ[K8] ((Fin 3 → Fin 2) → K8) →ₗ[K8] K8 :=
  LinearMap.mk₂ K8 tensorForm
    (fun u u' v => by simp [tensorForm, add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [tensorForm, Finset.mul_sum, mul_assoc])
    (fun u v v' => by simp [tensorForm, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [tensorForm, Finset.mul_sum, mul_left_comm])

theorem tfBil_apply (u v : (Fin 3 → Fin 2) → K8) : tfBil u v = tensorForm u v := rfl

theorem tensorForm_single (a : Fin 3 → Fin 2) :
    tensorForm (Pi.single a (1 : K8)) (Pi.single (flipX (Fin 3) a) (1 : K8)) = 1 := by
  unfold tensorForm
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem exists_invariant_map {L : Subgroup (GLV V)} (φ : ↥L ≃* SL(2, K8))
    (ψ : (K8 ⊗[ZMod 2] V) ≃ₗ[K8] ((Fin 3 → Fin 2) → K8))
    (hψ : ∀ (l : ↥L) (x : K8 ⊗[ZMod 2] V),
        ψ (LinearMap.baseChange K8 ((l : GLV V) : V →ₗ[ZMod 2] V) x) =
          tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) (φ l) (ψ x)) :
    ∃ β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] K8, (∀ l ∈ L, ∀ v w, β (l v) (l w) = β v w) ∧
      ∃ v w, β v w ≠ 0 := by
  let c : V →ₗ[ZMod 2] ((Fin 3 → Fin 2) → K8) :=
    (ψ.toLinearMap.restrictScalars (ZMod 2)) ∘ₗ (TensorProduct.mk (ZMod 2) K8 V) 1
  have hc : ∀ v, c v = ψ ((1 : K8) ⊗ₜ v) := fun v => rfl
  let β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] K8 :=
    ((tfBil).restrictScalars₁₂ (ZMod 2) (ZMod 2)).compl₁₂ c c
  have hβ : ∀ v w, β v w = tensorForm (c v) (c w) := fun v w => rfl
  refine ⟨β, fun l hl v w => ?_, ?_⟩
  · have hcl : ∀ u, c (l u) = tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) (φ ⟨l, hl⟩) (c u) := by
      intro u
      rw [hc, hc, ← hψ ⟨l, hl⟩]
      rfl
    rw [hβ, hβ, hcl, hcl]
    exact tensorForm_invariant _ _ _ _
  · by_contra hcon
    push Not at hcon
    have hz : ∀ t t' : K8 ⊗[ZMod 2] V, tfBil (ψ t) (ψ t') = 0 := by
      intro t t'
      induction t using TensorProduct.inductionOn with
      | tmul e v =>
        induction t' using TensorProduct.inductionOn with
        | tmul e' w =>
          have h1 : ∀ (e : K8) (v : V), ψ (e ⊗ₜ v) = e • c v := fun e v => by
            rw [hc, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          have h0 : tfBil (c v) (c w) = 0 := by
            have := hcon v w
            rwa [hβ] at this
          rw [h1, h1]
          simp [h0]
        | add y z hy hz =>
          simp only [map_add, hy, hz, add_zero]
      | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
    have := hz (ψ.symm (Pi.single (fun _ => 0) 1)) (ψ.symm (Pi.single (flipX (Fin 3) fun _ => 0) 1))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, tfBil_apply,
      tensorForm_single] at this
    exact one_ne_zero this

end Concrete

section End

open CFSG.Quasithin CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem natCard_endCommutant {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) (φ : ↥L ≃* SL(2, K8)) :
    Nat.card (endCommutant L) = Nat.card (EndRing (repOf L φ)) := by
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hL⟩
  have hmem : ∀ f : Module.End (ZMod 2) V, f ∈ endCommutant L ↔
      ∀ g v, f (repOf L φ g v) = repOf L φ g (f v) := by
    intro f
    rw [mem_endCommutant_iff]
    constructor
    · intro hf g v
      have := LinearMap.congr_fun (hf (φ.symm g : ↥L) (φ.symm g).2) v
      simpa [repOf_apply] using this.symm
    · intro hf h hh
      refine LinearMap.ext fun v => ?_
      have := hf (φ ⟨h, hh⟩) v
      simpa [repOf_apply] using this.symm
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun ψ : EndRing (repOf L φ) => (⟨AddMonoidHom.toZModLinearMap 2 ψ.toAddMonoidHom, ?_⟩ :
      endCommutant L)) ⟨?_, ?_⟩)
  · rw [hmem]
    intro g v
    exact (mem_endRing_iff (repOf L φ) _).mp ⟨ψ, rfl⟩ g v
  · intro ψ ψ' h
    refine LinearMap.ext fun v => ?_
    exact LinearMap.congr_fun (congrArg Subtype.val h) v
  · rintro ⟨f, hf⟩
    obtain ⟨ψ, hψ⟩ := (mem_endRing_iff (repOf L φ) f).mpr ((hmem f).mp hf)
    exact ⟨ψ, Subtype.ext (LinearMap.ext fun v => by rw [← hψ]; rfl)⟩

theorem endIsField_one {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) (φ : ↥L ≃* SL(2, K8))
    (hD : Nat.card (EndRing (repOf L φ)) = 2) : EndIsField L 1 := by
  obtain ⟨e, ⟨α⟩⟩ := exists_endIsField hL
  have hc : Nat.card (GaloisField 2 e) = 2 ^ 1 := by
    rw [← Nat.card_congr α.toEquiv, natCard_endCommutant hL φ, hD]; simp
  exact ⟨α.trans (GaloisField.algEquivGaloisField 2 1 hc)⟩

end End

theorem case16_holds : Case16Input := by
  intro V _ _ _ Γ A L m hs φ hm hD hdim
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hs.L_irr⟩
  have : Finite (EndRing (repOf L φ)) := finite_endRing (repOf L φ)
  have hfin : Module.finrank (ZMod 2) V = 8 := by
    have := finrank_eq_mul_of_card (V := V) (D := EndRing (repOf L φ)) (d := 1) (by simpa using hD)
    rw [this, hdim]
  have hb := hs.bound
  rw [hfin] at hb
  have hm3 : m = 3 := by omega
  obtain ⟨ψ, hψ⟩ := exists_steinberg_coord hs.L_irr φ hD hdim
  obtain ⟨β, hβinv, hne⟩ := exists_invariant_map φ ψ hψ
  exact ⟨⟨hm3, hfin, isL28_of_coord φ ψ hψ⟩, endIsField_one hs.L_irr φ hD,
    selfDual_of_invariant hs.L_irr β hβinv hne⟩

end CFSG.Quasithin.G11.Harris.L2

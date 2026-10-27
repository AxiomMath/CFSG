module

public import CFSG.Quasithin.Background.Harris.G2.Setup
public import CFSG.Quasithin.Background.Harris.G2.Perfect

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Form

variable {K : Type} [Field K]

theorem bilQ_comm (w w' : Ix3 → K) : bilQ w w' = bilQ w' w := by
  simp only [bilQ]
  ring

theorem bilQ_add_right (w x x' : Ix3 → K) : bilQ w (x + x') = bilQ w x + bilQ w x' := by
  rw [bilQ_comm, bilQ_add_left, bilQ_comm x, bilQ_comm x']

theorem bilQ_smul_right (c : K) (w x : Ix3 → K) : bilQ w (c • x) = c * bilQ w x := by
  rw [bilQ_comm, bilQ_smul_left, bilQ_comm]

theorem eq_zero_of_bilQ {z : Ix3 → K} (h : ∀ w, bilQ z w = 0) : z = 0 :=
  eq_of_bilQ fun w => by rw [h, show bilQ (0 : Ix3 → K) w = 0 by simp [bilQ]]

variable [Algebra (ZMod 2) K]

@[expose] noncomputable def trBil : LinearMap.BilinForm (ZMod 2) (Ix3 → K) :=
  LinearMap.mk₂ (ZMod 2) (fun w w' => Algebra.trace (ZMod 2) K (bilQ w w'))
    (fun w w' x => by rw [bilQ_add_left, map_add])
    (fun c w x => by
      rw [show c • w = (algebraMap (ZMod 2) K c) • w from by ext i; simp [Algebra.smul_def],
        bilQ_smul_left, ← Algebra.smul_def, map_smul])
    (fun w x x' => by rw [bilQ_add_right, map_add])
    (fun c w x => by
      rw [show c • x = (algebraMap (ZMod 2) K c) • x from by ext i; simp [Algebra.smul_def],
        bilQ_smul_right, ← Algebra.smul_def, map_smul])

theorem trBil_apply (w w' : Ix3 → K) :
    trBil w w' = Algebra.trace (ZMod 2) K (bilQ w w') := rfl

theorem trBil_swap (w w' : Ix3 → K) : trBil w' w = trBil w w' := by
  rw [trBil_apply, trBil_apply, bilQ_comm]

variable [Finite K]

theorem trBil_separatingLeft : ∀ w : Ix3 → K, (∀ w', trBil w w' = 0) → w = 0 := by
  intro w hw
  apply eq_zero_of_bilQ
  intro x
  have hnd := (traceForm_nondegenerate (ZMod 2) K).1
  refine hnd _ fun b => ?_
  have := hw (b • x)
  rw [trBil_apply, bilQ_smul_right] at this
  simpa [Algebra.traceForm_apply, mul_comm] using this

theorem trBil_nondegenerate : (trBil (K := K)).Nondegenerate :=
  ⟨trBil_separatingLeft, fun y hy => trBil_separatingLeft y fun x => by
    rw [← trBil_swap, hy x]⟩

end Form


section Natural

variable {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
  {L : Subgroup (GLV V)} (φ : V ≃+ (Ix3 → K))

omit [Finite K] [Algebra (ZMod 2) K] in
theorem equivariant_apply (e : ↥L ≃* ↥(cayleyGroup K))
    (hφ : ∀ (g : ↥(cayleyGroup K)) (w : V), φ (repC L e g w) = g2Act g (φ w))
    (h : ↥L) (v : V) : φ ((h : GLV V) v) = g2Act (e h) (φ v) := by
  have := hφ (e h) v
  rwa [repC_apply, MulEquiv.symm_apply_apply] at this

theorem selfDual_of_equivariant (ε : ↥L → ↥(cayleyGroup K))
    (hφ : ∀ (h : ↥L) (v : V), φ ((h : GLV V) v) = g2Act (ε h) (φ v)) :
    CFSG.Quasithin.G11.SelfDual L ⊤ := by
  let ψ : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] (Ix3 → K) :=
    Submodule.topEquiv.trans (LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 φ.toAddMonoidHom)
      φ.symm φ.left_inv φ.right_inv)
  have hψ : ∀ x : ↥(⊤ : Submodule (ZMod 2) V), ψ x = φ (x : V) := fun x => rfl
  refine ⟨trBil.compl₁₂ ψ.toLinearMap ψ.toLinearMap, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    apply ψ.injective
    rw [map_zero]
    apply trBil_separatingLeft
    intro y
    simpa using hi (ψ.symm y)
  · intro j hj
    apply ψ.injective
    rw [map_zero]
    exact (trBil_nondegenerate (K := K)).2 (ψ j) fun x => by
      simpa using hj (ψ.symm x)
  · intro k hk i j i' j' hi hj
    have hki : ψ i' = g2Act (ε ⟨k, hk⟩) (ψ i) := by
      rw [hψ, hψ, ← hi]
      exact hφ ⟨k, hk⟩ (i : V)
    have hkj : ψ j' = g2Act (ε ⟨k, hk⟩) (ψ j) := by
      rw [hψ, hψ, ← hj]
      exact hφ ⟨k, hk⟩ (j : V)
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hki, hkj, trBil_apply, trBil_apply, bilQ_g2Act]

omit [Finite K] in
theorem isG2NaturalModule_of_equivariant {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hG₀ : G₀ ≤ cayleyGroup K) (e' : ↥L ≃* ↥G₀)
    (hφ : ∀ (h : ↥L) (v : V),
      φ ((h : GLV V) v) = g2Act ⟨(e' h : quasithinZorn K ≃ₗ[K] quasithinZorn K), hG₀ (e' h).2⟩
        (φ v)) :
    IsG2NaturalModule L G₀ := by
  let piAdd : quasithinZorn K →+ V := φ.symm.toAddMonoidHom.comp (AddMonoidHom.mk' zP zP_add)
  have hpi : ∀ x, AddMonoidHom.toZModLinearMap 2 piAdd x = φ.symm (zP x) := fun x => rfl
  refine ⟨e', AddMonoidHom.toZModLinearMap 2 piAdd, fun v => ?_, fun x hx => ?_, fun h x hx => ?_⟩
  · refine ⟨zI (φ v), by simp [zI, zmk], ?_⟩
    rw [hpi, zP_zI, AddEquiv.symm_apply_apply]
  · rw [hpi]
    constructor
    · intro h0
      have h1 : zP x = 0 := by
        have := congrArg φ h0
        rwa [AddEquiv.apply_symm_apply, map_zero] at this
      have hu : x.2.1 = 0 := funext fun i => by
        have := congrFun h1 (.inl i)
        fin_cases i <;> simpa [zP, q6] using this
      have hv : x.2.2.1 = 0 := funext fun i => by
        have := congrFun h1 (.inr i)
        fin_cases i <;> simpa [zP, q6] using this
      have hs : x.2.2.2 = x.1 := by
        have : x.2.2.2 = -x.1 := eq_neg_of_add_eq_zero_right hx
        rw [this, CharTwo.neg_eq]
      exact ⟨x.1, Prod.ext rfl (Prod.ext hu (Prod.ext hv hs))⟩
    · rintro ⟨c, rfl⟩
      have h1 : zP ((c, 0, 0, c) : quasithinZorn K) = 0 := by
        funext i
        rcases i with i | i <;> fin_cases i <;> rfl
      rw [h1, map_zero]
  · have hx' : cayleyTr x = 0 := hx
    have h1 : zP (cgE ⟨(e' h : quasithinZorn K ≃ₗ[K] quasithinZorn K), hG₀ (e' h).2⟩ x) =
        g2Act ⟨(e' h : quasithinZorn K ≃ₗ[K] quasithinZorn K), hG₀ (e' h).2⟩ (zP x) :=
      g2_zP_apply _ x hx'
    rw [hpi, hpi]
    show φ.symm (zP (cgE ⟨(e' h : quasithinZorn K ≃ₗ[K] quasithinZorn K), hG₀ (e' h).2⟩ x)) = _
    rw [h1]
    apply φ.injective
    rw [AddEquiv.apply_symm_apply, hφ h, AddEquiv.apply_symm_apply]

theorem isG2NaturalModule_of_natural [IsSimpleGroup ↥L] (hK : 4 ≤ Nat.card K)
    (e : ↥L ≃* ↥(cayleyGroup K))
    (hφ : ∀ (g : ↥(cayleyGroup K)) (w : V), φ (repC L e g w) = g2Act g (φ w)) :
    IsG2NaturalModule L ⁅quasithinG2 K, quasithinG2 K⁆ := by
  have hq : quasithinG2 K = cayleyGroup K := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  have : IsSimpleGroup ↥(cayleyGroup K) := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  have hG0 : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [hq]
    exact commutator_cayleyGroup_eq hK
  refine isG2NaturalModule_of_equivariant φ hG0.le (e.trans (MulEquiv.subgroupCongr hG0.symm))
    fun h v => ?_
  exact equivariant_apply φ e hφ h v

end Natural

end CFSG.Quasithin.G11.Harris.G2

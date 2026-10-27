module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma dlift_dBasis_zero (n : ℕ) :
    dBasis (n + 1) 0 = (Fin.cons 1 (0 : DVec n) : DVec (n + 1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [dBasis, Pi.basisFun_apply, Pi.single_apply]
  · have hne : (0 : Fin (n + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hne]

private lemma dlift_dBasis_succ (n : ℕ) (i : Fin n) :
    dBasis (n + 1) i.succ = (Fin.cons 0 (dBasis n i) : DVec (n + 1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have hne : i.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero i
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hne]
  · simp [dBasis, Pi.basisFun_apply, Pi.single_apply, Fin.succ_inj]

private lemma dlift_cons_smul (n : ℕ) (c : ZMod 3) (v : DVec n) :
    (Fin.cons 0 (c • v) : DVec (n + 1)) = c • (Fin.cons 0 v : DVec (n + 1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [Pi.smul_apply]

@[expose] noncomputable def dLift (n : ℕ) (g : DVec n ≃ₗ[ZMod 3] DVec n) :
    DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1) where
  toFun v := Fin.cons (v 0) (g (Fin.tail v))
  invFun v := Fin.cons (v 0) (g.symm (Fin.tail v))
  map_add' v w := by
    have h : Fin.tail (v + w) = Fin.tail v + Fin.tail w := rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [h, map_add]
  map_smul' c v := by
    have h : Fin.tail (c • v) = c • Fin.tail v := rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [h, map_smul]
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.tail]
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.tail]

theorem dLift_apply (n : ℕ) (g : DVec n ≃ₗ[ZMod 3] DVec n) (v : DVec (n + 1)) :
    dLift n g v = Fin.cons (v 0) (g (Fin.tail v)) := rfl

theorem dLift_mul (n : ℕ) (g h : DVec n ≃ₗ[ZMod 3] DVec n) :
    dLift n (g * h) = dLift n g * dLift n h := by
  refine LinearEquiv.ext fun v => ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [dLift_apply]
  · simp [dLift_apply, LinearEquiv.mul_apply, Fin.tail_cons]

theorem dLift_one (n : ℕ) : dLift n 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [dLift_apply, Fin.tail]

theorem dLift_injective (n : ℕ) : Function.Injective (dLift n) := by
  intro g h hgh
  refine LinearEquiv.ext fun w => ?_
  funext j
  have h2 := congrFun (congrArg (fun e => e (Fin.cons 0 w)) hgh) j.succ
  simpa [dLift_apply, Fin.tail_cons] using h2

theorem dLift_basis_zero (n : ℕ) (g : DVec n ≃ₗ[ZMod 3] DVec n) :
    dLift n g (dBasis (n + 1) 0) = dBasis (n + 1) 0 := by
  rw [dLift_apply, dlift_dBasis_zero n]
  simp [Fin.tail_cons]

theorem dLift_basis_succ (n : ℕ) (g : DVec n ≃ₗ[ZMod 3] DVec n) (i : Fin n) :
    dLift n g (dBasis (n + 1) i.succ) = Fin.cons 0 (g (dBasis n i)) := by
  rw [dLift_apply, dlift_dBasis_succ n i]
  simp [Fin.tail_cons]

theorem dLift_mem_dEvenStab (n : ℕ) {g : DVec n ≃ₗ[ZMod 3] DVec n} (hg : g ∈ dEven n) :
    dLift n g ∈ dEvenStab (n + 1) (dBasis (n + 1) 0) := by
  refine ⟨?_, dLift_basis_zero n g⟩
  obtain ⟨σ, c, hc, hprod, hact⟩ := hg
  refine ⟨Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), σ), Fin.cons 1 c, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · left; rfl
    · exact hc j
  · rw [Fin.prod_univ_succ]
    simp [Fin.cons_succ, hprod]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [dLift_basis_zero n g, Equiv.Perm.decomposeFin_symm_apply_zero]
      simp
    · rw [dLift_basis_succ n g j, hact j, Fin.cons_succ,
        Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
        dlift_dBasis_succ n (σ j), dlift_cons_smul]

theorem exists_dLift_of_mem_dEvenStab (n : ℕ) {w : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)}
    (hw : w ∈ dEvenStab (n + 1) (dBasis (n + 1) 0)) : ∃ g ∈ dEven n, dLift n g = w := by
  obtain ⟨⟨σ, c, hc, hprod, hact⟩, hfix⟩ := hw
  have h0eq : c 0 • dBasis (n + 1) (σ 0) = dBasis (n + 1) 0 := by
    rw [← hact 0, hfix]
  have hval : c 0 * (if (0 : Fin (n + 1)) = σ 0 then 1 else 0) = 1 := by
    have h := congrFun h0eq 0
    simpa [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_apply] using h
  have hσ0 : σ 0 = 0 := by
    by_contra hne
    have h := hval
    rw [if_neg (fun hh => hne hh.symm), mul_zero] at h
    exact zero_ne_one h
  have hc0 : c 0 = 1 := by
    have h := hval
    rw [hσ0] at h
    simpa using h
  obtain ⟨p, σ₁, hpσ⟩ : ∃ p : Fin (n + 1), ∃ σ₁ : Equiv.Perm (Fin n),
      Equiv.Perm.decomposeFin σ = (p, σ₁) := ⟨_, _, rfl⟩
  have hsymm : Equiv.Perm.decomposeFin.symm (p, σ₁) = σ := by
    rw [← hpσ]
    exact Equiv.symm_apply_apply _ _
  have hp : p = 0 := by
    have h := Equiv.Perm.decomposeFin_symm_apply_zero p σ₁
    rw [hsymm, hσ0] at h
    exact h.symm
  subst p
  have hσ₁ : ∀ i : Fin n, σ i.succ = (σ₁ i).succ := by
    intro i
    have h := Equiv.Perm.decomposeFin_symm_apply_succ σ₁ (0 : Fin (n + 1)) i
    rw [hsymm, Equiv.swap_self, Equiv.refl_apply] at h
    exact h
  let u : Fin n → (ZMod 3)ˣ := fun i => if c i.succ = 1 then 1 else -1
  have hu : ∀ i : Fin n, (u i : ZMod 3) = c i.succ := by
    intro i
    by_cases h : c i.succ = 1
    · rw [show u i = 1 by simp [u, h], h]
      rfl
    · rcases hc i.succ with h1 | h1
      · exact absurd h1 h
      · rw [show u i = -1 by simp [u, h], h1]
        simp
  have hprod' : (∏ i : Fin n, c i.succ) = 1 := by
    have h := Fin.prod_univ_succ c
    rw [hprod, hc0, one_mul] at h
    exact h.symm
  let g : DVec n ≃ₗ[ZMod 3] DVec n :=
    ZS.diagMap 3 (dBasis n) (u ∘ σ₁.symm) * dPerm n σ₁
  have hgact : ∀ i : Fin n, g (dBasis n i) = (u i : ZMod 3) • dBasis n (σ₁ i) := by
    intro i
    rw [show g = ZS.diagMap 3 (dBasis n) (u ∘ σ₁.symm) * dPerm n σ₁ from rfl,
      LinearEquiv.mul_apply, dPerm_apply, ZS.diagMap_apply_basis, Function.comp_apply,
      Equiv.symm_apply_apply]
  have hgmem : g ∈ dEven n := by
    refine ⟨σ₁, fun i => (u i : ZMod 3), ?_, ?_, hgact⟩
    · intro i
      have hui : u i = 1 ∨ u i = -1 := by
        by_cases h : c i.succ = 1
        · left; simp [u, h]
        · right; simp [u, h]
      rcases hui with h | h
      · left
        show (u i : ZMod 3) = 1
        simp [h]
      · right
        show (u i : ZMod 3) = -1
        simp [h]
    · rw [show (∏ i : Fin n, (u i : ZMod 3)) = ∏ i : Fin n, c i.succ from
        Finset.prod_congr rfl fun i _ => hu i, hprod']
  refine ⟨g, hgmem, ?_⟩
  refine (dBasis (n + 1)).ext' fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [dLift_basis_zero n g, hfix]
  · rw [dLift_basis_succ n g j, hgact j, dlift_cons_smul, ← dlift_dBasis_succ n (σ₁ j),
      hact j.succ, hσ₁ j, hu j]

theorem dLift_dTau (n : ℕ) (ε : Bool) {a b : Fin n} (hab : a ≠ b) :
    dLift n (dTau n ε a b) = dTau (n + 1) ε a.succ b.succ := by
  refine (dBasis (n + 1)).ext' fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [dLift_basis_zero n (dTau n ε a b),
      dTau_apply_of_ne (n + 1) ε (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]
  · rw [dLift_basis_succ n (dTau n ε a b) j, dTau_basis n ε hab j,
      dTau_basis (n + 1) ε (fun h => hab (Fin.succ_injective n h)) j.succ]
    simp only [Fin.succ_inj]
    rw [Function.Injective.swap_apply (Fin.succ_injective n), dlift_cons_smul,
      ← dlift_dBasis_succ n (Equiv.swap a b j)]

@[expose] noncomputable def dLiftHom (n : ℕ) :
    dEven n →* ↥(dEvenStab (n + 1) (dBasis (n + 1) 0)) where
  toFun g := ⟨dLift n (g : DVec n ≃ₗ[ZMod 3] DVec n), dLift_mem_dEvenStab n g.2⟩
  map_one' := Subtype.ext (dLift_one n)
  map_mul' g h := Subtype.ext (dLift_mul n g h)

@[expose] noncomputable def dLiftEquiv (n : ℕ) :
    dEven n ≃* ↥(dEvenStab (n + 1) (dBasis (n + 1) 0)) :=
  MulEquiv.ofBijective (dLiftHom n)
    ⟨fun g h hgh => Subtype.ext (dLift_injective n (congrArg Subtype.val hgh)),
      fun w => by
        obtain ⟨g, hg, hgw⟩ := exists_dLift_of_mem_dEvenStab n w.2
        exact ⟨⟨g, hg⟩, Subtype.ext hgw⟩⟩

theorem dLiftEquiv_apply (n : ℕ) (g : dEven n) :
    (((dLiftEquiv n g : ↥(dEvenStab (n + 1) (dBasis (n + 1) 0))) :
      DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1))) = dLift n (g : DVec n ≃ₗ[ZMod 3] DVec n) := rfl

end CFSG.StandardType.QTwo

end

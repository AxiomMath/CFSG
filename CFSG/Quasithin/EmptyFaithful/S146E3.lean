module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F6Examples
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Quotient

variable {G : Type*} [Group G] [Finite G]

theorem nonempty_oTwoQuot_equiv_perm_three (X : Subgroup G) (Θ : ↥X →* Equiv.Perm (Fin 3))
    (hs : Function.Surjective Θ) (hk : ∀ x : ↥X, Θ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hker : CFSG.Open.pCore 2 ↥X = Θ.ker := by
    refine le_antisymm ?_ ?_
    · set N := CFSG.Open.pCore 2 ↥X with hN
      have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hNp : IsPGroup 2 N := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      have hmapn : (N.map Θ).Normal := Subgroup.Normal.map hNn Θ hs
      have hmapp : IsPGroup 2 ↥(N.map Θ) := hNp.map Θ
      have hle : N.map Θ ≤ CFSG.Open.pCore 2 (Equiv.Perm (Fin 3)) :=
        le_pCore 2 hmapn hmapp
      rw [F6.pCore_perm_three_eq_bot, le_bot_iff] at hle
      intro n hn
      have h1 : Θ n ∈ N.map Θ := Subgroup.mem_map_of_mem Θ hn
      rw [hle, Subgroup.mem_bot] at h1
      exact h1
    · refine le_pCore 2 (MonoidHom.normal_ker Θ) ?_
      intro n
      obtain ⟨k, hk'⟩ := hk n.1 n.2
      exact ⟨k, Subtype.ext (by simpa using hk')⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hs)⟩

end Quotient

namespace L3Stab

open CFSG.Quasithin.L3 CFSG.SectionRank.Ccomm

def e1 : Vec := ![1, 0, 0]

def rep (i : Fin 3) : Vec := ![![0, 1, 0], ![0, 0, 1], ![0, 1, 1]] i

def idx (v : Vec) : Fin 3 :=
  if v 1 = 1 ∧ v 2 = 0 then 0 else if v 1 = 0 ∧ v 2 = 1 then 1 else 2

def theta (g : Γ) (i : Fin 3) : Fin 3 := idx (act g (rep i))

theorem theta_bij : ∀ g : Γ, act g e1 = e1 → Function.Bijective (theta g) := by
  decide +kernel

theorem theta_mul : ∀ g h : Γ, act g e1 = e1 → act h e1 = e1 →
    ∀ i, theta (g * h) i = theta g (theta h i) := by
  decide +kernel

theorem theta_surj : ∀ π : Equiv.Perm (Fin 3), ∃ g : Γ, act g e1 = e1 ∧ ∀ i, theta g i = π i := by
  decide +kernel

theorem theta_ker : ∀ g : Γ, act g e1 = e1 → (∀ i, theta g i = i) → g * g = 1 := by
  decide +kernel

theorem theta_one : ∀ i, theta 1 i = i := by decide +kernel

@[expose] def stab1 : Subgroup Γ where
  carrier := {g | act g e1 = e1}
  one_mem' := act_one e1
  mul_mem' := by
    intro a b ha hb
    show act (a * b) e1 = e1
    rw [act_mul]
    have ha' : act a e1 = e1 := ha
    have hb' : act b e1 = e1 := hb
    rw [hb', ha']
  inv_mem' := by
    intro a ha
    show act a⁻¹ e1 = e1
    have ha' : act a e1 = e1 := ha
    conv_lhs => rw [← ha']
    exact act_inv_act a e1

theorem mem_stab1 {g : Γ} : g ∈ stab1 ↔ act g e1 = e1 := Iff.rfl

@[expose] noncomputable def thetaEquiv (g : ↥stab1) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (theta g.1) (theta_bij g.1 g.2)

theorem thetaEquiv_apply (g : ↥stab1) (i : Fin 3) : thetaEquiv g i = theta g.1 i := rfl

@[expose] noncomputable def thetaHom : ↥stab1 →* Equiv.Perm (Fin 3) where
  toFun := thetaEquiv
  map_one' := Equiv.ext fun i => by
    rw [thetaEquiv_apply]
    exact theta_one i
  map_mul' g h := Equiv.ext fun i => by
    rw [Equiv.Perm.mul_apply, thetaEquiv_apply, thetaEquiv_apply, thetaEquiv_apply]
    exact theta_mul g.1 h.1 g.2 h.2 i

theorem thetaHom_apply (g : ↥stab1) (i : Fin 3) : thetaHom g i = theta g.1 i := rfl

theorem thetaHom_surjective : Function.Surjective thetaHom := by
  intro π
  obtain ⟨g, hg, hπ⟩ := theta_surj π
  refine ⟨⟨g, hg⟩, Equiv.ext fun i => ?_⟩
  rw [thetaHom_apply]
  exact hπ i

theorem sq_eq_one_of_thetaHom_eq_one (g : ↥stab1) (h : thetaHom g = 1) : g.1 * g.1 = 1 :=
  theta_ker g.1 g.2 fun i => by
    have := congrArg (fun π : Equiv.Perm (Fin 3) => π i) h
    simpa [thetaHom_apply] using this

theorem e1_ne_zero : e1 ≠ 0 := by decide

theorem slEquivGL_coe (γ : Γ) :
    ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = (γ : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem exists_theta_of_stabilizer {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 8)
    {w : W} (hw : w ≠ 1) (A : Subgroup (MulAut W)) (hA : ∀ σ : MulAut W, σ ∈ A ↔ σ w = w) :
    ∃ Θ : ↥A →* Equiv.Perm (Fin 3), Function.Surjective Θ ∧
      ∀ σ : ↥A, Θ σ = 1 → σ.1 * σ.1 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq (n := 3)
    (by rw [hcard]; norm_num)
  set v : Vec := Multiplicative.toAdd (e₀ w) with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply hw
    apply e₀.injective
    rw [map_one]
    exact toAdd_eq_zero.mp h
  obtain ⟨γ, hγ⟩ := act_trans v e1 hv0 e1_ne_zero
  let τ : MulAut (Multiplicative Vec) :=
    (mulAutEquivGL (p := 2) 3).symm (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ)
  have hτ : ∀ x : Multiplicative Vec,
      Multiplicative.toAdd (τ x) = act γ (Multiplicative.toAdd x) := by
    intro x
    have h := mulAutEquivGL_mulVec (p := 2) 3 τ (Multiplicative.toAdd x)
    rw [ofAdd_toAdd] at h
    have h2 : mulAutEquivGL (p := 2) 3 τ = CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ :=
      (mulAutEquivGL (p := 2) 3).apply_symm_apply _
    rw [h2, slEquivGL_coe] at h
    exact h.symm
  let e : W ≃* Multiplicative Vec := e₀.trans τ
  have hew : Multiplicative.toAdd (e w) = e1 := by
    show Multiplicative.toAdd (τ (e₀ w)) = e1
    rw [hτ]
    exact hγ
  let Φ : MulAut W ≃* Γ :=
    (elemAutEquivGL e).trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm
  have hΦ : ∀ (σ : MulAut W) (x : W),
      act (Φ σ) (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e (σ x)) := by
    intro σ x
    have h := elemAutEquivGL_mulVec e σ x
    have h2 : CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 (Φ σ) = elemAutEquivGL e σ :=
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).apply_symm_apply _
    rw [← h, ← h2, slEquivGL_coe]
    rfl
  have hmemA : ∀ σ : ↥A, Φ σ.1 ∈ stab1 := by
    intro σ
    show act (Φ σ.1) e1 = e1
    rw [← hew, hΦ, (hA σ.1).mp σ.2]
  let Φ' : ↥A →* ↥stab1 := (Φ.toMonoidHom.comp A.subtype).codRestrict stab1 hmemA
  refine ⟨thetaHom.comp Φ', ?_, ?_⟩
  · have hΦ'surj : Function.Surjective Φ' := by
      intro g
      refine ⟨⟨Φ.symm g.1, (hA _).mpr ?_⟩, ?_⟩
      · apply e.injective
        apply Multiplicative.toAdd.injective
        rw [← hΦ, MulEquiv.apply_symm_apply, hew]
        exact g.2
      · apply Subtype.ext
        show Φ (Φ.symm g.1) = g.1
        exact Φ.apply_symm_apply _
    exact thetaHom_surjective.comp hΦ'surj
  · intro σ hσ
    have h1 : thetaHom (Φ' σ) = 1 := hσ
    have h2 := sq_eq_one_of_thetaHom_eq_one (Φ' σ) h1
    have h3 : Φ (σ.1 * σ.1) = 1 := by
      rw [map_mul]
      exact h2
    exact Φ.map_eq_one_iff.mp h3

end L3Stab

end CFSG.Quasithin

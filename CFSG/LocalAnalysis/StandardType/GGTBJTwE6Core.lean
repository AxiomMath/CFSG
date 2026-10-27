module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Class
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Roots
public import CFSG.LocalAnalysis.StandardType.GGTBJReflPlain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

section Refl


theorem ggTBJTwE6_excRefl_add {p : ℕ} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (t t' : Fin Tag.E6.rank → ZMod p) :
    ExcSplitRootGen.excRefl (p := p) γ (t + t') =
      ExcSplitRootGen.excRefl (p := p) γ t + ExcSplitRootGen.excRefl (p := p) γ t' := by
  rw [ggTBJTwE6_excRefl_eq hγ, ggTBJTwE6_excRefl_eq hγ, ggTBJTwE6_excRefl_eq hγ]
  have hf : ggTBJTwE6Fun p γ (t + t') = ggTBJTwE6Fun p γ t + ggTBJTwE6Fun p γ t' := by
    simp only [ggTBJTwE6Fun, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hf, add_smul]
  abel

@[expose] noncomputable def ggTBJTwE6ReflAut (p : ℕ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod p)) where
  toFun f := Multiplicative.ofAdd (ExcSplitRootGen.excRefl (p := p) γ (Multiplicative.toAdd f))
  invFun f := Multiplicative.ofAdd (ExcSplitRootGen.excRefl (p := p) γ (Multiplicative.toAdd f))
  left_inv f := by simp [ExcSplitRootGen.excRefl_excRefl hγ]
  right_inv f := by simp [ExcSplitRootGen.excRefl_excRefl hγ]
  map_mul' f g := by
    simp only [toAdd_mul]
    rw [ggTBJTwE6_excRefl_add hγ, ofAdd_add]

theorem ggTBJTwE6ReflAut_apply (p : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (f : Multiplicative (Fin Tag.E6.rank → ZMod p)) :
    ggTBJTwE6ReflAut p hγ f =
      Multiplicative.ofAdd (ExcSplitRootGen.excRefl (p := p) γ (Multiplicative.toAdd f)) :=
  rfl

theorem ggTBJTwE6ReflAut_sq (p : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggTBJTwE6ReflAut p hγ ^ 2 = 1 := by
  apply MulEquiv.ext
  intro f
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply, ggTBJTwE6ReflAut_apply,
    ggTBJTwE6ReflAut_apply, toAdd_ofAdd, ExcSplitRootGen.excRefl_excRefl hγ, ofAdd_toAdd]

theorem ggTBJTwE6ReflAut_card_fix (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nat.card {f // ggTBJTwE6ReflAut p hγ f = f} * p = p ^ 6 := by
  have h := ExcSplitRootGen.card_fix_excRefl (p := p) hp2 hγ
  have he : Nat.card {f // ggTBJTwE6ReflAut p hγ f = f} =
      Nat.card {t // ExcSplitRootGen.excRefl (p := p) γ t = t} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun f => ?_)
    rw [ggTBJTwE6ReflAut_apply]
    constructor
    · intro hf
      have := congrArg Multiplicative.toAdd hf
      simpa using this
    · intro hf
      apply Multiplicative.toAdd.injective
      simpa using hf
  rw [he, h]
  rfl

end Refl


theorem ggTBJ_twE6_core
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ}
    (hTinj : Function.Injective T)
    (hT : ∀ t : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd t)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (σ' : Multiplicative (Fin Tag.E6.rank → ZMod p) →* L') (hσ' : ∀ f, ψ (σ' f) = T f)
    (f₀ : Multiplicative (Fin Tag.E6.rank → ZMod p)) (hf₀ : f₀ ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ' f₀} : Set L')))
    (hJl : ∀ Q : Subgroup L',
      CFSG.Open.IsComponentOf Q (Subgroup.centralizer ({σ' f₀} : Set L')) → Q ≤ J)
    (hcount : p ^ 2 * Nat.card {f : Multiplicative (Fin Tag.E6.rank → ZMod p) //
      ∀ j ∈ J, σ' f * j = j * σ' f} ≤ p ^ 6) :
    ∃ (m₁ m₂ : L') (s₁ s₂ : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod p))),
      m₁ ∈ J ∧ m₂ ∈ J ∧
      (∀ f, ψ m₁ * ψ (σ' f) * (ψ m₁)⁻¹ = ψ (σ' (s₁ f))) ∧
      (∀ f, ψ m₂ * ψ (σ' f) * (ψ m₂)⁻¹ = ψ (σ' (s₂ f))) ∧
      s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f // s₁ f = f} * p = p ^ 6 ∧ Nat.card {f // s₂ f = f} * p = p ^ 6 ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set t₀ : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd f₀ with ht₀def
  have ht₀ : t₀ ≠ 0 := by
    intro h
    apply hf₀
    apply Multiplicative.toAdd.injective
    rw [← ht₀def, h]
    rfl
  have hu : ψ (σ' f₀) = T (Multiplicative.ofAdd t₀) := by rw [hσ']; rfl
  have hY : Function.Injective (ggKGTwY F) := by
    intro x x' hxx'
    rw [ggKGTwY_apply, ggKGTwY_apply] at hxx'
    exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      (mul_left_cancel (mul_right_cancel hxx')))
  have hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1 := by
    intro h
    apply ht₀
    have h1 : T (Multiplicative.ofAdd t₀) = 1 := hY (by rw [hT, map_one]; exact h)
    have h2 := hTinj (h1.trans (map_one T).symm)
    simpa using congrArg Multiplicative.toAdd h2
  have hy : ∀ l, ggKGTwY F (ψ (MulAut.conj (σ' f₀) l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) * ggKGTwY F (ψ l) *
        (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))⁻¹ := by
    intro l
    simp only [MulAut.conj_apply, map_mul, map_inv, hu, hT]
  obtain ⟨i, hJγ, hfixJ⟩ := ggTBJ_twE6_class hn hK hσ hpq F hv hζ ψ hψ hker t₀ hd1
    (MulAut.conj (σ' f₀)) hy (by rw [ggTBJ_fixSubgroup_conj]; exact hJ)
    (by rw [ggTBJ_fixSubgroup_conj]; exact hJl)
  have hW : ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
      ∃ m ∈ J, ggKGTwY F (ψ m) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) := by
    intro γ hγ
    obtain ⟨r, hrJ, hr⟩ := ggKGTwJ_weyl hK hσ F hv (isRoot_of_mem_componentRoots hγ)
    obtain ⟨m, hm, hmr⟩ := hJγ γ hγ r hrJ
    exact ⟨m, hm, by rw [hmr]; exact hr⟩
  have hker' : ∀ (l : L') (t : Fin Tag.E6.rank → ZMod p), ψ l = T (Multiplicative.ofAdd t) →
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∑ j, (γ j : ZMod p) * t j = 0) →
      ∀ x ∈ J, l * x = x * l := by
    intro l t hl ht x hx
    have h := hfixJ (MulAut.conj l) t
      (fun k => by simp only [MulAut.conj_apply, map_mul, map_inv, hl, hT]) ht x hx
    rw [MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  let ι := {β : Fin Tag.E6.rank → ℤ //
    β ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i}
  haveI : Nonempty ι := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep i
    exact ⟨⟨a.1, ⟨a.2, ha⟩⟩⟩
  have hroot : ∀ a : ι, IsRoot Tag.E6 a.1 := fun a => isRoot_of_mem_componentRoots a.2
  let f : ι → (Fin Tag.E6.rank → ZMod p) → ZMod p := fun a w => ggTBJTwE6Fun p a.1 w
  let v : ι → (Fin Tag.E6.rank → ZMod p) := fun a => ggTBJTwE6Vec p a.1
  have hfv : ∀ a, f a (v a) = 2 := fun a => ggTBJTwE6_fun_vec_self p (hroot a)
  have hadd : ∀ a (x y : Fin Tag.E6.rank → ZMod p), f a (x + y) = f a x + f a y := by
    intro a x y
    simp only [f, ggTBJTwE6Fun, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsmul : ∀ a (c : ZMod p) (x : Fin Tag.E6.rank → ZMod p), f a (c • x) = c * f a x := by
    intro a c x
    simp only [f, ggTBJTwE6Fun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hconn : ∀ S : Set ι, S.Nonempty →
      (∀ a b, (f a (v b) ≠ 0 ∨ f b (v a) ≠ 0) → (a ∈ S ↔ b ∈ S)) → S = Set.univ := by
    intro S hSne hSclosed
    let S' : Set (Fin Tag.E6.rank → ℤ) := (fun a : ι => (a : Fin Tag.E6.rank → ℤ)) '' S
    have hS'sub : S' ⊆ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i := by
      rintro β ⟨a, -, rfl⟩
      exact a.2
    have hS'ne : S'.Nonempty := by
      obtain ⟨a, ha⟩ := hSne
      exact ⟨(a : Fin Tag.E6.rank → ℤ), ⟨a, ha, rfl⟩⟩
    have hS'closed : ∀ β ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ((corootPair (τ := Tag.E6) γ β : ZMod p) ≠ 0 ∨
          (corootPair (τ := Tag.E6) β γ : ZMod p) ≠ 0) →
        (β ∈ S' ↔ γ ∈ S') := by
      intro β hβ γ hγ hpr
      have key : ∀ (δ : Fin Tag.E6.rank → ℤ)
          (hδ : δ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i),
          (δ ∈ S' ↔ (⟨δ, hδ⟩ : ι) ∈ S) := by
        intro δ hδ
        constructor
        · rintro ⟨a, ha, hae⟩
          have hEq : a = ⟨δ, hδ⟩ := Subtype.ext hae
          rwa [hEq] at ha
        · intro h
          exact ⟨⟨δ, hδ⟩, h, rfl⟩
      rw [key β hβ, key γ hγ]
      refine hSclosed ⟨β, hβ⟩ ⟨γ, hγ⟩ ?_
      have e1 : f ⟨β, hβ⟩ (v ⟨γ, hγ⟩) = (corootPair (τ := Tag.E6) γ β : ZMod p) :=
        ggTBJTwE6_fun_vec p (isRoot_of_mem_componentRoots hγ)
      have e2 : f ⟨γ, hγ⟩ (v ⟨β, hβ⟩) = (corootPair (τ := Tag.E6) β γ : ZMod p) :=
        ggTBJTwE6_fun_vec p (isRoot_of_mem_componentRoots hβ)
      rw [e1, e2]
      exact hpr
    have hSuniv := ggTBJ_e6_connected hp hp2 i S' hS'sub hS'ne hS'closed
    refine Set.eq_univ_of_forall fun a => ?_
    have ha : (a : Fin Tag.E6.rank → ℤ) ∈ S' := by
      rw [hSuniv]
      exact a.2
    obtain ⟨b, hb, hba⟩ := ha
    have hEq : b = a := Subtype.ext hba
    rwa [hEq] at hb
  have hV : Nat.card (Fin Tag.E6.rank → ZMod p) = p ^ 6 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hcard : p ^ 2 * Nat.card {w : Fin Tag.E6.rank → ZMod p // ∀ a, f a w = 0} ≤
      Nat.card (Fin Tag.E6.rank → ZMod p) := by
    rw [hV]
    have hmap : ∀ w : {w : Fin Tag.E6.rank → ZMod p // ∀ a, f a w = 0}, ∀ j ∈ J,
        σ' (Multiplicative.ofAdd (w : Fin Tag.E6.rank → ZMod p)) * j =
          j * σ' (Multiplicative.ofAdd (w : Fin Tag.E6.rank → ZMod p)) := by
      intro w j hj
      exact hker' (σ' (Multiplicative.ofAdd (w : Fin Tag.E6.rank → ZMod p))) w (hσ' _)
        (fun γ hγ => w.2 ⟨γ, hγ⟩) j hj
    let toW : {w : Fin Tag.E6.rank → ZMod p // ∀ a, f a w = 0} →
        {g : Multiplicative (Fin Tag.E6.rank → ZMod p) // ∀ j ∈ J, σ' g * j = j * σ' g} :=
      fun w => ⟨Multiplicative.ofAdd (w : Fin Tag.E6.rank → ZMod p), hmap w⟩
    have hinj : Function.Injective toW := by
      intro a b hab
      have h1 : (toW a).val = (toW b).val := Subtype.ext_iff.mp hab
      exact Subtype.ext (Multiplicative.ofAdd.injective h1)
    have hle := Nat.card_le_card_of_injective toW hinj
    exact le_trans (Nat.mul_le_mul_left (p ^ 2) hle) hcount
  obtain ⟨a₁, a₂, w, hw⟩ := exists_not_commute_reflection_plain hp2 f v hadd hsmul hfv hconn hcard
  have hrefl_eq : ∀ (a : ι) (y : Fin Tag.E6.rank → ZMod p),
      ExcSplitRootGen.excRefl (p := p) a.1 y = y - f a y • v a :=
    fun a y => ggTBJTwE6_excRefl_eq (hroot a) y
  have hwR : ExcSplitRootGen.excRefl (p := p) a₁.1 (ExcSplitRootGen.excRefl (p := p) a₂.1 w) ≠
      ExcSplitRootGen.excRefl (p := p) a₂.1 (ExcSplitRootGen.excRefl (p := p) a₁.1 w) := by
    rw [hrefl_eq a₂ w, hrefl_eq a₁ _, hrefl_eq a₁ w, hrefl_eq a₂ _]
    exact hw
  have hact : ∀ (a : ι) (m : L'), ggKGTwY F (ψ m) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection a.1) →
      ∀ g, ψ m * ψ (σ' g) * (ψ m)⁻¹ = ψ (σ' (ggTBJTwE6ReflAut p (hroot a) g)) := by
    intro a m hm g
    rw [hσ', hσ', ggTBJTwE6ReflAut_apply]
    have h := TwE6PlusRootGen.conj_twE6PlusTorus F hζ hT (u := rootReflection a.1) hm
      (Multiplicative.toAdd g)
    rw [ofAdd_toAdd] at h
    exact h
  obtain ⟨m₁, hm₁, hy₁⟩ := hW a₁.1 a₁.2
  obtain ⟨m₂, hm₂, hy₂⟩ := hW a₂.1 a₂.2
  have hnc : ggTBJTwE6ReflAut p (hroot a₁) * ggTBJTwE6ReflAut p (hroot a₂) ≠
      ggTBJTwE6ReflAut p (hroot a₂) * ggTBJTwE6ReflAut p (hroot a₁) := by
    intro hcom
    have hw' := congrArg
      (fun s : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod p)) =>
        Multiplicative.toAdd (s (Multiplicative.ofAdd w))) hcom
    simp only [MulAut.mul_apply, ggTBJTwE6ReflAut_apply, toAdd_ofAdd] at hw'
    exact hwR hw'
  exact ⟨m₁, m₂, ggTBJTwE6ReflAut p (hroot a₁), ggTBJTwE6ReflAut p (hroot a₂), hm₁, hm₂,
    hact a₁ m₁ hy₁, hact a₂ m₂ hy₂, ggTBJTwE6ReflAut_sq p (hroot a₁),
    ggTBJTwE6ReflAut_sq p (hroot a₂), ggTBJTwE6ReflAut_card_fix p hp2 (hroot a₁),
    ggTBJTwE6ReflAut_card_fix p hp2 (hroot a₂), hnc⟩

end CFSG.StandardType

end

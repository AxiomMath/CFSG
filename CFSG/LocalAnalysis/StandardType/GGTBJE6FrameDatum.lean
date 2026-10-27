module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
import CFSG.LocalAnalysis.StandardType.GGTBJLeviAssemble
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SpCoord
open Multiplicative

namespace TypeBDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def e6d_iota (p : ℕ) :
    Additive (Fin 6 → Multiplicative (ZMod p)) ≃+ (Fin 6 → ZMod p) where
  toFun f i := toAdd (f i)
  invFun v i := ofAdd (v i)
  left_inv f := by funext i; rfl
  right_inv v := by funext i; rfl
  map_add' f g := by
    funext i
    change toAdd ((f + g).toMul i) = toAdd (f.toMul i) + toAdd (g.toMul i)
    rw [toMul_add, Pi.mul_apply, toAdd_mul]

private lemma e6d_liftBs_injective {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type}
    [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) : Function.Injective (liftBs Θ) := by
  intro σ τ h
  have h' : liftAut W₀ σ = liftAut W₀ τ := (MulAut.congr Θ).injective h
  exact MulEquiv.ext fun w => congrArg (fun e : MulAut (W × W₀) => (e (w, 1)).1) h'

private lemma e6d_card_fix_lift {W : Type} [Group W] {W₀ : Type} [Group W₀] (σ : MulAut W) :
    Nat.card {f : W × W₀ // liftAut W₀ σ f = f} = Nat.card {w : W // σ w = w} * Nat.card W₀ := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  exact
  { toFun := fun f => (⟨f.1.1, congrArg Prod.fst f.2⟩, f.1.2)
    invFun := fun x => ⟨(x.1.1, x.2), Prod.ext x.1.2 rfl⟩
    left_inv := fun f => by ext <;> rfl
    right_inv := fun x => by ext <;> rfl }

private lemma e6d_isRefl_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L']
    {A : Subgroup L'} {W W₀ : Type} [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥A) {σ : MulAut W}
    (hσ : σ ^ 2 = 1) (hfix : Nat.card {w : W // σ w = w} * p = Nat.card W) :
    GGIsReflection p (liftBs Θ σ) := by
  have hσ' : (liftAut W₀ σ) ^ 2 = 1 := by rw [← map_pow, hσ, map_one]
  exact ⟨by rw [← map_pow, hσ, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hσ')
      (by rw [e6d_card_fix_lift, Nat.card_prod, mul_right_comm, hfix])).2⟩

private lemma e6d_cartan_diag (i : Fin 6) : Tag.cartan .E6 i i = 2 := by
  change Tag.cartanE 6 i i = 2
  simp [Tag.cartanE]

private lemma e6d_simple_apply {p : ℕ}
    (ρ : WeylGroup Tag.E6 →* MulAut (Fin 6 → Multiplicative (ZMod p)))
    (hρ : ∀ (w : WeylGroup Tag.E6) (f : Fin 6 → Multiplicative (ZMod p)),
      (fun i => toAdd (ρ w f i)) = TableBExc.E6Three.adAct .E6 p w (fun i => toAdd (f i)))
    (i : Fin 6) (f : Fin 6 → Multiplicative (ZMod p)) (j : Fin 6) :
    toAdd (ρ (simple .E6 i) f j) =
      toAdd (f j) - toAdd (f i) * ((Tag.cartan .E6 i j : ℤ) : ZMod p) := by
  calc toAdd (ρ (simple .E6 i) f j)
      = TableBExc.E6Three.adAct .E6 p (simple .E6 i) (fun k => toAdd (f k)) j :=
        congrFun (hρ (simple .E6 i) f) j
    _ = TableBExc.E6Three.adRefl .E6 p i (fun k => toAdd (f k)) j :=
        congrFun (TableBExc.E6Three.adAct_simple (τ := Tag.E6) (p := p) i _) j
    _ = toAdd (f j) - toAdd (f i) * ((Tag.cartan .E6 i j : ℤ) : ZMod p) := rfl

private lemma e6d_card_fix {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : WeylGroup Tag.E6 →* MulAut (Fin 6 → Multiplicative (ZMod p)))
    (hρ : ∀ (w : WeylGroup Tag.E6) (f : Fin 6 → Multiplicative (ZMod p)),
      (fun i => toAdd (ρ w f i)) = TableBExc.E6Three.adAct .E6 p w (fun i => toAdd (f i)))
    (i : Fin 6) :
    Nat.card {f : Fin 6 → Multiplicative (ZMod p) // ρ (simple .E6 i) f = f} * p =
      Nat.card (Fin 6 → Multiplicative (ZMod p)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hs := e6d_simple_apply ρ hρ i
  let a₁ : Fin 6 → Multiplicative (ZMod p) := fun j => ofAdd ((Tag.cartan .E6 i j : ℤ) : ZMod p)
  refine card_fix_mul_of_le_zpowers hp (fun a b => mul_comm a b) (ρ (simple .E6 i))
    (a₁ := a₁) ?_ (fun a => ⟨(toAdd (a i)).val, ?_⟩) ?_
  · funext j
    apply Multiplicative.toAdd.injective
    simp [a₁, toAdd_pow, nsmul_eq_mul]
  · funext j
    apply Multiplicative.toAdd.injective
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, toAdd_mul, toAdd_inv, toAdd_pow, hs,
      a₁, toAdd_ofAdd, nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  · intro h
    have h1 := congrArg (fun g : Fin 6 → Multiplicative (ZMod p) => toAdd (g i)) h
    simp only [Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv, hs, a₁, toAdd_ofAdd,
      Pi.one_apply, toAdd_one, e6d_cartan_diag, Int.cast_ofNat] at h1
    have h4 : (2 : ZMod p) * 2 = 0 := by linear_combination h1
    exact mul_ne_zero (coord_two_ne_zero hp hp2) (coord_two_ne_zero hp hp2) h4

theorem exists_E6_datum_of_frameAction {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin 6 → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (ρ : WeylGroup Tag.E6 →* MulAut (Fin 6 → Multiplicative (ZMod p)))
    (hρinj : Function.Injective ρ)
    (hρ : ∀ (w : WeylGroup Tag.E6) (f : Fin 6 → Multiplicative (ZMod p)),
      (fun i => toAdd (ρ w f i)) = TableBExc.E6Three.adAct .E6 p w (fun i => toAdd (f i)))
    (hX : ggAutomizer X Bs = ρ.range.map (liftBs Θ)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.E₆ i j : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, φ i = liftBs Θ (ρ (simple .E6 i))) ∧
      LinearIndependent (ZMod p) h := by
  classical
  have hp : p.Prime := Fact.out
  let W := Fin 6 → Multiplicative (ZMod p)
  have hcomm : ∀ u v : W₀, u * v = v * u := by
    intro u v
    have h : Θ (1, u) * Θ (1, v) = Θ (1, v) * Θ (1, u) := hBs.1.is_comm.comm _ _
    have h' : Θ ((1, u) * (1, v)) = Θ ((1, v) * (1, u)) := by
      rw [map_mul, map_mul]
      exact h
    simpa using congrArg Prod.snd (Θ.injective h')
  have hpow : ∀ u : W₀, u ^ p = 1 := by
    intro u
    have h : Θ (1, u) ^ p = 1 := Subtype.ext (hBs.2 _ (Θ (1, u)).2)
    have h' : Θ ((1, u) ^ p) = Θ 1 := by rw [map_pow, h, map_one]
    simpa using congrArg Prod.snd (Θ.injective h')
  let iA : AddCommGroup (Additive W₀) :=
    { (inferInstance : AddGroup (Additive W₀)) with
      add_comm := fun a b => congrArg Additive.ofMul (hcomm (Additive.toMul a) (Additive.toMul b)) }
  let iM : Module (ZMod p) (Additive W₀) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hpow _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  let V := (Fin 6 → ZMod p) × Additive W₀
  let ι₀ : Additive (W × W₀) ≃+ V :=
    (AddEquiv.prodAdditive ..).trans (AddEquiv.prodCongr (e6d_iota p) (AddEquiv.refl _))
  let ι : Additive ↥Bs ≃+ V := (MulEquiv.toAdditive Θ.symm).trans ι₀
  let σ : Fin 6 → MulAut W := fun i => ρ (simple .E6 i)
  let φ : Fin 6 → MulAut ↥Bs := fun i => liftBs Θ (σ i)
  let c : Fin 6 → Fin 6 → ZMod p := fun i j => ((Tag.cartan .E6 i j : ℤ) : ZMod p)
  let hv : Fin 6 → V := fun i => (c i, 0)
  let α : Fin 6 → Module.Dual (ZMod p) V := fun i =>
    (LinearMap.proj i).comp (LinearMap.fst (ZMod p) (Fin 6 → ZMod p) (Additive W₀))
  have hframe : ∀ i (v : Fin 6 → ZMod p),
      ggLin (p := p) (e6d_iota p) (σ i) v = v - v i • c i := by
    intro i v
    funext j
    rw [ggLin_apply]
    change toAdd ((σ i) (fun k => ofAdd (v k)) j) = v j - v i * c i j
    rw [e6d_simple_apply ρ hρ i]
    rfl
  have hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • hv i := by
    intro i w
    obtain ⟨v, u⟩ := w
    rw [show ι = (MulEquiv.toAdditive Θ.symm).trans ι₀ from rfl,
      show φ i = MulAut.congr Θ (liftAut W₀ (σ i)) from rfl, ggLin_mulEquiv_congr]
    have key : ggLin (p := p) ι₀ (liftAut W₀ (σ i)) (v, u) =
        (ggLin (p := p) (e6d_iota p) (σ i) v, u) := by
      rw [ggLin_apply, ggLin_apply]
      rfl
    rw [key, hframe]
    refine Prod.ext rfl ?_
    show u = u - (α i (v, u)) • (0 : Additive W₀)
    rw [smul_zero, sub_zero]
  have hrefl : ∀ i, GGIsReflection p (φ i) := by
    intro i
    refine e6d_isRefl_lift hp hp2 Θ ?_ (e6d_card_fix hp2 ρ hρ i)
    show ρ (simple .E6 i) ^ 2 = 1
    rw [← map_pow, show simple Tag.E6 i ^ 2 = 1 from (coxeterSystem Tag.E6).simple_sq i,
      map_one]
  have hpair : ∀ i j, α i (hv j) = (CartanMatrix.E₆ i j : ZMod p) := by
    intro i j
    change c j i = _
    change ((Tag.cartanE 6 j i : ℤ) : ZMod p) = _
    rw [cartanE_eq, (CartanMatrix.E_isSymm 6).apply i j]
  have hinj : Function.Injective (liftBs Θ) := e6d_liftBs_injective Θ
  let f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs) :=
    (ggE6Row_coxeterGroupEquiv.trans (MonoidHom.ofInjective hρinj)).trans
      ((Subgroup.equivMapOfInjective ρ.range (liftBs Θ) hinj).trans
        (MulEquiv.subgroupCongr hX.symm))
  have hf : ∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i := by
    intro i
    change ((MulEquiv.subgroupCongr hX.symm) ((Subgroup.equivMapOfInjective ρ.range (liftBs Θ)
      hinj) ((MonoidHom.ofInjective hρinj) (ggE6Row_coxeterGroupEquiv
        (CoxeterMatrix.E₆.simple i)))) : MulAut ↥Bs) = φ i
    rw [MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply,
      MonoidHom.ofInjective_apply, ggE6Row_coxeterGroupEquiv_simple]
  have hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
    rw [hX, MonoidHom.range_eq_map, ← (coxeterSystem Tag.E6).subgroup_closure_range_simple,
      MonoidHom.map_closure, MonoidHom.map_closure, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hind : LinearIndependent (ZMod p) hv := by
    refine ggLeviDatum_linearIndependent_of_pair (C := CartanMatrix.E 6) ?_ hv α hpair
    rw [CartanMatrix.E₆_det]
    refine isUnit_iff_ne_zero.mpr fun h3 => ?_
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
    have h3' : p ∣ 3 := by exact_mod_cast h3
    rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h
    · exact hp.one_lt.ne' h
    · exact hp3 h
  exact ⟨V, inferInstance, inferInstance, ι, φ, hv, α, f, hlin, hrefl, hpair, hf, hclos,
    fun _ => rfl, hind⟩

theorem exists_E6_datum_of_sectionFrameAut {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (Θ : ((Fin 6 → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (Θ₁ : (Fin 6 → Multiplicative (ZMod p)) →* G)
    (hAut : ggAutomizer X Bs = (FrameBs.sectionFrameAut Θ₁ X).map (liftBs Θ))
    (ρ : WeylGroup Tag.E6 →* MulAut (Fin 6 → Multiplicative (ZMod p)))
    (hρinj : Function.Injective ρ)
    (hρ : ∀ (w : WeylGroup Tag.E6) (f : Fin 6 → Multiplicative (ZMod p)),
      (fun i => toAdd (ρ w f i)) = TableBExc.E6Three.adAct .E6 p w (fun i => toAdd (f i)))
    (hW : FrameBs.sectionFrameAut Θ₁ X = ρ.range) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.E₆ i j : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, φ i = liftBs Θ (ρ (simple .E6 i))) ∧
      LinearIndependent (ZMod p) h :=
  exists_E6_datum_of_frameAction hp2 hp3 hBs Θ ρ hρinj hρ (hAut.trans (by rw [hW]))

end TypeBDatum

end CFSG.StandardType

end

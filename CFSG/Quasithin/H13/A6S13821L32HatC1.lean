module

public import CFSG.Quasithin.H13.A6S13821L32HatLemmaM
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.A6.L32HatC

open CFSG.Quasithin.H13.A6.L32HatM

private instance fact_prime_two_F4 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable def polyF : Polynomial (ZMod 2) := Polynomial.X ^ 2 + Polynomial.X + 1

private theorem polyF_natDegree : polyF.natDegree = 2 := by
  unfold polyF
  compute_degree!

private theorem polyF_ne_zero : polyF ≠ 0 := by
  intro h
  have h2 := polyF_natDegree
  rw [h, Polynomial.natDegree_zero] at h2
  omega

private theorem zmod2_zero_or_one : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem polyF_irr : Irreducible polyF := by
  have hdeg : polyF.natDegree ∈ Finset.Icc 1 3 := by
    rw [polyF_natDegree]
    simp
  have key : ∀ x : ZMod 2, x ^ 2 + x + 1 ≠ 0 := by
    intro x
    rcases zmod2_zero_or_one x with rfl | rfl <;> decide
  have hnot : ∀ x : ZMod 2, ¬ Polynomial.IsRoot polyF x := by
    intro x
    unfold polyF
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    exact key x
  exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 2) hdeg hnot

private instance polyF_fact : Fact (Irreducible polyF) := ⟨polyF_irr⟩

private theorem card_F4 : Nat.card (AdjoinRoot polyF) = 4 := by
  haveI : Module.Finite (ZMod 2) (AdjoinRoot polyF) :=
    (AdjoinRoot.powerBasis (K := ZMod 2) polyF_ne_zero).finite
  have hfr : Module.finrank (ZMod 2) (AdjoinRoot polyF) = polyF.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (K := ZMod 2) polyF_ne_zero),
      AdjoinRoot.powerBasis_dim polyF_ne_zero]
  simpa [hfr, polyF_natDegree, Nat.card_zmod] using
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := AdjoinRoot polyF)

private theorem algebraMap_F4_injective :
    Function.Injective (algebraMap (ZMod 2) (AdjoinRoot polyF)) := by
  intro a b hab
  have h1 : algebraMap (ZMod 2) (AdjoinRoot polyF) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rcases zmod2_zero_or_one (a - b) with h | h
  · exact sub_eq_zero.1 h
  · rw [h, map_one] at h1
    exact absurd h1 one_ne_zero

private instance charP_F4 : CharP (AdjoinRoot polyF) 2 :=
  charP_of_injective_algebraMap algebraMap_F4_injective 2

private instance finite_F4 : Finite (AdjoinRoot polyF) :=
  Nat.finite_of_card_ne_zero (by rw [card_F4]; norm_num)

private theorem commute_aeval_poly {S : Type*} [Semiring S] [Algebra (ZMod 2) S] {x y : S}
    (h : Commute x y) (p : Polynomial (ZMod 2)) : Commute x (Polynomial.aeval y p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_right (Algebra.commutes a x).symm (h.pow_right n)

private theorem mem_fix {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (ρ : SL3 →* Module.End F U) (u : U) :
    u ∈ (⨅ e ∈ E₀, LinearMap.ker (ρ e - 1)) ↔ ∀ e ∈ E₀, ρ e u = u := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

private theorem core {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ω : Module.End (ZMod 2) U) (hω : ω ^ 2 + ω + 1 = 0)
    (ρ : SL3 →* Module.End (ZMod 2) U) (hcomm : ∀ g : SL3, ρ g * ω = ω * ρ g)
    (v₀ : U) (hA : ∀ a ∈ A₀, ρ a v₀ = v₀)
    (hgen : AddSubgroup.closure {u : U | ∃ g : SL3, u = ρ g v₀ ∨ u = ω (ρ g v₀)} = ⊤)
    (hnt : ∃ g : SL3, ρ g ≠ 1)
    (C : AddSubgroup U) (hC : ∀ u ∈ C, ∀ e ∈ E₀, ρ e u = u) :
    16 * Nat.card C ∣ Nat.card U := by
  have hpoly : Polynomial.aeval ω polyF = 0 := by
    simp only [polyF, map_add, map_pow, Polynomial.aeval_X, map_one]
    exact hω
  let φ : AdjoinRoot polyF →+* Module.End (ZMod 2) U :=
    Ideal.Quotient.lift (Ideal.span {polyF}) (Polynomial.aeval ω).toRingHom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
      show Polynomial.aeval ω (polyF * b) = 0
      rw [map_mul, hpoly, zero_mul])
  letI : Module (AdjoinRoot polyF) U := Module.compHom U φ
  have hroot : φ (AdjoinRoot.root polyF) = ω := by
    show Polynomial.aeval ω Polynomial.X = ω
    rw [Polynomial.aeval_X]
  have hωsmul : ∀ y : U, AdjoinRoot.root polyF • y = ω y := fun y => by
    rw [show AdjoinRoot.root polyF • y = φ (AdjoinRoot.root polyF) y from rfl, hroot]
  have hcommφ : ∀ (g : SL3) (a : AdjoinRoot polyF), ρ g * φ a = φ a * ρ g := by
    intro g a
    induction a using AdjoinRoot.induction_on with
    | ih p => exact commute_aeval_poly (hcomm g) p
  have hFlin : ∀ (g : SL3) (a : AdjoinRoot polyF) (u : U), ρ g (a • u) = a • ρ g u :=
    fun g a u => congrArg (fun T : Module.End (ZMod 2) U => T u) (hcommφ g a)
  let ρF : SL3 →* Module.End (AdjoinRoot polyF) U :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := (ρ g).map_add
          map_smul' := fun a u => hFlin g a u }
      map_one' := LinearMap.ext fun u => by
        show ρ 1 u = u
        simp
      map_mul' := fun g h => LinearMap.ext fun u => by
        show ρ (g * h) u = ρ g (ρ h u)
        simp [map_mul] }
  have hgenF : Submodule.span (AdjoinRoot polyF) (Set.range fun g => ρF g v₀) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have hu : u ∈ AddSubgroup.closure {u : U | ∃ g : SL3, u = ρ g v₀ ∨ u = ω (ρ g v₀)} := by
      rw [hgen]
      exact AddSubgroup.mem_top u
    induction hu using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl | rfl⟩ := hx
      · exact Submodule.subset_span ⟨g, rfl⟩
      · rw [← hωsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  have hAF : ∀ a ∈ A₀, ρF a v₀ = v₀ := fun a ha => hA a ha
  have hntF : ∃ g : SL3, ρF g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h => hg ?_⟩
    exact LinearMap.ext fun u => LinearMap.congr_fun h u
  haveI : Module.Finite (AdjoinRoot polyF) U := Module.finite_iff_finite.2 inferInstance
  have hmain := two_le_finrank_quot_fixed ρF v₀ hAF hgenF hntF
  set C' : Submodule (AdjoinRoot polyF) U := ⨅ e ∈ E₀, LinearMap.ker (ρF e - 1) with hC'
  have hCC : C ≤ C'.toAddSubgroup := by
    intro u hu
    show u ∈ C'
    rw [hC', mem_fix]
    exact fun e he => hC u hu e he
  have hfinrank := C'.finrank_quotient_add_finrank
  have hcardU : Nat.card U = 4 ^ Module.finrank (AdjoinRoot polyF) U := by
    rw [Module.natCard_eq_pow_finrank (K := AdjoinRoot polyF), card_F4]
  have hcardC' : Nat.card C' = 4 ^ Module.finrank (AdjoinRoot polyF) C' := by
    rw [Module.natCard_eq_pow_finrank (K := AdjoinRoot polyF), card_F4]
  have hcardQ : Nat.card (U ⧸ C') = 4 ^ Module.finrank (AdjoinRoot polyF) (U ⧸ C') := by
    rw [Module.natCard_eq_pow_finrank (K := AdjoinRoot polyF), card_F4]
  have h16 : 16 ∣ Nat.card (U ⧸ C') := by
    rw [hcardQ]
    calc (16 : ℕ) = 4 ^ 2 := by norm_num
      _ ∣ 4 ^ Module.finrank (AdjoinRoot polyF) (U ⧸ C') := pow_dvd_pow 4 hmain
  have hdvd : Nat.card C ∣ Nat.card C'.toAddSubgroup := AddSubgroup.card_dvd_of_le hCC
  have hcardCC : Nat.card C'.toAddSubgroup = Nat.card C' :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [hcardCC] at hdvd
  rw [hcardU, ← hfinrank, pow_add, ← hcardQ, ← hcardC']
  exact mul_dvd_mul h16 hdvd

private def addOf {W : Type} [CommGroup W] (g : MulAut W) : Additive W →+ Additive W where
  toFun u := Additive.ofMul (g (Additive.toMul u))
  map_zero' := congrArg Additive.ofMul (map_one g)
  map_add' u v := congrArg Additive.ofMul (map_mul g (Additive.toMul u) (Additive.toMul v))

theorem index_dvd_of_fixed {W : Type} [CommGroup W] [Finite W] (hsq : ∀ w : W, w ^ 2 = 1)
    (c : MulAut W) (hc : ∀ w : W, w * c w * c (c w) = 1)
    (ρ : SL3 →* MulAut W) (hcomm : ∀ (g : SL3) (w : W), ρ g (c w) = c (ρ g w))
    (v₀ : W) (hA : ∀ a ∈ A₀, ρ a v₀ = v₀)
    (hgen : Subgroup.closure {w : W | ∃ g : SL3, w = ρ g v₀ ∨ w = c (ρ g v₀)} = ⊤)
    (hnt : ∃ g : SL3, ρ g ≠ 1)
    (C : Subgroup W) (hC : ∀ w ∈ C, ∀ e ∈ E₀, ρ e w = w) :
    16 * Nat.card C ∣ Nat.card W := by
  have h2 : ∀ u : Additive W, (2 : ℕ) • u = 0 := fun u => hsq (Additive.toMul u)
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  let ω : Module.End (ZMod 2) (Additive W) := (addOf c).toZModLinearMap 2
  have hωA : ∀ u : Additive W, u + ω u + ω (ω u) = 0 := fun u =>
    congrArg Additive.ofMul (hc (Additive.toMul u))
  have hω : ω ^ 2 + ω + 1 = 0 := by
    refine LinearMap.ext fun u => ?_
    simp only [sq, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    rw [show ω (ω u) + ω u + u = u + ω u + ω (ω u) by abel]
    exact hωA u
  let ρA : SL3 →* Module.End (ZMod 2) (Additive W) :=
    { toFun := fun g => (addOf (ρ g)).toZModLinearMap 2
      map_one' := LinearMap.ext fun u =>
        congrArg (fun f : MulAut W => Additive.ofMul (f (Additive.toMul u))) (map_one ρ)
      map_mul' := fun g h => LinearMap.ext fun u =>
        congrArg (fun f : MulAut W => Additive.ofMul (f (Additive.toMul u))) (map_mul ρ g h) }
  have hcommA : ∀ g : SL3, ρA g * ω = ω * ρA g := fun g =>
    LinearMap.ext fun u => congrArg Additive.ofMul (hcomm g (Additive.toMul u))
  have hA' : ∀ a ∈ A₀, ρA a (Additive.ofMul v₀) = Additive.ofMul v₀ := fun a ha =>
    congrArg Additive.ofMul (hA a ha)
  have hgen' : AddSubgroup.closure {u : Additive W | ∃ g : SL3,
      u = ρA g (Additive.ofMul v₀) ∨ u = ω (ρA g (Additive.ofMul v₀))} = ⊤ := by
    have key : ∀ x : W,
        x ∈ Subgroup.closure {w : W | ∃ g : SL3, w = ρ g v₀ ∨ w = c (ρ g v₀)} →
        Additive.ofMul x ∈ AddSubgroup.closure {u : Additive W | ∃ g : SL3,
          u = ρA g (Additive.ofMul v₀) ∨ u = ω (ρA g (Additive.ofMul v₀))} := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g, rfl | rfl⟩ := hx
        · exact AddSubgroup.subset_closure ⟨g, Or.inl rfl⟩
        · exact AddSubgroup.subset_closure ⟨g, Or.inr rfl⟩
      | one => exact AddSubgroup.zero_mem _
      | mul x y _ _ hx hy => exact AddSubgroup.add_mem _ hx hy
      | inv x _ hx => exact AddSubgroup.neg_mem _ hx
    rw [eq_top_iff]
    intro u _
    have hx : Additive.toMul u ∈
        Subgroup.closure {w : W | ∃ g : SL3, w = ρ g v₀ ∨ w = c (ρ g v₀)} := by
      rw [hgen]
      exact Subgroup.mem_top _
    exact key _ hx
  have hnt' : ∃ g : SL3, ρA g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h => hg ?_⟩
    refine MulEquiv.ext fun w => ?_
    exact LinearMap.congr_fun h (Additive.ofMul w)
  let Cadd : AddSubgroup (Additive W) :=
    { carrier := {u | Additive.toMul u ∈ C}
      add_mem' := fun {a b} (ha : Additive.toMul a ∈ C) (hb : Additive.toMul b ∈ C) =>
        C.mul_mem ha hb
      zero_mem' := C.one_mem
      neg_mem' := fun {a} (ha : Additive.toMul a ∈ C) => C.inv_mem ha }
  have hC' : ∀ u ∈ Cadd, ∀ e ∈ E₀, ρA e u = u := fun u hu e he =>
    congrArg Additive.ofMul (hC (Additive.toMul u) hu e he)
  have key := core ω hω ρA hcommA (Additive.ofMul v₀) hA' hgen' hnt' Cadd hC'
  have hcardC : Nat.card Cadd = Nat.card C :=
    Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩,
        invFun := fun y => ⟨Additive.ofMul y.1, y.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hcardW : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.ofMul.symm
  rw [hcardC, hcardW] at key
  exact key

end CFSG.Quasithin.H13.A6.L32HatC

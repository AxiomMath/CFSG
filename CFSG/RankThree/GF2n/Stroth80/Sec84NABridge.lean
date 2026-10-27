module

public import CFSG.ClassicalGroups.F2Fixed.Descent
public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

section Pad

@[expose] def PadSp (X : Type) (K : Type) (k : ℕ) : Type := X × (Fin k → K)

instance (X K : Type) [AddCommGroup X] [Field K] (k : ℕ) : AddCommGroup (PadSp X K k) :=
  inferInstanceAs (AddCommGroup (X × (Fin k → K)))

instance (X K : Type) [AddCommGroup X] [Field K] [Module K X] (k : ℕ) :
    Module K (PadSp X K k) := inferInstanceAs (Module K (X × (Fin k → K)))

instance (X K : Type) [AddCommGroup X] [Field K] [Module K X] [Module.Finite K X] (k : ℕ) :
    Module.Finite K (PadSp X K k) := inferInstanceAs (Module.Finite K (X × (Fin k → K)))

theorem PadSp.finrank (X K : Type) [AddCommGroup X] [Field K] [Module K X] [Module.Finite K X]
    (k : ℕ) : Module.finrank K (PadSp X K k) = Module.finrank K X + k := by
  show Module.finrank K (X × (Fin k → K)) = _
  rw [Module.finrank_prod, Module.finrank_fin_fun]

@[expose] def PadSp.mk {X K : Type} (k : ℕ) [Zero K] (x : X) : PadSp X K k :=
  (x, fun _ => 0)

instance (G X K : Type) [Group G] [AddCommGroup X] [Field K] [DistribMulAction G X] (k : ℕ) :
    DistribMulAction G (PadSp X K k) where
  smul g p := (g • (p : X × (Fin k → K)).1, (p : X × (Fin k → K)).2)
  one_smul p := Prod.ext (one_smul G (p : X × (Fin k → K)).1) rfl
  mul_smul g h p := Prod.ext (mul_smul g h (p : X × (Fin k → K)).1) rfl
  smul_zero g := Prod.ext (smul_zero g) rfl
  smul_add g p q := Prod.ext (smul_add g (p : X × (Fin k → K)).1 (q : X × (Fin k → K)).1) rfl

theorem PadSp.smul_mk {G X K : Type} [Group G] [AddCommGroup X] [Field K] [DistribMulAction G X]
    (k : ℕ) (g : G) (x : X) : g • (PadSp.mk (K := K) k x : PadSp X K k) = PadSp.mk k (g • x) :=
  rfl

theorem PadSp.mk_add {X K : Type} [AddCommGroup X] [Field K] (k : ℕ) (x x' : X) :
    (PadSp.mk (K := K) k (x + x') : PadSp X K k) = PadSp.mk k x + PadSp.mk k x' :=
  Prod.ext rfl (by
    show (fun _ : Fin k => (0 : K)) = (fun _ => (0 : K)) + (fun _ => (0 : K))
    funext i
    simp)

theorem PadSp.mk_smul {X K : Type} [AddCommGroup X] [Field K] [Module K X] (k : ℕ) (c : K)
    (x : X) : (PadSp.mk (K := K) k (c • x) : PadSp X K k) = c • PadSp.mk k x :=
  Prod.ext rfl (by
    show (fun _ : Fin k => (0 : K)) = c • (fun _ => (0 : K))
    funext i
    simp)

theorem PadSp.mk_zero {X K : Type} [AddCommGroup X] [Field K] (k : ℕ) :
    (PadSp.mk (K := K) k (0 : X) : PadSp X K k) = 0 := rfl

end Pad

section Bridge

open scoped Matrix

theorem noEmb_of_cited (hS : Sp6NoEmbeddingStatement)
    {Kg Kn : Type} [Field Kg] [Field Kn] [Finite Kn] [CharP Kn 2] (θ : Kg ≃+* Kn)
    (h4 : 4 ≤ Nat.card Kn)
    {R : Type} [Group R] (φ : R →* ↥(StatedSp 3 Kn)) (hφ : Function.Surjective φ)
    {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction R N]
    (hNker : ∀ g : R, φ g = 1 → ∀ a : N, g • a = a)
    (hNcard : Nat.card N = Nat.card Kn ^ 8) (hNnt : ∃ (g : R) (a : N), g • a ≠ a)
    (hNirr : ∀ S : AddSubgroup N, (∀ g : R, ∀ a ∈ S, g • a ∈ S) → S = ⊥ ∨ S = ⊤)
    {U : Type} [AddCommGroup U] [Module Kg U] [DistribMulAction R U]
    {X : Type} [AddCommGroup X] [Module Kg X] [Finite X] [DistribMulAction R X]
    [SMulCommClass R Kg X]
    (hXker : ∀ g : R, φ g = 1 → ∀ x : X, g • x = x)
    {d : ℕ} (hd : d ≤ 8) (hXcard : Nat.card X = Nat.card Kn ^ d)
    (Ψ : U →+ (Fin 3 ⊕ Fin 3 → Kn)) (hΨ : Function.Surjective Ψ)
    (hΨsmul : ∀ (c : Kg) (u : U), Ψ (c • u) = θ c • Ψ u)
    (hΨeq : ∀ (g : R) (u : U), Ψ (g • u) =
      ((((φ g : ↥(StatedSp 3 Kn)) : GL (Fin 3 ⊕ Fin 3) Kn) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Kn) *ᵥ Ψ u))
    (f : N →+ (U →ₗ[Kg] X)) (hΨ0 : ∀ u, Ψ u = 0 → ∀ n, f n u = 0)
    (hfeq : ∀ (g : R) n u, f (g • n) (g • u) = g • f n u) (hfinj : Function.Injective f) :
    False := by
  classical
  let s : ↥(StatedSp 3 Kn) → R := Function.surjInv hφ
  have hs : ∀ g, φ (s g) = g := Function.surjInv_eq hφ
  have hNker' : ∀ x ∈ φ.ker, ∀ a : N, x • a = a := fun x hx a =>
    hNker x (MonoidHom.mem_ker.mp hx) a
  have hXker' : ∀ x ∈ φ.ker, ∀ a : X, x • a = a := fun x hx a =>
    hXker x (MonoidHom.mem_ker.mp hx) a
  letI actN : DistribMulAction ↥(StatedSp 3 Kn) N :=
    CFSG.ClassicalGroups.F2Fixed.descendAction φ hφ hNker'
  letI actX : DistribMulAction ↥(StatedSp 3 Kn) X :=
    CFSG.ClassicalGroups.F2Fixed.descendAction φ hφ hXker'
  have hactN : ∀ (g : ↥(StatedSp 3 Kn)) (a : N), g • a = s g • a := fun g a => rfl
  have hactX : ∀ (g : ↥(StatedSp 3 Kn)) (x : X), g • x = s g • x := fun g x => rfl
  letI modX : Module Kn X := Module.compHom X θ.symm.toRingHom
  have hcX : ∀ (c : Kn) (x : X), c • x = θ.symm c • x := fun c x => rfl
  haveI : Module.Finite Kn X := Module.Finite.of_finite
  have hfinX : Module.finrank Kn X = d := by
    have h1 := Module.natCard_eq_pow_finrank (K := Kn) (V := X)
    rw [hXcard] at h1
    have h2 : 2 ≤ Nat.card Kn := by omega
    exact (Nat.pow_right_injective h2 h1).symm
  have hlin : ∀ (g : ↥(StatedSp 3 Kn)) (c : Kn) (x : PadSp X Kn (8 - d)),
      g • (c • x) = c • (g • x) := by
    intro g c x
    refine Prod.ext ?_ rfl
    show g • (c • (x : X × (Fin (8 - d) → Kn)).1) = c • (g • (x : X × (Fin (8 - d) → Kn)).1)
    rw [hcX, hcX, hactX, hactX]
    exact smul_comm (s g) (θ.symm c) _
  have hfin : Module.finrank Kn (PadSp X Kn (8 - d)) = 8 := by
    rw [PadSp.finrank, hfinX]
    omega
  let lift : (Fin 3 ⊕ Fin 3 → Kn) → U := Function.surjInv hΨ
  have hlift : ∀ y, Ψ (lift y) = y := Function.surjInv_eq hΨ
  have hwd : ∀ (n : N) (u u' : U), Ψ u = Ψ u' → f n u = f n u' := by
    intro n u u' h
    have h1 : f n (u - u') = 0 := hΨ0 (u - u') (by rw [map_sub, h, sub_self]) n
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  let Fn : N → ((Fin 3 ⊕ Fin 3 → Kn) →ₗ[Kn] PadSp X Kn (8 - d)) := fun n =>
    { toFun := fun y => PadSp.mk (8 - d) (f n (lift y))
      map_add' := fun y y' => by
        have h1 : f n (lift (y + y')) = f n (lift y) + f n (lift y') := by
          rw [← map_add]
          apply hwd
          rw [hlift, map_add, hlift, hlift]
        show PadSp.mk (8 - d) (f n (lift (y + y'))) =
          PadSp.mk (8 - d) (f n (lift y)) + PadSp.mk (8 - d) (f n (lift y'))
        rw [h1, PadSp.mk_add]
      map_smul' := fun c y => by
        have h1 : f n (lift (c • y)) = c • f n (lift y) := by
          have h2 : f n (lift (c • y)) = f n (θ.symm c • lift y) := by
            apply hwd
            rw [hlift, hΨsmul, hlift, RingEquiv.apply_symm_apply]
          rw [h2, map_smul]
          rfl
        show PadSp.mk (8 - d) (f n (lift (c • y))) = c • PadSp.mk (8 - d) (f n (lift y))
        rw [h1, PadSp.mk_smul] }
  let F : N →+ ((Fin 3 ⊕ Fin 3 → Kn) →ₗ[Kn] PadSp X Kn (8 - d)) :=
    { toFun := Fn
      map_zero' := by
        refine LinearMap.ext fun y => ?_
        show PadSp.mk (8 - d) (f 0 (lift y)) = 0
        rw [map_zero, LinearMap.zero_apply]
        exact PadSp.mk_zero _
      map_add' := fun n n' => by
        refine LinearMap.ext fun y => ?_
        rw [LinearMap.add_apply]
        show PadSp.mk (8 - d) (f (n + n') (lift y)) =
          PadSp.mk (8 - d) (f n (lift y)) + PadSp.mk (8 - d) (f n' (lift y))
        rw [map_add, LinearMap.add_apply, PadSp.mk_add] }
  have hFeq : ∀ (g : ↥(StatedSp 3 Kn)) (n : N) (v : Fin 3 ⊕ Fin 3 → Kn),
      F (g • n) v = g • F n ((((g⁻¹ : ↥(StatedSp 3 Kn)) : GL (Fin 3 ⊕ Fin 3) Kn) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Kn) *ᵥ v) := by
    intro g n v
    show PadSp.mk (8 - d) (f (g • n) (lift v)) = g • PadSp.mk (8 - d) (f n (lift (_ *ᵥ v)))
    rw [PadSp.smul_mk, hactN, hactX]
    congr 1
    have h1 : f (s g • n) (lift v) = s g • f n ((s g)⁻¹ • lift v) := by
      conv_lhs => rw [← smul_inv_smul (s g) (lift v)]
      exact hfeq (s g) n _
    rw [h1]
    congr 1
    apply hwd
    rw [hΨeq, hlift, hlift, map_inv, hs]
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have h0 : ∀ u : U, f n u = 0 := by
      intro u
      have h1 := LinearMap.congr_fun hn (Ψ u)
      have h2 : f n (lift (Ψ u)) = 0 := congrArg Prod.fst h1
      rw [← h2]
      apply hwd
      rw [hlift]
    exact hfinj ((LinearMap.ext h0).trans (map_zero f).symm)
  have hnt' : ∃ (g : ↥(StatedSp 3 Kn)) (a : N), g • a ≠ a := by
    obtain ⟨g, a, h⟩ := hNnt
    refine ⟨φ g, a, ?_⟩
    rw [show (φ g) • a = g • a from
      CFSG.ClassicalGroups.F2Fixed.descendAction_smul φ hφ hNker' g a]
    exact h
  have hirr' : ∀ S : AddSubgroup N, (∀ (g : ↥(StatedSp 3 Kn)), ∀ a ∈ S, g • a ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS'
    refine hNirr S (fun g a ha => ?_)
    rw [← CFSG.ClassicalGroups.F2Fixed.descendAction_smul φ hφ hNker' g a]
    exact hS' (φ g) a ha
  exact hS Kn h4 N hNcard hnt' hirr' (PadSp X Kn (8 - d)) hlin hfin F hFeq hFinj

end Bridge

end CFSG.RankThree.GF2n.Stroth80

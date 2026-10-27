module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneLinear
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusFix
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

namespace CFSG.StandardType

open Multiplicative

section Abs

private theorem ggKGLn_T_fix_iff {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [NeZero p] [Fact p.Prime] {ζ : L} (hζo : IsPrimitiveRoot ζ p)
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    (f : Fin s → Multiplicative (ZMod p)) (x : (Fin s → L) × (Fin r → K)) :
    T f x = x ↔ ∀ i, f i ≠ 1 → x.1 i = 0 := by
  obtain ⟨d, w⟩ := x
  rw [hT]
  constructor
  · intro h i hi
    have h1 := congrFun (Prod.ext_iff.mp h).1 i
    change ζ ^ (toAdd (f i)).val * d i = d i at h1
    have hv : ζ ^ (toAdd (f i)).val ≠ 1 := by
      intro h1'
      apply hi
      have h3 := (hζo.pow_eq_one_iff_dvd _).mp h1'
      rw [← ofAdd_toAdd (f i), ← ZMod.natCast_zmod_val (toAdd (f i)),
        (ZMod.natCast_eq_zero_iff _ _).mpr h3, ofAdd_zero]
    have h2 : (ζ ^ (toAdd (f i)).val - 1) * d i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hv)
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    change ζ ^ (toAdd (f i)).val * d i = d i
    by_cases hi : f i = 1
    · rw [hi, toAdd_one, ZMod.val_zero, pow_zero, one_mul]
    · have hd : d i = 0 := h i hi
      rw [hd, mul_zero]

private theorem ggKGLn_T_card_fix {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [NeZero p] [Fact p.Prime] {ζ : L} (hζo : IsPrimitiveRoot ζ p)
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    (f : Fin s → Multiplicative (ZMod p)) :
    Nat.card {x : (Fin s → L) × (Fin r → K) // T f x = x} =
      Nat.card L ^ (Finset.univ.filter fun i => f i = 1).card * Nat.card (Fin r → K) := by
  classical
  have e1 : {x : (Fin s → L) × (Fin r → K) // T f x = x} ≃
      {x : (Fin s → L) × (Fin r → K) // ∀ i, f i ≠ 1 → x.1 i = 0} :=
    { toFun := fun x => ⟨x.1, (ggKGLn_T_fix_iff hζo T hT f x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (ggKGLn_T_fix_iff hζo T hT f x.1).mpr x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  have e2 : {x : (Fin s → L) × (Fin r → K) // ∀ i, f i ≠ 1 → x.1 i = 0} ≃
      ({i // f i = 1} → L) × (Fin r → K) :=
    { toFun := fun x => (fun i => x.1.1 i.1, x.1.2)
      invFun := fun y => ⟨(fun i => if h : f i = 1 then y.1 ⟨i, h⟩ else 0, y.2),
        fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
        by_cases hi : f i = 1
        · simp [hi]
        · simp [hi, x.2 i hi]
      right_inv := fun y => by
        refine Prod.ext (funext fun i => ?_) rfl
        simp [i.2] }
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, Nat.card_fun,
    Nat.card_eq_fintype_card (α := {i // f i = 1}), Fintype.card_subtype]

private theorem ggKGLn_T_injective {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [NeZero p] {ζ : L} (hζo : IsPrimitiveRoot ζ p)
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w)) :
    Function.Injective T := by
  intro f f' hff
  funext i
  have h1 := congrArg (fun (e : ((Fin s → L) × (Fin r → K)) ≃ₗ[K] _) =>
    (e (Pi.single i (1 : L), (0 : Fin r → K))).1 i) hff
  simp only [hT, Pi.single_eq_same, mul_one] at h1
  have h2 := hζo.pow_inj (ZMod.val_lt (toAdd (f i))) (ZMod.val_lt (toAdd (f' i))) h1
  rw [← ofAdd_toAdd (f i), ← ofAdd_toAdd (f' i)]
  congr 1
  exact ZMod.val_injective p h2

private theorem ggKGLn_T_one {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [Fact p.Prime] {ζ : L} 
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w)) :
    T 1 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨d, w⟩ := x
  rw [hT]
  change (fun i => ζ ^ (toAdd (1 : Fin s → Multiplicative (ZMod p)) i).val * d i, w) = (d, w)
  congr 1
  funext i
  change ζ ^ (toAdd (1 : Multiplicative (ZMod p))).val * d i = d i
  simp

private theorem ggKGLn_T_mul {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [NeZero p] [Fact p.Prime] {ζ : L} (hζ : ζ ^ p = 1)
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    (f g : Fin s → Multiplicative (ZMod p)) : T (f * g) = (T g).trans (T f) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨d, w⟩ := x
  rw [hT, LinearEquiv.trans_apply,
    show (T g) (d, w) = (fun i => ζ ^ (toAdd (g i)).val * d i, w) from hT g d w, hT]
  congr 1
  funext i
  rw [Pi.mul_apply, toAdd_mul, CoordSL.pow_val_add hζ, mul_assoc, mul_left_comm]

private theorem ggKGLn_T_single {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} {ζ : L} 
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    (f : Fin s → Multiplicative (ZMod p)) (j : Fin s) (v : L) :
    T f (Pi.single j v, (0 : Fin r → K)) =
      (Pi.single j (ζ ^ (toAdd (f j)).val * v), 0) := by
  rw [hT]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [Pi.single_eq_of_ne hi]

private theorem ggKGLn_T_sub_self_single {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [Fact p.Prime] {ζ : L} 
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    {f : Fin s → Multiplicative (ZMod p)} {j : Fin s}
    (hf : ∀ j', j' ≠ j → f j' = 1) (x : (Fin s → L) × (Fin r → K)) :
    T f x - x = (Pi.single j ((ζ ^ (toAdd (f j)).val - 1) * x.1 j), 0) := by
  obtain ⟨d, w⟩ := x
  rw [hT]
  refine Prod.ext (funext fun j' => ?_) (by simp)
  by_cases hj : j' = j
  · subst hj; simp [sub_mul]
  · simp only [Prod.fst_sub, Pi.sub_apply, Pi.single_eq_of_ne hj]
    rw [hf j' hj]
    simp


private theorem ggKGLn_monomial_data {K : Type} [Field K] [Fintype K] {L : Type} [Field L] [Algebra K L] 
    {s r p : ℕ} [NeZero p] [Fact p.Prime] {ζ : L} (hζo : IsPrimitiveRoot ζ p)
    (hL : 1 < Nat.card L)
    (hroots : ∀ (a : ZMod p) (θ : L →ₗ[K] L), Function.Injective θ →
      (∀ u, θ (ζ * u) = ζ ^ a.val * θ u) → a = 1 ∨ a = -1)
    (T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → L) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → L) × (Fin r → K)))
    (hT : ∀ f d w, T f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w))
    (H : ((Fin s → L) × (Fin r → K)) ≃ₗ[K] ((Fin s → L) × (Fin r → K)))
    (hH : ∀ f, ∃ f', ∀ x, H (T f x) = T f' (H x)) :
    ∃ (π : Equiv.Perm (Fin s)) (ε : Fin s → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', (∀ x, H (T f x) = T f' (H x)) → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  choose α hα using hH
  have hinj := ggKGLn_T_injective hζo T hT
  have hαuniq : ∀ f f', (∀ x, H (T f x) = T f' (H x)) → f' = α f := by
    intro f f' hf
    apply hinj
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := H.surjective y
    rw [← hf x, hα f x]
  have hT1 := ggKGLn_T_one T hT
  have hα1 : α 1 = 1 := by
    have h := hαuniq 1 1 (by intro x; rw [hT1]; rfl)
    exact h.symm
  have hTmul := ggKGLn_T_mul hζp T hT
  have hαmul : ∀ f g, α (f * g) = α f * α g := by
    intro f g
    apply hinj
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := H.surjective y
    calc T (α (f * g)) (H x) = H (T (f * g) x) := (hα (f * g) x).symm
      _ = H (((T g).trans (T f)) x) := by rw [hTmul]
      _ = H ((T f) ((T g) x)) := rfl
      _ = (T (α f)) (H ((T g) x)) := (hα f ((T g) x))
      _ = (T (α f)) ((T (α g)) (H x)) := by rw [hα g x]
      _ = ((T (α g)).trans (T (α f))) (H x) := rfl
      _ = T (α f * α g) (H x) := by rw [hTmul]
  let αh : (Fin s → Multiplicative (ZMod p)) →* (Fin s → Multiplicative (ZMod p)) :=
    { toFun := α, map_one' := hα1, map_mul' := hαmul }
  have hκpos : 0 < Nat.card (Fin r → K) := Nat.card_pos
  have hsupp : ∀ f, (Finset.univ.filter fun j => α f j ≠ 1).card =
      (Finset.univ.filter fun j => f j ≠ 1).card := by
    intro f
    have hbij : Nat.card {x : (Fin s → L) × (Fin r → K) // T f x = x}
        = Nat.card {x : (Fin s → L) × (Fin r → K) // T (α f) x = x} := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun x => ⟨H x.1, ?_⟩
          invFun := fun y => ⟨H.symm y.1, ?_⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun y => Subtype.ext (by simp) }
      · rw [← hα f x.1, x.2]
      · have h1 : H (T f (H.symm y.1)) = H (H.symm y.1) := by
          rw [hα f (H.symm y.1), LinearEquiv.apply_symm_apply]
          exact y.2
        exact H.injective h1
    have h1 : Nat.card L ^ (Finset.univ.filter fun j => f j = 1).card * Nat.card (Fin r → K) =
        Nat.card L ^ (Finset.univ.filter fun j => α f j = 1).card * Nat.card (Fin r → K) := by
      rw [← ggKGLn_T_card_fix hζo T hT f, ← ggKGLn_T_card_fix hζo T hT (α f)]
      exact hbij
    have h3 : (Finset.univ.filter fun j => α f j = 1).card =
        (Finset.univ.filter fun j => f j = 1).card :=
      Nat.pow_right_injective hL (Nat.eq_of_mul_eq_mul_right hκpos h1).symm
    have h4 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => α f j = 1)
    have h5 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => f j = 1)
    simp only [ne_eq]
    omega
  have hδ1 : ofAdd (1 : ZMod p) ≠ 1 := by
    rw [Ne, ofAdd_eq_one]; exact one_ne_zero
  set δ : Fin s → Fin s → Multiplicative (ZMod p) := fun i => Pi.mulSingle i (ofAdd (1 : ZMod p))
  have hδsupp : ∀ i, (Finset.univ.filter fun j => δ i j ≠ 1).card = 1 := by
    intro i
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simp [δ, hδ1]
    · simp [δ, hj]
  have hone : ∀ i, ∃ j, ∀ j', α (δ i) j' ≠ 1 ↔ j' = j := by
    intro i
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp ((hsupp (δ i)).trans (hδsupp i))
    exact ⟨j, fun j' => by simpa using Finset.ext_iff.mp hj j'⟩
  choose π₀ hπ₀ using hone
  set a : Fin s → ZMod p := fun i => toAdd (α (δ i) (π₀ i))
  have hαδ : ∀ i, α (δ i) = Pi.mulSingle (π₀ i) (ofAdd (a i)) := by
    intro i
    funext j
    by_cases hj : j = π₀ i
    · subst hj; simp [a]
    · rw [Pi.mulSingle_eq_of_ne hj]
      by_contra hne
      exact hj ((hπ₀ i j).mp hne)
  have hπinj : Function.Injective π₀ := by
    intro i i' hii
    by_contra hne
    have h1 := hsupp (δ i * δ i')
    rw [SpNS.filter_ne_one_card_mulSingle_mul hne, hαmul, hαδ, hαδ, ← hii, ← Pi.mulSingle_mul] at h1
    have h2 : (Finset.univ.filter fun j => (Pi.mulSingle (π₀ i) (ofAdd (a i) * ofAdd (a i')) :
        Fin s → Multiplicative (ZMod p)) j ≠ 1) ⊆ {π₀ i} := by
      intro x hx
      rw [Finset.mem_singleton]
      by_contra hxne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx (Pi.mulSingle_eq_of_ne hxne _)
    have h3 := (Finset.card_le_card h2).trans (Finset.card_singleton _).le
    omega
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζo.ne_one (Fact.out : p.Prime).one_lt)
  have hval1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have hblock : ∀ i (u : L), ∃ c : L,
      H (Pi.single i u, (0 : Fin r → K)) = (Pi.single (π₀ i) c, 0) := by
    intro i u
    set u' := (ζ - 1)⁻¹ * u with hu'
    have hf : ∀ j', j' ≠ i → δ i j' = 1 := by
      intro j' hj'; simp [δ, Pi.mulSingle_eq_of_ne hj']
    have hsub := ggKGLn_T_sub_self_single T hT (f := δ i) (j := i) hf (Pi.single i u', 0)
    have hval : (ζ ^ (toAdd (δ i i)).val - 1) * (Pi.single i u' : Fin s → L) i = u := by
      rw [Pi.single_eq_same]
      simp only [δ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one, hu']
      rw [← mul_assoc, mul_inv_cancel₀ hζ1, one_mul]
    have hrhs : (Pi.single i ((ζ ^ (toAdd (δ i i)).val - 1) * (Pi.single i u' : Fin s → L) i),
        (0 : Fin r → K)) = ((Pi.single i u : Fin s → L), (0 : Fin r → K)) := by
      rw [hval]
    have e1 : (Pi.single i u, (0 : Fin r → K)) =
        T (δ i) (Pi.single i u', 0) - (Pi.single i u', 0) := (hsub.trans hrhs).symm
    have hf1 : ∀ j', j' ≠ π₀ i → α (δ i) j' = 1 := by
      intro j' hj'; rw [hαδ, Pi.mulSingle_eq_of_ne hj']
    refine ⟨(ζ ^ (toAdd (α (δ i) (π₀ i))).val - 1) *
      (H (Pi.single i u', 0)).1 (π₀ i), ?_⟩
    rw [e1, map_sub, hα (δ i) (Pi.single i u', 0),
      ggKGLn_T_sub_self_single T hT (f := α (δ i)) (j := π₀ i) hf1 (H (Pi.single i u', 0))]
  choose c hc using hblock
  have hθadd : ∀ i (u v : L),
      (H (Pi.single i (u + v), (0 : Fin r → K))).1 (π₀ i) =
        (H (Pi.single i u, (0 : Fin r → K))).1 (π₀ i) +
          (H (Pi.single i v, (0 : Fin r → K))).1 (π₀ i) := by
    intro i u v
    have hp : ((Pi.single i u : Fin s → L) + (Pi.single i v : Fin s → L), (0 : Fin r → K)) =
        ((Pi.single i u : Fin s → L), (0 : Fin r → K)) +
          ((Pi.single i v : Fin s → L), (0 : Fin r → K)) := by
      rw [Prod.mk_add_mk]; simp
    rw [Pi.single_add, hp, map_add]
    rfl
  have hθsmul : ∀ i (c₀ : K) (u : L),
      (H (Pi.single i (c₀ • u), (0 : Fin r → K))).1 (π₀ i) =
        c₀ • (H (Pi.single i u, (0 : Fin r → K))).1 (π₀ i) := by
    intro i c₀ u
    have hp : (c₀ • (Pi.single i u : Fin s → L), (0 : Fin r → K)) =
        c₀ • ((Pi.single i u : Fin s → L), (0 : Fin r → K)) := by
      rw [Prod.smul_mk, smul_zero]
    rw [Pi.single_smul, hp, map_smul]
    rfl
  set θ : Fin s → (L →ₗ[K] L) := fun i =>
    { toFun := fun u => (H (Pi.single i u, (0 : Fin r → K))).1 (π₀ i)
      map_add' := hθadd i
      map_smul' := hθsmul i }
  have hθc : ∀ i u, H (Pi.single i u, (0 : Fin r → K)) = (Pi.single (π₀ i) (θ i u), 0) := by
    intro i u
    have h2 : θ i u = c i u := by
      have h3 := congrArg (fun x : (Fin s → L) × (Fin r → K) => x.1 (π₀ i)) (hc i u)
      simpa [θ] using h3
    rw [h2, hc i u]
  have hθζ : ∀ i u, θ i (ζ * u) = ζ ^ (a i).val * θ i u := by
    intro i u
    have e1 : (Pi.single i (ζ * u), (0 : Fin r → K)) = T (δ i) (Pi.single i u, 0) := by
      rw [ggKGLn_T_single T hT]
      refine Prod.ext (funext fun j => ?_) rfl
      by_cases hj : j = i
      · subst hj
        simp only [δ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
      · simp [δ, Pi.single_eq_of_ne hj]
    have e2 := hθc i (ζ * u)
    rw [e1, hα (δ i) (Pi.single i u, 0), hθc i u, ggKGLn_T_single T hT] at e2
    have e3 := congrArg (fun x : (Fin s → L) × (Fin r → K) => x.1 (π₀ i)) e2
    simp only [Pi.single_eq_same] at e3
    exact e3.symm
  have hθinj : ∀ i, Function.Injective (θ i) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 := hθc i u
    rw [hu, Pi.single_zero, Prod.mk_zero_zero] at h1
    have h2 : H (Pi.single i u, (0 : Fin r → K)) = H 0 := h1.trans (map_zero H).symm
    have h3 := congrArg (fun x : (Fin s → L) × (Fin r → K) => x.1 i) (H.injective h2)
    simpa using h3
  have ha1 : ∀ i, a i = 1 ∨ a i = -1 := fun i => hroots (a i) (θ i) (hθinj i) (hθζ i)
  refine ⟨Equiv.ofBijective π₀ hπinj.bijective_of_finite, a, ha1, fun f f' hff' i => ?_⟩
  have hf' : f' = α f := hαuniq f f' hff'
  subst hf'
  have hfprod : f = ∏ j, δ j ^ (toAdd (f j)).val := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle f]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [δ]
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val,
      ofAdd_toAdd]
  have hαf : α f = ∏ j, (Pi.mulSingle (π₀ j) (ofAdd (a j))) ^ (toAdd (f j)).val := by
    have e : α f = αh f := rfl
    rw [e]
    conv_lhs => rw [hfprod]
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow]
    congr 1
    exact hαδ j
  rw [Equiv.ofBijective_apply, hαf, Finset.prod_apply, Finset.prod_eq_single i]
  · rw [Pi.pow_apply, Pi.mulSingle_eq_same, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
      ZMod.natCast_zmod_val, mul_comm]
  · intro j _ hji
    rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne (fun h' => hji (hπinj h').symm), one_pow]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

end Abs

section SLFrame

open Matrix Polynomial

private theorem ggKGLn_aeval_root_pow_eq_zero {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {p : ℕ} {a : ZMod p}
    (θ : AdjoinRoot g →ₗ[K] AdjoinRoot g) (hθ : Function.Injective θ)
    (hθζ : ∀ u, θ (AdjoinRoot.root g * u) = AdjoinRoot.root g ^ a.val * θ u) :
    aeval (AdjoinRoot.root g ^ a.val) g = 0 := by
  set ζ := AdjoinRoot.root g with hζ
  have key : ∀ (P : K[X]) (u : AdjoinRoot g), θ (aeval ζ P * u) = aeval (ζ ^ a.val) P * θ u := by
    intro P
    induction P using Polynomial.induction_on with
    | C c => intro u; rw [aeval_C, aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add P Q hP hQ =>
      intro u
      rw [map_add, map_add, add_mul, add_mul, map_add, hP, hQ]
    | monomial n c ih =>
      intro u
      have e1 : aeval ζ (C c * X ^ (n + 1)) * u = aeval ζ (C c * X ^ n) * (ζ * u) := by
        simp only [map_mul, map_pow, aeval_X, aeval_C, pow_succ]
        ring
      have e2 : aeval (ζ ^ a.val) (C c * X ^ (n + 1)) * θ u =
          aeval (ζ ^ a.val) (C c * X ^ n) * (ζ ^ a.val * θ u) := by
        simp only [map_mul, map_pow, aeval_X, aeval_C, pow_succ]
        ring
      rw [e1, e2, ih, hθζ]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hθ) 1
  have h1 := key g u
  rw [hζ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul, map_zero, hu, mul_one] at h1
  exact h1.symm



private theorem ggKGLn_exists_irreducible_dvd_cyclotomic {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) :
    ∃ g : Polynomial K, Irreducible g ∧ g ∣ Polynomial.cyclotomic p K := by
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (cyclotomic_ne_zero p K), natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  exact WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p K)

theorem ggKGLn_signedEltSC_specialLinear {K : Type} [Field K] [Finite K] {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0)
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusSignedEltSC p (Matrix.SpecialLinearGroup (Fin d) K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty K := ⟨0⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq
  obtain ⟨g, hg, hgd⟩ := ggKGLn_exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζo := CoordSL.root_isPrimitiveRoot (g := g) hp hpK0 hgd
  have hCdet : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : (CoordSL.rootMat g) ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  intro E hE h3 hsc
  set S : Set (Matrix (Fin d) (Fin d) K) :=
    {x | ∃ e ∈ E, ((e : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = x}
    with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := TableB.IsElemAbelian.comm hE he he'
    have h2 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin d) K =>
      ((y : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
    exact h2
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hE.2 e he
    have h2 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin d) K =>
      ((y : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using h2
  obtain ⟨s, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd S hSc hSp
  have hnf : ∀ e ∈ E, ∃ k : Fin s → ℕ,
      e = SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀
        (SLNS.nsSL ε hCdet k) := by
    intro e he
    obtain ⟨k, hk⟩ := hframe _ ⟨e, he, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : e * A₀ = A₀ * SLNS.nsSL ε hCdet k := Subtype.ext hk
    have h2 : e = A₀ * SLNS.nsSL ε hCdet k * A₀⁻¹ := by rw [← h1, mul_inv_cancel_right]
    rw [SLRep.ggFrame_apply, MonoidHom.id_apply]
    exact h2
  let τ : (Fin s → Multiplicative (ZMod p)) →* Matrix.SpecialLinearGroup (Fin d) K :=
    { toFun := fun f => SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀
        (SLNS.nsSL ε hCdet fun i => (toAdd (f i)).val)
      map_one' := by
        rw [SLRep.ggFrame_apply, MonoidHom.id_apply]
        have h0 : (fun i => (toAdd ((1 : Fin s → Multiplicative (ZMod p)) i)).val) = 0 := by
          funext i; rw [Pi.one_apply, Pi.zero_apply, toAdd_one, ZMod.val_zero]
        rw [h0, SLNS.nsSL_zero, mul_one, mul_inv_cancel]
      map_mul' := fun f f' => by
        rw [SLRep.ggFrame_apply, MonoidHom.id_apply, SLRep.ggFrame_apply, MonoidHom.id_apply,
          SLRep.ggFrame_apply, MonoidHom.id_apply]
        have hcongr : SLNS.nsSL ε hCdet (fun i => (toAdd ((f * f') i)).val) =
            SLNS.nsSL ε hCdet ((fun i => (toAdd (f i)).val) + fun i => (toAdd (f' i)).val) :=
          SLNS.nsSL_congr ε hCdet hCp fun i => by
            rw [Pi.mul_apply, toAdd_mul, Pi.add_apply, ZMod.val_add]
            exact Nat.mod_mod _ _
        rw [hcongr, ← SLNS.nsSL_mul]
        group }
  have hτapp : ∀ f, τ f = SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ (SLNS.nsSL ε hCdet fun i => (toAdd (f i)).val) := fun f => rfl
  have hτE : τ.range = E := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      refine hsc _ (fun e he => ?_) ?_
      · obtain ⟨k, hk⟩ := hnf e he
        rw [hk, hτapp, ← map_mul, ← map_mul, SLNS.nsSL_comm]
      · rw [hτapp, SLRep.ggFrame_apply, MonoidHom.id_apply]
        have h1 : (SLNS.nsSL ε hCdet fun i => (toAdd (f i)).val) ^ p = 1 :=
          SLNS.nsSL_pow_p ε hCdet hCp _
        rw [conj_pow, h1, mul_one, mul_inv_cancel]
    · intro e he
      obtain ⟨k, hk⟩ := hnf e he
      refine ⟨fun i => ofAdd (k i : ZMod p), ?_⟩
      rw [hk, hτapp, SLRep.ggFrame_apply, MonoidHom.id_apply]
      congr 2
      exact (SLNS.nsSL_congr ε hCdet hCp fun i => by
        rw [toAdd_ofAdd, ZMod.val_natCast, Nat.mod_mod]).symm
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h1 : SLNS.nsSL ε hCdet (fun i => (toAdd (f i)).val) = 1 := by
      have h2 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin d) K =>
        A₀⁻¹ * y * A₀) hf
      rw [hτapp, SLRep.ggFrame_apply, MonoidHom.id_apply] at h2
      group at h2
      exact h2
    have hdim : 0 < (CoordSL.rootPB g).dim := by
      rw [CoordSL.rootPB, AdjoinRoot.powerBasis_dim]
      exact hg.natDegree_pos
    haveI : Nonempty (Fin (CoordSL.rootPB g).dim) := ⟨⟨0, hdim⟩⟩
    have h3 : ∀ j : Fin s, (CoordSL.rootMat g) ^ ((toAdd (f j)).val) = 1 := by
      intro j
      ext a b
      have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
        M (ε.symm (Sum.inl (a, j)))
          (ε.symm (Sum.inl (b, j)))) (congrArg Subtype.val h1)
      change SLNS.nsMat ε (CoordSL.rootMat g) (fun i => (toAdd (f i)).val)
        (ε.symm (Sum.inl (a, j))) (ε.symm (Sum.inl (b, j))) = _ at h4
      rw [SLNS.nsMat_block] at h4
      simpa [Matrix.one_apply] using h4
    funext j
    have h5 : p ∣ (toAdd (f j)).val := by
      by_contra h
      have hu := CoordSL.isUnit_rootMat_pow_sub (g := g) hp hpK' hpK0 hgd
        ((toAdd (f j)).val) h (1 : K)
      rw [h3 j] at hu
      have hu' : IsUnit (0 : Matrix (Fin (CoordSL.rootPB g).dim) (Fin (CoordSL.rootPB g).dim) K) := by
        simpa using hu
      exact not_isUnit_zero hu'
    apply Multiplicative.toAdd.injective
    rw [Pi.one_apply, toAdd_one, ← ZMod.natCast_zmod_val (toAdd (f j))]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr h5
  have hτof : ∀ f : Fin s → Multiplicative (ZMod p), τ f =
      CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp
        (ofAdd (fun i => toAdd (f i))) := fun f => rfl
  have hrange : (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp).range = E := by
    rw [← hτE]
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨ofAdd (fun i => toAdd (f i)), (hτof f).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨fun i => ofAdd ((toAdd t) i), ?_⟩
      rw [hτof]
      congr 1
  have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
  have hone : (1 : (ZMod p)ˣ) ∈ CoordSL.galExp g hζp := (CoordSL.galExp g hζp).one_mem
  have hneg : (-1 : (ZMod p)ˣ) ∈ CoordSL.galExp g hζp := by
    refine CoordSpNs.card_mem_galExp (g := g) hζp (u := -1) ?_
    have hzero : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (Nat.card K + 1) p).mpr hpq
    have hcast : (Nat.card K : ZMod p) + 1 = 0 := by simpa using hzero
    have hu0 : (Nat.card K : ZMod p) = -1 := add_eq_zero_iff_eq_neg.mp hcast
    simp [Units.val_neg, Units.val_one, hu0]
    rw [← Nat.card_eq_fintype_card]
    exact hu0.symm
  refine ⟨s, τ, hτinj, hτE, ?_, ?_, ?_⟩
  ·
    intro i₀
    let η : Fin s → (ZMod p)ˣ := Function.update (1 : Fin s → (ZMod p)ˣ) i₀ (-1)
    have hη : ∀ l, η l ∈ CoordSL.galExp g hζp := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simpa [η, Function.update_self] using hneg
      · simpa [η, Function.update_of_ne hl] using hone
    obtain ⟨w, -, hw⟩ := CoordSL.exists_move_mem g
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp hζp hrange
      (Equiv.refl (Fin s)) η hη
    refine ⟨w⁻¹, fun f => ?_⟩
    have hfun : (fun l => (η l : ZMod p) * toAdd (f l)) =
        fun l => toAdd (SpCoord.sgnAut i₀ f l) := by
      funext l
      rw [SpCoord.sgnAut_apply]
      by_cases hl : l = i₀
      · subst hl; simp [η, Function.update_self]
      · simp [η, Function.update_of_ne hl]
    calc w⁻¹ * τ f * (w⁻¹)⁻¹ = w⁻¹ * τ f * w := by rw [inv_inv]
      _ = w⁻¹ * CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε
            hCdet hCp (ofAdd (fun l => toAdd (f l))) * w := by rw [hτof f]
      _ = CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp
            (ofAdd (fun l => (η l : ZMod p) * toAdd (f l))) := hw (fun l => toAdd (f l))
      _ = CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp
            (ofAdd (fun l => toAdd (SpCoord.sgnAut i₀ f l))) := by rw [hfun]
      _ = τ (SpCoord.sgnAut i₀ f) := (hτof _).symm
  ·
    intro σ
    obtain ⟨w, -, hw⟩ := CoordSL.exists_move_mem g
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp hζp hrange
      σ⁻¹ (fun _ => 1) (fun _ => hone)
    refine ⟨w⁻¹, fun f => ?_⟩
    have hfun : (fun l => ((1 : (ZMod p)ˣ) : ZMod p) * toAdd (f (σ⁻¹ l))) =
        fun l => toAdd (SpCoord.permAut σ f l) := by
      funext l
      rw [SpCoord.permAut_apply, Units.val_one, one_mul]
      rfl
    calc w⁻¹ * τ f * (w⁻¹)⁻¹ = w⁻¹ * τ f * w := by rw [inv_inv]
      _ = w⁻¹ * CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε
            hCdet hCp (ofAdd (fun l => toAdd (f l))) * w := by rw [hτof f]
      _ = CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp
            (ofAdd (fun l => ((1 : (ZMod p)ˣ) : ZMod p) * toAdd (f (σ⁻¹ l)))) :=
          hw (fun l => toAdd (f l))
      _ = CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp
            (ofAdd (fun l => toAdd (SpCoord.permAut σ f l))) := by rw [hfun]
      _ = τ (SpCoord.permAut σ f) := (hτof _).symm
  · intro g₀ hg₀
    have hroots : ∀ (a : ZMod p) (θ : AdjoinRoot g →ₗ[K] AdjoinRoot g), Function.Injective θ →
        (∀ u, θ (AdjoinRoot.root g * u) = AdjoinRoot.root g ^ a.val * θ u) → a = 1 ∨ a = -1 :=
      fun a θ hθ hθζ => SpNS.eq_one_or_eq_neg_one_of_aeval hp hp2 hpK0 hgd hpq
        (ggKGLn_aeval_root_pow_eq_zero θ hθ hθζ)
    let T : (Fin s → Multiplicative (ZMod p)) → ((Fin s → AdjoinRoot g) × (Fin r → K)) ≃ₗ[K]
        ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
      fun f => SpNS.torEquiv (K := K) (L := AdjoinRoot g) (κ := Fin r) hζo.pow_eq_one f
    let g₁ : Matrix.SpecialLinearGroup (Fin d) K := A₀⁻¹ * g₀ * A₀
    let H : ((Fin s → AdjoinRoot g) × (Fin r → K)) ≃ₗ[K]
        ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
      (CoordSL.frameCoords (g := g) ε).trans
        (((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))
            (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL g₁))).trans
          (CoordSL.frameCoords (g := g) ε).symm)
    have hT : ∀ f d w, T f (d, w) =
        (fun i => AdjoinRoot.root g ^ (toAdd (f i)).val * d i, w) :=
      fun f d w => SpNS.torEquiv_apply (K := K) (L := AdjoinRoot g) (κ := Fin r)
        hζo.pow_eq_one f d w
    have hgl : ∀ v : Fin d → K,
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))
            (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL g₁))) v =
          (g₁ : Matrix (Fin d) (Fin d) K) *ᵥ v := by
      intro v
      change (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL g₁) :
        (Fin d → K) →ₗ[K] (Fin d → K)) v = _
      rw [Matrix.GeneralLinearGroup.toLin_apply]
      rfl
    have hHrel : ∀ f f', g₀ * τ f * g₀⁻¹ = τ f' → ∀ x, H (T f x) = T f' (H x) := by
      intro f f' hff' x
      obtain ⟨x1, x2⟩ := x
      have hmatrix : SLNS.nsSL ε hCdet (fun i => (toAdd (f' i)).val) =
          g₁ * SLNS.nsSL ε hCdet (fun i => (toAdd (f i)).val) * g₁⁻¹ := by
        have h3 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin d) K =>
          A₀⁻¹ * y * A₀) hff'
        rw [hτapp f', hτapp f, SLRep.ggFrame_apply, MonoidHom.id_apply,
          SLRep.ggFrame_apply, MonoidHom.id_apply] at h3
        rw [show g₁ = A₀⁻¹ * g₀ * A₀ from rfl]
        group at h3 ⊢
        exact h3.symm
      have hmat : (g₁ : Matrix (Fin d) (Fin d) K) *
            SLNS.nsMat ε (CoordSL.rootMat g) (fun i => (toAdd (f i)).val) =
          SLNS.nsMat ε (CoordSL.rootMat g) (fun i => (toAdd (f' i)).val) *
            (g₁ : Matrix (Fin d) (Fin d) K) := by
        have h5 : g₁ * SLNS.nsSL ε hCdet (fun i => (toAdd (f i)).val) =
            SLNS.nsSL ε hCdet (fun i => (toAdd (f' i)).val) * g₁ := by
          rw [hmatrix]; group
        have h6 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin d) K =>
          (y : Matrix (Fin d) (Fin d) K)) h5
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h6
        exact h6
      have hHapp : ∀ y, H y = (CoordSL.frameCoords (g := g) ε).symm
          ((g₁ : Matrix (Fin d) (Fin d) K) *ᵥ (CoordSL.frameCoords (g := g) ε) y) := by
        intro y
        simp only [H, LinearEquiv.trans_apply, LinearEquiv.coe_coe, hgl]
      rw [hHapp (T f (x1, x2)), hHapp (x1, x2)]
      apply (CoordSL.frameCoords (g := g) ε).injective
      rw [LinearEquiv.apply_symm_apply,
        show (CoordSL.frameCoords (g := g) ε) (T f (x1, x2)) =
          (CoordSL.frameCoords (g := g) ε)
            (fun i => AdjoinRoot.root g ^ (toAdd (f i)).val * x1 i, x2) from by
              rw [hT f x1 x2],
        show (CoordSL.frameCoords (g := g) ε) (T f' _) =
          (CoordSL.frameCoords (g := g) ε)
            (fun i => AdjoinRoot.root g ^ (toAdd (f' i)).val *
              ((CoordSL.frameCoords (g := g) ε).symm
                ((g₁ : Matrix (Fin d) (Fin d) K) *ᵥ
                  (CoordSL.frameCoords (g := g) ε) (x1, x2))).1 i,
              ((CoordSL.frameCoords (g := g) ε).symm
                ((g₁ : Matrix (Fin d) (Fin d) K) *ᵥ
                  (CoordSL.frameCoords (g := g) ε) (x1, x2))).2) from by
              rw [hT f' _ _],
        ← CoordSL.nsMat_mulVec_frameCoords (g := g) ε (fun i => (toAdd (f i)).val) (x1, x2),
        ← CoordSL.nsMat_mulVec_frameCoords (g := g) ε (fun i => (toAdd (f' i)).val)
          ((CoordSL.frameCoords (g := g) ε).symm
            ((g₁ : Matrix (Fin d) (Fin d) K) *ᵥ (CoordSL.frameCoords (g := g) ε) (x1, x2))),
        LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec]
    have hH : ∀ f, ∃ f', ∀ x, H (T f x) = T f' (H x) := by
      intro f
      have hτfE : τ f ∈ E := by rw [← hτE]; exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
      have hmem : g₀ * τ f * g₀⁻¹ ∈ E := hg₀ (τ f) hτfE
      have hmem' : g₀ * τ f * g₀⁻¹ ∈ τ.range := by rw [hτE]; exact hmem
      obtain ⟨f', hf'⟩ := MonoidHom.mem_range.mp hmem'
      exact ⟨f', hHrel f f' hf'.symm⟩
    obtain ⟨π, ε', hε', hrel⟩ :=
      ggKGLn_monomial_data hζo Finite.one_lt_card hroots T hT H hH
    exact ⟨π, ε', hε', fun f f' hff' => hrel f f' (hHrel f f' hff')⟩

end SLFrame

end CFSG.StandardType

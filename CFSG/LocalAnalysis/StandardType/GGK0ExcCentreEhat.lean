module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreMarks
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreRational
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreSupport
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreNodeExp
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreKernelRoots
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreCount
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreOrbitCount

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lk0xpa5_zmod_natCast_val {p : ℕ} [NeZero p] (i : ZMod p) :
    ((i.val : ℕ) : ZMod p) = i := by
  apply ZMod.val_injective p
  rw [ZMod.val_natCast_of_lt (ZMod.val_lt i)]

private lemma lk0xpa5_zeta_pow_inj {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (fun k : ZMod p => ζ ^ k.val) := by
  intro a b hab
  apply ZMod.val_injective p
  have hmod : a.val ≡ b.val [MOD p] := by
    have h := (pow_eq_pow_iff_modEq (x := ζ)).mp hab
    rwa [← hζ.eq_orderOf] at h
  exact hmod.eq_of_lt_of_lt (ZMod.val_lt a) (ZMod.val_lt b)

private lemma lk0xpa5_zeta_pow_add {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (a b : ZMod p) :
    ζ ^ a.val * ζ ^ b.val = ζ ^ (a + b).val := by
  rw [← pow_add]
  apply (pow_eq_pow_iff_modEq (x := ζ)).mpr
  rw [← hζ.eq_orderOf]
  have h : ((a.val + b.val : ℕ) : ZMod p) = (((a + b).val : ℕ) : ZMod p) := by
    rw [Nat.cast_add, lk0xpa5_zmod_natCast_val a, lk0xpa5_zmod_natCast_val b,
      lk0xpa5_zmod_natCast_val (a + b)]
  exact (ZMod.natCast_eq_natCast_iff _ _ p).mp h

private lemma lk0xpa5_rootChar_mul {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply]
  rw [Finset.prod_congr rfl (fun i _ => mul_zpow (a i) (b i) (v i)),
    Finset.prod_mul_distrib]

private noncomputable def lk0xpa5_Tsub {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Subgroup (Fin ρ.tau.rank → Omegaˣ) where
  carrier := {b | ∀ i, b i ^ p = 1}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    rw [Pi.mul_apply, mul_pow, ha i, hb i, one_mul]
  inv_mem' := by
    intro a ha i
    rw [Pi.inv_apply, inv_pow, ha i, inv_one]

private lemma lk0xpa5_e_one {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) :
    (e ⟨1, fun _ => by simp⟩).1 = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : IsPrimitiveRoot ρ.zeta p := IsPrimitiveRoot.iff_orderOf.mpr ρ.zeta_order
  funext i
  apply lk0xpa5_zeta_pow_inj hζ
  calc
    ρ.zeta ^ ((e ⟨1, fun _ => by simp⟩).1 i).val
        = rootChar (1 : Fin ρ.tau.rank → Omegaˣ) (ρ.nodeMap (Pi.single i 1)) :=
          (he ⟨1, fun _ => by simp⟩ i).symm
    _ = ρ.zeta ^ ((0 : ZMod p).val) := by simp [rootChar]

private lemma lk0xpa5_e_add {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime)
    (b b' : Fin ρ.tau.rank → Omegaˣ) (hb : ∀ i, b i ^ p = 1) (hb' : ∀ i, b' i ^ p = 1)
    (hbb' : ∀ i, (b * b') i ^ p = 1) :
    (e ⟨b * b', hbb'⟩).1 = (e ⟨b, hb⟩).1 + (e ⟨b', hb'⟩).1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : IsPrimitiveRoot ρ.zeta p := IsPrimitiveRoot.iff_orderOf.mpr ρ.zeta_order
  funext i
  apply lk0xpa5_zeta_pow_inj hζ
  calc
    ρ.zeta ^ ((e ⟨b * b', hbb'⟩).1 i).val
        = rootChar (b * b') (ρ.nodeMap (Pi.single i 1)) := (he ⟨b * b', hbb'⟩ i).symm
    _ = rootChar b (ρ.nodeMap (Pi.single i 1)) *
          rootChar b' (ρ.nodeMap (Pi.single i 1)) := lk0xpa5_rootChar_mul b b' _
    _ = ρ.zeta ^ ((e ⟨b, hb⟩).1 i).val * ρ.zeta ^ ((e ⟨b', hb'⟩).1 i).val := by
          rw [he ⟨b, hb⟩ i, he ⟨b', hb'⟩ i]
    _ = ρ.zeta ^ (((e ⟨b, hb⟩).1 + (e ⟨b', hb'⟩).1) i).val :=
          lk0xpa5_zeta_pow_add hζ ((e ⟨b, hb⟩).1 i) ((e ⟨b', hb'⟩).1 i)

private noncomputable def lk0xpa5_Ehom {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) :
    lk0xpa5_Tsub ρ →* Multiplicative (Fin ρ.row.diagram.marks.length → ZMod p) where
  toFun b := Multiplicative.ofAdd fun i => (e ⟨b.1, b.2⟩).1 i
  map_one' := congrArg Multiplicative.ofAdd (lk0xpa5_e_one ρ e he hp)
  map_mul' b b' := congrArg Multiplicative.ofAdd
    (lk0xpa5_e_add ρ e he hp b.1 b'.1 b.2 b'.2
      (fun j => by rw [Pi.mul_apply, mul_pow, b.2 j, b'.2 j, one_mul]))

private noncomputable def lk0xpa5_Bsub {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) : Subgroup (lk0xpa5_Tsub ρ) where
  carrier := {b | (∀ i, i ∉ posNodes ρ → (lk0xpa5_Ehom ρ e he hp b).toAdd i = 0) ∧
    (∀ i, (lk0xpa5_Ehom ρ e he hp b).toAdd (ρ.row.nodePerm i) =
      (lk0xpa5_Ehom ρ e he hp b).toAdd i)}
  one_mem' := by
    have h1 : (lk0xpa5_Ehom ρ e he hp 1).toAdd = 0 := by rw [map_one]; rfl
    constructor <;> intro i <;> simp [h1]
  mul_mem' := by
    intro a b ha hb
    have hmul : (lk0xpa5_Ehom ρ e he hp (a * b)).toAdd =
        (lk0xpa5_Ehom ρ e he hp a).toAdd + (lk0xpa5_Ehom ρ e he hp b).toAdd := by
      rw [map_mul]; rfl
    constructor
    · intro i hi
      rw [hmul, Pi.add_apply, ha.1 i hi, hb.1 i hi, add_zero]
    · intro i
      simp only [hmul, Pi.add_apply, ha.2 i, hb.2 i]
  inv_mem' := by
    intro a ha
    have hinv : (lk0xpa5_Ehom ρ e he hp a⁻¹).toAdd = -(lk0xpa5_Ehom ρ e he hp a).toAdd := by
      rw [map_inv]; rfl
    constructor
    · intro i hi
      rw [hinv, Pi.neg_apply, ha.1 i hi, neg_zero]
    · intro i
      simp only [hinv, Pi.neg_apply, ha.2 i]

private noncomputable def lk0xpa5_f {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    lk0xpa5_Tsub ρ →* ModGL ρ.tau Omega where
  toFun b := rootDiagUnit ρ.tau b.1
  map_one' := rootDiagUnit_one
  map_mul' b b' := rootDiagUnit_mul b.1 b'.1

private lemma lk0xpa5_f_injective {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Function.Injective (lk0xpa5_f ρ) := by
  intro a b hab
  apply Subtype.ext
  exact rootDiagUnit_injective hab

private noncomputable def lk0xpa5_Ehat {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) : Subgroup (ModGL ρ.tau Omega) :=
  (lk0xpa5_Bsub ρ e he hp).map (lk0xpa5_f ρ)

private noncomputable def lk0xpa5_W {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Type :=
  {t : Fin ρ.row.diagram.marks.length → ZMod p //
    (∀ i, i ∉ posNodes ρ → t i = 0) ∧ (∀ i, t (ρ.row.nodePerm i) = t i) ∧
    ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0}

private noncomputable def lk0xpa5_eT {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0}) :
    lk0xpa5_Tsub ρ ≃
      {t : Fin ρ.row.diagram.marks.length → ZMod p //
        ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0} where
  toFun b := e ⟨b.1, b.2⟩
  invFun t := ⟨(e.symm t).1, (e.symm t).2⟩
  left_inv b := by
    apply Subtype.ext
    simpa using congrArg Subtype.val (Equiv.symm_apply_apply e ⟨b.1, b.2⟩)
  right_inv t := by
    apply Subtype.ext
    dsimp only
    rw [show (⟨(e.symm t).1, (e.symm t).2⟩ : {b : Fin ρ.tau.rank → Omegaˣ //
        ∀ i, b i ^ p = 1}) = e.symm t from Subtype.ext rfl]
    exact congrArg Subtype.val (Equiv.apply_symm_apply e t)

private lemma lk0xpa5_eT_apply {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) (b : lk0xpa5_Tsub ρ) :
    (lk0xpa5_eT ρ e b).1 = (lk0xpa5_Ehom ρ e he hp b).toAdd := rfl

private noncomputable def lk0xpa5_BsubEquivW {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0})
    (he : ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val)
    (hp : p.Prime) : lk0xpa5_Bsub ρ e he hp ≃ lk0xpa5_W ρ where
  toFun b :=
    ⟨(lk0xpa5_eT ρ e b.1).1, b.2.1, b.2.2, (lk0xpa5_eT ρ e b.1).2⟩
  invFun t :=
    ⟨(lk0xpa5_eT ρ e).symm ⟨t.1, t.2.2.2⟩, by
      have hs : (lk0xpa5_Ehom ρ e he hp
          ((lk0xpa5_eT ρ e).symm ⟨t.1, t.2.2.2⟩)).toAdd = t.1 := by
        rw [← lk0xpa5_eT_apply ρ e he hp]
        exact congrArg Subtype.val
          (Equiv.apply_symm_apply (lk0xpa5_eT ρ e) ⟨t.1, t.2.2.2⟩)
      exact ⟨fun i hi => by rw [hs]; exact t.2.1 i hi,
        fun i => by rw [hs]; exact t.2.2.1 i⟩⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    simp [lk0xpa5_eT]
  right_inv t := by
    apply Subtype.ext
    dsimp only
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (lk0xpa5_eT ρ e) ⟨t.1, t.2.2.2⟩)

theorem PA5_assembly
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p) (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hrz : 2 ≤ ρ.row.D.rZ) :
    ∃ Ehat : Subgroup (ModGL ρ.tau Omega),
      (∀ z ∈ Ehat, z ∈ ρ.setup.D.torus ∧ z ^ p = 1 ∧ ∃ b : Fin ρ.tau.rank → Omegaˣ,
        rootDiagUnit ρ.tau b = z ∧ ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) ∧
      Nat.card Ehat = p ^ ρ.row.D.rZ := by
  classical
  have hp : p.Prime := hpair.1
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, he⟩ := PA1_nodeExp_equiv hp ρ
  obtain ⟨hS, hnz⟩ := PA4'_orbit_coefficient hpair hc ρ hrz
  have hcardW : Nat.card (lk0xpa5_W ρ) =
      p ^ (numOrbitsOn ρ.row.nodePerm (posNodes ρ) - 1) := by
    simpa only [lk0xpa5_W] using
      PA3_card_invariant_hyperplane hp ρ.row.nodePerm (posNodes ρ) hS
        (fun i => (ρ.row.diagram.marks.getD i.val 0 : ZMod p))
        (fun i => by rw [PA0_marks_perm_invariant ρ i]) hnz
  have hrZ : numOrbitsOn ρ.row.nodePerm (posNodes ρ) - 1 = ρ.row.D.rZ := by
    have h := PA4_rZ_eq_numOrbits ρ
    omega
  have hcardW' : Nat.card (lk0xpa5_W ρ) = p ^ ρ.row.D.rZ := by
    rw [hcardW, hrZ]
  refine ⟨lk0xpa5_Ehat ρ e he hp, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hz
    have htorus : rootDiagUnit ρ.tau b.1 ∈ ρ.setup.D.torus :=
      PA2b_mem_torus_of_perm_invariant hpair ρ b.1 b.2 (lk0xpa5_Ehom ρ e he hp b).toAdd
        (he ⟨b.1, b.2⟩) hbB.2
    have hzpow : (rootDiagUnit ρ.tau b.1) ^ p = 1 := by
      have hbpow : b.1 ^ p = 1 := by
        funext i
        exact b.2 i
      rw [rootDiagUnit_pow, hbpow, rootDiagUnit_one]
    have hker : ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b.1 γ = 1 :=
      PA2a_vanishes_on_kernelRoots ρ b.1 (lk0xpa5_Ehom ρ e he hp b).toAdd
        (he ⟨b.1, b.2⟩) (fun i _ => hbB.1 i (by
          simp only [posNodes, Finset.mem_filter, Finset.mem_univ, true_and]
          omega))
    exact ⟨htorus, hzpow, b.1, rfl, hker⟩
  · change Nat.card ((lk0xpa5_Bsub ρ e he hp).map (lk0xpa5_f ρ)) = p ^ ρ.row.D.rZ
    rw [Subgroup.card_map_of_injective (lk0xpa5_f_injective ρ),
      Nat.card_congr (lk0xpa5_BsubEquivW ρ e he hp)]
    exact hcardW'

end CFSG.StandardType.GGK0ExcCentreU

end

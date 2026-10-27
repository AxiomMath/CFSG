module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Rows
public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Prop329.G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13.VolI Matrix
open CFSG.Quasithin.Explicit

@[expose] def ixM (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix Ix3 Ix3 (ZMod 2) :=
  M.submatrix finSumFinEquiv finSumFinEquiv

@[expose] def t1 : Matrix Ix3 Ix3 (ZMod 2) :=
  ixM !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def t2 : Matrix Ix3 Ix3 (ZMod 2) :=
  ixM !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0;
    1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def t3 : Matrix Ix3 Ix3 (ZMod 2) :=
  ixM !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0;
    1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def wordQ : List (Fin 2) → Matrix Ix3 Ix3 (ZMod 2)
  | [] => 1
  | i :: w => ![matA6, matB6] i * wordQ w

@[expose] def prodT (x : Bool × Bool × Bool) : Matrix Ix3 Ix3 (ZMod 2) :=
  (if x.1 then t1 else 1) * (if x.2.1 then t2 else 1) * (if x.2.2 then t3 else 1)

@[expose] def fixVec (c : Fin 3 → ZMod 2) : Ix3 → ZMod 2 :=
  Sum.elim ![0, 0, c 0] ![c 1, c 2, 0]

theorem prodT_mul : ∀ x y : Bool × Bool × Bool,
    prodT x * prodT y = prodT (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2 y.2.2) := by
  decide +kernel

theorem prodT_injective : Function.Injective prodT := by
  intro x y h
  revert x y
  decide +kernel

theorem prodT_mul_self (x : Bool × Bool × Bool) : prodT x * prodT x = 1 := by
  rw [prodT_mul]
  simp only [Bool.xor_self]
  decide +kernel

theorem t1_mul_self : t1 * t1 = 1 := by decide +kernel

theorem t2_mul_self : t2 * t2 = 1 := by decide +kernel

theorem t3_mul_self : t3 * t3 = 1 := by decide +kernel

theorem conj_t1 : t1 * matA6 * t1 = wordQ [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0] ∧
    t1 * matB6 * t1 = wordQ [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1] := by
  decide +kernel

theorem conj_t2 : t2 * matA6 * t2 = wordQ [1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1] ∧
    t2 * matB6 * t2 = wordQ [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1] := by
  decide +kernel

theorem conj_t3 : t3 * matA6 * t3 = wordQ [1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] ∧
    t3 * matB6 * t3 = wordQ [1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1] := by
  decide +kernel

theorem prodT_fixVec : ∀ (x : Bool × Bool × Bool) (c : Fin 3 → ZMod 2),
    prodT x *ᵥ fixVec c = fixVec c := by
  decide +kernel

theorem fixVec_injective : Function.Injective fixVec := by
  intro c c' h
  revert c c'
  decide +kernel

@[expose] def linAut (M : Matrix Ix3 Ix3 (ZMod 2)) (hM : M * M = 1) :
    MulAut (Multiplicative (Ix3 → ZMod 2)) where
  toFun w := Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd w)
  invFun w := Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd w)
  left_inv w := by simp [mulVec_mulVec, hM]
  right_inv w := by simp [mulVec_mulVec, hM]
  map_mul' x y := by simp [mulVec_add]

section Transport

variable {V : Type*} [CommGroup V] (e : V ≃* Multiplicative (Ix3 → ZMod 2))

@[expose] def trAut (M : Matrix Ix3 Ix3 (ZMod 2)) (hM : M * M = 1) : MulAut V :=
  e.trans ((linAut M hM).trans e.symm)

theorem toAdd_trAut (M : Matrix Ix3 Ix3 (ZMod 2)) (hM : M * M = 1) (v : V) :
    Multiplicative.toAdd (e (trAut e M hM v)) = M *ᵥ Multiplicative.toAdd (e v) := by
  simp [trAut, linAut]

theorem trAut_mul {M N : Matrix Ix3 Ix3 (ZMod 2)} (hM : M * M = 1) (hN : N * N = 1)
    (hMN : M * N * (M * N) = 1) : trAut e M hM * trAut e N hN = trAut e (M * N) hMN := by
  ext v
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [MulAut.mul_apply, toAdd_trAut, toAdd_trAut, toAdd_trAut, mulVec_mulVec]

theorem trAut_one : trAut e (1 : Matrix Ix3 Ix3 (ZMod 2)) (mul_one 1) = 1 := by
  ext v
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_trAut, one_mulVec, MulAut.one_apply]

theorem trAut_mul_self {M : Matrix Ix3 Ix3 (ZMod 2)} (hM : M * M = 1) :
    trAut e M hM * trAut e M hM = 1 := by
  rw [trAut_mul e hM hM (by rw [hM, mul_one]), ← trAut_one e]
  congr 1

theorem trAut_injective {M N : Matrix Ix3 Ix3 (ZMod 2)} (hM : M * M = 1) (hN : N * N = 1)
    (h : trAut e M hM = trAut e N hN) : M = N := by
  rw [ext_iff_mulVec]
  intro w
  have h1 := congrArg (fun φ : MulAut V => Multiplicative.toAdd (e (φ (e.symm
    (Multiplicative.ofAdd w))))) h
  simp only [toAdd_trAut, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
  exact h1

theorem trAut_eq {M N : Matrix Ix3 Ix3 (ZMod 2)} (hM : M * M = 1) (hN : N * N = 1) (h : M = N) :
    trAut e M hM = trAut e N hN := by
  subst h
  rfl

end Transport

theorem muQ_wordEval
    (w : List (Fin 2)) : muQ (wordEval gensK w) = wordQ w := by
  induction w with
  | nil => exact muQ_one
  | cons i w ih =>
    have hgen : ∀ j : Fin 2, muQ (gensK j) = ![matA6, matB6] j := by
      intro j
      match j with
      | 0 => exact muQ_gensK0
      | 1 => exact muQ_gensK1
    rw [show wordEval gensK (i :: w) = gensK i * wordEval gensK w from rfl, muQ_mul, ih, hgen]
    rfl

theorem trAut_mem_normalizer
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (e : V ≃* Multiplicative (Ix3 → ZMod 2)) (ψ : ↥subG2 →* ↥L) (hψ : Function.Bijective ψ)
    (hact : ∀ (g : ↥subG2) (w : V), Multiplicative.toAdd (e (((ψ g : ↥L) : MulAut V) w)) =
      muQ g *ᵥ Multiplicative.toAdd (e w))
    {t : Matrix Ix3 Ix3 (ZMod 2)} (ht : t * t = 1) {wa wb : List (Fin 2)}
    (ha : t * matA6 * t = wordQ wa) (hb : t * matB6 * t = wordQ wb) :
    trAut e t ht ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
  set φ := trAut e t ht with hφ
  have hφφ : φ * φ = 1 := trAut_mul_self e ht
  have hφinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφφ
  let c : ↥subG2 →* MulAut V :=
    { toFun := fun k => φ * ((ψ k : ↥L) : MulAut V) * φ
      map_one' := by simp [hφφ]
      map_mul' := fun k k' => by
        simp only [map_mul, Subgroup.coe_mul]
        calc φ * (((ψ k : ↥L) : MulAut V) * ((ψ k' : ↥L) : MulAut V)) * φ =
              φ * ((ψ k : ↥L) : MulAut V) * (φ * φ) * ((ψ k' : ↥L) : MulAut V) * φ := by
                rw [hφφ]; group
          _ = φ * ((ψ k : ↥L) : MulAut V) * φ * (φ * ((ψ k' : ↥L) : MulAut V) * φ) := by
                group }
  have hcw : ∀ (M : Matrix Ix3 Ix3 (ZMod 2)) (k : ↥subG2), muQ k = M →
      ∀ w : List (Fin 2), t * M * t = wordQ w → c k = ((ψ (wordEval gensK w) : ↥L) : MulAut V) := by
    intro M k hk w hw
    ext v
    apply e.injective
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (e (φ (((ψ k : ↥L) : MulAut V) (φ v)))) = _
    rw [hφ, toAdd_trAut, hact, toAdd_trAut, hact, muQ_wordEval, hk, mulVec_mulVec,
      mulVec_mulVec, ← hw, mul_assoc]
  have hc : ∀ k, c k ∈ L := by
    set S : Set ↥subG2 := (((↑) : ↥subG2 →
        (quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))) ⁻¹'
        ({((g2a : ↥(cayleyGroup (ZMod 2))) :
            quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)),
          ((g2b : ↥(cayleyGroup (ZMod 2))) :
            quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))} : Set _)) with hS
    have htop : Subgroup.closure S = ⊤ := Subgroup.closure_closure_coe_preimage
    have hle : Subgroup.closure S ≤ L.comap c := by
      rw [Subgroup.closure_le]
      rintro s (hs | hs)
      · have e0 : s = gensK 0 := Subtype.ext hs
        rw [SetLike.mem_coe, Subgroup.mem_comap, e0, hcw matA6 (gensK 0) muQ_gensK0 wa ha]
        exact (ψ _).2
      · have e1 : s = gensK 1 := Subtype.ext hs
        rw [SetLike.mem_coe, Subgroup.mem_comap, e1, hcw matB6 (gensK 1) muQ_gensK1 wb hb]
        exact (ψ _).2
    rw [htop] at hle
    exact fun k => hle (Subgroup.mem_top k)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hψ.2 ⟨x, hx⟩
    have hx' : x = ((ψ k : ↥L) : MulAut V) := (congrArg Subtype.val hk).symm
    rw [hx', hφinv]
    exact hc k
  · intro hx
    obtain ⟨k, hk⟩ := hψ.2 ⟨_, hx⟩
    have hx' : φ * x * φ⁻¹ = ((ψ k : ↥L) : MulAut V) := (congrArg Subtype.val hk).symm
    have : x = φ * ((ψ k : ↥L) : MulAut V) * φ := by
      rw [← hx', hφinv]
      calc x = (φ * φ) * x * (φ * φ) := by rw [hφφ, one_mul, mul_one]
        _ = φ * (φ * x * φ) * φ := by group
    rw [this]
    exact hc k

theorem isFFModule_normalizer
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : G2NaturalDerived L ⊤ ⊥ 1) : IsFFModule (Subgroup.normalizer (L : Set (MulAut V))) := by
  classical
  obtain ⟨e, ψ, hψ, hact⟩ := H13.A6.GR.G2.g2_frame_data h
  have : Finite V := Finite.of_equiv _ e.symm.toEquiv
  have hN1 := trAut_mem_normalizer e ψ hψ hact t1_mul_self conj_t1.1 conj_t1.2
  have hN2 := trAut_mem_normalizer e ψ hψ hact t2_mul_self conj_t2.1 conj_t2.2
  have hN3 := trAut_mem_normalizer e ψ hψ hact t3_mul_self conj_t3.1 conj_t3.2
  set φP : Bool × Bool × Bool → MulAut V := fun x => trAut e (prodT x) (prodT_mul_self x)
    with hφP
  have hφPmul : ∀ x y, φP x * φP y = φP (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2 y.2.2) := by
    intro x y
    rw [hφP]
    simp only
    rw [trAut_mul e (prodT_mul_self x) (prodT_mul_self y) (by rw [prodT_mul, prodT_mul_self])]
    exact trAut_eq e _ _ (prodT_mul x y)
  have hφPone : φP (false, false, false) = 1 := by
    rw [hφP]
    simp only
    rw [← trAut_one e]
    exact trAut_eq e _ _ (by simp [prodT])
  have hφP1 : φP (true, false, false) = trAut e t1 t1_mul_self := by
    rw [hφP]
    exact trAut_eq e _ _ (by simp [prodT])
  have hφP2 : φP (false, true, false) = trAut e t2 t2_mul_self := by
    rw [hφP]
    exact trAut_eq e _ _ (by simp [prodT])
  have hφP3 : φP (false, false, true) = trAut e t3 t3_mul_self := by
    rw [hφP]
    exact trAut_eq e _ _ (by simp [prodT])
  have hφPinj : Function.Injective φP := fun x y hxy =>
    prodT_injective (trAut_injective e (prodT_mul_self x) (prodT_mul_self y) hxy)
  have hφPN : ∀ x, φP x ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
    have hgen : ∀ x ∈ ({(false, false, false), (true, false, false), (false, true, false),
        (false, false, true)} : Set (Bool × Bool × Bool)),
        φP x ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
      rintro x (rfl | rfl | rfl | rfl)
      · rw [hφPone]
        exact Subgroup.one_mem _
      · rw [hφP1]
        exact hN1
      · rw [hφP2]
        exact hN2
      · rw [hφP3]
        exact hN3
    rintro ⟨a, b, c⟩
    have hsplit : φP (a, b, c) = φP (a, false, false) * φP (false, b, false) *
        φP (false, false, c) := by
      rw [hφPmul, hφPmul]
      simp
    rw [hsplit]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · cases a <;> exact hgen _ (by simp)
    · cases b <;> exact hgen _ (by simp)
    · cases c <;> exact hgen _ (by simp)
  have hφPsq : ∀ x, φP x * φP x = 1 := fun x => by
    rw [hφPmul]
    simpa using hφPone
  let A : Subgroup (MulAut V) :=
    { carrier := Set.range φP
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨_, (hφPmul x y).symm⟩
      one_mem' := ⟨_, hφPone⟩
      inv_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, (inv_eq_of_mul_eq_one_right (hφPsq x)).symm⟩ }
  have hcardA : Nat.card A = 8 := by
    have h1 : Nat.card A = Nat.card (Set.range φP) := rfl
    rw [h1, Nat.card_range_of_injective hφPinj]
    simp
  have hfixA : ∀ c : Fin 3 → ZMod 2, e.symm (Multiplicative.ofAdd (fixVec c)) ∈ fixV A := by
    intro c a ha
    obtain ⟨x, rfl⟩ := ha
    apply e.injective
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (e (trAut e (prodT x) (prodT_mul_self x) _)) = _
    rw [toAdd_trAut, MulEquiv.apply_symm_apply, toAdd_ofAdd, prodT_fixVec]
  have hcardFix : 8 ≤ Nat.card (fixV A) := by
    let f : (Fin 3 → ZMod 2) → fixV A := fun c => ⟨_, hfixA c⟩
    have hf : Function.Injective f := by
      intro c c' hcc
      have h1 := congrArg (fun v : fixV A => Multiplicative.toAdd (e (v : V))) hcc
      simp only [f, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
      exact fixVec_injective h1
    have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by simp
    rw [← h8]
    exact Nat.card_le_card_of_injective f hf
  have hcardV : Nat.card V = 64 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  refine ⟨A, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hφPN x
  · intro hA
    have h1 : φP (true, false, false) ∈ A := ⟨_, rfl⟩
    rw [hA, Subgroup.mem_bot, ← hφPone] at h1
    exact absurd (hφPinj h1) (by decide)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hφPmul, hφPmul]
    simp [Bool.xor_comm]
  · rintro _ ⟨x, rfl⟩
    rw [sq]
    exact hφPsq x
  · rw [hcardV, hcardA]
    calc 64 = 8 * 8 := by norm_num
      _ ≤ 8 * Nat.card (fixV A) := Nat.mul_le_mul_left _ hcardFix

end CFSG.Quasithin.H13.Prop329.G2

namespace CFSG.Quasithin.H13

theorem row329G2_holds :
    Row329G2 := fun _ _ _ _ h =>
  Prop329.G2.isFFModule_normalizer h

end CFSG.Quasithin.H13

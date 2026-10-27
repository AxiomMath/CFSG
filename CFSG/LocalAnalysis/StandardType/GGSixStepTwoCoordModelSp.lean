module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralClassical
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame

public section

open Matrix

namespace CFSG.StandardType

namespace CoordSp

open Multiplicative CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic

@[expose] def signs (p : ℕ) : Subgroup (ZMod p)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  mul_mem' := by
    rintro u v (rfl | rfl) (rfl | rfl) <;> simp
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro u (rfl | rfl) <;> simp

theorem mem_signs {p : ℕ} {u : (ZMod p)ˣ} : u ∈ signs p ↔ u = 1 ∨ u = -1 :=
  Iff.rfl

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def spDiag (u : Fin n → Fˣ) : StatedSp n F :=
  ⟨TauCeti.diagGL (TableBSymp.pairedUnits u), TableBSymp.diagGL_pairedUnits_mem u⟩

theorem coe_spDiag (u : Fin n → Fˣ) :
    (spDiag u : GL (Fin n ⊕ Fin n) F) = TauCeti.diagGL (TableBSymp.pairedUnits u) :=
  rfl

theorem spDiag_mul (u v : Fin n → Fˣ) : spDiag (u * v) = spDiag u * spDiag v := by
  apply Subtype.ext
  change TauCeti.diagGL _ = TauCeti.diagGL _ * TauCeti.diagGL _
  rw [← map_mul]
  congr 1
  funext x
  rcases x with i | i <;> simp [TableBSymp.pairedUnits, mul_comm]

theorem spDiag_one : spDiag (1 : Fin n → Fˣ) = 1 := by
  apply Subtype.ext
  change TauCeti.diagGL _ = 1
  rw [← map_one TauCeti.diagGL]
  congr 1
  funext x
  rcases x with i | i <;> simp [TableBSymp.pairedUnits]

theorem spDiag_injective : Function.Injective (spDiag (F := F) (n := n)) := by
  intro u v h
  have h1 := TauCeti.diagGL_injective (congrArg Subtype.val h)
  funext i
  exact congrFun h1 (Sum.inl i)

theorem frameDiag_eq (A₀ : StatedSp n F) (u : Fin n → Fˣ) :
    RestSp.frameDiag A₀ u = A₀ * spDiag u * A₀⁻¹ := by
  rw [RestSp.frameDiag]
  congr 2
  exact Subtype.ext (RestSp.coe_equiv_diagonal u)

@[expose] def pairFlip (sw : Fin n → Bool) : Equiv.Perm (Fin n ⊕ Fin n) where
  toFun x := Sum.elim (fun i => if sw i then Sum.inr i else Sum.inl i)
    (fun i => if sw i then Sum.inl i else Sum.inr i) x
  invFun x := Sum.elim (fun i => if sw i then Sum.inr i else Sum.inl i)
    (fun i => if sw i then Sum.inl i else Sum.inr i) x
  left_inv x := by rcases x with i | i <;> cases h : sw i <;> simp [h]
  right_inv x := by rcases x with i | i <;> cases h : sw i <;> simp [h]

@[expose] def signedPerm (sw : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n ⊕ Fin n) :=
  (pairFlip sw).trans (Equiv.sumCongr π π)

theorem signedPerm_inl (sw : Fin n → Bool) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    signedPerm sw π (Sum.inl i) = if sw i then Sum.inr (π i) else Sum.inl (π i) := by
  cases h : sw i <;> simp [signedPerm, pairFlip, h]

theorem signedPerm_inr (sw : Fin n → Bool) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    signedPerm sw π (Sum.inr i) = if sw i then Sum.inl (π i) else Sum.inr (π i) := by
  cases h : sw i <;> simp [signedPerm, pairFlip, h]

set_option linter.unusedSimpArgs false in
theorem largeEvenSpForm_signedPerm [CharP F 2] (sw : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (x y : Fin n ⊕ Fin n) :
    LargeEvenSpForm F n (signedPerm sw π x) (signedPerm sw π y) = LargeEvenSpForm F n x y := by
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  rw [TableBSymp.largeEvenSpForm_apply, TableBSymp.largeEvenSpForm_apply]
  rcases x with a | a <;> rcases y with b | b <;> cases ha : sw a <;> cases hb : sw b <;>
    by_cases hab : a = b <;>
    first
      | (subst hab; simp_all [signedPerm_inl, signedPerm_inr])
      | simp [signedPerm_inl, signedPerm_inr, ha, hb, hneg, π.injective.eq_iff, hab]

@[expose] noncomputable def spPerm [CharP F 2] (sw : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    StatedSp n F :=
  ⟨TauCeti.permutationGL (signedPerm sw π),
    TableBSymp.permutationGL_mem_sp _ (largeEvenSpForm_signedPerm sw π)⟩

theorem spPerm_conj_spDiag [CharP F 2] (sw : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (u : Fin n → Fˣ) :
    (spPerm sw π)⁻¹ * spDiag u * spPerm sw π =
      spDiag (fun i => if sw i then (u (π i))⁻¹ else u (π i)) := by
  apply Subtype.ext
  change (TauCeti.permutationGL (signedPerm sw π))⁻¹ * TauCeti.diagGL (TableBSymp.pairedUnits u) *
      TauCeti.permutationGL (signedPerm sw π) = TauCeti.diagGL (TableBSymp.pairedUnits _)
  have h := TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (TauCeti.permutationGL (k := F) (signedPerm sw π)⁻¹) (signedPerm sw π)
    (by rw [TauCeti.permutationGL_coe, inv_inv]) (TableBSymp.pairedUnits u)
  rw [map_inv] at h
  rw [h, inv_mul_cancel_right]
  congr 1
  funext x
  rcases x with i | i <;> cases hi : sw i <;>
    simp [TableBSymp.pairedUnits, signedPerm_inl, signedPerm_inr, hi]

section FrameHom

variable {G : Type} [Group G] {p : ℕ} [NeZero p] (ψ : StatedSp n F →* G) (A₀ : StatedSp n F)
  {ζ : Fˣ} (hζ : ζ ^ p = 1)

@[expose] noncomputable def frameHom : Multiplicative (Fin n → ZMod p) →* G where
  toFun t := ψ (A₀ * spDiag (fun i => ζ ^ (toAdd t i).val) * A₀⁻¹)
  map_one' := by
    have h0 : (fun i => ζ ^ (toAdd (1 : Multiplicative (Fin n → ZMod p)) i).val) = 1 := by
      funext i
      simp
    rw [h0, spDiag_one, mul_one, mul_inv_cancel, map_one]
  map_mul' a b := by
    have h : (fun i => ζ ^ (toAdd (a * b) i).val) =
        (fun i => ζ ^ (toAdd a i).val) * fun i => ζ ^ (toAdd b i).val := by
      funext i
      simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply, CoordSL.pow_val_add hζ]
    rw [h, spDiag_mul, ← map_mul]
    congr 1
    group

theorem frameHom_apply (t : Fin n → ZMod p) :
    frameHom ψ A₀ hζ (ofAdd t) = ψ (A₀ * spDiag (fun i => ζ ^ (t i).val) * A₀⁻¹) :=
  rfl

theorem frameHom_injective (hψ : Function.Injective ψ) (hζo : orderOf ζ = p) :
    Function.Injective (frameHom ψ A₀ hζ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [← ofAdd_toAdd a, frameHom_apply] at ha
  have h1 : A₀ * spDiag (fun i => ζ ^ (toAdd a i).val) * A₀⁻¹ = 1 := hψ (ha.trans (map_one ψ).symm)
  have h2 : spDiag (fun i => ζ ^ (toAdd a i).val) = spDiag 1 := by
    rw [spDiag_one]
    calc spDiag (fun i => ζ ^ (toAdd a i).val)
        = A₀⁻¹ * (A₀ * spDiag (fun i => ζ ^ (toAdd a i).val) * A₀⁻¹) * A₀ := by group
      _ = 1 := by rw [h1]; group
  have h3 := spDiag_injective h2
  rw [← ofAdd_toAdd a]
  convert ofAdd_zero (α := Fin n → ZMod p)
  funext i
  have h4 : ζ ^ (toAdd a i).val = 1 := congrFun h3 i
  rw [← orderOf_dvd_iff_pow_eq_one, hζo] at h4
  rw [Pi.zero_apply, ← ZMod.natCast_zmod_val (toAdd a i), (ZMod.natCast_eq_zero_iff _ _).mpr h4]

theorem frameHom_pow_p (a : Multiplicative (Fin n → ZMod p)) : frameHom ψ A₀ hζ a ^ p = 1 := by
  have ha : a ^ p = 1 := by
    apply toAdd.injective
    funext i
    simp [toAdd_pow]
  rw [← map_pow, ha, map_one]

theorem range_frameHom (hψ : Function.Injective ψ) (hζo : orderOf ζ = p) {B Bs : Subgroup G}
    (hBs : GGBstar p B Bs)
    (hframe : ∀ b ∈ Bs, ∃ u : Fin n → Fˣ, b = ψ (A₀ * spDiag u * A₀⁻¹)) :
    (frameHom ψ A₀ hζ).range = Bs := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) (frameHom_pow_p ψ A₀ hζ a)
    obtain ⟨u, rfl⟩ := hframe b hb
    rw [← ofAdd_toAdd a, frameHom_apply, ← map_mul, ← map_mul]
    congr 1
    calc A₀ * spDiag u * A₀⁻¹ * (A₀ * spDiag (fun i => ζ ^ (toAdd a i).val) * A₀⁻¹)
        = A₀ * (spDiag u * spDiag (fun i => ζ ^ (toAdd a i).val)) * A₀⁻¹ := by group
      _ = A₀ * (spDiag (fun i => ζ ^ (toAdd a i).val) * spDiag u) * A₀⁻¹ := by
          rw [← spDiag_mul, ← spDiag_mul, mul_comm]
      _ = A₀ * spDiag (fun i => ζ ^ (toAdd a i).val) * A₀⁻¹ * (A₀ * spDiag u * A₀⁻¹) := by group
  · intro b hb
    obtain ⟨u, rfl⟩ := hframe b hb
    have hp : (ψ (A₀ * spDiag u * A₀⁻¹)) ^ p = 1 := hBs.2.1.2 _ hb
    have hup : ∀ i, u i ^ p = 1 := by
      have h1 : A₀ * spDiag (u ^ p) * A₀⁻¹ = 1 := by
        apply hψ
        rw [map_one, ← hp, ← map_pow]
        congr 1
        have hpow : ∀ k : ℕ, spDiag (u ^ k) = spDiag u ^ k := fun k => by
          induction k with
          | zero => rw [pow_zero, pow_zero, spDiag_one]
          | succ k ih => rw [pow_succ, spDiag_mul, ih, pow_succ]
        rw [hpow, conj_pow]
      have h2 : spDiag (u ^ p) = spDiag 1 := by
        rw [spDiag_one]
        calc spDiag (u ^ p) = A₀⁻¹ * (A₀ * spDiag (u ^ p) * A₀⁻¹) * A₀ := by group
          _ = 1 := by rw [h1]; group
      exact fun i => congrFun (spDiag_injective h2) i
    have hprim : IsPrimitiveRoot (ζ : F) p :=
      IsPrimitiveRoot.coe_units_iff.mpr (hζo ▸ IsPrimitiveRoot.orderOf ζ)
    have hk : ∀ i, ∃ k : ℕ, ζ ^ k = u i := fun i => by
      have hui : (u i : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hup i, Units.val_one]
      obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hui
      exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hk])⟩
    choose k hk using hk
    refine ⟨ofAdd fun i => (k i : ZMod p), ?_⟩
    have hu : (fun i => ζ ^ ((k i : ZMod p)).val) = u := by
      funext i
      rw [← hk i, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
    rw [frameHom_apply, hu]

end FrameHom

section Moves

variable {G : Type} [Group G] {p : ℕ} [NeZero p] [CharP F 2] (ψ : StatedSp n F →* G)
  (A₀ : StatedSp n F) {ζ : Fˣ} (hζ : ζ ^ p = 1)

omit [CharP F 2] in
theorem pow_val_neg (hζ' : ζ ^ p = 1) (a : ZMod p) : ζ ^ (-a).val = (ζ ^ a.val)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← CoordSL.pow_val_add hζ', neg_add_cancel, ZMod.val_zero, pow_zero]

theorem exists_move_mem {Bs : Subgroup G} (hBs : (frameHom ψ A₀ hζ).range = Bs)
    (π : Equiv.Perm (Fin n)) (η : Fin n → (ZMod p)ˣ) (hη : ∀ i, η i ∈ signs p) :
    ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ t : Fin n → ZMod p,
      w⁻¹ * frameHom ψ A₀ hζ (ofAdd t) * w =
        frameHom ψ A₀ hζ (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  set sw : Fin n → Bool := fun i => decide (η i ≠ 1) with hsw
  set P : StatedSp n F := spPerm sw π with hP
  have hM : ∀ t : Fin n → ZMod p,
      (ψ (A₀ * P * A₀⁻¹))⁻¹ * frameHom ψ A₀ hζ (ofAdd t) * ψ (A₀ * P * A₀⁻¹) =
        frameHom ψ A₀ hζ (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
    intro t
    have hu : (fun i => if sw i then (ζ ^ (t (π i)).val)⁻¹ else ζ ^ (t (π i)).val) =
        fun i => ζ ^ ((η i : ZMod p) * t (π i)).val := by
      funext i
      by_cases h1 : η i = 1
      · have hs : sw i = false := by simp [hsw, h1]
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        rw [h1, Units.val_one, one_mul]
      · have h2 : η i = -1 := (hη i).resolve_left h1
        have hs : sw i = true := by simp [hsw, h1]
        simp only [hs, ↓reduceIte]
        rw [h2, Units.val_neg, Units.val_one, neg_one_mul, pow_val_neg hζ]
    have hc := spPerm_conj_spDiag sw π (fun i => ζ ^ (t i).val)
    rw [frameHom_apply, frameHom_apply, ← hu]
    calc (ψ (A₀ * P * A₀⁻¹))⁻¹ * ψ (A₀ * spDiag (fun i => ζ ^ (t i).val) * A₀⁻¹) *
          ψ (A₀ * P * A₀⁻¹)
        = ψ (A₀ * (P⁻¹ * spDiag (fun i => ζ ^ (t i).val) * P) * A₀⁻¹) := by
          simp only [← map_inv, ← map_mul]
          congr 1
          group
      _ = _ := by rw [hP, hc]
  refine ⟨ψ (A₀ * P * A₀⁻¹), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
    hBs ▸ CoordSL.mem_normalizer_range_of_conj π η hM⟩, hM⟩

end Moves

end CoordSp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic CoordSp Multiplicative

section Inputs

@[expose] def GGSpCoordCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (A₀ : StatedSp n F) (ζ : Fˣ) (hζ : ζ ^ p = 1), orderOf ζ = p →
    ∀ (b : G) (L₁ : Subgroup G),
      b ∈ (frameHom ψ A₀ hζ).range → b ≠ 1 →
      IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
      Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (L₁ : Set G) :
        Subgroup G) ≤ p ^ 2 →
      ∀ β : Fin n → ZMod p, frameHom ψ A₀ hζ (ofAdd β) = b →
        (∃ j j' : Fin n, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
          ∀ t : Fin n → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ hζ (ofAdd t) ∈ L₁) ∨
        (∃ (k : Fin n) (c : ZMod p) (ε : Fin n → (ZMod p)ˣ), c ≠ 0 ∧
          (∀ i, ε i ∈ signs p) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
          ∀ t : Fin n → ZMod p, t k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * t i = 0 →
            frameHom ψ A₀ hζ (ofAdd t) ∈ L₁)

@[expose] def GGSpCoordContraryInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ →
      GGSixStepOne p B Bs x L D J → p ∣ 2 ^ f - 1 →
    ∀ (A₀ : StatedSp n (GaloisField 2 f)) (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1),
      orderOf ζ = p → (frameHom ψ A₀ hζ).range = Bs → (n : ZMod p) - 1 = 0 →
        ∃ (k : Fin n) (o : Fin n → (ZMod p)ˣ) (t : Fin n → ZMod p),
          (∀ i, o i ∈ signs p) ∧ t ≠ 0 ∧ t k = 0 ∧ ∑ i, (o i : ZMod p) * t i = 0 ∧
            frameHom ψ A₀ hζ (ofAdd t) ∈ D

@[expose] def GGSpCoordModelNonsplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ p ∣ 2 ^ f - 1 →
      ∃ (r : ℕ) (O : Subgroup (ZMod p)ˣ) (ι : Multiplicative (Fin r → ZMod p) →* G),
        StepTwoToral.GGStepTwoCoords p r O ι Bs (ggG0 p B x L D J) D
          (GGStepTwoPair p B Bs x L D J)

theorem ggStepTwoCoordModelOn_PSp_of_inputs (hcomp : GGSpCoordCompInput)
    (hcontr : GGSpCoordContraryInput) (hns : GGSpCoordModelNonsplitInput) :
    GGStepTwoCoordModelOn .PSp := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 _
  by_cases hsplit : p ∣ 2 ^ f - 1
  swap
  · exact hns G p B Bs x L D J n f ψ hctx s1 hsplit
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) hpF
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  obtain ⟨A₀, hA₀⟩ := ggSpBstarFrameInput_holds G p B Bs x L D J n f ψ hctx s1 hsplit
  have hframe : ∀ b ∈ Bs, ∃ u : Fin n → (GaloisField 2 f)ˣ, b = ψ (A₀ * spDiag u * A₀⁻¹) := by
    intro b hb
    obtain ⟨u, hu⟩ := hA₀ b hb
    exact ⟨u, by rw [hu, frameDiag_eq]⟩
  have hrange : (frameHom ψ A₀ hζ).range = Bs :=
    range_frameHom ψ A₀ hζ hinj hζo hctx.bstar hframe
  have hG₀ : ψ.range = ggG0 p B x L D J := hctx.range_eq
  refine ⟨n, signs p, frameHom ψ A₀ hζ,
    ⟨frameHom_injective ψ A₀ hζ hinj hζo, hrange, ?_, ?_, ?_⟩⟩
  ·
    intro π η hη _
    obtain ⟨w, hw, hws⟩ := exists_move_mem ψ A₀ hζ hrange π η hη
    refine ⟨w, ?_, hws⟩
    rw [← hG₀]
    exact hw
  ·
    exact hcontr G p B Bs x L D J n f ψ hctx s1 hsplit A₀ ζ hζ hζo hrange
  ·
    intro b L₁ hpair β hβ
    obtain ⟨hb, hb1, hcomp', hcard⟩ := hpair
    rw [← hG₀] at hcomp'
    rw [← hrange] at hb hcard
    exact hcomp G (GaloisField 2 f) n p hp2 hpF ψ hinj A₀ ζ hζ hζo b L₁ hb hb1 hcomp' hcard β hβ

end Inputs

end CFSG.StandardType

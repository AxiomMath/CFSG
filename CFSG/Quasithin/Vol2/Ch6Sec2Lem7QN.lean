module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C118NoOuterAlg
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5A

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique.Setup.Offender

variable {Q : Type} [CommGroup Q]

structure NatData627 (Ks : Subgroup (MulAut Q)) : Type 1 where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  card : Nat.card F = 4
  π : SpecialLinearGroup (Fin 2) F →* ↥Ks
  surj : Function.Surjective π
  ψ : Multiplicative (Fin 2 → F) →* Q
  inj : Function.Injective ψ
  range : ψ.range = commV Ks
  equiv : ∀ (γ : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
    ((π γ : ↥Ks) : MulAut Q) (ψ (Multiplicative.ofAdd v)) =
      ψ (Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) F).mulVec v))

attribute [instance] NatData627.instField NatData627.instFinite

theorem natData627_of {Ks : Subgroup (MulAut Q)} (h : BinaryNaturalSL Ks (commV Ks) ⊥ 2 2) :
    Nonempty (NatData627 Ks) := by
  classical
  obtain ⟨F, _, _, hF, π₀, hsurj, -, -, hU, -, -, -, β, hβs, hβk, hβe⟩ := h
  set e := specialLinearGroupEquivStatedSL 2 F with he
  set P := (⊤ : Subgroup (Multiplicative (Fin 2 → F))) with hP
  set q : ↥P →* ↥P ⧸ (⊥ : Subgroup (Multiplicative (Fin 2 → F))).subgroupOf P :=
    QuotientGroup.mk' _ with hq
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have h1 := (hβk u).mp hu
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  set eβ := MulEquiv.ofBijective β ⟨hβi, hβs⟩ with heβ
  set ι : Multiplicative (Fin 2 → F) →* ↥P :=
    MonoidHom.codRestrict (MonoidHom.id _) P fun _ => Subgroup.mem_top _ with hι
  set ψ : Multiplicative (Fin 2 → F) →* Q :=
    (commV Ks).subtype.comp ((eβ.symm.toMonoidHom.comp q).comp ι) with hψ
  have hqinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, hq, QuotientGroup.ker_mk']
    ext x
    simp
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 := Subtype.ext hab
    have h2 := eβ.symm.injective h1
    have h3 := hqinj h2
    exact congrArg Subtype.val h3
  have hψapp : ∀ v, ψ v = ((eβ.symm (q (ι v)) : ↥(commV Ks)) : Q) := fun v => rfl
  refine ⟨⟨F, by rw [hF]; norm_num, π₀.comp e.toMonoidHom, ?_, ψ, hψinj, ?_, ?_⟩⟩
  · intro x
    obtain ⟨γ, rfl⟩ := hsurj x
    refine ⟨e.symm γ, ?_⟩
    exact congrArg π₀ (e.apply_symm_apply γ)
  · ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (eβ.symm (q (ι v))).2
    · intro hx
      obtain ⟨m, hm⟩ : ∃ m : ↥P, q m = eβ ⟨x, hx⟩ := QuotientGroup.mk_surjective (eβ ⟨x, hx⟩)
      refine ⟨(m : Multiplicative (Fin 2 → F)), ?_⟩
      rw [hψapp, show ι (m : Multiplicative (Fin 2 → F)) = m from rfl, hm,
        MulEquiv.symm_apply_apply]
  · intro γ v
    set u := eβ.symm (q (ι (Multiplicative.ofAdd v))) with hu
    have hβu : β u = q (ι (Multiplicative.ofAdd v)) := eβ.apply_symm_apply _
    have hmem : ((π₀ (e γ) : ↥Ks) : MulAut Q) (u : Q) ∈ commV Ks := hU _ _ u.2
    have hm : (FFModel.nat (StatedSL 2 F)).act (e γ) (Multiplicative.ofAdd v) ∈
        (FFModel.nat (StatedSL 2 F)).sec := Subgroup.mem_top _
    have h1 := hβe (e γ) u (ι (Multiplicative.ofAdd v)) hmem hm hβu
    have h4 : eβ ⟨((π₀ (e γ) : ↥Ks) : MulAut Q) (u : Q), hmem⟩ =
        q (ι (Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) F).mulVec v))) := h1
    have h2 : (⟨((π₀ (e γ) : ↥Ks) : MulAut Q) (u : Q), hmem⟩ : ↥(commV Ks)) =
        eβ.symm (q (ι (Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) F).mulVec v)))) := by
      calc (⟨((π₀ (e γ) : ↥Ks) : MulAut Q) (u : Q), hmem⟩ : ↥(commV Ks)) =
          eβ.symm (eβ ⟨((π₀ (e γ) : ↥Ks) : MulAut Q) (u : Q), hmem⟩) :=
            (eβ.symm_apply_apply _).symm
        _ = _ := by rw [h4]
    have h3 := congrArg Subtype.val h2
    rw [hψapp, hψapp]
    exact h3

theorem mem_commV_of_mem_normalizer627 {Ks : Subgroup (MulAut Q)} {f : MulAut Q}
    (hf : f ∈ Subgroup.normalizer (Ks : Set (MulAut Q))) {w : Q} (hw : w ∈ commV Ks) :
    f w ∈ commV Ks :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hf hw

@[expose] def unitri627 (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := {γ | (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have hab : ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (a : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) :=
      congrArg Subtype.val rfl
    refine ⟨?_, ?_⟩
    · show ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      rw [hab, Matrix.mul_apply, Fin.sum_univ_two, ha1, hb1]
      ring
    · show ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      rw [hab, Matrix.mul_apply, Fin.sum_univ_two, ha2, hb2, hb1]
      ring
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hdet := a.2
    rw [Matrix.det_fin_two, ha1, ha2] at hdet
    have hinv : ((a⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val rfl
    refine ⟨?_, ?_⟩
    · show ((a⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      rw [hinv]
      simp [Matrix.adjugate_fin_two, ha1]
    · show ((a⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      rw [hinv]
      simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination hdet

theorem sl_mulVec_mulVec627 {F : Type} [Field F] (a b : SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) :
    (a : Matrix (Fin 2) (Fin 2) F).mulVec ((b : Matrix (Fin 2) (Fin 2) F).mulVec v) =
      ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v := by
  rw [Matrix.mulVec_mulVec]
  rfl

@[expose] def unitriElem627 {F : Type} [Field F] (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem unitriElem627_mem {F : Type} [Field F] (t : F) : unitriElem627 t ∈ unitri627 F := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem card_unitri627 (F : Type) [Field F] : Nat.card (unitri627 F) = Nat.card F := by
  refine (Nat.card_congr (show F ≃ ↥(unitri627 F) from
    { toFun := fun t => (⟨unitriElem627 t, unitriElem627_mem t⟩ : ↥(unitri627 F))
      invFun := fun γ => ((γ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1
      left_inv := fun t => rfl
      right_inv := fun γ => ?_ })).symm
  obtain ⟨h1, h2⟩ := γ.2
  have hdet := (γ : SpecialLinearGroup (Fin 2) F).2
  rw [Matrix.det_fin_two, h1, h2] at hdet
  apply Subtype.ext
  apply Subtype.ext
  show !![1, ((γ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1] =
    ((γ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j
  · exact h2.symm
  · rfl
  · exact h1.symm
  · show (1 : F) = ((γ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
    linear_combination -hdet

section Tri

variable {F : Type} [Field F]

theorem ringAut_mul_apply627 (σ τ : F ≃+* F) (c : F) : (σ * τ) c = σ (τ c) := rfl

theorem ringAut_apply_inv627 (σ : F ≃+* F) (c : F) : σ (σ⁻¹ c) = c := σ.apply_symm_apply c

theorem ringAut_inv_apply627 (σ : F ≃+* F) (c : F) : σ⁻¹ (σ c) = c := σ.symm_apply_apply c

theorem ringAut_one_apply627 (c : F) : (1 : F ≃+* F) c = c := rfl

theorem perm_apply_inv627 {α : Type*} (X : Equiv.Perm α) (v : α) : X (X⁻¹ v) = v :=
  X.apply_symm_apply v

@[expose] def Tri627 (X : Equiv.Perm (Fin 2 → F)) (σ : F ≃+* F) (a κ : F) : Prop :=
  (∀ v w, X (v + w) = X v + X w) ∧ IsSemilinearWith X σ ∧
    X (Pi.single 0 1) = a • Pi.single 0 1 ∧ ∀ v, X v 1 = σ (v 1) * κ

theorem Tri627.mul {X Y : Equiv.Perm (Fin 2 → F)} {σ τ : F ≃+* F} {a κ b μ : F}
    (hX : Tri627 X σ a κ) (hY : Tri627 Y τ b μ) :
    Tri627 (X * Y) (σ * τ) (σ b * a) (σ μ * κ) := by
  obtain ⟨hXa, hXs, hX0, hX1⟩ := hX
  obtain ⟨hYa, hYs, hY0, hY1⟩ := hY
  refine ⟨fun v w => by simp only [Equiv.Perm.mul_apply, hYa, hXa], hXs.mul hYs, ?_, fun v => ?_⟩
  · rw [Equiv.Perm.mul_apply, hY0, hXs, hX0, smul_smul]
  · rw [Equiv.Perm.mul_apply, hX1, hY1, map_mul, ringAut_mul_apply627]
    ring

theorem Tri627.inv {X : Equiv.Perm (Fin 2 → F)} {σ : F ≃+* F} {a κ : F}
    (hX : Tri627 X σ a κ) (ha : a ≠ 0) (hκ : κ ≠ 0) :
    Tri627 X⁻¹ σ⁻¹ (σ⁻¹ a⁻¹) (σ⁻¹ κ⁻¹) := by
  obtain ⟨hXa, hXs, hX0, hX1⟩ := hX
  refine ⟨perm_inv_add X hXa, fun c v => ?_, ?_, fun v => ?_⟩
  · apply X.injective
    rw [perm_apply_inv627, hXs, ringAut_apply_inv627, perm_apply_inv627]
  · apply X.injective
    rw [perm_apply_inv627, hXs, ringAut_apply_inv627, hX0, smul_smul,
      inv_mul_cancel₀ ha, one_smul]
  · have h1 := hX1 (X⁻¹ v)
    rw [perm_apply_inv627] at h1
    have h2 : σ ((X⁻¹ v) 1) = v 1 * κ⁻¹ := by
      rw [h1, mul_assoc, mul_inv_cancel₀ hκ, mul_one]
    have h3 := congrArg (fun x => (σ⁻¹ : F ≃+* F) x) h2
    simp only [ringAut_inv_apply627] at h3
    rw [h3, map_mul]

theorem Tri627.one : Tri627 (1 : Equiv.Perm (Fin 2 → F)) 1 1 1 := by
  refine ⟨fun v w => rfl, fun c v => rfl, by simp, fun v => by simp⟩

theorem Tri627.unique {X : Equiv.Perm (Fin 2 → F)} {σ σ' : F ≃+* F} {a κ a' κ' : F}
    (hX : Tri627 X σ a κ) (hX' : Tri627 X σ' a' κ') : a = a' ∧ κ = κ' := by
  refine ⟨?_, ?_⟩
  · have h := congrFun (hX.2.2.1.symm.trans hX'.2.2.1) 0
    simpa using h
  · have h := (hX.2.2.2 (Pi.single 1 1)).symm.trans (hX'.2.2.2 (Pi.single 1 1))
    simpa using h

theorem Tri627.pow {X : Equiv.Perm (Fin 2 → F)} {a κ : F} (hX : Tri627 X 1 a κ) (n : ℕ) :
    Tri627 (X ^ n) 1 (a ^ n) (κ ^ n) := by
  induction n with
  | zero => simpa using Tri627.one
  | succ n ih =>
    have h := ih.mul hX
    rw [mul_one, ringAut_one_apply627, ringAut_one_apply627, ← pow_succ', ← pow_succ',
      ← pow_succ] at h
    exact h

theorem Tri627.a_ne_zero {X : Equiv.Perm (Fin 2 → F)} {σ : F ≃+* F} {a κ : F}
    (hX : Tri627 X σ a κ) : a ≠ 0 := by
  intro h0
  have h1 := hX.2.2.1
  rw [h0, zero_smul, ← hX.2.1.map_zero] at h1
  have h2 := congrFun (X.injective h1) 0
  simp at h2

theorem Tri627.κ_ne_zero {X : Equiv.Perm (Fin 2 → F)} {σ : F ≃+* F} {a κ : F}
    (hX : Tri627 X σ a κ) : κ ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := X.surjective (Pi.single 1 1)
  have h1 := hX.2.2.2 v
  rw [hv, h0, mul_zero] at h1
  simp at h1

end Tri

theorem mem_normalizer_of_conj_mem627 {X : Type*} [Group X] {S : Subgroup X} [Finite S] {y : X}
    (h : ∀ x ∈ S, y * x * y⁻¹ ∈ S) : y ∈ Subgroup.normalizer (S : Set X) := by
  have hle : S.map (MulAut.conj y).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]))

theorem mem_normalizer_of_inner627 {X : Type*} [Group X] [Finite X] {G₀ K R : Subgroup X}
    (hKG : K ≤ G₀) (hRG : R ≤ G₀) (hR2 : IsPGroup 2 R)
    (hRmax : ∀ P : Subgroup X, IsPGroup 2 P → R ≤ P → P ≤ G₀ → P = R)
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1)
    (hinner : ∀ r ∈ R, ∃ k ∈ K, ∀ x ∈ K, r * x * r⁻¹ = k * x * k⁻¹) {y : X} (hyK : y ∈ K)
    (hyS : y ∈ Subgroup.normalizer ((R ⊓ K : Subgroup X) : Set X)) :
    y ∈ Subgroup.normalizer (R : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := G₀ ⊓ Subgroup.centralizer (K : Set X) with hC
  have hCK : ∀ c ∈ C, ∀ x ∈ K, Commute x c := fun c hc x hx =>
    Subgroup.mem_centralizer_iff.mp hc.2 x hx
  have hKC : ∀ z ∈ K, z ∈ C → z = 1 := fun z hz hzC =>
    hZ z hz fun x hx => (hCK z hzC x hx).symm
  have hdec : ∀ r ∈ R, ∃ k ∈ K, ∃ c ∈ C, r = k * c := by
    intro r hr
    obtain ⟨k, hk, hkr⟩ := hinner r hr
    refine ⟨k, hk, k⁻¹ * r, Subgroup.mem_inf.mpr ⟨G₀.mul_mem (G₀.inv_mem (hKG hk)) (hRG hr),
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩, by group⟩
    have := hkr x hx
    calc x * (k⁻¹ * r) = k⁻¹ * (k * x * k⁻¹) * r := by group
      _ = k⁻¹ * (r * x * r⁻¹) * r := by rw [this]
      _ = k⁻¹ * r * x := by group
  let A : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ∃ c ∈ C, k * c ∈ R}
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, c, hc, hac⟩ ⟨hb, d, hd, hbd⟩
        refine ⟨K.mul_mem ha hb, c * d, C.mul_mem hc hd, ?_⟩
        have e : a * b * (c * d) = (a * c) * (b * d) := by
          calc a * b * (c * d) = a * (b * c) * d := by group
            _ = a * (c * b) * d := by rw [(hCK c hc b hb).eq]
            _ = (a * c) * (b * d) := by group
        rw [e]
        exact R.mul_mem hac hbd
      inv_mem' := by
        rintro a ⟨ha, c, hc, hac⟩
        refine ⟨K.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
          rw [_root_.mul_inv_rev, ((hCK c hc a ha).inv_inv).eq]
        rw [e]
        exact R.inv_mem hac }
  let B : Subgroup X :=
    { carrier := {c | c ∈ C ∧ ∃ k ∈ K, k * c ∈ R}
      one_mem' := ⟨C.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro c d ⟨hc, a, ha, hac⟩ ⟨hd, b, hb, hbd⟩
        refine ⟨C.mul_mem hc hd, a * b, K.mul_mem ha hb, ?_⟩
        have e : a * b * (c * d) = (a * c) * (b * d) := by
          calc a * b * (c * d) = a * (b * c) * d := by group
            _ = a * (c * b) * d := by rw [(hCK c hc b hb).eq]
            _ = (a * c) * (b * d) := by group
        rw [e]
        exact R.mul_mem hac hbd
      inv_mem' := by
        rintro c ⟨hc, a, ha, hac⟩
        refine ⟨C.inv_mem hc, a⁻¹, K.inv_mem ha, ?_⟩
        have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
          rw [_root_.mul_inv_rev, ((hCK c hc a ha).inv_inv).eq]
        rw [e]
        exact R.inv_mem hac }
  have hpow : ∀ a ∈ K, ∀ c ∈ C, a * c ∈ R → ∃ m : ℕ, a ^ 2 ^ m = 1 ∧ c ^ 2 ^ m = 1 := by
    intro a ha c hc hac
    obtain ⟨m, hm⟩ := hR2 ⟨a * c, hac⟩
    have h1 : (a * c) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [(hCK c hc a ha).mul_pow] at h1
    have h2 : a ^ 2 ^ m = (c ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ 2 ^ m = 1 := hKC _ (K.pow_mem ha _) (h2 ▸ C.inv_mem (C.pow_mem hc _))
    refine ⟨m, h3, ?_⟩
    rw [h3, one_mul] at h1
    exact h1
  have hA2 : IsPGroup 2 A := by
    rintro ⟨a, ha, c, hc, hac⟩
    obtain ⟨m, hm, -⟩ := hpow a ha c hc hac
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  have hB2 : IsPGroup 2 B := by
    rintro ⟨c, hc, a, ha, hac⟩
    obtain ⟨m, -, hm⟩ := hpow a ha c hc hac
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  have hAB : A ≤ Subgroup.normalizer (B : Set X) := by
    intro a ha
    refine mem_normalizer_of_conj_mem627 fun x hx => ?_
    have e : a * x * a⁻¹ = x := by rw [(hCK x hx.1 a ha.1).eq, mul_inv_cancel_right]
    rw [e]
    exact hx
  have hAB2 : IsPGroup 2 (A ⊔ B : Subgroup X) := IsPGroup.to_sup_of_normal_right' hA2 hB2 hAB
  have hRAB : R ≤ A ⊔ B := by
    intro r hr
    obtain ⟨k, hk, c, hc, rfl⟩ := hdec r hr
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ⟨hk, c, hc, hr⟩)
      (Subgroup.mem_sup_right ⟨hc, k, hk, hr⟩)
  have hABG : A ⊔ B ≤ G₀ := sup_le (fun a ha => hKG ha.1) (fun c hc => hc.1.1)
  have hAR : A ≤ R := (hRmax _ hAB2 hRAB hABG) ▸ le_sup_left
  refine mem_normalizer_of_conj_mem627 fun r hr => ?_
  obtain ⟨k, hk, c, hc, rfl⟩ := hdec r hr
  have hkR : k ∈ R := hAR ⟨hk, c, hc, hr⟩
  have hcR : c ∈ R := by
    have := R.mul_mem (R.inv_mem hkR) hr
    simpa using this
  have hyk : y * k * y⁻¹ ∈ R ⊓ K := (Subgroup.mem_normalizer_iff.mp hyS k).mp ⟨hkR, hk⟩
  have e : y * (k * c) * y⁻¹ = (y * k * y⁻¹) * c := by
    have := (hCK c hc y hyK).eq
    calc y * (k * c) * y⁻¹ = (y * k * y⁻¹) * (y * c * y⁻¹) := by group
      _ = (y * k * y⁻¹) * c := by rw [this, mul_inv_cancel_right]
  rw [e]
  exact R.mul_mem hyk.1 hcR

namespace NatData627

variable {Ks : Subgroup (MulAut Q)} (D : NatData627 Ks)

theorem ψ_mem (v : Multiplicative (Fin 2 → D.F)) : D.ψ v ∈ commV Ks := D.range ▸ ⟨v, rfl⟩

theorem exists_ψ {x : Q} (hx : x ∈ commV Ks) :
    ∃ v : Fin 2 → D.F, D.ψ (Multiplicative.ofAdd v) = x := by
  rw [← D.range] at hx
  obtain ⟨v, rfl⟩ := hx
  exact ⟨Multiplicative.toAdd v, rfl⟩

theorem π_apply (γ : SpecialLinearGroup (Fin 2) D.F) (v : Fin 2 → D.F) :
    ((D.π γ : ↥Ks) : MulAut Q) (D.ψ (Multiplicative.ofAdd v)) =
      D.ψ (Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) D.F).mulVec v)) := D.equiv γ v

theorem ψ_inj {v w : Fin 2 → D.F}
    (h : D.ψ (Multiplicative.ofAdd v) = D.ψ (Multiplicative.ofAdd w)) :
    v = w :=
  congrArg Multiplicative.toAdd (D.inj h)

theorem eq_of_agree {x y : MulAut Q} (hx : x ∈ Ks) (hy : y ∈ Ks)
    (h : ∀ v, x (D.ψ (Multiplicative.ofAdd v)) = y (D.ψ (Multiplicative.ofAdd v))) : x = y := by
  obtain ⟨γ₁, hγ₁⟩ := D.surj ⟨x, hx⟩
  obtain ⟨γ₂, hγ₂⟩ := D.surj ⟨y, hy⟩
  have hx' : x = ((D.π γ₁ : ↥Ks) : MulAut Q) := by rw [hγ₁]
  have hy' : y = ((D.π γ₂ : ↥Ks) : MulAut Q) := by rw [hγ₂]
  have hm : ∀ v, (γ₁ : Matrix (Fin 2) (Fin 2) D.F).mulVec v =
      (γ₂ : Matrix (Fin 2) (Fin 2) D.F).mulVec v := by
    intro v
    have h1 := h v
    rw [hx', hy', D.π_apply, D.π_apply] at h1
    exact D.ψ_inj h1
  have hγ : γ₁ = γ₂ := by
    ext i j
    have := congrFun (hm (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  rw [hx', hy', hγ]

@[expose] noncomputable def hatFun (f : MulAut Q)
    (hf : f ∈ Subgroup.normalizer (Ks : Set (MulAut Q))) (v : Fin 2 → D.F) : Fin 2 → D.F :=
  Classical.choose
    (D.exists_ψ (mem_commV_of_mem_normalizer627 hf (D.ψ_mem (Multiplicative.ofAdd v))))

theorem hatFun_spec (f : MulAut Q) (hf : f ∈ Subgroup.normalizer (Ks : Set (MulAut Q)))
    (v : Fin 2 → D.F) :
    D.ψ (Multiplicative.ofAdd (D.hatFun f hf v)) = f (D.ψ (Multiplicative.ofAdd v)) :=
  Classical.choose_spec
    (D.exists_ψ (mem_commV_of_mem_normalizer627 hf (D.ψ_mem (Multiplicative.ofAdd v))))

theorem hatFun_eq_iff (f : MulAut Q) (hf : f ∈ Subgroup.normalizer (Ks : Set (MulAut Q)))
    (v w : Fin 2 → D.F) :
    D.hatFun f hf v = w ↔ D.ψ (Multiplicative.ofAdd w) = f (D.ψ (Multiplicative.ofAdd v)) := by
  constructor
  · rintro rfl
    exact D.hatFun_spec f hf v
  · intro h
    exact D.ψ_inj ((D.hatFun_spec f hf v).trans h.symm)

@[expose] noncomputable def hat : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))) →*
    Equiv.Perm (Fin 2 → D.F) where
  toFun f :=
    { toFun := D.hatFun f f.2
      invFun := D.hatFun (f⁻¹ : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))) (f⁻¹).2
      left_inv := fun v => (D.hatFun_eq_iff _ _ _ _).mpr (by rw [hatFun_spec]; simp)
      right_inv := fun v => (D.hatFun_eq_iff _ _ _ _).mpr (by rw [hatFun_spec]; simp) }
  map_one' := Equiv.ext fun v =>
    (D.hatFun_eq_iff _ (1 : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))).2 _ _).mpr (by simp)
  map_mul' f g := Equiv.ext fun v => (D.hatFun_eq_iff _ (f * g).2 _ _).mpr (by
    show D.ψ (Multiplicative.ofAdd (D.hatFun f f.2 (D.hatFun g g.2 v))) = _
    rw [hatFun_spec, hatFun_spec]
    simp)

theorem hat_spec (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))) (v : Fin 2 → D.F) :
    D.ψ (Multiplicative.ofAdd (D.hat f v)) = (f : MulAut Q) (D.ψ (Multiplicative.ofAdd v)) :=
  D.hatFun_spec f f.2 v

theorem hat_eq_iff (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))) (v w : Fin 2 → D.F) :
    D.hat f v = w ↔ D.ψ (Multiplicative.ofAdd w) = (f : MulAut Q) (D.ψ (Multiplicative.ofAdd v)) :=
  D.hatFun_eq_iff f f.2 v w

theorem hat_add (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))) (v w : Fin 2 → D.F) :
    D.hat f (v + w) = D.hat f v + D.hat f w := by
  rw [hat_eq_iff, ofAdd_add, map_mul, ofAdd_add, map_mul, map_mul, hat_spec, hat_spec]

theorem hat_normalizes (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (γ : SpecialLinearGroup (Fin 2) D.F) : ∃ γ' : SpecialLinearGroup (Fin 2) D.F,
      ∀ v, D.hat f ((γ : Matrix (Fin 2) (Fin 2) D.F).mulVec v) =
        (γ' : Matrix (Fin 2) (Fin 2) D.F).mulVec (D.hat f v) := by
  have hmem : (f : MulAut Q) * ((D.π γ : ↥Ks) : MulAut Q) * (f : MulAut Q)⁻¹ ∈ Ks :=
    (Subgroup.mem_normalizer_iff.mp f.2 _).mp (D.π γ).2
  obtain ⟨γ', hγ'⟩ := D.surj ⟨_, hmem⟩
  refine ⟨γ', fun v => ?_⟩
  rw [hat_eq_iff, ← D.π_apply, hγ', hat_spec, ← D.π_apply]
  simp

theorem exists_semilinear (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q)))) :
    ∃ σ : D.F ≃+* D.F, IsSemilinearWith (D.hat f) σ := by
  refine exists_semilinear_of_normalizes (D.hat f) (D.hat_add f) (D.hat_normalizes f) ?_
  intro γ
  obtain ⟨γ', hγ'⟩ := D.hat_normalizes f⁻¹ γ
  refine ⟨γ', fun v => ?_⟩
  rw [← map_inv]
  exact hγ' v

theorem exists_inner_of_linear (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (hlin : ∀ (c : D.F) (v : Fin 2 → D.F), D.hat f (c • v) = c • D.hat f v) :
    ∃ k ∈ Ks, ∀ x ∈ Ks, (f : MulAut Q) * x * (f : MulAut Q)⁻¹ = k * x * k⁻¹ := by
  classical
  set M := semilinMatrix (D.hat f) with hM
  have hσ : IsSemilinearWith (D.hat f) (RingEquiv.refl D.F) := fun c v => hlin c v
  have hMv : ∀ v, D.hat f v = M.mulVec v := by
    intro v
    rw [semilinMatrix_mulVec (D.hat_add f) hσ]
    rfl
  have hdet := semilinMatrix_det_ne_zero (D.hat_add f) hσ
  set lam := M.det ^ 2 with hlam
  have hlam2 : lam ^ 2 = M.det := sq_sq_ch625 D.card M.det
  have hlam0 : lam ≠ 0 := pow_ne_zero 2 hdet
  have hdet0 : (lam⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hlam2, inv_mul_cancel₀ hdet]
  set γ₀ : SpecialLinearGroup (Fin 2) D.F := mkSL (lam⁻¹ • M) hdet0 with hγ₀
  have hMγ : M = lam • (γ₀ : Matrix (Fin 2) (Fin 2) D.F) := by
    rw [hγ₀, mkSL_coe, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
  set k : MulAut Q := ((D.π γ₀ : ↥Ks) : MulAut Q) with hk
  refine ⟨k, (D.π γ₀).2, fun x hx => ?_⟩
  have hfx : (f : MulAut Q) * x * (f : MulAut Q)⁻¹ ∈ Ks :=
    (Subgroup.mem_normalizer_iff.mp f.2 x).mp hx
  have hkx : k * x * k⁻¹ ∈ Ks :=
    Ks.mul_mem (Ks.mul_mem (D.π γ₀).2 hx) (Ks.inv_mem (D.π γ₀).2)
  obtain ⟨γ, hγ⟩ := D.surj ⟨x, hx⟩
  have hxγ : x = ((D.π γ : ↥Ks) : MulAut Q) := by rw [hγ]
  apply D.eq_of_agree hfx hkx
  intro v
  obtain ⟨w, rfl⟩ := (D.hat f).surjective v
  have hkinv : k⁻¹ = ((D.π γ₀⁻¹ : ↥Ks) : MulAut Q) := by rw [hk, map_inv]; rfl
  have e1 : (f : MulAut Q)⁻¹ (D.ψ (Multiplicative.ofAdd (D.hat f w))) =
      D.ψ (Multiplicative.ofAdd w) := by
    rw [D.hat_spec, MulAut.inv_apply_self]
  have key : ((γ₀⁻¹ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F).mulVec
      (M.mulVec w) = lam • w := by
    rw [hMγ, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have h := congrArg Subtype.val (inv_mul_cancel γ₀)
    rw [show ((γ₀⁻¹ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F) *
      (γ₀ : Matrix (Fin 2) (Fin 2) D.F) = 1 from h, Matrix.one_mulVec]
  rw [MulAut.mul_apply, MulAut.mul_apply, e1, hxγ, D.π_apply, ← D.hat_spec, MulAut.mul_apply,
    MulAut.mul_apply, hkinv, hk, hMv, hMv, D.π_apply, D.π_apply, D.π_apply, key,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hMγ, Matrix.smul_mulVec]

theorem π_injective : Function.Injective D.π := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  rw [Subgroup.mem_bot]
  ext i j
  have h1 := D.π_apply γ (Pi.single j 1)
  rw [hγ] at h1
  have h2 := congrFun (D.ψ_inj h1.symm) i
  have h3 : (γ : Matrix (Fin 2) (Fin 2) D.F) i j = (Pi.single j (1 : D.F) : Fin 2 → D.F) i := by
    simpa [Matrix.mulVec_single_one] using h2
  rw [h3, Pi.single_apply]
  simp [Matrix.one_apply]

include D in
theorem card_Ks : Nat.card Ks = 60 := by
  rw [← Nat.card_congr (Equiv.ofBijective D.π ⟨D.π_injective, D.surj⟩),
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, D.card]
  norm_num

include D in
theorem exists_sylow_coords {S : Subgroup (MulAut Q)} (hSK : S ≤ Ks) (hS4 : Nat.card S = 4) :
    ∃ D' : NatData627 Ks, ∀ γ : SpecialLinearGroup (Fin 2) D'.F,
      ((D'.π γ : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D'.F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (S.subgroupOf Ks).comap D.π with hP
  have hP4 : Nat.card P = 4 := by
    rw [← hS4, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective D.π ⟨D.π_injective, D.surj⟩)
      fun γ => Iff.rfl)
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) D.F) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, D.card]
    norm_num
  have hidx : ∀ H : Subgroup (SpecialLinearGroup (Fin 2) D.F), Nat.card H = 4 → H.index = 15 := by
    intro H hH
    have := H.card_mul_index
    rw [hH, hSL] at this
    omega
  have hU4 : Nat.card (unitri627 D.F) = 4 := by rw [card_unitri627, D.card]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  set SP : Sylow 2 (SpecialLinearGroup (Fin 2) D.F) :=
    (IsPGroup.of_card (hP4.trans h4)).toSylow (by rw [hidx P hP4]; decide) with hSP
  set SU : Sylow 2 (SpecialLinearGroup (Fin 2) D.F) :=
    (IsPGroup.of_card (hU4.trans h4)).toSylow (by rw [hidx _ hU4]; decide) with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) D.F) SU SP
  have hPU : ∀ γ, γ ∈ P ↔ g⁻¹ * γ * g ∈ unitri627 D.F := by
    intro γ
    have e : γ ∈ P ↔ γ ∈ ((g • SU : Sylow 2 _) : Subgroup (SpecialLinearGroup (Fin 2) D.F)) := by
      rw [hg]
      rfl
    rw [e, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : g⁻¹ * (MulAut.conj g • y) * g = y := by
        simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
      rw [this]
      exact hy
    · intro h
      refine ⟨g⁻¹ * γ * g, h, ?_⟩
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  set c : SpecialLinearGroup (Fin 2) D.F →* SpecialLinearGroup (Fin 2) D.F :=
    (MulAut.conj g).toMonoidHom with hc
  set mg : Multiplicative (Fin 2 → D.F) →* Multiplicative (Fin 2 → D.F) :=
    (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) D.F)).toAddMonoidHom.toMultiplicative with hmg
  have hmg_app : ∀ v : Fin 2 → D.F, mg (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) D.F).mulVec v) := fun v => rfl
  set gi : Matrix (Fin 2) (Fin 2) D.F :=
    ((g⁻¹ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F) with hgi
  have hginv : ∀ v : Fin 2 → D.F, (g : Matrix (Fin 2) (Fin 2) D.F).mulVec (gi.mulVec v) = v := by
    intro v
    rw [hgi, sl_mulVec_mulVec627, mul_inv_cancel]
    exact Matrix.one_mulVec v
  refine ⟨⟨D.F, D.card, D.π.comp c, ?_, D.ψ.comp mg, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨γ, hγ⟩ := D.surj x
    exact ⟨g⁻¹ * γ * g, by simp [hc, MulAut.conj_apply, mul_assoc, hγ]⟩
  · intro a b hab
    have h1 := D.inj hab
    have h2 : (g⁻¹ : SpecialLinearGroup (Fin 2) D.F) • (g • Multiplicative.toAdd a) =
        (g⁻¹ : SpecialLinearGroup (Fin 2) D.F) • (g • Multiplicative.toAdd b) := by
      rw [show g • Multiplicative.toAdd a = g • Multiplicative.toAdd b from
        congrArg Multiplicative.toAdd h1]
    rw [inv_smul_smul, inv_smul_smul] at h2
    exact h2
  · ext x
    rw [← D.range]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨mg v, rfl⟩
    · rintro ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd (gi.mulVec (Multiplicative.toAdd v)), ?_⟩
      show D.ψ (mg _) = _
      rw [hmg_app, hginv]
      rfl
  · intro γ v
    show ((D.π (c γ) : ↥Ks) : MulAut Q) (D.ψ (mg (Multiplicative.ofAdd v))) =
      D.ψ (mg (Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) D.F).mulVec v)))
    rw [hmg_app, hmg_app, D.π_apply, sl_mulVec_mulVec627, sl_mulVec_mulVec627]
    congr 3
    simp [hc, MulAut.conj_apply, mul_assoc]
  · intro γ
    show ((D.π (c γ) : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D.F
    have e1 : ((D.π (c γ) : ↥Ks) : MulAut Q) ∈ S ↔ c γ ∈ P := Iff.rfl
    rw [e1, hPU]
    simp [hc, MulAut.conj_apply, mul_assoc]

theorem exists_fpf627 {S : Subgroup (MulAut Q)} (hSK : S ≤ Ks) [Finite S]
    (hS : ∀ γ : SpecialLinearGroup (Fin 2) D.F,
      ((D.π γ : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D.F) :
    ∃ y ∈ Ks, y ∈ Subgroup.normalizer (S : Set (MulAut Q)) ∧ y ^ 3 = 1 ∧
      ∀ v : Fin 2 → D.F, y (D.ψ (Multiplicative.ofAdd v)) = D.ψ (Multiplicative.ofAdd v) →
        v = 0 := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 D.card
  have hω3 : ω ^ 3 = 1 := pow_three_ch625 D.card hω0
  obtain ⟨t₀, ht₀⟩ : ∃ t : SpecialLinearGroup (Fin 2) D.F,
      (t : Matrix (Fin 2) (Fin 2) D.F) = !![ω, 0; 0, ω⁻¹] :=
    ⟨⟨!![ω, 0; 0, ω⁻¹], by simp [Matrix.det_fin_two, hω0]⟩, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ t : SpecialLinearGroup (Fin 2) D.F,
      (t : Matrix (Fin 2) (Fin 2) D.F) = !![ω⁻¹, 0; 0, ω] :=
    ⟨⟨!![ω⁻¹, 0; 0, ω], by simp [Matrix.det_fin_two, hω0]⟩, rfl⟩
  have ht01 : t₀ * t₁ = 1 := by
    apply Subtype.ext
    show (t₀ : Matrix (Fin 2) (Fin 2) D.F) * (t₁ : Matrix (Fin 2) (Fin 2) D.F) = 1
    rw [ht₀, ht₁, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hω0]
  have ht0inv : t₀⁻¹ = t₁ := (eq_inv_of_mul_eq_one_right ht01).symm
  refine ⟨D.π t₀, (D.π t₀).2, ?_, ?_, ?_⟩
  · refine mem_normalizer_of_conj_mem627 fun x hx => ?_
    obtain ⟨γ, hγ⟩ := D.surj ⟨x, hSK hx⟩
    have hγU : γ ∈ unitri627 D.F := (hS γ).mp (by rw [hγ]; exact hx)
    have e : ((D.π t₀ : ↥Ks) : MulAut Q) * x * ((D.π t₀ : ↥Ks) : MulAut Q)⁻¹ =
        ((D.π (t₀ * γ * t₁) : ↥Ks) : MulAut Q) := by
      rw [← ht0inv, map_mul, map_mul, map_inv, hγ]
      rfl
    rw [e, hS]
    obtain ⟨h1, h2⟩ := hγU
    have hm : ((t₀ * γ * t₁ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F) =
        (t₀ : Matrix (Fin 2) (Fin 2) D.F) * (γ : Matrix (Fin 2) (Fin 2) D.F) *
          (t₁ : Matrix (Fin 2) (Fin 2) D.F) := rfl
    refine ⟨?_, ?_⟩
    · show ((t₀ * γ * t₁ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F) 1 0 = 0
      rw [hm, ht₀, ht₁, Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) D.F), Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      simp [h1]
    · show ((t₀ * γ * t₁ : SpecialLinearGroup (Fin 2) D.F) : Matrix (Fin 2) (Fin 2) D.F) 0 0 = 1
      rw [hm, ht₀, ht₁, Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) D.F), Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      simp [h1, h2, hω0]
  · have h3 : t₀ ^ 3 = 1 := by
      apply Subtype.ext
      show (t₀ : Matrix (Fin 2) (Fin 2) D.F) ^ 3 = 1
      rw [ht₀, pow_three, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j
      · simp
        linear_combination hω3
      · simp
      · simp
      · simp
        rw [show ω⁻¹ * (ω⁻¹ * ω⁻¹) = (ω ^ 3)⁻¹ by ring, hω3, inv_one]
    rw [← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
  · intro v hv
    rw [D.π_apply] at hv
    have h1 := D.ψ_inj hv
    rw [ht₀] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    ext i
    fin_cases i
    · show v 0 = 0
      by_contra h
      exact hω1 (mul_right_cancel₀ h (by rw [one_mul]; exact e0))
    · show v 1 = 0
      by_contra h
      have : ω⁻¹ = 1 := mul_right_cancel₀ h (by rw [one_mul]; exact e1)
      exact hω1 (inv_eq_one.mp this)

theorem hat_e0_snd627 {S : Subgroup (MulAut Q)} (hSK : S ≤ Ks)
    (hS : ∀ γ : SpecialLinearGroup (Fin 2) D.F,
      ((D.π γ : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D.F)
    (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (hfS : (f : MulAut Q) ∈ Subgroup.normalizer (S : Set (MulAut Q))) :
    D.hat f (Pi.single 0 1) 1 = 0 := by
  set u := unitriElem627 (1 : D.F) with hudef
  have hu : ((D.π u : ↥Ks) : MulAut Q) ∈ S := (hS u).mpr (unitriElem627_mem 1)
  have hx : (f : MulAut Q)⁻¹ * ((D.π u : ↥Ks) : MulAut Q) * (f : MulAut Q) ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hfS) _).mp hu
    simpa using this
  obtain ⟨γ', hγ'⟩ := D.surj ⟨_, hSK hx⟩
  have hγ'U : γ' ∈ unitri627 D.F := (hS γ').mp (by rw [hγ']; exact hx)
  have he0 : (γ' : Matrix (Fin 2) (Fin 2) D.F).mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    obtain ⟨h1, h2⟩ := hγ'U
    ext i
    fin_cases i
    · simpa [Matrix.mulVec_single_one] using h2
    · simpa [Matrix.mulVec_single_one] using h1
  have e : ((D.π u : ↥Ks) : MulAut Q) * (f : MulAut Q) =
      (f : MulAut Q) * ((D.π γ' : ↥Ks) : MulAut Q) := by
    rw [hγ']
    show _ = (f : MulAut Q) * ((f : MulAut Q)⁻¹ * ((D.π u : ↥Ks) : MulAut Q) * (f : MulAut Q))
    group
  have key : (u : Matrix (Fin 2) (Fin 2) D.F).mulVec (D.hat f (Pi.single 0 1)) =
      D.hat f (Pi.single 0 1) := by
    apply D.ψ_inj
    rw [← D.π_apply, D.hat_spec]
    calc ((D.π u : ↥Ks) : MulAut Q) ((f : MulAut Q) (D.ψ (Multiplicative.ofAdd (Pi.single 0 1))))
        = (((D.π u : ↥Ks) : MulAut Q) * (f : MulAut Q))
            (D.ψ (Multiplicative.ofAdd (Pi.single 0 1))) := rfl
      _ = ((f : MulAut Q) * ((D.π γ' : ↥Ks) : MulAut Q))
            (D.ψ (Multiplicative.ofAdd (Pi.single 0 1))) := by rw [e]
      _ = (f : MulAut Q) (D.ψ (Multiplicative.ofAdd (Pi.single 0 1))) := by
        rw [MulAut.mul_apply, D.π_apply, he0]
  have h0 := congrFun key 0
  have hm : (u : Matrix (Fin 2) (Fin 2) D.F) = !![1, 1; 0, 1] := rfl
  rw [hm] at h0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  exact h0

theorem tri_hat627 {S : Subgroup (MulAut Q)} (hSK : S ≤ Ks)
    (hS : ∀ γ : SpecialLinearGroup (Fin 2) D.F,
      ((D.π γ : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D.F)
    (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (hfS : (f : MulAut Q) ∈ Subgroup.normalizer (S : Set (MulAut Q))) {σ : D.F ≃+* D.F}
    (hσ : IsSemilinearWith (D.hat f) σ) :
    Tri627 (D.hat f) σ (D.hat f (Pi.single 0 1) 0) (D.hat f (Pi.single 1 1) 1) := by
  have h1 := D.hat_e0_snd627 hSK hS f hfS
  refine ⟨D.hat_add f, hσ, ?_, fun v => ?_⟩
  · ext i
    fin_cases i
    · simp
    · simpa using h1
  · have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → D.F) + v 1 • (Pi.single 1 1 : Fin 2 → D.F) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv, D.hat_add, hσ, hσ]
    simp [h1]

theorem eq_one_of_pow_three_of_pow_two_pow627 {M : Type*} [Monoid M] {a : M} (h3 : a ^ 3 = 1)
    {n : ℕ} (h2 : a ^ 2 ^ n = 1) : a = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem hat_eq_one_of_outer627 {S : Subgroup (MulAut Q)} (hSK : S ≤ Ks)
    (hS : ∀ γ : SpecialLinearGroup (Fin 2) D.F,
      ((D.π γ : ↥Ks) : MulAut Q) ∈ S ↔ γ ∈ unitri627 D.F)
    (d r : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (hdS : (d : MulAut Q) ∈ Subgroup.normalizer (S : Set (MulAut Q)))
    (hrS : (r : MulAut Q) ∈ Subgroup.normalizer (S : Set (MulAut Q)))
    (hd3 : d ^ 3 = 1)
    (hr : ¬ ∃ k ∈ Ks, ∀ x ∈ Ks, (r : MulAut Q) * x * (r : MulAut Q)⁻¹ = k * x * k⁻¹)
    (hc : ∃ n : ℕ, (r * d * r⁻¹ * d⁻¹) ^ 2 ^ n = 1) : D.hat d = 1 := by
  classical
  have hK := D.card
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 hK
  obtain ⟨σd, hσd⟩ := D.exists_semilinear d
  obtain ⟨σr, hσr⟩ := D.exists_semilinear r
  set X := D.hat d with hX
  set Y := D.hat r with hY
  have hX3 : X ^ 3 = 1 := by rw [hX, ← map_pow, hd3, map_one]
  have hσd1 : σd = 1 := by
    rcases ringAut_ch625 hK σd with h | h
    · exact RingEquiv.ext h
    · exfalso
      have h3 : IsSemilinearWith (X * (X * X)) (σd * (σd * σd)) := hσd.mul (hσd.mul hσd)
      have hXX : X * (X * X) = 1 := by rw [← pow_three]; exact hX3
      have h4 := congrFun (h3 ω (Pi.single 0 1)) 0
      rw [hXX] at h4
      simp only [Equiv.Perm.coe_one, id_eq, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one, ringAut_mul_apply627, h] at h4
      rw [sq_sq_ch625 hK] at h4
      apply hω1
      have h5 : ω * (ω - 1) = 0 := by linear_combination -h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 hω0
      · exact sub_eq_zero.mp h6
  have hσr2 : ∀ c, σr c = c ^ 2 := by
    rcases ringAut_ch625 hK σr with h | h
    · exfalso
      exact hr (D.exists_inner_of_linear r fun c v => by rw [hσr, h])
    · exact h
  have hσrinv : ∀ c, σr⁻¹ c = c ^ 2 := by
    intro c
    have h1 : σr (c ^ 2) = c := by rw [hσr2, sq_sq_ch625 hK]
    rw [← h1, ringAut_inv_apply627, h1]
  rw [hσd1] at hσd
  have hTX := D.tri_hat627 hSK hS d hdS hσd
  have hTY := D.tri_hat627 hSK hS r hrS hσr
  rw [← hX] at hTX
  rw [← hY] at hTY
  set a := X (Pi.single 0 1) 0 with ha
  set κ := X (Pi.single 1 1) 1 with hκ
  set p := Y (Pi.single 0 1) 0 with hp
  set s := Y (Pi.single 1 1) 1 with hs
  have ha0 := hTX.a_ne_zero
  have hκ0 := hTX.κ_ne_zero
  have hp0 := hTY.a_ne_zero
  have hs0 := hTY.κ_ne_zero
  obtain ⟨n, hn⟩ := hc
  have hTc := ((hTY.mul hTX).mul (hTY.inv hp0 hs0)).mul (hTX.inv ha0 hκ0)
  have hτ : σr * 1 * σr⁻¹ * (1 : D.F ≃+* D.F)⁻¹ = 1 := by
    rw [mul_one, inv_one, mul_one, mul_inv_cancel]
  rw [hτ] at hTc
  have hα : (σr * 1 * σr⁻¹) ((1 : D.F ≃+* D.F)⁻¹ a⁻¹) *
      ((σr * 1) (σr⁻¹ p⁻¹) * (σr a * p)) = a := by
    simp only [ringAut_mul_apply627, ringAut_one_apply627, ringAut_apply_inv627, inv_one]
    rw [hσr2 a]
    field_simp
  have hκ' : (σr * 1 * σr⁻¹) ((1 : D.F ≃+* D.F)⁻¹ κ⁻¹) *
      ((σr * 1) (σr⁻¹ s⁻¹) * (σr κ * s)) = κ := by
    simp only [ringAut_mul_apply627, ringAut_one_apply627, ringAut_apply_inv627, inv_one]
    rw [hσr2 κ]
    field_simp
  rw [hα, hκ'] at hTc
  have hc1 : (Y * X * Y⁻¹ * X⁻¹) ^ 2 ^ n = 1 := by
    rw [hX, hY, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hn, map_one]
  have hTcn := hTc.pow (2 ^ n)
  rw [hc1] at hTcn
  obtain ⟨han, hκn⟩ := hTcn.unique Tri627.one
  have ha1 : a = 1 := eq_one_of_pow_three_of_pow_two_pow627 (pow_three_ch625 hK ha0) han
  have hκ1 : κ = 1 := eq_one_of_pow_three_of_pow_two_pow627 (pow_three_ch625 hK hκ0) hκn
  obtain ⟨hXa, hXs, hX0, hX1⟩ := hTX
  rw [ha1, one_smul] at hX0
  set b := X (Pi.single 1 1) 0 with hb
  have hXe1 : X (Pi.single 1 1) = b • Pi.single 0 1 + Pi.single 1 1 := by
    ext i
    fin_cases i
    · simp [hb]
    · have := hX1 (Pi.single 1 1)
      simp only [Pi.single_eq_same, ringAut_one_apply627, one_mul, hκ1] at this
      simp [this]
  have hXX1 : X (X (Pi.single 1 1)) = Pi.single 1 1 := by
    rw [hXe1, hXa, hXs, ringAut_one_apply627, hX0, hXe1, ← add_assoc, ← add_smul,
      add_self_ch625 hK, zero_smul, zero_add]
  have hX2 : X * X = 1 := by
    refine Equiv.ext fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → D.F) + v 1 • (Pi.single 1 1 : Fin 2 → D.F) := by
      ext i
      fin_cases i <;> simp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq]
    conv_lhs => rw [hv, hXa, hXs, hXs, ringAut_one_apply627, ringAut_one_apply627, hXa, hXs,
      hXs, ringAut_one_apply627, ringAut_one_apply627, hX0, hX0, hXX1]
    exact hv.symm
  calc X = X * X * X := by rw [hX2, one_mul]
    _ = X ^ 3 := by rw [pow_three, mul_assoc]
    _ = 1 := hX3

include D in
theorem eq_one_of_central627 {k : MulAut Q} (hk : k ∈ Ks) (hc : ∀ x ∈ Ks, k * x = x * k) :
    k = 1 := by
  obtain ⟨γ, hγ⟩ := D.surj ⟨k, hk⟩
  have hγc : γ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) D.F) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply D.π_injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hγ]
    exact (hc _ (D.π x).2).symm
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hγc
  obtain ⟨r, hr2, hr⟩ := hγc
  rw [Fintype.card_fin] at hr2
  have hr1 : r = 1 := by
    have h2 := two_eq_zero_ch625 D.card
    have h3 : (r + 1) * (r + 1) = 0 := by linear_combination hr2 + (r + 1) * h2
    have h4 := mul_self_eq_zero.mp h3
    linear_combination h4 - h2
  have hγ1 : γ = 1 := by
    apply Subtype.ext
    rw [← hr, hr1]
    simp
  have h5 := congrArg Subtype.val hγ
  rw [hγ1, map_one] at h5
  exact h5.symm

theorem fix_of_hat_eq_one (f : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))))
    (hf : D.hat f = 1) :
    (∀ v, (f : MulAut Q) (D.ψ (Multiplicative.ofAdd v)) = D.ψ (Multiplicative.ofAdd v)) ∧
      ∀ x ∈ Ks, (f : MulAut Q) * x = x * (f : MulAut Q) := by
  have hfix : ∀ v, (f : MulAut Q) (D.ψ (Multiplicative.ofAdd v)) =
      D.ψ (Multiplicative.ofAdd v) := by
    intro v
    rw [← D.hat_spec, hf, Equiv.Perm.coe_one, id_eq]
  refine ⟨hfix, fun x hx => ?_⟩
  have hfx : (f : MulAut Q) * x * (f : MulAut Q)⁻¹ ∈ Ks :=
    (Subgroup.mem_normalizer_iff.mp f.2 x).mp hx
  have h1 : (f : MulAut Q) * x * (f : MulAut Q)⁻¹ = x := by
    apply D.eq_of_agree hfx hx
    intro v
    have hinv : (f : MulAut Q)⁻¹ (D.ψ (Multiplicative.ofAdd v)) = D.ψ (Multiplicative.ofAdd v) := by
      conv_lhs => rw [← hfix v]
      exact MulAut.inv_apply_self Q _ _
    obtain ⟨γ, hγ⟩ := D.surj ⟨x, hx⟩
    have hxγ : x = ((D.π γ : ↥Ks) : MulAut Q) := by rw [hγ]
    rw [MulAut.mul_apply, MulAut.mul_apply, hinv, hxγ, D.π_apply, hfix]
  calc (f : MulAut Q) * x = (f : MulAut Q) * x * (f : MulAut Q)⁻¹ * (f : MulAut Q) := by group
    _ = x * (f : MulAut Q) := by rw [h1]

theorem mem_fixV_of_fix627 (hsum : IsIntDirect (commV Ks) (fixV Ks) ⊤) {y : MulAut Q}
    (hy : y ∈ Ks)
    (hfpf : ∀ v, y (D.ψ (Multiplicative.ofAdd v)) = D.ψ (Multiplicative.ofAdd v) → v = 0)
    {q : Q} (hq : y q = q) : q ∈ fixV Ks := by
  have hq' : q ∈ commV Ks ⊔ fixV Ks := by rw [hsum.1]; exact Subgroup.mem_top q
  obtain ⟨n, hn, f, hf, rfl⟩ := Subgroup.mem_sup.mp hq'
  have hyf : y f = f := hf y hy
  rw [map_mul, hyf] at hq
  have hyn : y n = n := mul_right_cancel hq
  obtain ⟨v, rfl⟩ := D.exists_ψ hn
  have hv := hfpf v hyn
  rw [hv, ofAdd_zero, map_one, one_mul]
  exact hf

end NatData627

end CFSG.Quasithin.H13

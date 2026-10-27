module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Transv

public section

namespace CFSG.Quasithin.Kleidman.F204.Sec

open Subgroup

section Basic

variable {A : Type*} [CommGroup A]

@[expose] def kap (σ : MulAut A) : A →* A :=
  MonoidHom.mk' (fun a => σ a * a⁻¹) (fun a b => by
    simp only [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹]; exact mul_mul_mul_comm (σ a) (σ b) a⁻¹ b⁻¹)

@[simp] theorem kap_apply (σ : MulAut A) (a : A) : kap σ a = σ a * a⁻¹ := rfl

@[expose] def I (σ : MulAut A) (Y X : Subgroup A) : Subgroup A := Y ⊓ X.comap (kap σ)

theorem mem_I {σ : MulAut A} {Y X : Subgroup A} {a : A} : a ∈ I σ Y X ↔ a ∈ Y ∧ σ a * a⁻¹ ∈ X :=
  Iff.rfl

@[expose] noncomputable def idx (σ : MulAut A) (Y X : Subgroup A) : ℕ := (I σ Y X).relIndex Y

variable [Finite A]

theorem relIndex_ne_zero' (H K : Subgroup A) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite

theorem idx_ne_zero (σ : MulAut A) (Y X : Subgroup A) : idx σ Y X ≠ 0 :=
  relIndex_ne_zero' _ _

theorem idx_mono_left (σ : MulAut A) {Y Y' : Subgroup A} (h : Y' ≤ Y) (X : Subgroup A) :
    idx σ Y' X ≤ idx σ Y X := by
  have h1 : I σ Y' X = I σ Y X ⊓ Y' := by
    ext a; simp only [mem_I, Subgroup.mem_inf]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h h1, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  unfold idx
  rw [h1, inf_relIndex_right]
  exact Subgroup.relIndex_le_of_le_right h (relIndex_ne_zero' _ _)

theorem idx_anti_right (σ : MulAut A) (Y : Subgroup A) {X X' : Subgroup A} (h : X ≤ X') :
    idx σ Y X' ≤ idx σ Y X := by
  have : I σ Y X ≤ I σ Y X' := fun a ha => ⟨ha.1, h ha.2⟩
  exact Subgroup.relIndex_le_of_le_left this (relIndex_ne_zero' _ _)

theorem idx_super (σ : MulAut A) {W Y X : Subgroup A} (hYW : Y ≤ W) (hXY : X ≤ Y)
    (hY : ∀ y ∈ Y, σ y ∈ Y) : idx σ W Y * idx σ Y X ≤ idx σ W X := by
  have hle1 : I σ W X ≤ I σ W Y := fun a ha => ⟨ha.1, hXY ha.2⟩
  have hYle : Y ≤ I σ W Y := fun y hy => ⟨hYW hy, Y.mul_mem (hY y hy) (Y.inv_mem hy)⟩
  have h1 : I σ Y X = I σ W X ⊓ Y := by
    ext a; simp only [mem_I, Subgroup.mem_inf]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨hYW h1, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have h2 : idx σ Y X ≤ (I σ W X).relIndex (I σ W Y) := by
    unfold idx
    rw [h1, inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right hYle (relIndex_ne_zero' _ _)
  have h3 := Subgroup.relIndex_mul_relIndex (I σ W X) (I σ W Y) W hle1 (show I σ W Y ≤ W from inf_le_left)
  unfold idx
  calc (I σ W Y).relIndex W * idx σ Y X ≤ (I σ W Y).relIndex W * (I σ W X).relIndex (I σ W Y) :=
        Nat.mul_le_mul_left _ h2
    _ = (I σ W X).relIndex (I σ W Y) * (I σ W Y).relIndex W := Nat.mul_comm _ _
    _ = (I σ W X).relIndex W := h3

end Basic

section Action

variable {A : Type*} [CommGroup A] {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut A)

@[expose] def GInv (Y : Subgroup A) : Prop := ∀ (g : Γ) (y : A), y ∈ Y → ρ g y ∈ Y

variable {ρ}

theorem GInv.map_eq {Y : Subgroup A} (hY : GInv ρ Y) (g : Γ) :
    Y.map ((ρ g : MulAut A) : A →* A) = Y := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact hY g y hy
  · intro y hy
    refine ⟨ρ g⁻¹ y, hY g⁻¹ y hy, ?_⟩
    show ρ g (ρ g⁻¹ y) = y
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[expose] noncomputable def quotAct (N : Subgroup A) (hN : GInv ρ N) : Γ →* MulAut (A ⧸ N) where
  toFun g := QuotientGroup.congr N N (ρ g) (hN.map_eq g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a => rw [QuotientGroup.congr_mk]; simp
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a =>
      simp only [MulAut.mul_apply, QuotientGroup.congr_mk, map_mul]

theorem quotAct_mk {N : Subgroup A} (hN : GInv ρ N) (g : Γ) (a : A) :
    quotAct N hN g (a : A ⧸ N) = ((ρ g a : A) : A ⧸ N) := by
  show QuotientGroup.congr N N (ρ g) (hN.map_eq g) (a : A ⧸ N) = _
  rw [QuotientGroup.congr_mk]

@[expose] noncomputable def subAct (Y : Subgroup A) (hY : GInv ρ Y) : Γ →* MulAut ↥Y where
  toFun g :=
    { toFun := fun y => ⟨ρ g y, hY g y y.2⟩
      invFun := fun y => ⟨ρ g⁻¹ y, hY g⁻¹ y y.2⟩
      left_inv := fun y => Subtype.ext (by
        show ρ g⁻¹ (ρ g (y : A)) = y
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
      right_inv := fun y => Subtype.ext (by
        show ρ g (ρ g⁻¹ (y : A)) = y
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
      map_mul' := fun a b => Subtype.ext (by
        show ρ g ((a : A) * b) = ρ g a * ρ g b
        exact map_mul _ _ _) }
  map_one' := by ext y; show ρ 1 (y : A) = _; simp
  map_mul' g h := by ext y; show ρ (g * h) (y : A) = ρ g (ρ h (y : A)); simp

theorem subAct_coe {Y : Subgroup A} (hY : GInv ρ Y) (g : Γ) (y : Y) :
    ((subAct Y hY g y : Y) : A) = ρ g y := rfl

end Action

section Coprime

variable {A : Type*} [CommGroup A] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut A}

theorem coprime_fix (h2 : ∀ a : A, a * a = 1) {g : Γ} (hg : Odd (orderOf g)) {c m : A}
    (hc : ρ g c = c) (hm : ρ g m = c * m) : ρ g m = m := by
  have hpow : ∀ k : ℕ, ρ (g ^ k) m = c ^ k * m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, hc, hm]
      simp [pow_succ, mul_assoc]
  have h1 := hpow (orderOf g)
  rw [pow_orderOf_eq_one, map_one] at h1
  have hcc : c ^ 2 = 1 := by rw [sq]; exact h2 c
  obtain ⟨j, hj⟩ := hg
  have hcn : c ^ orderOf g = c := by
    rw [hj, pow_succ, pow_mul, hcc, one_pow, one_mul]
  rw [hcn] at h1
  have : c = 1 := by
    have h3 : c * m = m := by simpa using h1.symm
    simpa using h3
  rw [hm, this, one_mul]

theorem coprime_sub (h2 : ∀ a : A, a * a = 1) {g : Γ} (hg : Odd (orderOf g)) {X Y : Subgroup A}
    (hX : ∀ x ∈ X, ρ g x = x) (hY : ∀ y ∈ Y, ρ g y * y⁻¹ ∈ X) : ∀ y ∈ Y, ρ g y = y := by
  intro y hy
  have hc := hX _ (hY y hy)
  refine coprime_fix h2 hg (c := ρ g y * y⁻¹) hc ?_
  simp

end Coprime

section TV

variable {A : Type*} [CommGroup A] [Finite A] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut A}

theorem eq_pow_of_dvd_pow_two (h2 : ∀ a : A, a * a = 1) (Y : Subgroup A) {n : ℕ}
    (hn : n ∣ Nat.card Y) (hn0 : n ≠ 0) (h3 : n < 4) : n ≤ 2 := by
  have hp : IsPGroup 2 Y := fun g => ⟨1, by
    rw [pow_one, sq]; exact Subtype.ext (h2 g)⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  rw [hm] at hn
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  by_contra hlt
  have : 2 ≤ i := by
    by_contra h; push_neg at h
    interval_cases i <;> simp at hi <;> omega
  have : 4 ≤ 2 ^ i := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem four_le_idx_section (h2 : ∀ a : A, a * a = 1) (φ : Γ →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ) {Y X : Subgroup A} (hXY : X ≤ Y)
    (hY : GInv ρ Y) (hX : GInv ρ X)
    (hQ : ∀ q ∈ φ.ker, ∀ y ∈ Y, ρ q y * y⁻¹ ∈ X)
    (hnt : ∃ (g : Γ) (y : A), y ∈ Y ∧ ρ g y * y⁻¹ ∉ X)
    {z : Γ} (hz1 : φ z ≠ 1) (hz2 : φ z ^ 2 = 1) : 4 ≤ idx (ρ z) Y X := by
  by_contra hlt
  push_neg at hlt
  have hidx2 : idx (ρ z) Y X ≤ 2 := by
    refine eq_pow_of_dvd_pow_two h2 Y ?_ (idx_ne_zero _ _ _) hlt
    exact Subgroup.relIndex_dvd_card _ _
  let X' : Subgroup ↥Y := X.subgroupOf Y
  have hX' : GInv (subAct Y hY) X' := by
    intro g y hy
    show ((subAct Y hY g y : Y) : A) ∈ X
    rw [subAct_coe]; exact hX g y hy
  let ρh : Γ →* MulAut (↥Y ⧸ X') := quotAct X' hX'
  have hV2 : ∀ v : ↥Y ⧸ X', v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_mul]; exact (congrArg _ (Subtype.ext (h2 a))).trans (QuotientGroup.mk_one _)
  have hmem : ∀ (g : Γ) (y : Y), ρh g (y : ↥Y ⧸ X') = (y : ↥Y ⧸ X') ↔ ρ g y * y⁻¹ ∈ X := by
    intro g y
    rw [quotAct_mk, QuotientGroup.eq]
    show ((((subAct Y hY g y)⁻¹ * y : ↥Y)) : A) ∈ X ↔ _
    have e : (ρ g y)⁻¹ * (y : A) = (ρ g y * (y : A)⁻¹)⁻¹ := by simp [mul_comm]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, subAct_coe, e, inv_mem_iff]
    exact Iff.rfl
  have hle : φ.ker ≤ ρh.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    ext v
    induction v using QuotientGroup.induction_on with
    | H y => exact (hmem q y).mpr (hQ q hq y y.2)
  let ρ' := MonoidHom.liftOfSurjective φ hφ ⟨ρh, hle⟩
  have hρ' : ∀ g, ρ' (φ g) = ρh g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ) ⟨ρh, hle⟩ g
  have hfix : (FA5.fixSub (ρ' (φ z))).index ≤ 2 := by
    let H : Subgroup ↥Y := (I (ρ z) Y X).subgroupOf Y
    have hsub : H.map (QuotientGroup.mk' X') ≤ FA5.fixSub (ρ' (φ z)) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [FA5.mem_fixSub, hρ']
      exact (hmem z y).mpr (Subgroup.mem_subgroupOf.mp hy).2
    calc (FA5.fixSub (ρ' (φ z))).index ≤ (H.map (QuotientGroup.mk' X')).index :=
          Subgroup.index_antitone hsub
      _ ≤ H.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_map_dvd H (QuotientGroup.mk'_surjective X'))
      _ = idx (ρ z) Y X := rfl
      _ ≤ 2 := hidx2
  obtain ⟨g, y, hy, hgy⟩ := hnt
  have h1 := FA5.alt5_trivial_of_transvection hV2 (ρ := ρ') hz1 hz2 hfix (φ g)
  rw [hρ'] at h1
  apply hgy
  have := (hmem g ⟨y, hy⟩).mp (by rw [h1]; rfl)
  exact this

end TV

section Layers

variable {A : Type*} [CommGroup A] [Finite A] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut A}

@[expose] def qcomm (ρ : Γ →* MulAut A) (K : Subgroup Γ) (Y : Subgroup A) : Subgroup A :=
  Subgroup.closure {a | ∃ q ∈ K, ∃ y ∈ Y, a = ρ q y * y⁻¹}

theorem qcomm_le {K : Subgroup Γ} {Y : Subgroup A} (hY : GInv ρ Y) : qcomm ρ K Y ≤ Y := by
  refine (Subgroup.closure_le Y).mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  exact Y.mul_mem (hY q y hy) (Y.inv_mem hy)

theorem mul_inv_mem_qcomm {K : Subgroup Γ} {Y : Subgroup A} {q : Γ} (hq : q ∈ K) {y : A}
    (hy : y ∈ Y) : ρ q y * y⁻¹ ∈ qcomm ρ K Y :=
  Subgroup.subset_closure ⟨q, hq, y, hy, rfl⟩

theorem qcomm_ginv {K : Subgroup Γ} [K.Normal] {Y : Subgroup A} (hY : GInv ρ Y) :
    GInv ρ (qcomm ρ K Y) := by
  intro g a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q, hq, y, hy, rfl⟩ := hx
    have : ρ g (ρ q y * y⁻¹) = ρ (g * q * g⁻¹) (ρ g y) * (ρ g y)⁻¹ := by
      have e : g * q * g⁻¹ * g = g * q := by group
      have e1 : ρ (g * q * g⁻¹) (ρ g y) = ρ g (ρ q y) := by
        rw [← MulAut.mul_apply, ← map_mul, e, map_mul]; rfl
      rw [e1, map_mul, map_inv]
    rw [this]
    exact mul_inv_mem_qcomm (Subgroup.Normal.conj_mem ‹K.Normal› q hq g) (hY g y hy)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem four_le_idx_of_nonfix (h2 : ∀ a : A, a * a = 1) (φ : Γ →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ)
    (hnil : ∀ Y : Subgroup A, GInv ρ Y → qcomm ρ φ.ker Y = Y → Y = ⊥)
    {z : Γ} (hz1 : φ z ≠ 1) (hz2 : φ z ^ 2 = 1) :
    ∀ (n : ℕ) (Y : Subgroup A), Nat.card Y ≤ n → GInv ρ Y →
      (∃ g : Γ, Odd (orderOf g) ∧ ∃ y ∈ Y, ρ g y ≠ y) → 4 ≤ idx (ρ z) Y ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hn hY ⟨g0, hg0, y0, hy0, hne⟩
    set X := qcomm ρ φ.ker Y with hXdef
    have hXY : X ≤ Y := qcomm_le hY
    have hXg : GInv ρ X := qcomm_ginv hY
    by_cases hc : ∃ g : Γ, ∃ y ∈ Y, ρ g y * y⁻¹ ∉ X
    · obtain ⟨g, y, hy, hgy⟩ := hc
      have h4 := four_le_idx_section h2 φ hφ hXY hY hXg
        (fun q hq y hy => mul_inv_mem_qcomm hq hy) ⟨g, y, hy, hgy⟩ hz1 hz2
      exact h4.trans (idx_anti_right _ Y bot_le)
    · push_neg at hc
      have hfixX : ∃ x ∈ X, ρ g0 x ≠ x := by
        by_contra hall
        push_neg at hall
        exact hne (coprime_sub h2 hg0 hall (fun y hy => hc g0 y hy) y0 hy0)
      have hlt : X < Y := by
        refine lt_of_le_of_ne hXY ?_
        intro heq
        have := hnil Y hY heq
        rw [this] at hy0
        have : y0 = 1 := (Subgroup.mem_bot.mp hy0)
        rw [this, map_one] at hne
        exact hne rfl
      have hcard : Nat.card X < n := lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) hn
      have := ih (Nat.card X) hcard X le_rfl hXg (by
        obtain ⟨x, hx, hxne⟩ := hfixX
        exact ⟨g0, hg0, x, hx, hxne⟩)
      exact this.trans (idx_mono_left _ hXY _)

theorem orderOf_conj' (h g : Γ) : orderOf (h * g * h⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g
  simpa [MulAut.conj_apply] using this

variable (ρ) in
@[expose] def Cfix : Subgroup A where
  carrier := {m | ∀ g : Γ, Odd (orderOf g) → ρ g m = m}
  mul_mem' := fun {a b} ha hb g hg => by rw [map_mul, ha g hg, hb g hg]
  one_mem' := fun g _ => map_one _
  inv_mem' := fun {a} ha g hg => by rw [map_inv, ha g hg]

theorem mem_Cfix {m : A} : m ∈ Cfix ρ ↔ ∀ g : Γ, Odd (orderOf g) → ρ g m = m := Iff.rfl

theorem Cfix_ginv : GInv ρ (Cfix ρ) := by
  intro h m hm g hg
  have hoc : orderOf (h⁻¹ * g * h) = orderOf g := by
    have := orderOf_conj' h⁻¹ g; simpa using this
  have h1 := hm (h⁻¹ * g * h) (by rw [hoc]; exact hg)
  have : ρ g (ρ h m) = ρ h (ρ (h⁻¹ * g * h) m) := by
    simp only [← MulAut.mul_apply, ← map_mul]; congr 2; group
  rw [this, h1]

theorem mem_Cfix_of (h2 : ∀ a : A, a * a = 1) {m : A}
    (h : ∀ g : Γ, Odd (orderOf g) → ρ g m * m⁻¹ ∈ Cfix ρ) : m ∈ Cfix ρ := by
  intro g hg
  have hc := h g hg
  exact coprime_fix h2 hg (c := ρ g m * m⁻¹) (hc g hg) (by simp)

theorem odd_fix_qcomm (h2 : ∀ a : A, a * a = 1) (φ : Γ →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ)
    (hnil : ∀ Y : Subgroup A, GInv ρ Y → qcomm ρ φ.ker Y = Y → Y = ⊥)
    {z : Γ} (hz1 : φ z ≠ 1) (hz2 : φ z ^ 2 = 1)
    (hbound : idx (ρ z) ⊤ ⊥ ≤ 4)
    (hnt : ∃ (g : Γ) (y : A), ρ g y * y⁻¹ ∉ qcomm ρ φ.ker ⊤) :
    qcomm ρ φ.ker ⊤ ≤ Cfix ρ := by
  have hT : GInv ρ (⊤ : Subgroup A) := fun _ _ _ => Subgroup.mem_top _
  have hW : GInv ρ (qcomm ρ φ.ker ⊤) := qcomm_ginv hT
  intro x hx g hg
  by_contra hne
  have h1 := four_le_idx_of_nonfix h2 φ hφ hnil hz1 hz2 _ (qcomm ρ φ.ker ⊤) le_rfl hW
    ⟨g, hg, x, hx, hne⟩
  have h2' := four_le_idx_section h2 φ hφ (qcomm_le hT) hT hW
    (fun q hq y _ => mul_inv_mem_qcomm hq (Subgroup.mem_top _))
    (by obtain ⟨g, y, hy⟩ := hnt; exact ⟨g, y, Subgroup.mem_top _, hy⟩) hz1 hz2
  have h3 := idx_super (ρ z) (W := ⊤) (Y := qcomm ρ φ.ker ⊤) (X := ⊥) le_top bot_le
    (fun y hy => hW z y hy)
  nlinarith

end Layers

section FourPoint

variable {V : Type*} [CommGroup V] [Finite V] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut V}
  {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction Γ Ω]

theorem prod_transport_eq_one [MulAction.IsPretransitive Γ Ω] (p0 : Ω)
    (hNoFix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1) {u : V}
    (hB : ∀ b : Γ, b • p0 = p0 → ρ b u = u) (r : Ω → Γ) (hr : ∀ y, r y • p0 = y) :
    ∏ y : Ω, ρ (r y) u = 1 := by
  apply hNoFix
  intro g
  rw [map_prod]
  have key : ∀ y : Ω, ρ g (ρ (r y) u) = ρ (r (g • y)) u := by
    intro y
    have hc : ((r (g • y))⁻¹ * (g * r y)) • p0 = p0 := by
      rw [mul_smul, mul_smul, hr y, inv_smul_eq_iff, hr]
    have := hB _ hc
    calc ρ g (ρ (r y) u) = ρ (g * r y) u := by rw [map_mul]; rfl
      _ = ρ (r (g • y) * ((r (g • y))⁻¹ * (g * r y))) u := by group
      _ = ρ (r (g • y)) u := by rw [map_mul, MulAut.mul_apply, this]
  simp_rw [key]
  exact Equiv.prod_comp (MulAction.toPerm g) (fun y => ρ (r y) u)

theorem sq_card_le_range_kap [MulAction.IsPretransitive Γ Ω] (h2 : ∀ v : V, v * v = 1)
    (p0 p1 p2 p3 p4 : Ω) (hlist : ([p0, p1, p2, p3, p4] : List Ω).Nodup)
    (huniv : ∀ y : Ω, y ∈ ([p0, p1, p2, p3, p4] : List Ω))
    (hNoFix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1) {z z' : Γ}
    (hz1 : z • p1 = p2) (hz1' : z' • p1 = p3) (hz3 : z • p3 = p4)
    (hzz : ρ (z * z) = 1) (hzz' : ρ (z' * z') = 1) (hcomm : ρ (z * z') = ρ (z' * z))
    (U : Subgroup V) (hU : ∀ u ∈ U, ∀ b : Γ, b • p0 = p0 → ρ b u = u) :
    Nat.card U ^ 2 ≤ Nat.card (kap (ρ z)).range := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Ω → Γ, ∀ y, r y • p0 = y := ⟨fun y => (MulAction.exists_smul_eq Γ p0 y).choose,
    fun y => (MulAction.exists_smul_eq Γ p0 y).choose_spec⟩
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (h2 v)
  have htr : ∀ (g : Γ) (y y' : Ω), g • y = y' → ∀ u ∈ U, ρ g (ρ (r y) u) = ρ (r y') u := by
    intro g y y' hgy u hu
    have hc : ((r y')⁻¹ * (g * r y)) • p0 = p0 := by
      rw [mul_smul, mul_smul, hr y, hgy, inv_smul_eq_iff, hr]
    have := hU u hu _ hc
    calc ρ g (ρ (r y) u) = ρ (g * r y) u := by rw [map_mul]; rfl
      _ = ρ (r y' * ((r y')⁻¹ * (g * r y))) u := by group
      _ = ρ (r y') u := by rw [map_mul, MulAut.mul_apply, this]
  have hrel : ∀ u ∈ U, u * ρ (r p1) u * ρ z (ρ (r p1) u) * ρ z' (ρ (r p1) u) *
      ρ z (ρ z' (ρ (r p1) u)) = 1 := by
    intro u hu
    have hprod := prod_transport_eq_one (ρ := ρ) p0 hNoFix (hU u hu) r hr
    have huniv' : (Finset.univ : Finset Ω) = ([p0, p1, p2, p3, p4] : List Ω).toFinset := by
      ext y; simp only [Finset.mem_univ, List.mem_toFinset, true_iff]; exact huniv y
    rw [huniv', List.prod_toFinset _ hlist] at hprod
    have h0 : ρ (r p0) u = u := hU u hu _ (hr p0)
    have h2' : ρ (r p2) u = ρ z (ρ (r p1) u) := (htr z p1 p2 hz1 u hu).symm
    have h3' : ρ (r p3) u = ρ z' (ρ (r p1) u) := (htr z' p1 p3 hz1' u hu).symm
    have h4' : ρ (r p4) u = ρ z (ρ z' (ρ (r p1) u)) := by
      rw [← htr z p3 p4 hz3 u hu, ← htr z' p1 p3 hz1' u hu]
    simpa [h0, h2', h3', h4', mul_assoc] using hprod
  let w : U →* V := (ρ (r p1) : MulAut V).toMonoidHom.comp U.subtype
  let s : U →* V := (kap (ρ z)).comp w
  have hs : ∀ u : U, s u = ρ z (w u) * w u := fun u => by
    show kap (ρ z) (w u) = _
    rw [kap_apply, hinv]
  have hzz1 : ∀ v : V, ρ z (ρ z v) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) hzz
    simpa [map_mul] using this
  have hzz1' : ∀ v : V, ρ z' (ρ z' v) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) hzz'
    simpa [map_mul] using this
  have hc : ∀ v : V, ρ z' (ρ z v) = ρ z (ρ z' v) := fun v => by
    have := congrArg (fun f : MulAut V => f v) hcomm
    simp only [map_mul, MulAut.mul_apply] at this
    exact this.symm
  have hs' : ∀ u : U, ρ z' (s u) = ρ z (ρ z' (w u)) * ρ z' (w u) := fun u => by
    rw [hs, map_mul, hc]
  have hF1 : ∀ u : U, (u : V) = s u * ρ z' (s u) := by
    intro u
    have h := hrel u u.2
    have hw : ρ (r p1) (u : V) = w u := rfl
    rw [hw] at h
    rw [hs', hs]
    have e0 : (u : V) * (w u * ρ z (w u) * ρ z' (w u) * ρ z (ρ z' (w u))) = 1 := by
      simpa [mul_assoc] using h
    have e : (u : V) = (w u * ρ z (w u) * ρ z' (w u) * ρ z (ρ z' (w u)))⁻¹ :=
      eq_inv_of_mul_eq_one_left e0
    rw [e, hinv]
    ac_rfl
  have hF2 : ∀ u : U, kap (ρ z') (s u) = u := by
    intro u
    rw [kap_apply, hinv]
    exact (mul_comm _ _).trans (hF1 u).symm
  have hF3 : ∀ u : U, kap (ρ z') (ρ z' (s u)) = u := by
    intro u
    rw [kap_apply, hzz1', hinv]
    exact (hF1 u).symm
  let H : U × U →* V := s.comp (MonoidHom.fst U U) *
    ((ρ z' : MulAut V).toMonoidHom.comp s).comp (MonoidHom.snd U U)
  have hH : ∀ p : U × U, H p = s p.1 * ρ z' (s p.2) := fun p => rfl
  have hinj : Function.Injective H := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, u'⟩ h
    rw [hH] at h
    have h1 : s u = ρ z' (s u') := by
      have := eq_inv_of_mul_eq_one_left h
      rw [this, hinv]
    have h2' : u = u' := Subtype.ext (by rw [← hF2 u, h1, hF3])
    subst h2'
    have h3 : u = 1 := by
      apply Subtype.ext
      rw [← hF2 u, kap_apply, ← h1, mul_inv_cancel]; rfl
    exact Prod.ext h3 h3
  have hmem : ∀ p : U × U, H p ∈ (kap (ρ z)).range := by
    intro p
    rw [hH]
    refine (kap (ρ z)).range.mul_mem ⟨w p.1, rfl⟩ ?_
    refine ⟨ρ z' (w p.2), ?_⟩
    rw [hs', kap_apply, hinv]
  have hcard := Nat.card_le_card_of_injective (fun p : U × U => (⟨H p, hmem p⟩ : (kap (ρ z)).range))
    (fun a b hab => hinj (congrArg Subtype.val hab))
  rw [Nat.card_prod] at hcard
  rw [pow_two]; exact hcard

end FourPoint

section Summary

variable {A : Type*} [CommGroup A] [Finite A] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut A}

theorem card_range_kap_eq_idx (σ : MulAut A) : Nat.card (kap σ).range = idx σ ⊤ ⊥ := by
  have h : I σ ⊤ ⊥ = (kap σ).ker := by
    ext a; simp [mem_I, MonoidHom.mem_ker]
  unfold idx
  rw [h, Subgroup.relIndex_ker, Subgroup.map_top]

theorem relIndex_Cfix_le_two (h2 : ∀ a : A, a * a = 1) (φ : Γ →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ)
    (hnil : ∀ Y : Subgroup A, GInv ρ Y → qcomm ρ φ.ker Y = Y → Y = ⊥)
    {z z' : Γ} (hz1 : φ z ≠ 1) (hz2 : φ z ^ 2 = 1)
    (hbound : idx (ρ z) ⊤ ⊥ ≤ 4)
    (hnt : ∃ (g : Γ) (y : A), ρ g y * y⁻¹ ∉ qcomm ρ φ.ker ⊤)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction Γ Ω] [MulAction.IsPretransitive Γ Ω]
    (p0 p1 p2 p3 p4 : Ω) (hlist : ([p0, p1, p2, p3, p4] : List Ω).Nodup)
    (huniv : ∀ y : Ω, y ∈ ([p0, p1, p2, p3, p4] : List Ω))
    (hz1p : z • p1 = p2) (hz1p' : z' • p1 = p3) (hz3p : z • p3 = p4)
    (hzz : φ (z * z) = 1) (hzz' : φ (z' * z') = 1) (hcomm : φ (z * z') = φ (z' * z))
    (Z : Subgroup A)
    (hZ : ∀ u ∈ Z, ∀ b : Γ, b • p0 = p0 → ρ b u * u⁻¹ ∈ qcomm ρ φ.ker ⊤) :
    (Cfix ρ).relIndex Z ≤ 2 := by
  have hW : qcomm ρ φ.ker ⊤ ≤ Cfix ρ :=
    odd_fix_qcomm h2 φ hφ hnil hz1 hz2 hbound hnt
  have hker : ∀ q ∈ φ.ker, ∀ a : A, ρ q a * a⁻¹ ∈ Cfix ρ := fun q hq a =>
    hW (mul_inv_mem_qcomm hq (Subgroup.mem_top a))
  let ρ' : Γ →* MulAut (A ⧸ Cfix ρ) := quotAct (Cfix ρ) Cfix_ginv
  have hρ'mk : ∀ (g : Γ) (a : A), ρ' g (a : A ⧸ Cfix ρ) = ((ρ g a : A) : A ⧸ Cfix ρ) :=
    fun g a => quotAct_mk Cfix_ginv g a
  have hmkeq : ∀ x y : A, (x : A ⧸ Cfix ρ) = (y : A ⧸ Cfix ρ) ↔ y⁻¹ * x ∈ Cfix ρ := by
    intro x y; rw [QuotientGroup.eq, ← inv_mem_iff]; simp
  have hρ'ker : ∀ q ∈ φ.ker, ρ' q = 1 := by
    intro q hq
    ext v
    induction v using QuotientGroup.induction_on with
    | H a =>
      rw [hρ'mk]
      show _ = (a : A ⧸ Cfix ρ)
      rw [hmkeq, mul_comm]
      exact hker q hq a
  have hV2 : ∀ v : A ⧸ Cfix ρ, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_mul, h2 a]; rfl
  have hNoFix : ∀ v : A ⧸ Cfix ρ, (∀ g : Γ, ρ' g v = v) → v = 1 := by
    intro v hv
    induction v using QuotientGroup.induction_on with
    | H a =>
      have : a ∈ Cfix ρ := by
        refine mem_Cfix_of h2 (fun g _ => ?_)
        have h1 := (hmkeq _ _).mp ((hρ'mk g a).symm.trans (hv g))
        rw [mul_comm] at h1
        exact h1
      exact (QuotientGroup.eq_one_iff a).mpr this
  have hq : ∀ x y : Γ, φ x = φ y → ρ' x = ρ' y := by
    intro x y hxy
    have hm : x⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have := hρ'ker _ hm
    rw [map_mul, map_inv] at this
    exact (inv_mul_eq_one.mp this)
  have hρzz : ρ' (z * z) = 1 := by
    apply hρ'ker; exact hzz
  have hρzz' : ρ' (z' * z') = 1 := hρ'ker _ hzz'
  have hρc : ρ' (z * z') = ρ' (z' * z) := hq _ _ hcomm
  let Zb : Subgroup (A ⧸ Cfix ρ) := Z.map (QuotientGroup.mk' (Cfix ρ))
  have hZb : ∀ u ∈ Zb, ∀ b : Γ, b • p0 = p0 → ρ' b u = u := by
    rintro _ ⟨u, hu, rfl⟩ b hb
    show ρ' b (u : A ⧸ Cfix ρ) = (u : A ⧸ Cfix ρ)
    rw [hρ'mk, hmkeq, mul_comm]
    exact hW (hZ u hu b hb)
  have h1 := sq_card_le_range_kap (ρ := ρ') hV2 p0 p1 p2 p3 p4 hlist huniv hNoFix hz1p hz1p' hz3p
    hρzz hρzz' hρc Zb hZb
  have h2' : Nat.card (kap (ρ' z)).range ≤ Nat.card (kap (ρ z)).range := by
    refine Nat.card_le_card_of_surjective
      (fun x : (kap (ρ z)).range => (⟨(x.1 : A ⧸ Cfix ρ), ?_⟩ : (kap (ρ' z)).range)) ?_
    · obtain ⟨a, ha⟩ := x.2
      refine ⟨(a : A ⧸ Cfix ρ), ?_⟩
      rw [kap_apply, hρ'mk, ← ha]; rfl
    · rintro ⟨_, ⟨v, rfl⟩⟩
      induction v using QuotientGroup.induction_on with
      | H a =>
        refine ⟨⟨kap (ρ z) a, a, rfl⟩, ?_⟩
        apply Subtype.ext
        show ((kap (ρ z) a : A) : A ⧸ Cfix ρ) = kap (ρ' z) (a : A ⧸ Cfix ρ)
        simp only [kap_apply]
        rw [hρ'mk]; rfl
  have h3 : Nat.card Zb ^ 2 ≤ 4 := by
    calc Nat.card Zb ^ 2 ≤ Nat.card (kap (ρ' z)).range := h1
      _ ≤ Nat.card (kap (ρ z)).range := h2'
      _ = idx (ρ z) ⊤ ⊥ := card_range_kap_eq_idx _
      _ ≤ 4 := hbound
  have h4 : Nat.card Zb ≤ 2 := by nlinarith [Nat.zero_le (Nat.card Zb)]
  have h5 : (Cfix ρ).relIndex Z = Nat.card Zb := by
    have := Subgroup.relIndex_ker (f := QuotientGroup.mk' (Cfix ρ)) (K := Z)
    rwa [QuotientGroup.ker_mk'] at this
  rw [h5]; exact h4

end Summary

section OddClosure

variable {A : Type*} [CommGroup A] [Finite A] {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] def oddNC (Γ : Type*) [Group Γ] : Subgroup Γ :=
  Subgroup.normalClosure {g : Γ | Odd (orderOf g)}

theorem exists_odd_ne_one (φ : Γ →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ) :
    ∃ g : Γ, Odd (orderOf g) ∧ φ g ≠ 1 := by
  obtain ⟨h, hh3, hh1⟩ : ∃ h : alternatingGroup (Fin 5), h ^ 3 = 1 ∧ h ≠ 1 := by decide +kernel
  obtain ⟨g, rfl⟩ := hφ h
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨g ^ 2 ^ a, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by positivity) (hnm ▸ Dvd.intro _ rfl), hnm, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  · intro h1
    rw [map_pow] at h1
    have h3 : orderOf (φ g) ∣ 3 := orderOf_dvd_of_pow_eq_one hh3
    have h2 : orderOf (φ g) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
    have : orderOf (φ g) = 1 := by
      have h4 : orderOf (φ g) ∣ Nat.gcd 3 (2 ^ a) := Nat.dvd_gcd h3 h2
      have h5 : Nat.gcd 3 (2 ^ a) = 1 := Nat.Coprime.pow_right a (by norm_num)
      rw [h5] at h4; exact Nat.dvd_one.mp h4
    exact hh1 (orderOf_eq_one_iff.mp this)

theorem oddNC_map_top (φ : Γ →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ) :
    (oddNC Γ).map φ = ⊤ := by
  haveI : (oddNC Γ).Normal := Subgroup.normalClosure_normal
  haveI : ((oddNC Γ).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oddNC Γ).map φ) with h | h
  · exfalso
    obtain ⟨g, hg, hg1⟩ := exists_odd_ne_one φ hφ
    have : g ∈ oddNC Γ := Subgroup.subset_normalClosure hg
    have h2 : φ g ∈ (oddNC Γ).map φ := ⟨g, this, rfl⟩
    rw [h] at h2
    exact hg1 (Subgroup.mem_bot.mp h2)
  · exact h

theorem oddNC_fix {ρ : Γ →* MulAut A} {g : Γ} (hg : g ∈ oddNC Γ) :
    ∀ c ∈ Cfix ρ, ρ g c = c := by
  let K0 : Subgroup Γ :=
    { carrier := {g | ∀ c ∈ Cfix ρ, ρ g c = c}
      mul_mem' := fun {a b} ha hb c hc => by
        rw [map_mul, MulAut.mul_apply, hb c hc, ha c hc]
      one_mem' := fun c _ => by simp
      inv_mem' := fun {a} ha c hc => by
        have := ha c hc
        rw [map_inv, MulAut.inv_apply]
        exact (MulEquiv.symm_apply_eq _).mpr this.symm }
  haveI : K0.Normal := ⟨fun n hn h c hc => by
    have hc' : ρ h⁻¹ c ∈ Cfix ρ := Cfix_ginv h⁻¹ c hc
    have := hn _ hc'
    show ρ (h * n * h⁻¹) c = c
    simp only [map_mul, MulAut.mul_apply]
    rw [this, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl⟩
  have : oddNC Γ ≤ K0 := by
    refine (Subgroup.normalClosure_le_normal (N := K0) ?_)
    intro g hg c hc
    exact hc g hg
  exact this hg

end OddClosure

end CFSG.Quasithin.Kleidman.F204.Sec

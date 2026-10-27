module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314G
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314I
public import CFSG.Quasithin.Background.HL3WrWreath

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

theorem nonempty_quot_wreath {K : Type} [Group K] (φ : K →* Equiv.Perm (Fin 6))
    (hφ : φ.range = wreathS3Z2) (hk : IsPGroup 2 φ.ker) :
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* ↥wreathS3Z2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ x, φ x ∈ wreathS3Z2 := fun x => hφ ▸ ⟨x, rfl⟩
  set ψ : K →* ↥wreathS3Z2 := φ.codRestrict wreathS3Z2 hmem with hψ
  set χ : K →* S152N.W3 := Wreath.wreathEquiv.symm.toMonoidHom.comp ψ with hχ
  have hψs : Function.Surjective ψ := by
    rintro ⟨σ, hσ⟩
    rw [← hφ] at hσ
    obtain ⟨x, rfl⟩ := hσ
    exact ⟨x, rfl⟩
  have hχs : Function.Surjective χ := Wreath.wreathEquiv.symm.surjective.comp hψs
  have hkerχ : χ.ker = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hχ, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    rw [← Subtype.coe_inj]
    rfl
  have hle1 : χ.ker ≤ CFSG.pCore 2 K := le_sSup ⟨MonoidHom.normal_ker χ, hkerχ ▸ hk⟩
  have hle2 : CFSG.pCore 2 K ≤ χ.ker := by
    have hN : ((CFSG.pCore 2 K).map χ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := K)).map χ hχs
    have h2 : IsPGroup 2 ((CFSG.pCore 2 K).map χ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := K)).map χ
    have hbot := H.L3Wr.W3.eq_bot_of_normal_isPGroup_two hN h2
    intro x hx
    rw [MonoidHom.mem_ker]
    have : χ x ∈ (CFSG.pCore 2 K).map χ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hkeq : χ.ker = CFSG.pCore 2 K := le_antisymm hle1 hle2
  have : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal (p := 2) (G := K)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkeq.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective χ hχs).trans Wreath.wreathEquiv)⟩

@[expose] def lo (j : Fin 3) : Fin 6 := ⟨j.val, by omega⟩

@[expose] def hi (j : Fin 3) : Fin 6 := ⟨j.val + 3, by omega⟩

theorem fin6_cases (i : Fin 6) : (∃ j : Fin 3, i = lo j) ∨ ∃ j : Fin 3, i = hi j := by
  by_cases h : i.val < 3
  · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
  · exact Or.inr ⟨⟨i.val - 3, by omega⟩, Fin.ext (by simp [hi]; omega)⟩

theorem lo_val (j : Fin 3) : (lo j).val = j.val := rfl

theorem hi_val (j : Fin 3) : (hi j).val = j.val + 3 := rfl

@[expose] def emb₁ (α : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 6) where
  toFun i := if h : i.val < 3 then ⟨(α ⟨i.val, h⟩ : Fin 3).val, by omega⟩ else i
  invFun i := if h : i.val < 3 then ⟨(α.symm ⟨i.val, h⟩ : Fin 3).val, by omega⟩ else i
  left_inv i := by
    by_cases h : i.val < 3
    · have h' : (α ⟨i.val, h⟩ : Fin 3).val < 3 := (α _).isLt
      simp only [h, h', dite_true]
      ext
      simp
    · simp only [h, dite_false]
  right_inv i := by
    by_cases h : i.val < 3
    · have h' : (α.symm ⟨i.val, h⟩ : Fin 3).val < 3 := (α.symm _).isLt
      simp only [h, h', dite_true]
      ext
      simp
    · simp only [h, dite_false]

theorem emb₁_lo (α : Equiv.Perm (Fin 3)) (j : Fin 3) : emb₁ α (lo j) = lo (α j) := by
  simp [emb₁, lo, j.isLt]

theorem emb₁_hi (α : Equiv.Perm (Fin 3)) (j : Fin 3) : emb₁ α (hi j) = hi j := by
  simp [emb₁, hi]

theorem emb₁_one : emb₁ 1 = 1 := by decide +kernel

theorem emb₁_swap : emb₁ (Equiv.swap 0 1) = Equiv.swap 0 1 := by decide +kernel

theorem emb₁_cyc : emb₁ (Equiv.swap 0 1 * Equiv.swap 1 2) = Equiv.swap 0 1 * Equiv.swap 1 2 := by
  decide +kernel

theorem swap_check : ∀ s : Equiv.Perm (Fin 6), BlockPres s → 3 ≤ (s 0).val →
    ∃ α β : Equiv.Perm (Fin 3), emb₁ β * s * emb₁ α =
      Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5 := by
  decide +kernel

section Six

variable {G : Type} [Group G] {X T L : Subgroup G} {V : Type} [CommGroup V]
  (ρ : ↥X →* MulAut V) {Lb L2 : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ}
  (c : Coord Lb U Z k) (r : ↥X) (cc : L3.Γ)

@[expose] def pts (i : Fin 6) : Subgroup (MulAut V) :=
  if i.val < 3 then c.imgSub (sylOf cc ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩)
  else conjSub (ρ r) (c.imgSub (sylOf cc ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩))

theorem pts_low (j : Fin 3) : pts ρ c r cc (lo j) = c.imgSub (sylOf cc j) := by
  have h1 : j.val % 3 = j.val := Nat.mod_eq_of_lt j.isLt
  simp only [pts, lo, j.isLt, ↓reduceIte, h1]

theorem pts_high (j : Fin 3) :
    pts ρ c r cc (hi j) = conjSub (ρ r) (c.imgSub (sylOf cc j)) := by
  have h1 : (j.val + 3) % 3 = j.val := by omega
  simp only [pts, hi, show ¬ j.val + 3 < 3 by omega, ↓reduceIte, h1]

variable {ρ c r cc}

variable (hL2 : conjSub (ρ r) Lb = L2) (hbot : Lb ⊓ L2 = ⊥)
  (hdist : ∀ i j : Fin 3, i ≠ j → (cc ^ (j : ℕ))⁻¹ * cc ^ (i : ℕ) ∉ bSub)

theorem pts_le_low (j : Fin 3) : pts ρ c r cc (lo j) ≤ Lb := by
  rw [pts_low]
  exact c.imgSub_le _

include hL2 in
theorem pts_le_high (j : Fin 3) : pts ρ c r cc (hi j) ≤ L2 := by
  rw [pts_high, ← hL2]
  exact conjSub_mono _ (c.imgSub_le _)

theorem pts_ne_bot (i : Fin 6) : pts ρ c r cc i ≠ ⊥ := by
  intro h
  have h8 : Nat.card (pts ρ c r cc i) = 8 := by
    unfold pts
    split_ifs
    · rw [c.card_imgSub, card_sylOf]
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective, c.card_imgSub,
        card_sylOf]
  rw [h, Subgroup.card_bot] at h8
  omega

include hL2 hbot in
theorem lt_three_of_le {i : Fin 6} (h : pts ρ c r cc i ≤ Lb) : i.val < 3 := by
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact j.isLt
  · exfalso
    apply pts_ne_bot (ρ := ρ) (c := c) (r := r) (cc := cc) (hi j)
    exact le_bot_iff.mp (hbot ▸ le_inf h (pts_le_high hL2 j))

include hbot in
theorem three_le_of_le {i : Fin 6} (h : pts ρ c r cc i ≤ L2) : 3 ≤ i.val := by
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    apply pts_ne_bot (ρ := ρ) (c := c) (r := r) (cc := cc) (lo j)
    exact le_bot_iff.mp (hbot ▸ le_inf (pts_le_low j) h)
  · rw [hi_val]
    omega

include hL2 hbot hdist in
theorem pts_injective : Function.Injective (pts ρ c r cc) := by
  intro i i' h
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> rcases fin6_cases i' with ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [pts_low, pts_low, c.imgSub_inj] at h
    rw [sylOf_injective hdist h]
  · exfalso
    have h1 : pts ρ c r cc (lo j) ≤ L2 := h ▸ pts_le_high hL2 j'
    have := three_le_of_le hbot h1
    rw [lo_val] at this
    omega
  · exfalso
    have h1 : pts ρ c r cc (hi j) ≤ Lb := h ▸ pts_le_low j'
    have := lt_three_of_le hL2 hbot h1
    rw [hi_val] at this
    omega
  · rw [pts_high, pts_high, conjSub_inj, c.imgSub_inj] at h
    rw [sylOf_injective hdist h]

theorem conjSub_eq_of_comm {W : Type} [Group W] {a : W} {D : Subgroup W}
    (h : ∀ d ∈ D, a * d = d * a) : conjSub a D = D := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have e := h _ hx
    have : x = a⁻¹ * x * a := by
      calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
        _ = (a⁻¹ * x * a) * a * a⁻¹ := by rw [e]
        _ = a⁻¹ * x * a := by group
    rw [this]
    exact hx
  · intro hx
    have e := h _ hx
    have : a⁻¹ * x * a = x := by
      calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
        _ = a⁻¹ * (a * x) := by rw [e]
        _ = x := by group
    rw [this]
    exact hx

@[expose] def stabD (hinj : Function.Injective (pts ρ c r cc)) : Subgroup (MulAut V) where
  carrier := {w | ∀ i, ∃ j, conjSub w (pts ρ c r cc i) = pts ρ c r cc j}
  one_mem' i := ⟨i, conjSub_one _⟩
  mul_mem' {a b} ha hb i := by
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨j', hj'⟩ := ha j
    exact ⟨j', by rw [conjSub_mul, hj, hj']⟩
  inv_mem' {a} ha i := by
    choose f hf using ha
    have hfi : Function.Injective f := by
      intro i₁ i₂ h
      apply hinj
      have h1 := hf i₁
      have h2 := hf i₂
      rw [h, ← h2] at h1
      exact ((conjSub_inj a).mp h1)
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hfi) i
    refine ⟨j, ?_⟩
    rw [← hj, ← hf j, conjSub_conjSub_inv]

theorem mem_stabD (hinj : Function.Injective (pts ρ c r cc)) {w : MulAut V} :
    w ∈ stabD hinj ↔ ∀ i, ∃ j, conjSub w (pts ρ c r cc i) = pts ρ c r cc j := Iff.rfl

end Six

theorem conjSub_self_of_mem {W : Type} [Group W] {D : Subgroup W} {d : W} (hd : d ∈ D) :
    conjSub d D = D := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := D.mul_mem (D.mul_mem hd h) (D.inv_mem hd)
    simpa [mul_assoc] using this
  · intro h
    exact D.mul_mem (D.mul_mem (D.inv_mem hd) h) hd

theorem conjSub_pow_of_eq {W : Type} [Group W] {a : W} {D : Subgroup W} (h : conjSub a D = D)
    (n : ℕ) : conjSub (a ^ n) D = D := by
  induction n with
  | zero => rw [pow_zero, conjSub_one]
  | succ n ih => rw [pow_succ, conjSub_mul, h, ih]

section Hyp

variable {G : Type} [Group G] {X T L : Subgroup G} {V : Type} [CommGroup V]
  {ρ : ↥X →* MulAut V} {Lb L2 : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ}
  {c : Coord Lb U Z k} {r : ↥X} {Q : Subgroup L3.Γ} {cc : L3.Γ}

variable (T L ρ L2 c r Q cc) in
structure SixHyp : Prop where
  TX : T ≤ X
  rT : (r : G) ∈ T
  hL2 : conjSub (ρ r) Lb = L2
  hbot : Lb ⊓ L2 = ⊥
  comm : ∀ a ∈ Lb, ∀ b ∈ L2, a * b = b * a
  dich : ∀ x : ↥X, conjSub (ρ x) Lb = Lb ∨ conjSub (ρ x) Lb = L2
  liftL : ∀ a ∈ Lb, ∃ x : ↥X, (x : G) ∈ L ∧ ρ x = a
  can : ∀ x : ↥X, (x : G) ∈ T → conjSub (ρ x) Lb = Lb → conjSub (ρ x) (c.imgSub Q) = c.imgSub Q
  ker2 : ∀ x : ↥X, ρ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1
  pow : ∀ x : ↥X, ∃ n : ℕ, ∃ a ∈ Lb, ∃ b ∈ L2, ρ x ^ 2 ^ n = a * b
  hBQ : bSub ≤ Q
  hcQ : cc ∈ Q
  hcos : ∀ y ∈ Q, ∃ j : Fin 3, (cc ^ (j : ℕ))⁻¹ * y ∈ bSub
  hsyl : ∀ γ : L3.Γ, (∀ b ∈ bSub, γ * b * γ⁻¹ ∈ Q) → γ ∈ Q
  hdist : ∀ i j : Fin 3, i ≠ j → (cc ^ (j : ℕ))⁻¹ * cc ^ (i : ℕ) ∉ bSub
  hperm : ∀ α : Equiv.Perm (Fin 3), ∃ γ : L3.Γ, γ ∈ Q ∧
    ∀ i : Fin 3, (cc ^ ((α i : Fin 3) : ℕ))⁻¹ * γ * cc ^ (i : ℕ) ∈ bSub
  hker : ∀ γ : L3.Γ, (∀ i : Fin 3, (cc ^ (i : ℕ))⁻¹ * γ * cc ^ (i : ℕ) ∈ bSub) → γ * γ = 1
  hz : ∀ i : Fin 3, zB ∈ sylOf cc i

namespace SixHyp

variable (s : SixHyp T L ρ L2 c r Q cc)
include s

theorem inj : Function.Injective (pts ρ c r cc) := pts_injective s.hL2 s.hbot s.hdist

theorem Lb_ne_L2 : Lb ≠ L2 := by
  intro h
  apply pts_ne_bot (ρ := ρ) (c := c) (r := r) (cc := cc) (lo 0)
  refine le_bot_iff.mp (s.hbot ▸ le_inf (pts_le_low 0) ?_)
  rw [← h]
  exact pts_le_low 0

theorem conjSub_L2 (x : ↥X) :
    (conjSub (ρ x) Lb = Lb → conjSub (ρ x) L2 = L2) ∧
      (conjSub (ρ x) Lb = L2 → conjSub (ρ x) L2 = Lb) := by
  have e : conjSub (ρ x) L2 = conjSub (ρ (x * r)) Lb := by
    rw [map_mul, conjSub_mul, s.hL2]
  constructor
  · intro hx
    rcases s.dich (x * r) with h | h
    · have h' : conjSub (ρ x) L2 = Lb := by rw [e]; exact h
      exact absurd ((conjSub_inj (ρ x)).mp (hx.trans h'.symm)) s.Lb_ne_L2
    · rw [e, h]
  · intro hx
    rcases s.dich (x * r) with h | h
    · rw [e, h]
    · have h' : conjSub (ρ x) L2 = L2 := by rw [e]; exact h
      exact absurd ((conjSub_inj (ρ x)).mp (hx.trans h'.symm)) s.Lb_ne_L2

theorem conjSub_inv_L2 : conjSub (ρ r)⁻¹ L2 = Lb := by
  rw [← s.hL2, conjSub_conjSub_inv]

theorem fc {x : ↥X} (hxT : (x : G) ∈ T) (hx : conjSub (ρ x) Lb = Lb) (j : Fin 3) :
    ∃ j', conjSub (ρ x) (c.imgSub (sylOf cc j)) = c.imgSub (sylOf cc j') := by
  have hle : conjSub (ρ x) (c.imgSub (sylOf cc j)) ≤ Lb :=
    (conjSub_mono _ (c.imgSub_le _)).trans hx.le
  obtain ⟨P, hP⟩ := c.exists_imgSub hle
  have h8 : Nat.card P = 8 := by
    rw [← c.card_imgSub, ← hP, conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      c.card_imgSub, card_sylOf]
  have hPQ : P ≤ Q := by
    rw [← c.imgSub_le_imgSub_iff, ← hP, ← s.can x hxT hx]
    exact conjSub_mono _ ((c.imgSub_le_imgSub_iff).mpr (sylOf_le s.hBQ s.hcQ j))
  obtain ⟨j', rfl⟩ := eq_sylOf s.hsyl s.hcos h8 hPQ
  exact ⟨j', hP⟩

theorem mem_stabD_of_T {x : ↥X} (hxT : (x : G) ∈ T) : ρ x ∈ stabD s.inj := by
  refine (mem_stabD _).mpr fun i => ?_
  have hrT := s.rT
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> rcases s.dich x with hx | hx
  · obtain ⟨j', hj'⟩ := s.fc hxT hx j
    exact ⟨lo j', by rw [pts_low, pts_low, hj']⟩
  · have hyT : ((r⁻¹ * x : ↥X) : G) ∈ T := T.mul_mem (T.inv_mem hrT) hxT
    have hy : conjSub (ρ (r⁻¹ * x)) Lb = Lb := by
      rw [map_mul, conjSub_mul, hx, map_inv, s.conjSub_inv_L2]
    obtain ⟨j', hj'⟩ := s.fc hyT hy j
    refine ⟨hi j', ?_⟩
    have e : ρ x = ρ r * ρ (r⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
    rw [pts_low, pts_high, e, conjSub_mul, hj']
  · have hyT : ((r⁻¹ * x * r : ↥X) : G) ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hrT) hxT) hrT
    have hy : conjSub (ρ (r⁻¹ * x * r)) Lb = Lb := by
      rw [map_mul, map_mul, conjSub_mul, conjSub_mul, s.hL2, (s.conjSub_L2 x).1 hx, map_inv,
        s.conjSub_inv_L2]
    obtain ⟨j', hj'⟩ := s.fc hyT hy j
    refine ⟨hi j', ?_⟩
    have e : ρ x * ρ r = ρ r * ρ (r⁻¹ * x * r) := by
      rw [← map_mul, ← map_mul, show x * r = r * (r⁻¹ * x * r) by group]
    rw [pts_high, pts_high, ← conjSub_mul, e, conjSub_mul, hj']
  · have hyT : ((x * r : ↥X) : G) ∈ T := T.mul_mem hxT hrT
    have hy : conjSub (ρ (x * r)) Lb = Lb := by
      rw [map_mul, conjSub_mul, s.hL2, (s.conjSub_L2 x).2 hx]
    obtain ⟨j', hj'⟩ := s.fc hyT hy j
    refine ⟨lo j', ?_⟩
    rw [pts_high, pts_low, ← conjSub_mul, ← map_mul, hj']

theorem conjSub_hi_of_mem {a : MulAut V} (ha : a ∈ Lb) (j : Fin 3) :
    conjSub a (pts ρ c r cc (hi j)) = pts ρ c r cc (hi j) :=
  conjSub_eq_of_comm fun d hd => s.comm a ha d (pts_le_high s.hL2 j hd)

theorem conjSub_pts_of_img {x : ↥X} {γ : L3.Γ} (hx : ρ x = c.img γ) {α : Equiv.Perm (Fin 3)}
    (hα : ∀ i, conjSub γ (sylOf cc i) = sylOf cc (α i)) (i : Fin 6) :
    conjSub (ρ x) (pts ρ c r cc i) = pts ρ c r cc (emb₁ α i) := by
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [emb₁_lo, pts_low, pts_low, hx, ← c.imgSub_conjSub, hα]
  · rw [emb₁_hi, hx]
    exact s.conjSub_hi_of_mem (c.img_mem γ) j

theorem mem_stabD_of_img {x : ↥X} (hx : ρ x ∈ c.imgSub Q) : ρ x ∈ stabD s.inj := by
  obtain ⟨γ, hγ, hγx⟩ := (c.mem_imgSub).mp hx
  refine (mem_stabD _).mpr fun i => ?_
  rcases fin6_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨j', hj'⟩ := exists_conjSub_sylOf s.hcos s.hcQ hγ j
    exact ⟨lo j', by rw [pts_low, pts_low, ← hγx, ← c.imgSub_conjSub, hj']⟩
  · exact ⟨hi j, s.conjSub_hi_of_mem (hγx ▸ c.img_mem γ) j⟩

theorem blockPres {x : ↥X} {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ i, conjSub (ρ x) (pts ρ c r cc i) = pts ρ c r cc (σ i)) : BlockPres σ := by
  unfold BlockPres
  intro i hi3
  obtain ⟨j, rfl⟩ : ∃ j : Fin 3, i = lo j := ⟨⟨i.val, hi3⟩, rfl⟩
  rcases s.dich x with hx | hx
  · have key : ∀ j : Fin 3, (σ (lo j)).val < 3 := by
      intro j
      apply lt_three_of_le s.hL2 s.hbot
      rw [← hσ]
      exact (conjSub_mono _ (pts_le_low j)).trans hx.le
    have k0 : (σ 0).val < 3 := key 0
    exact ⟨fun _ => k0, fun _ => key j⟩
  · have key : ∀ j : Fin 3, 3 ≤ (σ (lo j)).val := by
      intro j
      have hle : pts ρ c r cc (σ (lo j)) ≤ L2 := by
        rw [← hσ]
        exact (conjSub_mono _ (pts_le_low j)).trans hx.le
      exact three_le_of_le s.hbot hle
    have k0 : 3 ≤ (σ 0).val := key 0
    have kj := key j
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem ker_pow {x : ↥X} (hx : ∀ i, conjSub (ρ x) (pts ρ c r cc i) = pts ρ c r cc i) :
    ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  obtain ⟨n, a, ha, b, hb, hab⟩ := s.pow x
  have hz : ∀ i, conjSub (a * b) (pts ρ c r cc i) = pts ρ c r cc i := fun i => by
    rw [← hab]
    exact conjSub_pow_of_eq (hx i) _
  have ha' : ∀ j : Fin 3, conjSub a (pts ρ c r cc (lo j)) = pts ρ c r cc (lo j) := by
    intro j
    have h1 := hz (lo j)
    rw [conjSub_mul, conjSub_eq_of_comm (a := b) (D := pts ρ c r cc (lo j))
      (fun d hd => (s.comm d (pts_le_low j hd) b hb).symm)] at h1
    exact h1
  have hb' : ∀ j : Fin 3, conjSub b (pts ρ c r cc (hi j)) = pts ρ c r cc (hi j) := by
    intro j
    have h1 := hz (hi j)
    have hle : conjSub b (pts ρ c r cc (hi j)) ≤ L2 := by
      rw [← conjSub_self_of_mem hb]
      exact conjSub_mono b (pts_le_high s.hL2 j)
    rw [conjSub_mul, conjSub_eq_of_comm (a := a) (D := conjSub b (pts ρ c r cc (hi j)))
      (fun d hd => s.comm a ha d (hle hd))] at h1
    exact h1
  obtain ⟨γ, rfl⟩ := c.exists_img ha
  have hγ : γ * γ = 1 := sq_eq_one s.hker fun j => by
    have h1 := ha' j
    rw [pts_low, ← c.imgSub_conjSub, c.imgSub_inj] at h1
    exact h1
  have hb₀ : (ρ r)⁻¹ * b * ρ r ∈ Lb := by
    rw [← s.conjSub_inv_L2]
    exact (mem_conjSub).mpr (by simpa [mul_assoc] using hb)
  obtain ⟨δ, hδ⟩ := c.exists_img hb₀
  have hδ2 : δ * δ = 1 := sq_eq_one s.hker fun j => by
    have h1 := hb' j
    rw [pts_high] at h1
    have h2 : conjSub ((ρ r)⁻¹ * b * ρ r) (c.imgSub (sylOf cc j)) = c.imgSub (sylOf cc j) := by
      rw [conjSub_mul, conjSub_mul, h1, conjSub_conjSub_inv]
    rw [← hδ, ← c.imgSub_conjSub, c.imgSub_inj] at h2
    exact h2
  have hb2 : b * b = 1 := by
    have h1 : c.img δ * c.img δ = 1 := by
      rw [← c.img_mul, hδ2]
      simp [Coord.img]
    rw [hδ] at h1
    have h2 : ρ r * ((ρ r)⁻¹ * b * ρ r * ((ρ r)⁻¹ * b * ρ r)) * (ρ r)⁻¹ = b * b := by group
    rw [← h2, h1]
    group
  have ha2 : c.img γ * c.img γ = 1 := by
    rw [← c.img_mul, hγ]
    simp [Coord.img]
  have hab2 : (c.img γ * b) ^ 2 = 1 := by
    rw [sq, show c.img γ * b * (c.img γ * b) = c.img γ * c.img γ * (b * b) by
      rw [mul_assoc, ← mul_assoc b, ← s.comm _ ha b hb]
      group]
    rw [ha2, hb2, one_mul]
  have h1 : ρ (x ^ 2 ^ (n + 1)) = 1 := by
    rw [map_pow, pow_succ, pow_mul, hab, hab2]
  obtain ⟨m, hm⟩ := s.ker2 _ h1
  exact ⟨n + 1 + m, by rw [pow_add, pow_mul, hm]⟩

end SixHyp

@[expose] def stabX (hinj : Function.Injective (pts ρ c r cc)) : Subgroup G :=
  ((stabD hinj).comap ρ).map X.subtype

theorem stabX_le (hinj : Function.Injective (pts ρ c r cc)) : stabX hinj ≤ X := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_stabX (hinj : Function.Injective (pts ρ c r cc)) (x : ↥X) :
    (x : G) ∈ stabX hinj ↔ ρ x ∈ stabD hinj := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

namespace SixHyp

variable (s : SixHyp T L ρ L2 c r Q cc)
include s

theorem exists_wreath :
    ∃ H : Subgroup G, H ≤ X ∧ InH T H ∧ Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) ∧
      ∀ x : ↥X, ρ x ∈ c.imgSub Q → (x : G) ∈ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := stabX s.inj with hH
  have hHX : H ≤ X := stabX_le s.inj
  set ψ : ↥H →* MulAut V := ρ.comp (Subgroup.inclusion hHX) with hψ
  have hψS : ∀ h : ↥H, ψ h ∈ stabD s.inj := fun h =>
    (mem_stabX s.inj (Subgroup.inclusion hHX h)).mp h.2
  set act : ↥H →* Equiv.Perm (Subgroup (MulAut V)) := conjPerm.comp ψ with hact
  have hinv : ∀ (h : ↥H) (i : Fin 6), ∃ j, act h (pts ρ c r cc i) = pts ρ c r cc j :=
    fun h i => (mem_stabD s.inj).mp (hψS h) i
  set φ := permOf act (pts ρ c r cc) s.inj hinv with hφ
  have hφ_iff : ∀ (h : ↥H) (i j : Fin 6),
      φ h i = j ↔ conjSub (ψ h) (pts ρ c r cc i) = pts ρ c r cc j :=
    fun h i j => permOf_apply_eq_iff act (pts ρ c r cc) s.inj hinv h i j
  have hφ_eq : ∀ (h : ↥H) (σ : Equiv.Perm (Fin 6)),
      (∀ i, conjSub (ψ h) (pts ρ c r cc i) = pts ρ c r cc (σ i)) → φ h = σ := by
    intro h σ hσ
    ext i
    exact congrArg Fin.val ((hφ_iff h i (σ i)).mpr (hσ i))
  have hmemH : ∀ x : ↥X, ρ x ∈ c.imgSub Q → (x : G) ∈ H := fun x hx =>
    (mem_stabX s.inj x).mpr (s.mem_stabD_of_img hx)
  have hTH : T ≤ H := fun y hy => (mem_stabX s.inj ⟨y, s.TX hy⟩).mpr (s.mem_stabD_of_T hy)
  have hemb : ∀ α : Equiv.Perm (Fin 3), ∃ h : ↥H, φ h = emb₁ α := by
    intro α
    obtain ⟨γ, hγQ, hγ⟩ := exists_perm s.hperm α
    obtain ⟨x, -, hx⟩ := s.liftL (c.img γ) (c.img_mem γ)
    have hxQ : ρ x ∈ c.imgSub Q := by
      rw [hx]
      exact (c.img_mem_imgSub_iff).mpr hγQ
    exact ⟨⟨x, hmemH x hxQ⟩, hφ_eq _ _ fun i => s.conjSub_pts_of_img hx hγ i⟩
  have hr : (r : G) ∈ H := hTH s.rT
  have hrange : φ.range = wreathS3Z2 := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      rw [mem_wreathS3Z2_iff]
      exact s.blockPres (x := Subgroup.inclusion hHX h) fun i => (hφ_iff h i _).mp rfl
    · rw [wreathS3Z2, Subgroup.closure_le]
      intro σ hσ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl | rfl
      · obtain ⟨h, hh⟩ := hemb (Equiv.swap 0 1)
        exact ⟨h, hh.trans emb₁_swap⟩
      · obtain ⟨h, hh⟩ := hemb (Equiv.swap 0 1 * Equiv.swap 1 2)
        exact ⟨h, hh.trans emb₁_cyc⟩
      · have hbp : BlockPres (φ ⟨r, hr⟩) :=
          s.blockPres (x := Subgroup.inclusion hHX ⟨r, hr⟩) fun i => (hφ_iff ⟨r, hr⟩ i _).mp rfl
        have h3 : 3 ≤ (φ ⟨r, hr⟩ 0).val := by
          have hle : pts ρ c r cc (φ ⟨r, hr⟩ 0) ≤ L2 := by
            rw [← (hφ_iff ⟨r, hr⟩ 0 _).mp rfl, ← s.hL2]
            exact conjSub_mono _ (pts_le_low 0)
          exact three_le_of_le s.hbot hle
        obtain ⟨α, β, hαβ⟩ := swap_check _ hbp h3
        obtain ⟨hα, hhα⟩ := hemb α
        obtain ⟨hβ, hhβ⟩ := hemb β
        exact ⟨hβ * ⟨r, hr⟩ * hα, by rw [map_mul, map_mul, hhα, hhβ, hαβ]⟩
  have hker : IsPGroup 2 φ.ker := by
    rintro ⟨h, hh⟩
    have hfix : ∀ i, conjSub (ρ (Subgroup.inclusion hHX h)) (pts ρ c r cc i) =
        pts ρ c r cc i := fun i => (hφ_iff h i i).mp (by rw [MonoidHom.mem_ker.mp hh]; rfl)
    obtain ⟨n, hn⟩ := s.ker_pow hfix
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨H, hHX, ⟨hTH, ?_⟩, nonempty_quot_wreath φ hrange hker, hmemH⟩
  obtain ⟨x₀, -, hx₀⟩ := s.liftL (c.img zB) (c.img_mem zB)
  have hzQ : zB ∈ Q := sylOf_le s.hBQ s.hcQ 0 (s.hz 0)
  have hx₀Q : ρ x₀ ∈ c.imgSub Q := by
    rw [hx₀]
    exact (c.img_mem_imgSub_iff).mpr hzQ
  have hx₀H : (x₀ : G) ∈ H := hmemH x₀ hx₀Q
  have hx₀k : (⟨x₀, hx₀H⟩ : ↥H) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ_eq ⟨x₀, hx₀H⟩ (emb₁ 1) (s.conjSub_pts_of_img hx₀ fun i => by
      rw [Equiv.Perm.one_apply]
      exact conjSub_self_of_mem (s.hz i)), emb₁_one]
  have hcore : (⟨x₀, hx₀H⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
    have hle : φ.ker ≤ CFSG.pCore 2 ↥H := le_sSup ⟨MonoidHom.normal_ker φ, hker⟩
    exact hle hx₀k
  intro hbot
  have hmem : (x₀ : G) ∈ CFSG.Open.pCoreOf 2 H := ⟨⟨x₀, hx₀H⟩, hcore, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : x₀ = 1 := Subtype.ext hmem
  rw [h1, map_one] at hx₀
  exact zB_ne_one (c.img_injective (hx₀.symm.trans (by simp [Coord.img])))

end SixHyp

end Hyp

end CFSG.Quasithin.H13.Ins314

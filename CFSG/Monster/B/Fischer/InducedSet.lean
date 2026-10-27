module

public import CFSG.Monster.B.Fischer.HexadAffine
public import CFSG.Monster.B.Fischer.InducedData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem hexTable3_size {n k₀ : ℕ} {s : String} : (hexTable3 n k₀ s).size = n := by
  simp [hexTable3]

theorem rhoW_inv_apply
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀) :
    rhoW k⁻¹ (rhoW k w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rhoW_apply_inv
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀) :
    rhoW k (rhoW k⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[expose] noncomputable def wMulAut
    (k : CFSG.Blueprint.NativeSporadic.M22) :
    MulAut (Multiplicative W₀) where
  toFun w := Multiplicative.ofAdd (rhoW k (Multiplicative.toAdd w))
  invFun w := Multiplicative.ofAdd (rhoW k⁻¹ (Multiplicative.toAdd w))
  left_inv w := by simp
  right_inv w := by simp
  map_mul' w w' := by simp [map_add]

@[expose] noncomputable def wAut :
    CFSG.Blueprint.NativeSporadic.M22 →* MulAut (Multiplicative W₀)
    where
  toFun := wMulAut
  map_one' := MulEquiv.ext fun w => by simp [wMulAut]
  map_mul' k l := MulEquiv.ext fun w => by simp [wMulAut, map_mul]

abbrev F₀ :
    Type := SemidirectProduct (Multiplicative W₀) CFSG.Blueprint.NativeSporadic.M22 wAut

@[expose] def zRel
    (p p' : CFSG.Blueprint.NativeSporadic.M22 × Q₀) : Prop :=
  ∃ h : KB, p.1 = p'.1 * h ∧ p'.2 = affA h p.2

@[expose] def Z :
    Type := Quot zRel

@[expose] def zMk
    (k : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) : Z := Quot.mk _ (k, q)

theorem zMk_mul
    (k : CFSG.Blueprint.NativeSporadic.M22) (h : KB) (q : Q₀) :
    zMk (k * h) q = zMk k (affA h q) :=
  Quot.sound ⟨h, rfl, rfl⟩

theorem zMk_surj
    (z : Z) : ∃ k q, zMk k q = z := by
  obtain ⟨⟨k, q⟩, rfl⟩ := Quot.exists_rep z
  exact ⟨k, q, rfl⟩

@[expose] def zK
    (k : CFSG.Blueprint.NativeSporadic.M22) : Z → Z :=
  Quot.lift (fun p => zMk (k * p.1) p.2) (by
    rintro ⟨l, q⟩ ⟨l', q'⟩ ⟨h, h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    rw [← mul_assoc]
    exact zMk_mul _ _ _)

theorem zK_mk
    (k l : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) :
    zK k (zMk l q) = zMk (k * l) q := rfl

theorem rhoQ_mkQ
    (h : KB) (w : W₀) : rhoQ h (U₀.mkQ w) = U₀.mkQ (rhoW h w) := rfl

@[expose] noncomputable def zW
    (r : W₀) : Z → Z :=
  Quot.lift (fun p => zMk p.1 (p.2 + U₀.mkQ (rhoW p.1⁻¹ r))) (by
    rintro ⟨l, q⟩ ⟨l', q'⟩ ⟨h, h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    show zMk (l' * ↑h) (q + U₀.mkQ (rhoW (l' * ↑h)⁻¹ r)) =
      zMk l' (affA h q + U₀.mkQ (rhoW l'⁻¹ r))
    rw [zMk_mul, isAffineAction_affA, rhoQ_mkQ, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
      mul_inv_cancel_left])

theorem zW_mk
    (r : W₀) (l : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) :
    zW r (zMk l q) = zMk l (q + U₀.mkQ (rhoW l⁻¹ r)) := rfl

@[expose] def hexadOf :
    Z → Finset (Fin 24) :=
  Quot.lift (fun p => B₀.map (psiHom p.1).toEmbedding) (by
    rintro ⟨l, q⟩ ⟨l', q'⟩ ⟨h, h1, h2⟩
    simp only at h1 h2 ⊢
    subst h1
    rw [Subgroup.coe_mul, map_mul, map_perm_mul, (mem_KB.1 h.2)])

theorem hexadOf_mk
    (k : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) :
    hexadOf (zMk k q) = B₀.map (psiHom k).toEmbedding := rfl

abbrev Y :
    Type := X₀ ⊕ W₀ ⊕ Z

@[expose] noncomputable def o :
    Y := .inr (.inl 0)

@[expose] noncomputable def kAct
    (k : CFSG.Blueprint.NativeSporadic.M22) : Y → Y
  | .inl x => .inl (psiX k x)
  | .inr (.inl u) => .inr (.inl (rhoW k u))
  | .inr (.inr z) => .inr (.inr (zK k z))

@[expose] noncomputable def wAct
    (r : W₀) : Y → Y
  | .inl x => .inl x
  | .inr (.inl u) => .inr (.inl (r + u))
  | .inr (.inr z) => .inr (.inr (zW r z))

theorem zK_one
    (z : Z) : zK 1 z = z := by
  obtain ⟨k, q, rfl⟩ := zMk_surj z
  rw [zK_mk, one_mul]

theorem zK_mul
    (k l : CFSG.Blueprint.NativeSporadic.M22) (z : Z) :
    zK (k * l) z = zK k (zK l z) := by
  obtain ⟨m, q, rfl⟩ := zMk_surj z
  rw [zK_mk, zK_mk, zK_mk, mul_assoc]

theorem zW_zero
    (z : Z) : zW 0 z = z := by
  obtain ⟨k, q, rfl⟩ := zMk_surj z
  rw [zW_mk, map_zero, map_zero, add_zero]

theorem zW_add
    (r r' : W₀) (z : Z) : zW (r + r') z = zW r (zW r' z) := by
  obtain ⟨k, q, rfl⟩ := zMk_surj z
  rw [zW_mk, zW_mk, zW_mk, map_add, map_add, add_comm (U₀.mkQ _), add_assoc]

theorem zK_zW
    (k : CFSG.Blueprint.NativeSporadic.M22) (r : W₀) (z : Z) :
    zK k (zW r z) = zW (rhoW k r) (zK k z) := by
  obtain ⟨l, q, rfl⟩ := zMk_surj z
  rw [zW_mk, zK_mk, zK_mk, zW_mk, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    inv_mul_cancel_right]

theorem kAct_one
    (y : Y) : kAct 1 y = y := by
  rcases y with x | u | z
  · simp [kAct]
  · simp [kAct]
  · simp [kAct, zK_one]

theorem kAct_mul
    (k l : CFSG.Blueprint.NativeSporadic.M22) (y : Y) :
    kAct (k * l) y = kAct k (kAct l y) := by
  rcases y with x | u | z
  · simp [kAct, map_mul]
  · simp [kAct, map_mul]
  · simp [kAct, zK_mul]

theorem wAct_zero
    (y : Y) : wAct 0 y = y := by
  rcases y with x | u | z
  · simp [wAct]
  · simp [wAct]
  · simp [wAct, zW_zero]

theorem wAct_add
    (r r' : W₀) (y : Y) : wAct (r + r') y = wAct r (wAct r' y) := by
  rcases y with x | u | z
  · simp [wAct]
  · simp [wAct, add_assoc]
  · simp [wAct, zW_add]

theorem kAct_wAct
    (k : CFSG.Blueprint.NativeSporadic.M22) (r : W₀) (y : Y) :
    kAct k (wAct r y) = wAct (rhoW k r) (kAct k y) := by
  rcases y with x | u | z
  · simp [kAct, wAct]
  · simp [kAct, wAct, map_add]
  · simp [kAct, wAct, zK_zW]

noncomputable instance instMulActionF₀Y :
    MulAction F₀ Y where
  smul f y := wAct (Multiplicative.toAdd f.left) (kAct f.right y)
  one_smul y := by
    change wAct (Multiplicative.toAdd 1) (kAct 1 y) = y
    rw [kAct_one, toAdd_one, wAct_zero]
  mul_smul f g y := by
    change wAct (Multiplicative.toAdd (f * g).left) (kAct (f * g).right y) =
      wAct (Multiplicative.toAdd f.left) (kAct f.right
        (wAct (Multiplicative.toAdd g.left) (kAct g.right y)))
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, kAct_mul, kAct_wAct, toAdd_mul,
      wAct_add]
    rfl

theorem smul_def
    (f : F₀) (y : Y) :
    f • y = wAct (Multiplicative.toAdd f.left) (kAct f.right y) := rfl

@[expose] noncomputable def kF
    (k : CFSG.Blueprint.NativeSporadic.M22) : F₀ :=
  SemidirectProduct.inr k

@[expose] noncomputable def wF
    (r : W₀) : F₀ := SemidirectProduct.inl (Multiplicative.ofAdd r)

theorem smul_mk
    (k l : CFSG.Blueprint.NativeSporadic.M22) (r u : W₀) (x : X₀) (q : Q₀) :
    kF k • (.inl x : Y) = .inl (psiX k x) ∧ kF k • (.inr (.inl u) : Y) = .inr (.inl (rhoW k u)) ∧
    kF k • (.inr (.inr (zMk l q)) : Y) = .inr (.inr (zMk (k * l) q)) ∧
    wF r • (.inl x : Y) = .inl x ∧ wF r • (.inr (.inl u) : Y) = .inr (.inl (r + u)) ∧
    wF r • (.inr (.inr (zMk l q)) : Y) = .inr (.inr (zMk l (q + U₀.mkQ (rhoW l⁻¹ r)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [smul_def, kF, wF, kAct, wAct, zK_mk, zW_mk]

theorem Fischer_induced_Mathieu_permutation_data :
    (∀ (k : CFSG.Blueprint.NativeSporadic.M22) (h : KB) (q : Q₀),
      zMk (k * h) q = zMk k (affA h q)) ∧
    (∀ (k l : CFSG.Blueprint.NativeSporadic.M22) (r u : W₀) (x : X₀) (q : Q₀),
      kF k • (.inl x : Y) = .inl (psiX k x) ∧ kF k • (.inr (.inl u) : Y) = .inr (.inl (rhoW k u)) ∧
      kF k • (.inr (.inr (zMk l q)) : Y) = .inr (.inr (zMk (k * l) q)) ∧
      wF r • (.inl x : Y) = .inl x ∧ wF r • (.inr (.inl u) : Y) = .inr (.inl (r + u)) ∧
      wF r • (.inr (.inr (zMk l q)) : Y) = .inr (.inr (zMk l (q + U₀.mkQ (rhoW l⁻¹ r))))) ∧
    (∀ (k : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀),
      hexadOf (zMk k q) = B₀.map (psiHom k).toEmbedding) ∧
    o = .inr (.inl 0) ∧
    (∀ k < 13, (indCandidate k).size = 3510) ∧ pinXiRaw.size = 3510 ∧
    pinMembership.length = 13 := by
  refine ⟨zMk_mul, smul_mk, hexadOf_mk, rfl, fun k _ => ?_, hexTable3_size, rfl⟩
  unfold indCandidate
  split_ifs <;> exact hexTable3_size

end CFSG.Monster.B.Fischer

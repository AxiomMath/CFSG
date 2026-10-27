
module

public import CFSG.Sporadic.Co1.Module.OddCentCardBase
public import CFSG.Certificates.Kernel.TreeKSound

public section

namespace CFSG.Sporadic.Co1.Module.TwoBFrame

open Equiv

theorem perm_eq_of_sym2 {α : Type*} (three : ∀ i : α, ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k)
    {ρ ρ' : Perm α} (h : ∀ i j, i ≠ j → s(ρ i, ρ j) = s(ρ' i, ρ' j)) : ρ = ρ' := by
  ext i
  obtain ⟨j, k, hj, hk, hjk⟩ := three i
  have e1 := Sym2.eq_iff.1 (h i j (Ne.symm hj))
  have e2 := Sym2.eq_iff.1 (h i k (Ne.symm hk))
  rcases e1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  rcases e2 with ⟨h2, -⟩ | ⟨h2, -⟩
  · exact h2
  exact absurd (ρ'.injective (h1.symm.trans h2)) hjk

theorem three_fin24 : ∀ i : Fin 24, ∃ j k : Fin 24, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  intro i
  have hi := i.isLt
  refine ⟨⟨(i.val + 1) % 24, Nat.mod_lt _ (by norm_num)⟩, ⟨(i.val + 2) % 24, Nat.mod_lt _ (by norm_num)⟩,
    ?_, ?_, ?_⟩
  all_goals
    rw [ne_eq, Fin.ext_iff]
    dsimp only
    omega

structure Frame (G V α : Type*) [Group G] [AddCommGroup V] where
  act : G → V → V
  act_mul : ∀ g h v, act (g * h) v = act g (act h v)
  act_one : ∀ v, act 1 v = v
  act_add : ∀ g v w, act g (v + w) = act g v + act g w
  ω : V
  ω_add : ω + ω = 0
  a : α → α → V
  three : ∀ i : α, ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k
  dist : ∀ i j k l, i ≠ j → k ≠ l → (a i j = a k l ∨ a i j = a k l + ω) → s(i, j) = s(k, l)

namespace Frame

variable {G V α : Type*} [Group G] [AddCommGroup V] (F : Frame G V α)

@[expose] def Cl (v w : V) : Prop := v = w ∨ v = w + F.ω

@[expose] def Ind (x : G) (ρ : Perm α) : Prop :=
  F.act x F.ω = F.ω ∧ ∀ i j, i ≠ j → F.Cl (F.act x (F.a i j)) (F.a (ρ i) (ρ j))

variable {F}

theorem cl_refl (v : V) : F.Cl v v := Or.inl rfl

theorem cl_symm {v w : V} (h : F.Cl v w) : F.Cl w v := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [add_assoc, F.ω_add, add_zero]

theorem cl_trans {u v w : V} (h1 : F.Cl u v) (h2 : F.Cl v w) : F.Cl u w := by
  rcases h1 with rfl | rfl
  · exact h2
  rcases h2 with rfl | rfl
  · exact Or.inr rfl
  · left
    rw [add_assoc, F.ω_add, add_zero]

theorem act_cl {x : G} (hx : F.act x F.ω = F.ω) {v w : V} (h : F.Cl v w) :
    F.Cl (F.act x v) (F.act x w) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [F.act_add, hx]

theorem act_inv_act (x : G) (v : V) : F.act x⁻¹ (F.act x v) = v := by
  rw [← F.act_mul, inv_mul_cancel, F.act_one]

theorem Ind.fix {x : G} {ρ : Perm α} (h : F.Ind x ρ) : F.act x F.ω = F.ω := h.1

theorem ind_one : F.Ind 1 1 :=
  ⟨F.act_one _, fun i j _ => by rw [F.act_one]; exact cl_refl _⟩

theorem ind_mul {x y : G} {ρ σ : Perm α} (hx : F.Ind x ρ) (hy : F.Ind y σ) :
    F.Ind (x * y) (ρ * σ) := by
  refine ⟨by rw [F.act_mul, hy.1, hx.1], fun i j hij => ?_⟩
  rw [F.act_mul, Perm.mul_apply, Perm.mul_apply]
  exact cl_trans (act_cl hx.1 (hy.2 i j hij)) (hx.2 _ _ (σ.injective.ne hij))

theorem ind_inv {x : G} {ρ : Perm α} (hx : F.Ind x ρ) : F.Ind x⁻¹ ρ⁻¹ := by
  have hfix : F.act x⁻¹ F.ω = F.ω := by
    conv_lhs => rw [← hx.1]
    exact act_inv_act x F.ω
  refine ⟨hfix, fun i j hij => ?_⟩
  have h := hx.2 (ρ⁻¹ i) (ρ⁻¹ j) (ρ⁻¹.injective.ne hij)
  have e1 : ∀ y, ρ (ρ⁻¹ y) = y := fun y => ρ.apply_symm_apply y
  rw [e1, e1] at h
  have h' := act_cl hfix h
  rw [act_inv_act] at h'
  exact cl_symm h'

theorem ind_conj {x s : G} {ρ σ : Perm α} (hx : F.Ind x ρ) (hs : F.Ind s σ) :
    F.Ind (x * s * x⁻¹) (ρ * σ * ρ⁻¹) :=
  ind_mul (ind_mul hx hs) (ind_inv hx)

theorem ind_unique {x : G} {ρ ρ' : Perm α} (h : F.Ind x ρ) (h' : F.Ind x ρ') : ρ = ρ' := by
  refine perm_eq_of_sym2 F.three fun i j hij => ?_
  have hc := cl_trans (cl_symm (h.2 i j hij)) (h'.2 i j hij)
  exact F.dist _ _ _ _ (ρ.injective.ne hij) (ρ'.injective.ne hij) hc

@[expose] def indSub (F : Frame G V α) : Subgroup (Perm α) where
  carrier := {ρ | ∃ x, F.Ind x ρ}
  mul_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, ind_mul hx hy⟩
  one_mem' := ⟨1, ind_one⟩
  inv_mem' := fun ⟨x, hx⟩ => ⟨x⁻¹, ind_inv hx⟩

theorem mem_indSub {ρ : Perm α} : ρ ∈ F.indSub ↔ ∃ x, F.Ind x ρ := Iff.rfl

theorem conj_perm_eq {Y Y' z z' : G} {π π' σ : Perm α} (hY : F.Ind Y π) (hY' : F.Ind Y' π')
    (hz : F.Ind z σ) (hz' : F.Ind z' σ) (e : Y * z * Y⁻¹ = Y' * z' * Y'⁻¹) :
    π * σ * π⁻¹ = π' * σ * π'⁻¹ := by
  have h1 := ind_conj hY hz
  rw [e] at h1
  exact ind_unique h1 (ind_conj hY' hz')

theorem decode_inj {B C i i' : ℕ} (h1 : i / C / B = i' / C / B) (h2 : i / C % B = i' / C % B)
    (h3 : i % C = i' % C) : i = i' := by
  have e : i / C = i' / C := by
    rw [← Nat.div_add_mod (i / C) B, ← Nat.div_add_mod (i' / C) B, h1, h2]
  rw [← Nat.div_add_mod i C, ← Nat.div_add_mod i' C, e, h3]

theorem decode_lt {A B C i : ℕ} (hi : i < A * B * C) :
    i / C / B < A ∧ i / C % B < B ∧ i % C < C := by
  have hC : 0 < C := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hB : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  refine ⟨Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul (hi.trans_eq (by ring))), Nat.mod_lt _ hB,
    Nat.mod_lt _ hC⟩

theorem exists_frame_family {s : G} {σ : Perm α} (hs : F.Ind s σ) (p q : α) {A B C : ℕ}
    (ρc : ℕ → Perm α) (hρc : ∀ c < A, ρc c ∈ F.indSub) (hρp : ∀ c < A, ρc c p = p)
    (hρq : ∀ c < A, ∀ c' < A, ρc c q = ρc c' q → c = c')
    (κ : ℕ → Perm α) (hκ : ∀ j < B, κ j ∈ F.indSub) (hκq : ∀ j < B, (κ j * σ * (κ j)⁻¹) p = q)
    (hκinj : ∀ j < B, ∀ j' < B, κ j * σ * (κ j)⁻¹ = κ j' * σ * (κ j')⁻¹ → j = j')
    (e : ℕ → G) (he : ∀ k < C, F.Ind (e k) 1)
    (heinj : ∀ k < C, ∀ k' < C, e k * s * (e k)⁻¹ = e k' * s * (e k')⁻¹ → k = k') :
    ∃ f : ℕ → G, (∀ i < A * B * C, ∃ x, F.act x F.ω = F.ω ∧ f i = x * s * x⁻¹) ∧
      ∀ i < A * B * C, ∀ i' < A * B * C, f i = f i' → i = i' := by
  have hG : Nonempty G := ⟨1⟩
  choose! gc hgc using hρc
  choose! hk hhk using hκ
  let X : ℕ → G := fun i => gc (i / C / B) * hk (i / C % B) * e (i % C)
  have hX : ∀ i < A * B * C, F.Ind (X i) (ρc (i / C / B) * κ (i / C % B) * 1) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := decode_lt hi
    exact ind_mul (ind_mul (hgc _ h1) (hhk _ h2)) (he _ h3)
  refine ⟨fun i => X i * s * (X i)⁻¹, fun i hi => ⟨X i, (hX i hi).fix, rfl⟩, ?_⟩
  intro i hi i' hi' heq
  obtain ⟨h1, h2, h3⟩ := decode_lt hi
  obtain ⟨h1', h2', h3'⟩ := decode_lt hi'
  have hp := conj_perm_eq (hX i hi) (hX i' hi') hs hs heq
  have hr : ∀ (ρ κ' : Perm α), ρ * κ' * 1 * σ * (ρ * κ' * 1)⁻¹ = ρ * (κ' * σ * κ'⁻¹) * ρ⁻¹ := by
    intro ρ κ'
    group
  rw [hr, hr] at hp
  have hpinv : ∀ c < A, (ρc c)⁻¹ p = p := fun c hc => by
    rw [Perm.inv_eq_iff_eq, hρp c hc]
  have hap : ∀ ρ T : Perm α, ρ⁻¹ p = p → (ρ * T * ρ⁻¹) p = ρ (T p) := by
    intro ρ T h
    rw [Perm.mul_apply, Perm.mul_apply, h]
  have hev := congrArg (fun π : Perm α => π p) hp
  rw [hap _ _ (hpinv _ h1), hap _ _ (hpinv _ h1'), hκq _ h2, hκq _ h2'] at hev
  have ec := hρq _ h1 _ h1' hev
  rw [ec] at hp
  have ej := hκinj _ h2 _ h2' (mul_left_cancel (mul_right_cancel hp))
  have hY : gc (i / C / B) * hk (i / C % B) = gc (i' / C / B) * hk (i' / C % B) := by rw [ec, ej]
  have heq' : (gc (i / C / B) * hk (i / C % B)) * (e (i % C) * s * (e (i % C))⁻¹) *
      (gc (i / C / B) * hk (i / C % B))⁻¹ =
      (gc (i / C / B) * hk (i / C % B)) * (e (i' % C) * s * (e (i' % C))⁻¹) *
      (gc (i / C / B) * hk (i / C % B))⁻¹ := by
    have e1 : X i * s * (X i)⁻¹ = (gc (i / C / B) * hk (i / C % B)) *
        (e (i % C) * s * (e (i % C))⁻¹) * (gc (i / C / B) * hk (i / C % B))⁻¹ := by
      simp only [X]
      group
    have e2 : X i' * s * (X i')⁻¹ = (gc (i' / C / B) * hk (i' / C % B)) *
        (e (i' % C) * s * (e (i' % C))⁻¹) * (gc (i' / C / B) * hk (i' / C % B))⁻¹ := by
      simp only [X]
      group
    have heq2 : X i * s * (X i)⁻¹ = X i' * s * (X i')⁻¹ := heq
    rw [← e1, heq2, e2, ← hY]
  have ek := heinj _ h3 _ h3' (mul_left_cancel (mul_right_cancel heq'))
  exact decode_inj ec ej ek

end Frame

section Co1

open CFSG.Blueprint CFSG.Sporadic.Co1.Module

@[expose] noncomputable def co1Frame (ω : Vec24) (a : Fin 24 → Fin 24 → Vec24)
    (dist : ∀ i j k l, i ≠ j → k ≠ l → (a i j = a k l ∨ a i j = a k l + ω) → s(i, j) = s(k, l)) :
    Frame NativeSporadic.Co1 Vec24 (Fin 24) where
  act := co1Act
  act_mul := co1Act_mul
  act_one := co1Act_one
  act_add g v w := by
    simp only [co1Act_eq_mulVec]
    exact Matrix.mulVec_add _ _ _
  ω := ω
  ω_add := funext fun i => CharTwo.add_self_eq_zero (ω i)
  a := a
  three := three_fin24
  dist := dist

theorem frame_card_bound (F : Frame NativeSporadic.Co1 Vec24 (Fin 24))
    (hF : F.act = co1Act) {N Fb : ℕ}
    (hN : (Set.range fun g : NativeSporadic.Co1 => co1Act g F.ω).ncard = N)
    {s : NativeSporadic.Co1} {σ : Perm (Fin 24)} (hs : F.Ind s σ) (p q : Fin 24) {A B C : ℕ}
    (ρc : ℕ → Perm (Fin 24)) (hρc : ∀ c < A, ρc c ∈ F.indSub) (hρp : ∀ c < A, ρc c p = p)
    (hρq : ∀ c < A, ∀ c' < A, ρc c q = ρc c' q → c = c')
    (κ : ℕ → Perm (Fin 24)) (hκ : ∀ j < B, κ j ∈ F.indSub)
    (hκq : ∀ j < B, (κ j * σ * (κ j)⁻¹) p = q)
    (hκinj : ∀ j < B, ∀ j' < B, κ j * σ * (κ j)⁻¹ = κ j' * σ * (κ j')⁻¹ → j = j')
    (e : ℕ → NativeSporadic.Co1) (he : ∀ k < C, F.Ind (e k) 1)
    (heinj : ∀ k < C, ∀ k' < C, e k * s * (e k)⁻¹ = e k' * s * (e k')⁻¹ → k = k')
    (hFb : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g F.ω) | co1Act s w = w}.ncard ≤ Fb) :
    Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) * (A * B * C) * N ≤
      Nat.card NativeSporadic.Co1 * Fb := by
  obtain ⟨f, hf, hfinj⟩ := Frame.exists_frame_family hs p q ρc hρc hρp hρq κ hκ hκq hκinj e he
    heinj
  have hs' : co1Act s F.ω = F.ω := by
    rw [← hF]
    exact hs.fix
  refine card_centralizer_bound hN hs' f hfinj (fun i hi => ?_) hFb
  obtain ⟨x, hx, hfx⟩ := hf i hi
  exact ⟨x, by rw [← hF]; exact hx, hfx⟩

end Co1

section Trees

open CFSG.KC.TreeK

variable {G β : Type*} [Group G]

theorem reach_op (C : Subgroup G) (op : G → β → β) (hop : ∀ g h b, op (g * h) b = op g (op h b))
    (hone : ∀ b, op 1 b = b) {act : ℕ → ℕ → ℕ} {ng root : ℕ} (enc : ℕ → β) (gen : ℕ → G)
    (hgen : ∀ l < ng, gen l ∈ C) (P : ℕ → Prop) (hP0 : P root)
    (hPs : ∀ l < ng, ∀ y, P y → P (act l y))
    (hact : ∀ l < ng, ∀ y, P y → enc (act l y) = op (gen l) (enc y)) {x : ℕ}
    (hx : Reach act ng root x) : P x ∧ ∃ g ∈ C, enc x = op g (enc root) := by
  induction hx with
  | root => exact ⟨hP0, 1, C.one_mem, (hone _).symm⟩
  | step l hl _ ih =>
    obtain ⟨hPx, g, hg, hgx⟩ := ih
    refine ⟨hPs l hl _ hPx, gen l * g, C.mul_mem (hgen l hl) hg, ?_⟩
    rw [hact l hl _ hPx, hgx, hop]

theorem exists_tree_family (C : Subgroup G) (op : G → β → β)
    (hop : ∀ g h b, op (g * h) b = op g (op h b)) (hone : ∀ b, op 1 b = b) {act : ℕ → ℕ → ℕ}
    {ng root : ℕ} (enc : ℕ → β) (gen : ℕ → G) (hgen : ∀ l < ng, gen l ∈ C) (P : ℕ → Prop)
    (hP0 : P root) (hPs : ∀ l < ng, ∀ y, P y → P (act l y))
    (hact : ∀ l < ng, ∀ y, P y → enc (act l y) = op (gen l) (enc y))
    (hinj : ∀ x y, P x → P y → enc x = enc y → x = y) {xs : List ℕ} (hnd : xs.Nodup)
    (hreach : ∀ x ∈ xs, Reach act ng root x) :
    ∃ t : ℕ → G, (∀ i < xs.length, t i ∈ C ∧ enc (xs.getD i 0) = op (t i) (enc root)) ∧
      ∀ i < xs.length, ∀ j < xs.length, op (t i) (enc root) = op (t j) (enc root) → i = j := by
  have hG : Nonempty G := ⟨1⟩
  have key : ∀ i, i < xs.length → P (xs.getD i 0) ∧
      ∃ g, g ∈ C ∧ enc (xs.getD i 0) = op g (enc root) := by
    intro i hi
    obtain ⟨hP, g, hg, hgx⟩ := reach_op C op hop hone enc gen hgen P hP0 hPs hact
      (hreach (xs.getD i 0) (by rw [List.getD_eq_getElem xs 0 hi]; exact List.getElem_mem hi))
    exact ⟨hP, g, hg, hgx⟩
  choose! t ht using fun i hi => (key i hi).2
  refine ⟨t, ht, fun i hi j hj e => ?_⟩
  have hxy := hinj (xs.getD i 0) (xs.getD j 0) (key i hi).1 (key j hj).1
    (by rw [(ht i hi).2, (ht j hj).2, e])
  rw [List.getD_eq_getElem xs 0 hi, List.getD_eq_getElem xs 0 hj] at hxy
  exact (hnd.getElem_inj_iff).1 hxy

end Trees

section UniTri

open Matrix

variable {n : ℕ}

@[expose] def UniTri (U : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  (∀ i j : Fin n, j < i → U i j = 0) ∧ ∀ i : Fin n, U i i = 1

theorem uniTri_one : UniTri (1 : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨fun _ _ h => Matrix.one_apply_ne (ne_of_lt h).symm, fun i => Matrix.one_apply_eq i⟩

theorem uniTri_mul {U W : Matrix (Fin n) (Fin n) (ZMod 2)} (hU : UniTri U) (hW : UniTri W) :
    UniTri (U * W) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hki | hik
    · rw [hU.1 i k hki, zero_mul]
    · rw [hW.1 k j (lt_of_lt_of_le hji hik), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hU.2, hW.2, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hU.1 i k h, zero_mul]
      · rw [hW.1 k i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem strict_pow_apply {N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : ∀ i j : Fin n, j ≤ i → N i j = 0)
    (m : ℕ) : ∀ i j : Fin n, j.val < i.val + m → (N ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j h
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun e => by rw [e] at h; omega)
  | succ m ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val < i.val + m
    · rw [ih i k hk, zero_mul]
    · rw [hN k j (by rw [Fin.le_def]; omega), mul_zero]

theorem mat_add_self (M : Matrix (Fin n) (Fin n) (ZMod 2)) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

theorem one_add_pow_two_pow (N : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) :
    (1 + N) ^ 2 ^ k = 1 + N ^ 2 ^ k := by
  have hsq : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), (1 + M) ^ 2 = 1 + M ^ 2 := by
    intro M
    have e : (1 + M) ^ 2 = 1 + M ^ 2 + (M + M) := by noncomm_ring
    rw [e, mat_add_self, add_zero]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hsq, ← pow_mul]

theorem uniTri_pow_two_pow {U : Matrix (Fin n) (Fin n) (ZMod 2)} (hU : UniTri U) {k : ℕ}
    (hk : n ≤ 2 ^ k) : U ^ 2 ^ k = 1 := by
  have hN : ∀ i j : Fin n, j ≤ i → (U - 1) i j = 0 := by
    intro i j hji
    rw [Matrix.sub_apply]
    rcases lt_or_eq_of_le hji with h | h
    · rw [hU.1 i j h, Matrix.one_apply_ne (ne_of_lt h).symm]
      rfl
    · rw [h, hU.2, Matrix.one_apply_eq, sub_self]
  have h0 : (U - 1) ^ 2 ^ k = 0 := by
    ext i j
    have hj := j.isLt
    rw [strict_pow_apply hN (2 ^ k) i j (by omega), Matrix.zero_apply]
  have e : U = 1 + (U - 1) := by abel
  rw [e, one_add_pow_two_pow, h0, add_zero]

variable {G : Type*} [Group G]

theorem pow_two_pow_eq_one_of_closure (φ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hφ : Function.Injective φ) (Q Qi : Matrix (Fin n) (Fin n) (ZMod 2)) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (gens : Set G) (hgens : ∀ g ∈ gens, UniTri (Q * φ g * Qi)) {k : ℕ}
    (hk : n ≤ 2 ^ k) : ∀ x ∈ Subgroup.closure gens, x ^ 2 ^ k = 1 := by
  have hmul : ∀ x y : G, UniTri (Q * φ x * Qi) → UniTri (Q * φ y * Qi) →
      UniTri (Q * φ (x * y) * Qi) := by
    intro x y hx hy
    have e : Q * φ (x * y) * Qi = (Q * φ x * Qi) * (Q * φ y * Qi) := by
      rw [map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc Qi Q, hQ, one_mul]
    rw [e]
    exact uniTri_mul hx hy
  have hpow : ∀ x : G, UniTri (Q * φ x * Qi) → ∀ m : ℕ, UniTri (Q * φ (x ^ m) * Qi) := by
    intro x hx m
    induction m with
    | zero =>
      rw [pow_zero, map_one, mul_one, hQ']
      exact uniTri_one
    | succ m ih =>
      rw [pow_succ]
      exact hmul _ _ ih hx
  have hord : ∀ x : G, UniTri (Q * φ x * Qi) → x ^ 2 ^ k = 1 := by
    intro x hx
    apply hφ
    have h1 := uniTri_pow_two_pow (hpow x hx 1) hk
    rw [pow_one] at h1
    have h2 : (Q * φ x * Qi) ^ 2 ^ k = Q * φ (x ^ 2 ^ k) * Qi := by
      rw [map_pow]
      generalize 2 ^ k = m
      induction m with
      | zero => rw [pow_zero, pow_zero, mul_one, hQ']
      | succ m ih =>
        rw [pow_succ (Q * φ x * Qi), ih, pow_succ (φ x)]
        simp only [mul_assoc]
        rw [← mul_assoc Qi Q, hQ, one_mul]
    rw [h2] at h1
    calc φ (x ^ 2 ^ k) = Qi * (Q * φ (x ^ 2 ^ k) * Qi) * Q := by
          simp only [mul_assoc]
          rw [← mul_assoc Qi Q, hQ, one_mul, mul_one]
      _ = φ 1 := by rw [h1, mul_one, hQ, map_one]
  have hinv : ∀ x : G, UniTri (Q * φ x * Qi) → UniTri (Q * φ x⁻¹ * Qi) := by
    intro x hx
    have e : x⁻¹ = x ^ (2 ^ k - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, hord x hx]
    rw [e]
    exact hpow x hx _
  intro x hx
  refine hord x ?_
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hgens y hy
  | one =>
    rw [map_one, mul_one, hQ']
    exact uniTri_one
  | mul y z _ _ hy hz => exact hmul y z hy hz
  | inv y _ hy => exact hinv y hy

theorem card_closure_two_pow [Finite G] (φ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hφ : Function.Injective φ) (Q Qi : Matrix (Fin n) (Fin n) (ZMod 2)) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (gens : Set G) (hgens : ∀ g ∈ gens, UniTri (Q * φ g * Qi)) :
    ∃ m : ℕ, Nat.card (Subgroup.closure gens) = 2 ^ m := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.iff_card.1 fun y => ⟨n, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_two_pow_eq_one_of_closure φ hφ Q Qi hQ hQ' gens hgens
    (Nat.lt_two_pow_self).le y.1 y.2

theorem two_pow_dvd_of_le {m a c : ℕ} (hc : c = 2 ^ m) (h : 2 ^ a ≤ c) : 2 ^ a ∣ c := by
  rw [hc] at h ⊢
  exact Nat.pow_dvd_pow 2 ((pow_le_pow_iff_right₀ (by norm_num)).1 h)

theorem eq_two_pow_of_dvd {m a r c : ℕ} (hc : c = 2 ^ m) (h : 2 ^ a ≤ c) (hr : Odd r)
    (hd : c ∣ 2 ^ a * r) : c = 2 ^ a := by
  rw [hc] at h hd ⊢
  have hcop : Nat.Coprime (2 ^ m) r := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hr)
  have h1 : 2 ^ m ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hd
  have h2 : m ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have h3 : a ≤ m := (pow_le_pow_iff_right₀ (by norm_num)).1 h
  rw [le_antisymm h2 h3]

end UniTri

section Orbits

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]

theorem card_mul_le_of_orbit_stab (C : Subgroup G) (ω : Ω) {n m : ℕ} (t u : ℕ → G)
    (ht : ∀ i < n, t i ∈ C) (hdist : ∀ i < n, ∀ j < n, t i • ω = t j • ω → i = j)
    (hu : ∀ j < m, u j ∈ C ∧ u j • ω = ω) (huinj : ∀ i < m, ∀ j < m, u i = u j → i = j) :
    n * m ≤ Nat.card ↥C := by
  have h1 := CFSG.Sporadic.Co1.Module.Odd.card_mul_card_stab_le C ω n t ht hdist
  have h2 : m ≤ Nat.card ↥(MulAction.stabilizer G ω ⊓ C) := by
    let f : Fin m → ↥(MulAction.stabilizer G ω ⊓ C) := fun j =>
      ⟨u j, Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 (hu j j.2).2, (hu j j.2).1⟩⟩
    have hf : Function.Injective f := fun i j e =>
      Fin.ext (huinj i i.2 j j.2 (congrArg Subtype.val e))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  exact (Nat.mul_le_mul_left n h2).trans h1

theorem card_inf_conj_le (S : Subgroup G) (ω : Ω) (hS : ∀ x ∈ S, x • ω = ω) (g : G) {n : ℕ}
    (t : ℕ → G) (ht : ∀ i < n, t i ∈ S)
    (hdist : ∀ i < n, ∀ j < n, t i • (g • ω) = t j • (g • ω) → i = j) :
    n * Nat.card ↥(S ⊓ S.map (MulAut.conj g).toMonoidHom) ≤ Nat.card ↥S := by
  have h1 := CFSG.Sporadic.Co1.Module.Odd.card_mul_card_stab_le S (g • ω) n t ht hdist
  have hle : S ⊓ S.map (MulAut.conj g).toMonoidHom ≤ MulAction.stabilizer G (g • ω) ⊓ S := by
    intro x hx
    obtain ⟨hxS, y, hyS, rfl⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 ?_, hxS⟩
    change (g * y * g⁻¹) • (g • ω) = g • ω
    rw [mul_smul, mul_smul, inv_smul_smul, hS y hyS]
  exact (Nat.mul_le_mul_left n (Subgroup.card_le_of_le hle)).trans h1

end Orbits

end CFSG.Sporadic.Co1.Module.TwoBFrame

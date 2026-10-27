module

public import CFSG.Quasithin.Background.SmithB45MatQ

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

section Four

variable {V : Type*} [CommGroup V]

theorem mem_fixV_fourSub {a b : MulAut V} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {v : V} : v ∈ fixV (fourSub a b ha hb hab) ↔ a v = v ∧ b v = v := by
  rw [mem_fixV]
  constructor
  · intro h
    exact ⟨h a ((mem_fourSub ha hb hab a).2 (Or.inr (Or.inl rfl))),
      h b ((mem_fourSub ha hb hab b).2 (Or.inr (Or.inr (Or.inl rfl))))⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · rfl
    · exact h1
    · exact h2
    · rw [MulAut.mul_apply, h2, h1]

theorem isElemAbelian2_fourSub {a b : MulAut V} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsElemAbelian2 (fourSub a b ha hb hab) := by
  have hc : Commute a b := hab
  have hab' : ∀ x ∈ fourSub a b ha hb hab, Commute a x ∧ Commute b x := by
    intro x hx
    rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · exact ⟨Commute.one_right a, Commute.one_right b⟩
    · exact ⟨Commute.refl a, hc.symm⟩
    · exact ⟨hc, Commute.refl b⟩
    · exact ⟨(Commute.refl a).mul_right hc, hc.symm.mul_right (Commute.refl b)⟩
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · exact (Commute.one_left y).eq
    · exact (hab' y hy).1.eq
    · exact (hab' y hy).2.eq
    · exact ((hab' y hy).1.mul_left (hab' y hy).2).eq
  · rw [sq]
    rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · exact mul_one 1
    · exact ha
    · exact hb
    · rw [hc.symm.mul_mul_mul_comm, ha, hb, mul_one]

theorem qOf_le_two_of_fourSub [Finite V] {X : Subgroup (MulAut V)} {a b : MulAut V}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) (haX : a ∈ X) (hbX : b ∈ X)
    (hqa : ∀ v, a v * v⁻¹ ∈ fixV (fourSub a b ha hb hab))
    (hqb : ∀ v, b v * v⁻¹ ∈ fixV (fourSub a b ha hb hab))
    (hr : rkIdx (fixV (fourSub a b ha hb hab)) ≤ 4) : qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
  set A := fourSub a b ha hb hab with hA
  have hAX : A ≤ X := by
    intro x hx
    rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · exact X.one_mem
    · exact haX
    · exact hbX
    · exact X.mul_mem haX hbX
  have hbot : A ≠ ⊥ := fun h => ha1 ((Subgroup.mem_bot).1
    (h ▸ (mem_fourSub ha hb hab a).2 (Or.inr (Or.inl rfl))))
  have hquad : IsQuadratic A := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    rcases (mem_fourSub ha hb hab x).1 hx with h | h | h | h <;> rw [h]
    · rw [MulAut.one_apply, mul_inv_cancel]
      exact (fixV A).one_mem
    · exact hqa v
    · exact hqb v
    · have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        rw [MulAut.mul_apply, mul_assoc (a (b v)), inv_mul_cancel_left]
      rw [this]
      exact (fixV A).mul_mem (hqa (b v)) (hqb v)
  have hrk : rk ↥A = 2 := by
    unfold rk
    rw [card_fourSub ha hb hab ha1 hb1 hne]
    exact padicValNat.prime_pow (p := 2) 2
  have hr' : rAV A ≤ 2 := by
    unfold rAV
    rw [hrk, div_le_iff₀ (by norm_num)]
    have : (rkIdx (fixV A) : ℚ) ≤ 4 := by exact_mod_cast hr
    push_cast
    linarith
  exact qOf_le_iff.2 ⟨A, ⟨hAX, hbot, isElemAbelian2_fourSub ha hb hab⟩, hquad, hr'⟩

theorem qOf_le_two_of_masks [Finite V] {n : ℕ} (c : MaskCoords V n) {X : Subgroup (MulAut V)}
    {a b : MulAut V} (fa fb : ℕ → ℕ) (hfa : ∀ m < 2 ^ n, a (c.vm m) = c.vm (fa m))
    (hfb : ∀ m < 2 ^ n, b (c.vm m) = c.vm (fb m)) (hla : ∀ m < 2 ^ n, fa m < 2 ^ n)
    (hlb : ∀ m < 2 ^ n, fb m < 2 ^ n) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (haX : a ∈ X) (hbX : b ∈ X)
    (hq : (List.range (2 ^ n)).all (fun m =>
      fa (fa m ^^^ m) == fa m ^^^ m && fb (fa m ^^^ m) == fa m ^^^ m &&
      fa (fb m ^^^ m) == fb m ^^^ m && fb (fb m ^^^ m) == fb m ^^^ m) = true)
    {k : ℕ} (hk : ((List.range (2 ^ n)).filter fun m => fa m == m && fb m == m).length = 2 ^ k)
    (hnk : n ≤ k + 4) : qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hspec : ∀ m < 2 ^ n, fa (fa m ^^^ m) = fa m ^^^ m ∧ fb (fa m ^^^ m) = fa m ^^^ m ∧
      fa (fb m ^^^ m) = fb m ^^^ m ∧ fb (fb m ^^^ m) = fb m ^^^ m := by
    intro m hm
    have := List.all_eq_true.1 hq m (List.mem_range.2 hm)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hfix : ∀ {m : ℕ}, m < 2 ^ n →
      (c.vm m ∈ fixV (fourSub a b ha hb hab) ↔ fa m = m ∧ fb m = m) := by
    intro m hm
    rw [mem_fixV_fourSub, hfa m hm, hfb m hm]
    exact and_congr ⟨c.vm_inj _ _ (hla m hm) hm, fun h => by rw [h]⟩
      ⟨c.vm_inj _ _ (hlb m hm) hm, fun h => by rw [h]⟩
  refine qOf_le_two_of_fourSub ha hb hab ha1 hb1 hne haX hbX (fun v => ?_) (fun v => ?_) ?_
  · obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [hfa m hm, B45Mat.vm_inv_eq c m, ← c.vm_xor]
    exact (hfix (Nat.xor_lt_two_pow (hla m hm) hm)).2 ⟨(hspec m hm).1, (hspec m hm).2.1⟩
  · obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rw [hfb m hm, B45Mat.vm_inv_eq c m, ← c.vm_xor]
    exact (hfix (Nat.xor_lt_two_pow (hlb m hm) hm)).2 ⟨(hspec m hm).2.2.1, (hspec m hm).2.2.2⟩
  · have hcard := c.card_eq (fixV (fourSub a b ha hb hab))
      (fun m => fa m == m && fb m == m) fun m hm => by
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
        exact hfix hm
    rw [hk, ← List.length_range (n := 2 ^ k)] at hcard
    rw [c.rkIdx_of_card hcard, List.length_range, Nat.log_pow (by norm_num)]
    omega

end Four

@[expose] def q22sArr : Array ℕ :=
  #[1, 0, 2, 3, 7, 5, 6, 4, 10, 9, 8, 11, 16, 19, 18, 17, 12, 15, 14, 13, 22, 21, 20, 23]

@[expose] def q22tArr : Array ℕ :=
  #[1, 0, 3, 2, 7, 6, 5, 4, 10, 11, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 20, 21]

theorem q22s_inv : InvPairOK 24 q22sArr q22sArr = true := by decide

theorem q22t_inv : InvPairOK 24 q22tArr q22tArr = true := by decide

@[expose] def q22sPerm : Equiv.Perm (Fin 24) := permOfArr 24 q22sArr q22sArr q22s_inv

@[expose] def q22tPerm : Equiv.Perm (Fin 24) := permOfArr 24 q22tArr q22tArr q22t_inv

theorem q22sPerm_mem : q22sPerm ∈ mog22plus :=
  ⟨mem_AutPerm_of_arr q22s_inv (by decide), Or.inr ⟨by decide, by decide⟩⟩

theorem q22tPerm_mem : q22tPerm ∈ mog22plus :=
  ⟨mem_AutPerm_of_arr q22t_inv (by decide), Or.inr ⟨by decide, by decide⟩⟩

@[expose] def q22s : ↥mog22plus := ⟨q22sPerm, q22sPerm_mem⟩

@[expose] def q22t : ↥mog22plus := ⟨q22tPerm, q22tPerm_mem⟩

theorem q22s_mul_self : q22s * q22s = 1 :=
  Subtype.ext (Equiv.ext fun i => (permOfArr 24 q22sArr q22sArr q22s_inv).left_inv i)

theorem q22t_mul_self : q22t * q22t = 1 :=
  Subtype.ext (Equiv.ext fun i => (permOfArr 24 q22tArr q22tArr q22t_inv).left_inv i)

theorem q22s_mul_q22t : q22s * q22t = q22t * q22s := by
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  change (q22sPerm (q22tPerm i) : ℕ) = (q22tPerm (q22sPerm i) : ℕ)
  simp only [q22sPerm, q22tPerm, permOfArr_val]
  revert i
  decide

theorem q22s_ne_one : q22s ≠ 1 := fun h => by
  have h0 : q22sPerm 0 = 0 := congrArg (fun σ : ↥mog22plus => (σ : Equiv.Perm (Fin 24)) 0) h
  exact absurd h0 (by decide)

theorem q22t_ne_one : q22t ≠ 1 := fun h => by
  have h0 : q22tPerm 0 = 0 := congrArg (fun σ : ↥mog22plus => (σ : Equiv.Perm (Fin 24)) 0) h
  exact absurd h0 (by decide)

theorem q22s_ne_q22t : q22s ≠ q22t := fun h => by
  have h2 : q22sPerm 2 = q22tPerm 2 :=
    congrArg (fun σ : ↥mog22plus => (σ : Equiv.Perm (Fin 24)) 2) h
  exact absurd h2 (by decide)

theorem psiC22_q22s (m : ℕ) : psiC22 q22s (toW 10 m) = toW 10 (actC10 q22sArr m) :=
  rhoC10_toW mog22plus le_rfl q22s (hasArr_permOfArr q22s_inv) m

theorem psiC22_q22t (m : ℕ) : psiC22 q22t (toW 10 m) = toW 10 (actC10 q22tArr m) :=
  rhoC10_toW mog22plus le_rfl q22t (hasArr_permOfArr q22t_inv) m

theorem q22_quad_check : (List.range 1024).all (fun m =>
    actC10 q22sArr (actC10 q22sArr m ^^^ m) == actC10 q22sArr m ^^^ m &&
    actC10 q22tArr (actC10 q22sArr m ^^^ m) == actC10 q22sArr m ^^^ m &&
    actC10 q22sArr (actC10 q22tArr m ^^^ m) == actC10 q22tArr m ^^^ m &&
    actC10 q22tArr (actC10 q22tArr m ^^^ m) == actC10 q22tArr m ^^^ m) = true := by
  decide +kernel

theorem q22_fix_check : ((List.range (2 ^ 10)).filter fun m =>
    actC10 q22sArr m == m && actC10 q22tArr m == m).length = 2 ^ 6 := by
  decide +kernel

theorem qOf_le_two_of_q22
    {Y : Subgroup (MulAut W10)} (hs : psiC22 q22s ∈ Y) (ht : psiC22 q22t ∈ Y) :
    qOf Y ≤ ((2 : ℚ) : WithTop ℚ) := by
  have ha : psiC22 q22s * psiC22 q22s = 1 := by rw [← map_mul, q22s_mul_self, map_one]
  have hb : psiC22 q22t * psiC22 q22t = 1 := by rw [← map_mul, q22t_mul_self, map_one]
  have hab : psiC22 q22s * psiC22 q22t = psiC22 q22t * psiC22 q22s := by
    rw [← map_mul, ← map_mul, q22s_mul_q22t]
  have ha1 : psiC22 q22s ≠ 1 := fun h =>
    q22s_ne_one (rhoC10_mog22plus_injective (h.trans (map_one _).symm))
  have hb1 : psiC22 q22t ≠ 1 := fun h =>
    q22t_ne_one (rhoC10_mog22plus_injective (h.trans (map_one _).symm))
  have hne : psiC22 q22s ≠ psiC22 q22t := fun h => q22s_ne_q22t (rhoC10_mog22plus_injective h)
  exact qOf_le_two_of_masks (MaskCoords.std 10) (actC10 q22sArr) (actC10 q22tArr)
    (fun m _ => psiC22_q22s m) (fun m _ => psiC22_q22t m) (fun m _ => actC10_lt _ m)
    (fun m _ => actC10_lt _ m) ha hb hab ha1 hb1 hne hs ht q22_quad_check q22_fix_check
    (by norm_num)

end CFSG.Quasithin.H.Mathieu

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.Code

variable {V : Type*} [CommGroup V] [Finite V] {L X : Subgroup (MulAut V)}

theorem qOf_le_of_map_congrHom {W : Type*} [CommGroup W] [Finite W] (e : V ≃* W) {r : ℚ}
    (h : qOf (X.map (congrHom e)) ≤ (r : WithTop ℚ)) : qOf X ≤ (r : WithTop ℚ) := by
  obtain ⟨B, hB, hBq, hBr⟩ := qOf_le_iff.1 h
  obtain ⟨A, -, rfl⟩ := exists_eq_map_congrHom e hB.1
  refine qOf_le_iff.2 ⟨A, (isA2_map_congrHom e).1 hB, (Subgroup.closure_le _).2 ?_, ?_⟩
  · rintro _ ⟨x, hx, v, rfl⟩
    rw [SetLike.mem_coe, mem_fixV]
    intro y hy
    have hw : congrHom e x (e v) * (e v)⁻¹ ∈ commV (A.map (congrHom e)) :=
      Subgroup.subset_closure ⟨congrHom e x, ⟨x, hx, rfl⟩, e v, rfl⟩
    have h1 := hBq hw (congrHom e y) ⟨y, hy, rfl⟩
    have h2 : congrHom e x (e v) * (e v)⁻¹ = e (x v * v⁻¹) := by
      rw [map_mul, map_inv, congrHom_apply, MulEquiv.symm_apply_apply]
    rw [h2, congrHom_apply, MulEquiv.symm_apply_apply] at h1
    exact e.injective h1
  · unfold rAV at hBr ⊢
    rwa [rk_map_congrHom, rkIdx_fixV_map_congrHom] at hBr

omit [Finite V] in
theorem psiC22_mem_of_swap
    (hLX : IsOver L X) {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC10 mog22 mog22_le_mog22plus).range) (hXL : ¬ X ≤ L)
    {τ : ↥mog22plus} (hτ0 : (τ : Equiv.Perm (Fin 24)) 0 = 1)
    (hτ1 : (τ : Equiv.Perm (Fin 24)) 1 = 0) : psiC22 τ ∈ X.map (congrHom e) := by
  obtain ⟨x, hxX, hxL⟩ := Set.not_subset.1 hXL
  obtain ⟨σ, hσ⟩ := map_le_of_normalizer hLX he normalizer_rhoC10_mog22 le_rfl ⟨x, hxX, rfl⟩
  have hmem : ∀ ρ : ↥mog22plus, (ρ : Equiv.Perm (Fin 24)) ∈ mog22 →
      psiC22 ρ ∈ L.map (congrHom e) := by
    intro ρ hρ
    rw [he, range_rhoC10_mog22]
    exact ⟨ρ, Subgroup.mem_subgroupOf.2 hρ, rfl⟩
  have hσ01 : (σ : Equiv.Perm (Fin 24)) 0 = 1 ∧ (σ : Equiv.Perm (Fin 24)) 1 = 0 := by
    rcases σ.2.2 with ⟨h0, h1⟩ | h01
    · refine absurd ?_ hxL
      have h := hmem σ ⟨⟨σ.2.1, (mem_stab_iff 0 _).2 h0⟩, (mem_stab_iff 1 _).2 h1⟩
      rw [hσ] at h
      exact (Subgroup.mem_map_iff_mem (congrHom_injective e)).1 h
    · exact h01
  have hρ : ((σ⁻¹ * τ : ↥mog22plus) : Equiv.Perm (Fin 24)) ∈ mog22 := by
    refine ⟨⟨(σ⁻¹ * τ).2.1, (mem_stab_iff 0 _).2 ?_⟩, (mem_stab_iff 1 _).2 ?_⟩
    · change (σ : Equiv.Perm (Fin 24))⁻¹ ((τ : Equiv.Perm (Fin 24)) 0) = 0
      rw [hτ0, Equiv.Perm.inv_eq_iff_eq, hσ01.1]
    · change (σ : Equiv.Perm (Fin 24))⁻¹ ((τ : Equiv.Perm (Fin 24)) 1) = 1
      rw [hτ1, Equiv.Perm.inv_eq_iff_eq, hσ01.2]
  have h1 : psiC22 (σ⁻¹ * τ) ∈ X.map (congrHom e) := Subgroup.map_mono hLX.1 (hmem _ hρ)
  have h2 : psiC22 σ ∈ X.map (congrHom e) := by
    rw [hσ]
    exact ⟨x, hxX, rfl⟩
  have h3 : psiC22 σ * psiC22 (σ⁻¹ * τ) ∈ X.map (congrHom e) := (X.map (congrHom e)).mul_mem h2 h1
  rwa [← map_mul, mul_inv_cancel_left] at h3

theorem qOf_le_two_code22
    (hLX : IsOver L X) (h : MathieuCode22 L ⊤ ⊥) (hXL : ¬ X ≤ L) :
    qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨e, he⟩ := code22_std h
  exact qOf_le_of_map_congrHom e (qOf_le_two_of_q22
    (psiC22_mem_of_swap hLX he hXL (by decide) (by decide))
    (psiC22_mem_of_swap hLX he hXL (by decide) (by decide)))

theorem qOf_eq_two_code22
    (hLX : IsOver L X) (h : MathieuCode22 L ⊤ ⊥) (hXL : ¬ X ≤ L) : qOf X = 2 := by
  have h2 : ((2 : ℚ) : WithTop ℚ) = 2 := rfl
  rw [← h2]
  exact le_antisymm (qOf_le_two_code22 hLX h hXL) (two_le_qOf_code22 hLX h)

end CFSG.Quasithin.B45Mat

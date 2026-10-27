module

public import CFSG.Quasithin.Background.A312SporAlt5
public import CFSG.Quasithin.Background.A312SporE8Check
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L Matrix

section E8

variable {Γ : Type} [Group Γ]

@[expose] def e8Elt (v : Fin 3 → Γ) (c : Fin 3 → ZMod 2) : Γ :=
  v 0 ^ (c 0).val * v 1 ^ (c 1).val * v 2 ^ (c 2).val

structure E8Basis (v : Fin 3 → Γ) : Prop where
  sq : ∀ i, v i * v i = 1
  comm : ∀ i j, Commute (v i) (v j)
  ne_one : ∀ c, e8Elt v c = 1 → c = 0

variable {v : Fin 3 → Γ}

theorem pow_mod_two_of_mul_self {x : Γ} (hx : x * x = 1) (m : ℕ) : x ^ (m % 2) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, sq, hx, one_pow, mul_one]

theorem pow_val_add_of_mul_self {x : Γ} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, pow_mod_two_of_mul_self hx, pow_add]

theorem e8Elt_zero : e8Elt v 0 = 1 := by simp [e8Elt]

theorem e8Elt_add (h : E8Basis v) (c d : Fin 3 → ZMod 2) :
    e8Elt v (c + d) = e8Elt v c * e8Elt v d := by
  unfold e8Elt
  simp only [Pi.add_apply]
  rw [pow_val_add_of_mul_self (h.sq 0), pow_val_add_of_mul_self (h.sq 1),
    pow_val_add_of_mul_self (h.sq 2)]
  have c01 : Commute (v 0 ^ (d 0).val) (v 1 ^ (c 1).val) := (h.comm 0 1).pow_pow _ _
  have c02 : Commute (v 0 ^ (d 0).val) (v 2 ^ (c 2).val) := (h.comm 0 2).pow_pow _ _
  have c12 : Commute (v 1 ^ (d 1).val) (v 2 ^ (c 2).val) := (h.comm 1 2).pow_pow _ _
  simp only [mul_assoc]
  rw [c01.left_comm, c12.left_comm, c02.left_comm]

theorem add_self_f2 (x : Fin 3 → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

theorem e8Elt_mul_self (h : E8Basis v) (c : Fin 3 → ZMod 2) : e8Elt v c * e8Elt v c = 1 := by
  rw [← e8Elt_add h, add_self_f2, e8Elt_zero]

theorem e8Elt_injective (h : E8Basis v) : Function.Injective (e8Elt v) := by
  intro c d hcd
  have h1 : e8Elt v (c + d) = 1 := by rw [e8Elt_add h, hcd, e8Elt_mul_self h]
  have h2 := h.ne_one _ h1
  funext i
  have h3 := congrFun h2 i
  simp only [Pi.add_apply, Pi.zero_apply] at h3
  revert h3
  generalize c i = a
  generalize d i = b
  revert a b
  decide

@[expose] def e8Hom (h : E8Basis v) : Multiplicative (Fin 3 → ZMod 2) →* Γ where
  toFun c := e8Elt v c.toAdd
  map_one' := e8Elt_zero
  map_mul' c d := e8Elt_add h c.toAdd d.toAdd

theorem conj_e8Elt (g : Γ) (c : Fin 3 → ZMod 2) :
    g * e8Elt v c * g⁻¹ = e8Elt (fun i => g * v i * g⁻¹) c := by
  have h1 : g * e8Elt v c * g⁻¹ = MulAut.conj g (e8Elt v c) := rfl
  rw [h1]
  simp only [e8Elt, map_mul, map_pow, MulAut.conj_apply]

theorem e8Elt_pow_val (a : ZMod 2) (w : Fin 3 → ZMod 2) :
    e8Elt v w ^ a.val = e8Elt v (a • w) := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · rw [zero_smul, e8Elt_zero, ZMod.val_zero, pow_zero]
  · rw [one_smul, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem e8Elt_mulVec (h : E8Basis v) (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (c : Fin 3 → ZMod 2) : e8Elt (fun i => e8Elt v fun r => M r i) c = e8Elt v (M *ᵥ c) := by
  have hM : M *ᵥ c = c 0 • (fun r => M r 0) + c 1 • (fun r => M r 1) + c 2 • (fun r => M r 2) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [hM, e8Elt_add h, e8Elt_add h, ← e8Elt_pow_val, ← e8Elt_pow_val, ← e8Elt_pow_val]
  rfl

theorem e8Elt_one_col (i : Fin 3) :
    e8Elt v (fun r => (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) r i) = v i := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  have h0 : (0 : ZMod 2).val = 0 := rfl
  fin_cases i <;> simp [e8Elt, Matrix.one_apply, h1, h0]

variable (h : E8Basis v)

@[expose] def e8Sub : Subgroup Γ := (e8Hom h).range

theorem mem_e8Sub_iff (x : Γ) : x ∈ e8Sub h ↔ ∃ c, e8Elt v c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

abbrev e8Norm : Subgroup Γ := Subgroup.normalizer (e8Sub h : Set Γ)

theorem conj_mem_e8Sub (g : ↥(e8Norm h)) (c : Fin 3 → ZMod 2) :
    (g : Γ) * e8Elt v c * (g : Γ)⁻¹ ∈ e8Sub h :=
  (Subgroup.mem_normalizer_iff.mp g.2 _).mp ((mem_e8Sub_iff h _).mpr ⟨c, rfl⟩)

@[expose] noncomputable def e8Co (g : ↥(e8Norm h)) (c : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  ((mem_e8Sub_iff h _).mp (conj_mem_e8Sub h g c)).choose

theorem e8Elt_e8Co (g : ↥(e8Norm h)) (c : Fin 3 → ZMod 2) :
    e8Elt v (e8Co h g c) = (g : Γ) * e8Elt v c * (g : Γ)⁻¹ :=
  ((mem_e8Sub_iff h _).mp (conj_mem_e8Sub h g c)).choose_spec

theorem e8Co_eq {g : ↥(e8Norm h)} {c d : Fin 3 → ZMod 2}
    (hd : e8Elt v d = (g : Γ) * e8Elt v c * (g : Γ)⁻¹) : e8Co h g c = d :=
  e8Elt_injective h (by rw [e8Elt_e8Co, hd])

theorem e8Co_mul (g k : ↥(e8Norm h)) (c : Fin 3 → ZMod 2) :
    e8Co h (g * k) c = e8Co h g (e8Co h k c) := by
  apply e8Co_eq
  rw [e8Elt_e8Co, e8Elt_e8Co, Subgroup.coe_mul]
  group

theorem e8Co_one (c : Fin 3 → ZMod 2) : e8Co h 1 c = c :=
  e8Co_eq h (by rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])

theorem e8Co_add (g : ↥(e8Norm h)) (c d : Fin 3 → ZMod 2) :
    e8Co h g (c + d) = e8Co h g c + e8Co h g d := by
  apply e8Co_eq
  rw [e8Elt_add h, e8Elt_e8Co, e8Elt_e8Co, e8Elt_add h]
  group

theorem e8Co_smul (g : ↥(e8Norm h)) (a : ZMod 2) (x : Fin 3 → ZMod 2) :
    e8Co h g (a • x) = a • e8Co h g x := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · have h1 := e8Co_add h g 0 0
    rw [add_zero, add_self_f2] at h1
    rw [zero_smul, zero_smul, h1]
  · rw [one_smul, one_smul]

@[expose] noncomputable def e8Mat (g : ↥(e8Norm h)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun r i => e8Co h g (Pi.single i 1) r

theorem e8Mat_mulVec (g : ↥(e8Norm h)) (c : Fin 3 → ZMod 2) : e8Mat h g *ᵥ c = e8Co h g c := by
  have hc : c = c 0 • Pi.single 0 1 + c 1 • Pi.single 1 1 + c 2 • Pi.single 2 1 := by
    funext i
    fin_cases i <;> simp
  conv_rhs => rw [hc]
  rw [e8Co_add, e8Co_add, e8Co_smul, e8Co_smul, e8Co_smul]
  funext r
  simp only [e8Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem matrix_ext_mulVec {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hMN : ∀ c, M *ᵥ c = N *ᵥ c) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun c => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hMN])

theorem e8Mat_mul (g k : ↥(e8Norm h)) : e8Mat h (g * k) = e8Mat h g * e8Mat h k :=
  matrix_ext_mulVec fun c => by
    rw [e8Mat_mulVec, e8Co_mul, ← Matrix.mulVec_mulVec, e8Mat_mulVec, e8Mat_mulVec]

theorem e8Mat_one : e8Mat h 1 = 1 :=
  matrix_ext_mulVec fun c => by rw [e8Mat_mulVec, e8Co_one, Matrix.one_mulVec]

theorem e8Mat_det (g : ↥(e8Norm h)) : (e8Mat h g).det = 1 := by
  have h1 : (e8Mat h g).det * (e8Mat h g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← e8Mat_mul, mul_inv_cancel, e8Mat_one, Matrix.det_one]
  generalize (e8Mat h g).det = x at h1 ⊢
  generalize (e8Mat h g⁻¹).det = y at h1
  revert x y
  decide

@[expose] noncomputable def e8SL : ↥(e8Norm h) →* SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun g := ⟨e8Mat h g, e8Mat_det h g⟩
  map_one' := Subtype.ext (e8Mat_one h)
  map_mul' g k := Subtype.ext (e8Mat_mul h g k)

theorem e8SL_eq (g : ↥(e8Norm h)) (M : SpecialLinearGroup (Fin 3) (ZMod 2))
    (hM : ∀ i, (g : Γ) * v i * (g : Γ)⁻¹ =
      e8Elt v fun r => (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) r i) : e8SL h g = M := by
  apply Subtype.ext
  apply matrix_ext_mulVec
  intro c
  change e8Mat h g *ᵥ c = _
  rw [e8Mat_mulVec]
  apply e8Co_eq
  rw [conj_e8Elt, ← e8Elt_mulVec h]
  congr 1
  funext i
  exact (hM i).symm

theorem e8SL_eq_one (g : ↥(e8Norm h)) (hc : ∀ i, Commute (g : Γ) (v i)) : e8SL h g = 1 :=
  e8SL_eq h g 1 fun i => by
    rw [show (((1 : SpecialLinearGroup (Fin 3) (ZMod 2))) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
      from rfl, e8Elt_one_col]
    exact (hc i).mul_inv_cancel

theorem mem_e8Norm [Finite Γ] {g : Γ} (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hM : ∀ i, g * v i * g⁻¹ = e8Elt v fun r => M r i) : g ∈ e8Norm h := by
  have hle : (e8Sub h).map (MulAut.conj g).toMonoidHom ≤ e8Sub h := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_e8Sub_iff h x).mp hx
    refine (mem_e8Sub_iff h _).mpr ⟨M *ᵥ c, ?_⟩
    rw [← e8Elt_mulVec h]
    change _ = g * e8Elt v c * g⁻¹
    rw [conj_e8Elt]
    congr 1
    funext i
    exact (hM i).symm
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end E8

theorem eq_top_of_orders_sl32 {H : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))}
    {x₃ x₄ x₇ : SpecialLinearGroup (Fin 3) (ZMod 2)} (h₃ : x₃ ∈ H) (h₄ : x₄ ∈ H) (h₇ : x₇ ∈ H)
    (o₃ : orderOf x₃ = 3) (o₄ : orderOf x₄ = 4) (o₇ : orderOf x₇ = 7) : H = ⊤ := by
  have := Seven.slThree_isSimple
  have hc := Seven.card_slThree
  have hd : ∀ x ∈ H, orderOf x ∣ Nat.card H := fun x hx => by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have d3 := hd x₃ h₃
  have d4 := hd x₄ h₄
  have d7 := hd x₇ h₇
  rw [o₃] at d3
  rw [o₄] at d4
  rw [o₇] at d7
  have hle : Nat.card H ≤ 168 := hc ▸ Subgroup.card_le_card_group H
  have hpos : 0 < Nat.card H := Nat.card_pos
  rcases (show Nat.card H = 84 ∨ Nat.card H = 168 by omega) with h84 | h168
  · exfalso
    have hi : H.index = 2 := by
      have h1 := Subgroup.card_mul_index H
      rw [h84, hc] at h1
      omega
    have := Subgroup.normal_of_index_eq_two hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · rw [h, Subgroup.card_bot] at h84
      omega
    · rw [h, Subgroup.card_top, hc] at h84
      omega
  · exact Subgroup.eq_top_of_card_eq H (by rw [h168, hc])

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem lFamily_psl32_of_hom {S B Y : Subgroup Γ} (hB : B ∈ lFamily S) (hY : B ⊔ S = Y)
    (ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ) {e : ℕ}
    (hcard : Nat.card ↥Y = 168 * 2 ^ e)
    (hquot : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 1) :
    IsPSL 3 2 1 (ModO2 B) ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ e := by
  subst hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Seven.slThree_isSimple
  have hc := Seven.card_slThree
  have hK : Nat.card ψ.ker = 2 ^ e := by
    have h1 := card_eq_card_ker_mul_card_range ψ
    rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top, hc, hcard] at h1
    have h2 : 168 * Nat.card ψ.ker = 168 * 2 ^ e := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hKp : IsPGroup 2 ↥ψ.ker := IsPGroup.of_card hK
  have hPY : perfectCore (B ⊔ S) ≤ B ⊔ S := perfectCore_le _
  have hnorm := perfectCore_normal (B ⊔ S)
  have himg : ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).map ψ = ⊤ := by
    have hN := hnorm.map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).map ψ) with h | h
    · exfalso
      apply not_isSolvable_sup hB
      have hle : (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S) ≤ ψ.ker := by
        intro x hx
        have h1 : ψ x ∈ ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).map ψ := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact h1
      let κ : ↥(perfectCore (B ⊔ S)) →* ↥ψ.ker :=
        { toFun := fun x => ⟨Subgroup.inclusion hPY x, hle x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hκ : Function.Injective κ := fun x y hxy => by
        have := congrArg (fun z : ↥ψ.ker => ((z : ↥(B ⊔ S)) : Γ)) hxy
        exact Subtype.ext this
      have hKs : Group.IsSolvable ↥ψ.ker := by
        have := hKp.isNilpotent
        infer_instance
      have hPs : Group.IsSolvable ↥(perfectCore (B ⊔ S)) :=
        Group.isSolvable_of_isSolvable_injective hκ
      exact (isSolvable_iff_perfectCore_eq_bot _).mpr
        (eq_bot_of_perfect_of_solvable (perfectCore_perfect _) hPs)
    · exact h
  let f : ↥(perfectCore (B ⊔ S)) →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ψ.comp (Subgroup.inclusion hPY)
  have hf : Function.Surjective f := by
    intro s
    have hs : s ∈ ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).map ψ := by
      rw [himg]; exact Subgroup.mem_top s
    obtain ⟨y, hy, hys⟩ := hs
    exact ⟨⟨(y : Γ), hy⟩, hys⟩
  let ι : ↥f.ker →* ↥ψ.ker :=
    { toFun := fun x => ⟨Subgroup.inclusion hPY x.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy => by
    have := congrArg (fun z : ↥ψ.ker => ((z : ↥(B ⊔ S)) : Γ)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hkf2 : IsPGroup 2 ↥f.ker := hKp.of_injective ι hι
  have hkerf : Group.IsSolvable ↥f.ker := by
    have := hkf2.isNilpotent
    infer_instance
  have hBP : B = perfectCore (B ⊔ S) :=
    lFamily_eq_perfectCore hB Seven.slThree_nonabelian f hf hkerf
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hkf2
  have hP : Nat.card ↥(perfectCore (B ⊔ S)) = 2 ^ a * 168 := by
    rw [card_eq_card_ker_mul_card_range f, ha, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      hc]
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hP, hcard] at hQ
  have hQ' : Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * 2 ^ a = 2 ^ e := by
    have h1 : 168 * (Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * 2 ^ a) =
        168 * 2 ^ e := by
      rw [hQ]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hQp : IsPGroup 2 (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) :=
    IsPGroup.of_card_dvd_pow (n := e) ⟨2 ^ a, hQ'.symm⟩
  have hQ1 := hquot _ hQp
  have hQpos : 0 < Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) :=
    Nat.card_pos
  have hae : 2 ^ a = 2 ^ e := by
    have hq1 : Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) = 1 := by omega
    rw [hq1, one_mul] at hQ'
    exact hQ'
  rw [hBP]
  refine ⟨Seven.isPSL_three_two (modO2EquivOfHom Seven.slThree_nonabelian f hf hkf2), ?_⟩
  rw [pCore_two_eq_ker Seven.slThree_nonabelian f hf hkf2, ha, hae]

theorem quot_le_one_of_ker_le {Y : Type} [Group Y] [Finite Y]
    (ψ : Y →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ) (N : Subgroup Y)
    [N.Normal] (hp : IsPGroup 2 (Y ⧸ N)) (hker : ψ.ker ≤ N) : Nat.card (Y ⧸ N) ≤ 1 := by
  have := Seven.slThree_isSimple
  have hN := (inferInstance : N.Normal).map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
  · exfalso
    have heq : ψ.ker = N := le_antisymm hker ((Subgroup.map_eq_bot_iff N).mp h)
    have e : (Y ⧸ N) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq heq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    have h168 : Nat.card (Y ⧸ N) = 168 := by rw [Nat.card_congr e.toEquiv, Seven.card_slThree]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [h168] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 168)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · have hNtop : N = ⊤ := by
      have h1 := Subgroup.comap_map_eq ψ N
      rw [h, Subgroup.comap_top, sup_eq_left.mpr hker] at h1
      exact h1.symm
    rw [hNtop]
    exact (Subgroup.index_top).le

theorem ker_le_of_odd_closure {Y C : Subgroup Γ} {H : Type} [Group H] (ψ : ↥Y →* H)
    {R : List Γ} (hRY : ∀ x ∈ R, x ∈ Y) (hRodd : ∀ x ∈ R, ∃ m, m % 2 = 1 ∧ x ^ m = 1)
    (hCR : C ≤ Subgroup.closure {x | x ∈ R}) (hCker : ∀ x (hx : x ∈ Y), x ∈ C → ψ ⟨x, hx⟩ = 1)
    (hcard : Nat.card ψ.ker ≤ Nat.card C) (N : Subgroup ↥Y) [N.Normal]
    (hp : IsPGroup 2 (↥Y ⧸ N)) : ψ.ker ≤ N := by
  have hCY : C ≤ Y := hCR.trans ((Subgroup.closure_le Y).mpr hRY)
  have h1 : C.subgroupOf Y ≤ ψ.ker := fun x hx => hCker x x.2 hx
  have h2 : C.subgroupOf Y = ψ.ker := Subgroup.eq_of_le_of_card_ge h1
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv]; exact hcard)
  have h3 : ∀ g ∈ Subgroup.closure {x | x ∈ R}, ∃ h : g ∈ Y, (⟨g, h⟩ : ↥Y) ∈ N := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm, hxm⟩ := hRodd x hx
      exact ⟨hRY x hx, CFSG.QuasithinUnique.Ch1.SporLat.mem_of_pow_eq_one_odd N hp hm
        (Subtype.ext (by simpa using hxm))⟩
    | one => exact ⟨Y.one_mem, N.one_mem⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hxN⟩ := ihx
      obtain ⟨hy, hyN⟩ := ihy
      exact ⟨Y.mul_mem hx hy, N.mul_mem hxN hyN⟩
    | inv x _ ihx =>
      obtain ⟨hx, hxN⟩ := ihx
      exact ⟨Y.inv_mem hx, N.inv_mem hxN⟩
  rw [← h2]
  intro x hx
  obtain ⟨_, hxN⟩ := h3 x (hCR hx)
  exact hxN

section Tables

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

variable {G : Type} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem tabArr_mul (x y : G) :
    (tab n (x * y)).toArray = compArr (tab n x).toArray (tab n y).toArray := by
  apply Array.ext'
  rw [compArr_toList, List.toList_toArray, List.toList_toArray, List.toList_toArray, tab_mul]

theorem eq_of_tabArr_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) {x y : G}
    (h : (tab n x).toArray = (tab n y).toArray) : x = y :=
  eq_of_act_eq_base hB hbase fun b _ => by rw [← img_tab, ← img_tab, h]

theorem tabArr_pow_of_lt_two (x : G) {b : ℕ} (hb : b < 2) {vt : Array (Array ℕ)} {i : ℕ}
    (hx : (tab n x).toArray = vt.getD i #[]) : (tab n (x ^ b)).toArray = e8VPow vt n b i := by
  interval_cases b
  · rw [pow_zero, CFSG.QuasithinUnique.Ch1.SporLat.tab_one_toArray]
    rfl
  · rw [pow_one, hx]
    rfl

@[expose] def e8Vec (c : Fin 3 → ZMod 2) : List ℕ := [(c 0).val, (c 1).val, (c 2).val]

theorem tabArr_e8Elt {v : Fin 3 → G} {vt : Array (Array ℕ)}
    (hv : ∀ i : Fin 3, (tab n (v i)).toArray = vt.getD i #[]) (c : Fin 3 → ZMod 2) :
    (tab n (e8Elt v c)).toArray = e8BTab vt n (e8Vec c) := by
  unfold e8Elt
  rw [tabArr_mul, tabArr_mul, tabArr_pow_of_lt_two _ (ZMod.val_lt _) (hv 0),
    tabArr_pow_of_lt_two _ (ZMod.val_lt _) (hv 1), tabArr_pow_of_lt_two _ (ZMod.val_lt _) (hv 2)]
  rfl

theorem e8Vec_mem_e8NZ {c : Fin 3 → ZMod 2} (hc : c ≠ 0) : e8Vec c ∈ e8NZ := by
  have key : ∀ a b d : ZMod 2, ¬ (a = 0 ∧ b = 0 ∧ d = 0) → [a.val, b.val, d.val] ∈ e8NZ := by
    decide
  refine key (c 0) (c 1) (c 2) fun h0 => hc ?_
  funext i
  fin_cases i
  · exact h0.1
  · exact h0.2.1
  · exact h0.2.2

theorem e8_of_check {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) {v : Fin 3 → G}
    {vt : Array (Array ℕ)} (hv : ∀ i : Fin 3, (tab n (v i)).toArray = vt.getD i #[])
    {g : ℕ → G} {letters : Array (Array ℕ)}
    (hg : ∀ l < letters.size, (tab n (g l)).toArray = letters.getD l #[])
    {mats : List (List (List ℕ))} {M : ℕ → Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hM : ∀ l < letters.size, ∀ i : Fin 3, e8Col (mats.getD l []) i = e8Vec fun r => M l r i)
    (hchk : e8Check n vt letters mats = true) :
    E8Basis v ∧
      ∀ l < letters.size, ∀ i : Fin 3, g l * v i * (g l)⁻¹ = e8Elt v fun r => M l r i := by
  simp only [e8Check, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨hsq, hcomm⟩, hne⟩, hconj⟩ := hchk
  have tab1 : (tab n (1 : G)).toArray = Array.range n :=
    CFSG.QuasithinUnique.Ch1.SporLat.tab_one_toArray
  refine ⟨⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩, fun l hl i => ?_⟩
  · apply eq_of_tabArr_eq hB hbase
    rw [tabArr_mul, hv, tab1]
    exact hsq i i.2
  · change v i * v j = v j * v i
    apply eq_of_tabArr_eq hB hbase
    rw [tabArr_mul, tabArr_mul, hv i, hv j]
    exact hcomm i i.2 j j.2
  · by_contra hc0
    apply hne (e8Vec c) (e8Vec_mem_e8NZ hc0)
    rw [← tabArr_e8Elt hv c, hc, tab1]
  · apply mul_inv_eq_of_eq_mul
    apply eq_of_tabArr_eq hB hbase
    rw [tabArr_mul, tabArr_mul, hg l hl, hv i, tabArr_e8Elt hv, ← hM l hl i]
    exact hconj l hl i i.2

end Tables

end CFSG.Quasithin.A312S

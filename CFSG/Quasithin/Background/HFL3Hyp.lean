module

public import CFSG.Quasithin.Background.HFL3Res

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H.SU3 CFSG.Quasithin.E3

theorem gammaCheck_map_le {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W) (k : ℕ)
    (P : Subgroup (MulAut V)) :
    gammaCheck k (P.map (congrHom e)) ≤ (gammaCheck k P).map e.toMonoidHom := by
  refine iSup_le fun X => iSup_le fun hX => iSup_le fun hXk => ?_
  set X₀ := X.comap (congrHom e) with hX₀def
  have hX₀ : X₀.map (congrHom e) = X :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.congr e).surjective X
  have hX₀P : X₀ ≤ P := fun a ha =>
    (Subgroup.mem_map_iff_mem (congrHom_injective e)).mp (hX ha)
  have hk : mQuot P X₀ ≤ k := by
    rw [← mQuot_map_congrHom e, hX₀]
    exact hXk
  rw [← hX₀, fixV_map_congrHom]
  exact Subgroup.map_mono (le_iSup_of_le X₀ (le_iSup_of_le hX₀P (le_iSup_of_le hk le_rfl)))

theorem fixV_le_gammaCheck {W : Type*} [CommGroup W] {k : ℕ} {P X : Subgroup (MulAut W)}
    (hXP : X ≤ P) (hk : mQuot P X ≤ k) : fixV X ≤ gammaCheck k P :=
  le_iSup_of_le X (le_iSup_of_le hXP (le_iSup_of_le hk le_rfl))

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem padicValNat_two_le {m j : ℕ} (hm : m ≤ 2 ^ j) : padicValNat 2 m ≤ j := by
  refine (padicValNat_le_nat_log m).trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt hm
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j))))

theorem mQuot_map_rho_le (hK : Nat.card K = (2 ^ n) ^ 2)
    {P B : Subgroup (SpecialLinearGroup (Fin 3) K)} (hBP : B ≤ P)
    (hinj : ∀ x ∈ P, rho hK x = 1 → x = 1) {j : ℕ} (hidx : B.relIndex P ≤ 2 ^ j) :
    mQuot (P.map (rho hK)) (B.map (rho hK)) ≤ j := by
  have hinjB : ∀ x ∈ B, rho hK x = 1 → x = 1 := fun x hx => hinj x (hBP hx)
  have h1 := Subgroup.relIndex_mul_card (B.map (rho hK)) (P.map (rho hK))
  have h2 := Subgroup.relIndex_mul_card B P
  rw [inf_eq_left.2 (Subgroup.map_mono hBP), card_map_rho_of_inj hK hinjB,
    card_map_rho_of_inj hK hinj] at h1
  rw [inf_eq_left.2 hBP] at h2
  have hB0 : 0 < Nat.card B := Nat.card_pos
  have heq : (B.map (rho hK)).relIndex (P.map (rho hK)) = B.relIndex P :=
    Nat.eq_of_mul_eq_mul_right hB0 (h1.trans h2.symm)
  unfold mQuot
  rw [heq]
  exact padicValNat_two_le hidx

omit [CharP K 2] in
theorem relIndex_ker_le {P : Subgroup (SpecialLinearGroup (Fin 3) K)} {Q : Type*} [Group Q]
    [Finite Q] (f : ↥P →* Q) {j : ℕ} (hQ : Nat.card Q ≤ 2 ^ j) :
    (f.ker.map P.subtype).relIndex P ≤ 2 ^ j := by
  have h1 := Subgroup.relIndex_mul_card (f.ker.map P.subtype) P
  rw [inf_eq_left.2 (Subgroup.map_subtype_le _),
    Subgroup.card_map_of_injective P.subtype_injective] at h1
  have h2 := Subgroup.index_mul_card f.ker
  have h3 : (f.ker.map P.subtype).relIndex P = f.ker.index :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  rw [h3, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hQ

theorem herm_diag {c d : K} (hc : bar n c = c) (hd : bar n d = d) :
    (conjM n (Matrix.diagonal ![c, 0, d]))ᵀ = Matrix.diagonal ![c, 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjM, hc, hd]

theorem rho_diag (hK : Nat.card K = (2 ^ n) ^ 2) {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx02 : (x : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (hx12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) {c d : K} (hc : bar n c = c)
    (hd : bar n d = d) :
    rho hK x (mkH (Matrix.diagonal ![c, 0, d]) (herm_diag hc hd)) =
      mkH (Matrix.diagonal ![c, 0, d]) (herm_diag hc hd) := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  apply mat_injective
  rw [mat_rho, mat_mkH]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, Matrix.mul_apply, Fin.sum_univ_three, conjM, x00, x11, x22, x10, x20, x21, hx02,
      hx12, Matrix.diagonal_apply]

theorem card_fixV_ge_of_Q1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P₀ : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P₀ ≤ unitriangular 3 K)
    (h02 : ∀ x ∈ P₀, (x : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (h12 : ∀ x ∈ P₀, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    2 ^ (2 * n) ≤ Nat.card ↥(fixV (P₀.map (rho hK))) := by
  let f : {c : K // bar n c = c} × {d : K // bar n d = d} → ↥(fixV (P₀.map (rho hK))) :=
    fun p => ⟨mkH (Matrix.diagonal ![p.1.1, 0, p.2.1]) (herm_diag p.1.2 p.2.2), by
      rintro _ ⟨x, hx, rfl⟩
      exact rho_diag hK (hPU hx) (h02 x hx) (h12 x hx) p.1.2 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ h
    have h' := congrArg (fun Y : ↥(fixV (P₀.map (rho hK))) => mat (Y : HMod n K)) h
    simp only [f, mat_mkH] at h'
    have e0 := congrFun (congrFun h' 0) 0
    have e2 := congrFun (congrFun h' 2) 2
    simp at e0 e2
    exact Prod.ext (Subtype.ext e0) (Subtype.ext e2)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, card_fixed hn hK, ← pow_add, ← two_mul] at this

theorem exists_mQuot_le_of_Q1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hP12 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (hinj : ∀ x ∈ P, rho hK x = 1 → x = 1) (hcard : 2 ^ (3 * n) < Nat.card P) :
    ∃ B ≤ P.map (rho hK), mQuot (P.map (rho hK)) B ≤ 2 * n ∧
      fixV B ≠ fixV (P.map (rho hK)) := by
  let f : ↥P →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd
        (((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, uni3_mul_02 (hPU x.2) (hPU y.2), hP12 y y.2, mul_zero, add_zero,
          ← ofAdd_add, add_comm] }
  set P₀ := f.ker.map P.subtype with hP₀
  have hP₀P : P₀ ≤ P := Subgroup.map_subtype_le _
  have hQ : Nat.card (Multiplicative K) ≤ 2 ^ (2 * n) := by
    rw [Nat.card_congr Multiplicative.toAdd, hK, ← pow_mul, mul_comm]
  refine ⟨P₀.map (rho hK), Subgroup.map_mono hP₀P,
    mQuot_map_rho_le hK hP₀P hinj (relIndex_ker_le f hQ), fun heq => ?_⟩
  have h1 := card_fixV_le_of_Q1 hn hK hPU hP12 hcard
  have h2 : 2 ^ (2 * n) ≤ Nat.card ↥(fixV (P₀.map (rho hK))) := by
    refine card_fixV_ge_of_Q1 hn hK (hP₀P.trans hPU) ?_ fun x hx => hP12 x (hP₀P hx)
    rintro _ ⟨x, hx, rfl⟩
    exact ofAdd_eq_one.mp (MonoidHom.mem_ker.mp hx)
  rw [heq] at h2
  have h3 : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact absurd (h2.trans h1) (not_le.mpr h3)

theorem rho_fix_of_Q2 (hK : Nat.card K = (2 ^ n) ^ 2) {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    {X : HMod n K} (hX : mat X 2 2 = 0) {t : K} (ht : bar n t = t)
    (h02 : (x : Matrix (Fin 3) (Fin 3) K) 0 2 = t * mat X 0 2)
    (h12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = t * mat X 1 2) : rho hK x X = X := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  have hY20 : mat X 2 0 = bar n (mat X 0 2) := (herm_apply X 2 0).symm
  have hY21 : mat X 2 1 = bar n (mat X 1 2) := (herm_apply X 2 1).symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply mat_injective
  rw [mat_rho]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, Matrix.mul_apply, Fin.sum_univ_three, conjM, x00, x11, x22, x10, x20, x21, hx01,
      h02, h12, hY20, hY21, hX, ht] <;> ring_nf <;> simp [h2]

theorem mem_gammaCheck_of_Q2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hP01 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (hinj : ∀ x ∈ P, rho hK x = 1 → x = 1) (hcard : 2 ^ (3 * n) < Nat.card P)
    {X : HMod n K} (hX : mat X 2 2 = 0) : X ∈ gammaCheck (3 * n) (P.map (rho hK)) := by
  by_cases hu : mat X 0 2 = 0 ∧ mat X 1 2 = 0
  · have hXb : X ∈ fixV (P.map (rho hK)) := by
      rw [fixV_eq_blkW_of_Q2 hn hK hPU hP01
        (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard)]
      exact ⟨hu.1, hu.2, hX⟩
    refine fixV_le_gammaCheck le_rfl ?_ hXb
    simp [mQuot]
  set u₀ := mat X 0 2 with hu₀
  set u₁ := mat X 1 2 with hu₁
  let S : AddSubgroup (K × K) :=
    { carrier := {p | ∃ t : K, bar n t = t ∧ p = (t * u₀, t * u₁)}
      zero_mem' := ⟨0, map_zero _, by ext <;> simp⟩
      add_mem' := by
        rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
        exact ⟨t + t', by rw [map_add, ht, ht'], by ext <;> simp <;> ring⟩
      neg_mem' := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨-t, by rw [map_neg, ht], by ext <;> simp⟩ }
  have hS : 2 ^ n ≤ Nat.card S := by
    let g : {t : K // bar n t = t} → S := fun t => ⟨(t.1 * u₀, t.1 * u₁), t.1, t.2, rfl⟩
    have hg : Function.Injective g := by
      rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' := congrArg Subtype.val h
      simp only [g, Prod.mk.injEq] at h'
      apply Subtype.ext
      by_cases h0 : u₀ = 0
      · exact mul_right_cancel₀ (fun h1 => hu ⟨h0, h1⟩) h'.2
      · exact mul_right_cancel₀ h0 h'.1
    have := Nat.card_le_card_of_injective g hg
    rwa [card_fixed hn hK] at this
  have hQ : Nat.card (Multiplicative ((K × K) ⧸ S)) ≤ 2 ^ (3 * n) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S
    rw [Nat.card_prod, hK] at h1
    rw [Nat.card_congr Multiplicative.toAdd]
    have h2 : (2 ^ n) ^ 2 * (2 ^ n) ^ 2 = 2 ^ (3 * n) * 2 ^ n := by ring
    rw [h2] at h1
    by_contra hlt
    exact (ne_of_lt (Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) hS Nat.card_pos)) h1
  let f : ↥P →* Multiplicative ((K × K) ⧸ S) :=
    { toFun := fun x => Multiplicative.ofAdd (QuotientAddGroup.mk
        (((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2,
          ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2))
      map_one' := by
        simp only [OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one]
        rw [Matrix.one_apply_ne (by decide), Matrix.one_apply_ne (by decide), ← ofAdd_zero]
        exact congrArg Multiplicative.ofAdd ((QuotientAddGroup.eq_zero_iff _).mpr
          ⟨0, map_zero _, by simp⟩)
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, uni3_mul_02 (hPU x.2) (hPU y.2), uni3_mul_12 (hPU x.2) (hPU y.2),
          hP01 x x.2, zero_mul, add_zero, ← ofAdd_add, ← QuotientAddGroup.mk_add]
        congr 2
        ext <;> simp [add_comm] }
  set P₀ := f.ker.map P.subtype with hP₀
  have hP₀P : P₀ ≤ P := Subgroup.map_subtype_le _
  have hXfix : X ∈ fixV (P₀.map (rho hK)) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨t, ht, he⟩ := (QuotientAddGroup.eq_zero_iff _).mp (ofAdd_eq_one.mp
      (MonoidHom.mem_ker.mp hx))
    simp only [Prod.mk.injEq] at he
    exact rho_fix_of_Q2 hK (hPU x.2) (hP01 x x.2) hX ht he.1 he.2
  exact fixV_le_gammaCheck (Subgroup.map_mono hP₀P)
    (mQuot_map_rho_le hK hP₀P hinj (relIndex_ker_le f hQ)) hXfix

theorem rkIdx_le_of_entry (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {G : Subgroup (HMod n K)}
    (hG : ∀ X : HMod n K, mat X 2 2 = 0 → X ∈ G) : rkIdx G ≤ n := by
  let f : HMod n K →* Multiplicative K :=
    { toFun := fun X => Multiplicative.ofAdd (mat X 2 2)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hle : f.ker ≤ G := fun X hX => hG X (ofAdd_eq_one.mp (MonoidHom.mem_ker.mp hX))
  refine (rkIdx_anti hle).trans ?_
  unfold rkIdx
  rw [Subgroup.index_ker]
  refine padicValNat_two_le ?_
  let g : ↥f.range → {c : K // bar n c = c} := fun y => ⟨Multiplicative.toAdd y.1, by
    obtain ⟨X, hX⟩ := y.2
    rw [← hX]
    exact herm_apply X 2 2⟩
  have hg : Function.Injective g := by
    intro y y' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have := Nat.card_le_card_of_injective g hg
  rwa [card_fixed hn hK] at this

theorem rkIdx_gammaCheck_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ∈ aSet (2 * n + 1) (norm hK))
    (hcard : 2 ^ (3 * n) < Nat.card A) : rkIdx (gammaCheck (3 * n) A) ≤ n := by
  obtain ⟨hAN, hA1, hAe, hAfix⟩ := hA
  have hAL : A ≤ img hK := le_img_of_card hn hK hAN hAe
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard)
  have hA2 : IsPGroup 2 A := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hAe.2 x x.2)⟩
  obtain ⟨g, P, hPU, -, hinj, hPmap⟩ := exists_conj_uni3 hK (hAL.trans (img_le_linImg hK)) hA2
  set c := rho hK g with hc
  have hA' : P.map (rho hK) = A.map (congrHom c) := by rw [hPmap, conj_eq_congrHom]
  have hA'fix : ∀ B, B ≤ P.map (rho hK) → mQuot (P.map (rho hK)) B < 2 * n + 1 →
      fixV B = fixV (P.map (rho hK)) := by
    have hmem : A.map (congrHom c) ∈
        aSet (2 * n + 1) ((⊤ : Subgroup (MulAut (HMod n K))).map (congrHom c)) :=
      (map_mem_aSet_iff c).2 (aSet_mono le_top ⟨hAN, hA1, hAe, hAfix⟩)
    rw [← hA'] at hmem
    exact hmem.2.2.2
  have hAe' : IsElemAbelian2 (P.map (rho hK)) := by
    rw [hA']
    exact (isElemAbelian2_map_congrHom c).2 hAe
  have hcP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : rho hK (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hAe'.1 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
        mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx)))
      h1)
  have hsP : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, ← sq]
    exact hAe'.2 _ ⟨x, hx, rfl⟩
  have hcardP : 2 ^ (3 * n) < Nat.card P := by
    rw [← card_map_rho_of_inj hK hinj, hA', card_map_congrHom]
    exact hcard
  have hΓ : rkIdx (gammaCheck (3 * n) A) ≤ rkIdx (gammaCheck (3 * n) (P.map (rho hK))) := by
    rw [hA', ← rkIdx_map_mulEquiv c (gammaCheck (3 * n) A)]
    exact rkIdx_anti (gammaCheck_map_le c (3 * n) A)
  rcases uni3_cases hPU hcP hsP with h12 | h01
  · exfalso
    obtain ⟨B, hB, hBm, hBne⟩ := exists_mQuot_le_of_Q1 hn hK hPU h12 hinj hcardP
    exact hBne (hA'fix B hB (by omega))
  · exact hΓ.trans (rkIdx_le_of_entry hn hK fun X hX =>
      mem_gammaCheck_of_Q2 hn hK hPU h01 hinj hcardP hX)

end CFSG.Quasithin.H.L3Nine

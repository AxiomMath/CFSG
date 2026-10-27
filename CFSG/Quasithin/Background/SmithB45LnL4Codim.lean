module

public import CFSG.Quasithin.Background.SmithB45LnL4Mod
public import CFSG.Quasithin.Background.SmithB45LnL4Dim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45Ln

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.B42Ln

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def rowsInv1 : Fin 5 → Fin 1 × Fin 14 := ![(0, 0), (0, 1), (0, 2), (0, 7), (0, 10)]

@[expose] def colsInv1 : Fin 5 → Fin 14 := ![3, 4, 5, 6, 9]

@[expose] def yInv1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

theorem rank14_inv1 : 5 ≤ (stackMat fun i => mat14 (up4 (![1] i))).rank :=
  le_rank_of_submatrix _ rowsInv1 colsInv1 yInv1 (by decide +kernel)

@[expose] def rowsInv18 : Fin 5 → Fin 1 × Fin 14 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

@[expose] def colsInv18 : Fin 5 → Fin 14 := ![7, 6, 0, 9, 3]

@[expose] def yInv18 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    1, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 1, 1]

theorem rank14_inv18 : 5 ≤ (stackMat fun i => mat14 (up4 (![18] i))).rank :=
  le_rank_of_submatrix _ rowsInv18 colsInv18 yInv18 (by decide +kernel)

@[expose] def rowsMix0 : Fin 9 → Fin 2 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 4), (0, 11), (0, 12), (1, 0), (1, 1), (1, 2)]

@[expose] def colsMix0 : Fin 9 → Fin 14 := ![7, 6, 8, 3, 9, 13, 10, 0, 12]

@[expose] def yMix0 : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1]

theorem rank14_mix0 : 9 ≤ (stackMat fun i => mat14 (up4 (![2, 12] i))).rank :=
  le_rank_of_submatrix _ rowsMix0 colsMix0 yMix0 (by decide +kernel)

@[expose] def rowsMix1 : Fin 9 → Fin 2 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 7), (0, 10), (0, 12), (1, 2), (1, 7), (1, 8)]

@[expose] def colsMix1 : Fin 9 → Fin 14 := ![3, 4, 5, 6, 9, 12, 1, 10, 11]

@[expose] def yMix1 : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 1]

theorem rank14_mix1 : 9 ≤ (stackMat fun i => mat14 (up4 (![1, 33] i))).rank :=
  le_rank_of_submatrix _ rowsMix1 colsMix1 yMix1 (by decide +kernel)

@[expose] def rowsNtv0 : Fin 7 → Fin 2 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0)]

@[expose] def colsNtv0 : Fin 7 → Fin 14 := ![10, 0, 9, 6, 7, 3, 12]

@[expose] def yNtv0 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 1, 0, 1;
    0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 1, 0;
    1, 0, 0, 0, 1, 0, 1]

theorem rank14_ntv0 : 7 ≤ (stackMat fun i => mat14 (up4 (![12, 22] i))).rank :=
  le_rank_of_submatrix _ rowsNtv0 colsNtv0 yNtv0 (by decide +kernel)

@[expose] def rowsNtv1 : Fin 7 → Fin 2 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0)]

@[expose] def colsNtv1 : Fin 7 → Fin 14 := ![7, 6, 0, 9, 3, 10, 11]

@[expose] def yNtv1 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 1]

theorem rank14_ntv1 : 7 ≤ (stackMat fun i => mat14 (up4 (![18, 33] i))).rank :=
  le_rank_of_submatrix _ rowsNtv1 colsNtv1 yNtv1 (by decide +kernel)

@[expose] def rowsReg0 : Fin 7 → Fin 3 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 7), (0, 10), (0, 12), (1, 0)]

@[expose] def colsReg0 : Fin 7 → Fin 14 := ![3, 4, 5, 6, 9, 12, 7]

@[expose] def yReg0 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

theorem rank14_reg0 : 7 ≤ (stackMat fun i => mat14 (up4 (![1, 2, 4] i))).rank :=
  le_rank_of_submatrix _ rowsReg0 colsReg0 yReg0 (by decide +kernel)

@[expose] def rowsReg1 : Fin 7 → Fin 3 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 5), (0, 8), (0, 13), (1, 2)]

@[expose] def colsReg1 : Fin 7 → Fin 14 := ![10, 11, 9, 3, 6, 12, 0]

@[expose] def yReg1 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

theorem rank14_reg1 : 7 ≤ (stackMat fun i => mat14 (up4 (![4, 16, 32] i))).rank :=
  le_rank_of_submatrix _ rowsReg1 colsReg1 yReg1 (by decide +kernel)

theorem rep14_uOf (c : Fin 64) (hc : up4 c * up4 c = 1) (v : Fin 14 → ZMod 2) :
    rep14 (uOf c) v = mat14 (up4 c) *ᵥ v := by
  have hinv : (uOf c)⁻¹ = uOf c := inv_eq_of_mul_eq_one_right (Subtype.ext hc)
  rw [rep14_apply, hinv]
  exact c14v_conj_eq (up4 c) v

variable {V : Type} [CommGroup V] {G L A : Subgroup (MulAut V)}

section Coords

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))}

theorem card_fixV_le_of_rank {n : ℕ} {ρ' : Representation (ZMod 2) G4 (Fin n → ZMod 2)}
    {β : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = ρ' g (β w)) {B : Subgroup (MulAut V)} {m r : ℕ}
    (g : Fin m → G4) (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ i v, ρ' (g i) v = M i *ᵥ v) (h : G4) (hB : ∀ i, fL4 e (h⁻¹ * g i * h) ∈ B)
    (hr : r ≤ (stackMat M).rank) : Nat.card (fixV B) ≤ 2 ^ (n - r) := by
  have hρh : ∀ x, ρ' h⁻¹ (ρ' h x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hρh' : ∀ x, ρ' h (ρ' h⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let F : fixV B → {v : Fin n → ZMod 2 // ∀ i, M i *ᵥ v = v} := fun w =>
    ⟨ρ' h (β (Additive.ofMul (w : V))), fun i => by
      rw [← hM]
      have h1 := hβ (h⁻¹ * g i * h) (Additive.ofMul (w : V))
      rw [repOf4_apply, ← fL4_apply, w.2 _ (hB i), map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply] at h1
      have h2 := congrArg (ρ' h) h1
      rw [hρh'] at h2
      exact h2.symm⟩
  have hF : Function.Injective F := by
    intro w w' hww'
    have h1 : ρ' h (β (Additive.ofMul (w : V))) = ρ' h (β (Additive.ofMul (w' : V))) :=
      congrArg Subtype.val hww'
    have h2 := congrArg (ρ' h⁻¹) h1
    rw [hρh, hρh] at h2
    exact Subtype.ext (Additive.ofMul.injective (β.injective h2))
  calc Nat.card (fixV B) ≤ Nat.card {v : Fin n → ZMod 2 // ∀ i, M i *ᵥ v = v} :=
        Nat.card_le_card_of_injective F hF
    _ ≤ Nat.card (ZMod 2) ^ (n - r) := card_fixed_le hr
    _ = 2 ^ (n - r) := by rw [Nat.card_zmod]

theorem card_V_eq14 (β : Additive V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2)) : Nat.card V = 2 ^ 14 := by
  rw [show Nat.card V = Nat.card (Additive V) from rfl, Nat.card_congr β.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rfl

theorem pow_le_index14 {β : Additive V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = rep14 g (β w)) {B : Subgroup (MulAut V)} {m r : ℕ}
    (c : Fin m → Fin 64) (hc : ∀ i, up4 (c i) * up4 (c i) = 1) (h : G4)
    (hB : ∀ i, fL4 e (h⁻¹ * uOf (c i) * h) ∈ B)
    (hr : r ≤ (stackMat fun i => mat14 (up4 (c i))).rank) (hr14 : r ≤ 14) :
    2 ^ r ≤ (fixV B).index := by
  have h1 := card_fixV_le_of_rank hβ (fun i => uOf (c i)) (fun i => mat14 (up4 (c i)))
    (fun i v => rep14_uOf (c i) (hc i) v) h hB hr
  have h2 := (fixV B).index_mul_card
  rw [card_V_eq14 β] at h2
  have h3 : 2 ^ r * 2 ^ (14 - r) = 2 ^ 14 := by
    rw [← pow_add]
    congr 1
    omega
  have h4 : 2 ^ r * 2 ^ (14 - r) ≤ (fixV B).index * 2 ^ (14 - r) := by
    rw [h3, ← h2]
    exact Nat.mul_le_mul_left _ h1
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

theorem pow_le_index14_inv {β : Additive V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = rep14 g (β w)) {B : Subgroup (MulAut V)} {b : G4}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbB : fL4 e b ∈ B) : 2 ^ 5 ≤ (fixV B).index := by
  obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0_4 hb2 hb1
  · have e1 : c⁻¹ * uOf 1 * c = b := by
      rw [← hc]
      group
    refine pow_le_index14 hβ ![1] (fun i => by fin_cases i; decide) c (fun i => ?_) rank14_inv1
      (by norm_num)
    fin_cases i
    rw [← e1] at hbB
    exact hbB
  · have e1 : c⁻¹ * uOf 18 * c = b := by
      rw [← hc]
      group
    refine pow_le_index14 hβ ![18] (fun i => by fin_cases i; decide) c (fun i => ?_)
      rank14_inv18 (by norm_num)
    fin_cases i
    rw [← e1] at hbB
    exact hbB

end Coords

variable [Finite V] [Module (ZMod 2) (Additive V)]

theorem false_of_rep14 (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {β : Additive V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = rep14 g (β w)) (hA : IsA2 G A)
    (h2F : (fixV A).index ≤ Nat.card A ^ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAG : A ≤ G := hA.1
  have hel : IsElemAbelian2 A := hA.2.2
  have hcS := comm_of_comap4 (e := e) hel
  have h2S := sq_of_comap4 (e := e) hel
  have hcardA := card_le_two_mul_comap4 hHyp hZ e hAG
  set S := A.comap (fL4 e) with hS
  have hcontra : ∀ {r n : ℕ}, 2 ^ r ≤ (fixV A).index → Nat.card A ≤ n → n ^ 2 < 2 ^ r →
      False := by
    intro r n h1 h2 h3
    have := Nat.pow_le_pow_left h2 2
    omega
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S).exists_card_eq
  by_cases hk0 : k = 0
  · subst hk0
    have hAL : ¬ A ≤ L := by
      intro hAL
      apply hA.2.1
      have h1 := card_comap4_eq e hAL
      rw [← hS, hk, pow_zero] at h1
      exact Subgroup.card_eq_one.1 h1.symm
    obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    have hA2 : Nat.card A ≤ 2 := by rw [hk, pow_zero] at hcardA; omega
    have ha₀2 : a₀ * a₀ = 1 := by rw [← pow_two]; exact hel.2 a₀ ha₀
    obtain ⟨x, hx2, hx1, hxi⟩ := exists_inv_of_outer hHyp hZ e (hAG ha₀) ha₀L ha₀2
    have hB0 : (fixV (Subgroup.zpowers a₀)).index ≤ 4 := by
      refine (index_fixV_mono ((Subgroup.zpowers_le).2 ha₀)).trans (h2F.trans ?_)
      calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hA2 2
        _ = 4 := by norm_num
    have h3 := hxi.trans (Nat.pow_le_pow_left hB0 2)
    have h4 := pow_le_index14_inv hβ hx2 hx1 (Subgroup.mem_zpowers (fL4 e x))
    have h5 : (4 : ℕ) ^ 2 < 2 ^ 5 := by norm_num
    omega
  by_cases hk1 : k = 1
  · subst hk1
    have hSne : S ≠ ⊥ := by
      intro h0
      have h1 : Nat.card S = 1 := Subgroup.card_eq_one.2 h0
      rw [hk] at h1
      norm_num at h1
    obtain ⟨⟨b, hbS⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hSne
    have hb1' : b ≠ 1 := fun h0 => hb1 (by subst h0; rfl)
    have hA4 : Nat.card A ≤ 4 := by rw [hk] at hcardA; omega
    exact hcontra (pow_le_index14_inv hβ (h2S b hbS) hb1' hbS) hA4 (by norm_num)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨h, hh⟩ := exists_conj_le_U4 (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S)
  set T := codesOf S h with hTdef
  have hT : IsCodeGroup T := isCodeGroup_codesOf hcS h2S
  have hTc : T.card = 2 ^ k := by rw [card_codesOf hh, hk]
  have hmemA : ∀ c ∈ T, fL4 e (h⁻¹ * uOf c * h) ∈ A := fun c hc => mem_codesOf.1 hc
  have hk4 : k ≤ 4 := by
    by_contra hk4
    have h32 : 32 ≤ T.card := by
      rw [hTc]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (codes_q4 hT (by omega)).1
    omega
  have hA16 : Nat.card A ≤ 16 := by
    by_cases hk4' : k = 4
    · have hAL : A ≤ L := le_of_codes16 hHyp hZ e hAG hel hT (by rw [hTc, hk4']; norm_num)
      rw [← card_comap4_eq e hAL, ← hS, hk, hk4']
      norm_num
    · have : 2 ^ k ≤ 8 := by
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      rw [hk] at hcardA
      omega
  have h4T : 4 ≤ T.card := by
    rw [hTc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  by_cases htv : ∃ x ∈ T, x ∈ tvL
  · by_cases hntv : ∃ y ∈ T, y ∈ ntvL
    ·
      obtain ⟨x, hxT, hx⟩ := htv
      obtain ⟨y, hyT, hy⟩ := hntv
      obtain ⟨D, r, hDx, hDy⟩ :=
        exists_of_pairGood (pairTab4_spec x hx y hy (hT.comm x hxT y hyT))
      fin_cases r
      · refine hcontra (pow_le_index14 hβ ![2, 12] (fun i => by fin_cases i <;> decide) (D * h)
          (fun i => ?_) rank14_mix0 (by norm_num)) hA16 (by norm_num)
        fin_cases i
        · exact (conj_pair (f := 2) hDx).symm ▸ hmemA x hxT
        · exact (conj_pair (f := 12) hDy).symm ▸ hmemA y hyT
      · refine hcontra (pow_le_index14 hβ ![1, 33] (fun i => by fin_cases i <;> decide) (D * h)
          (fun i => ?_) rank14_mix1 (by norm_num)) hA16 (by norm_num)
        fin_cases i
        · exact (conj_pair (f := 1) hDx).symm ▸ hmemA x hxT
        · exact (conj_pair (f := 33) hDy).symm ▸ hmemA y hyT
    ·
      push Not at hntv
      have hall : ∀ c ∈ T, c ≠ 0 → c ∈ tvL := fun c hc hc0 =>
        (hT.inv_cases hc hc0).resolve_right (hntv c hc)
      by_cases hAL : A ≤ L
      · have hSA : Nat.card S = Nat.card A := card_comap4_eq e hAL
        by_cases hk2' : k = 2
        · subst hk2'
          obtain ⟨x, hxT, -, -, hx0, -, -⟩ := exists_two_codes h4T
          have hb1 : h⁻¹ * uOf x * h ≠ 1 := by
            intro h0
            apply hx0
            have : uOf x = 1 := by
              calc uOf x = h * (h⁻¹ * uOf x * h) * h⁻¹ := by group
                _ = 1 := by rw [h0]; group
            rw [← code4_up4 x]
            exact (congrArg (fun g : G4 => code4 (g : 𝕄₄)) this).trans (by decide)
          exact hcontra (pow_le_index14_inv hβ (h2S _ (mem_codesOf.1 hxT)) hb1 (hmemA x hxT))
            (n := 4) (by rw [← hSA, hk]; norm_num) (by norm_num)
        by_cases hk3 : k = 3
        · subst hk3
          have h8 : T.card = 8 := by rw [hTc]; norm_num
          have hA8 : Nat.card A ≤ 8 := by rw [← hSA, hk]; norm_num
          rcases codes_regular hT h8 hall with ⟨a, b, c⟩ | ⟨a, b, c⟩
          · refine hcontra (pow_le_index14 hβ ![1, 2, 4] (fun i => by fin_cases i <;> decide) h
              (fun i => ?_) rank14_reg0 (by norm_num)) hA8 (by norm_num)
            fin_cases i
            · exact hmemA _ a
            · exact hmemA _ b
            · exact hmemA _ c
          · refine hcontra (pow_le_index14 hβ ![4, 16, 32] (fun i => by fin_cases i <;> decide)
              h (fun i => ?_) rank14_reg1 (by norm_num)) hA8 (by norm_num)
            fin_cases i
            · exact hmemA _ a
            · exact hmemA _ b
            · exact hmemA _ c
        · have hk4' : k = 4 := by omega
          subst hk4'
          have := (codes_q4 hT (by rw [hTc]; norm_num)).2.2
          exact absurd (hntv 18 this) (by decide)
      · obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
        obtain ⟨P, hP⟩ := exists_conjG4_eq hHyp hZ e (hAG ha₀) ha₀L
        have hfix := conjG4_fix hHyp e hel ha₀ (hAG ha₀)
        obtain ⟨x, hxT, y, hyT, hx0, hy0, hxy⟩ := exists_two_codes h4T
        exact not_fixed_compat hP h (hall x hxT hx0) (hall y hyT hy0) hxy (hT.comm x hxT y hyT)
          (hall _ (hT.mul_mem x hxT y hyT) (code_mul_ne_zero (hT.sq y hyT) hxy))
          (hfix _ (mem_codesOf.1 hxT)) (hfix _ (mem_codesOf.1 hyT))
  ·
    push Not at htv
    have hall : ∀ c ∈ T, c ≠ 0 → c ∈ ntvL := fun c hc hc0 =>
      (hT.inv_cases hc hc0).resolve_left (htv c hc)
    by_cases hk2' : k = 2
    · subst hk2'
      obtain ⟨x, hxT, y, hyT, hx0, hy0, hxy⟩ := exists_two_codes h4T
      have hA8 : Nat.card A ≤ 8 := by rw [hk] at hcardA; omega
      obtain ⟨D, r, hDx, hDy⟩ := exists_of_pairGood (pairTab0_spec x (hall x hxT hx0) y
        (hall y hyT hy0) hxy (hT.comm x hxT y hyT)
        (hall _ (hT.mul_mem x hxT y hyT) (code_mul_ne_zero (hT.sq y hyT) hxy)))
      fin_cases r
      · refine hcontra (pow_le_index14 hβ ![12, 22] (fun i => by fin_cases i <;> decide) (D * h)
          (fun i => ?_) rank14_ntv0 (by norm_num)) hA8 (by norm_num)
        fin_cases i
        · exact (conj_pair (f := 12) hDx).symm ▸ hmemA x hxT
        · exact (conj_pair (f := 22) hDy).symm ▸ hmemA y hyT
      · refine hcontra (pow_le_index14 hβ ![18, 33] (fun i => by fin_cases i <;> decide) (D * h)
          (fun i => ?_) rank14_ntv1 (by norm_num)) hA8 (by norm_num)
        fin_cases i
        · exact (conj_pair (f := 18) hDx).symm ▸ hmemA x hxT
        · exact (conj_pair (f := 33) hDy).symm ▸ hmemA y hyT
    · by_cases hk3 : k = 3
      · subst hk3
        exact codes_not_ntv hT (by rw [hTc]; norm_num) hall
      · have hk4' : k = 4 := by omega
        subst hk4'
        have := (codes_q4 hT (by rw [hTc]; norm_num)).2.1
        exact absurd (htv 4 this) (by decide)

end CFSG.Quasithin.B45Ln

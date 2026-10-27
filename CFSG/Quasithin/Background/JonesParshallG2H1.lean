module

public import CFSG.Quasithin.Background.JonesParshallG2Torus
public import CFSG.Quasithin.Background.JonesParshallSp4H1
public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.Quasithin.Background.JonesParshallG2Cocycle

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem diag3_mul_transvection {a b e : F} (h : a * b * e = 1) {i j : Fin 3} (hij : i ≠ j)
    (hd : ![a, b, e] i = ![a, b, e] j) (x : F) :
    diag3 a b e h * transvection hij x = transvection hij x * diag3 a b e h := by
  have hc := sl3Diag_conj_transvection (d := ![a, b, e]) (by simpa using h) hij x
  have hne : ![a, b, e] j ≠ 0 := sl3Diag_ne_zero (d := ![a, b, e]) (by simpa using h) j
  have hx : ![a, b, e] j * x * (![a, b, e] j)⁻¹ = x := by field_simp
  rw [hd, hx] at hc
  have hD : sl3Diag ![a, b, e] (by simpa using h) = diag3 a b e h := rfl
  rw [hD] at hc
  calc diag3 a b e h * transvection hij x =
      (diag3 a b e h * transvection hij x * (diag3 a b e h)⁻¹) * diag3 a b e h := by group
    _ = transvection hij x * diag3 a b e h := by rw [hc]

namespace TEquiv

variable {ψ : ↥(cayleyGroup F) → (Ix3 → F)} (hψ : TEquiv ψ)
include hψ

theorem fix_torus {a b e : F} (h : a * b * e = 1) {g : ↥(cayleyGroup F)}
    (hc : g2A (diag3 a b e h) * g = g * g2A (diag3 a b e h)) :
    g2Act (g2A (diag3 a b e h)) (ψ g) = ψ g := by
  have ha : a ≠ 0 := fun h0 => by simp [h0] at h
  have hb : b ≠ 0 := fun h0 => by simp [h0] at h
  have hT : g2T (Units.mk0 a ha, Units.mk0 b hb) = g2A (diag3 a b e h) := by
    rw [g2T_apply]
    congr 1
    refine diag3_congr rfl rfl ?_
    simp only [Units.val_mk0]
    have he : e = (a * b)⁻¹ := (eq_inv_of_mul_eq_one_right h)
    exact he.symm
  rw [← hT] at hc ⊢
  exact hψ.conj_fix hc

theorem transvection_eq_zero {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {i j : Fin 3} (hij : i ≠ j)
    (x : F) : ψ (g2A (transvection hij x)) = 0 := by
  have hcc : c * c ≠ 1 := by rw [← sq]; exact sq_ne_one hc1
  have hci : c * (c * c)⁻¹ = c⁻¹ := by field_simp
  have hcc' : (c * c)⁻¹ * c = c⁻¹ := by field_simp
  have key : ∀ {a b e : F} (h : a * b * e = 1), ![a, b, e] i = ![a, b, e] j → a ≠ 1 → b ≠ 1 →
      e ≠ 1 → b * e ≠ 1 → a * e ≠ 1 → a * b ≠ 1 → ψ (g2A (transvection hij x)) = 0 := by
    intro a b e h hd h1 h2 h3 h4 h5 h6
    refine fixed_eq_zero h h1 h2 h3 h4 h5 h6 (hψ.fix_torus h ?_)
    rw [← map_mul, ← map_mul, diag3_mul_transvection h hij hd]
  have hx : c⁻¹ ≠ 1 := inv_ne_one' hc1
  have hy : (c * c)⁻¹ ≠ 1 := inv_ne_one' hcc
  fin_cases i <;> fin_cases j <;> simp at hij
  · exact key (a := c) (b := c) (e := (c * c)⁻¹) (by field_simp) rfl hc1 hc1 hy
      (by rw [hci]; exact hx) (by rw [hci]; exact hx) hcc
  · exact key (a := c) (b := (c * c)⁻¹) (e := c) (by field_simp) rfl hc1 hy hc1
      (by rw [hcc']; exact hx) hcc (by rw [hci]; exact hx)
  · exact key (a := c) (b := c) (e := (c * c)⁻¹) (by field_simp) rfl hc1 hc1 hy
      (by rw [hci]; exact hx) (by rw [hci]; exact hx) hcc
  · exact key (a := (c * c)⁻¹) (b := c) (e := c) (by field_simp) rfl hy hc1 hc1 hcc
      (by rw [hcc']; exact hx) (by rw [hcc']; exact hx)
  · exact key (a := c) (b := (c * c)⁻¹) (e := c) (by field_simp) rfl hc1 hy hc1
      (by rw [hcc']; exact hx) hcc (by rw [hci]; exact hx)
  · exact key (a := (c * c)⁻¹) (b := c) (e := c) (by field_simp) rfl hy hc1 hc1 hcc
      (by rw [hcc']; exact hx) (by rw [hcc']; exact hx)

theorem g2A_eq_zero {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (A : SL3 F) : ψ (g2A A) = 0 := by
  refine diagonal_transvection_induction' (fun M => ψ (g2A M) = 0) A
    (fun i j hij a ha => ?_) (fun i j hij a => hψ.transvection_eq_zero hc0 hc1 hij a)
    (fun M N hM hN => ?_)
  · set d : Fin 3 → F := fun k => if k = i then a else if k = j then a⁻¹ else 1 with hd
    have hp : d 0 * d 1 * d 2 = 1 := by
      fin_cases i <;> fin_cases j <;> simp at hij <;> simp [hd, ha]
    have h0 := sl3Diag_ne_zero hp 0
    have h1 := sl3Diag_ne_zero hp 1
    have e : diag2n hij a ha = (sl3Torus (Units.mk0 (d 0) h0, Units.mk0 (d 1) h1) : SL3 F) := by
      apply Subtype.ext
      change diagonal d = diagonal ![d 0, d 1, (d 0 * d 1)⁻¹]
      congr 1
      funext k
      fin_cases k
      · rfl
      · rfl
      · change d 2 = (d 0 * d 1)⁻¹
        exact eq_inv_of_mul_eq_one_right hp
    change ψ (g2A (diag2n hij a ha)) = 0
    rw [e]
    exact hψ.torus_eq_zero hc0 hc1 _
  · rw [map_mul, hψ.1, hM, hN, map_zero, add_zero]

theorem g2X_e0_eq {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ψ (g2X ![1, 0, 0]) = q6 (ψ (g2X ![1, 0, 0]) (.inl 0)) 0 0 0 0 0 := by
  have h1 : (1 : F) * c * c⁻¹ = 1 := by field_simp
  have hcomm : g2A (diag3 1 c c⁻¹ h1) * g2X ![1, 0, 0] =
      g2X ![1, 0, 0] * g2A (diag3 1 c c⁻¹ h1) := by
    rw [g2A_mul_g2X]
    congr 2
    funext i
    fin_cases i <;> simp [diag3, mulVec, dotProduct, Fin.sum_univ_three]
  have hfix := hψ.fix_torus h1 hcomm
  rw [q6_eta (ψ (g2X ![1, 0, 0])), g2Act_diag3] at hfix
  obtain ⟨-, k1, k2, -, k4, k5⟩ := q6_inj hfix
  have z : ∀ {x y : F}, x ≠ 1 → x * y = y → y = 0 := fun {x y} hx hxy => by
    have : (x - 1) * y = 0 := by linear_combination hxy
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx)
  have hu1 := z hc1 k1
  have hu2 := z (inv_ne_one' hc1) k2
  have hv1 := z (by rw [one_mul]; exact inv_ne_one' hc1) k4
  have hv2 := z (by rw [one_mul]; exact hc1) k5
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hcomm' : g2A (transvection h01 1) * g2X ![1, 0, 0] =
      g2X ![1, 0, 0] * g2A (transvection h01 (1 : F)) := by
    rw [g2A_mul_g2X]
    congr 2
    funext i
    fin_cases i <;> simp [transvection_coe, mulVec, dotProduct, Fin.sum_univ_three, single_apply]
  have hfix' := fix_of_commute hψ.1 hcomm' (hψ.g2A_eq_zero hc0 hc1 _)
  rw [q6_eta (ψ (g2X ![1, 0, 0])), hu1, hu2, hv1, hv2, g2Act_g2A] at hfix'
  obtain ⟨-, -, -, -, k4', -⟩ := q6_inj hfix'
  have hv0 : ψ (g2X ![1, 0, 0]) (.inr 0) = 0 := by
    simp [transvection_coe, adjugate_fin_three] at k4'
    linear_combination k4'
  rw [q6_eta (ψ (g2X ![1, 0, 0])), hu1, hu2, hv0, hv1, hv2]
  rfl

end TEquiv

theorem fG_conj_torus (s : Fˣ × Fˣ) (g : ↥(cayleyGroup F)) :
    fG (g2T s * g * (g2T s)⁻¹) = g2Act (g2T s) (fG g) := by
  rw [Z1A_conj fG_mem, g2T_apply, fG_g2A, map_zero, add_zero, sub_zero]

theorem g2Y_conj_e1 {b : Fin 3 → F} (hb : b ≠ 0) :
    ∃ B : SL3 F, g2Y b = g2A B * g2Y ![0, 1, 0] * (g2A B)⁻¹ := by
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
  set M : SL3 F := B * sl3P
  refine ⟨invTransposeFun M, ?_⟩
  have hM : (adjugate ((invTransposeFun M : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ =
      (M : Matrix (Fin 3) (Fin 3) F) := by
    change (adjugate ((M⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ)ᵀ = _
    rw [← adjugate_transpose, transpose_transpose]
    change adjugate (adjugate (M : Matrix (Fin 3) (Fin 3) F)) = _
    rw [adjugate_adjugate _ (by simp), M.2]
    simp
  rw [g2A_mul_g2Y, mul_inv_cancel_right, hM]
  congr 1
  rw [← hB]
  change (B : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 =
    ((B : Matrix (Fin 3) (Fin 3) F) * ((sl3P : SL3 F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ ![0, 1, 0]
  rw [← mulVec_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [sl3P, e0, mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_sub_fG_mem_B1A {a : ℕ} [Fintype F] (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {f : ↥(cayleyGroup F) → (Ix3 → F)} (hf : f ∈ Z1A (g2Act (F := F))) :
    ∃ α : F, f - α • fG ∈ B1A (g2Act (F := F)) := by
  classical
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hF ha
  have h2 : ∀ m : Ix3 → F, m + m = 0 := fun m => funext fun i => CharTwo.add_self_eq_zero (m i)
  have hodd : Odd (Fintype.card (Fˣ × Fˣ)) := by
    rw [Fintype.card_prod, Fintype.card_units, hF]
    obtain ⟨k, hk⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    have : Odd (2 ^ a - 1) := by
      rw [hk, pow_succ]
      exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
    exact this.mul this
  obtain ⟨ψ, hψ, hfψ, heq⟩ := exists_equivariant g2T hodd h2 hf
  have hT : TEquiv ψ := ⟨hψ, heq⟩
  set α := ψ (g2X ![1, 0, 0]) (.inl 0) with hα
  set ψ' := ψ - α • fG with hψ'
  have hT' : TEquiv ψ' := by
    refine ⟨sub_mem hψ (smul_fG_mem α), fun s g => ?_⟩
    rw [hψ', Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, heq, fG_conj_torus,
      map_sub, g2Act_smul]
  have hx : ψ' (g2X ![1, 0, 0]) = 0 := by
    rw [hψ', Pi.sub_apply, Pi.smul_apply, hT.g2X_e0_eq hc0 hc1, fG_g2X, q6_smul, q6_sub,
      ← q6_zero]
    apply q6_congr <;> simp [hα]
  have hA : ∀ A : SL3 F, ψ' (g2A A) = 0 := hT'.g2A_eq_zero hc0 hc1
  have hn : ψ' gN = 0 := hT'.gN_eq_zero hc0 hc1
  have hy : ψ' (g2Y ![0, 1, 0]) = 0 := by
    rw [← gN_conj_g2X, Z1A_conj hT'.1, hx, hn, map_zero, map_zero, zero_add, sub_zero]
  set V := vanishSubgroup hT'.1
  have hV : ∀ g : ↥(cayleyGroup F), ψ' g = 0 → g ∈ V := fun g h => h
  have hgens : gensG2 F ⊆ V.map (cayleyGroup F).subtype := by
    rintro g (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
    · refine ⟨g2X b, ?_, rfl⟩
      by_cases hb : b = 0
      · subst hb
        rw [g2X_zero]
        exact V.one_mem
      obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
      have e : g2X b = g2A B * g2X ![1, 0, 0] * (g2A B)⁻¹ := by
        rw [g2A_mul_g2X, mul_inv_cancel_right]
        congr 1
        exact hB.symm
      rw [e]
      exact V.mul_mem (V.mul_mem (hV _ (hA B)) (hV _ hx)) (V.inv_mem (hV _ (hA B)))
    · refine ⟨g2Y b, ?_, rfl⟩
      by_cases hb : b = 0
      · subst hb
        rw [g2Y_zero]
        exact V.one_mem
      obtain ⟨B, e⟩ := g2Y_conj_e1 hb
      rw [e]
      exact V.mul_mem (V.mul_mem (hV _ (hA B)) (hV _ hy)) (V.inv_mem (hV _ (hA B)))
    · exact ⟨g2A A, hV _ (hA A), rfl⟩
  have hall : ∀ g : ↥(cayleyGroup F), ψ' g = 0 := by
    intro g
    have hg : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ V.map (cayleyGroup F).subtype := by
      have hle : cayleyGroup F ≤ V.map (cayleyGroup F).subtype :=
        (cayleyGroup_eq_closure (F := F)).le.trans ((Subgroup.closure_le _).mpr hgens)
      exact hle g.2
    obtain ⟨g', hg', hgg⟩ := hg
    have : g' = g := Subtype.ext hgg
    rw [← this]
    exact hg'
  refine ⟨α, ?_⟩
  have e : f - α • fG = f - ψ := by
    funext g
    have := hall g
    rw [hψ', Pi.sub_apply, sub_eq_zero] at this
    rw [Pi.sub_apply, Pi.sub_apply, ← this]
  rw [e]
  exact hfψ

theorem g2Act_g2X_inl0 (t : F) (w : Ix3 → F) :
    g2Act (g2X (t • ![1, 0, 0])) w (.inl 0) = w (.inl 0) + t * t * w (.inr 0) := by
  rw [g2Act_apply]
  change zP (xaFun _ (zI w)) (.inl 0) = _
  rw [q6_eta w, zI_q6, xaFun_zmk, zP_zmk]
  simp [q6]
  ring

theorem eq_zero_of_smul_fG_mem_B1A {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {α : F}
    (h : α • fG ∈ B1A (g2Act (F := F))) : α = 0 := by
  obtain ⟨v, hv⟩ := h
  have key : ∀ t : F, α * t = t * t * v (.inr 0) := fun t => by
    have h1 := congrFun (congrFun hv (g2X (t • ![1, 0, 0]))) (.inl 0)
    rw [coboundaryA_apply, Pi.sub_apply, g2Act_g2X_inl0, Pi.smul_apply, fG_g2X] at h1
    simp [q6] at h1
    linear_combination -h1
  have k1 := key 1
  have k2 := key c
  rw [one_mul, mul_one, one_mul] at k1
  rw [← k1] at k2
  have : α * (c * (c - 1)) = 0 := by linear_combination -k2
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc0
    · exact absurd (sub_eq_zero.mp h) hc1

theorem card_Z1A_g2Act {a : ℕ} [Fintype F] (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) :
    Nat.card (Z1A (g2Act (F := F))) = Fintype.card F * Nat.card (B1A (g2Act (F := F))) := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hF ha
  let Φ : F × B1A (g2Act (F := F)) → Z1A (g2Act (F := F)) := fun p =>
    ⟨p.1 • fG + (p.2 : ↥(cayleyGroup F) → (Ix3 → F)),
      add_mem (smul_fG_mem p.1) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨B, b⟩ ⟨B', b'⟩ h
      have h' : B • fG (F := F) + (b : ↥(cayleyGroup F) → (Ix3 → F)) = B' • fG (F := F) + b' := by
        simpa [Φ] using congrArg Subtype.val h
      have hBB : (B - B') • (fG : ↥(cayleyGroup F) → (Ix3 → F)) ∈ B1A (g2Act (F := F)) := by
        have : (B - B') • (fG : ↥(cayleyGroup F) → (Ix3 → F)) =
            (b' : ↥(cayleyGroup F) → (Ix3 → F)) - b := by
          calc (B - B') • (fG : ↥(cayleyGroup F) → (Ix3 → F)) =
              (B • fG (F := F) + (b : ↥(cayleyGroup F) → (Ix3 → F))) - (B' • fG (F := F) + b) := by
                rw [sub_smul]
                abel
            _ = (B' • fG (F := F) + b') - (B' • fG (F := F) + b) := by rw [h']
            _ = b' - b := by abel
        rw [this]
        exact sub_mem b'.2 b.2
      have hB : B = B' := sub_eq_zero.mp (eq_zero_of_smul_fG_mem_B1A hc0 hc1 hBB)
      subst hB
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      obtain ⟨B, hB⟩ := exists_sub_fG_mem_B1A hF ha hf
      exact ⟨(B, ⟨_, hB⟩), Subtype.ext (by simp [Φ])⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_eq_fintype_card]

end CFSG.Quasithin.JonesParshall

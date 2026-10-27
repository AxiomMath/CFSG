module

public import CFSG.Quasithin.Background.RonanD37Flag
public import CFSG.Quasithin.Background.SmithD37Orth

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37

variable {U : Type} [CommGroup U] [Finite U] {X L₁ L₂ : Subgroup (MulAut U)} {s : MulAut U}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem le_of_two_pow_le {x y : ℕ} (h : 2 ^ x ≤ 2 ^ y) : x ≤ y :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem rk_top_eq {d n : ℕ} (Mm : MatModel L₁ L₂ F d) (hF : Nat.card F = 2 ^ n) :
    rk U = d * d * n := by
  unfold rk
  rw [natCard_eq_of_matModel Mm, hF, ← pow_mul, padicValNat.prime_pow]
  ring

theorem card_fixV_eq (hU : ∀ u : U, u ^ 2 = 1) (B : Subgroup (MulAut U)) :
    Nat.card ↥(fixV B) = 2 ^ rk ↥(fixV B) := card_eq_two_pow hU _

theorem cent_inf_cent_eq_bot {d : ℕ} (Mm : MatModel L₁ L₂ F d) {B : Subgroup (MulAut U)}
    (hE : IsElemAbelian2 B) :
    (B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U))) ⊓
      (B ⊓ Subgroup.centralizer (L₂ : Set (MulAut U))) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_comm Mm (fun l hl => (Subgroup.mem_centralizer_iff.mp hx.1.2 l hl).symm)
    (fun k hk => (Subgroup.mem_centralizer_iff.mp hx.2.2 k hk).symm) (e := 1)
    (by rw [pow_one]; exact hE.2 x hx.1.1)

theorem exists_not_comm_of_card_lt {B : Subgroup (MulAut U)} {L : Subgroup (MulAut U)}
    (h : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set (MulAut U))) < Nat.card B) :
    ∃ a ∈ B, ∃ l ∈ L, a * l ≠ l * a := by
  by_contra hcon
  push Not at hcon
  have hle : B ≤ B ⊓ Subgroup.centralizer (L : Set (MulAut U)) := fun b hb =>
    ⟨hb, Subgroup.mem_centralizer_iff.mpr fun l hl => (hcon b hb l hl).symm⟩
  exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr h)

theorem card_fixV_mul_le_of_cent_two
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hL : IsPSL 2 2 n ↥L₁) {B : Subgroup (MulAut U)}
    (hE : IsElemAbelian2 B) (hPN : ∀ a ∈ B, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (hK : B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) ≠ ⊥) :
    Nat.card ↥(fixV B) * Nat.card B ≤
      Nat.card F ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U))) := by
  set K := B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) with hKdef
  have hnc₁ := Mm.not_comm (by norm_num)
  obtain ⟨Y₀, hY₀⟩ := exists_fixV_eq_rowSub Mm (K := K)
    (fun c hc l hl => (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm)
  have hlt := finrank_lt_of_ne_bot Mm hK hY₀
  have hinv : IsInvBy B (rowSub Mm Y₀) := by
    rw [← hY₀]
    exact isInvBy_fixV_of_comm fun b hb c hc => hE.1 b hb c hc.1
  have hsub : fixV B ≤ rowSub Mm Y₀ := hY₀ ▸ fixV_anti inf_le_left
  have hinf : rowSub Mm Y₀ ⊓ fixV B = fixV B := inf_eq_right.mpr hsub
  have hrk := card_le_mul_cent_psl Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE hPN
  rcases (by omega : Module.finrank F Y₀ = 0 ∨ Module.finrank F Y₀ = 1) with h0 | h1
  · have hY : Y₀ = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [hY, rowSub_bot] at hsub
    have hf : Nat.card ↥(fixV B) = 1 := by
      rw [le_bot_iff.mp hsub, Subgroup.card_bot]
    rw [hf, one_mul]
    calc Nat.card B ≤ 2 ^ n * Nat.card K := hrk
      _ ≤ Nat.card F ^ 2 * Nat.card K := by
        apply Nat.mul_le_mul_right
        rw [hF]
        exact Nat.le_self_pow (by norm_num) _
  · have h := card_fixV_flag Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE hPN 1 Y₀ h1 hinv
    rw [hinf, pow_one, pow_one, mul_one] at h
    exact h

theorem norm_two
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hL : IsPSL 2 2 n ↥L₁) {B : Subgroup (MulAut U)} (hB : IsA2 X B)
    (hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    3 * rk B ≤ 2 * rkIdx (fixV B) ∧ (3 * rk B = 2 * rkIdx (fixV B) → rk B = 2 * n) := by
  have hE := hB.2.2
  have hPN₁ : ∀ a ∈ B, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer (hBN a ha) hl
  have hBN₂ : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₂ : Set (MulAut U)) := fun b hb =>
    hC.mem_normalizer₂ (hB.1 hb) (hBN b hb)
  have hPN₂ : ∀ a ∈ B, ∀ k ∈ L₂, a * k * a⁻¹ ∈ L₂ := fun a ha k hk =>
    mul_mem_of_mem_normalizer (hBN₂ a ha) hk
  have hC' := hC.swap
  have hL₂ : IsPSL 2 2 n ↥L₂ := isPSL_transfer hC.equiv.symm hL
  have hnc₁ := Mm.not_comm (by norm_num)
  have hnc₂ := Mm.swap.not_comm (by norm_num)
  have hrank : Module.finrank F (⊤ : Submodule F (Fin 2 → F)) = 2 := by
    rw [finrank_top, Module.finrank_fin_fun]
  have htop : IsInvBy B (⊤ : Subgroup U) := fun _ _ _ _ => Subgroup.mem_top _
  have hflag₁ := card_fixV_flag Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE hPN₁ 2 ⊤ hrank
    (by rw [rowSub_top]; exact htop)
  have hflag₂ := card_fixV_flag Mm.swap (by norm_num) hC'.simple hnc₂ hC'.sqtk hL₂ hE hPN₂ 2 ⊤
    hrank (by rw [rowSub_top]; exact htop)
  rw [rowSub_top, top_inf_eq] at hflag₁ hflag₂
  have hrk₁ := card_le_mul_cent_psl Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE hPN₁
  have hrk₂ := card_le_mul_cent_psl Mm.swap (by norm_num) hC'.simple hnc₂ hC'.sqtk hL₂ hE hPN₂
  set K := B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) with hKdef
  set K' := B ⊓ Subgroup.centralizer (L₂ : Set (MulAut U)) with hK'def
  have hprod := card_mul_card_le_of_inf_eq_bot (inf_le_left : K ≤ B) (inf_le_left : K' ≤ B)
    (cent_inf_cent_eq_bot Mm hE)
  have h4 : K ≠ ⊥ → Nat.card ↥(fixV B) * Nat.card B ≤ Nat.card F ^ 2 * Nat.card K :=
    card_fixV_mul_le_of_cent_two hC Mm hF hL hE hPN₁
  have h4' : K' ≠ ⊥ → Nat.card ↥(fixV B) * Nat.card B ≤ Nat.card F ^ 2 * Nat.card K' :=
    card_fixV_mul_le_of_cent_two hC' Mm.swap hF hL₂ hE hPN₂
  have hU := hC.exp
  have hB2 : IsPGroup 2 ↥B := hE.isPGroup
  have hcB := card_eq_two_pow_of_isPGroup hB2
  have hcK := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : K ≤ B))
  have hcK' := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : K' ≤ B))
  have hcf := card_fixV_eq hU B
  have hidx := rk_add_rkIdx (fixV B)
  rw [rk_top_eq Mm hF] at hidx
  have ha : 1 ≤ rk B := by
    rcases Nat.eq_zero_or_pos (rk B) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hB2).mp h) hB.2.1
    · exact h
  have hKbot : ∀ {H : Subgroup (MulAut U)}, IsPGroup 2 ↥H → (H ≠ ⊥ ↔ 1 ≤ rk H) := by
    intro H hH
    constructor
    · intro hne
      rcases Nat.eq_zero_or_pos (rk H) with h | h
      · exact absurd ((rk_eq_zero_iff_of_isPGroup hH).mp h) hne
      · exact h
    · intro h1 hbot
      rw [(rk_eq_zero_iff_of_isPGroup hH).mpr hbot] at h1
      omega
  rw [hcB, hcK, hcf, hF] at hflag₁
  rw [hcB, hcK] at hrk₁
  rw [hcB, hcK', hcf, hF] at hflag₂
  rw [hcB, hcK'] at hrk₂
  rw [hcB, hcK, hcK'] at hprod
  set a := rk B
  set c := rk K
  set c' := rk K'
  set f := rk ↥(fixV B)
  have e1 : f + 2 * a ≤ 2 * 2 * n + 2 * c := by
    apply le_of_two_pow_le
    calc 2 ^ (f + 2 * a) = 2 ^ f * (2 ^ a) ^ 2 := by ring
      _ ≤ (2 ^ n) ^ (2 * 2) * (2 ^ c) ^ 2 := hflag₁
      _ = 2 ^ (2 * 2 * n + 2 * c) := by ring
  have e2 : f + 2 * a ≤ 2 * 2 * n + 2 * c' := by
    apply le_of_two_pow_le
    calc 2 ^ (f + 2 * a) = 2 ^ f * (2 ^ a) ^ 2 := by ring
      _ ≤ (2 ^ n) ^ (2 * 2) * (2 ^ c') ^ 2 := hflag₂
      _ = 2 ^ (2 * 2 * n + 2 * c') := by ring
  have e3 : a ≤ n + c := by
    apply le_of_two_pow_le
    calc 2 ^ a ≤ 2 ^ n * 2 ^ c := hrk₁
      _ = 2 ^ (n + c) := by ring
  have e4 : a ≤ n + c' := by
    apply le_of_two_pow_le
    calc 2 ^ a ≤ 2 ^ n * 2 ^ c' := hrk₂
      _ = 2 ^ (n + c') := by ring
  have e5 : c + c' ≤ a := by
    apply le_of_two_pow_le
    calc 2 ^ (c + c') = 2 ^ c * 2 ^ c' := by ring
      _ ≤ 2 ^ a := hprod
  have e6 : 1 ≤ c → f + a ≤ 2 * n + c := by
    intro hc
    have h := h4 ((hKbot (hB2.to_le (inf_le_left : K ≤ B))).mpr hc)
    rw [hcB, hcK, hcf, hF] at h
    apply le_of_two_pow_le
    calc 2 ^ (f + a) = 2 ^ f * 2 ^ a := by ring
      _ ≤ (2 ^ n) ^ 2 * 2 ^ c := h
      _ = 2 ^ (2 * n + c) := by ring
  have e7 : 1 ≤ c' → f + a ≤ 2 * n + c' := by
    intro hc
    have h := h4' ((hKbot (hB2.to_le (inf_le_left : K' ≤ B))).mpr hc)
    rw [hcB, hcK', hcf, hF] at h
    apply le_of_two_pow_le
    calc 2 ^ (f + a) = 2 ^ f * 2 ^ a := by ring
      _ ≤ (2 ^ n) ^ 2 * 2 ^ c' := h
      _ = 2 ^ (2 * n + c') := by ring
  constructor
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · omega
    rcases Nat.eq_zero_or_pos c' with hc' | hc'
    · omega
    have := e6 hc
    have := e7 hc'
    omega
  · intro heq
    rcases Nat.eq_zero_or_pos c with hc | hc
    · omega
    rcases Nat.eq_zero_or_pos c' with hc' | hc'
    · omega
    have := e6 hc
    have := e7 hc'
    omega

theorem card_fixV_le_of_cent_three (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    {B : Subgroup (MulAut U)} (hE : IsElemAbelian2 B) (hPN : ∀ a ∈ B, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (hK : B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) ≠ ⊥)
    (hnc : ∃ a ∈ B, ∃ l ∈ L₁, a * l ≠ l * a) :
    Nat.card ↥(fixV B) ≤ 16 := by
  set K := B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) with hKdef
  obtain ⟨Y₀, hY₀⟩ := exists_fixV_eq_rowSub Mm (K := K)
    (fun c hc l hl => (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm)
  have hlt := finrank_lt_of_ne_bot Mm hK hY₀
  have hinv : IsInvBy B (rowSub Mm Y₀) := by
    rw [← hY₀]
    exact isInvBy_fixV_of_comm fun b hb c hc => hE.1 b hb c hc.1
  have hsub : fixV B ≤ rowSub Mm Y₀ := hY₀ ▸ fixV_anti inf_le_left
  have hinf : rowSub Mm Y₀ ⊓ fixV B = fixV B := inf_eq_right.mpr hsub
  have h := card_fixV_flag_mul Mm hE.isPGroup hPN 2 (Nat.card F ^ 3)
    (fun Y' Y D hP hP' => card_fixV_range_mul_two_le Mm D hP hP' hPN hE.isPGroup hnc)
    _ Y₀ rfl hinv
  rw [hinf, hF] at h
  set k := Module.finrank F Y₀
  have hk : k ≤ 2 := by omega
  have h' : Nat.card ↥(fixV B) * 2 ^ k ≤ 4 ^ k * 2 ^ k := by
    calc Nat.card ↥(fixV B) * 2 ^ k ≤ (2 ^ 3) ^ k := h
      _ = 4 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  have h'' := Nat.le_of_mul_le_mul_right h' (by positivity)
  calc Nat.card ↥(fixV B) ≤ 4 ^ k := h''
    _ ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
    _ = 16 := by norm_num

theorem norm_three (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    {B : Subgroup (MulAut U)} (hB : IsA2 X B)
    (hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    5 * rk B ≤ 4 * rkIdx (fixV B) ∧ (5 * rk B = 4 * rkIdx (fixV B) → rk B = 4) := by
  have hE := hB.2.2
  have hPN₁ : ∀ a ∈ B, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer (hBN a ha) hl
  have hBN₂ : ∀ b ∈ B, b ∈ Subgroup.normalizer (L₂ : Set (MulAut U)) := fun b hb =>
    hC.mem_normalizer₂ (hB.1 hb) (hBN b hb)
  have hPN₂ : ∀ a ∈ B, ∀ k ∈ L₂, a * k * a⁻¹ ∈ L₂ := fun a ha k hk =>
    mul_mem_of_mem_normalizer (hBN₂ a ha) hk
  have h8 : Nat.card F ^ 3 = 8 := by rw [hF]; norm_num
  have hrank : Module.finrank F (⊤ : Submodule F (Fin 3 → F)) = 3 := by
    rw [finrank_top, Module.finrank_fin_fun]
  have htop : IsInvBy B (⊤ : Subgroup U) := fun _ _ _ _ => Subgroup.mem_top _
  set K := B ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) with hKdef
  set K' := B ⊓ Subgroup.centralizer (L₂ : Set (MulAut U)) with hK'def
  have hflag : ∀ (L L' : Subgroup (MulAut U)) (Mm' : MatModel L L' F 3)
      (hPN : ∀ a ∈ B, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hnc : ∃ a ∈ B, ∃ l ∈ L, a * l ≠ l * a),
      Nat.card ↥(fixV B) * 8 ≤ 512 := by
    intro L L' Mm' hPN hnc
    have h := card_fixV_flag_mul Mm' hE.isPGroup hPN 2 (Nat.card F ^ 3)
      (fun Y' Y D hP hP' => card_fixV_range_mul_two_le Mm' D hP hP' hPN hE.isPGroup hnc)
      3 ⊤ hrank (by rw [rowSub_top]; exact htop)
    rw [rowSub_top, top_inf_eq, h8] at h
    simpa using h
  have hrk₁ := card_le_mul_cent_eight Mm (by norm_num) h8 hE hPN₁
  have hrk₂ := card_le_mul_cent_eight Mm.swap (by norm_num) h8 hE hPN₂
  have hprod := card_mul_card_le_of_inf_eq_bot (inf_le_left : K ≤ B) (inf_le_left : K' ≤ B)
    (cent_inf_cent_eq_bot Mm hE)
  have hU := hC.exp
  have hB2 : IsPGroup 2 ↥B := hE.isPGroup
  have hcB := card_eq_two_pow_of_isPGroup hB2
  have hcK := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : K ≤ B))
  have hcK' := card_eq_two_pow_of_isPGroup (hB2.to_le (inf_le_left : K' ≤ B))
  have hcf := card_fixV_eq hU B
  have hidx := rk_add_rkIdx (fixV B)
  rw [rk_top_eq Mm (n := 1) (by rw [hF, pow_one])] at hidx
  have ha : 1 ≤ rk B := by
    rcases Nat.eq_zero_or_pos (rk B) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hB2).mp h) hB.2.1
    · exact h
  have hKne : ∀ {H : Subgroup (MulAut U)}, IsPGroup 2 ↥H → 1 ≤ rk H → H ≠ ⊥ := by
    intro H hH h1 hbot
    rw [(rk_eq_zero_iff_of_isPGroup hH).mpr hbot] at h1
    omega
  have hlt : ∀ {L : Subgroup (MulAut U)},
      rk ↥(B ⊓ Subgroup.centralizer (L : Set (MulAut U))) < rk B →
        ∃ a ∈ B, ∃ l ∈ L, a * l ≠ l * a := by
    intro L h
    refine exists_not_comm_of_card_lt ?_
    rw [card_eq_two_pow_of_isPGroup (hB2.to_le inf_le_left), hcB]
    exact Nat.pow_lt_pow_right (by norm_num) h
  rw [hcB, hcK] at hrk₁
  rw [hcB, hcK'] at hrk₂
  rw [hcB, hcK, hcK'] at hprod
  set a := rk B
  set c := rk K
  set c' := rk K'
  set f := rk ↥(fixV B)
  have e1 : c < a → f + 3 ≤ 9 := by
    intro h
    have h' := hflag L₁ L₂ Mm hPN₁ (hlt h)
    rw [hcf] at h'
    apply le_of_two_pow_le
    calc 2 ^ (f + 3) = 2 ^ f * 8 := by ring
      _ ≤ 512 := h'
      _ = 2 ^ 9 := by norm_num
  have e2 : c' < a → f + 3 ≤ 9 := by
    intro h
    have h' := hflag L₂ L₁ Mm.swap hPN₂ (hlt h)
    rw [hcf] at h'
    apply le_of_two_pow_le
    calc 2 ^ (f + 3) = 2 ^ f * 8 := by ring
      _ ≤ 512 := h'
      _ = 2 ^ 9 := by norm_num
  have e3 : a ≤ 2 + c := by
    apply le_of_two_pow_le
    calc 2 ^ a ≤ 4 * 2 ^ c := hrk₁
      _ = 2 ^ (2 + c) := by ring
  have e4 : a ≤ 2 + c' := by
    apply le_of_two_pow_le
    calc 2 ^ a ≤ 4 * 2 ^ c' := hrk₂
      _ = 2 ^ (2 + c') := by ring
  have e5 : c + c' ≤ a := by
    apply le_of_two_pow_le
    calc 2 ^ (c + c') = 2 ^ c * 2 ^ c' := by ring
      _ ≤ 2 ^ a := hprod
  have e6 : 1 ≤ c → c < a → f ≤ 4 := by
    intro hc hca
    have h := card_fixV_le_of_cent_three Mm hF hE hPN₁
      (hKne (hB2.to_le (inf_le_left : K ≤ B)) hc) (hlt hca)
    rw [hcf] at h
    apply le_of_two_pow_le
    calc 2 ^ f ≤ 16 := h
      _ = 2 ^ 4 := by norm_num
  have e7 : 1 ≤ c' → c' < a → f ≤ 4 := by
    intro hc hca
    have h := card_fixV_le_of_cent_three Mm.swap hF hE hPN₂
      (hKne (hB2.to_le (inf_le_left : K' ≤ B)) hc) (hlt hca)
    rw [hcf] at h
    apply le_of_two_pow_le
    calc 2 ^ f ≤ 16 := h
      _ = 2 ^ 4 := by norm_num
  rcases Nat.eq_zero_or_pos c with hc | hc
  · have := e1 (by omega)
    omega
  rcases Nat.eq_zero_or_pos c' with hc' | hc'
  · have := e2 (by omega)
    omega
  have := e6 hc (by omega)
  omega

end CFSG.Quasithin.RonanD37

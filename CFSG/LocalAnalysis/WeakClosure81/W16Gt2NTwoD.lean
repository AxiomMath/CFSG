module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFacts
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

theorem eq_top_of_card_L2_Sz {Y : Type} [Group Y] [Finite Y] (Lb : Subgroup Y) {n : ℕ}
    (hn : 1 ≤ n)
    (hL : Nat.card Lb = 2 ^ n * (4 ^ n - 1) ∨
      Nat.card Lb = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1))
    (hY : Nat.card Y = 2 ^ n * (4 ^ n - 1) ∨
      Nat.card Y = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) :
    Lb = ⊤ := by
  set q : ℕ := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 4 ^ n = q ^ 2 := by
    rw [hq]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have := sq_tsub_sq q 1
    simpa using this
  have hq2sq : 2 ≤ q ^ 2 := by nlinarith [hq2]
  have hApos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hcop : Nat.Coprime (q + 1) q :=
    ((Nat.coprime_self_add_right (m := q) (n := 1)).mpr (Nat.coprime_one_right q)).symm
  rw [h4] at hL hY
  rcases hL with hL | hL <;> rcases hY with hY | hY
  · exact (Subgroup.card_eq_iff_eq_top Lb).mp (by rw [hL, hY])
  · exfalso
    have hdvd : q * (q ^ 2 - 1) ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      rw [← hL, ← hY]
      exact Subgroup.card_subgroup_dvd_card Lb
    have hdl : q * (q - 1) * (q + 1) ∣ q * (q - 1) * (q * (q ^ 2 + 1)) := by
      have h1 : q * (q ^ 2 - 1) = q * (q - 1) * (q + 1) := by rw [hfac]; ring
      have h2 : q ^ 2 * (q - 1) * (q ^ 2 + 1) = q * (q - 1) * (q * (q ^ 2 + 1)) := by
        ring
      rw [h1, h2] at hdvd
      exact hdvd
    have hcancel : (q + 1) ∣ q * (q ^ 2 + 1) :=
      (Nat.mul_dvd_mul_iff_left hApos).mp hdl
    have hfinal : (q + 1) ∣ q ^ 2 + 1 :=
      hcop.dvd_of_dvd_mul_left hcancel
    have hq21 : (q + 1) ∣ q ^ 2 - 1 := by
      rw [hfac]; exact dvd_mul_right (q + 1) (q - 1)
    have h2 : (q + 1) ∣ 2 := by
      have := Nat.dvd_sub hfinal hq21
      rwa [show q ^ 2 + 1 - (q ^ 2 - 1) = 2 by omega] at this
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
    omega
  · exfalso
    have hdvd : q ^ 2 * (q - 1) * (q ^ 2 + 1) ∣ q * (q ^ 2 - 1) := by
      rw [← hL, ← hY]
      exact Subgroup.card_subgroup_dvd_card Lb
    have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
    have hle := Nat.le_of_dvd hpos hdvd
    have hq1pos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
    have hlt : q * (q ^ 2 - 1) < q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      rw [hfac]
      calc q * ((q + 1) * (q - 1))
          = (q * (q - 1)) * (q + 1) := by ring
        _ < (q * (q - 1)) * (q * (q ^ 2 + 1)) := by
              apply mul_lt_mul_of_pos_left
              · nlinarith [hq2]
              · exact hq1pos
        _ = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by ring
    exact (not_le_of_gt hlt) hle
  · exact (Subgroup.card_eq_iff_eq_top Lb).mp (by rw [hL, hY])

private theorem transvectionCenterSet_smul (m : ℕ) (F : Type) [Field F] (a : Fin m → F) {c : F}
    (hc : c ≠ 0) : transvectionCenterSet m F (c • a) = transvectionCenterSet m F a := by
  ext x
  unfold transvectionCenterSet
  constructor
  · rintro ⟨g, hgx, f, hf, hmat⟩
    have hfa : f ⬝ᵥ a = 0 := by
      have h := hf
      rw [dotProduct_smul, smul_eq_mul, mul_eq_zero] at h
      exact h.resolve_left hc
    refine ⟨g, hgx, c • f, ?_, ?_⟩
    · rw [smul_dotProduct, smul_eq_mul, hfa, mul_zero]
    · rw [hmat]
      have hvec : Matrix.vecMulVec (c • a) f = Matrix.vecMulVec a (c • f) := by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
      rw [hvec]
  · rintro ⟨g, hgx, f, hf, hmat⟩
    refine ⟨g, hgx, c⁻¹ • f, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, hf]
    · rw [hmat]
      have hvec : Matrix.vecMulVec a f = Matrix.vecMulVec (c • a) (c⁻¹ • f) := by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
      rw [hvec]

theorem false_of_transvection_config (hK : KFacts1234) {Y : Type} [Group Y] {m : ℕ}
    (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] (e : Y ≃* StatedProj (StatedSL m F))
    {a : Fin m → F} (ha : a ≠ 0) (Vb Wb : Subgroup Y)
    (hVb : ∀ y : Y, y ∈ Vb ↔ e y ∈ transvectionCenterSet m F a) (hnt : Vb ≠ ⊥) (γ : Y)
    (hWb : Wb = conjSubgroup Vb γ)
    (hinf : ∀ x ∈ Vb, x ∈ Subgroup.normalizer (Wb : Set Y) → x = 1) : False := by
  haveI : Finite Y := Finite.of_injective (e : Y → StatedProj (StatedSL m F)) e.injective
  obtain ⟨a', ha', hT⟩ := hK.transvection_conj m F a ((e γ)⁻¹) hm ha
  have hWiff : ∀ w : Y, w ∈ Wb ↔ e w ∈ transvectionCenterSet m F a' := by
    intro w
    rw [hWb, mem_conjSubgroup_iff, hVb (γ * w * γ⁻¹), ← hT]
    simp only [map_mul, map_inv, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨e γ * e w * (e γ)⁻¹, h, by group⟩
    · rintro ⟨y, hy, hyeq⟩
      rw [hyeq]
      have : e γ * ((e γ)⁻¹ * y * ((e γ)⁻¹)⁻¹) * (e γ)⁻¹ = y := by group
      rwa [this]
  have hnc : ∀ c : F, a' ≠ c • a := by
    intro c hca
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hca
      exact ha' hca
    have hT' : transvectionCenterSet m F a' = transvectionCenterSet m F a := by
      rw [hca, transvectionCenterSet_smul m F a hc0]
    have hVbWb : Vb = Wb := by
      ext w
      rw [hVb w, hWiff w, hT']
    have hbot : Vb = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact hinf x hx (by rw [hVbWb] at hx; exact Subgroup.le_normalizer hx)
    exact hnt hbot
  obtain ⟨x, hxT, hx1, hxnorm⟩ := hK.transvection_normalizer m F a a' hm ha ha' hnc
  let y₀ : Y := e.symm x
  have he_y₀ : e y₀ = x := e.apply_symm_apply x
  have hy₀Vb : y₀ ∈ Vb := (hVb y₀).mpr (by rw [he_y₀]; exact hxT)
  have hy₀ne : y₀ ≠ 1 := by
    intro h
    exact hx1 (by rw [← he_y₀, h, map_one])
  have hconj : ∀ w ∈ Wb, y₀ * w * y₀⁻¹ ∈ Wb := by
    intro w hw
    refine (hWiff (y₀ * w * y₀⁻¹)).mpr ?_
    have hwe : e w ∈ transvectionCenterSet m F a' := (hWiff w).mp hw
    have : e (y₀ * w * y₀⁻¹) = x * e w * x⁻¹ := by
      simp only [map_mul, map_inv, he_y₀]
    rw [this]
    exact hxnorm (e w) hwe
  have hle : conjSubgroup Wb y₀⁻¹ ≤ Wb := by
    intro w hw
    rw [mem_conjSubgroup_iff] at hw
    have h2 := hconj (y₀⁻¹ * w * (y₀⁻¹)⁻¹) hw
    rwa [show y₀ * (y₀⁻¹ * w * (y₀⁻¹)⁻¹) * y₀⁻¹ = w by group] at h2
  have heq : conjSubgroup Wb y₀⁻¹ = Wb :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (E3.card_conjSubgroup Wb y₀⁻¹).symm)
  have hnorm : y₀ ∈ Subgroup.normalizer (Wb : Set Y) := by
    have h1 : y₀⁻¹ ∈ Subgroup.normalizer (Wb : Set Y) :=
      conjSubgroup_eq_iff_mem_normalizer.mp heq
    simpa using (Subgroup.inv_mem _ h1)
  exact hy₀ne (hinf y₀ hy₀Vb hnorm)

private theorem map_conjSubgroup {G H : Type} [Group G] [Group H] (f : G ≃* H)
    (A : Subgroup G) (g : G) :
    (conjSubgroup A g).map f.toMonoidHom = conjSubgroup (A.map f.toMonoidHom) (f g) := by
  unfold conjSubgroup
  rw [Subgroup.map_map_conj]
  simp only [map_inv, MulEquiv.toMonoidHom_eq_coe]
  rfl

private theorem exists_config_of_conj {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    {Vb Wb : Subgroup Y} {A B : Subgroup Z} (hA : A = Vb.map e.toMonoidHom)
    (hB : B = Wb.map e.toMonoidHom)
    (h : ∃ γ τ : Z, τ ∈ A ⊔ B ∧ conjSubgroup A γ ≠ A ∧
      (∀ x ∈ conjSubgroup A γ, ∀ y ∈ A ⊔ B, x * y = y * x) ∧
      τ ∈ Subgroup.normalizer (A : Set Z) ∧ ∀ a ∈ A, τ * a = a * τ → a = 1) :
    ∃ γ τ : Y, τ ∈ Vb ⊔ Wb ∧ conjSubgroup Vb γ ≠ Vb ∧
      (∀ x ∈ conjSubgroup Vb γ, ∀ y ∈ Vb ⊔ Wb, x * y = y * x) ∧
      τ ∈ Subgroup.normalizer (Vb : Set Y) ∧ ∀ a ∈ Vb, τ * a = a * τ → a = 1 := by
  obtain ⟨γ', τ', hτ', hγ'ne, hcomm', hnorm', hfpf'⟩ := h
  refine ⟨e.symm γ', e.symm τ', ?_, ?_, ?_, ?_, ?_⟩
  · have hmap : τ' ∈ (Vb ⊔ Wb).map e.toMonoidHom := by
      rw [Subgroup.map_sup, ← hA, ← hB]
      exact hτ'
    exact Subgroup.mem_map_equiv.mp hmap
  · intro heq
    apply hγ'ne
    have hmap : (conjSubgroup Vb (e.symm γ')).map e.toMonoidHom = Vb.map e.toMonoidHom := by
      rw [heq]
    rw [map_conjSubgroup e Vb (e.symm γ'), ← hA, e.apply_symm_apply] at hmap
    exact hmap
  · intro x hx y hy
    have hx' : e x ∈ conjSubgroup A γ' := by
      have h1 : e x ∈ (conjSubgroup Vb (e.symm γ')).map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [map_conjSubgroup e Vb (e.symm γ'), ← hA, e.apply_symm_apply] at h1
    have hy' : e y ∈ A ⊔ B := by
      have h1 : e y ∈ (Vb ⊔ Wb).map e.toMonoidHom := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rwa [Subgroup.map_sup, ← hA, ← hB] at h1
    have hh := hcomm' (e x) hx' (e y) hy'
    exact e.injective (by simpa only [map_mul] using hh)
  · rw [Subgroup.mem_set_normalizer_iff]
    intro x
    have hx' := Subgroup.mem_set_normalizer_iff.mp hnorm' (e x)
    calc x ∈ Vb ↔ e x ∈ A := by rw [hA, Subgroup.mem_map_equiv]; simp
      _ ↔ τ' * e x * τ'⁻¹ ∈ A := hx'
      _ ↔ e (e.symm τ' * x * (e.symm τ')⁻¹) ∈ A := by
            simp only [map_mul, map_inv, e.apply_symm_apply]
      _ ↔ e.symm τ' * x * (e.symm τ')⁻¹ ∈ Vb := by
            rw [hA, Subgroup.mem_map_equiv]; simp
  · intro a ha hca
    have haA : e a ∈ A := by rw [hA]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hca' : τ' * e a = e a * τ' := by
      rw [← e.apply_symm_apply τ', ← map_mul, ← map_mul, hca]
    exact e.injective (by rw [hfpf' (e a) haA hca', map_one])

theorem exists_config_sp (hK : KFacts1234) {Y : Type} [Group Y] {l n : ℕ} (hl : 2 ≤ l)
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (e : Y ≃* ↥(StatedSp l F)) (Vb Wb : Subgroup Y) (hV : Nat.card Vb = 2 ^ n)
    (hW : Nat.card Wb = 2 ^ n)
    (htV : ∀ x ∈ Vb, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l (e x))
    (htW : ∀ x ∈ Wb, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l (e x))
    (hnc : ¬ ∀ a ∈ Vb, ∀ b ∈ Wb, a * b = b * a) :
    ∃ γ τ : Y, τ ∈ Vb ⊔ Wb ∧ conjSubgroup Vb γ ≠ Vb ∧
      (∀ x ∈ conjSubgroup Vb γ, ∀ y ∈ Vb ⊔ Wb, x * y = y * x) ∧
      τ ∈ Subgroup.normalizer (Vb : Set Y) ∧ ∀ a ∈ Vb, τ * a = a * τ → a = 1 := by
  set A : Subgroup ↥(StatedSp l F) := Vb.map e.toMonoidHom with hA
  set B : Subgroup ↥(StatedSp l F) := Wb.map e.toMonoidHom with hB
  have hAcard : Nat.card A = 2 ^ n := by
    rw [hA, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hV]
  have hBcard : Nat.card B = 2 ^ n := by
    rw [hB, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hW]
  have htA : ∀ x ∈ A, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x := by
    intro x hx hx1
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact htV y hy (fun hy1 => hx1 (by rw [hy1, map_one]))
  have htB : ∀ x ∈ B, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x := by
    intro x hx hx1
    rw [hB, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact htW y hy (fun hy1 => hx1 (by rw [hy1, map_one]))
  have hncA : ¬ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro h
    apply hnc
    intro a ha b hb
    have haA : e a ∈ A := by rw [hA]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hbB : e b ∈ B := by rw [hB]; exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    exact e.injective (by rw [map_mul, map_mul, h (e a) haA (e b) hbB])
  obtain ⟨γ', τ', hτ', hγ'ne, hcomm', hnorm', hfpf'⟩ :=
    hK.sp_config l n F hl hn hF A B hAcard hBcard htA htB hncA
  exact exists_config_of_conj e hA hB ⟨γ', τ', hτ', hγ'ne, hcomm', hnorm', hfpf'⟩

theorem exists_config_su (hK : KFacts1234) {Y : Type} [Group Y] {m n : ℕ} (hm : 4 ≤ m)
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : Y ≃* StatedProj (StatedSU m (2 ^ n) F)) (Vb Wb : Subgroup Y)
    (hV : Nat.card Vb = 2 ^ n) (hW : Nat.card Wb = 2 ^ n)
    (htV : ∀ x ∈ Vb, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n (e x))
    (htW : ∀ x ∈ Wb, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n (e x))
    (hnc : ¬ ∀ a ∈ Vb, ∀ b ∈ Wb, a * b = b * a) :
    ∃ γ τ : Y, τ ∈ Vb ⊔ Wb ∧ conjSubgroup Vb γ ≠ Vb ∧
      (∀ x ∈ conjSubgroup Vb γ, ∀ y ∈ Vb ⊔ Wb, x * y = y * x) ∧
      τ ∈ Subgroup.normalizer (Vb : Set Y) ∧ ∀ a ∈ Vb, τ * a = a * τ → a = 1 := by
  set A : Subgroup (StatedProj (StatedSU m (2 ^ n) F)) := Vb.map e.toMonoidHom with hA
  set B : Subgroup (StatedProj (StatedSU m (2 ^ n) F)) := Wb.map e.toMonoidHom with hB
  have hAcard : Nat.card A = 2 ^ n := by
    rw [hA, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hV]
  have hBcard : Nat.card B = 2 ^ n := by
    rw [hB, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hW]
  have htA : ∀ x ∈ A, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x := by
    intro x hx hx1
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact htV y hy (fun hy1 => hx1 (by rw [hy1, map_one]))
  have htB : ∀ x ∈ B, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x := by
    intro x hx hx1
    rw [hB, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact htW y hy (fun hy1 => hx1 (by rw [hy1, map_one]))
  have hncA : ¬ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro h
    apply hnc
    intro a ha b hb
    have haA : e a ∈ A := by rw [hA]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hbB : e b ∈ B := by rw [hB]; exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    exact e.injective (by rw [map_mul, map_mul, h (e a) haA (e b) hbB])
  obtain ⟨γ', τ', hτ', hγ'ne, hcomm', hnorm', hfpf'⟩ :=
    hK.su_config m n F hm hn hF A B hAcard hBcard htA htB hncA
  exact exists_config_of_conj e hA hB ⟨γ', τ', hτ', hγ'ne, hcomm', hnorm', hfpf'⟩

end CFSG.LocalAnalysis.WeakClosure81

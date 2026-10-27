module

public import CFSG.Quasithin.Background.SmithB45ExcBlocks
public import CFSG.Quasithin.Background.SmithB45ExcL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare

public section

namespace CFSG.Quasithin.B45Exc

open Module CFSG.QuasithinUnique.Setup.Family

theorem three_le_of_orderOf_two_dvd {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) {c : ℕ}
    (hc : 0 < c) (h : orderOf (2 : ZMod p) ∣ 2 * c) : 3 ≤ c := by
  by_contra hlt
  push Not at hlt
  have h2 : (2 : ZMod p) ^ (2 * c) = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  have hd : p ∣ 2 ^ (2 * c) - 1 := by
    have h3 : ((2 ^ (2 * c) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, h2, Nat.cast_one,
        sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 h3
  interval_cases c
  · have := Nat.le_of_dvd (by norm_num) hd
    omega
  · have h15 : p ∣ 3 * 5 := by simpa using hd
    rcases (Nat.Prime.dvd_mul hp.out).1 h15 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h5
      omega

section Blocks

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
variable (hK : Fintype.card K = p ^ 2) (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E))

omit [Module.Finite (ZMod 2) E] in
theorem inv_mul_Bl {s : E ≃ₗ[ZMod 2] E}
    (hsU : ∀ a : K, s * U (Multiplicative.ofAdd a) * s⁻¹ = U (Multiplicative.ofAdd (-a)))
    (g : Kˣ) (j : ℕ) :
    (s : Module.End (ZMod 2) E) * Bl U g j = Bl U g j * (s : Module.End (ZMod 2) E) := by
  have h := mul_Eb_of_intertwine U (s : Module.End (ZMod 2) E) (fun a => -a) neg_bijective
    (fun a => op_intertwine U a (-a) (hsU a)) ((g : K) ^ j) (-((g : K) ^ j))
    (fun l => by simp only [mul_neg])
  have hm : Eb U (-((g : K) ^ j)) = Eb U ((g : K) ^ j) := by
    have hL : eL U (-((g : K) ^ j)) = eL U ((g : K) ^ j) := by
      unfold eL
      exact Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun l => by simp [map_neg])
    unfold Eb
    rw [hL]
  unfold Bl
  rw [h, hm]

omit [Module.Finite (ZMod 2) E] in
include hK in
theorem fpf_Eb (hp5 : 5 ≤ p) {a b : K} (hb : b ≠ 0) (hab : ∀ l : ZMod p, a ≠ fpMap p K l * b)
    {v : E} (hv : v ∈ LinearMap.range (Eb U b)) (hfix : U (Multiplicative.ofAdd a) v = v) :
    v = 0 := by
  obtain ⟨w, rfl⟩ := hv
  have h1 : eL U b (Eb U b w) = Eb U b w := by
    have : eL U b * Eb U b = Eb U b := by
      unfold Eb
      rw [mul_add, eL_mul_eL_self U hp5, eL_mul_eU U hp5]
    exact LinearMap.congr_fun this w
  have hnat : ∀ n : ℕ, U (Multiplicative.ofAdd ((n : K) * a)) (Eb U b w) = Eb U b w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ofAdd_add, map_mul, LinearEquiv.mul_apply, hfix, ih]
  have h2 : eL U a (Eb U b w) = Eb U b w := by
    unfold eL
    rw [LinearMap.sum_apply]
    have hl : ∀ l : ZMod p, Uop U (fpMap p K l * a) (Eb U b w) = Eb U b w := by
      intro l
      have e : fpMap p K l = ((l.val : ℕ) : K) := by
        rw [fpMap, ZMod.castHom_apply, ZMod.natCast_val]
      rw [e]
      exact hnat l.val
    simp only [hl]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    exact nsmul_odd_vec (hp_odd hp5) _
  have ha : a ≠ 0 := fun h0 => hab 0 (by simp [h0])
  have hba : ∀ l : ZMod p, b ≠ fpMap p K l * a := by
    intro l hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hl
      exact hb hl
    apply hab l⁻¹
    rw [hl, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hl0, map_one, one_mul]
  have h3 : eU U (Eb U b w) = Eb U b w := by
    rw [← eL_mul_eL_of_ne hK U a b ha hba, Module.End.mul_apply, h1, h2]
  have h4 : eU U (Eb U b w) = 0 := by
    have := LinearMap.congr_fun (eU_mul_Eb hK U hp5 b) w
    simpa using this
  rw [← h3, h4]

include hK in
theorem three_le_rank_Bl (hp7 : 7 ≤ p) {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsU : ∀ a : K, s * U (Multiplicative.ofAdd a) * s⁻¹ = U (Multiplicative.ofAdd (-a)))
    {j : ℕ} (hj : Bl U g j ≠ 0) :
    3 ≤ finrank (ZMod 2) ((LinearMap.range (Bl U g j)).map (sub1 s)) := by
  have hp5 : 5 ≤ p := by omega
  set M := LinearMap.range (Bl U g j) with hM
  set a : K := (g : K) ^ (j + 1) with ha
  set v := U (Multiplicative.ofAdd a) with hv
  have hne : ¬ j ≡ j + 1 [MOD p + 1] := by
    intro h
    have h1 : 0 ≡ 1 [MOD p + 1] := Nat.ModEq.add_left_cancel' j (by simpa using h)
    have h2 : (1 : ℕ) % (p + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    unfold Nat.ModEq at h1
    rw [Nat.zero_mod, h2] at h1
    exact absurd h1 (by norm_num)
  have hab : ∀ l : ZMod p, a ≠ fpMap p K l * (g : K) ^ j :=
    not_mem_line_of_not_modEq hK hg hne
  have hb0 : (g : K) ^ j ≠ 0 := pow_ne_zero _ g.ne_zero
  have hfpf : ∀ x ∈ M, v x = x → x = 0 := fun x hx hvx => fpf_Eb hK U hp5 hb0 hab hx hvx
  have hvp : v ^ p = 1 := by
    rw [hv, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero,
      map_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsv : s * v * s = v⁻¹ := by
    have := hsU a
    rw [hsinv] at this
    rw [hv, this, ofAdd_neg, map_inv]
  have hsM : ∀ x ∈ M, s x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (LinearMap.congr_fun (inv_mul_Bl U hsU g j) y).symm⟩
  have hvM : ∀ x ∈ M, v x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨v y, (LinearMap.congr_fun (Uop_mul_Eb U a ((g : K) ^ j)) y).symm⟩
  have hhalf := finrank_half M hs hsv (hp_odd hp5) hvp hsM hvM hfpf
  have hdvd := orderOf_two_dvd_finrank_of_fpf hvp M hvM hfpf
  have hMne : M ≠ ⊥ := fun h0 => hj (LinearMap.range_eq_bot.1 h0)
  have hMpos := Submodule.one_le_finrank_iff.2 hMne
  have hpos : 0 < finrank (ZMod 2) (M.map (sub1 s)) := by omega
  rw [hhalf] at hdvd
  exact three_le_of_orderOf_two_dvd hp7 hpos hdvd

include hK in
theorem twelve_le_rank_of_inv (hp7 : 7 ≤ p)
    (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1)
    (hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)))
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsU : ∀ a : K, s * U (Multiplicative.ofAdd a) * s⁻¹ = U (Multiplicative.ofAdd (-a))) :
    12 ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  have hp5 : 5 ≤ p := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨j₀, hj₀⟩ := exists_nonzero_Bl hK U hg hp5 hU1
  have hne : ∀ k : ℕ, Bl U g (j₀ + 2 * k) ≠ 0 := by
    intro k
    obtain ⟨T, hT'⟩ := hT ((g : K) ^ k) (pow_ne_zero _ g.ne_zero)
    exact Bl_ne_zero_add U hT' hj₀
  have hmod : ∀ k k' : ℕ, k < 4 → k' < 4 → k ≠ k' →
      ¬ (j₀ + 2 * k) ≡ (j₀ + 2 * k') [MOD p + 1] := by
    intro k k' hk hk' hkk' h
    have h1 := Nat.ModEq.add_left_cancel' j₀ h
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have := sum_le_finrank_range_sub1 s (Finset.range 4) (fun k => Bl U g (j₀ + 2 * k))
    (fun k _ => Bl_mul_Bl_of_modEq U hK hg hp5 (Nat.ModEq.refl _))
    (fun k hk k' hk' hkk' => Bl_mul_Bl_of_not_modEq U hK hg hp5
      (hmod k k' (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') hkk'))
    (fun k _ => inv_mul_Bl U hsU g _) (fun _ => 3)
    (fun k _ => three_le_rank_Bl hK U hp7 hg hs hsU (hne k))
  simpa using this

end Blocks

section PSL

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

omit hpf [Fintype K] [CharP K p] in
theorem pslMk_slD_sq {i : Kˣ} (hi : (i : K) * i = -1) :
    pslMk (slD i) * pslMk (slD i) = (1 : PSL2 K) := by
  rw [← map_mul]
  show (QuotientGroup.mk' _ (slD i * slD i) : PSL2 K) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  have hi' : ((i : K))⁻¹ * ((i : K))⁻¹ = -1 := by
    rw [← mul_inv, hi, inv_neg, inv_one]
  refine ⟨-1, by norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_slD, Matrix.mul_apply, Fin.sum_univ_two, hi, hi']

theorem psl2_square_inner_rank12 (hp7 : 7 ≤ p) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (ρ : PSL2 K →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) {t : PSL2 K} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) : 12 ≤ Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) := by
  have hp5 : 5 ≤ p := by omega
  have hodd : Odd p := hp_odd hp5
  obtain ⟨i0, hi0⟩ : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, hK, Nat.pow_mod]
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by have := Nat.odd_iff.1 hodd; omega
    rcases h4 with h4 | h4 <;> rw [h4] <;> norm_num
  have hi0' : i0 * i0 = -1 := hi0.symm
  have hi0ne : i0 ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hi0'
    exact one_ne_zero (neg_eq_zero.1 hi0'.symm)
  set i : Kˣ := Units.mk0 i0 hi0ne with hidef
  have hival : ((i : Kˣ) : K) = i0 := Units.val_mk0 _
  set t₀ : PSL2 K := pslMk (slD i) with ht₀def
  have ht₀U : ∀ a : K, t₀ * pslU (Multiplicative.ofAdd a) * t₀⁻¹ =
      pslU (Multiplicative.ofAdd (-a)) := by
    intro a
    rw [ht₀def, pslD_conj_pslU, hival, sq, hi0', neg_one_mul]
  have ht₀2 : t₀ * t₀ = 1 := pslMk_slD_sq (i := i) (by rw [hival]; exact hi0')
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    have h1 := ht₀U 1
    rw [h, one_mul, inv_one, mul_one] at h1
    have h2 := pslU_injective h1
    have h3 : (1 : K) = -1 := Multiplicative.ofAdd.injective h2
    have h4 : (2 : K) = 0 := by linear_combination h3
    exact two_ne_zero_of_charP hp5 h4
  have hKodd := isOddPrimePower_sq (K := K) hp5 hK
  obtain ⟨c, hc⟩ := psl2_involutions_conjugate_of_odd_prime_power K hKodd t t₀
    ⟨ht1, by rw [pow_two]; exact ht2⟩ ⟨ht₀1, by rw [pow_two]; exact ht₀2⟩
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) =
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ t₀)) := by
    rw [← hc]
    exact (finrank_range_disp_conj ρ t c).symm
  rw [hrank]
  let U : Multiplicative K →* (E ≃ₗ[ZMod 2] E) := ρ.comp pslU
  have hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1 := by
    intro a ha h
    have h1 : pslU (Multiplicative.ofAdd a) = 1 := hρ (by rw [map_one]; exact h)
    have h2 : Multiplicative.ofAdd a = 1 := pslU_injective (by rw [h1, map_one])
    exact ha (ofAdd_eq_one.1 h2)
  have hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)) := by
    intro c hc
    refine ⟨ρ (pslMk (slD (Units.mk0 c hc))), fun a => ?_⟩
    have h2 := pslD_conj_pslU (K := K) (Units.mk0 c hc) a
    have h3 := congrArg ρ h2
    simpa [U, map_mul, map_inv] using h3
  have hs : ρ t₀ * ρ t₀ = 1 := by rw [← map_mul, ht₀2, map_one]
  have hsU : ∀ a : K, ρ t₀ * U (Multiplicative.ofAdd a) * (ρ t₀)⁻¹ =
      U (Multiplicative.ofAdd (-a)) := by
    intro a
    have h3 := congrArg ρ (ht₀U a)
    simpa [U, map_mul, map_inv] using h3
  exact twelve_le_rank_of_inv hK U hp7 hU1 hT hs hsU

end PSL

section Offender

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem card_le_two_of_forall_eq {G : Type*} [Group G] {H : Subgroup G} (x : G)
    (h : ∀ y ∈ H, y = 1 ∨ y = x) : Nat.card H ≤ 2 := by
  have hsub : (H : Set G) ⊆ {1, x} := fun y hy => by
    rcases h y hy with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  calc Nat.card H = Set.ncard (H : Set G) := (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard ({1, x} : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Set.ncard ({x} : Set G) + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

theorem no_offender2_gamma
    (hp7 : 7 ≤ p) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] {Hg : Type*} [Group Hg]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) (j : Hg →* PGammaL2 K)
    (hj : Function.Injective j) (ι : PSL2 K →* Hg)
    (hjι : ∀ y, j (ι y) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  have hp5 : 5 ≤ p := by omega
  have hoddpp := isOddPrimePower_sq hp5 hK
  have hcard3 := three_lt_card_sq hp5 hK
  have hch : ringChar K ≠ 2 := ringChar_ne_two_sq (K := K) (p := p) hp5
  have hcardAut : Nat.card (K ≃+* K) = 2 :=
    (card_ringAut_and_isCyclic hpf.out K (by rw [Nat.card_eq_fintype_card, hK])).1
  have hι : Function.Injective ι := by
    intro y z hyz
    have h1 := hjι y
    rw [hyz, hjι z] at h1
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (SemidirectProduct.inl_injective h1.symm)
  obtain ⟨-, hidx, -, -, hpair⟩ := projective_involution_pairing K hch
  have hB8 : Nat.card B ≤ 8 := card_le_eight hch hcardAut hj hBc hB2
  have hinner : ∀ a : Hg, ∀ ha : a ∈ linPart j, linMap j ⟨a, ha⟩ ∈ pglS K → a ≠ 1 →
      a * a = 1 → 12 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
    intro a haL haS ha1 ha2
    obtain ⟨y, hy⟩ := haS
    have hia : ι y = a := by
      apply hj
      rw [hjι, hy]
      exact (j_eq_inl j ⟨a, haL⟩).symm
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply ha1
      rw [← hia, map_one]
    have hy2 : y * y = 1 := hι (by rw [map_mul, map_one, hia]; exact ha2)
    have h := psl2_square_inner_rank12 hp7 hK (ρ.comp ι) (hρ.comp hι) hy1 hy2
    have e : disp (ρ.comp ι) y = disp ρ a := by
      show disp ρ (ι y) = disp ρ a
      rw [hia]
    rwa [e] at h
  by_cases hcase : ∃ a ∈ B, ∃ ha : a ∈ linPart j, linMap j ⟨a, ha⟩ ∈ pglS K ∧ a ≠ 1
  · obtain ⟨a, haB, haL, haS, ha1⟩ := hcase
    have h1 := hinner a haL haS ha1 (hB2 a haB)
    have hlog : Nat.log 2 (Nat.card B) ≤ 3 := (Nat.log_mono_right hB8).trans (by norm_num)
    have h2 := finrank_range_disp_le_of_offender ρ haB (L := 6) (hoff.trans (by omega))
    omega
  · push Not at hcase
    let φ : ↥B →* (K ≃+* K) := SemidirectProduct.rightHom.comp (j.comp B.subtype)
    have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card B := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ 2 := by
      have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
      rw [← hcardAut]
      exact Subgroup.card_le_card_group _
    have hkerL : ∀ x ∈ φ.ker, (x : Hg) ∈ linPart j := fun x hx => hx
    have hkerS : ∀ x : ↥B, ∀ hx : x ∈ φ.ker, (x : Hg) ≠ 1 →
        linMap j ⟨(x : Hg), hkerL x hx⟩ ∉ pglS K :=
      fun x hx hx1 hS => hx1 (hcase x x.2 (hkerL x hx) hS)
    by_cases hk : ∃ x ∈ φ.ker, (x : Hg) ≠ 1
    ·
      obtain ⟨x, hx, hx1⟩ := hk
      have hsub : ∀ y ∈ φ.ker, y = 1 ∨ y = x := by
        intro y hy
        by_cases hy1 : (y : Hg) = 1
        · exact Or.inl (Subtype.ext hy1)
        · right
          have hmem : linMap j (⟨(y : Hg), hkerL y hy⟩ * (⟨(x : Hg), hkerL x hx⟩)⁻¹) ∈
              pglS K := by
            rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx]
            simp [hkerS y hy hy1, hkerS x hx hx1]
          have hyx : (y : Hg) * (x : Hg)⁻¹ ∈ linPart j :=
            (linPart j).mul_mem (hkerL y hy) ((linPart j).inv_mem (hkerL x hx))
          have h3 := hcase ((y : Hg) * (x : Hg)⁻¹) (B.mul_mem y.2 (B.inv_mem x.2)) hyx hmem
          exact Subtype.ext (mul_inv_eq_one.1 h3)
      have hker2 : Nat.card φ.ker ≤ 2 := card_le_two_of_forall_eq x hsub
      have hB4 : Nat.card B ≤ 4 := by
        calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
          _ ≤ 2 * 2 := Nat.mul_le_mul hker2 h2
      have hlog : Nat.log 2 (Nat.card B) ≤ 2 := (Nat.log_mono_right hB4).trans (by norm_num)
      set d : Hg := (x : Hg) with hd
      have hdB : d ∈ B := x.2
      have hdL : d ∈ linPart j := hkerL x hx
      have hd2 : d * d = 1 := hB2 d hdB
      set D := linMap j ⟨d, hdL⟩ with hD
      have hDS : D ∉ pglS K := hkerS x hx hx1
      have hD2 : D * D = 1 := by
        rw [hD, ← map_mul]
        have : (⟨d, hdL⟩ : linPart j) * ⟨d, hdL⟩ = 1 := Subtype.ext hd2
        rw [this, map_one]
      have hD1 : D ≠ 1 := fun h => hDS (h ▸ (pglS K).one_mem)
      obtain ⟨s, hsS, hst, hcomm⟩ := hpair D hD2 hD1
      obtain ⟨y₀, hy₀⟩ := hsS
      set s₀ : Hg := ι y₀ with hs₀
      have hjs₀ : j s₀ = SemidirectProduct.inl s := by rw [hs₀, hjι, hy₀]
      set d' : Hg := s₀⁻¹ * d * s₀ with hd'
      have hjd : j d = SemidirectProduct.inl D := j_eq_inl j ⟨d, hdL⟩
      have hjd' : j d' = SemidirectProduct.inl (s⁻¹ * D * s) := by
        rw [hd', map_mul j (s₀⁻¹ * d) s₀, map_mul j s₀⁻¹ d, map_inv, hjs₀, hjd, ← map_inv,
          ← map_mul, ← map_mul]
      have hjdd : j (d * d') = SemidirectProduct.inl (D * (s⁻¹ * D * s)) := by
        rw [map_mul j d d', hjd, hjd', ← map_mul]
      have hddL : d * d' ∈ linPart j := by
        show (j (d * d')).right = 1
        rw [hjdd]
        rfl
      have hddlin : linMap j ⟨d * d', hddL⟩ = D * (s⁻¹ * D * s) := by
        show (j (d * d')).left = _
        rw [hjdd]
        rfl
      have hsDS : s⁻¹ * D * s ∉ pglS K := by
        intro h
        apply hDS
        have hs' : s ∈ pglS K := ⟨y₀, hy₀⟩
        have : D = s * (s⁻¹ * D * s) * s⁻¹ := by group
        rw [this]
        exact (pglS K).mul_mem ((pglS K).mul_mem hs' h) ((pglS K).inv_mem hs')
      have hddS : linMap j ⟨d * d', hddL⟩ ∈ pglS K := by
        rw [hddlin, Subgroup.mul_mem_iff_of_index_two hidx]
        simp [hDS, hsDS]
      have hdd1 : d * d' ≠ 1 := by
        intro h
        apply hst
        have h3 : j (d * d') = 1 := by rw [h, map_one]
        rw [hjdd] at h3
        have h4 : D * (s⁻¹ * D * s) = 1 :=
          SemidirectProduct.inl_injective (h3.trans (map_one _).symm)
        have h5 : s⁻¹ * D * s = D⁻¹ := eq_inv_of_mul_eq_one_right h4
        rw [h5]
        exact inv_eq_of_mul_eq_one_right hD2
      have hcomm' : d * d' = d' * d := by
        apply hj
        rw [map_mul j d d', map_mul j d' d, hjd, hjd', ← map_mul, ← map_mul, hcomm.eq]
      have hd'2 : d' * d' = 1 := by
        calc d' * d' = s₀⁻¹ * (d * d) * s₀ := by rw [hd']; group
          _ = 1 := by rw [hd2]; group
      have hdd2 : (d * d') * (d * d') = 1 := by
        calc (d * d') * (d * d') = d * (d' * d) * d' := by group
          _ = d * (d * d') * d' := by rw [← hcomm']
          _ = (d * d) * (d' * d') := by group
          _ = 1 := by rw [hd2, hd'2, mul_one]
      have h12 := hinner (d * d') hddL hddS hdd1 hdd2
      have hsum := finrank_range_disp_mul_le ρ d d'
      have hconj : finrank (ZMod 2) (LinearMap.range (disp ρ d')) =
          finrank (ZMod 2) (LinearMap.range (disp ρ d)) := by
        have h3 := finrank_range_disp_conj ρ d s₀⁻¹
        rw [inv_inv] at h3
        rw [hd', h3]
      have hdle := finrank_range_disp_le_of_offender ρ hdB (L := 4) (hoff.trans (by omega))
      omega
    ·
      push Not at hk
      have hker1 : Nat.card φ.ker ≤ 1 := by
        have : φ.ker = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x hx => Subtype.ext (hk x hx)
        rw [this, Subgroup.card_bot]
      have hB2' : Nat.card B ≤ 2 := by
        calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
          _ ≤ 1 * 2 := Nat.mul_le_mul hker1 h2
          _ = 2 := by norm_num
      have hlog : Nat.log 2 (Nat.card B) ≤ 1 := (Nat.log_mono_right hB2').trans (by norm_num)
      obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
        obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
        exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
      have htf : (j t).right ≠ 1 := fun h => ht1 (hk ⟨t, htB⟩ h)
      have ht2 : t * t = 1 := hB2 t htB
      have hord : orderOf (j t) = 2 := by
        rw [orderOf_injective j hj t]
        exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
      obtain ⟨C, hC⟩ := pGammaL2_involution_conj_inr hoddpp (j t) hord htf
      let j' : Hg →* PGammaL2 K :=
        (MulAut.conj ((SemidirectProduct.inl C)⁻¹ : PGammaL2 K)).toMonoidHom.comp j
      let ι' : PSL2 K →* Hg := ι.comp (pgl2InnerAutPSL2 K hoddpp hcard3 C).toMonoidHom
      have hj' : Function.Injective j' := (MulAut.conj _).injective.comp hj
      have hjι' : ∀ y, j' (ι' y) =
          SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
        intro y
        show (SemidirectProduct.inl C)⁻¹ * j (ι (pgl2InnerAutPSL2 K hoddpp hcard3 C y)) *
          ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
        rw [hjι, toPGL_pgl2InnerAutPSL2_apply]
        simp only [map_mul, map_inv, inv_inv]
        group
      have hjt' : j' t = SemidirectProduct.inr (j t).right := by
        show (SemidirectProduct.inl C)⁻¹ * j t * ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
        rw [inv_inv]
        exact hC
      have h4 := field_involution_rank hp5 hK ρ hρ j' hj' ι' hjι' htf hjt'
      have h5 := finrank_range_disp_le_of_offender ρ htB (L := 2) (hoff.trans (by omega))
      omega

end Offender

section Final

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup

theorem primeSquareExclusion2F
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (W : Type) [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (Lb : Subgroup (MulAut W)) (hperf : Group.IsPerfect ↥Lb)
    (hirr : X1.IsIrrOn Lb) (hmod : StatedClassicalModel (CQ Lb) .PSL 2 p 2)
    (A : Subgroup (MulAut W)) (hAN : A ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card A ^ 2 * Nat.card (fixV A) < Nat.card W := by
  have hp5 : 5 ≤ p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have hp2 : p ≠ 2 := by omega
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have := hperf
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKcard
  have hoddpp := isOddPrimePower_sq hp5 hKcard
  have hcard3 := three_lt_card_sq hp5 hKcard
  let π : ↥Lb →* StatedProj (StatedSL 2 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥Lb := ker_comp_mk'_center e
  have hcenter : Subgroup.center ↥Lb = ⊥ := by
    have h25 : 25 ≤ p ^ 2 := by nlinarith
    have h := (odd_psl_two_perfect_odd_cover_kernel (p := p) (f := 2) hp2 hK π hπs hker.le
      (hker ▸ hodd)).1 (by omega)
    rw [← hker]
    exact h
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (hker.trans hcenter)
  let θ : ↥Lb ≃* PSL2 K :=
    (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hHn : Lb ⊔ A ≤ Subgroup.normalizer (Lb : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hAN
  have hNnormal : (Lb.subgroupOf (Lb ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (Lb.subgroupOf (Lb ⊔ A)) ≃* PSL2 K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : Lb ≤ Lb ⊔ A)).trans θ
  have hC := centralizer_trivial hW hirr.2 hcenter hAN hA2
  have hCbot : Subgroup.centralizer
      ((Lb.subgroupOf (Lb ⊔ A) : Subgroup ↥(Lb ⊔ A)) : Set ↥(Lb ⊔ A)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hC z
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 hz n hn).symm
  have hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hoddpp hcard3) :=
    pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 2) hK hoddpp hcard3
  let j := normalPSL2ToPGammaL2 (Lb.subgroupOf (Lb ⊔ A)) K hoddpp hcard3 θ' hsurj
  have hj : Function.Injective j :=
    normalPSL2ToPGammaL2_injective _ K hoddpp hcard3 θ' hCbot hsurj
  let ι : PSL2 K →* ↥(Lb ⊔ A) := (Lb.subgroupOf (Lb ⊔ A)).subtype.comp θ'.symm.toMonoidHom
  have hjι : ∀ y, j (ι y) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := fun y =>
    normalPSL2ToPGammaL2_apply _ K hoddpp hcard3 θ' hsurj y
  let ρH : ↥(Lb ⊔ A) →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp (Lb ⊔ A).subtype
  have hρH : ∀ (g : ↥(Lb ⊔ A)) (v : Additive W),
      ρH g v = Additive.ofMul ((g : MulAut W) (Additive.toMul v)) := fun g v => rfl
  have hρinj : Function.Injective ρH := by
    intro g g' h
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have h1 := LinearEquiv.congr_fun h (Additive.ofMul w)
    rw [hρH, hρH] at h1
    exact Additive.ofMul.injective h1
  by_contra hne
  push Not at hne
  have hAH : A ≤ Lb ⊔ A := le_sup_right
  have hB1 : A.subgroupOf (Lb ⊔ A) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAH a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext
      (congrArg (fun x : ↥(A.subgroupOf (Lb ⊔ A)) => ((x : ↥(Lb ⊔ A)) : MulAut W)) h)
  have hBc : ∀ a ∈ A.subgroupOf (Lb ⊔ A), ∀ b ∈ A.subgroupOf (Lb ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb)
  have hB2 : ∀ a ∈ A.subgroupOf (Lb ⊔ A), a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hA2.2 _ ha
    rwa [pow_two] at this
  have hfix : Nat.card (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) = Nat.card (fixV A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAH ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ A := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card (A.subgroupOf (Lb ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hpgrp : IsPGroup 2 (A.subgroupOf (Lb ⊔ A)) := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 (a : ↥(Lb ⊔ A)) a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : finrank (ZMod 2) (Additive W) -
      finrank (ZMod 2) (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) ≤
        2 * Nat.log 2 (Nat.card (A.subgroupOf (Lb ⊔ A))) := by
    refine finrank_sub_le_two_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfix]
    exact hne
  exact no_offender2_gamma hp7 hKcard ρH hρinj j hj ι hjι hB1 hBc hB2 hoff

end Final

end CFSG.Quasithin.B45Exc

module

public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S46

open Matrix

variable {F : Type} [Field F]

theorem eq_one_of_pow_two_pow_eq_one [CharP F 2] {a : F} {k : ℕ} (h : a ^ 2 ^ k = 1) :
    a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (a - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h1)

theorem inv_mulVec_mulVec_SL3 (x : SL3 F) (v : Fin 3 → F) :
    ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem mulVec_inv_mulVec_SL3 (x : SL3 F) (v : Fin 3 → F) :
    (x : Matrix (Fin 3) (Fin 3) F) *ᵥ (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem sup_span_eq_top {W : Submodule F (Fin 3 → F)} (hW : Module.finrank F W = 2)
    {v : Fin 3 → F} (hv : v ∉ W) : W ⊔ F ∙ v = ⊤ := by
  have hne : W ≠ W ⊔ F ∙ v := fun h => hv (by
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  have h1 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left hne)
  have h2 := Submodule.finrank_le (W ⊔ F ∙ v)
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun] at h2 ⊢
  omega

theorem exists_not_mem_of_finrank_eq_two {W : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 2) : ∃ v : Fin 3 → F, v ∉ W := by
  by_contra! hall
  have htop : W = ⊤ := eq_top_iff.mpr fun v _ => hall v
  rw [htop, finrank_top, Module.finrank_fin_fun] at hW
  omega

private theorem exists_pow_mulVec {t : SL3 F} {S : Submodule F (Fin 3 → F)}
    (hS : ∀ x ∈ S, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S) {w s : Fin 3 → F} {μ : F}
    (hs : s ∈ S) (hw : (t : Matrix (Fin 3) (Fin 3) F) *ᵥ w = s + μ • w) (m : ℕ) :
    ∃ s' ∈ S, ((t ^ m : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = s' + μ ^ m • w := by
  induction m with
  | zero => exact ⟨0, S.zero_mem, by simp⟩
  | succ m ih =>
    obtain ⟨s', hs', e⟩ := ih
    refine ⟨(t : Matrix (Fin 3) (Fin 3) F) *ᵥ s' + μ ^ m • s,
      S.add_mem (hS s' hs') (S.smul_mem _ hs), ?_⟩
    rw [pow_succ' t m, coe_mul_SL3, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_add,
      Matrix.mulVec_smul, hw, smul_add, smul_smul, pow_succ μ m, add_assoc]

theorem sub_mem_of_pow_two_pow [CharP F 2] {t : SL3 F} {k : ℕ} (ht : t ^ 2 ^ k = 1)
    {S : Submodule F (Fin 3 → F)} (hS : ∀ x ∈ S, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S)
    {w : Fin 3 → F} (hw : (t : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ S ⊔ F ∙ w) :
    (t : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w ∈ S := by
  by_cases hwS : w ∈ S
  · exact S.sub_mem (hS w hwS) hwS
  obtain ⟨s, hs, y, hy, e⟩ := Submodule.mem_sup.mp hw
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s', hs', e'⟩ := exists_pow_mulVec hS hs e.symm (2 ^ k)
  rw [ht, coe_one_SL3, Matrix.one_mulVec] at e'
  have hμ : μ ^ 2 ^ k = 1 := by
    by_contra hne
    apply hwS
    have h1 : (1 - μ ^ 2 ^ k) • w = s' := by
      rw [sub_smul, one_smul, eq_sub_of_add_eq e'.symm]
    have h2 : (1 - μ ^ 2 ^ k) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h3 : (1 - μ ^ 2 ^ k) • w ∈ S := by rw [h1]; exact hs'
    have := S.smul_mem (1 - μ ^ 2 ^ k)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
  rw [← e, eq_one_of_pow_two_pow_eq_one hμ, one_smul, add_sub_cancel_right]
  exact hs

theorem mulVec_eq_of_finrank_le_one [CharP F 2] {t : SL3 F} {k : ℕ} (ht : t ^ 2 ^ k = 1)
    {S : Submodule F (Fin 3 → F)} (hS1 : Module.finrank F S ≤ 1)
    (hS : ∀ x ∈ S, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S) {x : Fin 3 → F} (hx : x ∈ S) :
    (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  by_cases hx0 : x = 0
  · rw [hx0, Matrix.mulVec_zero]
  have hle : F ∙ x ≤ S := (Submodule.span_singleton_le_iff_mem _ _).mpr hx
  have heq : F ∙ x = S :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton hx0]; exact hS1)
  have hbot : ∀ y ∈ (⊥ : Submodule F (Fin 3 → F)),
      (t : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ (⊥ : Submodule F (Fin 3 → F)) := by
    intro y hy
    rw [(Submodule.mem_bot F).mp hy, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  have h := sub_mem_of_pow_two_pow ht hbot (w := x) (by rw [bot_sup_eq, heq]; exact hS x hx)
  rwa [Submodule.mem_bot, sub_eq_zero] at h

theorem sub_mem_of_finrank_eq_two [CharP F 2] {t : SL3 F} {k : ℕ} (ht : t ^ 2 ^ k = 1)
    {W : Submodule F (Fin 3 → F)} (hW2 : Module.finrank F W = 2)
    (hW : ∀ x ∈ W, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (x : Fin 3 → F) :
    (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ W := by
  by_cases hx : x ∈ W
  · exact W.sub_mem (hW x hx) hx
  exact sub_mem_of_pow_two_pow ht hW (by rw [sup_span_eq_top hW2 hx]; trivial)

theorem finrank_range_sub_one_le_one [CharP F 2] {t : SL3 F} (ht : t * t = 1) :
    Module.finrank F (LinearMap.range ((t : Matrix (Fin 3) (Fin 3) F) - 1).mulVecLin) ≤ 1 := by
  set N := (t : Matrix (Fin 3) (Fin 3) F) - 1 with hN
  have hNN : N * N = 0 := sub_one_mul_self_eq_zero ht
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hNN, Matrix.zero_mulVec]
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

theorem sub_mem_range_sub_one (t : SL3 F) (x : Fin 3 → F) :
    (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈
      LinearMap.range ((t : Matrix (Fin 3) (Fin 3) F) - 1).mulVecLin :=
  ⟨x, by rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]⟩

theorem mulVec_mem_range_of_commute {t g : SL3 F} (hgt : g * t = t * g) {y : Fin 3 → F}
    (hy : y ∈ LinearMap.range ((t : Matrix (Fin 3) (Fin 3) F) - 1).mulVecLin) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈
      LinearMap.range ((t : Matrix (Fin 3) (Fin 3) F) - 1).mulVecLin := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨(g : Matrix (Fin 3) (Fin 3) F) *ᵥ x, ?_⟩
  have e : (g : Matrix (Fin 3) (Fin 3) F) * t = t * g := by
    rw [← coe_mul_SL3, ← coe_mul_SL3, hgt]
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, sub_mul, mul_sub, one_mul, mul_one, e]

theorem commute_of_sub_mem {t g : SL3 F} {X Y : Submodule F (Fin 3 → F)}
    (ht1 : ∀ x, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ X)
    (ht2 : ∀ y ∈ Y, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y)
    (hg1 : ∀ x ∈ X, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x)
    (hg2 : ∀ x, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ Y) : g * t = t * g := by
  have key : ∀ x : Fin 3 → F,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((t : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
        (t : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
    intro x
    have h1 := hg1 _ (ht1 x)
    have h2 := ht2 _ (hg2 x)
    rw [Matrix.mulVec_sub, sub_eq_iff_eq_add] at h1 h2
    rw [h1, h2]
    abel
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) F) * t = (t : Matrix (Fin 3) (Fin 3) F) * g
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact key _

theorem mulVec_mem_commN_of_normalizes {E : Subgroup (SL3 F)} {n : SL3 F}
    (hn : ∀ e ∈ E, n * e * n⁻¹ ∈ E) {x : Fin 3 → F} (hx : x ∈ commN E) :
    (n : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ commN E := by
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨e, he, y, rfl⟩ := hy
    have h := sub_mem_commN (hn e he) ((n : Matrix (Fin 3) (Fin 3) F) *ᵥ y)
    rw [Matrix.mulVec_sub]
    rwa [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      inv_mulVec_mulVec_SL3] at h
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

theorem mulVec_mem_fixN_of_normalizes {E : Subgroup (SL3 F)} {n : SL3 F}
    (hn : ∀ e ∈ E, n⁻¹ * e * n ∈ E) {x : Fin 3 → F} (hx : x ∈ fixN E) :
    (n : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ fixN E := by
  intro e he
  have h := hx _ (hn e he)
  rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
  calc (e : Matrix (Fin 3) (Fin 3) F) *ᵥ ((n : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
      (n : Matrix (Fin 3) (Fin 3) F) *ᵥ (((n⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ ((n : Matrix (Fin 3) (Fin 3) F) *ᵥ x))) :=
        (mulVec_inv_mulVec_SL3 n _).symm
    _ = (n : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by rw [h]

theorem commute_of_normalizes [CharP F 2] {E : Subgroup (SL3 F)}
    (hc : Module.finrank F (commN E) ≤ 1) (hf : Module.finrank F (fixN E) = 2) {g : SL3 F}
    {k : ℕ} (hg : g ^ 2 ^ k = 1) (hn : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hn' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) {t : SL3 F} (ht : t ∈ E) : g * t = t * g :=
  commute_of_sub_mem (X := commN E) (Y := fixN E) (fun x => sub_mem_commN ht x)
    (fun _ hy => hy t ht)
    (fun _ hx => mulVec_eq_of_finrank_le_one hg hc
      (fun _ hy => mulVec_mem_commN_of_normalizes hn hy) hx)
    (sub_mem_of_finrank_eq_two hg hf fun _ hy => mulVec_mem_fixN_of_normalizes hn' hy)

theorem fixN_rootGroup_zero_two :
    fixN (rootGroup 0 2 : Subgroup (SL3 F)) = ln01 := by
  rw [fixN_rootGroup (by decide)]
  rfl

theorem mulVec_eq_of_mem_commN {E : Subgroup (SL3 F)} {Y : Submodule F (Fin 3 → F)}
    (hY : Y ≤ fixN E) {v : Fin 3 → F} (hYv : Y ⊔ F ∙ v = ⊤) {g : SL3 F}
    (hg : ∀ e ∈ E, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) =
      (e : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) {x : Fin 3 → F} (hx : x ∈ commN E) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨e, he, y, rfl⟩ := hy
    have hy : y ∈ Y ⊔ F ∙ v := by rw [hYv]; trivial
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have e1 : (e : Matrix (Fin 3) (Fin 3) F) *ᵥ (u + a • v) - (u + a • v) =
        a • ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hY hu e he, smul_sub]
      abel
    rw [e1, Matrix.mulVec_smul, hg e he]
  | zero => exact Matrix.mulVec_zero _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul c x _ hx => rw [Matrix.mulVec_smul, hx]

theorem finrank_commN_le_two_of_pGroup [Finite F] [CharP F 2] {P : Subgroup (SL3 F)}
    (hP : IsPGroup 2 P) : Module.finrank F (commN P) ≤ 2 := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  rw [← finrank_commN_map_conj x P, ← finrank_ln01 (F := F)]
  exact Submodule.finrank_mono (commN_le_ln01_of_le_sStar hx)

theorem finrank_fixN_pos [Finite F] [CharP F 2] {P : Subgroup (SL3 F)} (hP : IsPGroup 2 P) :
    0 < Module.finrank F (fixN P) := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  rw [← finrank_fixN_map_conj x P]
  calc 0 < 1 := one_pos
    _ = Module.finrank F (pt0 : Submodule F (Fin 3 → F)) := finrank_pt0.symm
    _ ≤ _ := Submodule.finrank_mono (pt0_le_fixN_of_le_sStar hx)

theorem finrank_commN_le_one_of_card_eq_two [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hE : Nat.card E = 2) : Module.finrank F (commN E) ≤ 1 := by
  obtain ⟨⟨t, htE⟩, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hE
  have hle : commN E ≤ LinearMap.range ((t : Matrix (Fin 3) (Fin 3) F) - 1).mulVecLin := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨g, hg, x, rfl⟩
    by_cases hg1 : (⟨g, hg⟩ : E) = 1
    · have hg1' : g = 1 := congrArg Subtype.val hg1
      subst hg1'
      rw [coe_one_SL3, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    · have hgt : g = t := congrArg Subtype.val (huniq _ hg1)
      subst hgt
      exact sub_mem_range_sub_one g x
  exact (Submodule.finrank_mono hle).trans (finrank_range_sub_one_le_one (h2 t htE))

theorem commN_eq_fixN_of_finrank_eq [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g)
    (hd : Module.finrank F (commN E) = Module.finrank F (fixN E)) : commN E = fixN E :=
  Submodule.eq_of_le_of_finrank_eq (commN_le_fixN_of_elemAb h2 hc) hd

end CFSG.Quasithin.MS93.S46

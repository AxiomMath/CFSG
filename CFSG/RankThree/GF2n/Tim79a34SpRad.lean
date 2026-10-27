module

public import CFSG.RankThree.GF2n.Tim79aSpPair

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped Matrix
open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

section Radical

variable {n : ℕ} {F : Type} [Field F]

theorem exists_spRad_param [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {g : StatedSp n F} (hg : g ∈ spRad a) : ∃ u, spForm a u = 0 ∧ ∃ c : F, ∀ x,
      SpExtras.mat n F g *ᵥ x = x + spForm a x • u + spForm u x • a + (c * spForm a x) • a := by
  obtain ⟨u, c, hu, hx⟩ := exists_param_of_mem_spRad ha hg
  exact ⟨u, hu, c, hx⟩

theorem exists_spRad_of_param [CharP F 2] {a u : Fin n ⊕ Fin n → F} (hu : spForm a u = 0)
    (c : F) : ∃ g ∈ spRad a, ∀ x, SpExtras.mat n F g *ᵥ x =
      x + spForm a x • u + spForm u x • a + (c * spForm a x) • a := by
  obtain ⟨z, hz, hzv⟩ := exists_mem_spRad_of_perp hu
  have hza : SpExtras.mat n F z *ᵥ a = a := by
    obtain ⟨h, -⟩ := hz
    exact h
  obtain ⟨s, hs⟩ := exists_mat_eq_spTrans a c
  have hsr : s ∈ spRad a := by
    refine ⟨?_, fun v _ => ⟨c * spForm a v, ?_⟩⟩
    · rw [hs, spTrans_mulVec, spForm_self, mul_zero, zero_smul, add_zero]
    · rw [hs, spTrans_mulVec]
  refine ⟨z * s, mul_mem hz hsr, fun x => ?_⟩
  rw [map_mul, ← Matrix.mulVec_mulVec, hs, spTrans_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, hza, hzv]

theorem spTrans_eq_one_imp {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {e : F}
    (h : spTrans a e = 1) : e = 0 := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have h1 : spTrans a e *ᵥ b = b := by rw [h, Matrix.one_mulVec]
  rw [spTrans_mulVec, hb, mul_one] at h1
  have h2 : e • a = 0 := add_left_cancel (h1.trans (add_zero b).symm)
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 ha

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {S T : Subgroup G}
    (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : G} (hx : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ s ∈ S, ∃ t ∈ T, x = s * t)
    ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, T.one_mem, (mul_one y).symm⟩
    · exact ⟨1, S.one_mem, y, hy, (one_mul y).symm⟩
  · exact ⟨1, S.one_mem, 1, T.one_mem, (mul_one 1).symm⟩
  · rintro x y _ _ ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, t₁ * t₂, T.mul_mem ht₁ ht₂, ?_⟩
    have h := hc s₂ hs₂ t₁ ht₁
    calc s₁ * t₁ * (s₂ * t₂) = s₁ * (t₁ * s₂) * t₂ := by group
      _ = s₁ * (s₂ * t₁) * t₂ := by rw [h]
      _ = s₁ * s₂ * (t₁ * t₂) := by group
  · rintro x _ ⟨s, hs, t, ht, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, t⁻¹, T.inv_mem ht, ?_⟩
    rw [hc s hs t ht, mul_inv_rev]

theorem exists_mem_param [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) {w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0) :
    ∃ s ∈ S, ∃ c : F, ∀ v, SpExtras.mat n F s *ᵥ v =
      v + spForm a v • w + spForm w v • a + (c * spForm a v) • a := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := exists_spRad_of_param hw (0 : F)
  have hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := fun s hs t ht =>
    spRadCommStmt_holds ha s (hS hs) t (le_spRad_of_isTransGroup hT ht)
  have hx₀S : x₀ ∈ S ⊔ T := hsup ▸ hx₀
  obtain ⟨s, hs, t, ht, hst⟩ := exists_mul_of_mem_sup hc hx₀S
  obtain ⟨e, he⟩ := (hT.1 t).1 ht
  have h1 : SpExtras.mat n F t⁻¹ * SpExtras.mat n F t = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have he' : SpExtras.mat n F t⁻¹ = spTrans a (-e) := by
    calc SpExtras.mat n F t⁻¹
        = SpExtras.mat n F t⁻¹ * (spTrans a e * spTrans a (-e)) := by
          rw [spTrans_mul_spTrans, add_neg_cancel, spTrans_zero, mul_one]
      _ = (SpExtras.mat n F t⁻¹ * spTrans a e) * spTrans a (-e) := by rw [mul_assoc]
      _ = spTrans a (-e) := by rw [← he, h1, one_mul]
  have ht' : ∀ v, SpExtras.mat n F t⁻¹ *ᵥ v = v + spForm a v • (0 : Fin n ⊕ Fin n → F) +
      spForm (0 : Fin n ⊕ Fin n → F) v • a + ((-e) * spForm a v) • a := by
    intro v
    rw [he', spTrans_mulVec]
    simp [spForm_zero_left]
  have hs' : s = x₀ * t⁻¹ := by rw [hst, mul_inv_cancel_right]
  refine ⟨s, hs, -e, fun v => ?_⟩
  rw [hs', mat_mul_mulVec_of_param hw (spForm_zero_right a) hx₀v ht' v]
  simp only [add_zero, zero_add, spForm_zero_right]

theorem param_eq_of_mem_inf [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hinf : S ⊓ T = ⊥)
    {w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0) {p q : StatedSp n F} {l l' : F}
    (hp : ∀ v, SpExtras.mat n F p *ᵥ v = v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hq : ∀ v, SpExtras.mat n F q *ᵥ v =
      v + spForm a v • w + spForm w v • a + (l' * spForm a v) • a)
    (hpS : p ∈ S) (hqS : q ∈ S) : l = l' := by
  have hmat : SpExtras.mat n F (p * q) = spTrans a (l + l') := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [mat_mul_mulVec_of_param hw hw hp hq v, vec_add_self, spForm_zero_left, spForm_self,
      spTrans_mulVec]
    simp
  have hpqT : p * q ∈ T := (hT.1 (p * q)).2 ⟨l + l', hmat⟩
  have hpq1 : p * q = 1 := by
    have hmem : p * q ∈ S ⊓ T := Subgroup.mem_inf.2 ⟨S.mul_mem hpS hqS, hpqT⟩
    rw [hinf] at hmem
    exact Subgroup.mem_bot.1 hmem
  have he : l + l' = 0 := spTrans_eq_one_imp ha (by rw [← hmat, hpq1, map_one])
  linear_combination he - l' * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem exists_dual {a w : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (haw : spForm a w = 0)
    (hwa : ∀ c : F, w ≠ c • a) : ∃ u, spForm a u = 0 ∧ spForm w u = 1 := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have hw0 : w - spForm w b • a ≠ 0 := by
    intro h
    apply hwa (spForm w b)
    exact sub_eq_zero.1 h
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero hw0
  have hwa' : spForm w a = 0 := spForm_eq_zero_comm haw
  set u' : Fin n ⊕ Fin n → F := y - spForm a y • b + spForm b y • a with hu'
  have hau' : spForm a u' = 0 := by
    rw [hu', spForm_add_right, spForm_sub_right, spForm_smul_right', spForm_smul_right', hb,
      spForm_self]
    ring
  have hwu' : spForm w u' = spForm (w - spForm w b • a) y := by
    rw [hu', spForm_add_right, spForm_sub_right, spForm_smul_right', spForm_smul_right', hwa',
      spForm_sub_left, spForm_smul_left']
    ring
  have hne : spForm w u' ≠ 0 := by
    rw [hwu']
    exact hy
  refine ⟨(spForm w u')⁻¹ • u', ?_, ?_⟩
  · rw [spForm_smul_right', hau', mul_zero]
  · rw [spForm_smul_right', inv_mul_cancel₀ hne]

theorem param_eq_one_of_mem [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) (hinf : S ⊓ T = ⊥)
    (hinv : ∀ (w : Fin n ⊕ Fin n → F) (g : StatedSp n F), spForm a w = 0 →
      SpExtras.mat n F g = spTrans w 1 → ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    {w : Fin n ⊕ Fin n → F} (haw : spForm a w = 0) (hwa : ∀ c : F, w ≠ c • a)
    {x : StatedSp n F} (hxS : x ∈ S) {l : F}
    (hx : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w + spForm w v • a + (l * spForm a v) • a) : l = 1 := by
  obtain ⟨u, hau, hwu⟩ := exists_dual ha haw hwa
  obtain ⟨y, hyS, lu, hy⟩ := exists_mem_param ha hT hS hsup hau
  obtain ⟨tw, htw⟩ := exists_mat_eq_spTrans w (1 : F)
  have hga : SpExtras.mat n F tw *ᵥ a = a := by
    rw [htw, spTrans_mulVec, spForm_eq_zero_comm haw, mul_zero, zero_smul, add_zero]
  have hgu : SpExtras.mat n F tw *ᵥ u = u + w := by
    rw [htw, spTrans_mulVec, hwu, mul_one, one_smul]
  have hz : tw * y * tw⁻¹ ∈ S := hinv w tw haw htw y hyS
  have hzp : ∀ v, SpExtras.mat n F (tw * y * tw⁻¹) *ᵥ v =
      v + spForm a v • (u + w) + spForm (u + w) v • a + (lu * spForm a v) • a := by
    intro v
    rw [mat_conj_mulVec_of_param hy hga v, hgu]
  have hyx : y * x ∈ S := S.mul_mem hyS hxS
  have hyxp : ∀ v, SpExtras.mat n F (y * x) *ᵥ v = v + spForm a v • (u + w) +
      spForm (u + w) v • a + ((lu + l + spForm u w) * spForm a v) • a :=
    fun v => mat_mul_mulVec_of_param hau haw hy hx v
  have hauw : spForm a (u + w) = 0 := by rw [spForm_add_right, hau, haw, add_zero]
  have key := param_eq_of_mem_inf ha hT hinf hauw hzp hyxp hz hyx
  have huw : spForm u w = -1 := by rw [spForm_comm, hwu]
  linear_combination -key - huw

theorem exists_triple {a : Fin n ⊕ Fin n → F} (hn : 3 ≤ n) (ha : a ≠ 0) :
    ∃ w₁ w₂ : Fin n ⊕ Fin n → F, spForm a w₁ = 0 ∧ spForm a w₂ = 0 ∧
      spForm a (w₁ + w₂) = 0 ∧ spForm w₁ w₂ = 0 ∧ (∀ c : F, w₁ ≠ c • a) ∧
      (∀ c : F, w₂ ≠ c • a) ∧ (∀ c : F, w₁ + w₂ ≠ c • a) := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have hba : spForm b a = -1 := by rw [spForm_comm, hb]
  obtain ⟨w₁, hw₁0, hw₁⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b]
    (by rw [Fintype.card_fin]; omega)
  have hw₁a : spForm a w₁ = 0 := hw₁ 0
  have hw₁b : spForm b w₁ = 0 := hw₁ 1
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero hw₁0
  obtain ⟨w₂, hw₂0, hw₂⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b, w₁, y]
    (by rw [Fintype.card_fin]; omega)
  have hw₂a : spForm a w₂ = 0 := hw₂ 0
  have hw₂b : spForm b w₂ = 0 := hw₂ 1
  have hw₁₂ : spForm w₁ w₂ = 0 := hw₂ 2
  have hyw₂ : spForm y w₂ = 0 := hw₂ 3
  refine ⟨w₁, w₂, hw₁a, hw₂a, by rw [spForm_add_right, hw₁a, hw₂a, add_zero], hw₁₂, ?_, ?_, ?_⟩
  · intro c hc
    have h0 : spForm b w₁ = 0 := hw₁b
    rw [hc, spForm_smul_right', hba] at h0
    have hc0 : c = 0 := by linear_combination (-1 : F) * h0
    apply hw₁0
    rw [hc, hc0, zero_smul]
  · intro c hc
    have h0 : spForm b w₂ = 0 := hw₂b
    rw [hc, spForm_smul_right', hba] at h0
    have hc0 : c = 0 := by linear_combination (-1 : F) * h0
    apply hw₂0
    rw [hc, hc0, zero_smul]
  · intro c hc
    have h0 : spForm b (w₁ + w₂) = 0 := by rw [spForm_add_right, hw₁b, hw₂b, add_zero]
    rw [hc, spForm_smul_right', hba] at h0
    have hc0 : c = 0 := by linear_combination (-1 : F) * h0
    have hsum : w₁ + w₂ = 0 := by rw [hc, hc0, zero_smul]
    apply hy
    have h1 : spForm y (w₁ + w₂) = 0 := by rw [hsum, spForm_zero_right]
    rw [spForm_add_right, hyw₂, add_zero] at h1
    have h2 := spForm_comm w₁ y
    rw [h1] at h2
    exact neg_eq_zero.1 h2.symm

end Radical

theorem no_invariant_complement_spRad {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [CharP F 2]
    [Finite F] (hF : Nat.card F = 2) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : CaseM.IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) (hinf : S ⊓ T = ⊥)
    (hinv : ∀ (w : Fin n ⊕ Fin n → F) (g : StatedSp n F), spForm a w = 0 →
      SpExtras.mat n F g = spTrans w 1 → ∀ x ∈ S, g * x * g⁻¹ ∈ S) : False := by
  obtain ⟨w₁, w₂, h1a, h2a, h3a, h12, h1c, h2c, h3c⟩ := exists_triple (F := F) hn ha
  obtain ⟨x₁, hx₁S, l₁, hx₁⟩ := exists_mem_param ha hT hS hsup h1a
  obtain ⟨x₂, hx₂S, l₂, hx₂⟩ := exists_mem_param ha hT hS hsup h2a
  have hprod : ∀ v, SpExtras.mat n F (x₁ * x₂) *ᵥ v = v + spForm a v • (w₁ + w₂) +
      spForm (w₁ + w₂) v • a + ((l₁ + l₂ + spForm w₁ w₂) * spForm a v) • a :=
    fun v => mat_mul_mulVec_of_param h1a h2a hx₁ hx₂ v
  have e3 := param_eq_one_of_mem ha hT hS hsup hinf hinv h3a h3c (S.mul_mem hx₁S hx₂S) hprod
  have e1 := param_eq_one_of_mem ha hT hS hsup hinf hinv h1a h1c hx₁S hx₁
  have e2 := param_eq_one_of_mem ha hT hS hsup hinf hinv h2a h2c hx₂S hx₂
  have h0 : (1 : F) = 0 := by linear_combination e3 - e1 - e2 - h12
  exact one_ne_zero h0

section Order

variable {n : ℕ} {F : Type} [Field F]

theorem spRad_comm [CharP F 2] (hF : Nat.card F = 2) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {g h : StatedSp n F} (hg : g ∈ spRad a) (hh : h ∈ spRad a) : g * h = h * g :=
  spRadCommStmt_holds ha g hg h hh

theorem spRad_sq [CharP F 2] (hF : Nat.card F = 2) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {g : StatedSp n F} (hg : g ∈ spRad a) : g * g = 1 := by
  obtain ⟨w, l, haw, hx⟩ := exists_param_of_mem_spRad ha hg
  refine eq_of_mat_mulVec_eq fun v => ?_
  rw [map_one, Matrix.one_mulVec, mat_mul_mulVec_of_param haw haw hx hx v, vec_add_self,
    spForm_zero_left, spForm_self, CharTwo.add_self_eq_zero]
  simp

theorem params_rel [CharP F 2] {a b : Fin n ⊕ Fin n → F} (hb : spForm a b = 1)
    {g h : StatedSp n F} {w w' : Fin n ⊕ Fin n → F} {l l' : F}
    (hx : ∀ v, SpExtras.mat n F g *ᵥ v = v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hy : ∀ v, SpExtras.mat n F h *ᵥ v =
      v + spForm a v • w' + spForm w' v • a + (l' * spForm a v) • a)
    (hgh : SpExtras.mat n F g *ᵥ b = SpExtras.mat n F h *ᵥ b) :
    ∃ lam : F, w' = w + lam • a ∧ l' = l := by
  have hgb : SpExtras.mat n F g *ᵥ b = b + w + (spForm w b + l) • a := by
    rw [hx b, hb, one_smul, mul_one]
    module
  have hhb : SpExtras.mat n F h *ᵥ b = b + w' + (spForm w' b + l') • a := by
    rw [hy b, hb, one_smul, mul_one]
    module
  rw [hgb, hhb] at hgh
  obtain ⟨lam, hlam⟩ : ∃ lam : F, lam = spForm w b + l - spForm w' b - l' := ⟨_, rfl⟩
  have hw' : w' = w + lam • a := by
    rw [hlam]
    linear_combination (norm := module) (-1 : F) • hgh
  have hB : spForm w' b = spForm w b + lam := by
    rw [hw', spForm_add_left, spForm_smul_left', hb, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hl' : l' = l := by
    linear_combination hlam - hB - lam * h2
  exact ⟨lam, hw', hl'⟩

theorem mat_eq_of_params [CharP F 2] {a : Fin n ⊕ Fin n → F} {g h : StatedSp n F}
    {w w' : Fin n ⊕ Fin n → F} {l l' lam : F}
    (hx : ∀ v, SpExtras.mat n F g *ᵥ v = v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hy : ∀ v, SpExtras.mat n F h *ᵥ v =
      v + spForm a v • w' + spForm w' v • a + (l' * spForm a v) • a)
    (hw' : w' = w + lam • a) (hl' : l' = l) : g = h := by
  refine eq_of_mat_mulVec_eq fun x => ?_
  have h2z := two_smul_vec_eq_zero ((lam * spForm a x) • a)
  rw [hx x, hy x, hw', hl', spForm_add_left, spForm_smul_left']
  linear_combination (norm := module) (-1 : F) • h2z

theorem eq_of_mulVec_eq_of_spForm_eq_one [CharP F 2] {a b : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    (hb : spForm a b = 1) {g h : StatedSp n F} (hg : g ∈ spRad a) (hh : h ∈ spRad a)
    (hgh : SpExtras.mat n F g *ᵥ b = SpExtras.mat n F h *ᵥ b) : g = h := by
  obtain ⟨w, l, -, hx⟩ := exists_param_of_mem_spRad ha hg
  obtain ⟨w', l', -, hy⟩ := exists_param_of_mem_spRad ha hh
  obtain ⟨lam, hw', hl'⟩ := params_rel hb hx hy hgh
  exact mat_eq_of_params hx hy hw' hl'

theorem natCard_ker_spFormL [Finite F] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    Nat.card (LinearMap.ker (spFormL a)) = Nat.card F ^ (2 * n - 1) := by
  have hf : spFormL a ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
    intro h
    have h0 : spFormL a y = 0 := by rw [h]; rfl
    exact hy (by simpa [spFormL] using h0)
  have h := LinearMap.finrank_range_add_finrank_ker (spFormL a)
  rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  have hfr : Module.finrank F (LinearMap.ker (spFormL a)) = 2 * n - 1 := by omega
  haveI hK : Fintype F := Fintype.ofFinite F
  haveI hV : Fintype (LinearMap.ker (spFormL a)) := Fintype.ofFinite _
  have hcard : Fintype.card (LinearMap.ker (spFormL a)) = Fintype.card F ^ (2 * n - 1) :=
    (Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker (spFormL a))).trans (by rw [hfr])
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcard

theorem spRad_card_eq_ker [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    Nat.card (spRad a) = Nat.card (LinearMap.ker (spFormL a)) := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have hΨ : ∀ g ∈ spRad a, spForm a (SpExtras.mat n F g *ᵥ b - b) = 0 := by
    intro g hg
    obtain ⟨hga, -⟩ := hg
    have h1 := spForm_mat_mulVec g a b
    rw [hga] at h1
    rw [spForm_sub_right, h1, sub_self]
  refine Nat.card_eq_of_bijective
    (fun g : spRad a => (⟨SpExtras.mat n F g.1 *ᵥ b - b, LinearMap.mem_ker.2 (hΨ g.1 g.2)⟩ :
      LinearMap.ker (spFormL a))) ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩ ⟨h, hh⟩ hgh
    have hv : SpExtras.mat n F g *ᵥ b - b = SpExtras.mat n F h *ᵥ b - b :=
      congrArg Subtype.val hgh
    exact Subtype.ext (eq_of_mulVec_eq_of_spForm_eq_one ha hb hg hh (sub_left_inj.1 hv))
  · rintro ⟨v, hv⟩
    obtain ⟨g, hg, hgx⟩ := exists_spRad_of_param (LinearMap.mem_ker.1 hv) (spForm v b)
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show SpExtras.mat n F g *ᵥ b - b = v
    rw [hgx b, hb, one_smul, mul_one]
    linear_combination (norm := module) (1 : F) • two_smul_vec_eq_zero (spForm v b • a)

theorem spRad_card [CharP F 2] (hF : Nat.card F = 2) (hn : 1 ≤ n) {a : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) : Nat.card (spRad a) = 2 ^ (2 * n - 1) := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  rw [spRad_card_eq_ker ha, natCard_ker_spFormL ha, hF]

end Order

section Tau

variable {n : ℕ} {F : Type} [Field F]

noncomputable def spTau [CharP F 2] (a u : Fin n ⊕ Fin n → F) (c : F) (hu : spForm a u = 0) :
    StatedSp n F :=
  (exists_spRad_of_param hu c).choose

theorem spTau_mem [CharP F 2] (a u : Fin n ⊕ Fin n → F) (c : F) (hu : spForm a u = 0) :
    spTau a u c hu ∈ spRad a :=
  (exists_spRad_of_param hu c).choose_spec.1

theorem spTau_mulVec [CharP F 2] (a u : Fin n ⊕ Fin n → F) (c : F) (hu : spForm a u = 0)
    (x : Fin n ⊕ Fin n → F) : SpExtras.mat n F (spTau a u c hu) *ᵥ x =
      x + spForm a x • u + spForm u x • a + (c * spForm a x) • a :=
  (exists_spRad_of_param hu c).choose_spec.2 x

theorem spTau_mul [CharP F 2] (a u u' : Fin n ⊕ Fin n → F) (c c' : F) (hu : spForm a u = 0)
    (hu' : spForm a u' = 0) :
    spTau a u c hu * spTau a u' c' hu' =
      spTau a (u + u') (c + c' + spForm u u') (by rw [spForm_add_right, hu, hu', add_zero]) := by
  refine eq_of_mat_mulVec_eq fun x => ?_
  rw [mat_mul_mulVec_of_param hu hu' (spTau_mulVec a u c hu) (spTau_mulVec a u' c' hu') x,
    spTau_mulVec]

theorem spForm_mat_mulVec_eq_zero {a u : Fin n ⊕ Fin n → F} {g : StatedSp n F}
    (hga : SpExtras.mat n F g *ᵥ a = a) (hu : spForm a u = 0) :
    spForm a (SpExtras.mat n F g *ᵥ u) = 0 := by
  have h := spForm_mat_mulVec g a u
  rw [hga] at h
  rw [h, hu]

theorem mat_spTau_zero [CharP F 2] (a : Fin n ⊕ Fin n → F) (c : F) (h0 : spForm a 0 = 0) :
    SpExtras.mat n F (spTau a 0 c h0) = spTrans a c := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [spTau_mulVec, spTrans_mulVec, spForm_zero_left]
  simp

theorem spTau_eq_iff [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {u u' : Fin n ⊕ Fin n → F} {c c' : F} (hu : spForm a u = 0) (hu' : spForm a u' = 0) :
    spTau a u c hu = spTau a u' c' hu' ↔ c = c' ∧ ∃ lam : F, u' = u + lam • a := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  constructor
  · intro h
    obtain ⟨lam, hw, hl⟩ := params_rel hb (spTau_mulVec a u c hu) (spTau_mulVec a u' c' hu')
      (by rw [h])
    exact ⟨hl.symm, lam, hw⟩
  · rintro ⟨hc, lam, hue⟩
    exact mat_eq_of_params (lam := lam) (spTau_mulVec a u c hu) (spTau_mulVec a u' c' hu') hue
      hc.symm

end Tau

end CFSG.RankThree.GF2n.Tim79a

end

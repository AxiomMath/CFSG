module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Fin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Form
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Sym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions QuadraticMap

theorem s16c1G44_card_le_four_of_pairs {G : Type*} [Group G] (E : Subgroup G) (t : G)
    (h : ∀ g ∈ E, ∀ k ∈ E, g = 1 ∨ g = t ∨ k = 1 ∨ k = t ∨ k = g ∨ k = t * g) :
    Nat.card E ≤ 4 := by
  classical
  by_cases hall : ∀ g ∈ E, g = 1 ∨ g = t
  · have hsub : (E : Set G) ⊆ {1, t} := fun g hg => by
      rcases hall g hg with h | h <;> simp [h]
    calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, t} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := by
        have h1 := Set.ncard_insert_le (1 : G) ({t} : Set G)
        rw [Set.ncard_singleton] at h1
        omega
  · push Not at hall
    obtain ⟨g₀, hg₀, hg1, hgt⟩ := hall
    have hsub : (E : Set G) ⊆ {1, t, g₀, t * g₀} := fun k hk => by
      rcases h g₀ hg₀ k hk with h | h | h | h | h | h
      · exact absurd h hg1
      · exact absurd h hgt
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, t, g₀, t * g₀} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := by
        have h0 : ({t * g₀} : Set G).ncard = 1 := Set.ncard_singleton _
        have h1 := Set.ncard_insert_le g₀ ({t * g₀} : Set G)
        have h2 := Set.ncard_insert_le t (insert g₀ ({t * g₀} : Set G))
        have h3 := Set.ncard_insert_le (1 : G) (insert t (insert g₀ ({t * g₀} : Set G)))
        omega

theorem s16c1G44_vec_inj : ∀ a < 64, ∀ b < 64, vec a = vec b → a = b := by
  decide +kernel

theorem s16c1G44_qB_eq_of_qModel_eq {a b : ℕ} (h : qModel true (vec a) = qModel true (vec b)) :
    qB true a = qB true b := by
  rw [qModel_vec, qModel_vec] at h
  cases ha : qB true a <;> cases hb : qB true b <;> simp_all

theorem s16c1G44_exists_code (g : V₀ ≃ₗ[ZMod 2] V₀) :
    ∃ m, m < 2 ^ 36 ∧ HasCode (g : V₀ →ₗ[ZMod 2] V₀) m := by
  have hinj : Function.Injective (fun m : Fin (2 ^ 36) => mat m.val) := by
    intro m m' h
    exact Fin.ext (Code.eq_of_mat_eq m.isLt m'.isLt h)
  have hcard : Fintype.card (Fin (2 ^ 36)) =
      Fintype.card (Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [Fintype.card_fin]
    show 2 ^ 36 = Fintype.card (Fin 6 → Fin 6 → ZMod 2)
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    norm_num
  have hsurj : Function.Surjective (fun m : Fin (2 ^ 36) => mat m.val) := by
    by_contra hns
    have hlt := Fintype.card_lt_of_injective_not_surjective _ hinj hns
    omega
  obtain ⟨m, hm⟩ := hsurj (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀))
  exact ⟨m.val, m.isLt, hm.symm⟩

theorem s16c1G44_pack_col {m : ℕ} (hm : m < 2 ^ 36) :
    pack (col m 0) (col m 1) (col m 2) (col m 3) (col m 4) (col m 5) = m := by
  have h63 : ∀ x : ℕ, x &&& 63 = x % 64 := fun x => by
    have := Nat.and_two_pow_sub_one_eq_mod x 6
    simpa using this
  unfold pack col
  simp only [h63, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem s16c1G44_sel_congr {v j c c' : ℕ} (h : v.testBit j = true → c = c') :
    sel v j c = sel v j c' := by
  unfold sel
  by_cases hv : v.testBit j = true
  · rw [if_pos hv, if_pos hv, h hv]
  · rw [if_neg hv, if_neg hv]

theorem s16c1G44_testBit_of_and {v M : ℕ} (h : v &&& M = v) {j : ℕ} (hj : v.testBit j = true) :
    M.testBit j = true := by
  have h1 : (v &&& M).testBit j = v.testBit j := by rw [h]
  rw [Nat.testBit_and, hj] at h1
  simpa using h1

theorem s16c1G44_actCols_congr {M v : ℕ} (hv : v &&& M = v)
    {a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ b₅ : ℕ}
    (h₀ : M.testBit 0 = true → a₀ = b₀) (h₁ : M.testBit 1 = true → a₁ = b₁)
    (h₂ : M.testBit 2 = true → a₂ = b₂) (h₃ : M.testBit 3 = true → a₃ = b₃)
    (h₄ : M.testBit 4 = true → a₄ = b₄) (h₅ : M.testBit 5 = true → a₅ = b₅) :
    actCols a₀ a₁ a₂ a₃ a₄ a₅ v = actCols b₀ b₁ b₂ b₃ b₄ b₅ v := by
  unfold actCols
  rw [s16c1G44_sel_congr (fun h => h₀ (s16c1G44_testBit_of_and hv h)),
    s16c1G44_sel_congr (fun h => h₁ (s16c1G44_testBit_of_and hv h)),
    s16c1G44_sel_congr (fun h => h₂ (s16c1G44_testBit_of_and hv h)),
    s16c1G44_sel_congr (fun h => h₃ (s16c1G44_testBit_of_and hv h)),
    s16c1G44_sel_congr (fun h => h₄ (s16c1G44_testBit_of_and hv h)),
    s16c1G44_sel_congr (fun h => h₅ (s16c1G44_testBit_of_and hv h))]

theorem s16c1G44_cond_of_full {m M : ℕ}
    (hfull : ∀ v < 64, qB true (act m v) = qB true v ∧
      (v < 32 → qB true (act m v ^^^ v) = false)) (h4 : col m 4 = 16)
    {b₀ b₁ b₂ b₃ b₅ : ℕ}
    (h₀ : M.testBit 0 = true → b₀ = col m 0) (h₁ : M.testBit 1 = true → b₁ = col m 1)
    (h₂ : M.testBit 2 = true → b₂ = col m 2) (h₃ : M.testBit 3 = true → b₃ = col m 3)
    (h₅ : M.testBit 5 = true → b₅ = col m 5) : s16c1G44_cond M b₀ b₁ b₂ b₃ b₅ := by
  intro v hv hvM
  have hact : actCols b₀ b₁ b₂ b₃ 16 b₅ v = act m v := by
    refine (s16c1G44_actCols_congr (M := M) hvM h₀ h₁ h₂ h₃ (fun _ => h4.symm) h₅).trans ?_
    rfl
  rw [hact]
  exact hfull v hv

theorem s16c1G44_act_sixteen (m : ℕ) : act m 16 = col m 4 := by
  have h0 : (16 : ℕ).testBit 0 = false := by decide
  have h1 : (16 : ℕ).testBit 1 = false := by decide
  have h2 : (16 : ℕ).testBit 2 = false := by decide
  have h3 : (16 : ℕ).testBit 3 = false := by decide
  have h4 : (16 : ℕ).testBit 4 = true := by decide
  have h5 : (16 : ℕ).testBit 5 = false := by decide
  simp [act, sel, h0, h1, h2, h3, h4, h5]

theorem s16c1G44_mem_goodList {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hm : m < 2 ^ 36)
    (hc : HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) (hiso : ∀ v, qModel true (g v) = qModel true v)
    (hfix : g (vec 16) = vec 16) (hgood : ∀ u < 32, qModel true (g (vec u) + vec u) = 0) :
    m ∈ s16c1G44_goodList := by
  have hact : ∀ n, g (vec n) = vec (act m n) := s16c1G_apply_vec hc
  have hfull : ∀ v < 64, qB true (act m v) = qB true v ∧
      (v < 32 → qB true (act m v ^^^ v) = false) := by
    intro v hv
    refine ⟨?_, fun hv32 => ?_⟩
    · apply (s16c1G44_qB_eq_of_qModel_eq (a := act m v) (b := v))
      rw [← hact v]
      exact hiso (vec v)
    · apply s16c1G_qB_eq_false
      rw [s16c1G_vec_xor, ← hact v]
      exact hgood v hv32
  have h16 : act m 16 = 16 := by
    apply s16c1G44_vec_inj _ (act_lt m 16) 16 (by norm_num)
    rw [← hact 16]
    exact hfix
  have h4 : col m 4 = 16 := by rw [← s16c1G44_act_sixteen]; exact h16
  have hpack := s16c1G44_pack_col hm
  rw [h4] at hpack
  have c17 : s16c1G44_cond 17 (col m 0) 0 0 0 0 :=
    s16c1G44_cond_of_full hfull h4 (fun _ => rfl) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  have c19 : s16c1G44_cond 19 (col m 0) (col m 1) 0 0 0 :=
    s16c1G44_cond_of_full hfull h4 (fun _ => rfl) (fun _ => rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  have c23 : s16c1G44_cond 23 (col m 0) (col m 1) (col m 2) 0 0 :=
    s16c1G44_cond_of_full hfull h4 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  have c31 : s16c1G44_cond 31 (col m 0) (col m 1) (col m 2) (col m 3) 0 :=
    s16c1G44_cond_of_full hfull h4 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun h => absurd h (by decide))
  have c63 : s16c1G44_cond 63 (col m 0) (col m 1) (col m 2) (col m 3) (col m 5) :=
    s16c1G44_cond_of_full hfull h4 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
  have hmem := s16c1G44_F1 (col m 0) (col_lt m 0) c17 (col m 1) (col_lt m 1) c19 (col m 2)
    (col_lt m 2) c23 (col m 3) (col_lt m 3) c31 (col m 5) (col_lt m 5) c63
  rwa [hpack] at hmem

theorem s16c1G44_card_le_four_normal (E : Subgroup (V₀ ≃ₗ[ZMod 2] V₀))
    (hiso : ∀ g ∈ E, ∀ v, qModel true (g v) = qModel true v)
    (hfix : ∀ g ∈ E, g (vec 16) = vec 16)
    (hgood : ∀ g ∈ E, ∀ u < 32, qModel true (g (vec u) + vec u) = 0)
    (hab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (ht : refl (vec 16) ∈ E) :
    Nat.card E ≤ 4 := by
  have hmem : ∀ g ∈ E, ∀ m, m < 2 ^ 36 → HasCode (g : V₀ →ₗ[ZMod 2] V₀) m →
      m ∈ s16c1G44_goodList := fun g hg m hm hc =>
    s16c1G44_mem_goodList hm hc (hiso g hg) (hfix g hg) (hgood g hg)
  have htc : HasCode ((refl (vec 16) : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) s16c1G44_tCode :=
    hasCode_refl 16
  refine s16c1G44_card_le_four_of_pairs E (refl (vec 16)) fun g hg k hk => ?_
  obtain ⟨mg, hmg, hcg⟩ := s16c1G44_exists_code g
  obtain ⟨mk, hmk, hck⟩ := s16c1G44_exists_code k
  have hgk : HasCode ((g * k : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (mul mg mk) :=
    hcg.mul hck
  have hkg : HasCode ((k * g : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (mul mk mg) :=
    hck.mul hcg
  have hprod : mul mg mk ∈ s16c1G44_goodList := hmem (g * k) (E.mul_mem hg hk) _ (mul_lt _ _) hgk
  have hcomm : mul mg mk = mul mk mg := by
    have h := hab g hg k hk
    rw [h] at hgk
    exact hgk.code_eq hkg (mul_lt _ _) (mul_lt _ _)
  rcases s16c1G44_F2 mg (hmem g hg mg hmg hcg) mk (hmem k hk mk hmk hck) hcomm hprod with
    h | h | h | h | h | h
  · exact Or.inl (hcg.eq_of_equiv (h ▸ hasCode_one))
  · exact Or.inr (Or.inl (hcg.eq_of_equiv (h ▸ htc)))
  · exact Or.inr (Or.inr (Or.inl (hck.eq_of_equiv (h ▸ hasCode_one))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hck.eq_of_equiv (h ▸ htc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hck.eq_of_equiv (h ▸ hcg))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hck.eq_of_equiv (h ▸ ?_))))))
    exact htc.mul hcg

@[expose] def s16c1G44_sub (P : Subgroup (Multiplicative V₀)) : Submodule (ZMod 2) V₀ where
  carrier := {x | Multiplicative.ofAdd x ∈ P}
  add_mem' := fun {x y} hx hy => by
    show Multiplicative.ofAdd (x + y) ∈ P
    rw [ofAdd_add]
    exact P.mul_mem hx hy
  zero_mem' := P.one_mem
  smul_mem' := fun c x hx => by
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · show Multiplicative.ofAdd ((0 : ZMod 2) • x) ∈ P
      rw [zero_smul]
      exact P.one_mem
    · show Multiplicative.ofAdd ((1 : ZMod 2) • x) ∈ P
      rw [one_smul]
      exact hx

theorem s16c1G44_mem_sub {P : Subgroup (Multiplicative V₀)} {x : V₀} :
    x ∈ s16c1G44_sub P ↔ Multiplicative.ofAdd x ∈ P := Iff.rfl

theorem s16c1G44_card_sub (P : Subgroup (Multiplicative V₀)) :
    Nat.card (s16c1G44_sub P) = Nat.card P :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
      invFun := fun p => ⟨Multiplicative.toAdd p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem s16c1G44_reflection {t : V₀ ≃ₗ[ZMod 2] V₀}
    (hiso : ∀ v, qModel true (t v) = qModel true v) (ht1 : t ≠ 1)
    {P : Subgroup (Multiplicative V₀)} (hP : P.index = 2)
    (htP : ∀ p ∈ P, t (Multiplicative.toAdd p) = Multiplicative.toAdd p) :
    ∃ c : V₀, qModel true c = 1 ∧ (∀ v, t v = v + polar (qModel true) v c • c) ∧
      ∀ x : V₀, Multiplicative.ofAdd x ∈ P ↔ polar (qModel true) x c = 0 := by
  have hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (qModel true) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hcardP : Nat.card P = 32 := by
    have h1 := Subgroup.card_mul_index P
    rw [hP, s16c1G_card_mul] at h1
    omega
  have hrk : Module.finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)
  have hrank : Module.finrank (ZMod 2) (s16c1G44_sub P) = 5 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := s16c1G44_sub P)
    rw [s16c1G44_card_sub, hcardP, Nat.card_zmod] at h1
    have h2 : (2 : ℕ) ^ 5 = 2 ^ Module.finrank (ZMod 2) (s16c1G44_sub P) := by
      rw [← h1]
      norm_num
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hle : s16c1G44_sub P ≤ fixSpace t := fun x hx => mem_fixSpace.2 (htP _ hx)
  have hge : 5 ≤ Module.finrank (ZMod 2) (fixSpace t) := by
    have := Submodule.finrank_mono hle
    omega
  have hfix5 : Module.finrank (ZMod 2) V₀ - 1 ≤ Module.finrank (ZMod 2) (fixSpace t) := by
    omega
  rcases CFSG.LargeExtraspecial.eq_one_or_eq_transvection_of_finrank_fixSpace
    (qModel_nondegenerate true) hO hfix5 with h | ⟨c, hqc, hform, -, -⟩
  · exact absurd h ht1
  · refine ⟨c, hqc, hform, fun x => ?_⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hqc
      exact zero_ne_one hqc
    have hne : fixSpace t ≠ ⊤ := fun htop => ht1 (LinearEquiv.ext fun v =>
      mem_fixSpace.1 (htop ▸ Submodule.mem_top))
    have hle5 : Module.finrank (ZMod 2) (fixSpace t) ≤ 5 := by
      have := Submodule.finrank_lt hne
      omega
    have heq : s16c1G44_sub P = fixSpace t :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    rw [← s16c1G44_mem_sub, heq, mem_fixSpace, hform x]
    constructor
    · intro h
      have h1 : polar (qModel true) x c • c = 0 := add_eq_left.1 h
      exact (smul_eq_zero.1 h1).resolve_right hc0
    · intro h
      rw [h, zero_smul, add_zero]

theorem s16c1G44_comm_fix {t e : V₀ ≃ₗ[ZMod 2] V₀} {c : V₀} (hqc : qModel true c = 1)
    (ht : ∀ v, t v = v + polar (qModel true) v c • c) (hcomm : e * t = t * e) : e c = c := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hqc
    exact zero_ne_one hqc
  obtain ⟨x, hx⟩ : ∃ x, polar (qModel true) x c ≠ 0 := by
    by_contra hcon
    have hall : ∀ x, polar (qModel true) x c = 0 := fun x => by
      by_contra hne
      exact hcon ⟨x, hne⟩
    exact hc0 (forall_polar_of_nondegenerate (qModel_nondegenerate true) c
      (fun y => by rw [polar_comm]; exact hall y))
  have h1 : polar (qModel true) x c = 1 := (zmod2_eq_zero_or_eq_one _).resolve_left hx
  have htx : t x = x + c := by rw [ht x, h1, one_smul]
  have h2 : e c = polar (qModel true) (e x) c • c := by
    have h3 : e (t x) = t (e x) := by
      simpa using congrArg (fun f : V₀ ≃ₗ[ZMod 2] V₀ => f x) hcomm
    rw [htx, map_add, ht (e x)] at h3
    exact add_left_cancel h3
  have hec0 : e c ≠ 0 := fun h => hc0 (e.injective (by rw [h, map_zero]))
  rcases zmod2_eq_zero_or_eq_one (polar (qModel true) (e x) c) with h | h
  · rw [h, zero_smul] at h2
    exact absurd h2 hec0
  · rw [h, one_smul] at h2
    exact h2

theorem s16c1G44_polar_perp : ∀ u < 32, polar (qModel true) (vec u) (vec 16) = 0 := by
  have h : ∀ u < 32, ((if qB true (u ^^^ 16) then 1 else 0) - (if qB true u then 1 else 0) -
      (if qB true 16 then 1 else 0) : ZMod 2) = 0 := by
    decide +kernel
  intro u hu
  have h1 := h u hu
  rw [QuadraticMap.polar, ← s16c1G_vec_xor, qModel_vec, qModel_vec, qModel_vec]
  exact h1

theorem s16c1G44_axisBound_lin (E : Subgroup (V₀ ≃ₗ[ZMod 2] V₀))
    (hiso : ∀ g ∈ E, ∀ v, qModel true (g v) = qModel true v)
    (hab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    {P : Subgroup (Multiplicative V₀)} (hP : P.index = 2)
    {t : V₀ ≃ₗ[ZMod 2] V₀} (htE : t ∈ E) (ht1 : t ≠ 1)
    (htP : ∀ p ∈ P, t (Multiplicative.toAdd p) = Multiplicative.toAdd p)
    (hgood : ∀ g ∈ E, ∀ u ∈ P,
      qModel true (g (Multiplicative.toAdd u) + Multiplicative.toAdd u) = 0) :
    Nat.card E ≤ 4 := by
  obtain ⟨c, hqc, htc, hPc⟩ := s16c1G44_reflection (hiso t htE) ht1 hP htP
  have hfixc : ∀ g ∈ E, g c = c := fun g hg => s16c1G44_comm_fix hqc htc (hab g hg t htE)
  obtain ⟨ω₀, hω₀Ω, hω₀c⟩ := s16c1G_exists_conj_nonsing hqc
  have hω₀c' : ω₀ (vec 16) = c := hω₀c
  have hω₀iso : ∀ v, qModel true (ω₀ v) = qModel true v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hω₀Ω.1
  have hωiso : ∀ v, qModel true (ω₀⁻¹ v) = qModel true v := fun v => by
    rw [← hω₀iso (ω₀⁻¹ v)]
    simp
  have hω₀pol : ∀ x y, polar (qModel true) (ω₀ x) (ω₀ y) = polar (qModel true) x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hω₀Ω.1
  have hωc : ω₀⁻¹ c = vec 16 := by rw [← hω₀c']; simp
  let φ : (V₀ ≃ₗ[ZMod 2] V₀) →* (V₀ ≃ₗ[ZMod 2] V₀) := (MulAut.conj ω₀⁻¹).toMonoidHom
  have hφ : ∀ g v, φ g v = ω₀⁻¹ (g (ω₀ v)) := fun g v => by
    simp [φ, MulAut.conj_apply]
  have hcard : Nat.card (E.map φ) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj ω₀⁻¹).injective
  rw [← hcard]
  refine s16c1G44_card_le_four_normal (E.map φ) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ v
    rw [hφ, hωiso, hiso g hg, hω₀iso]
  · rintro _ ⟨g, hg, rfl⟩
    rw [hφ, hω₀c', hfixc g hg, hωc]
  · rintro _ ⟨g, hg, rfl⟩ u hu
    have hmemP : Multiplicative.ofAdd (ω₀ (vec u)) ∈ P := by
      rw [hPc, ← hω₀c', hω₀pol]
      exact s16c1G44_polar_perp u hu
    have h1 := hgood g hg _ hmemP
    simp only [toAdd_ofAdd] at h1
    have h2 : φ g (vec u) + vec u = ω₀⁻¹ (g (ω₀ (vec u)) + ω₀ (vec u)) := by
      rw [hφ, map_add]
      simp
    rw [h2, hωiso]
    exact h1
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hab g hg h hh]
  · refine ⟨t, htE, ?_⟩
    ext x
    have hp : polar (qModel true) (ω₀ x) c = polar (qModel true) x (vec 16) := by
      rw [← hω₀c', hω₀pol]
    rw [hφ, htc (ω₀ x), map_add, map_smul, hωc, hp, refl_apply, ← polar_qModel true]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

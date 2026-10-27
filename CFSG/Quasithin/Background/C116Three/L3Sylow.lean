module

public import CFSG.Quasithin.Background.C116Three.L3Transfer
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.C116Three.L3LocalB

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

theorem Ustd_iff {γ : L3.Γ} : L3F.Ustd γ ↔ L3F.Ppt γ ∧ L3F.Pline γ := Iff.rfl

theorem Ppt_one' : L3F.Ppt (1 : L3.Γ) := by
  unfold L3F.Ppt; exact L3.act_one _

theorem Ppt_mul' {a b : L3.Γ} (ha : L3F.Ppt a) (hb : L3F.Ppt b) : L3F.Ppt (a * b) := by
  unfold L3F.Ppt at *; rw [L3.act_mul, hb, ha]

theorem Ppt_inv' {a : L3.Γ} (ha : L3F.Ppt a) : L3F.Ppt a⁻¹ := by
  unfold L3F.Ppt at *
  calc L3.act a⁻¹ L3F.e1 = L3.act a⁻¹ (L3.act a L3F.e1) := by rw [ha]
    _ = L3F.e1 := L3.act_inv_act a L3F.e1

theorem Pline_one' : L3F.Pline (1 : L3.Γ) := by
  unfold L3F.Pline; intro x hx; rw [L3.act_one]; exact hx

theorem Pline_mul' {a b : L3.Γ} (ha : L3F.Pline a) (hb : L3F.Pline b) : L3F.Pline (a * b) := by
  unfold L3F.Pline at *; intro x hx; rw [L3.act_mul]; exact ha _ (hb x hx)

theorem Pline_pow' {a : L3.Γ} (ha : L3F.Pline a) (n : ℕ) : L3F.Pline (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Pline_one'
  | succ k ih => rw [pow_succ]; exact Pline_mul' ih ha

theorem Pline_inv' {a : L3.Γ} (ha : L3F.Pline a) : L3F.Pline a⁻¹ := by
  have hpos : 0 < orderOf a := orderOf_pos a
  have hmul : a * a ^ (orderOf a - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_right hmul]
  exact Pline_pow' ha _

@[expose] def USub : Subgroup L3.Γ where
  carrier := {γ | L3F.Ustd γ}
  mul_mem' := fun {a b} ha hb => Ustd_iff.2 ⟨Ppt_mul' (Ustd_iff.1 ha).1 (Ustd_iff.1 hb).1,
    Pline_mul' (Ustd_iff.1 ha).2 (Ustd_iff.1 hb).2⟩
  one_mem' := Ustd_iff.2 ⟨Ppt_one', Pline_one'⟩
  inv_mem' := fun {a} ha => Ustd_iff.2 ⟨Ppt_inv' (Ustd_iff.1 ha).1, Pline_inv' (Ustd_iff.1 ha).2⟩

theorem card_USub : Nat.card USub = 8 := by
  have h : Nat.card USub = Nat.card {γ : L3.Γ // L3F.Ustd γ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun γ => Iff.rfl)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype, L3F.card_U]

@[expose] def sylowQ (D : L3Data G M C) : Subgroup ↥G := USub.map D.π

theorem card_sylowQ (D : L3Data G M C) : Nat.card (sylowQ D) = 8 := by
  rw [sylowQ, Subgroup.card_map_of_injective D.π_injective, card_USub]

section Syl

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

theorem jw_factorization_168 : (168 : ℕ).factorization 2 = 3 := by
  have h : (168 : ℕ) = 2 ^ 3 * 21 := by norm_num
  rw [Nat.factorization_def _ Nat.prime_two, h,
    padicValNat.mul (pow_ne_zero _ two_ne_zero) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_std (D : L3Data G M C) {P : Subgroup (MulAut V)} (hP : P ≤ G)
    (hP2 : IsPGroup 2 P) :
    ∃ g ∈ G, ∀ x ∈ P, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = g⁻¹ * x * g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥G := Finite.of_surjective D.π D.π_surj
  have hcard : Nat.card (sylowQ D) = 2 ^ (Nat.card ↥G).factorization 2 := by
    rw [card_sylowQ, D.card_G, jw_factorization_168]
    norm_num
  let S : Sylow 2 ↥G := Sylow.ofCard (sylowQ D) hcard
  have hS : (S : Subgroup ↥G) = sylowQ D := Sylow.coe_ofCard _ _
  have hP' : IsPGroup 2 ↥(P.subgroupOf G) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
  obtain ⟨Q, hPQ⟩ := hP'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥G Q S
  refine ⟨((h⁻¹ : ↥G) : MulAut V), (h⁻¹ : ↥G).2, fun x hx => ?_⟩
  have hxQ : (⟨x, hP hx⟩ : ↥G) ∈ (Q : Subgroup ↥G) := hPQ (Subgroup.mem_subgroupOf.2 hx)
  have hmem : h * ⟨x, hP hx⟩ * h⁻¹ ∈ (S : Subgroup ↥G) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxQ, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hS] at hmem
  obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.1 hmem
  refine ⟨γ, hγ, ?_⟩
  have h1 := congrArg Subtype.val hγeq
  have h2 : D.rho γ = ((D.π γ : ↥G) : MulAut V) := rfl
  rw [h2]
  simpa [mul_assoc] using h1


theorem jw_map_eq (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {g : MulAut V}
    (hg : g ∈ G) : M.map g.toMonoidHom = M ∧ C.map g.toMonoidHom = C := by
  constructor
  · apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      exact D.inv_U g hg m hm
    · intro m hm
      exact Subgroup.mem_map.2 ⟨g⁻¹ m, D.inv_U _ (G.inv_mem hg) m hm, by simp⟩
  · apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      show g c ∈ C
      rw [hCfix g hg c hc]
      exact hc
    · intro c hc
      exact Subgroup.mem_map.2 ⟨c, hc, hCfix g hg c hc⟩

theorem jw_conj_card [Finite V] (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {g : MulAut V}
    (hg : g ∈ G) (A : Subgroup (MulAut V)) :
    Nat.card ↥(B1.conjAut g A) = Nat.card ↥A ∧
      Nat.card ↥(fixV (B1.conjAut g A) ⊓ M) = Nat.card ↥(fixV A ⊓ M) ∧
      Nat.card ↥(fixMod (B1.conjAut g A) M C) = Nat.card ↥(fixMod A M C) := by
  obtain ⟨hM, hC⟩ := jw_map_eq D hCfix hg
  have hτ : Function.Injective g.toMonoidHom := g.injective
  refine ⟨B1.card_conjAut g A, ?_, ?_⟩
  · have h1 : fixV (B1.conjAut g A) ⊓ M = (fixV A ⊓ M).map g.toMonoidHom := by
      conv_lhs => rw [← hM]
      rw [B1.fixV_conjAut, Subgroup.map_inf_eq _ _ _ hτ]
    rw [h1, Subgroup.card_map_of_injective hτ]
  · have h1 := l3t_fixMod_conj g A M C
    rw [hM, hC] at h1
    rw [h1, Subgroup.card_map_of_injective hτ]

theorem jw_not_fix (D : L3Data G M C) {m : V} (hm : IsLift D m) : m ∉ fixV G := by
  intro hfix
  obtain ⟨γ, hγ⟩ := L3F.exists_move
  obtain ⟨hmM, hβ⟩ := hm
  have h1 : D.rho γ m = m := (mem_fixV.1 hfix) _ (D.rho_mem γ)
  have hmem : D.rho γ m ∈ M := D.inv_U _ (D.rho_mem γ) m hmM
  have h2 := D.β_rho γ m hmM hmem
  have h3 : (⟨D.rho γ m, hmem⟩ : ↥M) = ⟨m, hmM⟩ := Subtype.ext h1
  rw [h3, hβ] at h2
  exact hγ (Multiplicative.ofAdd.injective h2).symm

theorem jw_move (D : L3Data G M C) {m : V} (hm : IsLift D m) {g : MulAut V} (hg : g ∈ G) :
    g m ∉ fixV G := by
  intro hfix
  apply jw_not_fix D hm
  have h1 : g⁻¹ (g m) = g m := (mem_fixV.1 hfix) _ (G.inv_mem hg)
  have h2 : g⁻¹ (g m) = m := by simp
  rw [h2] at h1
  rw [h1]
  exact hfix

theorem l3core_dichotomy [Finite V] (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) :
    CoreFixed G M ∨ Bounds G M C := by
  obtain ⟨m, hm⟩ := exists_lift D
  by_cases hI : ∀ s : L3.Γ, L3F.Ustd s → D.rho s m = m
  · left
    intro P hPG hP2
    obtain ⟨g, hg, hgP⟩ := exists_conj_std D hPG hP2
    refine ⟨g m, D.inv_U g hg m hm.1, jw_move D hm hg, fun x hx => ?_⟩
    obtain ⟨γ, hγ, hγeq⟩ := hgP x hx
    have h1 := hI γ hγ
    rw [hγeq] at h1
    calc x (g m) = g ((g⁻¹ * x * g) m) := by simp [MulAut.mul_apply]
      _ = g m := by rw [h1]
  · right
    have hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m := by
      push Not at hI
      exact hI
    intro B hBG hBel
    obtain ⟨g, hg, hgB⟩ := exists_conj_std D hBG hBel.isPGroup
    have hBU : ∀ b ∈ B1.conjAut g⁻¹ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b := by
      intro b hb
      have hb' : g * b * g⁻¹ ∈ B := by simpa [B1.mem_conjAut] using hb
      obtain ⟨γ, hγ, hγeq⟩ := hgB _ hb'
      exact ⟨γ, hγ, by rw [hγeq]; group⟩
    obtain ⟨h1, h2⟩ := bounds_std D hCfix hm hII hBU (B1.isElemAbelian2_conjAut hBel)
    have hc := jw_conj_card D hCfix hg (B1.conjAut g⁻¹ B)
    rw [B1.conjAut_conjAut_inv] at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [c1, c2]
    rw [c1, c2, c3] at *
    exact ⟨h1, h2⟩

theorem l3core_tight [Finite V] (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c)
    {P : Subgroup (MulAut V)} (hP : P ≤ G) (hP2 : IsPGroup 2 P) :
    ∃ w ∈ M, w ∉ fixV G ∧ TightFixes P M w := by
  obtain ⟨m, hm⟩ := exists_lift D
  obtain ⟨g, hg, hgP⟩ := exists_conj_std D hP hP2
  refine ⟨g m, D.inv_U g hg m hm.1, jw_move D hm hg, ?_⟩
  by_cases hI : ∀ s : L3.Γ, L3F.Ustd s → D.rho s m = m
  · intro B hBP hBel _ b hb
    obtain ⟨γ, hγ, hγeq⟩ := hgP b (hBP hb)
    have h1 := hI γ hγ
    rw [hγeq] at h1
    calc b (g m) = g ((g⁻¹ * b * g) m) := by simp [MulAut.mul_apply]
      _ = g m := by rw [h1]
  · have hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m := by
      push Not at hI
      exact hI
    intro B hBP hBel ht b hb
    have hBU : ∀ b ∈ B1.conjAut g⁻¹ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b := by
      intro b hb
      have hb' : g * b * g⁻¹ ∈ B := by simpa [B1.mem_conjAut] using hb
      obtain ⟨γ, hγ, hγeq⟩ := hgP _ (hBP hb')
      exact ⟨γ, hγ, by rw [hγeq]; group⟩
    have hc := jw_conj_card D hCfix hg (B1.conjAut g⁻¹ B)
    rw [B1.conjAut_conjAut_inv] at hc
    obtain ⟨c1, c2, -⟩ := hc
    have ht' : Nat.card ↥(B1.conjAut g⁻¹ B) * Nat.card ↥(fixV (B1.conjAut g⁻¹ B) ⊓ M) =
        Nat.card M := by
      rw [← c1, ← c2]
      exact ht
    have hbb : g⁻¹ * b * g ∈ B1.conjAut g⁻¹ B := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hb
    have := tight_std D hCfix hm hII hBU (B1.isElemAbelian2_conjAut hBel) ht' _ hbb
    calc b (g m) = g ((g⁻¹ * b * g) m) := by simp [MulAut.mul_apply]
      _ = g m := by rw [this]

end Syl

end CFSG.Quasithin.C116Three

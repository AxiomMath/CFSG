module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

section Linear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem uc22s206e_common_eigen {A : Type*} (P : A → Module.End F V)
    (hcomm : ∀ a b, Commute (P a) (P b)) (hsq : ∀ a, P a * P a = 1) {e : Module.End F V}
    (he : ∀ a, Commute e (P a)) {v₀ : V} (hv₀ : v₀ ≠ 0) (hev₀ : e v₀ = -v₀) (s : Finset A) :
    ∃ v : V, v ≠ 0 ∧ e v = -v ∧ ∀ a ∈ s, P a v = v ∨ P a v = -v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨v₀, hv₀, hev₀, by simp⟩
  | insert j s hj ih =>
    obtain ⟨v, hv0, hev, hv⟩ := ih
    have hjj : P j (P j v) = v := by
      rw [← Module.End.mul_apply, hsq, Module.End.one_apply]
    have hej : e (P j v) = P j (e v) := by
      rw [← Module.End.mul_apply, (he j).eq, Module.End.mul_apply]
    have haj : ∀ a, P a (P j v) = P j (P a v) := fun a => by
      rw [← Module.End.mul_apply, (hcomm a j).eq, Module.End.mul_apply]
    by_cases h : v + P j v = 0
    · refine ⟨v, hv0, hev, fun a ha => ?_⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr (eq_neg_of_add_eq_zero_right h)
      · exact hv a ha
    · refine ⟨v + P j v, h, ?_, fun a ha => ?_⟩
      · rw [map_add, hej, hev, map_neg, neg_add]
      · rcases Finset.mem_insert.mp ha with rfl | ha
        · left
          rw [map_add, hjj, add_comm]
        · rcases hv a ha with h1 | h1
          · left
            rw [map_add, haj, h1]
          · right
            rw [map_add, haj, h1, map_neg, neg_add]

theorem uc22s206e_linearIndependent {A ι : Type*} (P : A → Module.End F V)
    (hcomm : ∀ a b, Commute (P a) (P b)) (χ : ι → A → F) (hχ : Function.Injective χ)
    (v : ι → V) (hv : ∀ i a, P a (v i) = χ i a • v i) (hv0 : ∀ i, v i ≠ 0) :
    LinearIndependent F v := by
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo P
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  refine (hind.comp hχ).linearIndependent _ (fun i => ?_) hv0
  simp only [Function.comp_apply, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  exact fun a => ⟨1, by simp [hv i a]⟩

theorem uc22s206e_linearIndependent_sub {n : ℕ} {W : Fin (n + 1) → V}
    (hW : LinearIndependent F W) : LinearIndependent F (fun i : Fin n => W i.succ - W 0) := by
  rw [Fintype.linearIndependent_iff] at hW ⊢
  intro c hc i
  have h := hW (Fin.cons (-∑ j, c j) c) ?_
  · simpa using h i.succ
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    simp only [smul_sub, Finset.sum_sub_distrib] at hc
    rw [← Finset.sum_smul] at hc
    rw [neg_smul, neg_add_eq_sub]
    exact hc

theorem uc22s206e_mem_range {Γ : Type*} [Group Γ] (P : Γ →* Module.End F V) (g : Γ) (n : ℕ)
    (v : V) : P (g ^ n) v - v ∈ LinearMap.range (P g - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : P (g ^ (n + 1)) v - v = (P g - 1) (P (g ^ n) v) + (P (g ^ n) v - v) := by
      rw [pow_succ', map_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      abel
    rw [h]
    exact add_mem (LinearMap.mem_range_self _ _) ih

theorem uc22s206e_six {Γ : Type*} [Group Γ] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (P : Γ →* Module.End F V) {E : Subgroup Γ} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hE8 : Nat.card E = 8) (hPE : ∀ e ∈ E, P e = 1 → e = 1) {g : Γ} (hg7 : g ^ 7 = 1)
    (hgE : g ∈ normalizer (E : Set Γ)) (hfix : ∀ e ∈ E, g * e * g⁻¹ = e → e = 1) :
    6 ≤ Module.finrank F (LinearMap.range (P g - 1)) := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE8]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEsq : ∀ a ∈ E, a * a = 1 := fun a ha => by rw [← pow_two]; exact hE.2 a ha
  have hPsq : ∀ a ∈ E, P a * P a = 1 := fun a ha => by rw [← map_mul, hEsq a ha, map_one]
  have hPc : ∀ a ∈ E, ∀ b ∈ E, Commute (P a) (P b) := fun a ha b hb => by
    show P a * P b = P b * P a
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hPinv : ∀ (a : Γ) (x : V), P a⁻¹ (P a x) = x := fun a x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e₀ ∈ E, e₀ ≠ 1 := by
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE8]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : E)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨v, hv⟩ : ∃ v, P e₀ v ≠ v := by
    by_contra h
    push Not at h
    exact he₀1 (hPE e₀ he₀ (LinearMap.ext h))
  have hu0 : v - P e₀ v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have heu : P e₀ (v - P e₀ v) = -(v - P e₀ v) := by
    rw [map_sub, ← Module.End.mul_apply, hPsq e₀ he₀, Module.End.one_apply, neg_sub]
  obtain ⟨w, hw0, hew, hw⟩ := uc22s206e_common_eigen (fun a : E => P a)
    (fun a b => hPc a a.2 b b.2) (fun a => hPsq a a.2) (fun a => hPc e₀ he₀ a a.2) hu0 heu
    Finset.univ
  have hw' : ∀ a ∈ E, P a w = w ∨ P a w = -w := fun a ha => hw ⟨a, ha⟩ (Finset.mem_univ _)
  have hwn : w ≠ -w := by
    intro h
    apply hw0
    have h2w : (2 : F) • w = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h]
      exact add_neg_cancel w
    exact (smul_eq_zero.mp h2w).resolve_left h2
  set χ : Γ → F := fun a => if P a w = w then 1 else -1 with hχ
  have hχw : ∀ a ∈ E, P a w = χ a • w := by
    intro a ha
    simp only [hχ]
    split_ifs with h
    · rw [h, one_smul]
    · rw [(hw' a ha).resolve_left h, neg_one_smul]
  have hgn : ∀ n : ℕ, g ^ n ∈ normalizer (E : Set Γ) := fun n => pow_mem hgE n
  have hconj : ∀ (n : ℕ) (a : Γ), a ∈ E → (g ^ n)⁻¹ * a * g ^ n ∈ E := fun n a ha => by
    have h := (mem_normalizer_iff.mp (inv_mem (hgn n)) a).mp ha
    rwa [inv_inv] at h
  set W : Fin 7 → V := fun i => P (g ^ (i : ℕ)) w with hW
  set χ' : Fin 7 → E → F := fun i a => χ ((g ^ (i : ℕ))⁻¹ * a * g ^ (i : ℕ)) with hχ'
  have hWe : ∀ i (a : E), P a (W i) = χ' i a • W i := by
    intro i a
    have h1 : P a (P (g ^ (i : ℕ)) w) =
        P (g ^ (i : ℕ)) (P ((g ^ (i : ℕ))⁻¹ * a * g ^ (i : ℕ)) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    simp only [hW, hχ']
    rw [h1, hχw _ (hconj i a a.2), map_smul]
  have hW0 : ∀ i, W i ≠ 0 := by
    intro i h
    apply hw0
    rw [← hPinv (g ^ (i : ℕ)) w]
    simp only [hW] at h
    rw [h, map_zero]
  have key : ∀ i j : Fin 7, (i : ℕ) < j → χ' i = χ' j → False := by
    intro i j hij heq
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = i + k := ⟨j - i, by omega⟩
    have hk6 : k ≤ 6 := by have := j.2; omega
    set h := g ^ k with hh
    have hhb : ∀ b ∈ E, h⁻¹ * b * h ∈ E := fun b hb => hconj k b hb
    have hkey : ∀ b ∈ E, P (h⁻¹ * b * h) w = P b w := by
      intro b hb
      have hmem : g ^ (i : ℕ) * b * (g ^ (i : ℕ))⁻¹ ∈ E :=
        (mem_normalizer_iff.mp (hgn i) b).mp hb
      have h1 := congrFun heq ⟨_, hmem⟩
      simp only [hχ'] at h1
      rw [show (g ^ (i : ℕ))⁻¹ * (g ^ (i : ℕ) * b * (g ^ (i : ℕ))⁻¹) * g ^ (i : ℕ) = b by group,
        show (g ^ (j : ℕ))⁻¹ * (g ^ (i : ℕ) * b * (g ^ (i : ℕ))⁻¹) * g ^ (j : ℕ) =
          h⁻¹ * b * h by rw [hk, pow_add, hh]; group] at h1
      rw [hχw _ hb, hχw _ (hhb b hb), h1]
    let D : Subgroup Γ :=
      { carrier := {b | b ∈ E ∧ P b w = w}
        mul_mem' := fun {a b} ha hb =>
          ⟨mul_mem ha.1 hb.1, by rw [map_mul, Module.End.mul_apply, hb.2, ha.2]⟩
        one_mem' := ⟨one_mem _, by rw [map_one, Module.End.one_apply]⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
          have h3 := hPinv a w
          rwa [ha.2] at h3⟩ }
    have hDE : D ≤ E := fun b hb => hb.1
    haveI : Finite D := Finite.of_injective _ (inclusion_injective hDE)
    have hD2 : IsPGroup 2 D := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 x (hDE x.2)
    have hhE : h ∈ normalizer (E : Set Γ) := hgn k
    have hhN : h ∈ normalizer (D : Set Γ) := by
      rw [mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨hn, hnw⟩
        have hE' : h * n * h⁻¹ ∈ E := (mem_normalizer_iff.mp hhE n).mp hn
        refine ⟨hE', ?_⟩
        rw [← hkey _ hE', show h⁻¹ * (h * n * h⁻¹) * h = n by group]
        exact hnw
      · rintro ⟨hn, hnw⟩
        have hE' : n ∈ E := (mem_normalizer_iff.mp hhE n).mpr hn
        refine ⟨hE', ?_⟩
        rw [← hkey _ hn, show h⁻¹ * (h * n * h⁻¹) * h = n by group] at hnw
        exact hnw
    have hk7 : Nat.Coprime k (orderOf g) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hg7)
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega)))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk7
    have hcg : ∀ x : Γ, h * x * h⁻¹ = x → g * x * g⁻¹ = x := by
      intro x hx
      have hc : Commute h x := by
        show h * x = x * h
        calc h * x = h * x * h⁻¹ * h := by group
          _ = x * h := by rw [hx]
      have hc' : Commute (h ^ m) x := hc.pow_left m
      rw [hh, hm] at hc'
      rw [hc'.eq, mul_inv_cancel_right]
    have hbE : g * e₀ * g⁻¹ ∈ E := (mem_normalizer_iff.mp hgE e₀).mp he₀
    have hb1 : g * e₀ * g⁻¹ ≠ 1 := fun h' => he₀1 (conj_eq_one_iff.mp h')
    have hbe : g * e₀ * g⁻¹ ≠ e₀ := fun h' => he₀1 (hfix e₀ he₀ h')
    obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
      rcases hw' _ hbE with h' | h'
      · exact ⟨_, ⟨hbE, h'⟩, hb1⟩
      · refine ⟨e₀ * (g * e₀ * g⁻¹), ⟨mul_mem he₀ hbE, ?_⟩, fun h'' => hbe ?_⟩
        · rw [map_mul, Module.End.mul_apply, h', map_neg, hew, neg_neg]
        · rw [eq_inv_of_mul_eq_one_right h'', inv_eq_of_mul_eq_one_right (hEsq e₀ he₀)]
    obtain ⟨E', hE'D, -, hE'8, -, -⟩ :=
      uc22s206d_e8 hD2 (c := h) (by rw [hh, ← pow_mul, mul_comm, pow_mul, hg7, one_pow]) hhN
        ⟨x, hxD, fun h' => hx1 (hfix x (hDE hxD) (hcg x h'))⟩
    have hDeq : D = E :=
      eq_of_le_of_card_ge hDE (by rw [hE8, ← hE'8]; exact card_le_of_le hE'D)
    have he₀D : e₀ ∈ D := by
      rw [hDeq]
      exact he₀
    exact hwn (he₀D.2.symm.trans hew)
  have hinj : Function.Injective χ' := by
    intro i j hij
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key i j h hij).elim
    · exact Fin.ext h
    · exact (key j i h hij.symm).elim
  have hli : LinearIndependent F W :=
    uc22s206e_linearIndependent (fun a : E => P a) (fun a b => hPc a a.2 b b.2) χ' hinj W hWe
      hW0
  have hz := uc22s206e_linearIndependent_sub hli
  have hmem : ∀ i : Fin 6, W i.succ - W 0 ∈ LinearMap.range (P g - 1) := by
    intro i
    have h0 : W 0 = w := by simp [hW]
    rw [h0]
    exact uc22s206e_mem_range P g ((i.succ : Fin 7) : ℕ) w
  have hz' : LinearIndependent F
      (fun i : Fin 6 => (⟨W i.succ - W 0, hmem i⟩ : LinearMap.range (P g - 1))) :=
    LinearIndependent.of_comp (LinearMap.range (P g - 1)).subtype hz
  have h6 := hz'.fintype_card_le_finrank
  rwa [Fintype.card_fin] at h6

end Linear

theorem uc22s206e_six_GL {d p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup (GL (Fin d) (ZMod p))} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hE8 : Nat.card E = 8) {g : GL (Fin d) (ZMod p)} (hg7 : g ^ 7 = 1)
    (hgE : g ∈ normalizer (E : Set (GL (Fin d) (ZMod p))))
    (hfix : ∀ e ∈ E, g * e * g⁻¹ = e → e = 1) :
    6 ≤ Module.finrank (ZMod p) (LinearMap.range
      ((Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1)) := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hPE : ∀ e ∈ E, ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) e = 1 → e = 1 := by
    intro e _ he
    have h1 : Matrix.GeneralLinearGroup.toLin e = 1 := Units.ext he
    exact Matrix.GeneralLinearGroup.toLin.injective (h1.trans (map_one _).symm)
  have h := uc22s206e_six (F := ZMod p) (V := Fin d → ZMod p) h2
    ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) hE hE8 hPE hg7 hgE hfix
  have hPg : ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) g =
        Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) (ZMod p)) :=
    Matrix.GeneralLinearGroup.coe_toLin g
  rw [hPg] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

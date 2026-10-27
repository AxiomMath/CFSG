module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CGenAux_ext {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) {e₁ e₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

private lemma hdRo7CGenAux_diagMap_apply {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (d : Fin m → (ZMod p)ˣ) (k : Fin m) :
    ZS.diagMap p b d (b k) = (d k : ZMod p) • b k := by
  apply b.equivFun.injective
  rw [map_smul]
  rw [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hk : b.equivFun (b k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hk]
  funext j
  by_cases h : j = k
  · subst h; rfl
  · simp [Pi.single_apply, h]

private noncomputable def hdRo7CGenAux_sgn {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k : Fin m) :
    V ≃ₗ[ZMod p] V :=
  ZS.diagMap p b (fun l => if l = k then -1 else 1)

private lemma hdRo7CGenAux_sgn_apply {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k l : Fin m) :
    hdRo7CGenAux_sgn b k (b l) = (if l = k then -1 else 1 : ZMod p) • b l := by
  rw [hdRo7CGenAux_sgn, hdRo7CGenAux_diagMap_apply]
  congr 1
  by_cases h : l = k <;> simp [h]

private lemma hdRo7CGenAux_conj_sgn {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (s0 : V ≃ₗ[ZMod p] V)
    (i : Fin (n + 1)) (ε : ZMod p) (hi0 : i ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (h0 : s0 (b 0) = ε • b i) (hi : s0 (b i) = ε • b 0)
    (hj : ∀ j, j ≠ 0 → j ≠ i → s0 (b j) = b j) :
    s0 * hdRo7CGenAux_sgn b i * s0⁻¹ = hdRo7CGenAux_sgn b 0 := by
  have hs0sq : s0 * s0 = 1 := by
    apply hdRo7CGenAux_ext (b := b)
    intro k
    rw [LinearEquiv.mul_apply]
    change s0 (s0 (b k)) = b k
    by_cases hk0 : k = 0
    · subst hk0
      rw [h0, map_smul, hi, smul_smul]
      rcases hε with h | h <;> rw [h] <;> simp
    · by_cases hki : k = i
      · subst hki
        rw [hi, map_smul, h0, smul_smul]
        rcases hε with h | h <;> rw [h] <;> simp
      · rw [hj k hk0 hki, hj k hk0 hki]
  have hs0inv : s0⁻¹ = s0 := inv_eq_of_mul_eq_one_right hs0sq
  rw [hs0inv]
  apply hdRo7CGenAux_ext (b := b)
  intro k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  by_cases hk0 : k = 0
  · rw [hk0]
    calc (s0 * hdRo7CGenAux_sgn b i * s0) (b 0)
        = s0 (hdRo7CGenAux_sgn b i (s0 (b 0))) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s0 (hdRo7CGenAux_sgn b i (ε • b i)) := by rw [h0]
      _ = s0 (ε • hdRo7CGenAux_sgn b i (b i)) := by rw [map_smul]
      _ = s0 (ε • ((-1 : ZMod p) • b i)) := by rw [hdRo7CGenAux_sgn_apply, if_pos rfl]
      _ = s0 ((ε * -1) • b i) := by rw [smul_smul]
      _ = (ε * -1) • s0 (b i) := by rw [map_smul]
      _ = (ε * -1) • (ε • b 0) := by rw [hi]
      _ = ((ε * -1) * ε) • b 0 := by rw [smul_smul]
      _ = (-1 : ZMod p) • b 0 := by rcases hε with h | h <;> rw [h] <;> simp
      _ = hdRo7CGenAux_sgn b 0 (b 0) := by rw [hdRo7CGenAux_sgn_apply, if_pos rfl]
  · by_cases hki : k = i
    · rw [hki]
      calc (s0 * hdRo7CGenAux_sgn b i * s0) (b i)
          = s0 (hdRo7CGenAux_sgn b i (s0 (b i))) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = s0 (hdRo7CGenAux_sgn b i (ε • b 0)) := by rw [hi]
        _ = s0 (ε • hdRo7CGenAux_sgn b i (b 0)) := by rw [map_smul]
        _ = s0 (ε • ((1 : ZMod p) • b 0)) := by
              rw [hdRo7CGenAux_sgn_apply, if_neg (fun h : (0 : Fin (n + 1)) = i => hi0 h.symm)]
        _ = s0 (ε • b 0) := by rw [one_smul]
        _ = ε • s0 (b 0) := by rw [map_smul]
        _ = ε • (ε • b i) := by rw [h0]
        _ = (ε * ε) • b i := by rw [smul_smul]
        _ = (1 : ZMod p) • b i := by rcases hε with h | h <;> rw [h] <;> simp
        _ = hdRo7CGenAux_sgn b 0 (b i) := by rw [hdRo7CGenAux_sgn_apply, if_neg hi0, one_smul]
    · calc (s0 * hdRo7CGenAux_sgn b i * s0) (b k)
          = s0 (hdRo7CGenAux_sgn b i (s0 (b k))) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = s0 (hdRo7CGenAux_sgn b i (b k)) := by rw [hj k hk0 hki]
        _ = s0 ((1 : ZMod p) • b k) := by rw [hdRo7CGenAux_sgn_apply, if_neg hki]
        _ = s0 (b k) := by rw [one_smul]
        _ = b k := by rw [hj k hk0 hki]
        _ = hdRo7CGenAux_sgn b 0 (b k) := by rw [hdRo7CGenAux_sgn_apply, if_neg hk0, one_smul]

private lemma hdRo7CGenAux_permMap_apply {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ZS.permMap p b σ (b k) = b (σ k) :=
  Module.Basis.equiv_apply (b := b) (b' := b) (e := σ) (i := k)

private lemma hdRo7CGenAux_permMap_mul {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ τ : Equiv.Perm (Fin m)) :
    ZS.permMap p b (σ * τ) = ZS.permMap p b σ * ZS.permMap p b τ := by
  apply hdRo7CGenAux_ext (b := b)
  intro k
  rw [LinearEquiv.mul_apply, hdRo7CGenAux_permMap_apply, hdRo7CGenAux_permMap_apply,
    hdRo7CGenAux_permMap_apply, Equiv.Perm.mul_apply]

private lemma hdRo7CGenAux_permMap_one {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    ZS.permMap p b (1 : Equiv.Perm (Fin m)) = 1 := by
  rw [ZS.permMap, show (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) from rfl,
    Module.Basis.equiv_refl]
  rfl

private lemma hdRo7CGenAux_list_prod_sgn_apply {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (l : List (Fin m)) (k : Fin m) :
    (l.map (fun i => hdRo7CGenAux_sgn b i)).prod (b k) =
      (l.map (fun i => (if k = i then -1 else 1 : ZMod p))).prod • b k := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, map_smul,
      hdRo7CGenAux_sgn_apply, smul_smul]
    rw [mul_comm]

private lemma hdRo7CGenAux_list_prod_sign {p : ℕ} {m : ℕ} (l : List (Fin m)) (hnd : l.Nodup)
    (k : Fin m) :
    (l.map (fun i => (if k = i then -1 else 1 : ZMod p))).prod =
      (if k ∈ l then -1 else 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : i ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, List.prod_cons, ih hnd']
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_neg hnot, if_pos (List.mem_cons_self)]
      ring
    · rw [if_neg hki]
      by_cases hmem : k ∈ l
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem i hmem)]
        ring
      · rw [if_neg hmem, if_neg (fun h => by
            rcases List.mem_cons.mp h with h' | h'
            · exact hki h'
            · exact hmem h')]
        ring

private lemma hdRo7CGenAux_sp_to_full {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V} {a : V ≃ₗ[ZMod p] V}
    (h : C2SP p b a) : C2Full p b a := by
  obtain ⟨σ, c, hσ, hc0, hc, ha⟩ := h
  exact ⟨σ, c, hc, ha⟩

private lemma hdRo7CGenAux_signX_to_full {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a : V ≃ₗ[ZMod p] V} (h : C2SignX p b a) : C2Full p b a := by
  refine ⟨1, fun k => if k = 0 then -1 else 1, ?_, ?_⟩
  · intro k; by_cases hk : k = 0 <;> simp [hk]
  · intro k
    change a (b k) = (if k = 0 then -1 else 1 : ZMod p) • b k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, h.1]; simp
    · rw [if_neg hk, h.2 k hk, one_smul]

private lemma hdRo7CGenAux_swap_to_full {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a : V ≃ₗ[ZMod p] V} (h : C2Swap p b a) : C2Full p b a := by
  obtain ⟨i, ε, hi0, hε, h0, hi, hj⟩ := h
  refine ⟨Equiv.swap 0 i, fun k => if k = 0 then ε else if k = i then ε else 1, ?_, ?_⟩
  · intro k
    change (if k = 0 then ε else if k = i then ε else 1) = 1 ∨
      (if k = 0 then ε else if k = i then ε else 1) = -1
    by_cases hk0 : k = 0
    · rw [if_pos hk0]; exact hε
    · rw [if_neg hk0]
      by_cases hki : k = i
      · rw [if_pos hki]; exact hε
      · rw [if_neg hki]; exact Or.inl rfl
  · intro k
    change a (b k) = (if k = 0 then ε else if k = i then ε else 1) • b (Equiv.swap 0 i k)
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, h0, Equiv.swap_apply_left]
    · by_cases hki : k = i
      · subst hki
        rw [if_neg hi0, if_pos rfl, hi, Equiv.swap_apply_right]
      · rw [if_neg hk0, if_neg hki, hj k hk0 hki, Equiv.swap_apply_of_ne_of_ne hk0 hki,
          one_smul]

private noncomputable def hdRo7CGenAux_fullSubgroup (p : ℕ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {a | C2Full p b a}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_⟩
    · intro i; left; rfl
    · intro i; simp
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, ha⟩ ⟨σ', c', hc', ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_⟩
    · intro i
      change c' i * c (σ' i) = 1 ∨ c' i * c (σ' i) = -1
      rcases hc' i with h | h <;> rcases hc (σ' i) with h2 | h2
      · left; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
    · intro i
      rw [LinearEquiv.mul_apply, ha', map_smul, ha, Equiv.Perm.mul_apply, smul_smul]
  inv_mem' := by
    rintro a ⟨σ, c, hc, ha⟩
    refine ⟨σ.symm, fun j => c (σ.symm j), ?_, ?_⟩
    · intro j; exact hc (σ.symm j)
    · intro j
      change a.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq, map_smul, ha, Equiv.apply_symm_apply, smul_smul]
      have hcc : c (σ.symm j) * c (σ.symm j) = 1 := by
        rcases hc (σ.symm j) with h | h <;> rw [h] <;> ring
      rw [hcc, one_smul]

theorem c2_gen_holds :
    ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
      (AL Q : Subgroup (V ≃ₗ[ZMod p] V)) (S : Set (V ≃ₗ[ZMod p] V)),
      (∀ a, a ∈ AL ↔ C2SP p b a) →
      (∀ s ∈ S, s ∈ Q ∧ GGLinRefl s ∧ (C2SP p b s ∨ C2SignX p b s ∨ C2Swap p b s)) →
      Q = Subgroup.closure S → (∃ s ∈ S, C2Swap p b s) →
      ∃ F : Subgroup (V ≃ₗ[ZMod p] V), (∀ a, a ∈ F ↔ C2Full p b a) ∧ AL ⊔ Q = F := by
  intro p _ _ n _ V _ _ b AL Q S hAL hS hQ hswap
  classical
  let F : Subgroup (V ≃ₗ[ZMod p] V) := hdRo7CGenAux_fullSubgroup p b
  have hF : ∀ a, a ∈ F ↔ C2Full p b a := fun a => Iff.rfl
  let M : Subgroup (V ≃ₗ[ZMod p] V) := AL ⊔ Q
  have hMl : ∀ {x : V ≃ₗ[ZMod p] V}, x ∈ AL → x ∈ M := by
    intro x hx; change x ∈ AL ⊔ Q; exact (le_sup_left : AL ≤ AL ⊔ Q) hx
  have hMr : ∀ {x : V ≃ₗ[ZMod p] V}, x ∈ Q → x ∈ M := by
    intro x hx; change x ∈ AL ⊔ Q; exact (le_sup_right : Q ≤ AL ⊔ Q) hx
  obtain ⟨s0, hs0S, hs0swap⟩ := hswap
  have hs0Q : s0 ∈ Q := (hS s0 hs0S).1
  have hs0M : s0 ∈ M := hMr hs0Q
  obtain ⟨i, ε, hi0, hε, ha0, hai, haj⟩ := hs0swap
  have h0i : (0 : Fin (n + 1)) ≠ i := fun h => hi0 h.symm
  have hsgnAL : ∀ k, k ≠ 0 → hdRo7CGenAux_sgn b k ∈ AL := by
    intro k hk
    rw [hAL]
    refine ⟨1, fun l => if l = k then -1 else 1, ?_, ?_, ?_, ?_⟩
    · rfl
    · change (if (0 : Fin (n + 1)) = k then -1 else 1 : ZMod p) = 1
      rw [if_neg (fun h => hk h.symm)]
    · intro l
      change (if l = k then -1 else 1 : ZMod p) = 1 ∨
        (if l = k then -1 else 1 : ZMod p) = -1
      by_cases hl : l = k <;> simp [hl]
    · intro l
      change hdRo7CGenAux_sgn b k (b l) = (if l = k then -1 else 1 : ZMod p) • b l
      rw [hdRo7CGenAux_sgn_apply]
  have hEiM : hdRo7CGenAux_sgn b i ∈ M := hMl (hsgnAL i hi0)
  have htau0 : s0 * hdRo7CGenAux_sgn b i * s0⁻¹ = hdRo7CGenAux_sgn b 0 :=
    hdRo7CGenAux_conj_sgn b s0 i ε hi0 hε ha0 hai haj
  have hsgnM : ∀ k, hdRo7CGenAux_sgn b k ∈ M := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [← htau0]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs0M hEiM) (Subgroup.inv_mem _ hs0M)
    · exact hMl (hsgnAL k hk)
  have huiM : ZS.permMap p b (Equiv.swap 0 i) ∈ M := by
    by_cases hε1 : ε = 1
    · have hui : ZS.permMap p b (Equiv.swap 0 i) = s0 := by
        apply hdRo7CGenAux_ext (b := b)
        intro k
        by_cases hk0 : k = 0
        · rw [hk0]
          simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_left, ha0, hε1]
        · by_cases hki : k = i
          · rw [hki]
            simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_right, hai, hε1]
          · simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_of_ne_of_ne hk0 hki,
              haj k hk0 hki]
      rw [hui]; exact hs0M
    · have hεm : ε = -1 := by
        rcases hε with h | h
        · exact absurd h hε1
        · exact h
      have ha0' : s0 (b 0) = -b i := by rw [ha0, hεm]; simp
      have hai' : s0 (b i) = -b 0 := by rw [hai, hεm]; simp
      have hui : ZS.permMap p b (Equiv.swap 0 i) =
          hdRo7CGenAux_sgn b i * s0 * hdRo7CGenAux_sgn b i := by
        apply hdRo7CGenAux_ext (b := b)
        intro k
        by_cases hk0 : k = 0
        · rw [hk0]
          simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_left, LinearEquiv.mul_apply,
            hdRo7CGenAux_sgn_apply, ha0', h0i]
        · by_cases hki : k = i
          · rw [hki]
            simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_right, LinearEquiv.mul_apply,
              hdRo7CGenAux_sgn_apply, hai', h0i]
          · simp [hdRo7CGenAux_permMap_apply, Equiv.swap_apply_of_ne_of_ne hk0 hki,
              LinearEquiv.mul_apply, hdRo7CGenAux_sgn_apply, haj k hk0 hki, hk0, hki]
      rw [hui]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hEiM hs0M) hEiM
  have huM : ∀ j, j ≠ 0 → ZS.permMap p b (Equiv.swap 0 j) ∈ M := by
    intro j hj0
    by_cases hji : j = i
    · subst hji; exact huiM
    · have hpiAL : ZS.permMap p b (Equiv.swap i j) ∈ AL := by
        rw [hAL]
        refine ⟨Equiv.swap i j, fun _ => 1, ?_, ?_, ?_, ?_⟩
        · rw [Equiv.swap_apply_of_ne_of_ne (fun h : (0 : Fin (n + 1)) = i => hi0 h.symm)
              (fun h : (0 : Fin (n + 1)) = j => hj0 h.symm)]
        · rfl
        · intro l; left; rfl
        · intro l; rw [hdRo7CGenAux_permMap_apply, one_smul]
      have hpiM : ZS.permMap p b (Equiv.swap i j) ∈ M := hMl hpiAL
      have hpiinv : (ZS.permMap p b (Equiv.swap i j))⁻¹ = ZS.permMap p b (Equiv.swap i j) := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← hdRo7CGenAux_permMap_mul]
        show ZS.permMap p b (Equiv.swap i j * Equiv.swap i j) = 1
        rw [Equiv.Perm.mul_def, Equiv.swap_swap]
        exact hdRo7CGenAux_permMap_one b
      have hperm : Equiv.swap i j * Equiv.swap 0 i * Equiv.swap i j = Equiv.swap 0 j := by
        have hinv : (Equiv.swap i j)⁻¹ = Equiv.swap i j :=
          inv_eq_of_mul_eq_one_right (by
            rw [Equiv.Perm.mul_def, Equiv.swap_swap]; rfl)
        have key : Equiv.swap i j * Equiv.swap 0 i * (Equiv.swap i j)⁻¹ = Equiv.swap 0 j := by
          rw [← Equiv.swap_apply_apply (Equiv.swap i j) 0 i]
          rw [Equiv.swap_apply_of_ne_of_ne (fun h : (0 : Fin (n + 1)) = i => hi0 h.symm)
                (fun h : (0 : Fin (n + 1)) = j => hj0 h.symm),
              Equiv.swap_apply_left]
        rwa [hinv] at key
      have hconj : ZS.permMap p b (Equiv.swap 0 j) =
          ZS.permMap p b (Equiv.swap i j) * ZS.permMap p b (Equiv.swap 0 i) *
            (ZS.permMap p b (Equiv.swap i j))⁻¹ := by
        rw [← hperm, hdRo7CGenAux_permMap_mul, hdRo7CGenAux_permMap_mul, hpiinv]
      rw [hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpiM huiM) (Subgroup.inv_mem _ hpiM)
  have hswapM : ∀ x y : Fin (n + 1), ZS.permMap p b (Equiv.swap x y) ∈ M := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [Equiv.swap_self]
      change ZS.permMap p b (1 : Equiv.Perm (Fin (n + 1))) ∈ M
      rw [hdRo7CGenAux_permMap_one]
      exact Subgroup.one_mem _
    · by_cases hx0 : x = 0
      · subst hx0
        exact huM y (Ne.symm hxy)
      · by_cases hy0 : y = 0
        · subst hy0
          rw [Equiv.swap_comm]
          exact huM x hxy
        · refine hMl ?_
          rw [hAL]
          refine ⟨Equiv.swap x y, fun _ => 1, ?_, ?_, ?_, ?_⟩
          · rw [Equiv.swap_apply_of_ne_of_ne (fun h : (0 : Fin (n + 1)) = x => hx0 h.symm)
                (fun h : (0 : Fin (n + 1)) = y => hy0 h.symm)]
          · rfl
          · intro l; left; rfl
          · intro l; rw [hdRo7CGenAux_permMap_apply, one_smul]
  have hpermMapM : ∀ σ : Equiv.Perm (Fin (n + 1)), ZS.permMap p b σ ∈ M := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ ?_ ?_
    · rw [hdRo7CGenAux_permMap_one]; exact Subgroup.one_mem _
    · intro f x y hxy hf
      rw [hdRo7CGenAux_permMap_mul]
      exact Subgroup.mul_mem _ (hswapM x y) hf
  have hFM : F ≤ M := by
    intro a ha
    rw [hF] at ha
    obtain ⟨σ, c, hc, ha'⟩ := ha
    let l : List (Fin (n + 1)) := (Finset.univ.filter (fun k => c k = -1)).toList
    have hnd : l.Nodup := Finset.nodup_toList _
    have hmem : ∀ k, k ∈ l ↔ c k = -1 := by
      intro k
      simp only [l, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdM : (l.map (fun i => hdRo7CGenAux_sgn b i)).prod ∈ M := by
      induction l with
      | nil => simp
      | cons i l ih =>
        rw [List.map_cons, List.prod_cons]
        exact Subgroup.mul_mem _ (hsgnM i) ih
    have hdecomp : a = ZS.permMap p b σ * (l.map (fun i => hdRo7CGenAux_sgn b i)).prod := by
      apply hdRo7CGenAux_ext (b := b)
      intro k
      rw [LinearEquiv.mul_apply, hdRo7CGenAux_list_prod_sgn_apply, map_smul,
        hdRo7CGenAux_permMap_apply, ha' k, hdRo7CGenAux_list_prod_sign l hnd k]
      congr 1
      by_cases hkl : k ∈ l
      · rw [if_pos hkl]; exact (hmem k).mp hkl
      · rw [if_neg hkl]
        have hcne : c k ≠ -1 := fun h => hkl ((hmem k).mpr h)
        rcases hc k with h | h
        · exact h
        · exact absurd h hcne
    rw [hdecomp]
    exact Subgroup.mul_mem _ (hpermMapM σ) hdM
  have hALF : AL ≤ F := by
    intro a ha
    rw [hF]
    exact hdRo7CGenAux_sp_to_full ((hAL a).mp ha)
  have hQF : Q ≤ F := by
    rw [hQ]
    rw [Subgroup.closure_le]
    intro s hs
    change s ∈ F
    rw [hF]
    rcases (hS s hs) with ⟨-, -, hcase⟩
    rcases hcase with h | h | h
    · exact hdRo7CGenAux_sp_to_full h
    · exact hdRo7CGenAux_signX_to_full h
    · exact hdRo7CGenAux_swap_to_full h
  exact ⟨F, hF, le_antisymm (sup_le hALF hQF) hFM⟩

end CFSG.StandardType.HdRo7C

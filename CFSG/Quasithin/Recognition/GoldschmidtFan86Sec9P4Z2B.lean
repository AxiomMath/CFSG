module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G)

include F

theorem exists_sib (m : Fin 5) :
    ∃ c, Γ.neighborSet (D.beta m) = {α, D.alpha m, c} ∧ α ≠ c ∧ D.alpha m ≠ c :=
  exists_third_neighbor (D.valence_beta F m) (D.adj_start_beta m).symm (D.adj_beta_alpha m)
    (D.alpha_ne_start m).symm

noncomputable def alphaS (m : Fin 5) : V := Classical.choose (D.exists_sib F m)

theorem alphaS_spec (m : Fin 5) :
    Γ.neighborSet (D.beta m) = {α, D.alpha m, D.alphaS F m} ∧ α ≠ D.alphaS F m ∧
      D.alpha m ≠ D.alphaS F m :=
  Classical.choose_spec (D.exists_sib F m)

theorem adj_beta_alphaS (m : Fin 5) : Γ.Adj (D.beta m) (D.alphaS F m) := by
  have h := (D.alphaS_spec F m).1
  have : D.alphaS F m ∈ Γ.neighborSet (D.beta m) := by rw [h]; simp
  exact this

theorem perm_cases {g : G} (hg : g ∈ nbrStab Γ G α) (m : Fin 5) :
    (g • D.alpha m = D.alpha m ∧ g • D.alphaS F m = D.alphaS F m) ∨
      (g • D.alpha m = D.alphaS F m ∧ g • D.alphaS F m = D.alpha m) := by
  obtain ⟨hN, hα1, hα2⟩ := D.alphaS_spec F m
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hg)
  have hgβ : g • D.beta m = D.beta m := mem_nbrStab.1 hg _ (D.adj_start_beta m)
  have hmem : ∀ x, Γ.Adj (D.beta m) x → g • x = α ∨ g • x = D.alpha m ∨ g • x = D.alphaS F m := by
    intro x hx
    have h1 : Γ.Adj (D.beta m) (g • x) := by
      have := (F.adj_smul g (D.beta m) x).2 hx
      rwa [hgβ] at this
    have h2 : g • x ∈ Γ.neighborSet (D.beta m) := h1
    rw [hN] at h2
    simpa using h2
  have hne : ∀ x, x ≠ α → g • x ≠ α := fun x hx h' =>
    hx (MulAction.injective g (h'.trans hgα.symm))
  have ha := hmem _ (D.adj_beta_alpha m)
  have hs := hmem _ (D.adj_beta_alphaS F m)
  have hna := hne _ (D.alpha_ne_start m)
  have hns := hne _ (D.alphaS_spec F m).2.1.symm
  have hinj : g • D.alpha m ≠ g • D.alphaS F m := fun h' =>
    (D.alphaS_spec F m).2.2 (MulAction.injective g h')
  rcases ha with h1 | h1 | h1
  · exact absurd h1 hna
  · rcases hs with h2 | h2 | h2
    · exact absurd h2 hns
    · exact absurd (h1.trans h2.symm) hinj
    · exact Or.inl ⟨h1, h2⟩
  · rcases hs with h2 | h2 | h2
    · exact absurd h2 hns
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hinj

theorem fix_mul_iff {g k : G} (hg : g ∈ nbrStab Γ G α) (hk : k ∈ nbrStab Γ G α) (m : Fin 5) :
    (g * k) • D.alpha m = D.alpha m ↔ (g • D.alpha m = D.alpha m ↔ k • D.alpha m = D.alpha m) := by
  have hs := (D.alphaS_spec F m).2.2
  rw [mul_smul]
  rcases D.perm_cases F hg m with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;>
    rcases D.perm_cases F hk m with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
  · simp [hk1, hg1]
  · rw [hk1, hg2]
    simp [hg1, hs.symm]
  · rw [hk1, hg1]
    simp [hs.symm]
  · rw [hk1, hg2]
    simp [hg1, hs.symm]

end D10Set

variable {L : ZLab Γ G} {F : FanTree Γ G}

theorem zGroup_smul_eq (h : Fan71c F L) {a : V} {v : G} (hv : v ∈ L.zGroup 2 a) {w : V}
    (hw : Γ.dist a w ≤ 2) : v • w = w := by
  have hle : L.zGroup 2 a ≤ MulAction.stabilizer G w := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨δ, hδ, hδ5, rfl⟩
    rw [SetLike.mem_coe, h.z_mem_stabilizer_iff hδ5]
    have := F.isTree.connected.dist_triangle (u := δ) (v := a) (w := w)
    have e : Γ.dist δ a = Γ.dist a δ := SimpleGraph.dist_comm
    rw [e] at this
    omega
  exact MulAction.mem_stabilizer_iff.1 (hle hv)

theorem trio_excl {H : Type*} [Group H] {a b c : H} (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hbc : b * c = c * b) (a1 : a ≠ 1) (b1 : b ≠ 1) (ab : a ≠ b)
    (ac : a ≠ c) (bc : b ≠ c) (abc : a * b * c ≠ 1) (e : Fin 2) :
    a * b ≠ a * c ^ (e : ℕ) ∧ a * b ≠ b * c ^ (e : ℕ) ∧ a * b ≠ c ∧
      a ≠ a * b * c ^ (e : ℕ) ∧ a ≠ b * c ^ (e : ℕ) := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have h3 : a * b ≠ c := fun h => abc (by rw [h, hc])
  fin_cases e
  · simp only [pow_zero, mul_one]
    refine ⟨fun h => b1 (mul_left_cancel (h.trans (mul_one a).symm)),
      fun h => a1 (mul_right_cancel (h.trans (one_mul b).symm)), h3,
      fun h => b1 (mul_left_cancel ((mul_one a).trans h)).symm, ab⟩
  · simp only [pow_one]
    refine ⟨fun h => bc (mul_left_cancel h),
      fun h => ac (mul_left_cancel (hab.symm.trans h)), h3, fun h => ?_, fun h => ?_⟩
    · have h1 : a * 1 = a * (b * c) := by rw [mul_one, ← mul_assoc]; exact h
      have h2 := mul_left_cancel h1
      exact bc (by rw [← hcinv]; exact eq_inv_of_mul_eq_one_left h2.symm)
    · apply abc
      rw [h]
      calc b * c * b * c = b * (c * b) * c := by group
        _ = b * (b * c) * c := by rw [hbc]
        _ = (b * b) * (c * c) := by group
        _ = 1 := by rw [hb, hc, one_mul]

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G)

theorem zGroup_mem_nbrStab (h : Fan71c F L) {v : G} (hv : v ∈ L.zGroup 2 α) :
    v ∈ nbrStab Γ G α := fun w hw =>
  zGroup_smul_eq h hv (by rw [dist_eq_one_iff_adj.2 hw]; norm_num)

theorem calpha_smul_alpha (h71a : Fan71a F L) (h71c : Fan71c F L) {c : G} (hc : c ∈ D.calpha)
    (m : Fin 5) : c • D.alpha m = D.alpha m :=
  D.fix_of_mem_calpha F h71a h71c hc m (m := 2) (by norm_num)

theorem calpha_mem_nbrStab {c : G} (hc : c ∈ D.calpha) : c ∈ nbrStab Γ G α :=
  (Subgroup.mem_inf.1 hc).1

theorem y_mem_nbrStab (h83a : Fan83a F L) {δ' : V} (hY : D.IsYPair δ') (k : Fin 5) :
    D.y δ' k ∈ nbrStab Γ G α := by
  rw [h83a α D δ' hY]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, rfl⟩)

theorem y_fix_alpha_iff (h : Fan71c F L) (h83b : Fan83b F L) {δ' : V} (hY : D.IsYPair δ')
    (k m : Fin 5) : D.y δ' k • D.alpha m = D.alpha m ↔ k = m := by
  have hc := h83b α D δ' hY k m
  rw [← h.comm_z_iff (D.valence_alpha F m)]
  constructor
  · intro hcomm
    by_contra hkm
    have hc' : fcomm (D.y δ' k) (L.z (D.alpha m)) = L.z α := by rw [hc]; simp [hkm]
    have h1 := fcomm_eq_one_of_mul_comm hcomm
    rw [hc'] at h1
    exact L.z_ne_one D.val h1
  · intro hkm
    have hc' : fcomm (D.y δ' k) (L.z (D.alpha m)) = 1 := by rw [hc]; simp [hkm]
    exact mul_comm_of_fcomm_eq_one hc'

theorem fixed_pair_of_shape (h71a : Fan71a F L) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h87 : Fan87 F L) {δ' : V} (hY : D.IsYPair δ') {g : G}
    (h0 : g • D.alpha 0 = D.alpha 0) (h2 : g • D.alpha 2 = D.alpha 2) (hord : orderOf g = 4)
    (hsq : g * g = L.z (D.alpha 0) * L.z (D.alpha 2) ∨ g * g = L.z (D.alpha 0)) :
    g ∈ nbrStab Γ G α ∧
      ((g * g = L.z (D.alpha 0) * L.z (D.alpha 2) ∧ g • D.alpha 1 = D.alpha 1 ∧
          g • D.alpha 3 ≠ D.alpha 3 ∧ g • D.alpha 4 ≠ D.alpha 4) ∨
        (g * g = L.z (D.alpha 0) ∧ g • D.alpha 3 = D.alpha 3 ∧
          g • D.alpha 1 ≠ D.alpha 1 ∧ g • D.alpha 4 ≠ D.alpha 4)) := by
  have hpath : ∀ v ∈ pathSet Γ (D.alpha 0) (D.alpha 2), g • v = v := fun v hv =>
    fixes_pathSet F h0 h2 hv
  have hsqE : ∃ e₁ e₂ e₃ : Fin 2, g * g = L.z (D.alpha 0) ^ (e₁ : ℕ) * L.z (D.alpha 2) ^ (e₂ : ℕ) *
      L.z α ^ (e₃ : ℕ) := by
    rcases hsq with h | h
    · exact ⟨1, 1, 0, by simpa using h⟩
    · exact ⟨1, 0, 0, by simpa using h⟩
  have k02 : kstar 0 2 = (4 : Fin 5) := by decide
  have k20 : kstar 2 0 = (3 : Fin 5) := by decide
  have m02 : midlab 0 2 = (1 : Fin 5) := by decide
  have hb : L.z (D.alpha 2) * L.z (D.alpha 2) = 1 := D.za_mul_self F 2
  have hc : L.z α * L.z α = 1 := L.z_mul_self D.val
  have hab : L.z (D.alpha 0) * L.z (D.alpha 2) = L.z (D.alpha 2) * L.z (D.alpha 0) :=
    D.za_comm F h71c 0 2
  have hbc : L.z (D.alpha 2) * L.z α = L.z α * L.z (D.alpha 2) := D.za_comm_start F h71c 2
  have a1 := D.zAlpha_ne_one F 0
  have b1 := D.zAlpha_ne_one F 2
  have ab := D.zAlpha_ne F h71c (show (0 : Fin 5) ≠ 2 by decide)
  have ac := D.zAlpha_ne_zStart F h71c 0
  have bc := D.zAlpha_ne_zStart F h71c 2
  have abc := D.zAlpha_prod_ne_one F h71c (show (0 : Fin 5) ≠ 2 by decide)
  have hy := D.y_mem_nbrStab F h83a hY
  have hyf := D.y_fix_alpha_iff F h71c h83b hY
  have hvf : ∀ {v : G}, v ∈ L.zGroup 2 α → ∀ m : Fin 5, v • D.alpha m = D.alpha m :=
    fun hv m => zGroup_smul_eq h71c hv (by rw [D.dist_start_alpha F m])
  have hcf : ∀ {c : G}, c ∈ D.calpha → ∀ m : Fin 5, c • D.alpha m = D.alpha m :=
    fun hc m => D.calpha_smul_alpha F h71a h71c hc m
  have hyy : ∀ (p q : Fin 5) (m : Fin 5),
      (D.y δ' p * D.y δ' q) • D.alpha m = D.alpha m ↔ ((p = m) ↔ (q = m)) := fun p q m => by
    rw [D.fix_mul_iff F (hy p) (hy q) m, hyf p m, hyf q m]
  rcases h87 α D δ' hY 0 2 (by decide) g hpath hord hsqE with
    ⟨v, hv, e, hg, hg2⟩ | ⟨v, hv, c, hc', hc4, e, hg, hg2⟩ | ⟨v, hv, c, hc', hc4, e, hg, hg2⟩ |
      ⟨v, hv, c, hc', hc4, hg, hg2⟩
  · rw [k02, k20] at hg
    have hvn := zGroup_mem_nbrStab F h71c hv
    have hgn : g ∈ nbrStab Γ G α := by
      rw [hg]
      exact mul_mem (mul_mem (hy 4) (hy 3)) hvn
    have key : ∀ m : Fin 5, g • D.alpha m = D.alpha m ↔ ((4 : Fin 5) = m ↔ (3 : Fin 5) = m) := by
      intro m
      rw [hg, D.fix_mul_iff F (mul_mem (hy 4) (hy 3)) hvn m, hyy 4 3 m]
      simp [hvf hv m]
    rcases hsq with hs | hs
    · refine ⟨hgn, Or.inl ⟨hs, (key 1).2 (by decide), fun h' => ?_, fun h' => ?_⟩⟩
      · have := (key 3).1 h'
        revert this; decide
      · have := (key 4).1 h'
        revert this; decide
    · exfalso
      rw [hg2] at hs
      have := (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).2.2.2.1
      exact this hs.symm
  · rw [k02, m02] at hg
    have hvn := zGroup_mem_nbrStab F h71c hv
    have hcn := D.calpha_mem_nbrStab hc'
    have hgn : g ∈ nbrStab Γ G α := by
      rw [hg]
      exact mul_mem (mul_mem (mul_mem (hy 4) (hy 1)) hvn) hcn
    have key : ∀ m : Fin 5, g • D.alpha m = D.alpha m ↔ ((4 : Fin 5) = m ↔ (1 : Fin 5) = m) := by
      intro m
      rw [hg, D.fix_mul_iff F (mul_mem (mul_mem (hy 4) (hy 1)) hvn) hcn m,
        D.fix_mul_iff F (mul_mem (hy 4) (hy 1)) hvn m, hyy 4 1 m]
      simp [hvf hv m, hcf hc' m]
    rcases hsq with hs | hs
    · exfalso
      rw [hg2] at hs
      have := (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).1
      exact this hs.symm
    · refine ⟨hgn, Or.inr ⟨hs, (key 3).2 (by decide), fun h' => ?_, fun h' => ?_⟩⟩
      · have := (key 1).1 h'
        revert this; decide
      · have := (key 4).1 h'
        revert this; decide
  · exfalso
    rcases hsq with hs | hs
    · rw [hg2] at hs
      exact (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).2.1 hs.symm
    · rw [hg2] at hs
      exact (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).2.2.2.2 hs.symm
  · exfalso
    rcases hsq with hs | hs
    · rw [hg2] at hs
      exact (trio_excl hb hc hab hbc a1 b1 ab ac bc abc 0).2.2.1 hs.symm
    · rw [hg2] at hs
      exact ac hs.symm

theorem exists_fixed_pair (h71a : Fan71a F L) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h87 : Fan87 F L) {δ' : V} (hY : D.IsYPair δ') {g : G}
    (h0 : g • D.alpha 0 = D.alpha 0) (h2 : g • D.alpha 2 = D.alpha 2) (hord : orderOf g = 4)
    (hsq : g * g = L.z (D.alpha 0) * L.z (D.alpha 2) ∨ g * g = L.z (D.alpha 0)) :
    ∃ m : Fin 5, (m = 1 ∨ m = 3) ∧ g • D.alpha m = D.alpha m := by
  rcases (D.fixed_pair_of_shape F h71a h71c h83a h83b h87 hY h0 h2 hord hsq).2 with
    ⟨-, h1, -, -⟩ | ⟨-, h3, -, -⟩
  · exact ⟨1, Or.inl rfl, h1⟩
  · exact ⟨3, Or.inr rfl, h3⟩

end D10Set

end CFSG.Quasithin.Fan86

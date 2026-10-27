module

public import CFSG.Quasithin.Vol2.Ch9Sec2Swap
public import CFSG.Quasithin.Vol2.Ch9Sec3Red

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

section Model

variable {K : Type} [Field K]

theorem mem_uni_of_ut {g : SpecialLinearGroup (Fin 2) K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) :
    g ∈ uni K := by
  have hdet := g.2
  rw [Matrix.det_fin_two, h10, h00, mul_zero, sub_zero, one_mul] at hdet
  refine mem_uni_iff.mpr ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, hdet]

theorem isUT_diagOf (a : Kˣ) : Om4.IsUT (Matrix.SpecialLinearGroup.toGL (diagOf a)) := by
  show (diagOf a : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  rw [coe_diagOf]
  rfl

theorem diagOf_inv (a : Kˣ) : (diagOf a)⁻¹ = diagOf a⁻¹ := by
  rw [← diagHom_apply, ← diagHom_apply, map_inv]

theorem mul_diagOf_inv_mem_uni {g : SpecialLinearGroup (Fin 2) K} {c : Kˣ}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = c) :
    g * (diagOf c)⁻¹ ∈ uni K := by
  rw [diagOf_inv]
  apply mem_uni_of_ut
  · rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagOf, Matrix.mul_apply, Fin.sum_univ_two, h10]
    simp
  · rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagOf, Matrix.mul_apply, Fin.sum_univ_two, h00]
    simp

theorem conj_diag_entries {P : GL (Fin 2) K} (hP : Om4.IsUT P) (τ : K ≃+* K) (a : Kˣ)
    {g : SpecialLinearGroup (Fin 2) K}
    (hg : ((P * GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (diagOf a)) *
      P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = g) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 = ((Units.map τ.toMonoidHom a : Kˣ) : K) := by
  have hUT : Om4.IsUT (P * GeneralLinearGroup.map τ.toRingHom
      (Matrix.SpecialLinearGroup.toGL (diagOf a)) * P⁻¹) :=
    (hP.mul ((isUT_diagOf a).map τ)).mul hP.inv.1
  refine ⟨?_, ?_⟩
  · rw [← hg]
    exact hUT
  · rw [← hg, (Om4.conj_map_apply hP (isUT_diagOf a) τ).1, Units.coe_map]
    rfl

theorem frob_of_ne_one [Fintype K] [CharP K 2] (hK : Fintype.card K = 4) {τ : K ≃+* K}
    (hτ : τ ≠ 1) : ∀ x : K, τ x = x ^ 2 := by
  obtain ⟨j, hj, hτj⟩ := exists_frob_pow_lt (n := 2) (by norm_num) (by rw [hK]; norm_num) τ
  interval_cases j
  · exfalso
    apply hτ
    ext x
    rw [hτj]
    simp
  · intro x
    rw [hτj]
    norm_num

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem exists_conj_uni {s : G} (hs : s ∈ T)
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hγ : γ ∈ (uni K).prod (uni K)) :
    ∃ u : ↥(fsuL0 T L), ψ u = γ ∧
      ψ ⟨s * u * s⁻¹, (Subgroup.mem_normalizer_iff.mp (Setup.T_le_fsuM hs) u).mp u.2⟩ ∈
        (uni K).prod (uni K) := by
  rw [← hc.sylow] at hγ
  obtain ⟨u, hu, hψu⟩ := hγ
  have huT : (u : G) ∈ T ⊓ fsuL0 T L := Subgroup.mem_subgroupOf.mp hu
  refine ⟨u, hψu, ?_⟩
  rw [← hc.sylow]
  exact ⟨_, Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem hs huT.1) (T.inv_mem hs),
    (Subgroup.mem_normalizer_iff.mp (Setup.T_le_fsuM hs) u).mp u.2⟩, rfl⟩

theorem exists_form_ut {s : G} (hs : s ∈ T) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), Om4.IsUT A ∧ Om4.IsUT B ∧
      (bar e ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ = Om4.lr A B * Om4.frM τ ∨
        bar e ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM) := by
  have hsM : s ∈ fsuM T L := Setup.T_le_fsuM hs
  obtain ⟨A, B, τ, h⟩ := hc.exists_form hsM
  refine ⟨A, B, τ, ?_, ?_, h⟩
  · rcases h with h | h
    · obtain ⟨u, hψu, hψ⟩ := hc.exists_conj_uni hs (γ := (u1 K, 1)) ⟨u1_mem, (uni K).one_mem⟩
      have hρ := hc.bar_conj hsM u
      have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL (u1 K))
          (Matrix.SpecialLinearGroup.toGL 1) := by rw [hψu]; rfl
      rw [h, hu, Om4.conj_isNS, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨h1, -⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
      obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.1
      refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
      rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]
    · obtain ⟨u, hψu, hψ⟩ := hc.exists_conj_uni hs (γ := (1, u1 K)) ⟨(uni K).one_mem, u1_mem⟩
      have hρ := hc.bar_conj hsM u
      have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL 1)
          (Matrix.SpecialLinearGroup.toGL (u1 K)) := by rw [hψu]; rfl
      rw [h, hu, Om4.conj_swap, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨h1, -⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
      obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.1
      refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
      rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]
  · rcases h with h | h
    · obtain ⟨u, hψu, hψ⟩ := hc.exists_conj_uni hs (γ := (1, u1 K)) ⟨(uni K).one_mem, u1_mem⟩
      have hρ := hc.bar_conj hsM u
      have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL 1)
          (Matrix.SpecialLinearGroup.toGL (u1 K)) := by rw [hψu]; rfl
      rw [h, hu, Om4.conj_isNS, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨-, h1⟩ := Om4.eq_of_rho_eq_lr (by rw [Units.val_one, Matrix.det_one]) hρ
      obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.2
      refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
      rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]
    · obtain ⟨u, hψu, hψ⟩ := hc.exists_conj_uni hs (γ := (u1 K, 1)) ⟨u1_mem, (uni K).one_mem⟩
      have hρ := hc.bar_conj hsM u
      have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL (u1 K))
          (Matrix.SpecialLinearGroup.toGL 1) := by rw [hψu]; rfl
      rw [h, hu, Om4.conj_swap, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨-, h1⟩ := Om4.eq_of_rho_eq_lr (by rw [Units.val_one, Matrix.det_one]) hρ
      obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.2
      refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
      rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]

variable {D : Subgroup G}

theorem conj_diag_ns (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {s : G} (hs : s ∈ T) {A B : GL (Fin 2) K} {τ : K ≃+* K} (hA : Om4.IsUT A) (hB : Om4.IsUT B)
    (hform : bar e ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ = Om4.lr A B * Om4.frM τ)
    {d : G} (hdL : d ∈ fsuL0 T L) {a b : Kˣ} (hψ : ψ ⟨d, hdL⟩ = (diagOf a, diagOf b)) :
    ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L,
      ψ ⟨d', hd'L⟩ = (diagOf (Units.map τ.toMonoidHom a), diagOf (Units.map τ.toMonoidHom b)) ∧
        s * d * s⁻¹ * d'⁻¹ ∈ T := by
  have hsM : s ∈ fsuM T L := Setup.T_le_fsuM hs
  have hρ := hc.bar_conj hsM ⟨d, hdL⟩
  rw [hform, Om4.rho_apply (ψ ⟨d, hdL⟩), Om4.conj_isNS, hψ] at hρ
  obtain ⟨h1, h2⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
  obtain ⟨d', hd'D, hd'L, hψd'⟩ := exists_mem_of_diag hdiag (Units.map τ.toMonoidHom a)
    (Units.map τ.toMonoidHom b)
  refine ⟨d', hd'D, hd'L, hψd', ?_⟩
  set x : ↥(fsuL0 T L) := ⟨s * d * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsM d).mp hdL⟩ with hx
  obtain ⟨e10, e00⟩ := conj_diag_entries hA τ a h1
  obtain ⟨f10, f00⟩ := conj_diag_entries hB τ b h2
  have hmem : ψ (x * ⟨d', hd'L⟩⁻¹) ∈ (uni K).prod (uni K) := by
    rw [map_mul, map_inv, hψd']
    exact ⟨mul_diagOf_inv_mem_uni e10 e00, mul_diagOf_inv_mem_uni f10 f00⟩
  exact (hc.mem_T_iff h37c h38c _).mpr hmem

theorem conj_diag_swap (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {s : G} (hs : s ∈ T) {A B : GL (Fin 2) K} {τ : K ≃+* K} (hA : Om4.IsUT A) (hB : Om4.IsUT B)
    (hform : bar e ⟨s, S.hMN (Setup.T_le_fsuM hs)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM)
    {d : G} (hdL : d ∈ fsuL0 T L) {a b : Kˣ} (hψ : ψ ⟨d, hdL⟩ = (diagOf a, diagOf b)) :
    ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L,
      ψ ⟨d', hd'L⟩ = (diagOf (Units.map τ.toMonoidHom b), diagOf (Units.map τ.toMonoidHom a)) ∧
        s * d * s⁻¹ * d'⁻¹ ∈ T := by
  have hsM : s ∈ fsuM T L := Setup.T_le_fsuM hs
  have hρ := hc.bar_conj hsM ⟨d, hdL⟩
  rw [hform, Om4.rho_apply (ψ ⟨d, hdL⟩), Om4.conj_swap, hψ] at hρ
  obtain ⟨h1, h2⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
  obtain ⟨d', hd'D, hd'L, hψd'⟩ := exists_mem_of_diag hdiag (Units.map τ.toMonoidHom b)
    (Units.map τ.toMonoidHom a)
  refine ⟨d', hd'D, hd'L, hψd', ?_⟩
  set x : ↥(fsuL0 T L) := ⟨s * d * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsM d).mp hdL⟩ with hx
  obtain ⟨e10, e00⟩ := conj_diag_entries hA τ b h1
  obtain ⟨f10, f00⟩ := conj_diag_entries hB τ a h2
  have hmem : ψ (x * ⟨d', hd'L⟩⁻¹) ∈ (uni K).prod (uni K) := by
    rw [map_mul, map_inv, hψd']
    exact ⟨mul_diagOf_inv_mem_uni e10 e00, mul_diagOf_inv_mem_uni f10 f00⟩
  exact (hc.mem_T_iff h37c h38c _).mpr hmem

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9

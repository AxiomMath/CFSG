module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzh

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

theorem trvE04_mem_X3 : trvE (0 : Fin 5) 4 (by decide) ∈ X3 :=
  ⟨by unfold PresStd; decide, by decide⟩

theorem trvE01_mem_X3 : trvE (0 : Fin 5) 1 (by decide) ∈ X3 :=
  ⟨by unfold PresStd; decide, by decide⟩

theorem trvE12_mem_X3 : trvE (1 : Fin 5) 2 (by decide) ∈ X3 :=
  ⟨by unfold PresStd; decide, by decide⟩

@[expose] def m21 : L3.Γ := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩

theorem m21_fix : L3.act m21 e0' = e0' := by
  unfold L3.act
  decide

theorem tau_m21_move : L3.act (τ3 m21) e2' ≠ e2' := by
  unfold L3.act
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.comp_of_fix_TL (c : Conf T L I t w J) (h1011 : Stmt10_1_1) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hall : ∀ i, C.dual i = false)
    (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (hU : ∀ j : ↥J, C.ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (h3 : InvStd (piL C.ρ c.le).range 3) (hX : (piL C.ρ c.le).range = X3) {e : G}
    (he : e ∈ fsuUL T L I) (hfix : ∀ x ∈ T ⊓ L, x * e * x⁻¹ = e) (i : Fin k) :
    C.E e i = 0 ∨ C.E e i = Pi.single 0 1 := by
  have hW := hV1W he
  have h3' : C.E e i 3 = 0 := by
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE c h1011 C.ρ hker h3 (a := 0) (b := 3) (by decide)
      (by norm_num) (by norm_num) (by rw [hX]; exact trvE_mem_X3 0 (by norm_num) (by decide))
    exact C.comp_eq_zero_nat hW (j := ⟨l, c.le l.2⟩) (conj_eq_of_mem_centralizer hlC he) _ hlρ
      (hall i)
  have h4' : C.E e i 4 = 0 := by
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE c h1011 C.ρ hker h3 (a := 0) (b := 4) (by decide)
      (by norm_num) (by norm_num) (by rw [hX]; exact trvE04_mem_X3)
    exact C.comp_eq_zero_nat hW (j := ⟨l, c.le l.2⟩) (conj_eq_of_mem_centralizer hlC he) _ hlρ
      (hall i)
  have h1' : C.E e i 1 = 0 := by
    obtain ⟨l, hlT, hlρ⟩ := Conf.exists_TL_of_uniSL c C.ρ hU
      (trvE_mem_uniSL (0 : Fin 5) 1 (by decide)) (by rw [hX]; exact trvE01_mem_X3)
    exact C.comp_eq_zero_nat hW (j := ⟨l, c.le l.2⟩) (hfix _ ⟨hlT, l.2⟩) _ hlρ (hall i)
  have h2' : C.E e i 2 = 0 := by
    obtain ⟨l, hlT, hlρ⟩ := Conf.exists_TL_of_uniSL c C.ρ hU
      (trvE_mem_uniSL (1 : Fin 5) 2 (by decide)) (by rw [hX]; exact trvE12_mem_X3)
    exact C.comp_eq_zero_nat hW (j := ⟨l, c.le l.2⟩) (hfix _ ⟨hlT, l.2⟩) _ hlρ (hall i)
  rcases zmod2_cases (C.E e i 0) with h0 | h0
  · left
    funext b
    fin_cases b <;> simp [h0, h1', h2', h3', h4']
  · right
    funext b
    fin_cases b <;> simp [h0, h1', h2', h3', h4']

theorem Conf.false_of_multi_E3_nat5 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h1011 : Stmt10_1_1) (h5 : Case10_1_1Five T L I) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hall : ∀ i, C.dual i = false)
    (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (hU : ∀ j : ↥J, C.ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (h3 : InvStd (piL C.ρ c.le).range 3) (hX : (piL C.ρ c.le).range = X3) : False := by
  obtain ⟨-, s, -, hsL, W, hWV1, hLW, hsup, -, ⟨hWc, hWnat⟩, hni⟩ := h5
  obtain ⟨F⟩ := exists_c5Coord h37 h38 h322 h1011 c.hyp hsL hWV1 hLW hsup hWnat hni
  have hLWs := le_normalizer_conjugate_of' hsL hLW
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hSyl := image_isSylowTwoOf (SecA.isSylowTwoOf_inf c.hyp.fsu.maximal.1) F.D.ρ F.D.ρ_surj
  obtain ⟨κ, hκ⟩ := SecD.L3.exists_conj_eq_P0 (card_eight_of_sylow hSyl)
  obtain ⟨a₀, ha₀W, hba₀⟩ := F.D.b_surj (L3.act κ e0')
  obtain ⟨b₀, hb₀W, hcb₀⟩ := F.c_surj (L3.act (τ3 κ) e2')
  have hP : ∀ (x : G) (hx : x ∈ T ⊓ L), ∃ p ∈ SecD.L3.P0, F.D.ρ ⟨x, hx.2⟩ = κ * p * κ⁻¹ := by
    intro x hx
    have h1 : F.D.ρ ⟨x, hx.2⟩ ∈ ((T ⊓ L).subgroupOf L).map F.D.ρ :=
      ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hκ] at h1
    obtain ⟨p, hp, hpe⟩ := h1
    exact ⟨p, hp, hpe.symm⟩
  have hfa : ∀ x ∈ T ⊓ L, x * a₀ * x⁻¹ = a₀ := by
    intro x hx
    have hxW : x * a₀ * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW hx.2) a₀).mp ha₀W
    refine F.D.b_inj _ hxW _ ha₀W ?_
    obtain ⟨p, hp, hpe⟩ := hP x hx
    rw [show x * a₀ * x⁻¹ = ((⟨x, hx.2⟩ : ↥L) : G) * a₀ * ((⟨x, hx.2⟩ : ↥L) : G)⁻¹ from rfl,
      F.D.equi _ a₀ ha₀W, hpe, hba₀, ← L3.act_mul, show κ * p * κ⁻¹ * κ = κ * p by group,
      L3.act_mul, P0_fix_e0 p hp]
  have hfb : ∀ x ∈ T ⊓ L, x * b₀ * x⁻¹ = b₀ := by
    intro x hx
    have hxW : x * b₀ * x⁻¹ ∈ CFSG.conjugate W s :=
      (Subgroup.mem_normalizer_iff.mp (hLWs hx.2) b₀).mp hb₀W
    refine F.c_inj _ hxW _ hb₀W ?_
    obtain ⟨p, hp, hpe⟩ := hP x hx
    rw [show x * b₀ * x⁻¹ = ((⟨x, hx.2⟩ : ↥L) : G) * b₀ * ((⟨x, hx.2⟩ : ↥L) : G)⁻¹ from rfl,
      F.c_equi _ b₀ hb₀W, hpe, hcb₀, map_mul, map_mul, map_inv, ← L3.act_mul,
      show τ3 κ * τ3 p * (τ3 κ)⁻¹ * τ3 κ = τ3 κ * τ3 p by group, L3.act_mul, tau_P0_fix_e2 p hp]
  have ha₀1 : a₀ ≠ 1 := fun h1 => by
    have h2 : L3.act κ e0' = L3.act κ 0 := by rw [L3.act_zero, ← hba₀, h1, F.b_one]
    exact absurd (C10P4F.act_injective κ h2) (by decide)
  have hb₀1 : b₀ ≠ 1 := fun h1 => by
    have h2 : L3.act (τ3 κ) e2' = L3.act (τ3 κ) 0 := by rw [L3.act_zero, ← hcb₀, h1, F.c_one]
    exact absurd (C10P4F.act_injective _ h2) (by decide)
  have ha₀V : a₀ ∈ fsuUL T L I := hWV1 ha₀W
  have hb₀V : b₀ ∈ fsuUL T L I := hWsV1 hb₀W
  have hca := Conf.comp_of_fix_TL c h1011 C hall hV1W hker hU h3 hX ha₀V hfa
  have hcb := Conf.comp_of_fix_TL c h1011 C hall hV1W hker hU h3 hX hb₀V hfb
  obtain ⟨l, hl⟩ := F.D.ρ_surj (κ * m21 * κ⁻¹)
  have hla : (l : G) * a₀ * (l : G)⁻¹ = a₀ := by
    refine F.D.b_inj _ ((Subgroup.mem_normalizer_iff.mp (hLW l.2) a₀).mp ha₀W) _ ha₀W ?_
    rw [F.D.equi l a₀ ha₀W, hl, hba₀, ← L3.act_mul, show κ * m21 * κ⁻¹ * κ = κ * m21 by group,
      L3.act_mul, m21_fix]
  have hlb : (l : G) * b₀ * (l : G)⁻¹ ≠ b₀ := by
    intro h
    have h1 := congrArg F.c h
    rw [F.c_equi l b₀ hb₀W, hl, hcb₀, map_mul, map_mul, map_inv, ← L3.act_mul,
      show τ3 κ * τ3 m21 * (τ3 κ)⁻¹ * τ3 κ = τ3 κ * τ3 m21 by group, L3.act_mul] at h1
    exact tau_m21_move (C10P4F.act_injective _ h1)
  have hjl := (C.conj_eq_iff hall (hV1W ha₀V) hca ha₀1 ⟨l, c.le l.2⟩).mp hla
  exact hlb ((C.conj_eq_iff hall (hV1W hb₀V) hcb hb₀1 ⟨l, c.le l.2⟩).mpr hjl)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

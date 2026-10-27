module

public import CFSG.Quasithin.MS93.S46KCFStr

public section

namespace CFSG.Quasithin.MS93.S46.KCF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
  CFSG.Quasithin.MS93.S46.KC2
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem natVecG_commutator_conj_smul (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z₁ z' : (puAmalgam c.pu.le).Universal} (hz₁ : z₁ ∈ Vv (puAmalgam c.pu.le) α)
    (hz' : z' ∈ Vv (puAmalgam c.pu.le) α) {a : F}
    (ha : ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z', v⁆ = a • natVecG d.lh.nat ⁅z₁, v⁆)
    (g : ↥(stab (puAmalgam c.pu.le) α)) {v : (puAmalgam c.pu.le).Universal}
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) :
    natVecG d.lh.nat ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * z' * g, v⁆ =
      a • natVecG d.lh.nat ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * g, v⁆ := by
  have hgv : (g : (puAmalgam c.pu.le).Universal) * v * (g : (puAmalgam c.pu.le).Universal)⁻¹ ∈
      Vv (puAmalgam c.pu.le) α := (Subgroup.mem_normalizer_iff.mp (d.lh.vN g.2) v).mp hv
  rw [natVecG_commutator_conj_left d hVU hz' hv g, natVecG_commutator_conj_left d hVU hz₁ hv g,
    ha _ hgv, Matrix.mulVec_smul]

theorem natVecG_commutator_conj_eq (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {E : ↥(stab (puAmalgam c.pu.le) α)}
    (hE : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1) :
    natVecG d.lh.nat ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ =
      natVecG d.lh.nat ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ 2 •
        (Pi.single 2 1 : Fin 3 → F) := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hxU : ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ ∈ Uloc c.pu.le L α :=
    hVU (Subgroup.commutator_mem_commutator hzV (inv_mul_mul_mem_vv d hzV E))
  obtain ⟨h0, h1⟩ := row_dotProduct_eq_zero d hz (h := 1) (h' := E)
    (x := ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆) (by simp) hxU
  rw [map_one, row_one, single_dotProduct, one_mul] at h0
  rw [hE, single_dotProduct, one_mul] at h1
  funext i
  fin_cases i
  · simp [h0]
  · simp [h1]
  · simp

variable [CharP F 2]

theorem natVecG_commutator_conj_smul_smul (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z₁ z' z'' : (puAmalgam c.pu.le).Universal} (hz₁ : z₁ ∈ Vv (puAmalgam c.pu.le) α)
    (hz' : z' ∈ Vv (puAmalgam c.pu.le) α) (hz'' : z'' ∈ Vv (puAmalgam c.pu.le) α) {a b : F}
    (ha : ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z', v⁆ = a • natVecG d.lh.nat ⁅z₁, v⁆)
    (hb : ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z'', v⁆ = b • natVecG d.lh.nat ⁅z₁, v⁆)
    (g h : ↥(stab (puAmalgam c.pu.le) α)) :
    natVecG d.lh.nat ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * z' * g,
        (h : (puAmalgam c.pu.le).Universal)⁻¹ * z'' * h⁆ =
      (a * b) • natVecG d.lh.nat ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * g,
        (h : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * h⁆ := by
  have hg₁ := inv_mul_mul_mem_vv d hz₁ g
  have hh'' := inv_mul_mul_mem_vv d hz'' h
  have hh₁ := inv_mul_mul_mem_vv d hz₁ h
  rw [natVecG_commutator_conj_smul d hVU hz₁ hz' ha g hh'',
    natVecG_commutator_comm d hVU hg₁ hh'', natVecG_commutator_conj_smul d hVU hz₁ hz'' hb h hg₁,
    natVecG_commutator_comm d hVU hh₁ hg₁, smul_smul]

theorem natVecG_commutator_points (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {E : ↥(stab (puAmalgam c.pu.le) α)}
    (hE : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1)
    {P : Fin 6 → ↥(stab (puAmalgam c.pu.le) α)}
    (hP : ∀ i, (toSL3 ψ (P i) : Matrix (Fin 3) (Fin 3) F) 0 = embv (lv i)) (i j : Fin 6) :
    natVecG d.lh.nat ⁅(P i : (puAmalgam c.pu.le).Universal)⁻¹ * z * P i,
        (P j : (puAmalgam c.pu.le).Universal)⁻¹ * z * P j⁆ =
      natVecG d.lh.nat ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ 2 • embv (tab i j) := by
  by_cases hij : i = j
  · subst hij
    rw [commutatorElement_self, natVecG_one, tab_self, embv_zero, smul_zero]
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hcU : ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ ∈ Uloc c.pu.le L α :=
    hVU (Subgroup.commutator_mem_commutator hzV (inv_mul_mul_mem_vv d hzV E))
  obtain ⟨K, hK⟩ := toSL3_surjective d.lh.surj
    (matF (F := F) (lv_ne_zero i) (lv_ne_zero j) (lv_injective.ne hij))
  have hconj := commutator_eq_conj d h2 hz hE (K := K) (h := P i) (h' := P j)
    (by rw [hP, hK, matF_zero]) (by rw [hP, hK, matF_one])
  have e : (K : (puAmalgam c.pu.le).Universal)⁻¹ *
      ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ * K =
      ((K⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) *
        ⁅z, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z * E⁆ *
        ((K⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ := by
    simp
  have hc := natVecG_commutator_conj_eq d hVU hz hE
  rw [hconj, e, natVecG_conj d.lh.nat K⁻¹ hcU]
  conv_lhs => rw [hc]
  rw [Matrix.mulVec_smul, map_inv, hK, matF_inv_mulVec]
  rfl

omit [CharP F 2] in
theorem commutator_eq_one_of_row (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    {h : ↥(stab (puAmalgam c.pu.le) α)} {a : F}
    (ha : (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 = a • Pi.single 0 1) :
    ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ = 1 := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hhzV := inv_mul_mul_mem_vv d hzV h
  have hxU : ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ ∈ Uloc c.pu.le L α :=
    hVU (Subgroup.commutator_mem_commutator hhzV hzV)
  have hinv : a • (((toSL3 ψ h)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
    have h1 := row_mul (toSL3 ψ h) (toSL3 ψ h)⁻¹ 0
    rw [mul_inv_cancel, row_one, ha, Matrix.smul_vecMul, Matrix.single_one_vecMul] at h1
    exact h1.symm
  have hfix : ∀ k : ↥(stab (puAmalgam c.pu.le) α),
      (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 →
        natVecG d.lh.nat ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ =
          (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) *ᵥ
            natVecG d.lh.nat ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ := by
    intro k hk
    have hk' : (toSL3 ψ (h * k * h⁻¹) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
      rw [map_mul, map_mul, map_inv, row_mul, row_mul, ha, Matrix.smul_vecMul,
        Matrix.single_one_vecMul, Matrix.smul_vecMul]
      have e : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F).row 0 = Pi.single 0 1 := hk
      rw [e, Matrix.single_one_vecMul]
      exact hinv
    have hc1 : ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h)⁻¹ *
        ((k : (puAmalgam c.pu.le).Universal) * ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h) *
          (k : (puAmalgam c.pu.le).Universal)⁻¹) ∈ ZM (puAmalgam c.pu.le) α := by
      have hc := commutator_mem_of_row d h2 (Subgroup.inv_mem _ hz) hk'
      have e : ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h)⁻¹ *
          ((k : (puAmalgam c.pu.le).Universal) * ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h) *
            (k : (puAmalgam c.pu.le).Universal)⁻¹) =
          ((h⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) *
            ⁅z⁻¹, ((h * k * h⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) :
              (puAmalgam c.pu.le).Universal)⁆ *
            ((h⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul, commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α (h⁻¹).2) _).mp hc
    have hc2 : z⁻¹ * ((k : (puAmalgam c.pu.le).Universal) * z *
        (k : (puAmalgam c.pu.le).Universal)⁻¹) ∈ ZM (puAmalgam c.pu.le) α := by
      have hc := commutator_mem_of_row d h2 (Subgroup.inv_mem _ hz) hk
      have e : z⁻¹ * ((k : (puAmalgam c.pu.le).Universal) * z *
          (k : (puAmalgam c.pu.le).Universal)⁻¹) = ⁅z⁻¹, (k : (puAmalgam c.pu.le).Universal)⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hc
    have hcomm := commutator_eq_of_inv_mul_mem d (d.lh.vq hhzV) (d.lh.vq hzV) hc1 hc2
    have e : (k : (puAmalgam c.pu.le).Universal) *
        ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ * (k : (puAmalgam c.pu.le).Universal)⁻¹ =
        ⁅(k : (puAmalgam c.pu.le).Universal) * ((h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h) *
            (k : (puAmalgam c.pu.le).Universal)⁻¹,
          (k : (puAmalgam c.pu.le).Universal) * z * (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 := natVecG_conj d.lh.nat k hxU
    rw [e, hcomm] at h1
    exact h1
  set w := natVecG d.lh.nat ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z * h, z⁆ with hw
  have hfix' : ∀ {i j : Fin 3}, i ≠ 0 → i ≠ j → w j = 0 := by
    intro i j hi hij
    obtain ⟨k, hk⟩ := toSL3_surjective d.lh.surj (rootElt i j 1)
    have h1 := hfix k (by rw [hk]; exact rootElt_row_zero hi 1)
    rw [hk, rootElt_mulVec hij, one_mul] at h1
    have h2' := congrFun h1 i
    simpa using h2'
  have hw0 : w = 0 := by
    funext k
    fin_cases k
    · exact hfix' (i := 1) (by decide) (by decide)
    · exact hfix' (i := 2) (by decide) (by decide)
    · exact hfix' (i := 1) (by decide) (by decide)
  exact natVecG_injective d.lh.nat hxU (Subgroup.one_mem _) (by rw [← hw, hw0, natVecG_one])

theorem natVecG_commutator_ne_zero (h466a : I466a) (h467 : I467) (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z₁ : (puAmalgam c.pu.le).Universal} (hz₁ : z₁ ∈ ZM (puAmalgam c.pu.le) γ)
    (hz₁α : z₁ ∉ ZM (puAmalgam c.pu.le) α) {E : ↥(stab (puAmalgam c.pu.le) α)}
    (hE : (toSL3 ψ E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1)
    {g : (puAmalgam c.pu.le).Universal} (hg : g ∈ stab (puAmalgam c.pu.le) α)
    (hle : ¬ ZM (puAmalgam c.pu.le) (g • γ) ≤ Qv _ γ) :
    natVecG d.lh.nat ⁅z₁, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * E⁆ 2 ≠ 0 := by
  have hz₁V : z₁ ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz₁
  obtain ⟨x, hx, hxQ⟩ := Set.not_subset.mp hle
  rw [SetLike.mem_coe, zm_smul, mem_map_conj] at hx
  have hxV : x ∈ Vv (puAmalgam c.pu.le) α := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (d.lh.vN hg) _).mp (d.zγVα hx)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅x, z⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hxQ (d.mem_qv_of_commute hxV hcon)
  obtain ⟨a', ha'⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz₁ hz₁α hx
  obtain ⟨a, ha⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz₁ hz₁α hz
  set h : ↥(stab (puAmalgam c.pu.le) α) := (⟨g, hg⟩ : ↥(stab (puAmalgam c.pu.le) α))⁻¹ with hh
  have hhx : (h : (puAmalgam c.pu.le).Universal)⁻¹ * (g⁻¹ * x * g) * h = x := by
    simp only [hh, Subgroup.coe_inv, inv_inv]
    group
  have hbil := natVecG_commutator_conj_smul_smul d hVU hz₁V (d.zγVα hx) (d.zγVα hz) ha' ha h 1
  simp only [Subgroup.coe_one, inv_one, one_mul, mul_one] at hbil
  rw [hhx] at hbil
  have hxzU : ⁅x, z⁆ ∈ Uloc c.pu.le L α :=
    hVU (Subgroup.commutator_mem_commutator hxV (d.zγVα hz))
  have hne' : ⁅(h : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * h, z₁⁆ ≠ 1 := by
    intro h1
    apply hxz
    refine natVecG_injective d.lh.nat hxzU (Subgroup.one_mem _) ?_
    rw [hbil, h1, natVecG_one, smul_zero]
  by_cases hrow : (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
      (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0
  · apply absurd _ hne'
    refine commutator_eq_one_of_row d h2 hVU hz₁ (h := h)
      (a := (toSL3 ψ h : Matrix (Fin 3) (Fin 3) F) 0 0) ?_
    funext k
    fin_cases k
    · simp
    · simp [hrow.1]
    · simp [hrow.2]
  · obtain ⟨A, hA0, hA1⟩ := exists_rows _ hrow
    obtain ⟨K, hK⟩ := toSL3_surjective d.lh.surj A
    have hconj := commutator_eq_conj d h2 hz₁ hE (K := K) (h := h) (h' := 1)
      (by rw [hK, hA0]) (by rw [hK, hA1, map_one, row_one])
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one] at hconj
    intro h0
    apply hne'
    have hcU : ⁅z₁, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * E⁆ ∈ Uloc c.pu.le L α :=
      hVU (Subgroup.commutator_mem_commutator hz₁V (inv_mul_mul_mem_vv d hz₁V E))
    have hc1 : ⁅z₁, (E : (puAmalgam c.pu.le).Universal)⁻¹ * z₁ * E⁆ = 1 :=
      natVecG_injective d.lh.nat hcU (Subgroup.one_mem _)
        (by rw [natVecG_commutator_conj_eq d hVU hz₁ hE, h0, zero_smul, natVecG_one])
    rw [hconj, hc1, mul_one, inv_mul_cancel]

end CFSG.Quasithin.MS93.S46.KCF

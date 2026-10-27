module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoB
public import CFSG.LocalAnalysis.WeakClosure81.W172Lem26A
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

private theorem w172_conj_inv_mul_eq_sq {A : Type*} [Group A] {y e : A} (he : e * e = 1)
    (hinv : e * y * e⁻¹ = y⁻¹) : e * (y⁻¹ * e * y) = y * y := by
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have h1 : e * y⁻¹ * e = y := by
    have heye : e * y * e = y⁻¹ := by simpa [he_inv] using hinv
    have h := congrArg Inv.inv heye
    simpa [mul_assoc, he_inv] using h
  calc e * (y⁻¹ * e * y) = (e * y⁻¹ * e) * y := by group
    _ = y * y := by rw [h1]

theorem w172_vInH_one (c : MinCex172 D V₀ V H) : vInH V H 1 = V := by
  unfold vInH
  rw [conjSubgroup_one, inf_eq_left.2 c.w172_V_le_H]

theorem w172_not_conj_le_M (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) (he1 : e ≠ 1) {x : ↥H} (hodd : Odd (orderOf (M.ρ x)))
    (hinv : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹) (hx1 : M.ρ x ≠ 1) :
    ¬ conjSubgroup V (x : G) ≤ D.M := by
  classical
  rintro hle
  obtain ⟨v, hvV, hvρ⟩ : ∃ v : ↥H, (v : G) ∈ V ∧ M.ρ v = e := by
    have he_mem : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
    rw [← hge] at he_mem
    exact M.mem_img.1 he_mem
  let hsub : ↥H := x⁻¹ * v * x
  have hv' : (hsub : G) ∈ conjSubgroup V (x : G) := by
    rw [mem_conjSubgroup_iff]
    rw [show (x : G) * (hsub : G) * (x : G)⁻¹ = (v : G) by
      simp only [hsub, Subgroup.coe_mul, Subgroup.coe_inv]
      group]
    exact hvV
  have hM : (hsub : G) ∈ D.M := hle hv'
  have hge' : M.img (vInH V H 1) = Subgroup.zpowers e := by
    rw [c.w172_vInH_one, hge]
  have hmem1 : (hsub : G) ∈ conjSubgroup D.M 1 := by rwa [conjSubgroup_one]
  have hcomm_ρ : M.ρ hsub * e = e * M.ρ hsub :=
    (c.w172_mem_conj_iff_comm h162 (c.w172_gam183_one h162)
      (w172_two5 h162 c (c.w172_gam183_one h162)) M hge' he he1 hsub.2).1 hmem1
  let y : LGL 2 M.W := M.ρ x
  have hhrho : M.ρ hsub = y⁻¹ * e * y := by
    have h1 : M.ρ hsub = (M.ρ x)⁻¹ * M.ρ v * M.ρ x := by
      simp only [hsub, map_mul, map_inv]
    rw [h1, hvρ]
  have hcomm : (y⁻¹ * e * y) * e = e * (y⁻¹ * e * y) := by
    have h := hcomm_ρ
    rw [hhrho] at h
    exact h
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have heye : e * y * e = y⁻¹ := by simpa [he_inv] using hinv
  have hL : (y⁻¹ * e * y) * e = y⁻¹ * y⁻¹ := by
    calc (y⁻¹ * e * y) * e = y⁻¹ * (e * y * e) := by group
      _ = y⁻¹ * y⁻¹ := by rw [heye]
  have hab : y⁻¹ * y⁻¹ = y * y := by rw [← hL, hcomm, w172_conj_inv_mul_eq_sq he hinv]
  have hmul : (y * y) * (y * y) = 1 := by
    have h := congrArg (fun z => (y * y) * z) hab
    have hl2 : (y * y) * (y⁻¹ * y⁻¹) = 1 := by group
    rw [hl2] at h
    exact h.symm
  have h4 : y ^ 4 = 1 := by
    rw [show y ^ 4 = (y * y) * (y * y) by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two (y ^ 2), pow_two y]]
    exact hmul
  have hdvd : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hone : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.2 hodd).pow_right 2)
      (by simpa using hdvd)
  exact hx1 (orderOf_eq_one_iff.1 hone)

theorem w172_not_le_conj_M (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) (he1 : e ≠ 1) {x : ↥H} (hodd : Odd (orderOf (M.ρ x)))
    (hinv : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹) (hx1 : M.ρ x ≠ 1) :
    ¬ V ≤ conjSubgroup D.M (x : G) := by
  intro hle
  have hodd' : Odd (orderOf (M.ρ x⁻¹)) := by
    rw [map_inv, orderOf_inv]
    exact hodd
  have hinv' : e * M.ρ x⁻¹ * e⁻¹ = (M.ρ x⁻¹)⁻¹ := by
    rw [map_inv, inv_inv]
    calc e * (M.ρ x)⁻¹ * e⁻¹ = (e * M.ρ x * e⁻¹)⁻¹ := by group
      _ = ((M.ρ x)⁻¹)⁻¹ := by rw [hinv]
  have hx1' : M.ρ x⁻¹ ≠ 1 := by
    rw [map_inv]
    exact inv_ne_one.2 hx1
  refine c.w172_not_conj_le_M h162 M hge he he1 hodd' hinv' hx1' ?_
  have h2 := E3.conjSubgroup_mono_left (x : G)⁻¹ hle
  rw [E3.conjSubgroup_conj_inv] at h2
  simpa using h2

theorem w172_hyp64_of_inverted (h162 : W3Thm162Gt2 G) (hL : W172Lem26 D V₀ V)
    (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W}
    (hge : M.img V = Subgroup.zpowers e) (he : e * e = 1) (he1 : e ≠ 1) {x : ↥H}
    (hodd : Odd (orderOf (M.ρ x))) (hinv : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹) (hx1 : M.ρ x ≠ 1) :
    Hyp64 1 D.M V₀ V (x : G) :=
  hL (x : G) (c.w172_inCalO_one h162 x.2 (c.w172_not_conj_le_M h162 M hge he he1 hodd hinv hx1)
    (c.w172_not_le_conj_M h162 M hge he he1 hodd hinv hx1))

theorem w172_conjSubgroup_eq_of_rho_eq (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {x x' : ↥H} (h : M.ρ x = M.ρ x') :
    conjSubgroup V (x : G) = conjSubgroup V (x' : G) := by
  let z : ↥H := x' * x⁻¹
  have hzρ : M.ρ z = 1 := by
    have h1 : M.ρ z = M.ρ x' * (M.ρ x)⁻¹ := by simp only [z, map_mul, map_inv]
    rw [h1, ← h, mul_inv_cancel]
  have hzC : (z : G) ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) :=
    (M.ρ_eq_one_iff z).1 hzρ
  have hzM : (z : G) ∈ D.M := by
    have h1 := w172_centralizer_le_conj_M h162 c (c.w172_gam183_one h162) hzC
    rwa [conjSubgroup_one] at h1
  have hzN : (z : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [c.hyp.setting.normalizer_eq]
    exact hzM
  have hconjz : conjSubgroup V (z : G) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hzN
  have hx'eq : (z : G) * (x : G) = (x' : G) := by
    simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc conjSubgroup V (x : G)
      = conjSubgroup (conjSubgroup V (z : G)) (x : G) := by rw [hconjz]
    _ = conjSubgroup V ((z : G) * (x : G)) := conjSubgroup_conjSubgroup V (z : G) (x : G)
    _ = conjSubgroup V (x' : G) := by rw [hx'eq]

theorem w172_inf_conj_le_of_mem_zpowers (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) {x x' : ↥H} (hodd : Odd (orderOf (M.ρ x)))
    (hinv : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹)
    (hmem : M.ρ x' ∈ Subgroup.zpowers (M.ρ x)) :
    V ⊓ conjSubgroup V (x : G) ≤ conjSubgroup V (x' : G) := by
  classical
  intro n hn
  rw [Subgroup.mem_inf] at hn
  obtain ⟨hnV, hnVx⟩ := hn
  have hV : IsElemAbelian 2 V := c.hyp.setting.isElemAbelian
  have hcentV : V ≤ Subgroup.centralizer ({n} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact (hV.comm ha hnV).symm
  have hcentVx : conjSubgroup V (x : G) ≤ Subgroup.centralizer ({n} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ((E3.isElemAbelian_conjSubgroup hV (x : G)).comm ha hnVx).symm
  have hcentL : V ⊔ conjSubgroup V (x : G) ≤ Subgroup.centralizer ({n} : Set G) :=
    sup_le hcentV hcentVx
  obtain ⟨v₀, hv₀V, hv₀ρ⟩ : ∃ v₀ : ↥H, (v₀ : G) ∈ V ∧ M.ρ v₀ = e := by
    have he_mem : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
    rw [← hge] at he_mem
    exact M.mem_img.1 he_mem
  let v₁ : ↥H := x⁻¹ * v₀ * x
  have hv₁ρ : M.ρ v₁ = (M.ρ x)⁻¹ * M.ρ v₀ * M.ρ x := by
    simp only [v₁, map_mul, map_inv]
  have hv₁Vx : (v₁ : G) ∈ conjSubgroup V (x : G) := by
    rw [mem_conjSubgroup_iff]
    rw [show (x : G) * (v₁ : G) * (x : G)⁻¹ = (v₀ : G) by
      simp only [v₁, Subgroup.coe_mul, Subgroup.coe_inv]
      group]
    exact hv₀V
  let l₁ : ↥H := v₀ * v₁
  have hl₁L : (l₁ : G) ∈ V ⊔ conjSubgroup V (x : G) := by
    have h1 : (l₁ : G) = (v₀ : G) * (v₁ : G) := by simp only [l₁, Subgroup.coe_mul]
    rw [h1]
    exact Subgroup.mul_mem_sup hv₀V hv₁Vx
  have hl₁ρ : M.ρ l₁ = M.ρ x * M.ρ x := by
    have h1 : M.ρ l₁ = M.ρ v₀ * M.ρ v₁ := by simp only [l₁, map_mul]
    rw [h1, hv₁ρ, hv₀ρ]
    exact w172_conj_inv_mul_eq_sq he hinv
  have hy_mem : M.ρ x ∈ Subgroup.zpowers (M.ρ l₁) := by
    rw [hl₁ρ, ← pow_two (M.ρ x), Subgroup.mem_zpowers_iff]
    obtain ⟨t, ht⟩ := hodd
    refine ⟨((t + 1 : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, ← pow_mul]
    have h2t : 2 * (t + 1) = orderOf (M.ρ x) + 1 := by omega
    rw [h2t, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem' : M.ρ x' ∈ Subgroup.zpowers (M.ρ l₁) :=
    (Subgroup.zpowers_le.mpr hy_mem) hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem'
  let l : ↥H := l₁ ^ k
  have hlρ : M.ρ l = M.ρ x' := by simp only [l, map_zpow, hk]
  have hconj := c.w172_conjSubgroup_eq_of_rho_eq h162 M hlρ
  rw [← hconj]
  rw [mem_conjSubgroup_iff]
  have hlL : (l : G) ∈ V ⊔ conjSubgroup V (x : G) := by
    have h1 : (l : G) = (l₁ : G) ^ k := by simp only [l, Subgroup.coe_zpow]
    rw [h1]
    exact Subgroup.zpow_mem _ hl₁L k
  have hcomml : n * (l : G) = (l : G) * n :=
    Subgroup.mem_centralizer_iff.1 (hcentL hlL) n (Set.mem_singleton n)
  have hln : (l : G) * n * (l : G)⁻¹ = n := by
    rw [hcomml.symm, mul_assoc, mul_inv_cancel, mul_one]
  rw [hln]
  exact hnV

theorem w172_comm_of_normalizes (h162 : W3Thm162Gt2 G) (hL : W172Lem26 D V₀ V)
    (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W}
    (hge : M.img V = Subgroup.zpowers e) (he : e * e = 1) (he1 : e ≠ 1) {x : ↥H}
    (hodd : Odd (orderOf (M.ρ x))) (hinv : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹) (hx1 : M.ρ x ≠ 1)
    {r : ↥H} (hr : (r : G) ∈ w172R D V₀ V)
    (hn : M.ρ r ∈ Subgroup.normalizer
      ((Subgroup.zpowers (M.ρ x) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    (r : G) ∈ Subgroup.centralizer (NOf D.M V (x : G) : Set G) := by
  classical
  have hVM : V ≤ D.M := by
    rw [← c.hyp.setting.normalizer_eq]
    exact Subgroup.le_normalizer
  have hV : IsElemAbelian 2 V := c.hyp.setting.isElemAbelian
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) :=
    le_of_eq c.hyp.setting.normalizer_eq.symm
  have hNeq : NOf D.M V (x : G) = V ⊓ conjSubgroup V (x : G) := NOf_eq D.M V (x : G) hVM
  have hH64 : Hyp64 1 D.M V₀ V (x : G) :=
    c.w172_hyp64_of_inverted h162 hL M hge he he1 hodd hinv hx1
  have hNbot : NOf D.M V (x : G) ⊓ V₀ = ⊥ := NOf_inf_eq_bot hH64
  have hrM : (r : G) ∈ D.M := w172R_le_M D V₀ V hr
  have hrN : (r : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [c.hyp.setting.normalizer_eq]
    exact hrM
  have hVr : conjSubgroup V (r : G) = V := conjSubgroup_eq_iff_mem_normalizer.mpr hrN
  let x' : ↥H := r⁻¹ * x * r
  have hx'ρ : M.ρ x' = (M.ρ r)⁻¹ * M.ρ x * M.ρ r := by
    simp only [x', map_mul, map_inv]
  have hx'zp : M.ρ x' ∈ Subgroup.zpowers (M.ρ x) := by
    rw [hx'ρ]
    exact (Subgroup.mem_normalizer_iff''.mp hn (M.ρ x)).mp (Subgroup.mem_zpowers (M.ρ x))
  have hNle : NOf D.M V (x : G) ≤ conjSubgroup V (x' : G) := by
    rw [hNeq]
    exact c.w172_inf_conj_le_of_mem_zpowers h162 M hge he hodd hinv hx'zp
  have hxr : (x : G) * (r : G) = (r : G) * (x' : G) := by
    simp only [x', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hNr : conjSubgroup (NOf D.M V (x : G)) (r : G) = V ⊓ conjSubgroup V (x' : G) := by
    rw [hNeq, E3.conjSubgroup_inf, hVr, conjSubgroup_conjSubgroup, hxr,
      ← conjSubgroup_conjSubgroup, hVr]
  have hNV : NOf D.M V (x : G) ≤ V := by rw [hNeq]; exact inf_le_left
  have hN_le_Nr : NOf D.M V (x : G) ≤ conjSubgroup (NOf D.M V (x : G)) (r : G) := by
    rw [hNr]
    exact le_inf hNV hNle
  have hcard_le : Nat.card (conjSubgroup (NOf D.M V (x : G)) (r : G)) ≤
      Nat.card (NOf D.M V (x : G)) := le_of_eq (E3.card_conjSubgroup _ _)
  have hNeqNr : NOf D.M V (x : G) = conjSubgroup (NOf D.M V (x : G)) (r : G) :=
    Subgroup.eq_of_le_of_card_ge hN_le_Nr hcard_le
  have hrCT : (r : G) ∈ F11.CTilde D.M V₀ V :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hr).1).2
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hrconj : (r : G) * n * (r : G)⁻¹ ∈ NOf D.M V (x : G) := by
    have h1 : n ∈ conjSubgroup (NOf D.M V (x : G)) (r : G) := by
      rw [← hNeqNr]
      exact hn
    exact mem_conjSubgroup_iff.1 h1
  have hcN : (r : G) * n * (r : G)⁻¹ * n⁻¹ ∈ NOf D.M V (x : G) :=
    (NOf D.M V (x : G)).mul_mem hrconj ((NOf D.M V (x : G)).inv_mem hn)
  have hcV₀ : (r : G) * n * (r : G)⁻¹ * n⁻¹ ∈ V₀ := by
    obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hMle).1 hrCT
    exact (actTil_eq_one_iff V₀ V hV ⟨(r : G), hs⟩).1 hact n (hNV hn)
  have hcbot : (r : G) * n * (r : G)⁻¹ * n⁻¹ = 1 := by
    have h1 : (r : G) * n * (r : G)⁻¹ * n⁻¹ ∈ NOf D.M V (x : G) ⊓ V₀ :=
      Subgroup.mem_inf.mpr ⟨hcN, hcV₀⟩
    rw [hNbot] at h1
    exact Subgroup.mem_bot.mp h1
  have hcomm1 : ⁅(r : G), n⁆ = 1 := by
    rw [commutatorElement_def]
    exact hcbot
  exact ((commutatorElement_eq_one_iff_mul_comm).1 hcomm1).symm

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end

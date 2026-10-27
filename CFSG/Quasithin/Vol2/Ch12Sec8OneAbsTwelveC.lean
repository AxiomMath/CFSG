module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveB
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsElevenThree
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHatTen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem π_mem_hat_inf (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) :
    D.π a ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g) :=
  HatU.π_mem_hat D (S.thirteen_one hg haV) (le_uA V V₁ haV)

theorem transvection_img (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g),
      ∃ f : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) →ₗ[ZMod 2] ZMod 2,
        f ⟨D.π a, S.π_mem_hat_inf hg D haV⟩ = 0 ∧
          ∀ w : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)),
            γ (w : D.V) = (w : D.V) + f w • D.π a := by
  intro γ hγ
  classical
  obtain ⟨hπa, -, hhatV⟩ := S.hat_V_cases D haV haZ
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  have hd : ∀ w : D.V, w ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g) →
      D.ρ ⟨x, hxN⟩ w - w = 0 ∨ D.ρ ⟨x, hxN⟩ w - w = D.π a := by
    intro w hw
    obtain ⟨e, heE, heU, rfl⟩ := (HatU.mem_hat D).mp hw
    rw [HatU.rho_sub_π D hxN heU]
    have hc : x * e * x⁻¹ * e⁻¹ ∈ rconj (V₁) g :=
      S.commutator_rconj_wA_inf_le x hxX e heE
    have hcV : x * e * x⁻¹ * e⁻¹ ∈ V := (S.l2Setting).V₁_le_rconj_V hg.mem hc
    exact hhatV _ (HatU.π_mem_hat D hcV (le_uA V V₁ hcV))
  have hF : ∀ w : D.V, w ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g) →
      D.ρ ⟨x, hxN⟩ w =
        w + (if D.ρ ⟨x, hxN⟩ w - w = 0 then (0 : ZMod 2) else 1) • D.π a := by
    intro w hw
    by_cases h0 : D.ρ ⟨x, hxN⟩ w - w = 0
    · rw [ite_eq_left h0, zero_smul, add_zero]
      exact sub_eq_zero.mp h0
    · rw [ite_eq_right h0, one_smul]
      have h1 := (hd w hw).resolve_left h0
      rw [← h1]
      abel
  let F : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) → ZMod 2 := fun w =>
    if D.ρ ⟨x, hxN⟩ (w : D.V) - w = 0 then 0 else 1
  have hFw : ∀ w : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)),
      D.ρ ⟨x, hxN⟩ (w : D.V) = (w : D.V) + F w • D.π a := fun w => hF w w.2
  have hinj : ∀ c c' : ZMod 2, c • D.π a = c' • D.π a → c = c' := by
    intro c c' hcc
    have h1 : (c - c') • D.π a = 0 := by rw [sub_smul, hcc, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hπa
  refine ⟨{ toFun := F, map_add' := fun w w' => ?_, map_smul' := fun c w => ?_ }, ?_, hFw⟩
  · apply hinj
    have h1 := hFw (w + w')
    have h2 := hFw w
    have h3 := hFw w'
    simp only [Submodule.coe_add, map_add] at h1
    rw [h2, h3] at h1
    have h5 : (w : D.V) + (w' : D.V) + (F w • D.π a + F w' • D.π a) =
        (w : D.V) + (w' : D.V) + F (w + w') • D.π a := by
      calc _ = ((w : D.V) + F w • D.π a) + ((w' : D.V) + F w' • D.π a) := by abel
        _ = _ := h1
    rw [add_smul]
    exact (add_left_cancel h5).symm
  · simp only [RingHom.id_apply]
    apply hinj
    have h1 := hFw (c • w)
    have h2 := hFw w
    simp only [Submodule.coe_smul, map_smul] at h1
    rw [h2, smul_add, smul_smul] at h1
    rw [smul_eq_mul]
    exact (add_left_cancel h1).symm
  · show (if D.ρ ⟨x, hxN⟩ (D.π a) - D.π a = 0 then (0 : ZMod 2) else 1) = 0
    rw [S.X_fixes_img hg D haV (D.ρ ⟨x, hxN⟩) (HatU.rho_mem_img D hxX hxN), sub_self,
      ite_eq_left rfl]

theorem transvection_full_img (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    ∀ f : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) →ₗ[ZMod 2] ZMod 2,
      f ⟨D.π a, S.π_mem_hat_inf hg D haV⟩ = 0 →
        ∃ γ ∈ D.img (rconj (wA V V₁) g),
          ∀ w : ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)),
            γ (w : D.V) = (w : D.V) + f w • D.π a := by
  intro f hf0
  classical
  obtain ⟨hπa, -, hhatV⟩ := S.hat_V_cases D haV haZ
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
    intro c
    revert c
    decide
  have hEU : wA V V₁ ⊓ rconj (wA V V₁) g ≤ uA V V₁ :=
    inf_le_left.trans (wA_le_uA V V₁)
  have hVE : V ≤ wA V V₁ ⊓ rconj (wA V V₁) g := S.thirteen_one hg
  have hzz : z * z = 1 := by
    simpa [sq] using S.base.sq_eq_one_of_mem_V (S.V₁_le hzZ)
  obtain ⟨z', hz'def⟩ : ∃ z', z' = g⁻¹ * z * g := ⟨_, rfl⟩
  have hz'mem : z' ∈ rconj (V₁) g := by
    rw [hz'def]
    exact inv_mul_mul_mem_rconj hzZ
  have hz'V : z' ∈ V := (S.l2Setting).V₁_le_rconj_V hg.mem hz'mem
  have hz'z' : z' * z' = 1 := by
    rw [hz'def]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    have : z = g * z' * g⁻¹ := by rw [hz'def]; group
    rw [this, h1]
    group
  have hπz'0 : D.π z' ≠ 0 := by
    intro h0
    have hZ : z' ∈ centerOf (uA V V₁) := (HatU.π_eq_zero_iff D (le_uA V V₁ hz'V)).mp h0
    have hbot : z' ∈ rconj (V₁) g ⊓ centerOf (uA V V₁) := ⟨hz'mem, hZ⟩
    rw [S.nine_seven hg] at hbot
    exact hz'1 (Subgroup.mem_bot.mp hbot)
  have hπz' : D.π z' = D.π a :=
    (hhatV _ (HatU.π_mem_hat D hz'V (le_uA V V₁ hz'V))).resolve_left hπz'0
  let fval : G → ZMod 2 := fun e =>
    if hE : e ∈ wA V V₁ ⊓ rconj (wA V V₁) g then f ⟨D.π e, HatU.π_mem_hat D hE (hEU hE)⟩ else 0
  have hfval_mul : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, ∀ e' ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      fval (e * e') = fval e + fval e' := by
    intro e he e' he'
    have hee' : e * e' ∈ wA V V₁ ⊓ rconj (wA V V₁) g :=
      (wA V V₁ ⊓ rconj (wA V V₁) g).mul_mem he he'
    simp only [fval, dite_eq_left he, dite_eq_left he', dite_eq_left hee']
    rw [← map_add]
    congr 1
    exact Subtype.ext (D.π_mul e (hEU he) e' (hEU he'))
  have hfval_V : ∀ v ∈ V, fval v = 0 := by
    intro v hv
    have hvE := hVE hv
    simp only [fval, dite_eq_left hvE]
    rcases hhatV (D.π v) (HatU.π_mem_hat D hv (le_uA V V₁ hv)) with h0 | h0
    · have e1 : (⟨D.π v, HatU.π_mem_hat D hvE (hEU hvE)⟩ :
          ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g))) = 0 := Subtype.ext h0
      rw [e1, map_zero]
    · have e1 : (⟨D.π v, HatU.π_mem_hat D hvE (hEU hvE)⟩ :
          ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g))) =
          ⟨D.π a, S.π_mem_hat_inf hg D haV⟩ := Subtype.ext h0
      rw [e1]
      exact hf0
  let ψ : G → G := fun e => if fval e = 0 then 1 else z'
  have hψV : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, ψ e ∈ rconj (V₁) g := by
    intro e _
    simp only [ψ]
    split_ifs
    · exact Subgroup.one_mem _
    · exact hz'mem
  have hψm : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, ∀ e' ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      ψ (e * e') = ψ e * ψ e' := by
    intro e he e' he'
    simp only [ψ]
    rw [hfval_mul e he e' he']
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hc01 (fval e) with h1 | h1 <;> rcases hc01 (fval e') with h2 | h2 <;>
      simp [h1, h2, h11, hz'z']
  have hψ1 : ∀ v ∈ V, ψ v = 1 := by
    intro v hv
    simp only [ψ, hfval_V v hv, ite_true]
  have hψZ : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, e ∈ centerOf (uA V V₁) → ψ e = 1 := by
    intro e heE heZ
    have h0 : fval e = 0 := by
      simp only [fval, dite_eq_left heE]
      have e1 : (⟨D.π e, HatU.π_mem_hat D heE (hEU heE)⟩ :
          ↥(D.hat (wA V V₁ ⊓ rconj (wA V V₁) g))) = 0 :=
        Subtype.ext ((HatU.π_eq_zero_iff D (hEU heE)).mpr heZ)
      rw [e1, map_zero]
    simp only [ψ, h0, ite_true]
  obtain ⟨x, hxX, hx⟩ := S.eleven_three hg D ψ hψV hψm hψ1 hψZ
  have hxN := S.rconj_wA_le_normalizer_uA hg hxX
  refine ⟨D.ρ ⟨x, hxN⟩, HatU.rho_mem_img D hxX hxN, fun w => ?_⟩
  obtain ⟨e, heE, heU, hπe⟩ := (HatU.mem_hat D).mp w.2
  have hwe : (w : D.V) = D.π e := hπe.symm
  have hfw : f w = fval e := by
    simp only [fval, dite_eq_left heE]
    congr 1
    exact Subtype.ext hwe
  have hxe : x * e * x⁻¹ = ψ e * e := by
    have h1 := hx e heE
    calc x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
      _ = ψ e * e := by rw [h1]
  have hψeV : ψ e ∈ V := (S.l2Setting).V₁_le_rconj_V hg.mem (hψV e heE)
  have hψeU : ψ e ∈ uA V V₁ := le_uA V V₁ hψeV
  rw [hwe, D.ρ_π ⟨x, hxN⟩ _ heU]
  show D.π (x * e * x⁻¹) = D.π e + f w • D.π a
  rw [hxe, D.π_mul _ hψeU _ heU, add_comm, hfw]
  congr 1
  simp only [ψ]
  by_cases h0 : fval e = 0
  · rw [ite_eq_left h0, h0, zero_smul, HatU.π_one D]
  · rw [ite_eq_right h0, hπz', (hc01 (fval e)).resolve_left h0, one_smul]

theorem twelve_one (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    G101Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) (D.img (rconj (wA V V₁) g))
      (D.img (rconj (centerOf (uA V V₁)) g)) where
  alt := HatU.B_isAlt D
  nondegenerate := fun v hv => HatU.B_nondegenerate D v hv
  isometry := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
    exact HatU.B_rho D ⟨x, hxN⟩ v w
  point := (S.hat_V_cases D haV haZ).1
  isotropic := S.hat_isotropic hg D
  mem_W := S.π_mem_hat_inf hg D haV
  X_le := L1294.img_mono D ((S.rconj_wA_le_T hg).trans S.base.T_le_H)
  X_fixes := S.X_fixes_img hg D haV
  X_comm := S.X_comm_img hg D
  X_sq := S.X_sq_img hg D
  X₀_le := L1294.img_mono D (rconj_centerOf_le_rconj_wA V V₁ g)
  span_orbit := S.span_orbit_img D haV haZ
  odd_index := S.odd_index_img D haV haZ
  rank := S.rank_eq hg D
  commutator_le := S.commutator_le_img hg D haV haZ
  centralizer_le := S.centralizer_le_img hg D haV haZ
  transvection := S.transvection_img hg D haV haZ
  transvection_full := S.transvection_full_img hg D haV haZ

end Setting

end L128A

end CFSG.Quasithin.H13

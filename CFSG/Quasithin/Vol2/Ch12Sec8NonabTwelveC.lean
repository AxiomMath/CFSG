module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTwelveB
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabElevenThree
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace HatModel

variable {G : Type} [Group G] {T M : Subgroup G} {D : HatModel T M}

theorem img_sup_eq_of_forall_rho_eq_one {K E : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hEN : E ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hE : ∀ x (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)), x ∈ E → D.rho ⟨x, hxN⟩ = 1) :
    D.img (K ⊔ E) = D.img K := by
  rw [D.img_eq_map (K ⊔ E), D.img_eq_map K, Subgroup.subgroupOf_sup hK hEN, Subgroup.map_sup]
  have : (E.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G))).map D.rho = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hE (x : G) x.2 hx
  rw [this, sup_bot_eq]

end HatModel

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem π_mem_hat_inf (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) :
    D.π a ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g) :=
  D.π_mem_hat (h.lemma_12_8_13_one hU hg haV) (VZ_le_uOfL22 T M haV)

theorem transvection_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g),
      ∃ f : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) →ₗ[ZMod 2] ZMod 2,
        f ⟨D.π a, h.π_mem_hat_inf hU hg D haV⟩ = 0 ∧
          ∀ w : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)),
            γ (w : D.V) = (w : D.V) + f w • D.π a := by
  intro γ hγ
  classical
  obtain ⟨hπa, -, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  have hd : ∀ w : D.V, w ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g) →
      D.rho ⟨x, hxN⟩ w - w = 0 ∨ D.rho ⟨x, hxN⟩ w - w = D.π a := by
    intro w hw
    obtain ⟨e, heE, heU, rfl⟩ := D.mem_hat.mp hw
    rw [HatModel.rho_sub_π (D := D) hxN heU]
    have hc : x * e * x⁻¹ * e⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g :=
      h.commutator_rconj_wOfU_inf_le x hxX e heE
    have hcV : x * e * x⁻¹ * e⁻¹ ∈ VZ T M := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem hc
    exact hhatV _ (D.π_mem_hat hcV (VZ_le_uOfL22 T M hcV))
  have hF : ∀ w : D.V, w ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g) →
      D.rho ⟨x, hxN⟩ w =
        w + (if D.rho ⟨x, hxN⟩ w - w = 0 then (0 : ZMod 2) else 1) • D.π a := by
    intro w hw
    by_cases h0 : D.rho ⟨x, hxN⟩ w - w = 0
    · rw [ite_eq_left h0, zero_smul, add_zero]
      exact sub_eq_zero.mp h0
    · rw [ite_eq_right h0, one_smul]
      have h1 := (hd w hw).resolve_left h0
      rw [← h1]
      abel
  let F : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) → ZMod 2 := fun w =>
    if D.rho ⟨x, hxN⟩ (w : D.V) - w = 0 then 0 else 1
  have hFw : ∀ w : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)),
      D.rho ⟨x, hxN⟩ (w : D.V) = (w : D.V) + F w • D.π a := fun w => hF w w.2
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
  · show (if D.rho ⟨x, hxN⟩ (D.π a) - D.π a = 0 then (0 : ZMod 2) else 1) = 0
    rw [h.X_fixes_img hU hg D haV (D.rho ⟨x, hxN⟩) (HatModel.rho_mem_img hxX hxN), sub_self,
      ite_eq_left rfl]

theorem transvection_full_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    ∀ f : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) →ₗ[ZMod 2] ZMod 2,
      f ⟨D.π a, h.π_mem_hat_inf hU hg D haV⟩ = 0 →
        ∃ γ ∈ D.img (rconj (wOfU T M) g),
          ∀ w : ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g)),
            γ (w : D.V) = (w : D.V) + f w • D.π a := by
  intro f hf0
  classical
  obtain ⟨hπa, -, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
    intro c
    revert c
    decide
  have hEU : wOfU T M ⊓ rconj (wOfU T M) g ≤ uOfL22 T M :=
    inf_le_left.trans (wOfU_le_uOfL22 T M)
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := h.lemma_12_8_13_one hU hg
  have hzz : z * z = 1 := by
    simpa [sq] using h.almostSpecialHyp_g1.sq_eq_one_of_mem_V (omegaOneCenter_le_VZ T M hzZ)
  obtain ⟨z', hz'def⟩ : ∃ z', z' = g⁻¹ * z * g := ⟨_, rfl⟩
  have hz'mem : z' ∈ rconj (quasithinOmegaOneCenter T) g := by
    rw [hz'def]
    exact inv_mul_mul_mem_rconj hzZ
  have hz'V : z' ∈ VZ T M := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem hz'mem
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
    have hZ : z' ∈ centerOf (uOfL22 T M) := (D.π_eq_zero_iff (VZ_le_uOfL22 T M hz'V)).mp h0
    have hbot : z' ∈ rconj (quasithinOmegaOneCenter T) g ⊓ centerOf (uOfL22 T M) := ⟨hz'mem, hZ⟩
    rw [h.lemma_12_8_9_seven hU hg] at hbot
    exact hz'1 (Subgroup.mem_bot.mp hbot)
  have hπz' : D.π z' = D.π a :=
    (hhatV _ (D.π_mem_hat hz'V (VZ_le_uOfL22 T M hz'V))).resolve_left hπz'0
  let fval : G → ZMod 2 := fun e =>
    if hE : e ∈ wOfU T M ⊓ rconj (wOfU T M) g then f ⟨D.π e, D.π_mem_hat hE (hEU hE)⟩ else 0
  have hfval_mul : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g, ∀ e' ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      fval (e * e') = fval e + fval e' := by
    intro e he e' he'
    have hee' : e * e' ∈ wOfU T M ⊓ rconj (wOfU T M) g :=
      (wOfU T M ⊓ rconj (wOfU T M) g).mul_mem he he'
    simp only [fval, dite_eq_left he, dite_eq_left he', dite_eq_left hee']
    rw [← map_add]
    congr 1
    exact Subtype.ext (D.π_mul e (hEU he) e' (hEU he'))
  have hfval_V : ∀ v ∈ VZ T M, fval v = 0 := by
    intro v hv
    have hvE := hVE hv
    simp only [fval, dite_eq_left hvE]
    rcases hhatV (D.π v) (D.π_mem_hat hv (VZ_le_uOfL22 T M hv)) with h0 | h0
    · have e1 : (⟨D.π v, D.π_mem_hat hvE (hEU hvE)⟩ :
          ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g))) = 0 := Subtype.ext h0
      rw [e1, map_zero]
    · have e1 : (⟨D.π v, D.π_mem_hat hvE (hEU hvE)⟩ :
          ↥(D.hat (wOfU T M ⊓ rconj (wOfU T M) g))) =
          ⟨D.π a, h.π_mem_hat_inf hU hg D haV⟩ := Subtype.ext h0
      rw [e1]
      exact hf0
  let ψ : G → G := fun e => if fval e = 0 then 1 else z'
  have hψV : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g, ψ e ∈ rconj (quasithinOmegaOneCenter T) g := by
    intro e _
    simp only [ψ]
    split_ifs
    · exact Subgroup.one_mem _
    · exact hz'mem
  have hψm : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g, ∀ e' ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      ψ (e * e') = ψ e * ψ e' := by
    intro e he e' he'
    simp only [ψ]
    rw [hfval_mul e he e' he']
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hc01 (fval e) with h1 | h1 <;> rcases hc01 (fval e') with h2 | h2 <;>
      simp [h1, h2, h11, hz'z']
  have hψ1 : ∀ v ∈ VZ T M, ψ v = 1 := by
    intro v hv
    simp only [ψ, hfval_V v hv, ite_true]
  obtain ⟨x, hxX, hx⟩ := h.lemma_12_8_11_three hU hg ψ hψV hψm hψ1
  have hxN := h.rconj_wOfU_le_normalizer_uOfL22 hU hg hxX
  refine ⟨D.rho ⟨x, hxN⟩, HatModel.rho_mem_img hxX hxN, fun w => ?_⟩
  obtain ⟨e, heE, heU, hπe⟩ := D.mem_hat.mp w.2
  have hwe : (w : D.V) = D.π e := hπe.symm
  have hfw : f w = fval e := by
    simp only [fval, dite_eq_left heE]
    congr 1
    exact Subtype.ext hwe
  have hxe : x * e * x⁻¹ = ψ e * e := by
    have h1 := hx e heE
    calc x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
      _ = ψ e * e := by rw [h1]
  have hψeV : ψ e ∈ VZ T M := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem (hψV e heE)
  have hψeU : ψ e ∈ uOfL22 T M := VZ_le_uOfL22 T M hψeV
  rw [hwe, D.rho_π ⟨x, hxN⟩ heU]
  show D.π (x * e * x⁻¹) = D.π e + f w • D.π a
  rw [hxe, D.π_mul _ hψeU _ heU, add_comm, hfw]
  congr 1
  simp only [ψ]
  by_cases h0 : fval e = 0
  · rw [ite_eq_left h0, h0, zero_smul, D.π_one]
  · rw [ite_eq_right h0, hπz', (hc01 (fval e)).resolve_left h0, one_smul]

theorem lemma_12_8_12_one (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    G101Hyp D.B (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a)
      (D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) (D.img (rconj (wOfU T M) g))
      (D.img (rconj (centerOf (uOfL22 T M)) g)) where
  alt := D.B_isAlt
  nondegenerate := fun v hv => D.B_nondegenerate v hv
  isometry := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := HatModel.mem_img.mp hγ
    exact D.B_rho ⟨x, hxN⟩ v w
  point := (h.hat_VZ_cases hU D haV haZ).1
  isotropic := h.hat_isotropic hU hg D
  mem_W := h.π_mem_hat_inf hU hg D haV
  X_le := HatModel.img_mono ((h.rconj_wOfU_le_T hU hg).trans h.almostSpecialHyp_g1.T_le_H)
  X_fixes := h.X_fixes_img hU hg D haV
  X_comm := h.X_comm_img hU hg D
  X_sq := h.X_sq_img hU hg D
  X₀_le := HatModel.img_mono (rconj_centerOf_le_rconj_wOfU T M g)
  span_orbit := h.span_orbit_img hU D haV haZ
  odd_index := h.odd_index_img hU D haV haZ
  rank := h.rank_eq hU hg D
  commutator_le := h.commutator_le_img hU hg D haV haZ
  centralizer_le := h.centralizer_le_img hU hg D haV haZ
  transvection := h.transvection_img hU hg D haV haZ
  transvection_full := h.transvection_full_img hU hg D haV haZ

end Hyp1281Two

end CFSG.Quasithin

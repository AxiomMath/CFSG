module

public import CFSG.Quasithin.Vol2.Ch3E213MG41C1
public import CFSG.Quasithin.Vol2.Ch3E213MG41A

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def fixPerp (v w : Fin 4 → k) : Subgroup (antiSp k) where
  carrier := {g | ∀ z, spBil z v = 0 → spBil z w = 0 → natAct g z = z}
  one_mem' z _ _ := natAct_one z
  mul_mem' {g h} hg hh z hzv hzw := by
    change natAct (g * h) z = z
    rw [natAct_mul, hh z hzv hzw, hg z hzv hzw]
  inv_mem' {g} hg z hzv hzw := by
    change natAct g⁻¹ z = z
    calc natAct g⁻¹ z = natAct g⁻¹ (natAct g z) := by rw [hg z hzv hzw]
      _ = z := act_inv_act g z

omit [CharP k 2] in
theorem mem_fixPerp {v w : Fin 4 → k} {g : antiSp k} :
    g ∈ fixPerp v w ↔ ∀ z, spBil z v = 0 → spBil z w = 0 → natAct g z = z :=
  Iff.rfl

omit [CharP k 2] in
theorem fixPerp_comm (v w : Fin 4 → k) : fixPerp v w = fixPerp w v := by
  ext g
  simp only [mem_fixPerp]
  exact ⟨fun h z h1 h2 => h z h2 h1, fun h z h1 h2 => h z h2 h1⟩

theorem trv_mem_fixPerp_left (v w : Fin 4 → k) (c : k) : trv v c ∈ fixPerp v w :=
  fun _ hzv _ => act_trv_of_bil_eq_zero c hzv

theorem trv_mem_fixPerp_right (v w : Fin 4 → k) (c : k) : trv w c ∈ fixPerp v w :=
  fun _ _ hzw => act_trv_of_bil_eq_zero c hzw

section Pair

variable {v w : Fin 4 → k} (hvw : spBil v w = 1)
include hvw

omit [CharP k 2] in
theorem bil_wv : spBil w v = 1 := by
  rw [bil_symm, hvw]

theorem perp_comb (x : Fin 4 → k) :
    spBil (x - spBil x w • v - spBil x v • w) v = 0 ∧
      spBil (x - spBil x w • v - spBil x v • w) w = 0 := by
  have hwv := bil_wv hvw
  constructor <;> simp [bil_self, hvw, hwv]

theorem eq_comb {r : Fin 4 → k} (hr : ∀ z, spBil z v = 0 → spBil z w = 0 → spBil z r = 0) :
    r = spBil r w • v + spBil r v • w := by
  set r' := r - spBil r w • v - spBil r v • w with hr'
  have h0 : r' = 0 := by
    apply eq_zero_of_bil_eq_zero
    intro z
    obtain ⟨hzv, hzw⟩ := perp_comb hvw z
    have h1 := hr _ hzv hzw
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left] at h1
    rw [hr']
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
    rw [bil_symm v r, bil_symm w r] at h1
    linear_combination h1
  rw [hr', sub_sub, sub_eq_zero] at h0
  exact h0

theorem act_eq_comb {g : antiSp k} (hg : g ∈ fixPerp v w) {x : Fin 4 → k}
    (hx : ∀ z, spBil z v = 0 → spBil z w = 0 → spBil z x = 0) :
    natAct g x = spBil (natAct g x) w • v + spBil (natAct g x) v • w := by
  apply eq_comb hvw
  intro z hzv hzw
  rw [← hg z hzv hzw, bil_act]
  exact hx z hzv hzw

theorem act_v_eq {g : antiSp k} (hg : g ∈ fixPerp v w) :
    natAct g v = spBil (natAct g v) w • v + spBil (natAct g v) v • w :=
  act_eq_comb hvw hg fun _ hz _ => hz

theorem act_w_eq {g : antiSp k} (hg : g ∈ fixPerp v w) :
    natAct g w = spBil (natAct g w) w • v + spBil (natAct g w) v • w :=
  act_eq_comb hvw hg fun _ _ hz => hz

theorem eq_of_agree {g h : antiSp k} (hg : g ∈ fixPerp v w) (hh : h ∈ fixPerp v w)
    (h1 : natAct g v = natAct h v) (h2 : natAct g w = natAct h w) : g = h := by
  apply ext_act
  intro z
  obtain ⟨hzv, hzw⟩ := perp_comb hvw z
  have hz : z = (z - spBil z w • v - spBil z v • w) + spBil z w • v + spBil z v • w := by abel
  rw [hz, act_add, act_add, act_add, act_add, act_smul, act_smul, act_smul, act_smul,
    hg _ hzv hzw, hh _ hzv hzw, h1, h2]

end Pair

@[expose] def rhoMat (v w : Fin 4 → k) (g : antiSp k) : Matrix (Fin 2) (Fin 2) k :=
  !![spBil (natAct g v) w, spBil (natAct g w) w; spBil (natAct g v) v, spBil (natAct g w) v]

variable {v w : Fin 4 → k}

theorem det_rhoMat (hvw : spBil v w = 1) {g : antiSp k} (hg : g ∈ fixPerp v w) :
    (rhoMat v w g).det = 1 := by
  rw [rhoMat, Matrix.det_fin_two_of]
  have key : spBil (natAct g v) (natAct g w) = 1 := by rw [bil_act, hvw]
  obtain ⟨a, c, hv⟩ : ∃ a c : k, natAct g v = a • v + c • w := ⟨_, _, act_v_eq hvw hg⟩
  obtain ⟨b, d, hw⟩ : ∃ b d : k, natAct g w = b • v + d • w := ⟨_, _, act_w_eq hvw hg⟩
  have hwv := bil_wv hvw
  rw [hv, hw] at key ⊢
  simp [bil_self, hvw, hwv] at key ⊢
  linear_combination key - b * c * (CharTwo.two_eq_zero : (2 : k) = 0)

theorem rhoMat_one (hvw : spBil v w = 1) : rhoMat v w (1 : antiSp k) = 1 := by
  have hwv := bil_wv hvw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoMat, natAct_one, bil_self, hvw, hwv]

theorem rhoMat_mul (hvw : spBil v w = 1) (g : antiSp k) {h : antiSp k} (hh : h ∈ fixPerp v w) :
    rhoMat v w (g * h) = rhoMat v w g * rhoMat v w h := by
  obtain ⟨a, c, hv⟩ : ∃ a c : k, natAct h v = a • v + c • w := ⟨_, _, act_v_eq hvw hh⟩
  obtain ⟨b, d, hw⟩ : ∃ b d : k, natAct h w = b • v + d • w := ⟨_, _, act_w_eq hvw hh⟩
  have hwv := bil_wv hvw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoMat, natAct_mul, hv, hw, act_add, act_smul, Matrix.mul_apply, Fin.sum_univ_two,
      bil_self, hvw, hwv] <;> ring

@[expose] noncomputable def rho (hvw : spBil v w = 1) :
    fixPerp v w →* Matrix.SpecialLinearGroup (Fin 2) k where
  toFun g := ⟨rhoMat v w g, det_rhoMat hvw g.2⟩
  map_one' := Subtype.ext (rhoMat_one hvw)
  map_mul' g h := Subtype.ext (rhoMat_mul hvw g h.2)

theorem rho_injective (hvw : spBil v w = 1) : Function.Injective (rho hvw) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hm : rhoMat v w g = 1 := congrArg Subtype.val hg
  have h00 : spBil (natAct g v) w = 1 := by
    have := congrFun (congrFun hm 0) 0
    simpa [rhoMat] using this
  have h01 : spBil (natAct g w) w = 0 := by
    have := congrFun (congrFun hm 0) 1
    simpa [rhoMat] using this
  have h10 : spBil (natAct g v) v = 0 := by
    have := congrFun (congrFun hm 1) 0
    simpa [rhoMat] using this
  have h11 : spBil (natAct g w) v = 1 := by
    have := congrFun (congrFun hm 1) 1
    simpa [rhoMat] using this
  have hv : natAct g v = v := by
    rw [act_v_eq hvw g.2, h00, h10, one_smul, zero_smul, add_zero]
  have hw : natAct g w = w := by
    rw [act_w_eq hvw g.2, h01, h11, zero_smul, one_smul, zero_add]
  apply Subtype.ext
  exact eq_of_agree hvw g.2 (one_mem _) (by rw [hv]; exact (natAct_one v).symm)
    (by rw [hw]; exact (natAct_one w).symm)

@[expose] noncomputable def rhoP (hvw : spBil v w = 1) :
    fixPerp v w →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
  (QuotientGroup.mk' _).comp (rho hvw)

theorem rhoP_injective (hvw : spBil v w = 1) : Function.Injective (rhoP hvw) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : rho hvw g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) :=
    (QuotientGroup.eq_one_iff _).mp hg
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at h1
  exact (injective_iff_map_eq_one _).mp (rho_injective hvw) g h1

end CFSG.Quasithin.Ch3E213M.G41

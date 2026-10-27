module

public import CFSG.Quasithin.H13.L32A513b
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.H13.L32A513a
public import CFSG.Quasithin.H13.L32A53c

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem lemma14_5_13Fin_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₂ Y : Subgroup G), Ctx G T L V V₂ Y →
      quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)) →
      (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T →
      pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) →
      thompsonJ T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) →
      xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ →
      (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)).map (hY T L V₂ Y).subtype ≤
        Subgroup.centralizer (vH T L V V₂ Y : Set G) →
      pCoreOf 2 (xL L V₂ ⊔ T) ≠ pCoreOf 2 (Y ⊔ T) →
      F6.IsF618CaseTwo (↥(hY T L V₂ Y) ⧸ CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)) →
      False := by
  intro G _ _ T L V V₂ Y C hXS3 _ hQ _ _ _ h311 _ hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  set H := hY T L V₂ Y with hHdef
  set W := vH T L V V₂ Y with hWdef
  have hWe : IsElemAbelian 2 W := (C.vH_le_center hQ).2
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hXH : xL L V₂ ⊔ T ≤ H := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hV1W : fsuV1 T V ≤ W := le_conjClosure _ _
  have hV2W : V₂ ≤ W := by
    rw [← C.conjClosure_V1_X]
    exact conjClosure_mono le_rfl (le_sup_left.trans le_sup_left)
  set ψ : ↥H →* MulAut (IntMod W hWe) := (convI hWe).comp (Subgroup.inclusion hHW) with hψ
  have hψ1 : ∀ h : ↥H, ψ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (W : Set G) := fun h =>
    convI_eq_one_iff hWe _
  have hψval : ∀ (h : ↥H) (u : IntMod W hWe), ((ψ h) u).val = (h : G) * u.val * (h : G)⁻¹ :=
    fun h u => convI_apply_val hWe _ u
  have hψv : ∀ (h : ↥H) (w : G) (hw : w ∈ W),
      ((ψ h) (IntMod.mk hWe ⟨w, hw⟩)).val = (h : G) * w * (h : G)⁻¹ := fun h w hw =>
    hψval h _
  have hNψ : CFSG.pPrimeCore 3 ↥H ≤ ψ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, hψ1]
    exact h311 ⟨h, hh, rfl⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) with hπ
  set ψ' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥H) ψ hNψ with hψ'
  have hψπ : ∀ h : ↥H, ψ' (π h) = ψ h := fun _ => rfl
  have hQ3 : ∀ a b : ↥H ⧸ CFSG.pPrimeCore 3 ↥H, a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 :=
    fun _ _ ha hb => (f618Two_cube hF ha hb).1
  obtain ⟨x₀, hx₀, hx₀o, y, hy, hyo, hb₀⟩ := C.exists_comm_not_mem
  obtain ⟨z, a, x, hz, hz1, ha, haV, hx, hx3, hxz, hxa⟩ := C.exists_rot_X
  have hxXT : x ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_left hx
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)
  have hzW : z ∈ W := hV1W hz
  have haW : a ∈ W := hV2W ha
  have hyY : y ∈ Y := by
    rw [← C.oTwoUpper_yT]
    exact Subgroup.subset_closure ⟨hy, hyo⟩
  have hyz : y * z * y⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp (C.le_centralizer_V1 hyY) z hz, mul_inv_cancel_right]
  set hx' : ↥H := ⟨x, hXH hxXT⟩ with hhx'
  set hy' : ↥H := ⟨y, hYH hy⟩ with hhy'
  set hx₀' : ↥H := ⟨x₀, hXH hx₀⟩ with hhx₀'
  have hπx : π hx' ≠ 1 := by
    intro h
    have h1 : ψ hx' = 1 := by rw [← hψπ, h, map_one]
    rw [hψ1] at h1
    apply haV
    have h2 : x * z = z * x := (Subgroup.mem_centralizer_iff.mp h1 z hzW).symm
    rw [← hxz, h2, mul_inv_cancel_right]
    exact hz
  obtain ⟨j, hj⟩ := exists_eq_pow_of_odd hXH hXS3 π hQ3 hxXT hx₀ hxo hx₀o hπx
  have hψx₀ : ψ hx₀' = ψ hx' ^ j := by rw [← hψπ, ← hψπ, ← map_pow, ← hj]
  have hcomm : ∀ (h k : ↥H), ⁅ψ h, ψ k⁆ = 1 → ⁅(h : G), (k : G)⁆ ∈
      Subgroup.centralizer (W : Set G) := fun h k hhk => by
    have : ψ ⁅h, k⁆ = 1 := by rw [map_commutatorElement, hhk]
    rw [hψ1] at this
    exact this
  have hb : ⁅x, y⁆ ∉ Subgroup.centralizer (W : Set G) := by
    intro hxy
    apply hb₀
    have h1 : ψ ⁅hx', hy'⁆ = 1 := (hψ1 _).mpr hxy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    refine hcomm hx₀' hy' ?_
    rw [hψx₀, commutatorElement_eq_one_iff_mul_comm]
    exact ((Commute.pow_left h1 j) : _)
  have hx3' : π hx' ^ 3 = 1 := by
    rw [← map_pow]
    have : hx' ^ 3 = 1 := Subtype.ext (by simpa [hhx'] using hx3)
    rw [this, map_one]
  have hy3' : π hy' ^ 3 = 1 := by
    rw [← map_pow]
    have : hy' ^ 3 = 1 := Subtype.ext (by simpa [hhy'] using cube_of_odd C.hS3 hy hyo)
    rw [this, map_one]
  obtain ⟨-, hcx, hcy, hc3, hcg⟩ := f618Two_cube hF hx3' hy3'
  set σx := ψ hx' with hσx
  set σy := ψ hy' with hσy
  set σb := ψ ⁅hx', hy'⁆ with hσb
  have hσb' : σb = ψ' ⁅π hx', π hy'⁆ := by
    rw [hσb, map_commutatorElement, map_commutatorElement, hψπ, hψπ]
  have hbx : σb * σx = σx * σb := by
    rw [hσb', hσx, ← hψπ, ← map_mul, ← map_mul, hcx]
  have hby : σb * σy = σy * σb := by
    rw [hσb', hσy, ← hψπ, ← map_mul, ← map_mul, hcy]
  have hb3 : σb ^ 3 = 1 := by rw [hσb', ← map_pow, hc3, map_one]
  have hbdef : σb = σx * σy * σx⁻¹ * σy⁻¹ := by
    rw [hσb, map_commutatorElement, commutatorElement_def]
  set v : IntMod W hWe := IntMod.mk hWe ⟨z, hzW⟩ with hv
  have hyv : σy v = v := by
    apply IntMod.val_injective
    rw [hσy, hv, hψv]
    exact hyz
  have hxv : v * σx v * σx (σx v) = 1 := by
    have h1 : σx v = IntMod.mk hWe ⟨a, haW⟩ := by
      apply IntMod.val_injective
      rw [hσx, hv, hψv]
      exact hxz
    have h2 : σx (σx v) = IntMod.mk hWe ⟨z * a, W.mul_mem hzW haW⟩ := by
      apply IntMod.val_injective
      rw [h1, hσx, hψv]
      exact hxa
    rw [h2, h1]
    apply IntMod.val_injective
    simp only [IntMod.val_mul, IntMod.val_one]
    show z * a * (z * a) = 1
    have hza : z * a = a * z := S.comm_V (Subgroup.mem_inf.mp hz).1 (S.hV2.2.1 ha)
    have hz2 : z * z = 1 := S.mul_self_V (Subgroup.mem_inf.mp hz).1
    have ha2 : a * a = 1 := S.mul_self_V (S.hV2.2.1 ha)
    calc z * a * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [← hza]
      _ = (z * z) * (a * a) := by group
      _ = 1 := by rw [hz2, ha2, one_mul]
  have hbv : σb v = v :=
    fix_of_comm_triple (fun w => IntMod.sq_eq_one (hV := hWe) w) hbdef hbx hby hb3 hyv hxv
  have hbz : ∀ h : ↥H, σb (ψ h v) = ψ h v := by
    intro h
    have hconj : (ψ h)⁻¹ * σb * ψ h = σb ∨ (ψ h)⁻¹ * σb * ψ h = σb ^ 2 := by
      rcases hcg (π h)⁻¹ with h1 | h1
      · left
        have := congrArg ψ' h1
        rwa [map_mul, map_mul, map_inv, inv_inv, hψπ, ← hσb'] at this
      · right
        have := congrArg ψ' h1
        rwa [map_mul, map_mul, map_inv, inv_inv, hψπ, map_pow, ← hσb'] at this
    have hfix : ((ψ h)⁻¹ * σb * ψ h) v = v := by
      rcases hconj with h1 | h1
      · rw [h1, hbv]
      · rw [h1, pow_two, MulAut.mul_apply, hbv, hbv]
    have := congrArg (ψ h) hfix
    simpa [MulAut.mul_apply] using this
  apply hb
  have hWC : W ≤ Subgroup.centralizer ({⁅x, y⁆} : Set G) := by
    refine conjClosure_le fun h hh w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rcases S.eq_of_mem_V1 hz hz1 hw with hw1 | hw1
    · rw [hw1]
      simp
    · rw [hw1]
      have h1 := congrArg IntMod.val (hbz ⟨h, hh⟩)
      rw [hσb, hψval, hψval] at h1
      have h2 : ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ = h * z * h⁻¹ := h1
      calc ⁅x, y⁆ * (h * z * h⁻¹) = ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by group
        _ = h * z * h⁻¹ * ⁅x, y⁆ := by rw [h2]
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hWC hw) _ rfl).symm

end CFSG.Quasithin.H13.L32A.T53

end

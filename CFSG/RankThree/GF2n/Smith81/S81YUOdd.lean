module

public import CFSG.RankThree.GF2n.Smith81.S81YUDef
public import CFSG.RankThree.GF2n.Smith81.S81RD8G1
public import CFSG.RankThree.GF2n.Smith81.S81RRangeOdd
public import CFSG.RankThree.GF2n.Smith81.S81RTransvOrder
public import CFSG.RankThree.GF2n.Smith81.S81UTv
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]

private theorem s81yu_tvMat_eq (a : Fin 6 → F) (c : F) :
    tvMat σ a c = 1 + vecMulVec a (fun i => c * σ (a i)) := by
  unfold tvMat
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec, Matrix.of_apply]
  ring

private theorem s81yu_mul_self [CharP K 2] {g : GL (Fin 6) K} (hg : IsTransvec K g) :
    g * g = 1 := by
  apply Units.ext
  have h := hg.1
  set A : Matrix (Fin 6) (Fin 6) K := (g : Matrix (Fin 6) (Fin 6) K) with hA
  have e : (A - 1) * (A - 1) = A * A - (A + A) + 1 := by noncomm_ring
  have h2 : A + A = 0 := by rw [← two_smul K A, CharTwo.two_eq_zero, zero_smul]
  have h1 : (1 : Matrix (Fin 6) (Fin 6) K) + 1 = 0 := by
    rw [← two_smul K (1 : Matrix (Fin 6) (Fin 6) K), CharTwo.two_eq_zero, zero_smul]
  rw [e, h2, sub_zero] at h
  rw [Units.val_mul, Units.val_one]
  calc A * A = (A * A + 1) + 1 := by rw [add_assoc, h1, add_zero]
    _ = 1 := by rw [h, zero_add]

theorem u6_herm_eq_zero_of_not_odd (hσ : IsUnitaryInvolution σ) (e : K ≃+* Fσ σ)
    {gx gy : SUid σ 6} (hx : IsTransvec F (gx : GL (Fin 6) F)) (hy : IsTransvec F (gy : GL (Fin 6) F))
    {a b : Fin 6 → F} {c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (haa : herm σ a a = 0) (hbb : herm σ b b = 0)
    (hxa : ((gx : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = tvMat σ a c)
    (hyb : ((gy : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = tvMat σ b d)
    (h : ¬ (Odd (orderOf (e3uWact σ e gx * e3uWact σ e gy)) ∧
      e3uWact σ e gx * e3uWact σ e gy ≠ 1)) :
    herm σ a b = 0 := by
  by_contra hab
  have hxmat : ((gx : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      1 + vecMulVec a (fun i => c * σ (a i)) := hxa.trans (s81yu_tvMat_eq a c)
  have hymat : ((gy : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      1 + vecMulVec b (fun i => d * σ (b i)) := hyb.trans (s81yu_tvMat_eq b d)
  have hfa : (fun i => c * σ (a i)) ⬝ᵥ a = 0 := by
    have : (fun i => c * σ (a i)) ⬝ᵥ a = c * herm σ a a := by
      simp only [dotProduct, herm, Finset.mul_sum, mul_assoc]
    rw [this, haa, mul_zero]
  have hgb : (fun i => d * σ (b i)) ⬝ᵥ b = 0 := by
    have : (fun i => d * σ (b i)) ⬝ᵥ b = d * herm σ b b := by
      simp only [dotProduct, herm, Finset.mul_sum, mul_assoc]
    rw [this, hbb, mul_zero]
  have hfb : (fun i => c * σ (a i)) ⬝ᵥ b = c * herm σ a b := by
    simp only [dotProduct, herm, Finset.mul_sum, mul_assoc]
  have hga : (fun i => d * σ (b i)) ⬝ᵥ a = d * σ (herm σ a b) := by
    rw [← CFSG.ClassicalGroups.Unitary.herm_conj σ hσ.invol a b]
    simp only [dotProduct, herm, Finset.mul_sum, mul_assoc]
  have hfb_ne : (fun i => c * σ (a i)) ⬝ᵥ b ≠ 0 := by
    rw [hfb]
    exact mul_ne_zero hc hab
  have hga_ne : (fun i => d * σ (b i)) ⬝ᵥ a ≠ 0 := by
    rw [hga]
    exact mul_ne_zero hd ((map_ne_zero σ).mpr hab)
  have hrho : rho F (((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F)) ^ 4) ≠ 1 := fun h4 => by
    rcases transvec_cases_of_rho_pow_four hxmat hymat hfa hgb h4 with h1 | h1
    · exact hfb_ne h1
    · exact hga_ne h1
  have hpow4 : ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F)) ^ 4 ≠ 1 :=
    fun h4 => hrho (by rw [h4, CFSG.RankThree.GF2n.Smith81.A5Cube.rho_one])
  have hndvd : ¬ orderOf ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F)) ∣ 4 :=
    fun hd4 => hpow4 (orderOf_dvd_iff_pow_eq_one.mp hd4)
  have hodd_gl : Odd (orderOf ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F))) := by
    rcases orderOf_mul_cases_gl hx hy with h4 | h5
    · exact absurd h4 hndvd
    · exact h5
  have hordG : orderOf (gx * gy) = orderOf ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F)) := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
  have hodd_pre : Odd (orderOf (gx * gy)) := by
    rw [hordG]
    exact hodd_gl
  have hodd_img : Odd (orderOf (e3uWact σ e gx * e3uWact σ e gy)) := by
    have hdvd : orderOf (e3uWact σ e (gx * gy)) ∣ orderOf (gx * gy) :=
      orderOf_map_dvd (e3uWact σ e) (gx * gy)
    rw [map_mul] at hdvd
    exact Odd.of_dvd_nat hodd_pre hdvd
  have hne_img : e3uWact σ e gx * e3uWact σ e gy ≠ 1 := by
    intro hprod
    have hgg1 : gy * gy = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact s81yu_mul_self hy)
    have hyy : e3uWact σ e gy * e3uWact σ e gy = 1 := by
      rw [← map_mul (e3uWact σ e) gy gy, hgg1, map_one]
    have heq : e3uWact σ e gx = e3uWact σ e gy :=
      calc e3uWact σ e gx = (e3uWact σ e gy)⁻¹ := eq_inv_of_mul_eq_one_left hprod
        _ = e3uWact σ e gy := inv_eq_of_mul_eq_one_right hyy
    have hgxy : gx = gy :=
      CFSG.RankThree.GF2n.Smith81.eq_of_e3uWact_eq_of_isTransvec hσ hx hy heq
    have hmat : tvMat σ a c = tvMat σ b d := by
      rw [← hxa, ← hyb, hgxy]
    have h1 : tvMat σ a c *ᵥ b = tvMat σ b d *ᵥ b := by
      rw [hmat]
    rw [CFSG.ClassicalGroups.Unitary.tvMat_mulVec, CFSG.ClassicalGroups.Unitary.tvMat_mulVec,
      hbb, mul_zero, zero_smul, add_zero] at h1
    have h2 : (c * herm σ a b) • a = 0 := by
      calc (c * herm σ a b) • a = (b + (c * herm σ a b) • a) - b := by abel
        _ = 0 := by rw [h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hab ((mul_eq_zero.mp h3).resolve_left hc)
    · exact ha h3
  exact h ⟨hodd_img, hne_img⟩

theorem u6_odd_disj (e : K ≃+* Fσ σ) (r s : E3UWspace σ e ≃ₗ[K] E3UWspace σ e)
    (hr : IsRtU σ e r) (hs : IsRtU σ e s) (hodd : Odd (orderOf (r * s))) (hne : r * s ≠ 1) :
    LinearMap.range ((r : E3UWspace σ e →ₗ[K] E3UWspace σ e) - 1) ⊓
      LinearMap.range ((s : E3UWspace σ e →ₗ[K] E3UWspace σ e) - 1) = ⊥ := by
  obtain ⟨gx, hx, rfl⟩ := hr
  obtain ⟨gy, hy, rfl⟩ := hs
  have hne' : (gx : GL (Fin 6) F) * (gy : GL (Fin 6) F) ≠ 1 := by
    intro h1
    apply hne
    have h2 : gx * gy = 1 := Subtype.ext (by rw [Subgroup.coe_mul, h1, Subgroup.coe_one])
    rw [← map_mul (e3uWact σ e) gx gy, h2, map_one]
  have hodd' : Odd (orderOf ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F))) := by
    rcases orderOf_mul_cases_gl hx hy with h4 | h5
    · exfalso
      have hp : ((gx : GL (Fin 6) F) * (gy : GL (Fin 6) F)) ^ 4 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp h4
      have hp' : (gx * gy) ^ 4 = 1 := Subtype.ext (by simpa using hp)
      have hpe : (e3uWact σ e gx * e3uWact σ e gy) ^ 4 = 1 := by
        rw [← map_mul (e3uWact σ e) gx gy, ← map_pow (e3uWact σ e) (gx * gy) 4, hp', map_one]
      have hdv4 : orderOf (e3uWact σ e gx * e3uWact σ e gy) ∣ 4 :=
        orderOf_dvd_of_pow_eq_one hpe
      obtain ⟨k, hk⟩ := hodd
      have hk1 : k ≤ 1 := by
        have hle : 2 * k + 1 ≤ 4 := Nat.le_of_dvd (by norm_num) (by rw [← hk]; exact hdv4)
        omega
      interval_cases k
      · exact hne (orderOf_eq_one_iff.mp (by simpa using hk))
      · rw [hk] at hdv4
        norm_num at hdv4
    · exact h5
  have key := range_inf_range_eq_bot_odd hx hy hodd' hne'
  have hX : ∀ (g : SUid σ 6) (v : E3UWspace σ e),
      ((show Wform σ from e3uWact σ e g v : Wform σ) : Cube F) =
        rho F (g : GL (Fin 6) F) ((show Wform σ from v : Wform σ) : Cube F) :=
    fun g v => CFSG.RankThree.GF2n.Smith81.e3uWactEquiv_apply σ e g v
  rw [Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  obtain ⟨v1, hv1⟩ := LinearMap.mem_range.mp hw1
  obtain ⟨v2, hv2⟩ := LinearMap.mem_range.mp hw2
  have hv1' : e3uWact σ e gx v1 - v1 = w := hv1
  have hv2' : e3uWact σ e gy v2 - v2 = w := hv2
  have hmx : ((show Wform σ from w : Wform σ) : Cube F) ∈
      LinearMap.range (rho F (gx : GL (Fin 6) F) - 1) := by
    refine LinearMap.mem_range.mpr ⟨((show Wform σ from v1 : Wform σ) : Cube F), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, ← hX gx v1, ← hv1'] <;> exact rfl
  have hmy : ((show Wform σ from w : Wform σ) : Cube F) ∈
      LinearMap.range (rho F (gy : GL (Fin 6) F) - 1) := by
    refine LinearMap.mem_range.mpr ⟨((show Wform σ from v2 : Wform σ) : Cube F), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, ← hX gy v2, ← hv2'] <;> exact rfl
  have hmem : ((show Wform σ from w : Wform σ) : Cube F) ∈
      LinearMap.range (rho F (gx : GL (Fin 6) F) - 1) ⊓
        LinearMap.range (rho F (gy : GL (Fin 6) F) - 1) :=
    Submodule.mem_inf.mpr ⟨hmx, hmy⟩
  rw [key, Submodule.mem_bot] at hmem
  exact Submodule.coe_eq_zero.mp hmem

end CFSG.RankThree.GF2n.Smith81.RootGenU

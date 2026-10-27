module

public import CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open

theorem burnsideF4m_conj_mem_centerOf_perfectCore {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup Y} {p c : Y} (hp : p ∈ H) (hc : c ∈ centerOf (perfectCore H)) :
    p * c * p⁻¹ ∈ centerOf (perfectCore H) := by
  have hcore : p * c * p⁻¹ ∈ perfectCore H :=
    (perfectCore_normal H).conj_mem ⟨c, perfectCore_le H hc.1⟩ hc.1 ⟨p, hp⟩
  refine ⟨hcore, ?_⟩
  show p * c * p⁻¹ ∈ Subgroup.centralizer ((perfectCore H : Subgroup Y) : Set Y)
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : p⁻¹ * d * p ∈ perfectCore H := by
    have h1 : p⁻¹ * d * p⁻¹⁻¹ ∈ perfectCore H :=
      (perfectCore_normal H).conj_mem ⟨d, perfectCore_le H hd⟩ hd ⟨p⁻¹, H.inv_mem hp⟩
    rwa [inv_inv] at h1
  have e := Subgroup.mem_centralizer_iff.1 hc.2 _ hd'
  calc d * (p * c * p⁻¹) = p * ((p⁻¹ * d * p) * c) * p⁻¹ := by group
    _ = p * (c * (p⁻¹ * d * p)) * p⁻¹ := by rw [e]
    _ = (p * c * p⁻¹) * d := by group

theorem burnsideF4m_sp_center_le {X : Type} [Group X] [Finite X] {U P : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUP : U ≤ P)
    (hZU : centerOf (perfectCore P) ≤ centerOf U) :
    centerOf (perfectCore P) ≤ ctr (oPPrime 2 P) := by
  set Z := centerOf (perfectCore P) with hZ
  have hZn : ∀ p ∈ P, ∀ z ∈ Z, p * z * p⁻¹ ∈ Z := fun p hp z hz =>
    burnsideF4m_conj_mem_centerOf_perfectCore hp hz
  set N : Subgroup X := P ⊓ Subgroup.centralizer (Z : Set X) with hN
  have hNP : N ≤ P := inf_le_left
  have hPN : P ≤ Subgroup.normalizer (N : Set X) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxP, hxC⟩
      refine ⟨P.mul_mem (P.mul_mem hp hxP) (P.inv_mem hp),
        Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : p⁻¹ * z * p ∈ Z := by
        have := hZn p⁻¹ (P.inv_mem hp) z hz
        rwa [inv_inv] at this
      have e := Subgroup.mem_centralizer_iff.mp hxC _ hz'
      calc z * (p * x * p⁻¹) = p * ((p⁻¹ * z * p) * x) * p⁻¹ := by group
        _ = p * (x * (p⁻¹ * z * p)) * p⁻¹ := by rw [e]
        _ = p * x * p⁻¹ * z := by group
    · rintro ⟨hxP, hxC⟩
      have hx : x = p⁻¹ * (p * x * p⁻¹) * p := by group
      refine ⟨by rw [hx]; exact P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp,
        Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : p * z * p⁻¹ ∈ Z := hZn p hp z hz
      have e := Subgroup.mem_centralizer_iff.mp hxC _ hz'
      calc z * x = p⁻¹ * ((p * z * p⁻¹) * (p * x * p⁻¹)) * p := by group
        _ = p⁻¹ * ((p * x * p⁻¹) * (p * z * p⁻¹)) * p := by rw [e]
        _ = x * z := by group
  have hUN : U ≤ N := by
    intro u hu
    refine ⟨hUP hu, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hZU hz).2 u hu).symm
  have hOP : oPPrime 2 P ≤ N := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyP, k, hk⟩
    have hy : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    exact CFSG.Quasithin.H13.U4Par.le_of_isPGroup_of_sylow_le hNP hPN hUN hU
      (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hy)
      ((Subgroup.zpowers_le (H := P)).mpr hyP) (Subgroup.mem_zpowers y)
  intro z hz
  have hzU : z ∈ U := (hZU hz).1
  obtain ⟨k, hk⟩ := hU.2.1 ⟨z, hzU⟩
  have hk' : z ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨burnsideF4gU4Inv_mem_oPPrime (hUP hzU) hk', Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hOP hg).2 z hz).symm

end CFSG.ASVolI

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open

open scoped commutatorElement

namespace SpOut2

section TorusU

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideF4m_sp_dElt_mul_uElt (l : Fˣ) (a b c d : F) :
    dElt l * uElt a b c d = uElt ((l : F) * a) ((l : F) * b) ((l : F) ^ 2 * c) d * dElt l :=
  mat_ext (by
    rw [mat_mul, mat_mul, mat_dElt]
    show dMat l * uMat a b c d = uMat ((l : F) * a) ((l : F) * b) ((l : F) ^ 2 * c) d * dMat l
    have hl : (l : F) * ((l⁻¹ : Fˣ) : F) = 1 := Units.mul_inv l
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dMat, uMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind)

theorem burnsideF4m_sp_dElt_mem_normalizer (l : Fˣ) :
    dElt l ∈ Subgroup.normalizer (antiUnipotent F : Set (antiSp F)) := by
  have key : ∀ (m : Fˣ), ∀ x ∈ antiUnipotent F, dElt m * x * (dElt m)⁻¹ ∈ antiUnipotent F := by
    rintro m _ ⟨a, b, c, d, rfl⟩
    rw [burnsideF4m_sp_dElt_mul_uElt, mul_inv_cancel_right]
    exact ⟨_, _, _, _, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key l x hx, fun hx => ?_⟩
  have hinv : (dElt l)⁻¹ = dElt l⁻¹ := by
    rw [← dHom₂_apply, ← dHom₂_apply, map_inv]
  have := key l⁻¹ _ hx
  rw [← hinv, inv_inv] at this
  simpa [mul_assoc] using this

theorem burnsideF4m_sp_dHom_one (l : Fˣ) : dHom F (axisOf 1) l = dElt l := rfl

theorem burnsideF4m_sp_frob_eq_one_of_torusU {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (s : ℕ) {u : antiSp F} (hu : u ∈ antiUnipotent F)
    (h : ∀ μ : Fˣ, dHom F (axisOf 1) μ * u * ((frobAut F ^ s) (dHom F (axisOf 1) μ))⁻¹ * u⁻¹ ∈
      antiUnipotent F) : frobAut F ^ s = 1 := by
  have hS := hS_axis hn hF 1
  have hcen : ∀ w ∈ antiUnipotent F, ∀ x : F,
      w * rootCoord F (axisOf 1) x = rootCoord F (axisOf 1) x * w := by
    intro w hw x
    have hz : rootCoord F (axisOf 1) x ∈ centerOf (antiUnipotent F) :=
      rootU_le_center 1 (hS.coord_mem x)
    exact (mem_centerOf_iff.mp hz).2 w hw
  have key : ∀ μ : Fˣ, μ ^ 2 ^ s = μ := by
    intro μ
    set ν : Fˣ := μ ^ 2 ^ s with hν
    set D₁ := dHom F (axisOf 1) μ with hD₁
    set D₂ := dHom F (axisOf 1) ν with hD₂
    have hw := h μ
    rw [frobAut_pow_dHom] at hw
    set w := D₁ * u * D₂⁻¹ * u⁻¹ with hwdef
    have hz1 : rootCoord F (axisOf 1) 1 * w = w * rootCoord F (axisOf 1) 1 :=
      (hcen w hw 1).symm
    have h1 : u⁻¹ * rootCoord F (axisOf 1) 1 * u = rootCoord F (axisOf 1) 1 := by
      calc u⁻¹ * rootCoord F (axisOf 1) 1 * u = u⁻¹ * (rootCoord F (axisOf 1) 1 * u) :=
            mul_assoc _ _ _
        _ = u⁻¹ * (u * rootCoord F (axisOf 1) 1) := by rw [hcen u hu 1]
        _ = rootCoord F (axisOf 1) 1 := inv_mul_cancel_left u _
    have h2 : D₂⁻¹ * rootCoord F (axisOf 1) 1 * D₂ =
        rootCoord F (axisOf 1) (((ν⁻¹ : Fˣ) : F) ^ 2 * 1) := by
      have := hS.d_coord ν⁻¹ 1
      rwa [map_inv, inv_inv] at this
    set e : F := ((ν⁻¹ : Fˣ) : F) ^ 2 * 1 with he
    have h3 : u * rootCoord F (axisOf 1) e * u⁻¹ = rootCoord F (axisOf 1) e := by
      rw [hcen u hu e, mul_inv_cancel_right]
    have h4 : D₁ * rootCoord F (axisOf 1) e * D₁⁻¹ =
        rootCoord F (axisOf 1) ((μ : F) ^ 2 * e) := hS.d_coord μ e
    have h5 : w * rootCoord F (axisOf 1) 1 * w⁻¹ = rootCoord F (axisOf 1) ((μ : F) ^ 2 * e) := by
      calc w * rootCoord F (axisOf 1) 1 * w⁻¹
          = D₁ * (u * (D₂⁻¹ * (u⁻¹ * rootCoord F (axisOf 1) 1 * u) * D₂) * u⁻¹) * D₁⁻¹ := by
            rw [hwdef]; group
        _ = rootCoord F (axisOf 1) ((μ : F) ^ 2 * e) := by rw [h1, h2, h3, h4]
    have h6 : w * rootCoord F (axisOf 1) 1 * w⁻¹ = rootCoord F (axisOf 1) 1 := by
      rw [← hz1, mul_inv_cancel_right]
    have h7 : (μ : F) ^ 2 * e = 1 :=
      rootCoord_injective' (axisOf 1) (h5.symm.trans h6)
    have h8 : ((μ : F) * ((ν⁻¹ : Fˣ) : F)) ^ 2 = 1 := by
      rw [mul_pow]
      simpa [he] using h7
    have h9 := eq_of_sq_eq_one h8
    have h10 : (μ : F) = (ν : F) := by
      rw [Units.val_inv_eq_inv_val] at h9
      exact (mul_inv_eq_one₀ ν.ne_zero).mp h9
    exact (Units.ext h10).symm
  apply frobAut_pow_eq_one_of_fix
  intro x
  by_cases hx : x = 0
  · rw [hx]
    exact zero_pow (pow_ne_zero _ two_ne_zero)
  · have := congrArg (fun y : Fˣ => (y : F)) (key (Units.mk0 x hx))
    simpa using this

end TorusU

end SpOut2

end CFSG.Quasithin.H13.F431

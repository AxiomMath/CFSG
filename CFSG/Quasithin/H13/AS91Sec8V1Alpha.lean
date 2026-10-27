module

public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import CFSG.Quasithin.H13.AS91Sec5HM22
public import CFSG.Quasithin.H13.AS91Sec8HPi
public import CFSG.Quasithin.H13.AS91Sec8HGeom
public import TauCeti.GroupTheory.Index.Two

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

theorem zmod2_mul_eq_one_of_ne_one {a b : Multiplicative (ZMod 2)} (ha : a ≠ 1) (hb : b ≠ 1) :
    a * b = 1 := by
  revert a b
  decide

@[expose] def twistHom {M : Type*} [Group M] (χ : M →* Multiplicative (ZMod 2)) (c : M)
    (hc : c * c = 1) (hcχ : χ c = 1) (hcent : ∀ x : M, c * x = x * c) : M →* M where
  toFun x := x * (if χ x = 1 then 1 else c)
  map_one' := by simp
  map_mul' x y := by
    by_cases hx : χ x = 1 <;> by_cases hy : χ y = 1
    · have hxy : χ (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
      simp [hx, hy, hxy]
    · have hxy : χ (x * y) ≠ 1 := by rw [map_mul, hx, one_mul]; exact hy
      simp only [hx, hy, hxy, if_true, if_false, mul_one]
      rw [mul_assoc]
    · have hxy : χ (x * y) ≠ 1 := by rw [map_mul, hy, mul_one]; exact hx
      simp only [hx, hy, hxy, if_true, if_false, mul_one]
      rw [mul_assoc x c y, hcent y, ← mul_assoc x y c]
    · have hxy : χ (x * y) = 1 := by rw [map_mul, zmod2_mul_eq_one_of_ne_one hx hy]
      simp only [hx, hy, hxy, if_true, if_false, mul_one]
      rw [mul_assoc x c (y * c), ← mul_assoc c y c, hcent y, mul_assoc y c c, hc, mul_one]

theorem twistHom_apply {M : Type*} [Group M] (χ : M →* Multiplicative (ZMod 2)) (c : M)
    (hc : c * c = 1) (hcχ : χ c = 1) (hcent : ∀ x : M, c * x = x * c) (x : M) :
    twistHom χ c hc hcχ hcent x = x * (if χ x = 1 then 1 else c) := rfl

theorem twistHom_chi_eq_one_iff {M : Type*} [Group M] (χ : M →* Multiplicative (ZMod 2)) (c : M)
    (hc : c * c = 1) (hcχ : χ c = 1) (hcent : ∀ x : M, c * x = x * c) (x : M) :
    χ (twistHom χ c hc hcχ hcent x) = 1 ↔ χ x = 1 := by
  rw [twistHom_apply]
  by_cases hx : χ x = 1
  · simp [hx]
  · rw [if_neg hx, map_mul, hcχ, mul_one]

theorem twistHom_comm {M : Type*} [Group M] (χ : M →* Multiplicative (ZMod 2)) (c : M)
    (hc : c * c = 1) (hcχ : χ c = 1) (hcent : ∀ x : M, c * x = x * c)
    (ρ : M →* M) (hρc : ρ c = c) (hρχ : ∀ x, χ (ρ x) = χ x) (x : M) :
    twistHom χ c hc hcχ hcent (ρ x) = ρ (twistHom χ c hc hcχ hcent x) := by
  rw [twistHom_apply, twistHom_apply, map_mul, hρχ]
  split_ifs <;> simp [hρc]

theorem twistHom_involutive {M : Type*} [Group M] (χ : M →* Multiplicative (ZMod 2)) (c : M)
    (hc : c * c = 1) (hcχ : χ c = 1) (hcent : ∀ x : M, c * x = x * c) :
    Function.Involutive (twistHom χ c hc hcχ hcent) := by
  intro x
  have hiff := twistHom_chi_eq_one_iff χ c hc hcχ hcent x
  conv_lhs => rw [twistHom_apply]
  by_cases hx : χ x = 1
  · rw [if_pos (hiff.mpr hx), mul_one]
    conv_lhs => rw [twistHom_apply]
    rw [if_pos hx, mul_one]
  · rw [if_neg (fun h => hx (hiff.mp h))]
    conv_lhs => rw [twistHom_apply]
    rw [if_neg hx, mul_assoc, hc, mul_one]

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] noncomputable def toddToG3 (r : ResM24T c) : W11 →* ↥c.G3 :=
  (Subgroup.inclusion c.E_le_G3).comp r.todd.symm.toMonoidHom

theorem toddToG3_conj (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (h : ↥(c.G3 ⊓ c.G1)) (w : W11) :
    toddToG3 c r (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) w) =
      Subgroup.inclusion inf_le_left h * toddToG3 c r w *
        (Subgroup.inclusion inf_le_left h)⁻¹ := by
  apply Subtype.ext
  have ht := c.todd_conj_phiS r hU h (r.todd.symm w)
  rw [r.todd.apply_symm_apply] at ht
  have hsy : r.todd.symm (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) w) =
      ⟨(h : G) * ((r.todd.symm w : ↥c.E) : G) * (h : G)⁻¹,
        c.conj_mem_E (Subgroup.inclusion inf_le_right h) (r.todd.symm w).2⟩ := by
    rw [← ht, r.todd.symm_apply_apply]
  simpa [toddToG3] using congrArg Subtype.val hsy

theorem rho11_phiS_sextClass
    (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (h : ↥(c.G3 ⊓ c.G1)) :
    rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h)
      (M24G.sextClass (M24G.sextFin 0)) = M24G.sextClass (M24G.sextFin 0) := by
  have hzw' : r.todd ⟨z, c.z_mem_E⟩ = M24G.sextClass (M24G.sextFin 0) := by
    rw [ResM24T.todd_z r, hU]
  have hconj : (h : G) * z * (h : G)⁻¹ = z := by
    have hh : (h : G) ∈ c.G3 := (Subgroup.mem_inf.mp h.2).1
    calc (h : G) * z * (h : G)⁻¹
        = (h : G) * ((h : G)⁻¹ * z * (h : G)) * (h : G)⁻¹ := by rw [c.G3_comm_z hh]
      _ = z := by group
  rw [← hzw', ← c.todd_conj_phiS r hU h ⟨z, c.z_mem_E⟩]
  exact congrArg r.todd (Subtype.ext hconj)

theorem E_le_of_indexTwo
    (hEnd : M24G.SextStabEndScalar) (hJ : HypJ4 G z)
    (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) {N : Subgroup G}
    (hNle : N ≤ c.G3) (hQN : Q z ≤ N) (hidx : N.relIndex c.G3 = 2) : c.E ≤ N := by
  classical
  let K : Subgroup ↥c.G3 := N.subgroupOf c.G3
  have hK : K.index = 2 := by simpa [Subgroup.relIndex] using hidx
  let χH : ↥c.G3 →* Multiplicative (ZMod 2) := Subgroup.indexTwoCharacter K hK
  have hzN : z ∈ N := hQN c.toLoc41.z_mem_Q
  have hzG3 : z ∈ c.G3 := hNle hzN
  let zH : ↥c.G3 := ⟨z, hzG3⟩
  have hzK : zH ∈ K := Subgroup.mem_subgroupOf.mpr hzN
  have hzχ : χH zH = 1 := (Subgroup.indexTwoCharacter_eq_one_iff (N := K) hK (γ := zH)).mpr hzK
  have hz2 : zH * zH = 1 :=
    Subtype.ext (by
      simpa [zH] using (mul_eq_one_iff_eq_inv.mpr
        (inv_eq_self_of_orderOf_eq_two hJ.orderOf_z).symm))
  have hcent : ∀ x : ↥c.G3, zH * x = x * zH := by
    intro x
    apply Subtype.ext
    have h := c.G3_comm_z x.2
    calc z * (x : G) = (x : G) * ((x : G)⁻¹ * z * (x : G)) := by group
      _ = (x : G) * z := by rw [h]
  let wz : W11 := M24G.sextClass (M24G.sextFin 0)
  have hzw : r.todd.symm wz = ⟨z, c.z_mem_E⟩ := by
    rw [show wz = r.todd ⟨z, c.z_mem_E⟩ from by rw [ResM24T.todd_z r, hU]]
    exact r.todd.symm_apply_apply _
  have hφz : toddToG3 c r wz = zH := by
    apply Subtype.ext
    simp [toddToG3, hzw, zH]
  have hεwz : (χH.comp (toddToG3 c r)) wz = 1 := by
    rw [show (χH.comp (toddToG3 c r)) wz = χH (toddToG3 c r wz) from rfl, hφz, hzχ]
  let fHom : W11 →* W11 :=
    twistHom (χH.comp (toddToG3 c r)) wz (M24G.W11_mul_self wz) hεwz (fun x => mul_comm wz x)
  have hinv : Function.Involutive fHom :=
    twistHom_involutive (χH.comp (toddToG3 c r)) wz _ hεwz _
  set f : W11 ≃* W11 := MulEquiv.ofBijective fHom hinv.bijective with hf_def
  have hf_apply : ∀ w : W11, f w = w * (if (χH.comp (toddToG3 c r)) w = 1 then 1 else wz) := by
    intro w
    rw [hf_def]
    rfl
  have hf_comm : ∀ (s : ↥M24G.sextStab) (w : W11),
      f (rho11 M24G.sextStab M24G.sextStab_le s w) =
        rho11 M24G.sextStab M24G.sextStab_le s (f w) := by
    intro s w
    obtain ⟨h, rfl⟩ := c.phiS_surjective r hU s
    have hρχ : ∀ x : W11, (χH.comp (toddToG3 c r))
        (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) x) =
          (χH.comp (toddToG3 c r)) x := by
      intro x
      show χH (toddToG3 c r (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) x)) =
        χH (toddToG3 c r x)
      rw [toddToG3_conj c r hU h x, map_mul, map_mul, map_inv]
      exact mul_inv_cancel_comm _ _
    have htw := twistHom_comm (χH.comp (toddToG3 c r)) wz (M24G.W11_mul_self wz) hεwz
      (fun x => mul_comm wz x)
      (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h)).toMonoidHom
      (rho11_phiS_sextClass c r hU h) hρχ w
    rw [hf_def]
    change fHom (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) w) =
      rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) (fHom w)
    exact htw
  have hfix : ∀ w : W11, f w = w := hEnd f hf_comm
  intro e he
  let w : W11 := r.todd ⟨e, he⟩
  have hfw : f w = w := hfix w
  have hA : (if (χH.comp (toddToG3 c r)) w = 1 then 1 else wz) = 1 := by
    have h2 := congrArg (fun x => w⁻¹ * x) hfw
    rw [hf_apply] at h2
    rw [inv_eq_of_mul_eq_one_right (M24G.W11_mul_self w)] at h2
    rw [← mul_assoc, M24G.W11_mul_self w, one_mul] at h2
    exact h2
  have hε1 : (χH.comp (toddToG3 c r)) w = 1 := by
    by_contra hne
    have hwz : wz = 1 := by
      rw [if_neg hne] at hA
      exact hA
    exact M24G.sextClass_ne_one (M24G.isSextet_sextFin (q := 0) (by norm_num))
      (by simpa [wz] using hwz)
  have hKmem : toddToG3 c r w ∈ K :=
    (Subgroup.indexTwoCharacter_eq_one_iff (N := K) hK (γ := toddToG3 c r w)).mp hε1
  have hNmem : (toddToG3 c r w : G) ∈ N := Subgroup.mem_subgroupOf.mp hKmem
  have hval : (toddToG3 c r w : G) = e := by
    simp [toddToG3, w]
  simpa [hval] using hNmem

theorem not_inf_le_of_indexTwo
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    (hJ : HypJ4 G z) (r : ResM24T c) {N : Subgroup G} (hidx : N.relIndex c.G3 = 2) :
    ¬ (c.G3 ⊓ c.G1 ≤ N) := by
  intro hle
  have h77 : (c.G3 ⊓ c.G1).relIndex c.G3 = 77 := by
    rw [Subgroup.inf_relIndex_left, ← c.ncard_ptsP_eq_relIndex]
    simpa [Loc49.ptsP, objOf, CInc] using c.ncard_ptsP r.toResM24 hLU hG2 hJ
  have hdvd := Subgroup.relIndex_dvd_of_le_left c.G3 hle
  rw [hidx, h77] at hdvd
  norm_num at hdvd

theorem hasAlphaTwist (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    (hEnd : M24G.SextStabEndScalar) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) :
    c.HasAlphaTwist r hU := by
  classical
  obtain ⟨N, -, hNle, hQXN, hidx, -, -, -, -⟩ := Loc41.exists_linear_M22 hJ c.toLoc41
  have hQN : Q z ≤ N := le_sup_left.trans hQXN
  have hEN : c.E ≤ N := c.E_le_of_indexTwo hEnd hJ r hU hNle hQN hidx
  have hIN : ¬ (c.G3 ⊓ c.G1 ≤ N) := c.not_inf_le_of_indexTwo hLU hG2 hJ r hidx
  let K : Subgroup ↥c.G3 := N.subgroupOf c.G3
  have hK : K.index = 2 := by simpa [Subgroup.relIndex] using hidx
  let χH : ↥c.G3 →* Multiplicative (ZMod 2) := Subgroup.indexTwoCharacter K hK
  have hzN : z ∈ N := hQN c.toLoc41.z_mem_Q
  have hzG3 : z ∈ c.G3 := hNle hzN
  let zH : ↥c.G3 := ⟨z, hzG3⟩
  have hzK : zH ∈ K := Subgroup.mem_subgroupOf.mpr hzN
  have hzχ : χH zH = 1 := (Subgroup.indexTwoCharacter_eq_one_iff (N := K) hK (γ := zH)).mpr hzK
  have hz2 : zH * zH = 1 :=
    Subtype.ext (by
      simpa [zH] using (mul_eq_one_iff_eq_inv.mpr
        (inv_eq_self_of_orderOf_eq_two hJ.orderOf_z).symm))
  have hcent : ∀ x : ↥c.G3, zH * x = x * zH := by
    intro x
    apply Subtype.ext
    have h := c.G3_comm_z x.2
    calc z * (x : G) = (x : G) * ((x : G)⁻¹ * z * (x : G)) := by group
      _ = (x : G) * z := by rw [h]
  let α : ↥c.G3 ≃* ↥c.G3 :=
    MulEquiv.ofBijective (twistHom χH zH hz2 hzχ hcent)
      (twistHom_involutive χH zH hz2 hzχ hcent).bijective
  have hαα : ∀ h : ↥c.G3, α (α h) = h := by
    intro h
    show twistHom χH zH hz2 hzχ hcent (twistHom χH zH hz2 hzχ hcent h) = h
    exact twistHom_involutive χH zH hz2 hzχ hcent h
  have hα_apply : ∀ h : ↥c.G3,
      ((α h : ↥c.G3) : G) = (h : G) * (if χH h = 1 then (1 : G) else (zH : G)) := by
    intro h
    show ((twistHom χH zH hz2 hzχ hcent h : ↥c.G3) : G) = _
    rw [twistHom_apply]
    by_cases hχ : χH h = 1 <;> simp [hχ]
  have hker : (c.phiS r hU).ker ≤
      (χH.comp (Subgroup.inclusion inf_le_left)).ker := by
    intro x hx
    let xI : ↥(c.G3 ⊓ c.G1) := x
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxE : (xI : G) ∈ c.E := (c.phiS_eq_one_iff r hU xI).mp hx
    have hxN : (xI : G) ∈ N := hEN hxE
    have hxK : (Subgroup.inclusion inf_le_left xI : ↥c.G3) ∈ K :=
      Subgroup.mem_subgroupOf.mpr hxN
    exact (Subgroup.indexTwoCharacter_eq_one_iff (N := K) hK).mpr hxK
  let χ : ↥M24G.sextStab →* Multiplicative (ZMod 2) :=
    MonoidHom.liftOfSurjective (c.phiS r hU) (c.phiS_surjective r hU)
      ⟨χH.comp (Subgroup.inclusion inf_le_left), hker⟩
  have hχφ : ∀ h : ↥(c.G3 ⊓ c.G1),
      χ (c.phiS r hU h) = χH (Subgroup.inclusion inf_le_left h) := by
    intro h
    simp [χ, MonoidHom.liftOfSurjective]
  have hχne : χ ≠ 1 := by
    intro hχ
    apply hIN
    intro x hx
    let xI : ↥(c.G3 ⊓ c.G1) := ⟨x, hx⟩
    have hgI : χH (Subgroup.inclusion inf_le_left xI) = 1 := by
      simpa [hχ] using (hχφ xI).symm
    have hxK : (Subgroup.inclusion inf_le_left xI : ↥c.G3) ∈ K :=
      (Subgroup.indexTwoCharacter_eq_one_iff (N := K) hK).mp hgI
    exact Subgroup.mem_subgroupOf.mp hxK
  have hpres : ∀ h : ↥c.G3, (h : G) ∈ c.G1 ↔ ((α h : ↥c.G3) : G) ∈ c.G1 := by
    have hfwd : ∀ h : ↥c.G3, (h : G) ∈ c.G1 → ((α h : ↥c.G3) : G) ∈ c.G1 := by
      intro h hh
      rw [hα_apply h]
      apply mul_mem hh
      by_cases hχ : χH h = 1
      · rw [if_pos hχ]
        exact c.G1.one_mem
      · rw [if_neg hχ]
        exact c.E_le_G1 c.z_mem_E
    intro h
    constructor
    · exact hfwd h
    · intro hh
      have h2 := hfwd (α h) hh
      rwa [hαα h] at h2
  have hformula : ∀ h : ↥(c.G3 ⊓ c.G1),
      ((α (Subgroup.inclusion inf_le_left h) : ↥c.G3) : G) =
        (h : G) * (r.todd.symm
          (if χ (c.phiS r hU h) = 1 then 1 else M24G.sextClass (M24G.sextFin 0)) : G) := by
    intro h
    have hχh : χH (Subgroup.inclusion inf_le_left h) = χ (c.phiS r hU h) := (hχφ h).symm
    have hzw : r.todd.symm (M24G.sextClass (M24G.sextFin 0)) = ⟨z, c.z_mem_E⟩ := by
      rw [show M24G.sextClass (M24G.sextFin 0) = r.todd ⟨z, c.z_mem_E⟩ from by
        rw [ResM24T.todd_z r, hU]]
      exact r.todd.symm_apply_apply _
    rw [hα_apply (Subgroup.inclusion inf_le_left h), hχh]
    by_cases hc : χ (c.phiS r hU h) = 1
    · rw [if_pos hc, if_pos hc, mul_one]
      rw [show r.todd.symm 1 = 1 from map_one r.todd.symm]
      simp
    · rw [if_neg hc, if_neg hc]
      rw [hzw]
      simp [zH]
  exact ⟨χ, α, hχne, hpres, hformula⟩

end Loc49

end CFSG.Quasithin.H13.AS91

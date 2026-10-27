module

public import CFSG.Sporadic.Co2Smith.GlWFactsB

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Phi

variable {G : Type} [Group G] {z : G}
  (φ : centralizer ({z} : Set G) ≃* Cz)

@[expose] noncomputable def phiH : Cz →* G where
  toFun u := (φ.symm u : G)
  map_one' := by rw [map_one, Subgroup.coe_one]
  map_mul' u v := by rw [map_mul, Subgroup.coe_mul]

theorem phiH_apply (u : Cz) : phiH φ u = (φ.symm u : G) := rfl

theorem phiH_injective : Function.Injective (phiH φ) :=
  Subtype.val_injective.comp φ.symm.injective

theorem phiH_comm_iff {u v : Cz} :
    phiH φ u * phiH φ v = phiH φ v * phiH φ u ↔ u * v = v * u := by
  rw [← map_mul, ← map_mul]
  exact (phiH_injective φ).eq_iff

theorem phiH_apply_symm (g : G) (hg : g ∈ centralizer ({z} : Set G)) :
    phiH φ (φ ⟨g, hg⟩) = g := by
  rw [phiH_apply, MulEquiv.symm_apply_apply]

@[expose] def IsNJChart (ψ : normalizer (Jc : Set K) →* G) : Prop :=
  ∀ (x : normalizer (Jc : Set K)) (hx : (x : K) ∈ Cz), ψ x = (φ.symm ⟨x, hx⟩ : G)

end Phi

section Delta


theorem lWord_w7_pair {k : ℕ} (hk : k < 7) : w7Letters.elt k * w7Letters.elt k = 1 := by
  have hD : [k, k] ∈ Native.glWRelsD :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have hmem : [k, k] ∈ Native.glWRelsN :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hD))
  have h := lWord_w7_rel hmem
  simpa [lWord] using h

theorem δ1hK_mul_self' : δ1hK * δ1hK = 1 := by
  have h := lWord_w7_pair (k := 6) (by norm_num)
  rwa [w7Letters_elt_six] at h

theorem δ1hK_inv : δ1hK⁻¹ = δ1hK := inv_eq_of_mul_eq_one_right δ1hK_mul_self'

theorem genLetters_mul_self (k : ℕ) : genLetters.elt k * genLetters.elt k = 1 := by
  by_cases hk : k < 6
  · have h := lWord_w7_pair (k := k) (by omega)
    rwa [w7Letters_elt_lt hk] at h
  · show (if k = 0 then z0 else if k < 6 then tK (k - 1) else 1) *
      (if k = 0 then z0 else if k < 6 then tK (k - 1) else 1) = 1
    rw [ite_eq_right (by omega), ite_eq_right hk, mul_one]

@[expose] noncomputable def δN : normalizer (Jc : Set K) := ⟨δ1hK, δ1hK_mem_N⟩

theorem x25K_eq_conj : x25K = δ1hK * z0 * δ1hK⁻¹ := by
  rw [δ1hK_inv, x25K, x16K_eq]

theorem conj_δ1hK_mem_Cz {y : K} (hy : y * x25K = x25K * y) : δ1hK * y * δ1hK⁻¹ ∈ Cz := by
  apply mem_Cz_of_comm
  rw [x25K_eq_conj] at hy
  calc δ1hK * y * δ1hK⁻¹ * z0 = δ1hK * (y * (δ1hK⁻¹ * z0 * δ1hK)) * δ1hK⁻¹ := by group
    _ = δ1hK * (y * (δ1hK * z0 * δ1hK⁻¹)) * δ1hK⁻¹ := by rw [δ1hK_inv]
    _ = δ1hK * ((δ1hK * z0 * δ1hK⁻¹) * y) * δ1hK⁻¹ := by rw [hy]
    _ = z0 * (δ1hK * y * δ1hK⁻¹) := by rw [δ1hK_inv]; group; rw [δ1hK_mul_self']; group

theorem conj_δ1hK_mem_Jc {x : K} (hx : x ∈ Jc) : δ1hK * x * δ1hK⁻¹ ∈ Jc :=
  (mem_normalizer_iff.1 δ1hK_mem_N x).1 hx

theorem jcB_zero : jcB 0 = z0 := by
  have h : Native.glNJB[0]! = [0] := rfl
  rw [← x16K_eq, jcB, h, x16K]

theorem z0_mem_Jc : z0 ∈ Jc := jcB_zero ▸ jcB_mem (by norm_num)

theorem x25K_mem_Jc : x25K ∈ Jc := by
  rw [x25K_eq_conj]
  exact conj_δ1hK_mem_Jc z0_mem_Jc

theorem x25K_mem_CzJ : x25K ∈ Cz := Jc_le_Cz x25K_mem_Jc

theorem δ1hK_conj_x25K : δ1hK * x25K * δ1hK⁻¹ = z0 := by
  rw [x25K_eq_conj, δ1hK_inv, show δ1hK * (δ1hK * z0 * δ1hK) * δ1hK =
    (δ1hK * δ1hK) * z0 * (δ1hK * δ1hK) by group, δ1hK_mul_self', one_mul, mul_one]

theorem δ1hK_conj_of_comm {y : K} (hy : δ1hK * y = y * δ1hK) : δ1hK * y * δ1hK⁻¹ = y := by
  rw [hy, mul_inv_cancel_right]

theorem hwKi_conj_of_comm {y : K} (hy : hwK * y = y * hwK) : hwKi * y * hwK = y := by
  rw [hwKi_eq, mul_assoc, ← hy, inv_mul_cancel_left]

end Delta

section Chart

variable {G : Type} [Group G]
  {z : G}

@[expose] noncomputable def dG (ψ : normalizer (Jc : Set K) →* G) : G := ψ δN

theorem dG_mul_self (ψ : normalizer (Jc : Set K) →* G) : dG ψ * dG ψ = 1 := by
  rw [dG, ← map_mul, show δN * δN = 1 from Subtype.ext δ1hK_mul_self', map_one]

theorem dG_inv (ψ : normalizer (Jc : Set K) →* G) : (dG ψ)⁻¹ = dG ψ :=
  inv_eq_of_mul_eq_one_right (dG_mul_self ψ)

variable {φ : centralizer ({z} : Set G) ≃* Cz} {ψ : normalizer (Jc : Set K) →* G}

theorem dG_conj (hψ : IsNJChart φ ψ) (u : Cz) (hu : (u : K) ∈ normalizer (Jc : Set K))
    (hv : δ1hK * u * δ1hK⁻¹ ∈ Cz) :
    dG ψ * phiH φ u * (dG ψ)⁻¹ = phiH φ ⟨δ1hK * u * δ1hK⁻¹, hv⟩ := by
  have hN : δ1hK * u * δ1hK⁻¹ ∈ normalizer (Jc : Set K) :=
    mul_mem (mul_mem δ1hK_mem_N hu) (inv_mem δ1hK_mem_N)
  have h1 : phiH φ u = ψ ⟨u, hu⟩ := (hψ ⟨u, hu⟩ u.2).symm
  have h2 : phiH φ ⟨δ1hK * u * δ1hK⁻¹, hv⟩ = ψ ⟨_, hN⟩ := (hψ ⟨_, hN⟩ hv).symm
  rw [h1, h2, dG, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext rfl)

end Chart

section Words


@[expose] noncomputable def gwLet (k : ℕ) : Cz :=
  ⟨genLetters.elt k, (mem_inf.1 (genLetters_mem_D k)).2⟩

@[expose] noncomputable def gwWord (w : List ℕ) : Cz := (w.map gwLet).prod

theorem gwWord_nil : gwWord [] = 1 := by rw [gwWord, List.map_nil, List.prod_nil]

theorem gwWord_cons (k : ℕ) (w : List ℕ) : gwWord (k :: w) = gwLet k * gwWord w := by
  rw [gwWord, List.map_cons, List.prod_cons, gwWord]

theorem gwWord_append (w w' : List ℕ) : gwWord (w ++ w') = gwWord w * gwWord w' := by
  rw [gwWord, List.map_append, List.prod_append, gwWord, gwWord]

theorem gwWord_val : ∀ w : List ℕ, (gwWord w : K) = lWord genLetters w
  | [] => by rw [gwWord_nil, lWord, Subgroup.coe_one]
  | k :: w => by rw [gwWord_cons, Subgroup.coe_mul, gwWord_val w, lWord]; rfl

theorem hwK_mem_D : hwK ∈ C0c ⊓ Cz := lWord_gen_mem_D _

theorem hwK_mem_Cz : hwK ∈ Cz := (mem_inf.1 hwK_mem_D).2

theorem gwWord_glWh : (gwWord Native.glWh : K) = hwK := gwWord_val _

theorem gwWord_glWh_rev : (gwWord Native.glWh.reverse : K) = hwKi := gwWord_val _


theorem gwLet_mul_self (k : ℕ) : gwLet k * gwLet k = 1 := Subtype.ext (genLetters_mul_self k)

theorem gwLet_inv (k : ℕ) : (gwLet k)⁻¹ = gwLet k := inv_eq_of_mul_eq_one_right (gwLet_mul_self k)

theorem gwWord_reverse : ∀ w : List ℕ, gwWord w.reverse = (gwWord w)⁻¹
  | [] => by rw [List.reverse_nil, gwWord_nil, inv_one]
  | k :: w => by
    rw [List.reverse_cons, gwWord_append, gwWord_reverse w, gwWord_cons, gwWord_cons, gwWord_nil,
      mul_one, mul_inv_rev, gwLet_inv]

theorem gwWord_eq_one {w : List ℕ} (hw : w ∈ Native.glWRelsN) (hlt : ∀ k ∈ w, k < 6) :
    gwWord w = 1 :=
  Subtype.ext (by rw [gwWord_val, ← lWord_w7_eq_gen hlt, lWord_w7_rel hw, Subgroup.coe_one])

theorem gwWord_E1 {j : ℕ} (hj : j < 4) : (gwWord Native.glWE1w[j]! : K) = e1K j := by
  rw [gwWord_val, e1K_eq hj]

theorem gwWord_E1i {j : ℕ} (hj : j < 4) : (gwWord Native.glWE1iw[j]! : K) = e1iK j := by
  rw [gwWord_val, e1iK_eq hj]

theorem gwWord_D0 : (gwWord Native.glWD0 : K) = δ0hK := by rw [gwWord_val, δ0hK_eq]

end Words

section Transition

variable
  {G : Type} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz}
  {ψ : normalizer (Jc : Set K) →* G}

theorem dG_conj_E1 (hψ : IsNJChart φ ψ) {j : ℕ} (hj : j < 4) :
    dG ψ * phiH φ (gwWord Native.glWE1w[j]!) * (dG ψ)⁻¹ = phiH φ (gwWord Native.glWE1iw[j]!) := by
  have hu : (gwWord Native.glWE1w[j]! : K) ∈ normalizer (Jc : Set K) := by
    rw [gwWord_E1 hj]
    exact Jc_le_N (jcElt_mem _)
  have hd : δ1hK * (gwWord Native.glWE1w[j]! : K) * δ1hK⁻¹ ∈ Cz := by
    rw [gwWord_E1 hj, δ1hK_conj_e1K hj]
    exact Jc_le_Cz (jcElt_mem _)
  rw [dG_conj hψ _ hu hd]
  congr 1
  apply Subtype.ext
  show δ1hK * (gwWord Native.glWE1w[j]! : K) * δ1hK⁻¹ = (gwWord Native.glWE1iw[j]! : K)
  rw [gwWord_E1 hj, δ1hK_conj_e1K hj, gwWord_E1i hj]

variable (φ ψ) in
@[expose] noncomputable def d2G : G :=
  phiH φ (gwWord Native.glWh) * dG ψ * (phiH φ (gwWord Native.glWh))⁻¹

theorem d2G_conj_eq (hψ : IsNJChart φ ψ) (b : Cz) (hb : (b : K) ∈ normalizer (Jc : Set K))
    (hb' : hwKi * b * hwK ∈ normalizer (Jc : Set K)) (hbd : δ1hK * b * δ1hK⁻¹ ∈ Cz) :
    d2G φ ψ * phiH φ b * (d2G φ ψ)⁻¹ = dG ψ * phiH φ b * (dG ψ)⁻¹ := by
  set hC := gwWord Native.glWh with hhC
  have hCv : (hC : K) = hwK := gwWord_glWh
  have hb'v : ((hC⁻¹ * b * hC : Cz) : K) = hwKi * b * hwK := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hCv, hwKi_eq]
  have hb'N : ((hC⁻¹ * b * hC : Cz) : K) ∈ normalizer (Jc : Set K) := hb'v ▸ hb'
  have e1 : δ1hK * hwK⁻¹ = hwK⁻¹ * δ1hK := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hwK_comm_δ1hK, inv_mul_cancel_left]
  have e2 : hwK * δ1hK⁻¹ = δ1hK⁻¹ * hwK := by
    rw [δ1hK_inv]
    exact hwK_comm_δ1hK
  have hcomm : δ1hK * ((hC⁻¹ * b * hC : Cz) : K) * δ1hK⁻¹ =
      hwK⁻¹ * (δ1hK * b * δ1hK⁻¹) * hwK := by
    rw [hb'v, hwKi_eq]
    calc δ1hK * (hwK⁻¹ * (b : K) * hwK) * δ1hK⁻¹ = (δ1hK * hwK⁻¹) * b * (hwK * δ1hK⁻¹) := by group
      _ = (hwK⁻¹ * δ1hK) * b * (δ1hK⁻¹ * hwK) := by rw [e1, e2]
      _ = hwK⁻¹ * (δ1hK * b * δ1hK⁻¹) * hwK := by group
  have hb'd : δ1hK * ((hC⁻¹ * b * hC : Cz) : K) * δ1hK⁻¹ ∈ Cz := by
    rw [hcomm]
    exact Cz.mul_mem (Cz.mul_mem (Cz.inv_mem hwK_mem_Cz) hbd) hwK_mem_Cz
  have k1 := dG_conj hψ (hC⁻¹ * b * hC) hb'N hb'd
  have k2 := dG_conj hψ b hb hbd
  have k3 : hC * ⟨_, hb'd⟩ * hC⁻¹ = (⟨δ1hK * b * δ1hK⁻¹, hbd⟩ : Cz) := by
    apply Subtype.ext
    show (hC : K) * (δ1hK * ((hC⁻¹ * b * hC : Cz) : K) * δ1hK⁻¹) * (hC : K)⁻¹ =
      δ1hK * b * δ1hK⁻¹
    rw [hcomm, hCv]
    group
  rw [k2, ← k3, map_mul, map_mul, ← k1, d2G, ← hhC, map_inv, map_mul, map_mul, map_inv]
  group

theorem cG_comm (hψ : IsNJChart φ ψ) (b : Cz) (hb : (b : K) ∈ normalizer (Jc : Set K))
    (hb' : hwKi * b * hwK ∈ normalizer (Jc : Set K)) (hbd : δ1hK * b * δ1hK⁻¹ ∈ Cz) :
    (dG ψ)⁻¹ * d2G φ ψ * phiH φ b = phiH φ b * ((dG ψ)⁻¹ * d2G φ ψ) := by
  have e := d2G_conj_eq hψ b hb hb' hbd
  calc (dG ψ)⁻¹ * d2G φ ψ * phiH φ b
      = (dG ψ)⁻¹ * (d2G φ ψ * phiH φ b * (d2G φ ψ)⁻¹) * d2G φ ψ := by group
    _ = (dG ψ)⁻¹ * (dG ψ * phiH φ b * (dG ψ)⁻¹) * d2G φ ψ := by rw [e]
    _ = phiH φ b * ((dG ψ)⁻¹ * d2G φ ψ) := by group

end Transition

end CFSG.Sporadic.Co2Smith

module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem burnsideF411a_g2_rel_uv {R : Type*} [CommRing R] :
    ∃ e : R, (e = 1 ∨ e = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![1, 1] x, pinnedX .G2 R ![1, 2] y⁆ = pinnedX .G2 R ![2, 3] (e * (3 * x * y)) := by
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  have f6 : s₁ • orbitCertRoot .G2 6 = orbitCertRoot .G2 8 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f9 : s₁ • orbitCertRoot .G2 9 = orbitCertRoot .G2 9 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f10 : s₁ • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r9 s₁ f6 f9
  refine ⟨σ (1, 1, 10, 3), hσ _, fun x y => ?_⟩
  rw [← e8, ← e9, ← e11, h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, f10, pow_one,
    Int.cast_ofNat]

theorem burnsideF411a_g2_rel_ru {R : Type*} [CommRing R] :
    ∃ e₁ e₂ e₃ : R, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ (e₃ = 1 ∨ e₃ = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 1] y⁆ =
        pinnedX .G2 R ![1, 2] (e₁ * (-2 * x * y)) *
          (pinnedX .G2 R ![2, 3] (e₂ * (-3 * x * y ^ 2)) *
            pinnedX .G2 R ![1, 3] (e₃ * (-3 * x ^ 2 * y))) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  have r7 : ((6, 8, 12, [(1, 1, 9, -2), (1, 2, 11, -3), (2, 1, 10, -3)]) : PairRow) ∈
      pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r7 1 (one 6) (one 8)
  refine ⟨σ (1, 1, 9, -2), σ (1, 2, 11, -3), σ (2, 1, 10, -3), hσ _, hσ _, hσ _, fun x y => ?_⟩
  rw [← e6, ← e8, ← e9, ← e10, ← e11, h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one, pow_one,
    Int.cast_neg, Int.cast_ofNat]

variable {K : Type} [Field K]

theorem burnsideF411a_eq_zero_of_sign_three (h3 : (3 : K) ≠ 0) {e x : K} (he : e = 1 ∨ e = -1)
    (h : e * (3 * x) = 0) : x = 0 :=
  (mul_eq_zero.1 (eq_zero_of_sign_mul' he h)).resolve_left h3

theorem burnsideF411a_g2_eq_Xc_of_central (h3 : (3 : K) ≠ 0) {z : ModGL .G2 K}
    (hzU : z ∈ posUnipotent .G2 K) (hz : ∀ h ∈ posUnipotent .G2 K, h * z = z * h) :
    ∃ t : K, z = Xc t := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq K
    (S := {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}) (fun α hα => hα)
    (posRoots_closed .G2) posRootList_nodup (fun α => mem_posRootList_iff) hzU
  have h6 : (List.map (fun α => pinnedX .G2 K α (c α)) posRootList).prod =
      Xa (c ![1, 0]) * (Xr (c ![0, 1]) * (Xu (c ![1, 1]) * (Xb (c ![1, 3]) *
        (Xv (c ![1, 2]) * (Xc (c ![2, 3]) * 1))))) := rfl
  rw [hc, mul_one] at h6
  obtain ⟨ca, cr, cu, cb, cv, cc, hz'⟩ : ∃ ca cr cu cb cv cc : K,
      z = Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc)))) :=
    ⟨_, _, _, _, _, _, h6⟩
  clear h6 hc c
  subst hz'
  have hA : ∀ h ∈ posUnipotent .G2 K,
      h * (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) =
        (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) * h := by
    intro h hh
    have h1 := hz h hh
    have h2 := (Xc_central cc h hh).eq
    refine mul_right_cancel (b := Xc cc) ?_
    calc h * (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) * Xc cc
        = h * (Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc))))) := by
          simp only [mul_assoc]
      _ = Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc)))) * h := h1
      _ = (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) * (Xc cc * h) := by
          simp only [mul_assoc]
      _ = (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) * (h * Xc cc) := by rw [h2]
      _ = (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv))) * h) * Xc cc := by
          simp only [mul_assoc]
  have hW1 : Commute (Xr cr * (Xu cu * (Xb cb * Xv cv))) (Xb (1 : K)) :=
    (comm_rb cr 1).mul_left ((comm_ub cu 1).mul_left ((Xb_comm cb 1).mul_left (comm_vb cv 1)))
  have hc1 : Xb (1 : K) * Xa ca = Xa ca * Xb (1 : K) := by
    refine mul_right_cancel (b := Xr cr * (Xu cu * (Xb cb * Xv cv))) ?_
    calc Xb (1 : K) * Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))
        = Xb (1 : K) * (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) := by simp only [mul_assoc]
      _ = (Xa ca * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) * Xb (1 : K) :=
          hA (Xb (1 : K)) (Xb_mem 1)
      _ = Xa ca * ((Xr cr * (Xu cu * (Xb cb * Xv cv))) * Xb (1 : K)) := by simp only [mul_assoc]
      _ = Xa ca * (Xb (1 : K) * (Xr cr * (Xu cu * (Xb cb * Xv cv)))) := by rw [hW1.eq]
      _ = Xa ca * Xb (1 : K) * (Xr cr * (Xu cu * (Xb cb * Xv cv))) := by simp only [mul_assoc]
  have hca : ca = 0 := by
    obtain ⟨e, he, hab⟩ := rel_ab (K := K)
    have h1 : ⁅Xa ca, Xb (1 : K)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc1.symm
    rw [hab] at h1
    have h2 : Xc (e * (ca * 1)) = Xc 0 := by rw [h1, Xc_zero]
    have h4 := Xc_injective h2
    exact eq_zero_of_sign_mul' he (by simpa using h4)
  subst hca
  simp only [Xa_zero, one_mul] at hA ⊢
  obtain ⟨e₁, e₂, e₃, e₄, he₁, he₂, he₃, he₄, har⟩ := rel_ar (K := K)
  obtain ⟨e', he', hab⟩ := rel_ab (K := K)
  have key : ∀ g h : ModGL .G2 K, g * h = ⁅g, h⁆ * (h * g) := fun g h => by
    simp only [commutatorElement_def]
    group
  obtain ⟨Q, hQdef⟩ : ∃ Q : ModGL .G2 K, Q = Xu (e₁ * (1 * cr)) * Xv (e₂ * (1 * cr ^ 2)) *
      Xb (e₃ * (1 * cr ^ 3)) * Xc (e₄ * (1 ^ 2 * cr ^ 3)) := ⟨_, rfl⟩
  obtain ⟨Xcb, hXcb⟩ : ∃ Y : ModGL .G2 K, Y = Xc (e' * (1 * cb)) := ⟨_, rfl⟩
  have hQ : Xa (1 : K) * Xr cr = Q * (Xr cr * Xa (1 : K)) := by
    rw [key (Xa (1 : K)) (Xr cr), har 1 cr, hQdef]
  have hB : Xa (1 : K) * Xb cb = Xcb * (Xb cb * Xa (1 : K)) := by
    rw [key (Xa (1 : K)) (Xb cb), hab 1 cb, hXcb]
  have hau : Xa (1 : K) * Xu cu = Xu cu * Xa (1 : K) := (comm_au 1 cu).eq
  have hav : Xa (1 : K) * Xv cv = Xv cv * Xa (1 : K) := (comm_av 1 cv).eq
  have hcr : Xr cr * Xcb = Xcb * Xr cr := by rw [hXcb]; exact (comm_rc cr _).eq
  have hcu : Xu cu * Xcb = Xcb * Xu cu := by rw [hXcb]; exact (comm_uc cu _).eq
  have hmain : Q * Xcb = 1 := by
    have hcent := hA (Xa (1 : K)) (Xa_mem 1)
    refine mul_right_cancel (b := Xr cr * (Xu cu * (Xb cb * (Xv cv * Xa (1 : K))))) ?_
    calc Q * Xcb * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xa (1 : K)))))
        = Q * ((Xcb * Xr cr) * (Xu cu * (Xb cb * (Xv cv * Xa (1 : K))))) := by
          simp only [mul_assoc]
      _ = Q * ((Xr cr * Xcb) * (Xu cu * (Xb cb * (Xv cv * Xa (1 : K))))) := by rw [hcr]
      _ = Q * (Xr cr * ((Xcb * Xu cu) * (Xb cb * (Xv cv * Xa (1 : K))))) := by
          simp only [mul_assoc]
      _ = Q * (Xr cr * ((Xu cu * Xcb) * (Xb cb * (Xv cv * Xa (1 : K))))) := by rw [hcu]
      _ = Q * (Xr cr * (Xu cu * (Xcb * (Xb cb * (Xv cv * Xa (1 : K)))))) := by
          simp only [mul_assoc]
      _ = Q * (Xr cr * (Xu cu * (Xcb * (Xb cb * (Xa (1 : K) * Xv cv))))) := by rw [hav]
      _ = Q * (Xr cr * (Xu cu * ((Xcb * (Xb cb * Xa (1 : K))) * Xv cv))) := by
          simp only [mul_assoc]
      _ = Q * (Xr cr * (Xu cu * ((Xa (1 : K) * Xb cb) * Xv cv))) := by rw [hB]
      _ = Q * (Xr cr * ((Xu cu * Xa (1 : K)) * (Xb cb * Xv cv))) := by simp only [mul_assoc]
      _ = Q * (Xr cr * ((Xa (1 : K) * Xu cu) * (Xb cb * Xv cv))) := by rw [hau]
      _ = (Q * (Xr cr * Xa (1 : K))) * (Xu cu * (Xb cb * Xv cv)) := by simp only [mul_assoc]
      _ = (Xa (1 : K) * Xr cr) * (Xu cu * (Xb cb * Xv cv)) := by rw [hQ]
      _ = Xa (1 : K) * (Xr cr * (Xu cu * (Xb cb * Xv cv))) := by simp only [mul_assoc]
      _ = (Xr cr * (Xu cu * (Xb cb * Xv cv))) * Xa (1 : K) := hcent
      _ = 1 * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xa (1 : K))))) := by
          simp only [mul_assoc, one_mul]
  have hone : Xu (0 : K) * Xv 0 * Xb 0 * Xc 0 = 1 := by
    rw [Xu_zero, Xv_zero, Xb_zero, Xc_zero]
    simp
  have hexp : Xu (e₁ * (1 * cr)) * Xv (e₂ * (1 * cr ^ 2)) * Xb (e₃ * (1 * cr ^ 3)) *
      Xc (e₄ * (1 ^ 2 * cr ^ 3) + e' * (1 * cb)) = Xu 0 * Xv 0 * Xb 0 * Xc 0 := by
    rw [hone, Xc_add, ← mul_assoc]
    rw [hQdef, hXcb] at hmain
    exact hmain
  obtain ⟨hp1, -, -, hp4⟩ := inj4 hexp
  have hcr0 : cr = 0 := eq_zero_of_sign_mul' he₁ (by simpa using hp1)
  subst hcr0
  have hcb0 : cb = 0 := by
    have h5 : e' * cb = 0 := by simpa using hp4
    exact eq_zero_of_sign_mul' he' h5
  subst hcb0
  simp only [Xr_zero, Xb_zero, one_mul] at hA ⊢
  have hcv0 : cv = 0 := by
    have hc := hA (Xu (1 : K)) (Xu_mem 1)
    have h1 : Xu (1 : K) * Xv cv = Xv cv * Xu (1 : K) := by
      refine mul_left_cancel (a := Xu cu) ?_
      calc Xu cu * (Xu (1 : K) * Xv cv) = (Xu cu * Xu (1 : K)) * Xv cv := by rw [mul_assoc]
        _ = (Xu (1 : K) * Xu cu) * Xv cv := by rw [(Xu_comm cu 1).eq]
        _ = Xu (1 : K) * (Xu cu * Xv cv) := by rw [mul_assoc]
        _ = (Xu cu * Xv cv) * Xu (1 : K) := hc
        _ = Xu cu * (Xv cv * Xu (1 : K)) := by rw [mul_assoc]
    obtain ⟨e, he, huv⟩ := burnsideF411a_g2_rel_uv (R := K)
    have h2 : ⁅pinnedX .G2 K ![1, 1] (1 : K), pinnedX .G2 K ![1, 2] cv⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h1
    rw [huv] at h2
    have h4 : Xc (e * (3 * 1 * cv)) = Xc 0 := by rw [Xc_zero]; exact h2
    have h5 := Xc_injective h4
    exact burnsideF411a_eq_zero_of_sign_three h3 he (by simpa using h5)
  subst hcv0
  simp only [Xv_zero, mul_one] at hA ⊢
  have hcu0 : cu = 0 := by
    have hc := hA (Xr (1 : K)) (Xr_mem 1)
    obtain ⟨e₁', e₂', e₃', -, -, he₃', hru⟩ := burnsideF411a_g2_rel_ru (R := K)
    have h2 : ⁅pinnedX .G2 K ![0, 1] (1 : K), pinnedX .G2 K ![1, 1] cu⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [hru] at h2
    have h4 : Xu (0 : K) * Xv (e₁' * (-2 * 1 * cu)) * Xb (e₃' * (-3 * 1 ^ 2 * cu)) *
        Xc (e₂' * (-3 * 1 * cu ^ 2)) = Xu 0 * Xv 0 * Xb 0 * Xc 0 := by
      rw [hone, Xu_zero, one_mul, mul_assoc, (comm_bc _ _).eq]
      exact h2
    obtain ⟨-, -, hb, -⟩ := inj4 h4
    have h5 : -e₃' * (3 * cu) = 0 := by
      have : e₃' * (-3 * 1 ^ 2 * cu) = 0 := hb
      linear_combination this
    refine burnsideF411a_eq_zero_of_sign_three h3 (e := -e₃') ?_ h5
    rcases he₃' with h | h <;> simp [h]
  subst hcu0
  exact ⟨cc, by simp only [Xu_zero, one_mul]⟩

end CFSG.ASVolI

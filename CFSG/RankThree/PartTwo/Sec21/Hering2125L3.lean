module

import CFSG.RankThree.PartTwo.Sec21.Hering2125Mat
public import CFSG.Foundations.Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open Matrix CFSG

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem comm_of_mk_comm {a b : GL (Fin 3) K} (ha : a * a = 1)
    (h : ProjGenLinGroup.mk a * ProjGenLinGroup.mk b =
      ProjGenLinGroup.mk b * ProjGenLinGroup.mk a) :
    a * b = b * a := by
  rw [← map_mul, ← map_mul] at h
  obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h1 : b * a * b⁻¹ = a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
    rw [← hν]
    calc a * b * Matrix.GeneralLinearGroup.scalar (Fin 3) ν * b⁻¹
        = a * (b * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) * b⁻¹ := by group
      _ = a * (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * b) * b⁻¹ := by
          rw [scalar_comm ν b]
      _ = a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by group
  have h2 := eq_one_of_conj_sq ha h1
  rw [h2, map_one, mul_one] at hν
  exact hν

theorem core_D {X' : Type} [Group X'] (ι : X' →* ProjGenLinGroup (Fin 3) K)
    (hι : Function.Injective ι)
    (hrange : ∀ s : GL (Fin 3) K, (s : Matrix (Fin 3) (Fin 3) K).det = 1 →
      ∃ x, ι x = ProjGenLinGroup.mk s)
    {D : GL (Fin 3) K} {e₀ : K} (he₀ : e₀ ≠ 1)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1])
    (Ubar : Subgroup X') (hcard : Nat.card Ubar = 4) (hexp : ∀ u ∈ Ubar, u * u = 1)
    (hfix : ∀ u ∈ Ubar, ProjGenLinGroup.mk D * ι u * (ProjGenLinGroup.mk D)⁻¹ = ι u) :
    ∃ x ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ubar : Set X')),
      ProjGenLinGroup.mk D * ι x * (ProjGenLinGroup.mk D)⁻¹ ≠ ι x := by
  classical
  have hlift : ∀ u ∈ Ubar, ∃ b : GL (Fin 3) K, ι u = ProjGenLinGroup.mk b ∧ b * b = 1 := by
    intro u hu
    obtain ⟨b₀, hb₀⟩ := ProjGenLinGroup.mk_surjective (ι u)
    have : ProjGenLinGroup.mk b₀ * ProjGenLinGroup.mk b₀ = 1 := by
      rw [hb₀, ← map_mul, hexp u hu, map_one]
    obtain ⟨b, hb, hbb⟩ := exists_sq_one_lift this
    exact ⟨b, by rw [← hb₀, hb], hbb⟩
  have hcommD : ∀ u ∈ Ubar, ∀ b : GL (Fin 3) K, ι u = ProjGenLinGroup.mk b → b * b = 1 →
      b * D = D * b := by
    intro u hu b hb hbb
    refine comm_of_mk_comm hbb ?_
    have h1 := hfix u hu
    rw [hb, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hcommU : ∀ u ∈ Ubar, ∀ u' ∈ Ubar, u * u' = u' * u := by
    intro u hu u' hu'
    have h1 := hexp (u * u') (Subgroup.mul_mem _ hu hu')
    have h2 := hexp u hu
    have h3 := hexp u' hu'
    have e1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right h2
    have e2 : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right h3
    have e3 : (u * u')⁻¹ = u * u' := inv_eq_of_mul_eq_one_right h1
    rw [_root_.mul_inv_rev, e1, e2] at e3
    exact e3.symm
  obtain ⟨u₁, hu₁, hu₁1⟩ : ∃ u₁ ∈ Ubar, u₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Ubar = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at hcard
    omega
  obtain ⟨a, ha, haa⟩ := hlift u₁ hu₁
  have haD : a * D = D * a := hcommD u₁ hu₁ a ha haa
  have hne : a ≠ 1 := by
    rintro rfl
    apply hu₁1
    apply hι
    rw [ha, map_one, map_one]
  obtain ⟨P, hPa, hPD⟩ := exists_basis_change he₀ hD haa haD hne
  have hPaU : P⁻¹ * a * P = uniGL 0 0 1 := by
    rw [mul_assoc, hPa]; group
  have hPD' : P⁻¹ * D = D * P⁻¹ := by
    have : P⁻¹ * D * P = D := by rw [mul_assoc, hPD]; group
    calc P⁻¹ * D = P⁻¹ * D * P * P⁻¹ := by group
      _ = D * P⁻¹ := by rw [this]
  have hclass : ∀ u ∈ Ubar, ∃ q : K,
      ι u = ProjGenLinGroup.mk (P * uniGL 0 0 q * P⁻¹) := by
    intro u hu
    obtain ⟨b, hb, hbb⟩ := hlift u hu
    have hbD : b * D = D * b := hcommD u hu b hb hbb
    have hba : a * b = b * a := by
      refine comm_of_mk_comm haa ?_
      rw [← ha, ← hb, ← map_mul, ← map_mul, hcommU u₁ hu₁ u hu]
    have hbhbh : (P⁻¹ * b * P) * (P⁻¹ * b * P) = 1 := by
      calc (P⁻¹ * b * P) * (P⁻¹ * b * P) = P⁻¹ * (b * b) * P := by group
        _ = 1 := by rw [hbb]; group
    have hbhD : (P⁻¹ * b * P) * D = D * (P⁻¹ * b * P) := by
      calc (P⁻¹ * b * P) * D = P⁻¹ * b * (P * D) := by group
        _ = P⁻¹ * b * (D * P) := by rw [← hPD]
        _ = P⁻¹ * (b * D) * P := by group
        _ = P⁻¹ * (D * b) * P := by rw [hbD]
        _ = (P⁻¹ * D) * b * P := by group
        _ = (D * P⁻¹) * b * P := by rw [hPD']
        _ = D * (P⁻¹ * b * P) := by group
    have hbhU : (P⁻¹ * b * P) * uniGL 0 0 1 = uniGL 0 0 1 * (P⁻¹ * b * P) := by
      calc (P⁻¹ * b * P) * uniGL 0 0 1 = P⁻¹ * (b * a) * P := by rw [← hPaU]; group
        _ = P⁻¹ * (a * b) * P := by rw [hba]
        _ = uniGL 0 0 1 * (P⁻¹ * b * P) := by rw [← hPaU]; group
    obtain ⟨q, hq⟩ := eq_uniGL_of_comm he₀ hD hbhbh hbhD hbhU
    refine ⟨q, ?_⟩
    rw [hb, ← hq]
    congr 1
    group
  let S : Subgroup X' :=
    { carrier := {x | ∃ a b c : K, ι x = ProjGenLinGroup.mk (P * uniGL a b c * P⁻¹)}
      mul_mem' := by
        rintro x y ⟨a, b, c, hx⟩ ⟨a', b', c', hy⟩
        refine ⟨a + a', b + b', c + c' + b * a', ?_⟩
        rw [map_mul, hx, hy, ← map_mul, ← uniGL_mul]
        congr 1
        group
      one_mem' := ⟨0, 0, 0, by rw [map_one, uniGL_zero]; simp⟩
      inv_mem' := by
        rintro x ⟨a, b, c, hx⟩
        refine ⟨-a, -b, a * b - c, ?_⟩
        rw [map_inv, hx, ← map_inv, ← uniGL_inv]
        congr 1
        group }
  have hSC : S ≤ Subgroup.centralizer (Ubar : Set X') := by
    intro x hx
    obtain ⟨a', b', c', hxm⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨q, hq⟩ := hclass u hu
    apply hι
    rw [map_mul, map_mul, hq, hxm, ← map_mul, ← map_mul]
    congr 1
    have : uniGL (0 : K) 0 q * uniGL a' b' c' = uniGL a' b' c' * uniGL 0 0 q := by
      rw [uniGL_mul, uniGL_mul]
      congr 1 <;> ring
    calc P * uniGL 0 0 q * P⁻¹ * (P * uniGL a' b' c' * P⁻¹)
        = P * (uniGL 0 0 q * uniGL a' b' c') * P⁻¹ := by group
      _ = P * (uniGL a' b' c' * uniGL 0 0 q) * P⁻¹ := by rw [this]
      _ = P * uniGL a' b' c' * P⁻¹ * (P * uniGL 0 0 q * P⁻¹) := by group
  have hCN : Subgroup.centralizer (Ubar : Set X') ≤ Subgroup.normalizer (S : Set X') := by
    have key : ∀ g ∈ Subgroup.centralizer (Ubar : Set X'), ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
      intro g hg x hx
      obtain ⟨a', b', c', hxm⟩ := hx
      obtain ⟨gm, hgm⟩ := ProjGenLinGroup.mk_surjective (ι g)
      have hg1 : u₁ * g = g * u₁ := Subgroup.mem_centralizer_iff.mp hg u₁ hu₁
      have hgcomm : a * gm = gm * a := by
        refine comm_of_mk_comm haa ?_
        rw [← ha, hgm, ← map_mul, ← map_mul, hg1]
      have hĝ : (P⁻¹ * gm * P) * uniGL 0 0 1 = uniGL 0 0 1 * (P⁻¹ * gm * P) := by
        calc (P⁻¹ * gm * P) * uniGL 0 0 1 = P⁻¹ * (gm * a) * P := by rw [← hPaU]; group
          _ = P⁻¹ * (a * gm) * P := by rw [hgcomm]
          _ = uniGL 0 0 1 * (P⁻¹ * gm * P) := by rw [← hPaU]; group
      obtain ⟨h01, h20, h21, h1122⟩ := shape_of_comm_uni hĝ
      obtain ⟨a'', b'', c'', hconj⟩ := conj_uniGL h01 h20 h21 h1122 a' b' c'
      refine ⟨a'', b'', c'', ?_⟩
      rw [map_mul, map_mul, hxm, map_inv, ← hgm, ← map_inv, ← map_mul, ← map_mul, ← hconj]
      congr 1
      group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hS2 : IsPGroup 2 S := by
    intro x
    refine ⟨2, ?_⟩
    obtain ⟨a', b', c', hxm⟩ := x.2
    apply Subtype.ext
    apply hι
    show ι ((x : X') ^ 2 ^ 2) = ι 1
    rw [map_pow, map_one, hxm, ← map_pow, conj_pow]
    have h4 : uniGL a' b' c' ^ 2 ^ 2 = 1 := by
      have e2 : uniGL a' b' c' ^ 2 = uniGL 0 0 (b' * a') := by
        rw [pow_two, uniGL_mul]
        have ha2 : a' + a' = 0 := by rw [← two_mul, h2, zero_mul]
        have hb2 : b' + b' = 0 := by rw [← two_mul, h2, zero_mul]
        have hc2 : c' + c' + b' * a' = b' * a' := by
          have : c' + c' = 0 := by rw [← two_mul, h2, zero_mul]
          rw [this, zero_add]
        rw [ha2, hb2, hc2]
      have e4 : uniGL a' b' c' ^ 2 ^ 2 = (uniGL a' b' c' ^ 2) ^ 2 := by
        rw [← pow_mul]
        norm_num
      rw [e4, e2, pow_two, uniGL_mul]
      have : b' * a' + b' * a' = 0 := by rw [← two_mul, h2, zero_mul]
      simp only [add_zero, mul_zero, this]
      exact uniGL_zero
    rw [h4]
    simp
  obtain ⟨x₀, hx₀⟩ := hrange (P * uniGL 1 0 0 * P⁻¹) (det_conj_uniGL P 1 0 0)
  have hx₀S : x₀ ∈ S := ⟨1, 0, 0, hx₀⟩
  refine ⟨x₀, ?_, ?_⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSC hCN hS2 hx₀S
  · intro hEq
    rw [hx₀, ← map_inv, ← map_mul, ← map_mul] at hEq
    obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hEq
    have hDU : D * uniGL 1 0 0 = uniGL (e₀ * 1) 0 0 * D := diag_conj_uni hD 1
    have h1 : D * (P * uniGL 1 0 0 * P⁻¹) * D⁻¹ = P * uniGL (e₀ * 1) 0 0 * P⁻¹ := by
      calc D * (P * uniGL 1 0 0 * P⁻¹) * D⁻¹ = (D * P) * uniGL 1 0 0 * (D * P)⁻¹ := by group
        _ = (P * D) * uniGL 1 0 0 * (P * D)⁻¹ := by rw [hPD]
        _ = P * (D * uniGL 1 0 0 * D⁻¹) * P⁻¹ := by group
        _ = P * (uniGL (e₀ * 1) 0 0 * D * D⁻¹) * P⁻¹ := by rw [hDU]
        _ = P * uniGL (e₀ * 1) 0 0 * P⁻¹ := by group
    have h2 : uniGL (e₀ * 1) 0 0 * Matrix.GeneralLinearGroup.scalar (Fin 3) ν =
        uniGL 1 0 0 := by
      have h3 : P * (uniGL (e₀ * 1) 0 0 * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) * P⁻¹ =
          P * uniGL 1 0 0 * P⁻¹ := by
        rw [← hν, h1]
        calc P * (uniGL (e₀ * 1) 0 0 * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) * P⁻¹
            = P * uniGL (e₀ * 1) 0 0 * (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * P⁻¹) := by
              group
          _ = P * uniGL (e₀ * 1) 0 0 * (P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) := by
              rw [← scalar_comm ν P⁻¹]
          _ = P * uniGL (e₀ * 1) 0 0 * P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
              group
      calc uniGL (e₀ * 1) 0 0 * Matrix.GeneralLinearGroup.scalar (Fin 3) ν
          = P⁻¹ * (P * (uniGL (e₀ * 1) 0 0 * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) * P⁻¹) *
              P := by group
        _ = P⁻¹ * (P * uniGL 1 0 0 * P⁻¹) * P := by rw [h3]
        _ = uniGL 1 0 0 := by group
    have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h2
    have e02 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h2
    simp [uniGL, uniM, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at e11 e02
    apply he₀
    rw [e11] at e02
    simpa using e02

end Core

section Det

variable {K : Type} [Field K]

theorem det_conj_eq_one {s : GL (Fin 3) K} (hs : (s : Matrix (Fin 3) (Fin 3) K).det = 1)
    (g : GL (Fin 3) K) : ((g * s * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := Matrix.GeneralLinearGroup.val_det_apply (g * s * g⁻¹)
  have hs' : Matrix.GeneralLinearGroup.det s = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hs
  rw [← h, map_mul, map_mul, map_inv, hs']
  simp

end Det

theorem l3_exists_moved {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Sec4.PiField true 2 n K)
    (hq : Sec4.ModThree true (2 ^ n)) {y : GL (Fin 3) K}
    (hy : Sec4.Type123 true (2 ^ n) K y 2)
    {X' : Type} [Group X'] (e : X' ≃* CFSG.Assembly.RankThreeEven.projImage
      (Sec4.slPi true 3 (2 ^ n) K))
    (Ubar : Subgroup X') (hcard : Nat.card Ubar = 4) (hexp : ∀ u ∈ Ubar, u * u = 1)
    (hfix : ∀ u ∈ Ubar, ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk y)⁻¹ = (e u : ProjGenLinGroup (Fin 3) K)) :
    ∃ x ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ubar : Set X')),
      ProjGenLinGroup.mk y * (e x : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ ≠
        (e x : ProjGenLinGroup (Fin 3) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK.card]; rfl)
  obtain ⟨e₀, he3, he1, z, hz, g, hg, hD⟩ := hy
  have he1' : (e₀ : K) ≠ 1 := fun h => he1 (Units.ext h)
  obtain ⟨ξ, -, hξ⟩ := Sec4.exists_scalar_of_mem_zPi hK hq he3 he1' hz
  have hmkz : ProjGenLinGroup.mk z = 1 := by rw [← hξ, ProjGenLinGroup.mk_scalar]
  set G := ProjGenLinGroup.mk g with hG
  have hmkD : ProjGenLinGroup.mk (Sec4.diagE e₀) = G⁻¹ * ProjGenLinGroup.mk y * G := by
    rw [← hD, map_mul, map_mul, map_mul, map_inv, hmkz, mul_one]
  let ι : X' →* ProjGenLinGroup (Fin 3) K :=
    ((MulAut.conj G⁻¹).toMonoidHom).comp
      ((CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi true 3 (2 ^ n) K)).subtype.comp
        e.toMonoidHom)
  have hιx : ∀ x, ι x = G⁻¹ * (e x : ProjGenLinGroup (Fin 3) K) * G := by
    intro x
    simp [ι, MulAut.conj_apply]
  have hι : Function.Injective ι := (MulAut.conj G⁻¹).injective.comp
    (Subgroup.subtype_injective _ |>.comp e.injective)
  have hrange : ∀ s : GL (Fin 3) K, (s : Matrix (Fin 3) (Fin 3) K).det = 1 →
      ∃ x, ι x = ProjGenLinGroup.mk s := by
    intro s hs
    have hs' := det_conj_eq_one hs g
    have hmem : ProjGenLinGroup.mk (g * s * g⁻¹) ∈
        CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi true 3 (2 ^ n) K) :=
      ⟨g * s * g⁻¹, (Sec4.mem_slPi_true _).mpr hs', rfl⟩
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    rw [hιx, MulEquiv.apply_symm_apply]
    show G⁻¹ * ProjGenLinGroup.mk (g * s * g⁻¹) * G = _
    rw [hG, map_mul, map_mul, map_inv]
    group
  have hfixD : ∀ u ∈ Ubar, ProjGenLinGroup.mk (Sec4.diagE e₀) * ι u *
      (ProjGenLinGroup.mk (Sec4.diagE e₀))⁻¹ = ι u := by
    intro u hu
    have h1 := hfix u hu
    rw [hmkD, hιx u]
    calc G⁻¹ * ProjGenLinGroup.mk y * G * (G⁻¹ * (e u : ProjGenLinGroup (Fin 3) K) * G) *
          (G⁻¹ * ProjGenLinGroup.mk y * G)⁻¹
        = G⁻¹ * (ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) *
            (ProjGenLinGroup.mk y)⁻¹) * G := by group
      _ = G⁻¹ * (e u : ProjGenLinGroup (Fin 3) K) * G := by rw [h1]
  obtain ⟨x, hx, hne⟩ := core_D (D := Sec4.diagE e₀) (e₀ := (e₀ : K)) ι hι hrange he1'
    (Sec4.coe_diagE e₀) Ubar hcard hexp hfixD
  refine ⟨x, hx, fun h => hne ?_⟩
  rw [hmkD, hιx x]
  calc G⁻¹ * ProjGenLinGroup.mk y * G * (G⁻¹ * (e x : ProjGenLinGroup (Fin 3) K) * G) *
        (G⁻¹ * ProjGenLinGroup.mk y * G)⁻¹
      = G⁻¹ * (ProjGenLinGroup.mk y * (e x : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk y)⁻¹) * G := by group
    _ = G⁻¹ * (e x : ProjGenLinGroup (Fin 3) K) * G := by rw [h]

end CFSG.RankThree.PartTwo.Sec21.Hering2125
